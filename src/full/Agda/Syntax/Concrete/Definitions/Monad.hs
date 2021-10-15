module Agda.Syntax.Concrete.Definitions.Monad where

import Control.Monad.Except
import Control.Monad.State

import Data.Bifunctor (second)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (TerminationCheck())
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Concrete.Definitions.Types
import Agda.Syntax.Concrete.Definitions.Errors
import Agda.Syntax.Info (DeclInfo (..))

import Agda.Utils.CallStack ( CallStack, HasCallStack, withCallerCallStack )
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Lens
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.List2 (List2)
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Maybe (caseMaybe)
import Agda.Utils.Monad (whenM)

-- | Nicifier monad.
--   Preserve the state when throwing an exception.

newtype Nice a = Nice { unNice :: ExceptT DeclarationException (State NiceEnv) a }
  deriving ( Functor, Applicative, Monad
           , MonadState NiceEnv, MonadError DeclarationException
           )

-- | Run a Nicifier computation, return result and warnings
--   (in chronological order).
runNice :: Nice a -> (Either DeclarationException a, NiceWarnings)
runNice m = second (reverse . niceWarn) $
  runExceptT (unNice m) `runState` initNiceEnv

-- | Nicifier state.

data NiceEnv = NiceEnv
  { _kinds    :: Kinds
    -- ^ Whether a name is a data type, record, or function.
  , _sigs     :: Sigs
    -- ^ Type signatures which may or may not have a definition.
  , _defs     :: Defs
    -- ^ Definitions for names which may or may not have type signatures.
  , _lateSigs :: Sigs
    -- ^ Signatures which occur after their name's definition.
  , _termChk  :: TerminationCheck
    -- ^ Termination checking pragma waiting for a definition.
  , _posChk   :: PositivityCheck
    -- ^ Positivity checking pragma waiting for a definition.
  , _uniChk   :: UniverseCheck
    -- ^ Universe checking pragma waiting for a data/rec signature or definition.
  , _catchall :: Catchall
    -- ^ Catchall pragma waiting for a function clause.
  , _covChk  :: CoverageCheck
    -- ^ Coverage pragma waiting for a definition.
  , niceWarn :: NiceWarnings
    -- ^ Stack of warnings. Head is last warning.
  , _nameId  :: NameId
    -- ^ We distinguish different 'NoName's (anonymous definitions) by a unique 'NameId'.
  }

type Kinds = Map Name DataRecOrFun
type Sigs  = Map Name (List1 DeclInfo)
     -- ^ We retain the 'Name' also in the codomain since
     --   'Name' as a key is up to @Eq Name@ which ignores the range.
     --   However, without range names are not unique in case the
     --   user gives a second definition of the same name.
     --   This causes then problems in 'replaceSigs' which might
     --   replace the wrong signature.
     --
     --   Another reason is that we want to distinguish different
     --   occurrences of 'NoName' in a mutual block (issue #4157).
     --   The 'NoName' in the codomain will have a unique 'NameId'.
type Defs  = Map Name (List1 DeclInfo)

type NiceWarnings = [DeclarationWarning]
     -- ^ Stack of warnings. Head is last warning.

-- | Initial nicifier state.

initNiceEnv :: NiceEnv
initNiceEnv = NiceEnv
  { _kinds    = Map.empty
  , _sigs     = Map.empty
  , _defs     = Map.empty
  , _lateSigs = Map.empty
  , _termChk  = TerminationCheck
  , _posChk   = YesPositivityCheck
  , _uniChk   = YesUniverseCheck
  , _catchall = False
  , _covChk   = YesCoverageCheck
  , niceWarn  = []
  , _nameId   = NameId 1 noModuleNameHash
  }

lensNameId :: Lens' NameId NiceEnv
lensNameId f e = f (_nameId e) <&> \ i -> e { _nameId = i }

nextNameId :: Nice NameId
nextNameId = do
  i <- use lensNameId
  lensNameId %= succ
  return i

-- * Handling the signatures and definitions, stored to infer mutual blocks
--   and handle duplicate, missing, or mismatched type signatures.

-- | Lens for field `_kinds`.
kinds :: Lens' Kinds NiceEnv
kinds f e = f (_kinds e) <&> \ k -> e { _kinds = k }

-- | Lens for field '_sigs'.
sigs :: Lens' Sigs NiceEnv
sigs f e = f (_sigs e) <&> \ s -> e { _sigs = s }

-- | Lens for field '_defs'.
defs :: Lens' Defs NiceEnv
defs f e = f (_defs e) <&> \ d -> e { _defs = d }

-- | Lens for field `_lateSigs`.
lateSigs :: Lens' Sigs NiceEnv
lateSigs f e = f (_lateSigs e) <&> \ s -> e { _sigs = s }

{-addLoneSig :: Range -> Name -> DataRecOrFun -> Nice Name
addLoneSig r x k = do
  loneSigs %== \ s -> do
    let (mr, s') = Map.insertLookupWithKey (\ _k new _old -> new) x (LoneSig r x' k) s
    case mr of
      Nothing -> return s'
      Just{}  -> declarationException $
        if not $ isNoName x then DuplicateDefinition x else DuplicateAnonDeclaration r
  return x'-}

makeNameUnique :: Name -> Nice Name
makeNameUnique x
-- Andreas, 2020-05-19, issue #4157, make '_' unique.
  | not (isNoName x) = return x
  | otherwise = do
    i <- nextNameId
    return x{ nameId = i }

addKind :: Name -> DataRecOrFun -> Nice ()
addKind x k = kinds %== \ ks -> do
  -- FIXME: cross-compare pragmas!!
  let (mk, ks') = Map.insertLookupWithKey (\ _k new _old -> new) x k ks
  case mk of
    Just k' | not (sameKind k k') -> declarationException $ WrongDefinition x k' k
    _                             -> return ks'

getSig :: Name -> Nice (Maybe DataRecOrFun)
getSig x = Map.lookup x <$> use kinds

-- | Add a type signature to the state.
--   Return the name (which is made unique if 'isNoName').
addSig :: Range -> Name -> DataRecOrFun -> Nice Name
addSig r x k = do
    ss <- use sigs
    when (isNoName x && Map.member x ss) $
      declarationException $ DuplicateAnonDeclaration r
    x' <- makeNameUnique x
    addKind x k
    sigs .= insertSig x x' r ss
    whenM (Map.member x <$> use defs) $ lateSigs %= insertSig x x' r
    return x'
  where
    insertSig :: Name -> Name -> Range -> Sigs -> Sigs
    insertSig x x' r ss =
        Map.insertWithKey (\ _k new old -> List1.append old (List1.toList new))
                          x
                          (List1.singleton (DeclInfo x' r))
                          ss

-- | Add a definition to the state.
addDef :: Range -> Name -> DataRecOrFun -> Nice ()
addDef r x k = do
  addKind x k
  if isNoName x
    then sigs %= Map.delete x
    else defs %= Map.insertWithKey (\ _k new old -> List1.append old (List1.toList new))
                                   x
                                   (List1.singleton (DeclInfo x r))

-- | Check that no lone signatures are left in the state.

noLoneSigs :: Nice Bool
noLoneSigs = do
  ss <- use sigs
  ds <- use defs
  return $ Set.null $ Set.difference (Map.keysSet ss) (Map.keysSet ds)

-- | Ensure that all forward declarations have been given a definition.

forgetDecls :: Nice ()
forgetDecls = do
  kinds .= Map.empty
  sigs  .= Map.empty
  defs  .= Map.empty

checkDecls :: Nice Sigs
checkDecls = do
  ss <- use sigs
  ds <- use defs
  ls <- use lateSigs
  forgetDecls
  let missingDefs = Map.withoutKeys ds (Map.keysSet ss) :: Map Name (List1 DeclInfo)
  let missingSigs = Map.withoutKeys ss (Map.keysSet ds)
  let duplicateSigs = Map.mapMaybe List2.fromList1Maybe ss
  let duplicateDefs = Map.mapMaybe List2.fromList1Maybe ds
  forM_ (Map.assocs duplicateSigs) $ \(name, sigs) ->
    declarationWarning $ DuplicateDeclarations name (fmap declRange sigs)
  forM_ (Map.assocs missingDefs) $ \(name, sigs) ->
    declarationWarning $ MissingDefinitions name (fmap declRange sigs)
  forM_ (Map.assocs duplicateDefs) $ \(name, defs) ->
    declarationException $ DuplicateDefinitions name (fmap declRange defs)
  forM_ (Map.assocs missingSigs) $ \(name, (r List1.:| _)) ->
    declarationWarning $ MissingDeclarations name $ declRange r
  forM_ (Map.assocs ls) $ \(name, rs) ->
    -- HACK: Make lateSigs contain the def so that you don't have to look it up here
    caseMaybe (Map.lookup name ds) __IMPOSSIBLE__ $ \ (def List1.:| _) ->
      declarationWarning $ DeclarationsAfterDefinition name (declRange def) (fmap declRange rs)
  return missingSigs

{-}
-- | Get names of lone function signatures, plus their unique names.

loneFuns :: LoneSigs -> [(Name,Name)]
loneFuns = map (second loneSigName) . filter (isFunName . loneSigKind . snd) . Map.toList

-- | Create a 'LoneSigs' map from an association list.

loneSigsFromLoneNames :: [(Range, Name, DataRecOrFun)] -> LoneSigs
loneSigsFromLoneNames = Map.fromList . map (\(r,x,k) -> (x, LoneSig r x k))
-}

-- | Lens for field '_termChk'.

terminationCheckPragma :: Lens' TerminationCheck NiceEnv
terminationCheckPragma f e = f (_termChk e) <&> \ s -> e { _termChk = s }

withTerminationCheckPragma :: TerminationCheck -> Nice a -> Nice a
withTerminationCheckPragma tc f = do
  tc_old <- use terminationCheckPragma
  terminationCheckPragma .= tc
  result <- f
  terminationCheckPragma .= tc_old
  return result

coverageCheckPragma :: Lens' CoverageCheck NiceEnv
coverageCheckPragma f e = f (_covChk e) <&> \ s -> e { _covChk = s }

withCoverageCheckPragma :: CoverageCheck -> Nice a -> Nice a
withCoverageCheckPragma tc f = do
  tc_old <- use coverageCheckPragma
  coverageCheckPragma .= tc
  result <- f
  coverageCheckPragma .= tc_old
  return result

-- | Lens for field '_posChk'.

positivityCheckPragma :: Lens' PositivityCheck NiceEnv
positivityCheckPragma f e = f (_posChk e) <&> \ s -> e { _posChk = s }

withPositivityCheckPragma :: PositivityCheck -> Nice a -> Nice a
withPositivityCheckPragma pc f = do
  pc_old <- use positivityCheckPragma
  positivityCheckPragma .= pc
  result <- f
  positivityCheckPragma .= pc_old
  return result

-- | Lens for field '_uniChk'.

universeCheckPragma :: Lens' UniverseCheck NiceEnv
universeCheckPragma f e = f (_uniChk e) <&> \ s -> e { _uniChk = s }

withUniverseCheckPragma :: UniverseCheck -> Nice a -> Nice a
withUniverseCheckPragma uc f = do
  uc_old <- use universeCheckPragma
  universeCheckPragma .= uc
  result <- f
  universeCheckPragma .= uc_old
  return result

-- | Get universe check pragma from a data/rec signature.
--   Defaults to 'YesUniverseCheck'.

getUniverseCheckFromSig :: Name -> Nice UniverseCheck
getUniverseCheckFromSig x = maybe YesUniverseCheck universeCheck <$> getSig x

-- | Lens for field '_catchall'.

catchallPragma :: Lens' Catchall NiceEnv
catchallPragma f e = f (_catchall e) <&> \ s -> e { _catchall = s }

-- | Get current catchall pragma, and reset it for the next clause.

popCatchallPragma :: Nice Catchall
popCatchallPragma = do
  ca <- use catchallPragma
  catchallPragma .= False
  return ca

withCatchallPragma :: Catchall -> Nice a -> Nice a
withCatchallPragma ca f = do
  ca_old <- use catchallPragma
  catchallPragma .= ca
  result <- f
  catchallPragma .= ca_old
  return result

-- | Add a new warning.
niceWarning :: DeclarationWarning -> Nice ()
niceWarning w = modify $ \ st -> st { niceWarn = w : niceWarn st }

declarationException :: HasCallStack => DeclarationException' -> Nice a
declarationException e = withCallerCallStack $ throwError . flip DeclarationException e

declarationWarning' :: DeclarationWarning' -> CallStack -> Nice ()
declarationWarning' w loc = niceWarning $ DeclarationWarning loc w

declarationWarning :: HasCallStack => DeclarationWarning' -> Nice ()
declarationWarning = withCallerCallStack . declarationWarning'
