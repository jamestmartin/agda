data A : Set
data A : Set where

-- Incorrect error:
-- Issue5592b.agda:1,1-13
-- The following names are declared but not accompanied by a
-- definition: A
-- Issue5592b.agda:2,6-13
-- Multiple definitions of A. Previous definition at
-- Issue5592b.agda:1,6-7
-- Perhaps you meant to write
--   'data A where'
-- at Issue5592b.agda:2,6-13?
-- In data definitions separate from data declaration, the ':' and type must be omitted.
-- when scope checking the declaration
--   data A : Set

-- Correct error:
-- Issue5592b.agda:2,6-7
-- Duplicate definition of A
