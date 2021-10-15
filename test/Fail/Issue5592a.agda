{-# OPTIONS --safe #-}
data A : Set
data A : Set where

-- Incorrect error:
-- Issue5592a.agda:2,1-13
-- The following names are declared but not accompanied by a
-- definition: A

-- Correct error:
-- Issue5592a.agda:3,6-7
-- Duplicate definition of A
