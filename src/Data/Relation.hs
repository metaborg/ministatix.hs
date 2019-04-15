module Data.Relation where

import Data.HashMap.Strict as Map
import Data.HashSet as Set
import Data.Hashable

import Control.Monad.State

type FinRel a b = HashMap a (HashSet b) 
type    Rel a b = a → b → Bool

contains :: (Eq a, Hashable a, Eq b, Hashable b) ⇒ FinRel a b → Rel a b
contains r lhs rhs =
  case Map.lookup lhs r of
    Nothing → False
    Just gt → rhs `Set.member` gt

finite :: (Eq a, Hashable a, Eq b, Hashable b) ⇒ [(a,b)] → FinRel a b
finite ps = foldl (\m (a, b) → insertWith Set.union a (Set.singleton b) m) Map.empty ps

transitiveClosure :: (Eq a, Hashable a) ⇒ FinRel a a → Rel a a
transitiveClosure r lhs rhs = evalState (closure r lhs rhs) Set.empty
  where
    closure :: (Eq a, Hashable a) ⇒ FinRel a a → a → a → State (HashSet a) Bool
    closure r lhs rhs = case Map.lookup lhs r of
      Nothing → return False
      Just gt →
        if (rhs `Set.member` gt) then return True
        else case Set.toList gt of
          []     → return False
          (x:xs) → do
            seen ← gets (Set.member x)
            if not seen
              then closure r x rhs
              else return False

reflexiveClosure :: (Eq a, Hashable a) ⇒ Rel a a → Rel a a
reflexiveClosure r lhs rhs =
  if lhs == rhs then True else r lhs rhs

