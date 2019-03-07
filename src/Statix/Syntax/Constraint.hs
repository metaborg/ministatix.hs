{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

{-

Tutorial on unification-fd package can be found here:
https://winterkoninkje.dreamwidth.org/tag/unification

-}

module Statix.Syntax.Constraint
  ( TermF
  , ConstraintF(..)
  , RawVar

  , RawTerm
  , pattern RCon
  , pattern RLabel
  , pattern RVar
  , RawConstraint

  {- Solver terms-}
  , Term
  , pattern Con
  , pattern Node
  , pattern Label
  , pattern Var
  , pattern Answer
  , cook

  {- Constraint syntax -}
  , Constraint
  , Constraints
  , pattern CTrue
  , pattern CFalse
  , pattern CAnd
  , pattern CEq
  , pattern CEx
  , pattern CNew
  , pattern CEdge
  , pattern CQuery
  , pattern COne

  , Label
  , Node
  ) where

import Data.Void
import Data.List
import Data.List.Extras.Pair
import Data.Functor.Fixedpoint

import Control.Unification
import Control.Unification.STVar

import Statix.Regex
import Statix.Graph.Paths

type Node   = String
type Label  = String
type RawVar = String

data TermF n r
  = TConF String [r]
  | TNodeF n
  | TLabelF Label
  | TVarF RawVar
  | TAnswerF [Path n Label]
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show n, Show r) ⇒ Show (TermF n r) where
  show (TConF c ts) = c ++ "(" ++ (intercalate ", " $ fmap show ts) ++ ")"
  show (TNodeF n)   = show n

  show (TLabelF l)  = show l
  show (TVarF x)    = x
  show (TAnswerF ps) = "ζ"

instance Eq n => Unifiable (TermF n) where
  -- One step of the unfication algorithm.
  -- Answers are not unifiable.
  zipMatch (TConF c ts) (TConF c' ts')
    | c /= c'   = Nothing
    | otherwise = TConF c <$> pairWith (\l r -> Right(l , r)) ts ts'
  zipMatch (TNodeF n) (TNodeF m)
    | n == m    = Just (TNodeF n)
    | otherwise = Nothing
  zipMatch (TLabelF l) (TLabelF k)
    | l == k    = Just (TLabelF l)
    | otherwise = Nothing
  zipMatch (TVarF x) (TVarF y)
    | x == y    = Just (TVarF x)
    | otherwise = Nothing
  zipMatch _ _ = Nothing

-- convert some raw, syntactic variables monadically to semantic variables
cook :: (RawVar → Maybe v) → UTerm (TermF n) v → UTerm (TermF n) v
cook f (UVar x)  = UVar x
cook f (UTerm t) = _cook t
  where
    _cook (TConF c ts) = let ts' = map (cook f) ts in Con c ts'
    _cook (TVarF x) = case f x of
      Just v  → UVar v
      Nothing → Var x

-- Statix internal terms
type Term n v = UTerm (TermF n) v
pattern Con c ts = UTerm (TConF c ts)
pattern Node n   = UTerm (TNodeF n)
pattern Label l  = UTerm (TLabelF l)
pattern Var x    = UTerm (TVarF x)
pattern Answer ps = UTerm (TAnswerF ps)

-- Statix surface terms
type RawTerm = Fix (TermF Void)
pattern RCon c ts = Fix (TConF c ts)
pattern RLabel l  = Fix (TLabelF l)
pattern RVar x    = Fix (TVarF x)

data ConstraintF t r
  = CTrueF | CFalseF
  | CAndF r r
  | CEqF t t
  | CExF [String] r
  | CNewF t
  | CEdgeF t Label t
  | CQueryF t (Regex Label) String
  | COneF String t
  deriving (Show, Functor)

type Constraint t = Fix (ConstraintF t)
pattern CTrue    = Fix CTrueF
pattern CFalse   = Fix CFalseF
pattern CAnd l r = Fix (CAndF l r)
pattern CEq :: t → t → Constraint t
pattern CEq l r  = Fix (CEqF l r)
pattern CEx ns c = Fix (CExF ns c)
pattern CNew t   = Fix (CNewF t)
pattern CEdge n l m = Fix (CEdgeF n l m)
pattern CQuery t re x = Fix (CQueryF t re x)
pattern COne x t = Fix (COneF x t)

type RawConstraint = Constraint RawTerm

type Constraints  t = [Constraint t]
