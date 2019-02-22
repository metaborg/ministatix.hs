{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

{-

Tutorial on unification-fd package can be found here:
https://winterkoninkje.dreamwidth.org/tag/unification

-}

module Statix.Syntax.Constraint
  ( TermF
  , ConstraintF

  {- Solver terms-}
  , Term
  , pattern Con
  , pattern Node
  , pattern Label
  , pattern Var

  {- Constraint syntax -}
  , Constraint
  , pattern CTrue
  , pattern CFalse
  , pattern CAnd
  , pattern CEq
  , pattern CEx
  , pattern CNew
  , pattern CEdge

  , Token(..)
  , Label
  , Node
  ) where

import Data.List.Extras.Pair
import Data.Functor.Fixedpoint
import Control.Unification
import Control.Unification.IntVar

type Node   = String
type Label  = String
type RawVar = String

data TermF r
  = TConF String [r]
  | TNodeF Node
  | TLabelF Label
  | TVarF RawVar
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Unifiable TermF where
  -- one step of the unfication algorithm
  zipMatch (TConF c ts) (TConF c' ts')
    | c /= c'   = Nothing
    | otherwise = TConF c <$> pairWith (\l r -> Right(l , r)) ts ts'
  zipMatch (TNodeF n) (TNodeF m)
    | n == m    = Just (TNodeF n)
    | otherwise = Nothing
  zipMatch (TLabelF l) (TLabelF k)
    | l == k    = Just (TLabelF l)
    | otherwise = Nothing
  zipMatch _ _ = Nothing

-- Statix internal terms
type Term = UTerm TermF IntVar
pattern Con c ts = UTerm (TConF c ts)
pattern Node n   = UTerm (TNodeF n)
pattern Label l  = UTerm (TLabelF l)
pattern Var x    = UTerm (TVarF x)

data ConstraintF t r
  = CTrueF | CFalseF
  | CAndF r r
  | CEqF t t
  | CExF [String] r
  | CNewF String
  | CEdgeF Term Label Term
  deriving Show

type Constraint = Fix (ConstraintF Term)
pattern CTrue    = Fix CTrueF
pattern CFalse   = Fix CFalseF
pattern CAnd l r = Fix (CAndF l r)
pattern CEq l r  = Fix (CEqF l r)
pattern CEx ns c = Fix (CExF ns c)
pattern CNew n   = Fix (CNewF n)
pattern CEdge n l m = Fix (CEdgeF n l m)

data Token
  = TokVar String
  | TokFalse
  | TokTrue
  | TokComma
  | TokEq
  | TokOpenBr
  | TokCloseBr
  | TokOpenB
  | TokCloseB
  | TokOpenSB
  | TokCloseSB
  | TokOpenArr
  | TokCloseArr
  | TokNew
  deriving Show
