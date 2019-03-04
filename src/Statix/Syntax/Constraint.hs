{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

{-

Tutorial on unification-fd package can be found here:
https://winterkoninkje.dreamwidth.org/tag/unification

-}

module Statix.Syntax.Constraint
  ( TermF
  , ConstraintF
  , RawVar

  {- Solver terms-}
  , Term
  , pattern Con
  , pattern Node
  , pattern Label
  , pattern Var
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

  , Token(..)
  , Label
  , Node
  ) where

import Data.List.Extras.Pair
import Data.Functor.Fixedpoint

import Control.Unification
import Control.Unification.STVar

type Node   = String
type Label  = String
type RawVar = String

data TermF n r
  = TConF String [r]
  | TNodeF n
  | TLabelF Label
  | TVarF RawVar
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Eq n => Unifiable (TermF n) where
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
  zipMatch (TVarF x) (TVarF y)
    | x == y    = Just (TVarF x)
    | otherwise = Nothing
  zipMatch _ _ = Nothing

cook :: (RawVar → Maybe v) → UTerm (TermF n) v → Maybe (UTerm (TermF n) v)
cook f (UVar x)  = Just (UVar x)
cook f (UTerm t) = _cook t
  where
    _cook (TConF c ts) = do
      ts' ← mapM (\t → cook f t) ts
      return (Con c ts')
    _cook (TVarF x) = UVar <$> f x

-- Statix internal terms
type Term n v = UTerm (TermF n) v
pattern Con c ts = UTerm (TConF c ts)
pattern Node n   = UTerm (TNodeF n)
pattern Label l  = UTerm (TLabelF l)
pattern Var x    = UTerm (TVarF x)

data ConstraintF t r
  = CTrueF | CFalseF
  | CAndF r r
  | CEqF t t
  | CExF [String] r
  | CNewF t
  | CEdgeF t Label t
  deriving Show

type Constraint t = Fix (ConstraintF t)
pattern CTrue    = Fix CTrueF
pattern CFalse   = Fix CFalseF
pattern CAnd l r = Fix (CAndF l r)
pattern CEq :: t → t → Constraint t
pattern CEq l r  = Fix (CEqF l r)
pattern CEx ns c = Fix (CExF ns c)
pattern CNew t   = Fix (CNewF t)
pattern CEdge n l m = Fix (CEdgeF n l m)

type Constraints  t = [Constraint t]

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