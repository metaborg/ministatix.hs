{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Statix.Syntax.Constraint where

import Data.Void
import Data.List as List
import Data.List.Extras.Pair
import Data.Functor.Fixedpoint

import Control.Unification
import Control.Unification.STVar

import Statix.Regex
import Statix.Graph.Types
import Statix.Graph.Paths

------------------------------------------------------------------
-- | Some primitives

type Node     = String

newtype Label = Lab String deriving (Eq)
instance Show Label where
  show (Lab l) = l

type VarName  = String
type ConName  = String
type PredName = String

------------------------------------------------------------------
-- | The term language

data TermF n r
  = TConF ConName [r]
  | TNodeF n
  | TLabelF Label
  | TVarF VarName
  | TAnswerF [Path n Label]
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show n, Show r) ⇒ Show (TermF n r) where
  show (TConF c ts) = c ++ "(" ++ (intercalate ", " $ fmap show ts) ++ ")"
  show (TNodeF n)   = "Node(" ++ show n ++ ")"

  show (TLabelF l)  = "`" ++ show l
  show (TVarF x)    = x
  show (TAnswerF ps) = "{" ++ intercalate ", " (fmap show ps) ++ "}"

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
cook :: (VarName → Maybe (UTerm (TermF n) v)) → UTerm (TermF n) v → UTerm (TermF n) v
cook f (UVar x)  = UVar x
cook f (UTerm t) = _cook t
  where
    _cook (TConF c ts) = let ts' = map (cook f) ts in Con c ts'
    _cook (TVarF x) = case f x of
      Just t  → t
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

------------------------------------------------------------------
-- | The constraint language

data ConstraintF t r
  = CTrueF | CFalseF
  | CAndF r r
  | CEqF t t
  | CExF [VarName] r
  | CNewF t
  | CEdgeF t Label t
  | CQueryF t (Regex Label) VarName
  | COneF VarName t
  | CApplyF PredName [t]
  deriving (Functor)

instance (Show t, Show r) ⇒ Show (ConstraintF t r) where

  show CTrueF  = "⊤"
  show CFalseF = "⊥"
  show (CEqF t₁ t₂) = show t₁ ++ "=" ++ show t₂
  show (CExF ns c) = "∃ " ++ intercalate ", " (fmap show ns) ++ ". " ++ show c
  show (CNewF t)  = "∇ (" ++ show t ++ ")"
  show (CEdgeF t l t') = show t ++ "─⟨ " ++ show l ++ " ⟩⟶" ++ show t'
  show (CQueryF t r s) = show t ++ "(" ++ show r ++ ")" ++ s
  show (COneF x t) = "one(" ++ x ++ "," ++ show t ++ ")"
  show (CApplyF p ts) = p ++ "(" ++ intercalate ", " (fmap show ts) ++ ")"

type Constraint t = Fix (ConstraintF t)

tmapc_ :: (t → s) → ConstraintF t (Constraint s) → Constraint s
tmapc_ f (CEqF t₁ t₂) = CEq (f t₁) (f t₂)
tmapc_ f (CNewF t) = CNew (f t)
tmapc_ f (CEdgeF t₁ l t₂) = CEdge (f t₁) l (f t₂)
tmapc_ f (CAndF c d) = CAnd c d
tmapc_ f (CExF ns c) = CEx ns c
tmapc_ f (CQueryF t r x) = CQuery (f t) r x
tmapc_ f (COneF x t) = COne x (f t)
tmapc_ f (CApplyF p ts) = CApply p (fmap f ts)

tmapc :: (t → s) → Constraint t → Constraint s
tmapc f = cata (tmapc_ f)

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
pattern CApply p ts = Fix (CApplyF p ts)

type RawConstraint = Constraint RawTerm
type Constraints t = [Constraint t]

------------------------------------------------------------------
-- | Predicates

data Predicate t = Pred
  { predname :: PredName
  , params   :: [VarName]
  , body     :: Constraint t
  } deriving (Show)

showSig :: Predicate t → String
showSig (Pred p ns _) = p ++ "(" ++ intercalate "," (reverse ns) ++ ")"

type Module t = [Predicate t]

showModuleContent :: Module t → String
showModuleContent mod = concatMap (\p → "  (defined " ++ (showSig p) ++ ")\n") mod
