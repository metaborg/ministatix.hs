{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Statix.Syntax.Constraint where

import Data.Void
import Data.List as List
import Data.List.Extras.Pair
import Data.Functor.Fixedpoint
import Data.HashMap.Strict as HM

import Control.Unification
import Control.Unification.STVar

import Statix.Regex
import Statix.Graph.Types
import Statix.Graph.Paths

------------------------------------------------------------------
-- | Some primitives

type Node     = String

newtype Label = Lab String deriving (Eq, Ord)
instance Show Label where
  show (Lab l) = l

type RawName  = String           -- raw references to existential vars and predicates
type Symbol   = String           -- constructor names

type ModName  = String           -- module names
type QName    = (String, String) -- qualified predicate names (module, raw)

------------------------------------------------------------------
-- | The term language

data TermF n r
  = TConF Symbol [r]
  | TNodeF n
  | TLabelF Label
  | TVarF RawName
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
cook :: (RawName → Maybe (UTerm (TermF n) v)) → UTerm (TermF n) v → UTerm (TermF n) v
cook f (UVar x)  = UVar x
cook f (UTerm t) = _cook t
  where
    _cook (TConF c ts) = let ts' = fmap (cook f) ts in Con c ts'
    _cook (TVarF x) = case f x of
      Just t  → t
      Nothing → Var x
    _cook (TAnswerF a) = Answer a
    _cook (TNodeF n) = Node n
    _cook (TLabelF l) = Label l

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

data ConstraintF p t r
  = CTrueF | CFalseF
  | CAndF r r
  | CEqF t t
  | CExF [RawName] r
  | CNewF t
  | CEdgeF t Label t
  | CQueryF t (Regex Label) RawName
  | COneF RawName t
  | CApplyF p [t]
  deriving (Functor, Foldable, Traversable)

instance (Show p, Show t, Show r) ⇒ Show (ConstraintF p t r) where

  show CTrueF  = "⊤"
  show CFalseF = "⊥"
  show (CEqF t₁ t₂) = show t₁ ++ "=" ++ show t₂
  show (CExF ns c) = "∃ " ++ intercalate ", " (fmap show ns) ++ ". " ++ show c
  show (CNewF t)  = "∇ (" ++ show t ++ ")"
  show (CEdgeF t l t') = show t ++ "─⟨ " ++ show l ++ " ⟩⟶" ++ show t'
  show (CQueryF t r s) = show t ++ "(" ++ show r ++ ")" ++ s
  show (COneF x t) = "one(" ++ x ++ "," ++ show t ++ ")"
  show (CApplyF p ts) = show p ++ "(" ++ intercalate ", " (fmap show ts) ++ ")"

type Constraint p t = Fix (ConstraintF p t)

tmapc_ :: (t → s) → ConstraintF p t (Constraint p s) → Constraint p s
tmapc_ f (CEqF t₁ t₂) = CEq (f t₁) (f t₂)
tmapc_ f (CNewF t) = CNew (f t)
tmapc_ f (CEdgeF t₁ l t₂) = CEdge (f t₁) l (f t₂)
tmapc_ f (CAndF c d) = CAnd c d
tmapc_ f (CExF ns c) = CEx ns c
tmapc_ f (CQueryF t r x) = CQuery (f t) r x
tmapc_ f (COneF x t) = COne x (f t)
tmapc_ f (CApplyF p ts) = CApply p (fmap f ts)

tmapc :: (t → s) → Constraint p t → Constraint p s
tmapc f = cata (tmapc_ f)

pattern CTrue    = Fix CTrueF
pattern CFalse   = Fix CFalseF
pattern CAnd l r = Fix (CAndF l r)
pattern CEq l r  = Fix (CEqF l r)
pattern CEx ns c = Fix (CExF ns c)
pattern CNew t   = Fix (CNewF t)
pattern CEdge n l m = Fix (CEdgeF n l m)
pattern CQuery t re x = Fix (CQueryF t re x)
pattern COne x t = Fix (COneF x t)
pattern CApply p ts = Fix (CApplyF p ts)

type RawConstraint = Constraint RawName RawTerm
type Constraints p t = [Constraint p t]

------------------------------------------------------------------
-- | Predicates and modules

data Signature = Sig
  { enclMod  :: ModName
  , predname :: RawName
  , params   :: [RawName]}

qname :: Signature → QName
qname sig = (enclMod sig, predname sig)

instance Show Signature where
  show (Sig m p ns) = m ++ "." ++ p ++ "(" ++ intercalate "," (reverse ns) ++ ")"

data Predicate p = Pred
  { sig      :: Signature
  , body     :: Constraint p RawTerm
  } deriving (Show)
