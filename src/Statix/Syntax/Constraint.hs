{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Statix.Syntax.Constraint where

import Data.Void
import Data.Text as Text hiding (intercalate, reverse)
import Data.Default
import Data.List as List
import Data.List.Extras.Pair
import Data.Functor.Fixedpoint
import Data.HashMap.Strict as HM

import Control.Applicative

import Statix.Regex
import Statix.Graph.Types
import Statix.Graph.Paths
import Statix.Analysis.Lexical as Lexical

import Unification

------------------------------------------------------------------
-- | Some primitives

type Node     = String

newtype Label = Lab Text deriving (Eq, Ord)
instance Show Label where
  show (Lab l) = unpack l

type QName = (Ident, Ident)   -- qualified predicate names (module, raw)

type Ident = Text
type IPath = Lexical.Path Ident

------------------------------------------------------------------
-- | The term language

data TermF ℓ r
  = TConF Ident [r]
  | TLabelF Label
  | TVarF ℓ 
  | TPathF r Label r
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show ℓ, Show r) ⇒ Show (TermF ℓ r) where
  show (TConF c ts)  = show c ++ "(" ++ (intercalate ", " $ fmap show ts) ++ ")"
  show (TLabelF l)   = "`" ++ show l
  show (TVarF x)     = show x
  show (TPathF n l p)     = show n ++ " ▻ " ++ show l ++ " ▻ " ++ show p

------------------------------------------------------------------
-- | The constraint language

data ConstraintF p ℓ t r
  = CTrueF | CFalseF
  | CAndF r r
  | CEqF t t
  | CExF [Ident] r
  | CNewF ℓ
  | CEdgeF ℓ Label ℓ
  | CQueryF ℓ (Regex Label) ℓ
  | COneF ℓ t
  | CEveryF Ident ℓ r
  | CApplyF p [t]
  deriving (Functor, Foldable, Traversable)

instance (Show ℓ, Show p, Show t, Show r) ⇒ Show (ConstraintF p ℓ t r) where

  show CTrueF  = "⊤"
  show CFalseF = "⊥"
  show (CAndF c₁ c₂) = show c₁ ++ " ∧ " ++ show c₂
  show (CEqF t₁ t₂) = show t₁ ++ " = " ++ show t₂
  show (CExF ns c) = "∃ " ++ intercalate ", " (fmap show ns) ++ ". " ++ show c
  show (CNewF t)  = "∇ (" ++ show t ++ ")"
  show (CEdgeF t l t') = show t ++ "─⟨ " ++ show l ++ " ⟩⟶" ++ show t'
  show (CQueryF t r s) = show t ++ "(" ++ show r ++ ")" ++ show s
  show (COneF x t) = "one(" ++ show x ++ "," ++ show t ++ ")"
  show (CEveryF x y c) = "every " ++ show x ++ " in " ++ show y ++ "(" ++ show c ++ ")"
  show (CApplyF p ts) = show p ++ "(" ++ intercalate ", " (fmap show ts) ++ ")"

type Constraint p ℓ t = Fix (ConstraintF p ℓ t)

tmapc_ :: (t → s) → ConstraintF p ℓ t (Constraint p ℓ s) → Constraint p ℓ s
tmapc_ f (CTrueF)         = CTrue
tmapc_ f (CFalseF)        = CFalse
tmapc_ f (CEqF t₁ t₂)     = CEq (f t₁) (f t₂)
tmapc_ f (CNewF n)        = CNew n
tmapc_ f (CEdgeF n₁ l n₂) = CEdge n₁ l n₂
tmapc_ f (CAndF c d)      = CAnd c d
tmapc_ f (CExF ns c)      = CEx ns c
tmapc_ f (CQueryF x r y)  = CQuery x r y
tmapc_ f (COneF x t)      = COne x (f t)
tmapc_ f (CEveryF x y c)  = CEvery x y c
tmapc_ f (CApplyF p ts)   = CApply p (fmap f ts)

tmapc :: (t → s) → Constraint p ℓ t → Constraint p ℓ s
tmapc f = cata (tmapc_ f)

------------------------------------------------------------------
-- | Predicates and modules

-- | Node permission modes:
-- `In` denotes that the node requires extension permission.
-- `Out` denotes that we have extension permission on the variable.
-- `InOut` means we both require and have extension permission.
data Mode
  = None
  | Out
  | In
  | InOut deriving (Eq, Show)

modeJoin :: Mode → Mode → Mode
modeJoin m None = m
modeJoin None m = m

modeJoin In In   = In
modeJoin Out Out = Out

modeJoin _ _     = InOut

data Type
  = TNode Mode
  | TTerm
  | TPath
  | TLabel
  | TAns
  | TBot deriving (Eq)

instance Unifiable (Const Type) where

  zipMatch (Const (TNode m)) (Const (TNode n)) =
    Just (Const (TNode (modeJoin m n)))
  zipMatch ty ty'
    | ty == ty'         = Just ((\r → (r,r)) <$> ty)
    | ty == Const TBot  = Just ((\r → (r,r)) <$> ty')
    | ty' == Const TBot = Just ((\r → (r,r)) <$> ty)
    | otherwise = Nothing

instance Show Type where
  show (TNode m) = "Node " ++ show m
  show TPath = "Path"
  show TAns  = "{Path}"
  show TBot  = "⊥"
  show TLabel = "Label"

type Signature = [(Ident, Type)]

data Predicate p ℓ t = Pred
  { qname    :: QName
  , sig      :: Signature
  , body     :: Constraint p ℓ t
  } deriving (Show)

type TermF₀ r         = TermF Ident r
type TermF₁ r         = TermF IPath r

type Term₀            = Fix (TermF Ident)
type Term₁            = Fix (TermF IPath)

pattern Con c ts      = Fix (TConF c ts)
pattern Label l       = Fix (TLabelF l)
pattern Var x         = Fix (TVarF x)
pattern Path t l t'   = Fix (TPathF t l t')

type ConstraintF₀ r   = ConstraintF Ident Ident Term₀ r -- parsed
type ConstraintF₁ r   = ConstraintF QName IPath Term₁ r -- named & optionally typed

type Constraint₀      = Constraint Ident  Ident Term₀ -- parsed
type Constraint₁      = Constraint QName  IPath Term₁ -- named & optionally typed

pattern CTrue         = Fix CTrueF
pattern CFalse        = Fix CFalseF
pattern CAnd l r      = Fix (CAndF l r)
pattern CEq l r       = Fix (CEqF l r)
pattern CEx ns c      = Fix (CExF ns c)
pattern CNew t        = Fix (CNewF t)
pattern CEdge n l m   = Fix (CEdgeF n l m)
pattern CQuery t re x = Fix (CQueryF t re x)
pattern COne x t      = Fix (COneF x t)
pattern CEvery x y c  = Fix (CEveryF x y c)
pattern CApply p ts   = Fix (CApplyF p ts)

type Predicate₀       = Predicate Ident   Ident   Term₀ -- parsed
type Predicate₁       = Predicate QName   IPath   Term₁ -- named & optionally typed
