{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Statix.Syntax.Constraint where

import Data.Void
import Data.Text as Text hiding (intercalate, reverse)
import Data.Default
import Data.List as List
import Data.List.Extras.Pair
import Data.Functor.Fixedpoint
import Data.HashMap.Strict as HM

import Statix.Regex
import Statix.Graph.Types
import Statix.Graph.Paths
import Statix.Analysis.Lexical as Lexical

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
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show ℓ, Show r) ⇒ Show (TermF ℓ r) where
  show (TConF c ts)  = show c ++ "(" ++ (intercalate ", " $ fmap show ts) ++ ")"
  show (TLabelF l)   = "`" ++ show l
  show (TVarF x)     = show x

------------------------------------------------------------------
-- | The constraint language

data ConstraintF p ℓ t r
  = CTrueF | CFalseF
  | CAndF r r
  | CEqF t t
  | CExF [Param] r
  | CNewF ℓ
  | CEdgeF ℓ Label ℓ
  | CQueryF ℓ (Regex Label) ℓ
  | COneF ℓ t
  | CApplyF p [t]
  deriving (Functor, Foldable, Traversable)

instance (Show ℓ, Show p, Show t, Show r) ⇒ Show (ConstraintF p ℓ t r) where

  show CTrueF  = "⊤"
  show CFalseF = "⊥"
  show (CEqF t₁ t₂) = show t₁ ++ "=" ++ show t₂
  show (CExF ns c) = "∃ " ++ intercalate ", " (fmap show ns) ++ ". " ++ show c
  show (CNewF t)  = "∇ (" ++ show t ++ ")"
  show (CEdgeF t l t') = show t ++ "─⟨ " ++ show l ++ " ⟩⟶" ++ show t'
  show (CQueryF t r s) = show t ++ "(" ++ show r ++ ")" ++ show s
  show (COneF x t) = "one(" ++ show x ++ "," ++ show t ++ ")"
  show (CApplyF p ts) = show p ++ "(" ++ intercalate ", " (fmap show ts) ++ ")"

type Constraint p ℓ t = Fix (ConstraintF p ℓ t)

tmapc_ :: (t → s) → ConstraintF p ℓ t (Constraint p ℓ s) → Constraint p ℓ s
tmapc_ f (CEqF t₁ t₂)     = CEq (f t₁) (f t₂)
tmapc_ f (CNewF n)        = CNew n
tmapc_ f (CEdgeF n₁ l n₂) = CEdge n₁ l n₂
tmapc_ f (CAndF c d)      = CAnd c d
tmapc_ f (CExF ns c)      = CEx ns c
tmapc_ f (CQueryF x r y)  = CQuery x r y
tmapc_ f (COneF x t)      = COne x (f t)
tmapc_ f (CApplyF p ts)   = CApply p (fmap f ts)

tmapc :: (t → s) → Constraint p ℓ t → Constraint p ℓ s
tmapc f = cata (tmapc_ f)

------------------------------------------------------------------
-- | Predicates and modules

data Type
  = TNode
  | TTerm
  | TPath
  | TAns
  | TBot

data Param = Param
  { pname     :: Ident
  , requires  :: [Label] -- requires ℓ-permission for l ∈ requires
  , sort      :: Type
  }

instance Eq Param where
  (==) l r = pname l == pname r

instance Default Param where
  def = Param Text.empty [] TBot

instance Show Type where
  show TTerm = "Term"
  show TPath = "Path"
  show TAns  = "{Path}"
  show TBot  = "⊥"

instance Show Param where
  show (Param n reqs τ) = show n ++ ": " ++ show τ

data Signature = Sig
  { enclMod  :: Ident
  , predname :: Ident
  , params   :: [Param] }

qname :: Signature → QName
qname sig = (enclMod sig, predname sig)

instance Show Signature where
  show (Sig m p ns) =
    show m
    ++ "." ++ show p
    ++ "(" ++ intercalate "," (fmap show $ reverse ns) ++ ")"

data Predicate p ℓ t = Pred
  { sig      :: Signature
  , body     :: Constraint p ℓ t
  } deriving (Show)

type TermF₀ r         = TermF Ident r
type TermF₁ r         = TermF IPath r

type Term₀            = Fix (TermF Ident)
type Term₁            = Fix (TermF IPath)

pattern Con c ts      = Fix (TConF c ts)
pattern Label l       = Fix (TLabelF l)
pattern Var x         = Fix (TVarF x)

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
pattern CApply p ts   = Fix (CApplyF p ts)

type Predicate₀       = Predicate Ident   Ident   Term₀ -- parsed
type Predicate₁       = Predicate QName   IPath   Term₁ -- named & optionally typed
