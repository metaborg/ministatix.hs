module Statix.Syntax.Constraint where

import Prelude hiding (lookup)

import Data.HashMap.Strict (HashMap, lookup)
import Data.List (concatMap, intercalate)
import Data.Functor.Fixedpoint
import Data.Maybe
import Data.Functor.Compose

import Control.Lens
import Control.Monad

import ATerms.Syntax.Types

import Statix.Regex
import Statix.Syntax.Terms
import Statix.Syntax.Typing

type QName = (Ident, Ident)   -- qualified predicate names (module, raw)
type ModPath = String

showQName :: QName → String
showQName (mod, pred) = mod ++ "." ++ pred

------------------------------------------------------------------
-- | The constraint language

data Guard t = GEq t t | GNotEq t t
  deriving (Functor, Foldable, Traversable, Show)

data Matcher t    = Matcher [Ident] t [Guard t]
  deriving (Functor, Foldable, Traversable, Show)

data Branch t c   = Branch (Matcher t) c
  deriving (Functor, Foldable, Traversable, Show)

data PathComp     = Lex [(Label,Label)]
  deriving (Show)

data PathFilter t = MatchDatum (Matcher t)
  deriving (Functor, Foldable, Traversable, Show)

data ConstraintF p ℓ t r
  = CTrueF
  | CFalseF
  | CAndF r r
  | CEqF t t
  | CNotEqF t t
  | CExF [Ident] r
  | CNewF ℓ t
  | CDataF ℓ t
  | CEdgeF ℓ t ℓ
  | CQueryF ℓ (Regex Label) ℓ
  | COneF ℓ t
  | CNonEmptyF ℓ
  | CEveryF ℓ (Branch t r)
  | CMinF ℓ PathComp ℓ
  | CFilterF ℓ (PathFilter t) ℓ
  | CApplyF p [t]
  | CMatchF t [Branch t r]
  deriving (Functor, Foldable, Traversable)

instance (Show ℓ, Show p, Show t, Show r) ⇒ Show (ConstraintF p ℓ t r) where

  show CTrueF          = "true"
  show CFalseF         = "false"
  show (CAndF c₁ c₂)   = show c₁ ++ ", " ++ show c₂
  show (CEqF t₁ t₂)    = show t₁ ++ " == " ++ show t₂
  show (CNotEqF t₁ t₂) = show t₁ ++ " != " ++ show t₂
  show (CExF ns c)     = "{ " ++ intercalate ", " (fmap show ns) ++ "} " ++ show c
  show (CNewF t t')    = "new " ++ show t ++ " -> " ++ show t'
  show (CDataF l t)    = show l ++ " ↦ " ++ show t
  show (CEdgeF t l t') = show t ++ " ─[ " ++ show l ++ " ]-> " ++ show t'
  show (CApplyF p ts)  = show p ++ "(" ++ intercalate ", " (fmap show ts) ++ ")"
  show (CMatchF t bs)  = show t ++ " match " ++ (concatMap show bs)
  show (CQueryF t r s) = "query " ++ show t ++ " " ++ show r ++ " as " ++ show s
  show (COneF x t)     = "only(" ++ show x ++ "," ++ show t ++ ")"
  show (CNonEmptyF x)  = "inhabited(" ++ show x ++ ")"
  show (CEveryF y br)  = "every " ++ show y ++ "(" ++ show br ++ ")"
  show (CMinF x e v)   = "min " ++ show x ++ " " ++ show e ++ " " ++ show v
  show (CFilterF x e v)= "filter " ++ show x ++ " " ++ show e ++ " " ++ show v

------------------------------------------------------------------
-- | Predicates and modules

data Predicate σ c = Pred
  { _position :: Pos
  , _qname    :: QName
  , _sig      :: [σ]
  , _body     :: c
  } deriving (Show)

data Module σ c = Mod 
  { _moduleName    :: Ident
  , _moduleImports :: [Ident]
  , _definitions   :: HashMap Ident (Predicate σ c) }
  deriving (Show)

type ConstraintF₀     = ConstraintF Ident Ident Term₀     -- parsed
type ConstraintF₁     = ConstraintF QName IPath Term₁     -- named

type Branch₀          = Branch Term₀ Constraint₀
type Branch₁          = Branch Term₁ Constraint₁

type Annotated a f = Compose ((,) a) f

pattern AnnF :: a → f r → Annotated a f r
pattern AnnF a f = Compose (a, f)

pattern Ann :: a → f (Fix (Annotated a f)) → Fix (Annotated a f)
pattern Ann a f = Fix (Compose (a, f))

type Constraint p l t = Fix (Annotated Pos (ConstraintF p l t))
type Constraint₀      = Fix (Annotated Pos ConstraintF₀)
type Constraint₁      = Fix (Annotated Pos ConstraintF₁)

pattern CTrue an         = Ann an CTrueF
pattern CFalse an        = Ann an CFalseF
pattern CAnd an l r      = Ann an (CAndF l r)
pattern CEq an l r       = Ann an (CEqF l r)
pattern CNotEq an l r    = Ann an (CNotEqF l r)
pattern CEx an ns c      = Ann an (CExF ns c)
pattern CNew an t t'     = Ann an (CNewF t t')
pattern CData an x t     = Ann an (CDataF x t)
pattern CEdge an n l m   = Ann an (CEdgeF n l m)
pattern CQuery an t re x = Ann an (CQueryF t re x)
pattern COne an x t      = Ann an (COneF x t)
pattern CNonEmpty an x   = Ann an (CNonEmptyF x)
pattern CEvery an x b    = Ann an (CEveryF x b)
pattern CMin an x p t    = Ann an (CMinF x p t)
pattern CFilter an x p t = Ann an (CFilterF x p t)
pattern CApply an p ts   = Ann an (CApplyF p ts)
pattern CMatch an t br   = Ann an (CMatchF t br)

type FormalSig        = (Ident,Type,Mode)

type Predicate₀       = Predicate Ident Constraint₀
type Predicate₁       = Predicate Ident Constraint₁
type Predicate₂       = Predicate (Ident,Type) Constraint₁
type Predicate₃       = Predicate FormalSig Constraint₁

type Module₀          = Module Ident Constraint₀
type Module₁          = Module Ident Constraint₁
type Module₂          = Module (Ident, Type) Constraint₁

type SymbolTable σ c  = HashMap Ident (Module σ c)
type SymbolTable₀     = SymbolTable Ident Constraint₀
type SymbolTable₁     = SymbolTable Ident Constraint₁
type SymbolTable₂     = SymbolTable (Ident, Type) Constraint₁
type SymbolTable₃     = SymbolTable FormalSig Constraint₁

makeLenses ''Predicate
makeLenses ''Module

lookupPred :: QName → Getter (SymbolTable σ c) (Maybe (Predicate σ c))
lookupPred (mod, pred) = to f
  where
    f symtab = do
      (Mod _ _ defs) ← lookup mod symtab
      lookup pred defs

getPred :: QName → Getter (SymbolTable σ c) (Predicate σ c)
getPred qn = lookupPred qn . to fromJust

sigOf :: QName → Getter (SymbolTable σ c) [σ]
sigOf q = getPred q . sig

-- | Get the arity of a predicate
arityOf :: QName → Getter (SymbolTable σ c) Int
arityOf q = sigOf q.to length

eachFormal :: Traversal (SymbolTable σ c) (SymbolTable τ c) σ τ
eachFormal = each.definitions.each.sig.each
