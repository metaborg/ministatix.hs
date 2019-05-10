module Statix.Syntax.Constraint where

import Prelude hiding (lookup)
import Data.HashMap.Strict (HashMap, lookup)
import Data.List (concatMap, intercalate)
import Data.Functor.Fixedpoint
import Data.Maybe

import Control.Lens
import Control.Applicative

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

pattern CTrue         = Fix CTrueF
pattern CFalse        = Fix CFalseF
pattern CAnd l r      = Fix (CAndF l r)
pattern CEq l r       = Fix (CEqF l r)
pattern CNotEq l r    = Fix (CNotEqF l r)
pattern CEx ns c      = Fix (CExF ns c)
pattern CNew t t'     = Fix (CNewF t t')
pattern CData x t     = Fix (CDataF x t)
pattern CEdge n l m   = Fix (CEdgeF n l m)
pattern CQuery t re x = Fix (CQueryF t re x)
pattern COne x t      = Fix (COneF x t)
pattern CNonEmpty x   = Fix (CNonEmptyF x)
pattern CEvery x b    = Fix (CEveryF x b)
pattern CMin x p t    = Fix (CMinF x p t)
pattern CFilter x p t = Fix (CFilterF x p t)
pattern CApply p ts   = Fix (CApplyF p ts)
pattern CMatch t br   = Fix (CMatchF t br)

instance (Show ℓ, Show p, Show t, Show r) ⇒ Show (ConstraintF p ℓ t r) where

  show CTrueF          = "⊤"
  show CFalseF         = "⊥"
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

type Constraint p ℓ t = Fix (ConstraintF p ℓ t)

tmapc :: (t → s) → Constraint p ℓ t → Constraint p ℓ s
tmapc f = cata (tmapc_ f)
  where
    tmapc_ :: (t → s) → ConstraintF p ℓ t (Constraint p ℓ s) → Constraint p ℓ s
    tmapc_ f (CTrueF)         = CTrue
    tmapc_ f (CFalseF)        = CFalse
    tmapc_ f (CEqF t₁ t₂)     = CEq (f t₁) (f t₂)
    tmapc_ f (CNotEqF t₁ t₂)  = CNotEq (f t₁) (f t₂)
    tmapc_ f (CNewF n t)      = CNew n (f t)
    tmapc_ f (CDataF l t)     = CData l (f t)
    tmapc_ f (CEdgeF n₁ l n₂) = CEdge n₁ (f l) n₂
    tmapc_ f (CAndF c d)      = CAnd c d
    tmapc_ f (CExF ns c)      = CEx ns c
    tmapc_ f (CQueryF x r y)  = CQuery x r y
    tmapc_ f (COneF x t)      = COne x (f t)
    tmapc_ f (CNonEmptyF x)   = CNonEmpty x
    tmapc_ f (CEveryF x (Branch m c)) = CEvery x (Branch (fmap f m) c)
    tmapc_ f (CMinF x p t)    = CMin x p t
    tmapc_ f (CFilterF x p t) = CFilter x (fmap f p) t
    tmapc_ f (CApplyF p ts)   = CApply p (fmap f ts)
    tmapc_ f (CMatchF t br)   =
      CMatch (f t) (fmap (\(Branch m c) → Branch (fmap f m) c) br)

tsequencec :: (Applicative f) ⇒ Constraint p ℓ (f t) → f (Constraint p ℓ t)
tsequencec = cata tsequencec_
  where
    tseqb :: (Applicative f) ⇒ Branch (f t) (f c) → f (Branch t c)
    tseqb (Branch t c) = liftA2 Branch (sequenceA t) c

    tsequencec_ :: (Applicative f) ⇒ ConstraintF p ℓ (f t) (f (Constraint p ℓ t)) → f (Constraint p ℓ t)
    tsequencec_ (CTrueF)         = pure CTrue
    tsequencec_ (CFalseF)        = pure CFalse
    tsequencec_ (CEqF t₁ t₂)     = liftA2 CEq t₁ t₂
    tsequencec_ (CNotEqF t₁ t₂)  = liftA2 CNotEq t₁ t₂
    tsequencec_ (CNewF n t)      = pure (CNew n) <*> t
    tsequencec_ (CDataF l t)     = pure (CData l) <*> t
    tsequencec_ (CEdgeF n₁ l n₂) = pure (\t → CEdge n₁ t n₂) <*> l
    tsequencec_ (CAndF c d)      = liftA2 CAnd c d
    tsequencec_ (CExF ns c)      = pure (CEx ns) <*> c
    tsequencec_ (CQueryF x r y)  = pure (CQuery x r y)
    tsequencec_ (COneF x t)      = pure (COne x) <*> t
    tsequencec_ (CNonEmptyF x)   = pure (CNonEmpty x)
    tsequencec_ (CEveryF x b)    = pure (CEvery x) <*> (tseqb b)
    tsequencec_ (CMinF x p t)    = pure (CMin x p t)
    tsequencec_ (CFilterF x p t) = pure (\p → CFilter x p t) <*> sequenceA p
    tsequencec_ (CApplyF p ts)   = pure (CApply p) <*> sequenceA ts
    tsequencec_ (CMatchF t brs)  = liftA2 (\t brs → CMatch t brs) t (sequenceA $ fmap tseqb brs)

------------------------------------------------------------------
-- | Predicates and modules

data Predicate σ c = Pred
  { _qname    :: QName
  , _sig      :: [σ]
  , _body     :: c
  } deriving (Show)

data Module σ c = Mod 
  { _moduleName    :: Ident
  , _moduleImports :: [Ident]
  , _definitions   :: HashMap Ident (Predicate σ c) }
  deriving (Show)

type ConstraintF₀ r = ConstraintF Ident Ident Term₀ r     -- parsed
type ConstraintF₁ r = ConstraintF QName IPath Term₁ r     -- named

type Branch₀        = Branch Term₀ Constraint₀
type Branch₁        = Branch Term₁ Constraint₁

type Constraint₀    = Constraint Ident  Ident Term₀
type Constraint₁    = Constraint QName  IPath Term₁

type Predicate₀     = Predicate Ident Constraint₀
type Predicate₁     = Predicate Ident Constraint₁
type Predicate₂     = Predicate (Ident,Type) Constraint₁

type Module₀        = Module Ident Constraint₀
type Module₁        = Module Ident Constraint₁
type Module₂        = Module (Ident, Type) Constraint₁

type SymbolTable σ c = HashMap Ident (Module σ c)
type SymbolTable₀   = SymbolTable Ident Constraint₀
type SymbolTable₁   = SymbolTable Ident Constraint₁
type SymbolTable₂   = SymbolTable (Ident, Type) Constraint₁

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
