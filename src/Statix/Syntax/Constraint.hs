module Statix.Syntax.Constraint where

import Data.Void
import Data.Text as Text hiding (intercalate, reverse)
import Data.Default
import Data.List as List
import Data.List.Extras.Pair
import Data.Functor.Fixedpoint
import Data.HashMap.Strict as HM
import Data.HashSet as HSet
import Data.Hashable
import Data.Set as Set

import Control.Applicative

import Statix.Regex
import Statix.Syntax.Terms
import Statix.Syntax.Typing
import Statix.Graph.Types
import Statix.Graph.Paths
import Statix.Analysis.Lexical as Lexical

import ATerms.Syntax.ATerm
import Unification

type QName = (Ident, Ident)   -- qualified predicate names (module, raw)
type ModPath   = Text

showQName :: QName → String
showQName (mod, pred) = unpack mod ++ "." ++ unpack pred

------------------------------------------------------------------
-- | The constraint language

data Matcher t    = Matcher [Ident] t [(t , t)]
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
  | CExF [Ident] r
  | CNewF ℓ t
  | CDataF ℓ t
  | CEdgeF ℓ t ℓ
  | CQueryF ℓ (Regex Label) ℓ
  | COneF ℓ t
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
pattern CEx ns c      = Fix (CExF ns c)
pattern CNew t t'     = Fix (CNewF t t')
pattern CData x t     = Fix (CDataF x t)
pattern CEdge n l m   = Fix (CEdgeF n l m)
pattern CQuery t re x = Fix (CQueryF t re x)
pattern COne x t      = Fix (COneF x t)
pattern CEvery x b    = Fix (CEveryF x b)
pattern CMin x p t    = Fix (CMinF x p t)
pattern CFilter x p t = Fix (CFilterF x p t)
pattern CApply p ts   = Fix (CApplyF p ts)
pattern CMatch t br   = Fix (CMatchF t br)

instance (Show ℓ, Show p, Show t, Show r) ⇒ Show (ConstraintF p ℓ t r) where

  show CTrueF          = "⊤"
  show CFalseF         = "⊥"
  show (CAndF c₁ c₂)   = show c₁ ++ ", " ++ show c₂
  show (CEqF t₁ t₂)    = show t₁ ++ " = " ++ show t₂
  show (CExF ns c)     = "{ " ++ intercalate ", " (fmap show ns) ++ "} " ++ show c
  show (CNewF t t')    = "new " ++ show t ++ " -> " ++ show t'
  show (CDataF l t)    = show l ++ " ↦ " ++ show t
  show (CEdgeF t l t') = show t ++ " ─[ " ++ show l ++ " ]-> " ++ show t'
  show (CApplyF p ts)  = show p ++ "(" ++ intercalate ", " (fmap show ts) ++ ")"
  show (CMatchF t bs)  = show t ++ " match " ++ (List.concatMap show bs)
  show (CQueryF t r s) = "query " ++ show t ++ " " ++ show r ++ " as " ++ show s
  show (COneF x t)     = "only(" ++ show x ++ "," ++ show t ++ ")"
  show (CEveryF y br)  = "every " ++ show y ++ "(" ++ show br ++ ")"
  show (CMinF x e v)   = "min " ++ show x ++ " " ++ show e ++ " " ++ show v
  show (CFilterF x e v) = "filter " ++ show x ++ " " ++ show e ++ " " ++ show v

type Constraint p ℓ t = Fix (ConstraintF p ℓ t)

tmapc :: (t → s) → Constraint p ℓ t → Constraint p ℓ s
tmapc f = cata (tmapc_ f)
  where
    tmapc_ :: (t → s) → ConstraintF p ℓ t (Constraint p ℓ s) → Constraint p ℓ s
    tmapc_ f (CTrueF)         = CTrue
    tmapc_ f (CFalseF)        = CFalse
    tmapc_ f (CEqF t₁ t₂)     = CEq (f t₁) (f t₂)
    tmapc_ f (CNewF n t)      = CNew n (f t)
    tmapc_ f (CDataF l t)     = CData l (f t)
    tmapc_ f (CEdgeF n₁ l n₂) = CEdge n₁ (f l) n₂
    tmapc_ f (CAndF c d)      = CAnd c d
    tmapc_ f (CExF ns c)      = CEx ns c
    tmapc_ f (CQueryF x r y)  = CQuery x r y
    tmapc_ f (COneF x t)      = COne x (f t)
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
    tsequencec_ (CNewF n t)      = pure (CNew n) <*> t
    tsequencec_ (CDataF l t)     = pure (CData l) <*> t
    tsequencec_ (CEdgeF n₁ l n₂) = pure (\t → CEdge n₁ t n₂) <*> l
    tsequencec_ (CAndF c d)      = liftA2 CAnd c d
    tsequencec_ (CExF ns c)      = pure (CEx ns) <*> c
    tsequencec_ (CQueryF x r y)  = pure (CQuery x r y)
    tsequencec_ (COneF x t)      = pure (COne x) <*> t
    tsequencec_ (CEveryF x b)    = pure (CEvery x) <*> (tseqb b)
    tsequencec_ (CMinF x p t)    = pure (CMin x p t)
    tsequencec_ (CFilterF x p t) = pure (\p → CFilter x p t) <*> sequenceA p
    tsequencec_ (CApplyF p ts)   = pure (CApply p) <*> sequenceA ts
    tsequencec_ (CMatchF t brs)  = liftA2 (\t brs → CMatch t brs) t (sequenceA $ fmap tseqb brs)

------------------------------------------------------------------
-- | Predicates and modules

type Signature = [(Ident, Type)]

data Predicate c = Pred
  { qname    :: QName
  , sig      :: Signature
  , body     :: c
  } deriving (Show)

data RawModule c = Mod 
  { moduleImports :: [ModPath]
  , definitions   :: [Predicate c] }

type ConstraintF₀ r   = ConstraintF Ident Ident Term₀ r -- parsed
type ConstraintF₁ r   = ConstraintF QName IPath Term₁ r -- named

type Branch₀          = Branch Term₀ Constraint₀ -- parsed
type Branch₁          = Branch Term₁ Constraint₁ -- named

type Constraint₀      = Constraint Ident  Ident Term₀ -- parsed
type Constraint₁      = Constraint QName  IPath Term₁ -- named

type Predicate₀       = Predicate Constraint₀
type Predicate₁       = Predicate Constraint₁

type RawModule₀       = RawModule Constraint₀
type RawModule₁       = RawModule Constraint₁
