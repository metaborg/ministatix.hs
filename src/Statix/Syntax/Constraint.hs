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
import Statix.Graph.Types
import Statix.Graph.Paths
import Statix.Analysis.Lexical as Lexical

import Unification

------------------------------------------------------------------
-- | Some primitives

type Node     = String

newtype Label = Lab Text deriving (Eq, Ord)
instance Hashable Label where
  hashWithSalt salt (Lab txt) = hashWithSalt salt txt

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
  | TPathConsF ℓ r r
  | TPathEndF ℓ
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show ℓ, Show r) ⇒ Show (TermF ℓ r) where
  show (TConF c ts)  = show c ++ "(" ++ (intercalate ", " $ fmap show ts) ++ ")"
  show (TLabelF l)   = "`" ++ show l
  show (TVarF x)     = show x
  show (TPathConsF n l p) = show n ++ " ▻ " ++ show l ++ " ▻ " ++ show p
  show (TPathEndF l)      = show l ++ " ◅"

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
  = CTrueF | CFalseF
  | CAndF r r | CEqF t t | CExF [Ident] r
  | CNewF ℓ | CDataF ℓ t | CEdgeF ℓ Label ℓ
  | CQueryF ℓ (Regex Label) ℓ
  | COneF ℓ t | CEveryF ℓ (Branch t r) | CMinF ℓ PathComp ℓ | CFilterF ℓ (PathFilter t) ℓ
  | CApplyF p [t] | CMatchF t [Branch t r]
  deriving (Functor, Foldable, Traversable)

instance (Show ℓ, Show p, Show t, Show r) ⇒ Show (ConstraintF p ℓ t r) where

  show CTrueF          = "⊤"
  show CFalseF         = "⊥"
  show (CAndF c₁ c₂)   = show c₁ ++ ", " ++ show c₂
  show (CEqF t₁ t₂)    = show t₁ ++ " = " ++ show t₂
  show (CExF ns c)     = "{ " ++ intercalate ", " (fmap show ns) ++ "} " ++ show c
  show (CNewF t)       = "new " ++ show t
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
    tmapc_ f (CNewF n)        = CNew n
    tmapc_ f (CDataF l t)     = CData l (f t)
    tmapc_ f (CEdgeF n₁ l n₂) = CEdge n₁ l n₂
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

fv :: (Hashable ℓ, Eq ℓ) ⇒ Fix (TermF ℓ) → HashSet ℓ
fv = cata fvF
  where
    fvF (TConF k ℓs)         = HSet.unions ℓs
    fvF (TVarF ℓ)            = HSet.singleton ℓ
    fvF (TPathConsF ℓ r₁ r₂) = HSet.singleton ℓ `HSet.union` r₁ `HSet.union` r₂
    fvF (TPathEndF ℓ)        = HSet.singleton ℓ
    fvF _                    = HSet.empty

------------------------------------------------------------------
-- | Predicates and modules

-- | Node permission modes:
-- `In` denotes that the node requires extension permission.
-- `Out` denotes that we have extension permission on the variable.
-- `InOut` means we both require and have extension permission.
data Mode
  = None
  | Out
  | In    (Set Label)
  | InOut (Set Label) deriving (Eq, Show)

modeJoin :: Mode → Mode → Mode
modeJoin m None             = m
modeJoin None m             = m
modeJoin (In ls) (In ks)    = In (ls `Set.union` ks)
modeJoin (In ls) Out        = In ls
modeJoin Out (In ls)        = In ls
modeJoin Out Out            = Out
modeJoin (InOut ks) (In ls) = InOut (ls `Set.union` ks)
modeJoin (In ls) (InOut ks) = InOut (ls `Set.union` ks)
modeJoin (InOut ks) Out     = InOut ks
modeJoin Out (InOut ks)     = InOut ks
modeJoin (InOut ls) (InOut ks) = InOut (ls `Set.union` ks)

data Type
  = TNode Mode
  | TPath
  | TLabel
  | TAns
  | TBot deriving (Eq)

instance Unifiable (Const Type) where

  zipMatch (Const (TNode m)) (Const (TNode n))
    = Just (Const (TNode (modeJoin m n)))
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
pattern PathCons t l t'   = Fix (TPathConsF t l t')
pattern PathEnd l         = Fix (TPathEndF l)

type ConstraintF₀ r   = ConstraintF Ident Ident Term₀ r -- parsed
type ConstraintF₁ r   = ConstraintF QName IPath Term₁ r -- named

type Branch₀          = Branch Term₀ Constraint₀ -- parsed
type Branch₁          = Branch Term₁ Constraint₁ -- named

type Constraint₀      = Constraint Ident  Ident Term₀ -- parsed
type Constraint₁      = Constraint QName  IPath Term₁ -- named

pattern CTrue         = Fix CTrueF
pattern CFalse        = Fix CFalseF
pattern CAnd l r      = Fix (CAndF l r)
pattern CEq l r       = Fix (CEqF l r)
pattern CEx ns c      = Fix (CExF ns c)
pattern CNew t        = Fix (CNewF t)
pattern CData x t     = Fix (CDataF x t)
pattern CEdge n l m   = Fix (CEdgeF n l m)
pattern CQuery t re x = Fix (CQueryF t re x)
pattern COne x t      = Fix (COneF x t)
pattern CEvery x b    = Fix (CEveryF x b)
pattern CMin x p t    = Fix (CMinF x p t)
pattern CFilter x p t = Fix (CFilterF x p t)
pattern CApply p ts   = Fix (CApplyF p ts)
pattern CMatch t br   = Fix (CMatchF t br)

type Predicate₀       = Predicate Ident   Ident   Term₀ -- parsed
type Predicate₁       = Predicate QName   IPath   Term₁ -- named & optionally typed

data RawModule = Mod 
  { moduleName    :: Ident
  , moduleImports :: [Ident]
  , definitions   :: [Predicate₀] }
  deriving (Show)
