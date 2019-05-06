module Statix.Syntax.Terms where

import Data.Text (Text, unpack)
import Data.Hashable
import Data.Functor.Fixedpoint

import ATerms.Syntax.ATerm
import Statix.Analysis.Lexical as Lexical

------------------------------------------------------------------
-- | Some primitives

type Node  = String
type Ident = Text
type IPath = Lexical.Path Ident
newtype Label = Lab Text deriving (Eq, Ord)

instance Hashable Label where
  hashWithSalt salt (Lab txt) = hashWithSalt salt txt

instance Show Label where
  show (Lab l) = unpack l

------------------------------------------------------------------
-- | The term language

data TermF ℓ r
  = TTmF (ATermF r)
  | TLabelF Label (Maybe r)
  | TVarF ℓ 
  | TPathConsF ℓ r r
  | TPathEndF ℓ
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show ℓ, Show r) ⇒ Show (TermF ℓ r) where
  show (TTmF t)           = show t
  show (TLabelF l t)      = "`" ++ show l ++ "(" ++ show t ++ ")"
  show (TVarF x)          = show x
  show (TPathConsF n l p) = show n ++ " ▻ " ++ show l ++ " ▻ " ++ show p
  show (TPathEndF l)      = show l ++ " ◅"

fromATerm :: ATerm → Fix (TermF ℓ)
fromATerm = cata (Fix . TTmF)

type TermF₀ r         = TermF Ident r
type TermF₁ r         = TermF IPath r

type Term₀            = Fix (TermF Ident)
type Term₁            = Fix (TermF IPath)

funcTm :: Text → [Fix (TermF ℓ)] → Fix (TermF ℓ)
funcTm c ts = Fix (TTmF (AFuncF c ts))

consTm :: Fix (TermF ℓ) → Fix (TermF ℓ) → Fix (TermF ℓ)
consTm t ts = Fix (TTmF (AConsF t ts))

nilTm :: Fix (TermF ℓ)
nilTm = Fix (TTmF ANilF)

tupleTm :: [Fix (TermF ℓ)] → Fix (TermF ℓ)
tupleTm ts = Fix (TTmF (ATupleF ts))

unitTm :: Fix (TermF ℓ)
unitTm = Fix (TTmF (ATupleF []))

wildcardTm :: Fix (TermF ℓ)
wildcardTm = Fix (TTmF AWildCardF)

pattern TTm t         = Fix (TTmF t)
pattern Label l t     = Fix (TLabelF l t)
pattern Var x         = Fix (TVarF x)
pattern PathCons t l t'   = Fix (TPathConsF t l t')
pattern PathEnd l         = Fix (TPathEndF l)
