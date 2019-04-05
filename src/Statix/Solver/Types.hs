module Statix.Solver.Types where

import Prelude hiding (lookup, null)
import Data.Text
import Data.List as List
import Data.Map.Strict as Map hiding (map, null)
import Data.STRef
import qualified Data.Sequence as Seq
import Data.HashMap.Strict as HM
import Data.Coerce
import Data.Functor.Fixedpoint
import Data.Default
import Data.UnionFind.ST

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans

import Statix.Regex
import Statix.Graph
import Statix.Graph.Types as Graph
import Statix.Syntax.Constraint
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical
import Statix.Solver.Unification
import Statix.Solver.Unification.ST

-- | Graph node references in ST 
type SNode s = STNodeRef s Label (SDag s)

-- | Graph paths in ST
type SPath s = Graph.Path (SNode s) Label

-- | Some information about the source of variables
type VarInfo = Text

-- | Solver DAG in ST
type SDag s   = TGraph (STmRef s) (STermF s) VarInfo
type STmRef s = Class s (STermF s) VarInfo

-- | The constructors of the term language
data STermF s c =
    SNodeF (SNode s)
  | SLabelF Label
  | SConF Ident [c]
  | SAnsF [SPath s]
 
pattern SNode n    = GTm (SNodeF n)
pattern SLabel l   = GTm (SLabelF l)
pattern SCon id ts = GTm (SConF id ts)
pattern SAns ps    = GTm (SAnsF ps)

instance Unifiable (STermF s) where

  zipMatch (SNodeF n) (SNodeF m)
    | n == m    = Just []
    | otherwise = Nothing
  zipMatch (SConF k₁ ts₁) (SConF k₂ ts₂)
    | k₁ == k₂ =
      if List.length ts₁ == List.length ts₂
        then Just (List.zip ts₁ ts₂)
        else Nothing
    | otherwise = Nothing
  zipMatch (SLabelF l₁) (SLabelF l₂)
    | l₁ == l₂  = Just []
    | otherwise = Nothing

  -- unifying answer sets is prohibited
  zipMatch (SAnsF _) (SAnsF _) = Nothing

  -- other combinations are constructor clashes
  zipMatch _ _ = Nothing

  children (SConF id ts) = ts
  children _ = []

{- READER -}
type Frame s = HashMap Ident (STmRef s)
data Env s = Env
 { symbols :: SymTab
 , locals  :: [Frame s]
 }

instance Default (Frame s) where
  def = HM.empty

instance Default (Env s) where
  def = Env HM.empty [def]

getPredicate :: QName → Env s → Maybe Predicate₁
getPredicate qn env = HM.lookup qn (symbols env)

{- ERROR -}
data StatixError =
  Unsatisfiable String
  | TypeError
  | Panic String

instance Show StatixError where
  show (Unsatisfiable x) = "Constraint unsatisfiable: " ++ x
  show TypeError = "Constraint unsatisfiable: type error"
  show (Panic x) = "Panic" ++ x
 
instance UnificationError StatixError where
  symbolClash = Unsatisfiable "Symbol clash"
  cyclicTerm  = Unsatisfiable "Cyclic term"

{- STATE -}
data Solver s = Solver
  { queue :: Seq.Seq (Goal s)
  , nextU :: Int
  , nextN :: Int
  , graph :: STGraph s Label (SDag s)
  }

emptySolver :: Solver s
emptySolver = Solver
  { queue = Seq.empty
  , nextU = 0
  , nextN = 0
  , graph = []
  }

-- | The monad that we use to solve Statix constraints
type SolverM s = ReaderT (Env s) (StateT (Solver s) (ExceptT StatixError (ST s)))

-- | Constraint closure
type Goal s    = (Env s, Constraint₁)

-- | (ST-less) solution to a constraint program
type Solution = Either StatixError (String, IntGraph Label String)
