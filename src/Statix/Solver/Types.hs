{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
module Statix.Solver.Types where

import Prelude hiding (lookup, null)
import Data.Text
import Data.Map.Strict as Map hiding (map, null)
import Data.STRef
import Data.Sequence as Seq
import Data.HashMap.Strict as HM
import Data.Coerce
import Data.Functor.Fixedpoint

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans
import Control.Unification hiding (STVar)

import Statix.Regex
import Statix.Graph
import Statix.Graph.Types as Graph
import Statix.Syntax.Constraint
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical

-- | Unification variables in ST
data MVar s = MVar
  { ident :: !Int
  , ref   :: !(STRef s (Maybe (STerm s)))
  , name  :: Text
  }

instance Show (MVar s) where
  show (MVar _ _ n) = unpack n

instance Eq (MVar s) where
  (MVar i _ _) == (MVar j _ _) = (i == j)

-- | Graph node references in ST 
type SNode s   = STNodeRef s Label (STerm s)

-- | Graph paths in ST
type SPath s = Graph.Path (SNode s) Label

-- | Solver terms in ST
type STerm s    = Fix (STermF s)
data STermF s r =
    SVarF (MVar s)
  | SNodeF (SNode s)
  | SLabelF Label
  | SConF Ident [r]
  | SAnsF [SPath s] deriving (Functor, Show)

pattern SVar x     = Fix (SVarF x)
pattern SNode n    = Fix (SNodeF n)
pattern SLabel l   = Fix (SLabelF l)
pattern SCon id ts = Fix (SConF id ts)
pattern SAns ps    = Fix (SAnsF ps)

{- READER -}
type Frame s = HashMap Ident (STerm s)
data Env s   = Env
 { symbols :: SymTab
 , locals  :: [Frame s]
 }

emptyEnv :: Env s
emptyEnv = Env HM.empty [HM.empty]

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
 
instance Fallible t v StatixError where
  occursFailure v t     = Unsatisfiable "Recursive term"
  mismatchFailure t1 t2 = Unsatisfiable "Term mismatch"

{- STATE -}
data Solver s = Solver
  { queue :: Seq (Goal s)
  , nextU :: Int
  , nextN :: Int
  , graph :: STGraph s Label (STerm s)
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
type Goal s   = (Env s, Constraint₁)

-- | (ST-less) solution to a constraint program
type Solution = Either StatixError (String, IntGraph Label String)
