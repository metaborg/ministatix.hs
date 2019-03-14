module Statix.Solver.Types where

import Prelude hiding (lookup, null)
import Data.Map.Strict as Map hiding (map, null)
import Data.STRef
import Data.Sequence as Seq
import Data.HashMap.Strict as HM

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans
import Control.Unification hiding (STVar)

import Statix.Regex
import Statix.Graph
import Statix.Syntax.Constraint
import Statix.Analysis.Symboltable

-- | Unification variables in ST
data STVar s t =
    STVar
      { ident :: {-# UNPACK #-} !Int
      , ref   :: {-# UNPACK #-} !(STRef s (Maybe (UTerm t (STVar s t))))
      , name  :: String
      }
    
instance Show (STVar s t) where
  show (STVar _ _ n) = n

instance Eq (STVar s t) where
  (STVar i _ _) == (STVar j _ _) = (i == j)

instance Variable (STVar s t) where
  getVarID u = ident u

{- Specialize stuff for our term language -}
newtype T s = PackT (UTerm (TermF (STNodeRef s Label (T s))) (STU s))

instance Show (T s) where
  show (PackT u) = show u

type C s    = Constraint QName (T s)
type STU s  = STVar s (TermF (STNodeRef s Label (T s)))
type STN s  = STNodeRef s Label (T s)

{- READER -}
data Env s = Env
 { symbols :: SymbolTable
 , locals  :: Map RawName (T s)
 }

emptyEnv :: Env s
emptyEnv = Env HM.empty Map.empty

getPredicate :: QName → Env s → Maybe (Predicate QName)
getPredicate qn env = HM.lookup qn (symbols env)

insertLocal :: RawName → T s → Env s → Env s
insertLocal x u env = env { locals = Map.insert x u (locals env) }

{- ERROR -}
data StatixError =
    UnboundVariable RawName
  | Unsatisfiable String
  | TypeError
  | Panic String

instance Show StatixError where
  show (UnboundVariable x) = "Found unbound variable " ++ x
  show (Unsatisfiable x) = "Constraint unsatisfiable: " ++ x
  show TypeError = "Constraint unsatisfiable: type error"
  show (Panic x) = "Panic" ++ x
 
instance Fallible t v StatixError where
  occursFailure v t     = Unsatisfiable "Recursive term"
  mismatchFailure t1 t2 = Unsatisfiable "Term mismatch"

{- STATE -}
data Solver s = Solver
  { queue :: Seq (Env s, C s)
  , nextU :: Int
  , nextN :: Int
  , graph :: STGraph s Label (T s)
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
type Goal s   = (Env s, C s)

-- | (ST-less) solution to a constraint program
type Solution = Either StatixError (String, IntGraph Label String)
