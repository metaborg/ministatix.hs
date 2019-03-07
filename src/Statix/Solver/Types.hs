{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Statix.Solver.Types where

import Prelude hiding (lookup, null)
import Data.Map.Strict as Map hiding (map, null)
import Data.STRef
import Data.Sequence as Seq

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Trans
import Control.Unification hiding (STVar)

import Statix.Graph
import Statix.Syntax.Constraint

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
newtype T s = PackT (UTerm (TermF (STNodeRef s Label (T s))) (STU s)) deriving (Show)
type C s    = Constraint (T s)
type STU s  = STVar s (TermF (STNodeRef s Label (T s)))

{- READER -}
type Env s = Map RawVar (STU s)

{- ERROR -}
data StatixError =
    UnificationError
  | UnboundVariable
  | UnsatisfiableError
  | TypeError
  | Panic String deriving (Show)

instance Error StatixError where
  strMsg = Panic

instance Fallible t v StatixError where
  occursFailure v t     = UnsatisfiableError
  mismatchFailure t1 t2 = UnsatisfiableError

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
type SolverM s = ReaderT (Env s) (StateT (Solver s) (ErrorT StatixError (ST s)))

-- | Constraint closure
type Goal s   = (Env s, C s)

-- | (ST-less) solution to a constraint program
type Solution = Either StatixError (String, IntGraph Label ())
