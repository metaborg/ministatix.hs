{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
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

import Control.Lens
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

import Unification
import Unification.ST

-- | Graph node references in ST 
type SNode s = STNodeRef s Label (SDag s)

-- | Graph paths in ST
type SPath s = Graph.Path (SNode s) Label

-- | Some information about the source of variables
type VarInfo = Text

-- | Solver DAG in ST
type SDag s   = Dag (STmRef s) (STermF s) VarInfo
type STmRef s = Class s (STermF s) VarInfo

-- | Solver terms
type STree s  = Tree (STermF s) VarInfo

-- | The constructors of the term language
data STermF s c =
    SNodeF (SNode s)
  | SLabelF Label
  | SConF Ident [c]
  | SAnsF [SPath s]
  | SPathF c Label c deriving (Functor, Foldable, Traversable)

instance (Show c) ⇒ Show (STermF s c) where
  show (SNodeF n)   = "∇(" ++ show n ++ ")"
  show (SLabelF l)  = "Label(" ++ show l ++ ")"
  show (SConF k ts) = show k ++ "(" ++ (List.intercalate "," (show <$> ts)) ++ ")"
  show (SAnsF _)    = "{...}"
  show (SPathF n l p) = show n ++ " ▻ " ++ show l ++ " ▻ " ++ show p
 
pattern SNode n    = Tm (SNodeF n)
pattern SLabel l   = Tm (SLabelF l)
pattern SCon id ts = Tm (SConF id ts)
pattern SAns ps    = Tm (SAnsF ps)
pattern SPath n l p = Tm (SPathF n l p)

instance Unifiable (STermF s) where

  zipMatch (SNodeF n) (SNodeF m)
    | n == m    = Just (SNodeF n)
    | otherwise = Nothing
  zipMatch (SConF k₁ ts₁) (SConF k₂ ts₂)
    | k₁ == k₂ =
      if List.length ts₁ == List.length ts₂
        then Just (SConF k₁ (List.zip ts₁ ts₂))
        else Nothing
    | otherwise = Nothing
  zipMatch (SLabelF l₁) (SLabelF l₂)
    | l₁ == l₂  = Just (SLabelF l₁)
    | otherwise = Nothing

  -- unifying answer sets is prohibited
  zipMatch (SAnsF _) (SAnsF _) = Nothing

  -- other combinations are constructor clashes
  zipMatch _ _ = Nothing

{- READER -}
type Frame s = HashMap Ident (STmRef s)
data Env s = Env
 { _symbols :: SymbolTable
 , _locals  :: [Frame s]
 }

makeLenses ''Env

instance Default (Frame s) where
  def = HM.empty

instance Default (Env s) where
  def = Env HM.empty [def]

{- ERROR -}
data StatixError
  = Unsatisfiable String
  | StuckError
  | TypeError
  | Panic String

instance Show StatixError where
  show (Unsatisfiable x) = "Constraint unsatisfiable: " ++ x
  show StuckError = "Stuck"
  show TypeError = "Constraint unsatisfiable: type error"
  show (Panic x) = "Panic" ++ x
 
instance HasClashError (STermF s) StatixError where
  symbolClash l r = Unsatisfiable $ "Symbol clash: " ++ show l ++ " != " ++ show r

instance HasCyclicError StatixError where
  cyclicTerm      = Unsatisfiable "Cyclic term"

{- STATE -}
data Solver s = Solver
  { queue :: Seq.Seq (Goal s)
  , nextFresh :: Int
  , graph :: STGraph s Label (SDag s)
  , generation :: Int
  }

emptySolver :: Solver s
emptySolver = Solver
  { queue  = Seq.empty
  , nextFresh = 0
  , graph  = []
  , generation = 0
  }

-- | The monad that we use to solve Statix constraints
type SolverM s = ReaderT (Env s) (StateT (Solver s) (ExceptT StatixError (ST s)))

-- | Constraint closure (environment, constraint, generation)
type Goal s    = (Env s, Constraint₁, Int)

-- | (ST-less) solution to a constraint program
type Solution = Either StatixError (String, IntGraph Label ())
