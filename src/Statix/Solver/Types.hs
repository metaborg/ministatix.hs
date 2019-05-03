{-# LANGUAGE StandaloneDeriving #-}
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

import ATerms.Syntax.ATerm

import Unification
import Unification.ST

-- | Graph node references in ST 
type SNode s = STNodeRef s Label (STmRef s)

-- | Graph paths in ST
type SPath s = Graph.Path (SNode s) Label

-- functorial in the edge term
deriving instance Functor (SPath s)
deriving instance Foldable (SPath s)
deriving instance Traversable (SPath s)

-- | Some information about the source of variables
type VarInfo = Text

-- | Solver DAG in ST
type STmRef s = Class s (STermF s) VarInfo

-- | Solver terms
type STree s  = Tree (STermF s) VarInfo

-- | Solver generation
type SGen = Int

-- | The constructors of the term language
data STermF s c =
    SNodeF (SNode s)
  | SLabelF Label (Maybe c)
  | STmF (ATermF c)
  | SAnsF [SPath s c]
  | SPathEndF c
  | SPathConsF c c c deriving (Functor, Foldable, Traversable)

instance (Show c) ⇒ Show (STermF s c) where
  show (SNodeF n)         = "new " ++ show n
  show (SLabelF l t)      = show l ++ "(" ++ show t ++ ")"
  show (STmF t)           = show t
  show (SAnsF _)          = "{...}"
  show (SPathConsF n l p) = show n ++ " ▻ " ++ show l ++ " ▻ " ++ show p
  show (SPathEndF n)      = show n ++ " ◅ "
 
pattern STm t           = Tm (STmF t)
pattern SNode n         = Tm (SNodeF n)
pattern SLabel l t      = Tm (SLabelF l t)
pattern SAns ps         = Tm (SAnsF ps)
pattern SPathCons s l p = Tm (SPathConsF s l p)
pattern SPathEnd s      = Tm (SPathEndF s)

instance Unifiable (STermF s) where

  zipMatch (SNodeF n) (SNodeF m)
    | n == m    = Just (SNodeF n)
    | otherwise = Nothing

  zipMatch (STmF tm) (STmF tm') = STmF <$> zipMatch tm tm'

  zipMatch (SLabelF l₁ t₁) (SLabelF l₂ t₂)
    | l₁ == l₂  =
        case (t₁, t₂) of
          (Just t₁ , Just t₂) → Just (SLabelF l₁ (Just (t₁ , t₂)))
          (Nothing , Nothing) → Just (SLabelF l₁ Nothing)
          _                   → Nothing
    | otherwise = Nothing

  -- paths
  zipMatch (SPathConsF s l p) (SPathConsF s' l' p')
    = Just (SPathConsF (s, s') (l, l') (p, p'))
  zipMatch (SPathEndF s) (SPathEndF s')
    = Just (SPathEndF (s, s'))

  -- unifying answer sets is prohibited
  zipMatch (SAnsF _) (SAnsF _) = Nothing

  -- other combinations are constructor clashes
  zipMatch _ _ = Nothing

data Trace = FrExist | FrPred QName

data Frame s = Frame
  { binders :: HashMap Ident (STmRef s)
  , desc    :: Trace
  }

data Env s = Env
 { _symbols :: SymbolTable
 , _locals  :: [Frame s]
 }

makeLenses ''Env

instance Default (Frame s) where
  def = Frame HM.empty FrExist

instance Default (Env s) where
  def = Env HM.empty [def]

{- ERROR -}
data Traceline = Call QName [String] | Within Constraint₁

data StatixError
  = Unsatisfiable [Traceline] String -- trace, reason
  | StuckError
  | TypeError
  | Panic String
  | UnificationError String

instance Show StatixError where
  show TypeError              = "Constraint unsatisfiable: type error"
  show (UnificationError e)   = "Constraint unsatisfiable: unification error (" ++ e ++ ")"
  show (Unsatisfiable tr msg) = "Constraint unsatisfiable: " ++ msg
  show StuckError             = "Stuck"
  show (Panic x)              = "Panic: " ++ x
 
instance HasClashError (STermF s) StatixError where
  symbolClash l r = UnificationError $ "Symbol clash: " ++ show l ++ " != " ++ show r

instance HasCyclicError StatixError where
  cyclicTerm      = UnificationError "Cyclic term"

instance HasSubsumptionError StatixError where
  doesNotSubsume  = StuckError

{- STATE -}
data Solver s = Solver
  { _queue      :: Seq.Seq (Goal s)
  , _nextFresh  :: Integer
  , _graph      :: STGraph s Label (STmRef s)
  , _generation :: SGen
  }

instance Default (Solver s) where
  def = Solver
    { _queue  = Seq.empty
    , _nextFresh = 0
    , _graph  = []
    , _generation = minBound + 1
    }

-- | The monad that we use to solve Statix constraints
type SolverM s = ReaderT (Env s) (ExceptT StatixError (StateT (Solver s) (ST s)))

-- | Constraint closure
type Goal s    = (Env s, Constraint₁, SGen)

-- | (ST-less) solution to a constraint program
type Solution = ((Either StatixError String), IntGraph Label String)

makeLenses ''Solver
