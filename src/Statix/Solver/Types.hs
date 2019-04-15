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
type SNode s = STNodeRef s Label (STmRef s)

-- | Graph paths in ST
type SPath s = Graph.Path (SNode s) Label

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
  | SLabelF Label
  | SConF Ident [c]
  | SAnsF [SPath s]
  | SPathEndF c
  | SPathConsF c c c deriving (Functor, Foldable, Traversable)

instance (Show c) ⇒ Show (STermF s c) where
  show (SNodeF n)         = "new " ++ show n
  show (SLabelF l)        = show l
  show (SConF k ts)       = unpack k ++ "(" ++ (List.intercalate "," (show <$> ts)) ++ ")"
  show (SAnsF _)          = "{...}"
  show (SPathConsF n l p) = show n ++ " ▻ " ++ show l ++ " ▻ " ++ show p
  show (SPathEndF n)      = show n ++ " ◅ "
 
pattern SNode n         = Tm (SNodeF n)
pattern SLabel l        = Tm (SLabelF l)
pattern SCon id ts      = Tm (SConF id ts)
pattern SAns ps         = Tm (SAnsF ps)
pattern SPathCons s l p = Tm (SPathConsF s l p)
pattern SPathEnd s      = Tm (SPathEndF s)

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

  -- paths
  zipMatch (SPathConsF s l p) (SPathConsF s' l' p')
    = Just (SPathConsF (s, s') (l, l') (p, p'))
  zipMatch (SPathEndF s) (SPathEndF s')
    = Just (SPathEndF (s, s'))

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
  | NoMatch

instance Show StatixError where
  show TypeError         = "Constraint unsatisfiable: type error"
  show (Unsatisfiable x) = "Constraint unsatisfiable: " ++ x
  show StuckError        = "Stuck"
  show NoMatch           = "No match"
  show (Panic x)         = "Panic: " ++ x
 
instance HasClashError (STermF s) StatixError where
  symbolClash l r = Unsatisfiable $ "Symbol clash: " ++ show l ++ " != " ++ show r

instance HasCyclicError StatixError where
  cyclicTerm      = Unsatisfiable "Cyclic term"

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
type SolverM s = ReaderT (Env s) (StateT (Solver s) (ExceptT StatixError (ST s)))

-- | Constraint closure
type Goal s    = (Env s, Constraint₁, SGen)

-- | (ST-less) solution to a constraint program
type Solution = Either StatixError (String, IntGraph Label String)

makeLenses ''Solver
