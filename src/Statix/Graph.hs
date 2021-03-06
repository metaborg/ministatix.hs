module Statix.Graph
  ( IntGraphEdge(..)
  , IntGraphNode(..)
  , IntGraph(..)
  , STEdge
  , STNodeData(..)
  , STNodeRef(..)
  , STGraph
  , toIntGraph
  ) where

import Data.IntMap as IM
import Data.Set as Set
import Data.STRef
import Data.List
import Data.Coerce

import Control.Monad.ST

import Statix.Regex as Re
import Statix.Syntax.Constraint

import Debug.Trace

{- Int Graphs without safety guarantees -}
data IntGraphEdge l d = IntEdge l (Maybe d) Int
  deriving (Functor, Foldable, Traversable)

data IntGraphNode l d = IntNode
  { id    :: Int
  , edges :: [IntGraphEdge l d]
  , datum :: d
  } deriving (Functor, Foldable, Traversable)

newtype IntGraph l d = IntGraph (IntMap (IntGraphNode l d))
  deriving (Functor, Foldable, Traversable)

instance (Show l, Show d) ⇒ Show (IntGraphEdge l d) where
  show (IntEdge l d i) = "─⟨ " ++ show l ++ "(" ++ show d ++ ") ⟩⟶ " ++ show i

instance (Show d, Show l) ⇒ Show (IntGraphNode l d) where
  show (IntNode i es d) =
    "∇ (" ++ (show i) ++ ")" ++ " ──■ " ++ show d
    ++ concatMap (\e → "\n    " ++ show e) es

instance (Show l, Show d) ⇒ Show (IntGraph l d) where
  show (IntGraph g) =
    concatMap (\ n → "  " ++ show n ++ "\n") g

{- Graph node/data types for graph in ST -} 
type STEdge s l d = (l , Maybe d, STNodeRef s l d)
data STNodeData s l d = STNData [STEdge s l d] d
data STNodeRef  s l d = STNRef !Int !(STRef s (STNodeData s l d))

instance Eq (STNodeRef s l d) where
  (STNRef i _) == (STNRef j _) = i == j

instance Ord (STNodeRef s l d) where
  (STNRef i _) <= (STNRef j _) = i <= j

instance Show (STNodeRef s l d) where
  show (STNRef i _) = show i

type STGraph s l d = [STNodeRef s l d]

toIntGraph :: STGraph s l d → ST s (IntGraph l d)
toIntGraph stg = do
  ns ← (mapM _groundN stg)
  return $ coerce $ (IM.fromList ns)
  where
    _groundE :: STEdge s l d → IntGraphEdge l d
    _groundE (l , d, STNRef i r) = IntEdge l d i

    _groundN :: STNodeRef s l d → ST s (Int, IntGraphNode l d)
    _groundN (STNRef i r) = do
      (STNData es d) ← readSTRef r
      let es' = fmap _groundE es
      return (i , IntNode i es' d)
