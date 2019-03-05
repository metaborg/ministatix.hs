{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Statix.Graph
  ( IntGraphEdge(..)
  , IntGraphNode(..)
  , IntGraph(..)
  , STEdge
  , STNodeData(..)
  , STNodeRef(..)
  , STGraph
  , toIntGraph
  , MonadGraph(..)
  ) where

import Data.IntMap as IM
import Data.STRef
import Control.Monad.ST

import Statix.Syntax.Constraint

{- Int Graphs without safety guarantees -}
data IntGraphEdge l = IntEdge l Int
  deriving (Show)

data IntGraphNode l d = IntNode
  { id    :: Int
  , edges :: [IntGraphEdge l]
  , datum :: Maybe d
  } deriving (Show)

type IntGraph l d = IntMap (IntGraphNode l d)

instance Functor (IntGraphNode l) where
  fmap f (IntNode i es d) = IntNode i es (fmap f d)

{- Graph node/data types for graph in ST -} 
type STEdge s l d = (l , STNodeRef s l d)
data STNodeData s l d = STNData [STEdge s l d] (Maybe d)
data STNodeRef  s l d = STNRef !Int !(STRef s (STNodeData s l d))

instance Eq (STNodeRef s l d) where
  (STNRef i _) == (STNRef j _) = i == j

instance Show (STNodeRef s l d) where
  show (STNRef i _) = show i

type STGraph s l d = [STNodeRef s l d]

toIntGraph :: STGraph s l d → ST s (IntGraph l d)
toIntGraph stg = do
  ns ← (mapM _groundN stg)
  return (fromList ns)
  where
    _groundE :: STEdge s l d → IntGraphEdge l
    _groundE (l , STNRef i r) = IntEdge l i

    _groundN :: STNodeRef s l d → ST s (Int, IntGraphNode l d)
    _groundN (STNRef i r) = do
      (STNData es d) ← readSTRef r
      let es' = fmap _groundE es
      return (i , IntNode i es' d)



{- A Graph monad interface -}
class (Monad m) => MonadGraph n l d m | m -> n l d where

  newNode  :: Maybe d -> m n
  newEdge  :: (n, l, n) → m ()
  getDatum :: n → m (Maybe d)
