module Statix.Solver.Unification.ST where

import Data.UnionFind.ST as UF
import Data.STRef

import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.Except

import Statix.Solver.Unification

data Rep s f = Rep Int (TGraph (Node s f) f)
type Node s f = Point s (Rep s f)

instance (Unifiable f) ⇒ MonadUnify
    (TGraph (Node s f) f)
    (Node s f)
    (ReaderT (STRef s Int) (ST s)) where

  type ReprId (ReaderT (STRef s Int) (ST s)) = Int

  fresh t = do
    nref ← ask
    n    ← lift $ readSTRef nref
    node ← lift $ UF.fresh (Rep n t)
    lift $ modifySTRef nref ((+) 1)
    return node

  repr n = do
    n         ← lift $ UF.repr n
    (Rep i _) ← lift $ UF.descriptor n
    return (i , n)

  schema n = do
    (Rep i t) ← lift $ UF.descriptor n
    return t

  setSchema n t = do
    lift $ UF.modifyDescriptor n (\(Rep i _) → Rep i t)

  union n m = do
    lift $ UF.union n m
