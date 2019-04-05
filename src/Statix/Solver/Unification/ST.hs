module Statix.Solver.Unification.ST where

import Data.UnionFind.ST as UF
import Data.STRef

import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Equiv

import Statix.Solver.Unification

newtype Class s f v = Class (Point s (Rep (Class s f v) f v)) deriving (Eq)

instance (Unifiable f) ⇒ MonadEquiv (Class s f v) (ST s) (Rep (Class s f v) f v) where

  newClass t = do
    n ← UF.fresh t
    return (Class n)

  repr (Class n) = do
    n ← UF.repr n
    r ← UF.descriptor n
    return (r , Class n)

  description (Class n) = do
    UF.descriptor n

  modifyDesc (Class n) f = do
    UF.modifyDescriptor n f

  union (Class n) (Class m) = do
    UF.union n m
