{-# LANGUAGE UndecidableInstances #-}
module Control.Monad.Equiv where

import Data.Hashable
import Control.Monad.State

-- A union find interface
-- TODO investigate if package `equivalence` works as well
class (Eq n, Monad m) ⇒ MonadEquiv n m d | n m → d
  where

  -- | Variables are represented as nodes in a dag

  -- | Create a new (singleton) class in the term dag with the given term
  -- as its schema (and pointing to itself for the representative).
  newClass :: d → m n

  -- | Find the representative node for the class of the given node
  repr :: n → m (d , n)

  -- | Get/Set the schema term of a class
  description :: n → m d
  modifyDesc  :: n → (d → d) → m ()

  -- | Take the union of two equivalence classes;
  -- the callback is used to select the descriptor for the resulting class
  unionWith :: n → n → (d → d → d) → m ()

union :: MonadEquiv n m d ⇒ n → n → m ()
union n n' = unionWith n n' (\_ d → d)

instance (MonadEquiv n m d) ⇒ MonadEquiv n (StateT r m) d where
  newClass    = lift . newClass
  repr        = lift . repr
  description = lift . description
  modifyDesc n f = lift (modifyDesc n f)
  unionWith n m f = lift (unionWith n m f)
  
