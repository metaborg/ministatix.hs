module Control.Monad.Equiv where

import Data.Hashable

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
  -- the schema term of the RHS is used for the resulting class
  union :: n → n → m ()

-- instance (MonadEquiv n m d) ⇒ MonadEquiv (ExceptT e )
