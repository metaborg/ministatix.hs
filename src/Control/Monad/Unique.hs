module Control.Monad.Unique where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

class (Eq a, Monad m) ⇒ MonadUnique a m where
  fresh      :: m a
  updateSeed :: a → m ()

instance (Monad m) ⇒ MonadUnique Integer (StateT Integer m) where
  fresh = do
    i ← get
    modify (+1)
    return i

  updateSeed = put

instance (MonadUnique i m) ⇒ MonadUnique i (ExceptT e m) where
  fresh      = lift fresh
  updateSeed = lift . updateSeed
