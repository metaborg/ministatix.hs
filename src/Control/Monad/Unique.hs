module Control.Monad.Unique where

import Control.Monad.Reader

class (Eq a, Monad m) ⇒ MonadUnique a m where
  fresh :: m a
