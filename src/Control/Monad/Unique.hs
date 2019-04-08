module Control.Monad.Unique where

class (Eq a, Monad m) ⇒ MonadUnique a m where

  fresh :: m a
