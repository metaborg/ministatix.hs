module Statix.Analysis.Lexical where

import Control.Monad.Reader

data Path id = Skip (Path id) | End id deriving (Eq, Show)

-- | A better monad for resolving lexical binders
class Monad m ⇒ MonadLex b r d m | m → b r d where
  enter   :: m a → m a
  intros  :: [b] → m a → m a
  resolve :: r → m d

enters :: (MonadLex b r d m) ⇒ [b] → m a → m a
enters is c = enter $ intros is c
