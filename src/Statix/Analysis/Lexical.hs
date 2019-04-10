module Statix.Analysis.Lexical where

data Path id = Skip (Path id) | End id deriving (Eq, Show)

-- | A monad for resolving lexical binders
class ScopedM m where
  type Binder m :: *
  type Ref    m :: *
  type Datum  m :: *

  enter   :: m a → m a
  intros  :: [Binder m] → m a → m a
  resolve :: Ref m → m (Datum m)

enters :: (ScopedM m) ⇒ [Binder m] → m a → m a
enters is c = enter $ intros is c

-- | A better monad for resolving lexical binders
class MonadLex b r d m | m → b r d where

  menter   :: m a → m a
  mintros  :: [b] → m a → m a
  mresolve :: r → m d

menters :: (MonadLex b r d m) ⇒ [b] → m a → m a
menters is c = menter $ mintros is c
