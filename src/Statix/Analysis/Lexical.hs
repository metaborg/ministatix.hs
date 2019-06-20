module Statix.Analysis.Lexical where

data Path id = Skip (Path id) | End id deriving (Eq, Show)

end :: Path id → id
end (Skip p) = end p
end (End id) = id

-- | A better monad for resolving lexical binders
class Monad m ⇒ MonadLex b r d m | m → b r d where
  type FrameDesc m :: *

  enter   :: FrameDesc m → m a → m a
  intros  :: [b] → m a → m a
  resolve :: r → m d

enters :: (MonadLex b r d m) ⇒ FrameDesc m → [b] → m a → m a
enters fd is c = enter fd $ intros is c

suffix :: Int → Path id → Maybe (Path id)
suffix i p
  | i == 0             = Just p
  | i > 0, Skip p' ← p = suffix (i - 1) p'
  | otherwise          = Nothing

popAll :: Path id → [fr] → Maybe (id, fr)
popAll (Skip p) (fr : frs) = popAll p frs
popAll (End id) (fr : frs) = Just (id, fr)
popAll _ _                 = Nothing
