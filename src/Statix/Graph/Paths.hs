module Statix.Graph.Paths where

import Data.Relation

import Control.Monad.Reader
import Control.Monad.Trans

import Statix.Regex as Re
import Statix.Graph.Types

toList :: Path n l → ([(n, l)], n)
toList (End n)   = ([], n)
toList (Via e p) = let (es, end) = toList p in (e:es, end)

labels :: Path n l → [l]
labels = fmap snd . fst . toList

target :: Path n l → n
target (End n)   = n
target (Via _ p) = target p

instance (Show n, Show l) ⇒ Show (Path n l) where

  show (End n) = show n
  show (Via (n,l) p) = show n ++ " ─⟨ " ++ show l ++ " ⟩⟶ " ++ show p

pathLT :: Rel a a → Rel [a] [a]
pathLT lt (a:as) (b:bs) =
  if a `lt` b then True else     -- a < b
    if b `lt` a then False else  -- b < a
      pathLT lt as bs
pathLT lt _ _ = True

setLeMin :: (a → a → Bool) → [a] → [a]
setLeMin le []     = []
setLeMin le (x:xs) = snd $ foldl f (x , [x]) xs
  where
    f (rep, acc) e =
      if e `le` rep then
        if rep `le` e
        then (rep, e:acc)
        else (e, [e])     -- RIP king, long live the king
      else (rep, acc)
