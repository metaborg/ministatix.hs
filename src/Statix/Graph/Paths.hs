module Statix.Graph.Paths where

import Data.Relation
import Data.Map as Map hiding (toList, foldl)
import Data.Set as Set hiding (toList, foldl)

import Statix.Regex as Re
import Statix.Graph.Types

toList :: Path n l t → ([(n, l, Maybe t)], n)
toList (End n)   = ([], n)
toList (Via e p) = let (es, end) = toList p in (e:es, end)

labels :: Path n l t → [l]
labels = fmap (\(n, l, t) → l) . fst . toList

target :: Path n l t → n
target (End n)   = n
target (Via _ p) = target p

prettyPath :: (n → String) → (l → String) → (t → String) → Path n l t → String
prettyPath n l t (End no) = n no
prettyPath n l t (Via (no, la, tm) p) =
  let prettyDatum = maybe "" (\tm → "(" ++ t tm ++ ")") in
    n no ++ " -[ " ++ l la ++ prettyDatum tm ++ " ]-> " ++ prettyPath n l t p

instance (Show n, Show l, Show t) ⇒ Show (Path n l t) where
  show = prettyPath show show show

pathLT :: (Eq a) ⇒ Rel a a → Rel [a] [a]
pathLT lt (a:as) (b:bs) =
  if a `lt` b then True else     -- a < b
    if b `lt` a then False else  -- b < a
      if a == b then pathLT lt as bs else False
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

setLtMin :: (a → a → Bool) → [a] → [a]
setLtMin lt []     = []
setLtMin lt (x:xs) = snd $ foldl f (x , [x]) xs
  where
    f (rep, acc) e =
      if e `lt` rep
        then (e, [e])
        else
          if rep `lt` e
          then (rep, acc)
          else (rep, e:acc)

-- | Find reachable nodes in the graph over a regex.
-- Together with the regex derivative in that node
findReachable :: (Ord l, MonadGraph n l d m) ⇒ n → Regex l → m (Map n (Regex l))
findReachable n re = _find n re Set.empty
  where
    _find n re vis
      | Re.empty re = return Map.empty
      | otherwise   = do
       -- check if we visited this node yet on the path here
       if Set.member n vis
         then return Map.empty
         else do
           -- put n in visisted set
           let vis' = Set.insert n vis
           -- get the edges out of here
           es ← getOutEdges n
           reachables ← Map.unionsWith RAlt <$> mapM (\(l, t, m) → _find m (Re.match l re) vis') es
           return (Map.insertWith RAlt n re reachables)

-- | Find regular paths in the graph
runQuery :: (MonadGraph n l d m) ⇒ n → Regex l → m [Path n l d]
runQuery n re = _resolve n re Set.empty
  where
    _resolve n re vis
      | Re.empty re = return []
      | otherwise   = do
       -- check if we visited this node yet on the path here
       if Set.member n vis
         then return (if Re.nullable re then [End n] else [] )
         else do
           -- get the edges out of here
           es ← getOutEdges n
           -- calculate the paths out of here
           pss ← mapM (\ (l , t, tgt) → do
                     ps ← _resolve tgt (Re.match l re) (Set.insert n vis)
                     return (fmap (Via (n, l, t)) ps)
                   ) es
           let ps = concat pss
           -- add the loop if it exists
           return (if Re.nullable re then (End n : ps) else ps)
