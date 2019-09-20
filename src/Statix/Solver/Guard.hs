module Statix.Solver.Guard where

import Data.Map.Strict as Map hiding (map, null)
import Data.Set as Set

import Control.Lens
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import Statix.Regex as Re
import Statix.Syntax as Syn
import Statix.Analysis.Lexical
import Statix.Solver.Types
import Statix.Solver.Monad ()

import Unification as U hiding (TTm)

checkNode ces n ls =
  case ces Map.!? n of
    Nothing  → Set.empty
    Just re  →
      let checkLabel = \l → if nomatch l re then Set.empty else Set.singleton (n, l)
          critics = checkLabel <$> (Set.toList ls)
      in Set.unions critics

checkVar ces p ls i = do
  -- Drop i lexical frames from the path
  -- corresponding to the number of binders we moved under during the
  -- critical occurence checking.
  -- This is safe, since those cannot possibly be instantiated to nodes.
  case (suffix i p) of
    Nothing → return Set.empty
    Just p → do
      tm ← resolve p >>= getSchema
      case tm of
        (SNode n) → return $ checkNode ces n ls
        _         → return $ Set.empty

checkTerm :: Map (SNode s) (Regex Label) → Term₁ → Set Label → Int → SolverM s (Set (SNode s, Label))
checkTerm ces t ls i =
  case t of
    (Syn.Var p) → checkVar ces p ls i
    _           → return Set.empty

checkCritical :: Map (SNode s) (Regex Label) → Constraint₁ → Int → SolverM s (Set (SNode s, Label))
checkCritical ces (CAnd _ l r) i = do
  lc ← checkCritical ces l i
  rc ← checkCritical ces r i
  return (lc `Set.union` rc)
checkCritical ces (CEx _ xs c) i = do
  checkCritical ces c (i + 1)
checkCritical ces (CEdge _ x e y) i
  | (Label l _) ← e = checkVar ces x (Set.singleton l) i
  | otherwise       = throwError TypeError
checkCritical ces (CApply _ qn ts) i = do
  -- get type information for p
  formals  ← view (symbols.sigOf qn)
  critters ← zipWithM (\t (_,ty,(_,perm)) → checkTerm ces t perm i) ts formals
  return $ Set.unions critters
checkCritical ces (CEvery _ z (Branch _ c)) i = do
  checkCritical ces c (i + 1)
checkCritical ces (CMatch _ t brs) i = do
  sets ← forM brs $ \(Branch _ c) → checkCritical ces c (i + 1)
  return $ Set.unions sets
checkCritical _ _ _ =
  return Set.empty

queryGuard :: Map (SNode s) (Regex Label) → SolverM s (Set (SNode s, Label))
queryGuard ce = do
  cs ← use queue
  Set.unions <$> mapM (\(e, c, _) → local (const e) $ checkCritical ce c 0) cs
