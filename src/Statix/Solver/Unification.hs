-- | Implementation of variation of Baader & Snyder description of Huet's unification algorithm.
-- (Implementation informed by wrengr/unification-fd)
module Statix.Solver.Unification where

import Data.Hashable
import Data.Either
import Data.Default
import Data.HashSet as HS hiding (union)
import Data.Maybe

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Equiv

-- | Term dags over a functor and variable representation.
-- Recursive term positions are filled with node references.
data TGraph n f v =
    GTm  (f n)
  | GVar v

-- | Term trees over a functor and variable representation.
-- Recursive positions are filled with other trees.
data Tree f v =
    TTm (f (Tree f))
  | TVar v

class Unifiable f where
  zipMatch :: f r → f r → Maybe [(r , r)]
  children :: f r → [r]

class UnificationError e where
  symbolClash :: e
  cyclicTerm  :: e

getSchema :: (MonadEquiv n m (Rep n f v)) ⇒ n → m (TGraph n f v)
getSchema n = do
  (Rep σ _, _) ← repr n
  return σ

-- | Computes the unification closure of two nodes in a term dag
closure :: (UnificationError e, MonadError e m, Unifiable f, MonadEquiv n m (Rep n f v)) ⇒
           n → n → m ()
closure s t = do
  -- find the representatives
  (Rep st _, s) ← repr s
  (Rep tt _, t) ← repr t

  -- check if the two terms are already in the same equivalence class
  if (s == t)
    then return ()
    else do
      -- When part of a different class,
      -- attempt to unify the class schemas.
      case (st, tt) of
        -- flex-flex: surely this unifies
        (GVar _, GVar _) → union s t
        -- flex-rigid: this unifies, we update the schema to the RHS
        (GVar _, GTm tm) → union s t
        -- rigid-flex: this unifies, we update the schema to the LHS
        (GTm tm, GVar _) → union t s
        -- rigid-rigid
        (GTm tm₁, GTm tm₂) →
          case zipMatch tm₁ tm₂ of
            Nothing → throwError symbolClash
            -- in case the constructors match,
            -- we get a list of pairings for recursive equivalence checking
            Just ts → do
              union s t
              mapM_ (uncurry closure) ts

data VisitState = Visitor
  { visited :: HashSet Int
  , acyclic :: HashSet Int
  }

instance Default VisitState where
  def = Visitor HS.empty HS.empty

-- | Equivalence class representatives
data Rep n f v = Rep
  { schema :: TGraph n f v
  , id     :: Int }

isAcyclic :: forall e f v n m .
  (Unifiable f, UnificationError e, MonadError e m, MonadEquiv n m (Rep n f v)) ⇒ n → m ()
isAcyclic node = evalStateT (find node) def

  where
    visit  n        = modify (\st → st { visited = insert n (visited st) })
    unvisit n       = modify (\st → st { visited = delete n (visited st) })
    flagAcyclic nid = modify (\st → st { acyclic = insert nid (acyclic st) }) 

    find n = do
      -- get class representative and its associated information
      (Rep t nid, n) ← lift $ repr n
      ac             ← gets (member nid . acyclic)

      if ac
        -- if we already figured out it was acyclic, we're done
        then return ()
        else do
          seen ← gets (member nid . visited)
          if seen then lift $ throwError cyclicTerm -- We are going in circles!
          else do
            case t of
              -- if it is a variable, it is not recursive
              GVar _ → return ()
              -- if it is a term, visit the children
              GTm tm → do
                visit nid
                mapM_ find (children tm)
                unvisit nid

            flagAcyclic nid

unify :: (Unifiable f, UnificationError e, MonadError e m, MonadEquiv n m (Rep n f v)) ⇒
         n → n → m ()
unify l r = do
  -- compute the closure
  closure l r
  -- check if the resulting term isn't cyclic
  isAcyclic l
 
