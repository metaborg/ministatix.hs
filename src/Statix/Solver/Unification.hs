-- | Implementation of variation of Baader & Snyder description of Huet's unification algorithm.
-- Implementation informed by wrengr/unification-fd.

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Statix.Solver.Unification where

import Data.Hashable
import Data.Either
import Data.Default
import Data.HashSet as HS hiding (union)
import Data.Maybe

import Control.Monad.Except
import Control.Monad.State

-- | Term dags over a variable representation and a term functor
data TGraph n f =
    GTm  n (f n)
  | GVar n

data Tree n f =
    TTm n (f (Tree n f))
  | TVar n

class Unifiable t where
  zipMatch :: t r → t r → Maybe [(r , r)]
  children :: t r → [r]

class (Eq n, Monad m, Eq (ReprId m), Hashable (ReprId m))
  ⇒ MonadUnify t n m
  | n m → t
  where

  type ReprId m :: *

  -- | Variables are represented as nodes in a dag

  -- | Create a fresh (singleton) class in the term dag with the given term
  -- as its schema (and pointing to itself for the representative).
  fresh  :: t → m n

  -- | Find the representative node for the class of the given node
  repr   :: n → m (ReprId m , n)

  -- | Get the schema of a node
  schema    :: n → m t
  setSchema :: n → t → m ()

  -- | Take the union of two equivalence classes;
  -- the schema term of the RHS is used for the resulting class
  union :: n → n → m ()

class UnificationError e where
   
  symbolClash :: e
  cyclicTerm  :: e

-- | Computes the unification closure of two nodes in a term dag
closure :: (UnificationError e, MonadError e m, Unifiable f, MonadUnify (TGraph n f) n m) ⇒
           n → n → m ()
closure s t = do
  -- find the representatives
  (_, s) ← repr s
  (_, t) ← repr t

  -- check if the two terms are already in the same equivalence class
  if (s == t)
    then return ()
    else do
      -- When part of a different class,
      -- attempt to unify the class schemas.
      lhs ← schema s
      rhs ← schema t

      case (lhs, rhs) of
        -- flex-flex: surely this unifies
        (GVar n, GVar m)  → union n m
        -- flex-rigid: this unifies, we update the schema to the RHS
        (GVar n, GTm m t) → union n m
        -- rigid-flex: this unifies, we update the schema to the LHS
        (GTm n t, GVar m) → union m n
        -- rigid-rigid
        (GTm n t , GTm m s) →
          case zipMatch t s of
            Nothing → throwError symbolClash
            -- in case the constructors match,
            -- we get a list of pairings for recursive equivalence checking
            Just ts → do
              union n m
              mapM_ (uncurry closure) ts

data VisitState n = Visitor
  { visited :: HashSet n
  , acyclic :: HashSet n
  }

instance Default (VisitState n) where
  def = Visitor HS.empty HS.empty

isAcyclic :: forall e f n m .
  (Unifiable f, UnificationError e, MonadError e m, MonadUnify (TGraph n f) n m) ⇒
  n → m ()
isAcyclic node = evalStateT (find node) def

  where
    visit n st = st { visited = insert n (visited st) }
    unvisit n st = st { visited = delete n (visited st) }

    find :: n → StateT (VisitState (ReprId m)) m ()
    find n = do
      -- get class representative and its associated information
      (nid, n) ← lift $ repr n
      ac       ← gets (member nid . acyclic)

      if ac
        -- if we already figured out it was acyclic, we're done
        then return ()
        else do
          seen ← gets (member nid . visited)
          if seen then lift $ throwError cyclicTerm -- We are going in circles!
          else do
            -- get the schema of the class representative
            t ← lift $ schema n
            case t of
              -- if it is a variable, it is not recursive
              GVar _  → return ()
              -- if it is a term, visit the children
              GTm _ t → do
                modify (visit nid)
                mapM_ find (children t)
                modify (unvisit nid)

            modify (\st → st { acyclic = insert nid (acyclic st) })

unify :: (Unifiable f, UnificationError e, MonadError e m, MonadUnify (TGraph n f) n m) ⇒
         n → n → m ()
unify l r = do
  -- compute the closure
  closure l r
  -- check if the resulting term isn't cyclic
  isAcyclic l
  
