-- | Implementation of variation of Baader & Snyder description of Huet's unification algorithm.
-- (Implementation informed by wrengr/unification-fd)
module Unification where

import Data.Hashable
import Data.Either
import Data.Default
import Data.HashSet as HS hiding (union)
import Data.Maybe
import Data.Functor.Fixedpoint

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Equiv
import Control.Monad.Unique

-- | The functor for terms with unification variables.
data STmF f v r =
    Tm  (f r)
  | Var v deriving (Functor, Foldable, Traversable)

-- Instantiating the recursive positions with node references gives us term graphs.
type Dag n f v = STmF f v n

-- Taking the fixpoint gives us term trees.
type Tree f v    = Fix (STmF f v)
pattern TTm r  = Fix (Tm r)
pattern TVar v = Fix (Var v)

instance (Show (f r), Show v) ⇒ Show (STmF f v r) where

  show (Tm  f) = show f
  show (Var v) = "Var " ++ show v

class (Traversable f) ⇒ Unifiable f where
  zipMatch :: f r → f r → Maybe (f (r , r))

class HasClashError f e  where
  symbolClash :: f () → f () → e

class HasCyclicError e where
  cyclicTerm  :: e

class HasSubsumptionError e where
  doesNotSubsume :: e

-- | Construct a dag from the tree representation where variables are
-- already node references; i.e. convert one layer of term structure.
construct :: (MonadUnique Integer m, MonadEquiv n m (Rep n f v)) ⇒ STmF f n n → m n
construct (Var n) = return n
construct (Tm tm) = do
  id  ← fresh
  c   ← newClass (Rep (Tm tm) id)
  return c

freshVar :: (MonadUnique Integer m, MonadEquiv n m (Rep n f v)) ⇒ v → m n
freshVar v = do
  id ← fresh
  newClass (Rep (Var v) id) 

getSchema :: (MonadEquiv n m (Rep n f v)) ⇒ n → m (Dag n f v)
getSchema n = do
  (Rep σ _, _) ← repr n
  return σ

-- | Computes the unification closure of two nodes in a term dag
closure :: MonadUnify f n v e m ⇒ n → n → m n
closure s t = do
  -- find the representatives
  (Rep st _, s) ← repr s
  (Rep tt i, t) ← repr t

  -- check if the two terms are already in the same equivalence class
  if (s == t)
    then return s
    else do
      -- When part of a different class,
      -- attempt to unify the class schemas.
      case (st, tt) of
        -- flex-flex: surely this unifies
        (Var _, Var _) → do
          union s t
          return s
        -- flex-rigid: this unifies, we update the schema to the RHS
        (Var _, Tm tm) → do
          union s t
          return t
        -- rigid-flex: this unifies, we update the schema to the LHS
        (Tm tm, Var _) → do
          union t s
          return s
        -- rigid-rigid
        (Tm tm₁, Tm tm₂) →
          case zipMatch tm₁ tm₂ of
            Nothing → throwError $ symbolClash (fmap (const ()) tm₁) (fmap (const ()) tm₂)
            -- in case the constructors match,
            -- we get a list of pairings for recursive equivalence checking
            Just tm₃ → do
              union s t -- optimistically merge the classes
              σ ← mapM (uncurry closure) tm₃
              modifyDesc s (\_ → Rep (Tm σ) i) 
              return s

-- | Computes the unification semiclosure of two nodes in a term dag.
-- Exactly like unification, except for the rigid-flex case.
-- The rhs is not refined.
semiclosure :: (HasSubsumptionError e, MonadUnify f n v e m) ⇒ n → n → m n
semiclosure s t = do
  (Rep st _, s) ← repr s
  (Rep tt i, t) ← repr t

  if (s == t)
    then return s
    else do
      case (st, tt) of
        (Var _, Var _) → do
          union s t
          return s
        (Var _, Tm tm) → do
          union s t
          return t
        -- rigid-flex: RHS is less defined than LHS, so does not subsume
        (Tm tm, Var _) → do
          throwError $ doesNotSubsume
        (Tm tm₁, Tm tm₂) →
          case zipMatch tm₁ tm₂ of
            Nothing → throwError $ symbolClash (fmap (const ()) tm₁) (fmap (const ()) tm₂)
            Just tm₃ → do
              σ ← mapM (uncurry semiclosure) tm₃

              -- we are less optimistic here about taking the union
              -- then in unification, because the applications of semiclosure
              -- checking requires us to backtrack on failures
              union s t

              modifyDesc s (\_ → Rep (Tm σ) i) 
              return s

equiv :: (HasSubsumptionError e, MonadUnify f n v e m) ⇒ n → n → m n
equiv s t = do
  (Rep st _, s) ← repr s
  (Rep tt i, t) ← repr t

  if (s == t)
    then return s
    else do
      case (st, tt) of
        (Var _, Var _) → do
          union s t
          return s
        (Var _, Tm tm) → do
          throwError $ doesNotSubsume
        (Tm tm, Var _) → do
          throwError $ doesNotSubsume
        (Tm tm₁, Tm tm₂) →
          case zipMatch tm₁ tm₂ of
            Nothing → throwError $ symbolClash (fmap (const ()) tm₁) (fmap (const ()) tm₂)
            Just tm₃ → do
              σ ← mapM (uncurry equiv) tm₃

              -- we are less optimistic here about taking the union
              -- then in unification, because the applications of equiv
              -- checking requires us to backtrack on failures
              union s t
              modifyDesc s (\_ → Rep (Tm σ) i) 
              return s

notequiv :: (HasSubsumptionError e, MonadUnify f n v e m) ⇒ n → n → m Bool
notequiv s t = do
  (Rep st _, s) ← repr s
  (Rep tt i, t) ← repr t

  if (s == t)
    then return False
    else do
      case (st, tt) of
        (Var x, Var y) → do
          throwError $ doesNotSubsume
        (Var _, Tm tm) → do
          throwError $ doesNotSubsume
        (Tm tm, Var _) → do
          throwError $ doesNotSubsume
        (Tm tm₁, Tm tm₂) →
          case zipMatch tm₁ tm₂ of
            Nothing → return True
            Just tm₃ → do
              any id <$> mapM (uncurry notequiv) tm₃

data VisitState = Visitor
  { visited :: HashSet Integer
  , acyclic :: HashSet Integer
  }

instance Default VisitState where
  def = Visitor HS.empty HS.empty

-- | Equivalence class representatives
data Rep n f v = Rep
  { schema :: Dag n f v
  , repId  :: Integer }

class
  ( Unifiable f
  , HasClashError f e
  , HasCyclicError e
  , MonadError e m
  , MonadEquiv n m (Rep n f v)
  ) ⇒ MonadUnify f n v e m  | m → f n v e

isAcyclic :: MonadUnify f n v e m ⇒ n → m ()
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
              Var _ → return ()
              -- if it is a term, visit the children
              Tm tm → do
                visit nid
                mapM_ find tm
                unvisit nid

            flagAcyclic nid

unify :: (Traversable f, MonadUnify f n v e m) ⇒ n → n → m ()
unify l r = do
  -- compute the closure
  r ← closure l r
  -- check if the resulting term isn't cyclic
  isAcyclic r

subsumes :: (Traversable f, HasSubsumptionError e, MonadUnify f n v e m) ⇒ n → n → m ()
subsumes l r = do
  r ← semiclosure l r
  isAcyclic r

-- | Freshen all variables in a term.
-- Expensive operation.
-- Assumes that the term is acyclic.
freshen :: (Traversable f, MonadUnique Integer m, MonadEquiv n m (Rep n f v)) ⇒ n → m n
freshen n = do
  (Rep σ _, n) ← repr n
  id ← fresh

  t ← case σ of
    (Tm f)  → do f' ← (mapM freshen f); return (Tm f')
    (Var v) → return (Var v)

  newClass (Rep t id)

-- | TODO rewrite to cata
toTree :: (Traversable f, MonadEquiv n m (Rep n f v)) ⇒ n → m (Tree f v)
toTree n = do
  t ← getSchema n
  case t of 
    Var v → return (Fix (Var v))
    Tm tm  → do
      subtree ← mapM toTree tm
      return (Fix (Tm subtree))
