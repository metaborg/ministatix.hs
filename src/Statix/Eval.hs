{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Statix.Eval where

import Prelude hiding (lookup, null)
import Data.Map.Strict hiding (map, null)
import qualified Data.Map.Strict as Map
import Data.Either
import Data.Maybe
import Data.STRef
import Data.Sequence
import Data.Functor.Fixedpoint
import qualified Data.Sequence as Seq
import Data.Coerce

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Trans
import Control.Unification

import Unsafe.Coerce

import Statix.Syntax.Constraint
import Statix.Syntax.Parser
import Statix.Graph
import Statix.UVars
import Statix.Syntax.Parser


  
{- Specialize that stuff for our term language -}
newtype T s = PackT (UTerm (TermF (STNodeRef s Label (T s))) (STU s))

type C s    = Constraint (T s)
type STU s  = STVar s (TermF (STNodeRef s Label (T s)))

{- READER -}
type Env s = Map RawVar (STU s)

{- STATE -}
data Solver s = Solver
  { queue :: Seq (Env s, C s)
  , nextU :: Int
  , nextN :: Int
  , graph :: STGraph s Label (T s)
  }

emptySolver :: Solver s
emptySolver = Solver
  { queue = Seq.empty
  , nextU = 0
  , nextN = 0
  , graph = []
  }

{- ERROR -}
data StatixError =
    UnificationError
  | UnboundVariable
  | UnsatisfiableError
  | Panic String deriving (Show)

instance Error StatixError where
  strMsg = Panic

instance Fallible t v StatixError where
  occursFailure v t     = UnsatisfiableError
  mismatchFailure t1 t2 = UnsatisfiableError

{- The Solver Monad -}
type SolverM s = ReaderT (Env s) (StateT (Solver s) (ErrorT StatixError (ST s)))

runSolver :: (forall s. SolverM s a) → Either StatixError a
runSolver c = runST (runErrorT (evalStateT (runReaderT c Map.empty) emptySolver))

{- Solver is a bunch of stuff -}
liftST :: ST s a → SolverM s a
liftST = lift . lift . lift

liftSt :: StateT (Solver s) (ErrorT StatixError (ST s)) a → SolverM s a
liftSt = lift
  
{- Semantic operations -}
freshVarName :: SolverM s Int
freshVarName = do
  s ← get
  let n = nextU s
  put (s { nextU = n + 1})
  return n
  
freshNodeName :: SolverM s Int
freshNodeName = do
  s ← get
  let n = nextN s
  put (s { nextN = n + 1})
  return n

instance BindingMonad (TermF (STNodeRef s Label (T s))) (STU s) (SolverM s) where
  lookupVar (STVar i r) = do
    liftST $ readSTRef r

  newVar t = do
    xi     ← freshVarName
    xr     ← liftST $ newSTRef (Just t)
    return (STVar xi xr)
  
  freeVar = do
    sv     ← get
    xi     ← freshVarName
    xr     ← liftST $ newSTRef Nothing
    return (STVar xi xr)

  bindVar (STVar _ xr) t = do
    liftST $ writeSTRef xr (Just t)

instance MonadGraph (STNodeRef s Label (T s)) Label (T s) (SolverM s) where

  newNode d = do
    ni ← freshNodeName
    nr ← liftST $ newSTRef (STNData [] d)
    let node = (STNRef ni nr)
    modify (\ s → s { graph = node : graph s })
    return node

  newEdge (STNRef i r, l, y) =
    liftST $ modifySTRef r (\case STNData es d → STNData ((l , y) : es) d)
    
  getDatum (STNRef i r) = do
    STNData _ d ← liftST (readSTRef r)
    return d

  runQuery n re = do
    liftST $ resolve n re

pushGoal :: C s → SolverM s ()
pushGoal c = do
  st  ← get
  env ← ask
  put (st { queue = queue st |> (env , c)})

popGoal :: SolverM s (Maybe (Goal s))
popGoal = do
  st ← get
  case viewl (queue st) of
    EmptyL        → return Nothing
    (c :< cs) → do
      liftSt $ put (st { queue = cs })
      return (Just c)

internalize :: RawConstraint → (forall s . C s)
internalize c = cata _intern c
  where
    tintern :: RawTerm → T s
    tintern t = unsafeCoerce $ unfreeze t

    _intern :: ConstraintF RawTerm (C s) → C s
    _intern (CEqF t₁ t₂) = CEq (tintern t₁) (tintern t₂)
    _intern (CNewF t) = CNew (tintern t)
    _intern (CEdgeF t₁ l t₂) = CEdge (tintern t₁) l (tintern t₂)
    _intern CTrueF = CTrue
    _intern CFalseF = CFalse
    _intern (CAndF c d) = CAnd c d
    _intern (CExF ns c) = CEx ns c
    _intern (CQueryF t r x) = CQuery (tintern t) r x

{- Evaluation -}
type Goal s   = (Env s, C s)
type Solution d = Either StatixError (IntGraph Label d)

subst :: T s → SolverM s (T s)
subst t = do
  e ← ask
  return $ coerce $ (cook (flip Map.lookup e) (coerce t))

next :: SolverM s ()
next = return ()

solveFocus :: C s → SolverM s ()
solveFocus CTrue  = return ()
solveFocus CFalse = throwError UnsatisfiableError
solveFocus (CEq t1 t2) = do
  t1' ← subst t1
  t2' ← subst t2
  _ ← unifyOccurs (coerce t1') (coerce t2') {- TODO unify -}
  next
solveFocus (CAnd l r) = do
  pushGoal l
  solveFocus r
solveFocus (CEx []     c) = solveFocus c
solveFocus (CEx (n:ns) c) = do
  v ← freeVar
  local (Map.insert n v) (solveFocus (CEx ns c))
solveFocus (CNew t) = do
  t' ← subst t
  u  ← newNode Nothing
  unify (coerce t') (Node u)
  next
solveFocus (CEdge t₁ l t₂) = do
  t₁' ← subst t₁
  t₂' ← subst t₂
  case (coerce t₁' , coerce t₂') of
    (Node n, Node m) → newEdge (n, l, m)
    (UVar x, _)      → pushGoal (CEdge t₁' l t₂')
    (_ , UVar x)     → pushGoal (CEdge t₁' l t₂')
    otherwise        → throwError UnsatisfiableError
solveFocus (CQuery t r x) = do
  PackT t' ← subst t
  x' ← asks (Map.lookup x)
  case x' of
    Nothing → throwError UnboundVariable
    -- if x has an associated semantic variable
    Just v →
      case t' of
        (Node n)  → do
          ans ← runQuery n r
          unify (UVar v) (Answer ans)
          next
        (UVar _)  → pushGoal (CQuery (PackT t') r x)
        otherwise → throwError UnsatisfiableError

kick :: Constraint RawTerm → (forall s. SolverM s (IntGraph Label ()))
kick c = do
    pushGoal (internalize c)
    loop
  where
  loop = do
    st ← get
    c  ← popGoal
    case c of
      Just (env , c) → do
        local (const env) (solveFocus c)
        loop
      Nothing → do
        s ← get
        g ← liftST $ toIntGraph (graph s)
        return (fmap (fmap (\ d → ())) g) {- trash the data in the graph for now -}

eval :: Constraint RawTerm → Solution ()
eval c = runSolver (kick c)

solve :: String → Solution ()
solve prog = eval (parser prog)

check :: String → Bool
check prog = isRight $ solve prog 
