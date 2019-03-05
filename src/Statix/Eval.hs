{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Statix.Eval where

import Prelude hiding (lookup, null)
import Data.Map.Strict hiding (map, null)
import qualified Data.Map.Strict as Map
import qualified Data.IntMap as IM
import Data.Either
import Data.Maybe
import Data.STRef
import Data.Sequence
import Data.Functor.Fixedpoint
import qualified Data.Sequence as Seq

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Trans
import Control.Unification
import Unsafe.Coerce
import Debug.Trace

import Statix.Syntax.Constraint
import Statix.Syntax.Parser
import Statix.Graph
import Statix.Syntax.Parser

{- ST unification variables with identity -}
data STVar s t =
    STVar
        {-# UNPACK #-} !Int
        {-# UNPACK #-} !(STRef s (Maybe (UTerm t (STVar s t))))

instance Show (STVar s t) where
  show (STVar i _) = "UVar " ++ show i

instance Eq (STVar s t) where
  (STVar i _) == (STVar j _) = (i == j)

instance Variable (STVar s t) where
  getVarID (STVar i _) = i


  
{- A Graph monad interface -}
class (Monad m) => MonadGraph n l d m | m -> n l d where

  newNode :: d -> m n
  newEdge :: (n, l, n) → m ()
  datum   :: n → m d



{- Graph node/data types for graph in ST -} 
type STEdge s l d = (l , NodeRef s l d)
data NodeData s l d = NData [STEdge s l d] d
data NodeRef  s l d = NRef !Int !(STRef s (NodeData s l d))

instance Eq (NodeRef s l d) where
  (NRef i _) == (NRef j _) = i == j

instance Show (NodeRef s l d) where
  show (NRef i _) = show i

type STGraph s = [STN s]


  
{- Specialize that stuff for our term language -}
type STN s = NodeRef s Label ()
type STU s = STVar s (TermF (STN s))

type Env s = Map RawVar (STU s)




{- Solver types -}
data Solver s = Solver
  { queue :: Seq (Env s, Constraint (UTerm (TermF (STN s)) (STU s)))
  , nextU :: Int
  , nextN :: Int
  , graph :: STGraph s
  }

emptySolver :: Solver s
emptySolver = Solver
  { queue = Seq.empty
  , nextU = 0
  , nextN = 0
  , graph = []
  }

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

type SolverM s = ReaderT (Env s) (StateT (Solver s) (ErrorT StatixError (ST s)))

runSolver :: (forall s. SolverM s a) → Either StatixError a
runSolver c = runST (runErrorT (evalStateT (runReaderT c Map.empty) emptySolver))

{- Solver is a bunch of stuff -}
liftST :: ST s a → SolverM s a
liftST = lift . lift . lift

liftSt :: StateT (Solver s) (ErrorT StatixError (ST s)) a → SolverM s a
liftSt = lift
  
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

instance BindingMonad (TermF (STN s)) (STU s) (SolverM s) where
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

instance MonadGraph (STN s) Label () (SolverM s) where
  newNode d = do
    ni ← freshNodeName
    nr ← liftST $ newSTRef (NData [] d)
    let node = (NRef ni nr)
    modify (\ s → s { graph = node : graph s })
    return node

  newEdge (NRef i r, l, y) =
    liftST $ modifySTRef r (\case NData es d → NData ((l , y) : es) d)
    
  datum (NRef i r) = do
    NData _ d ← liftST (readSTRef r)
    return d





{- Evaluation -}
type T s = (UTerm (TermF (STN s)) (STU s))
type C s = Constraint (T s)
type Goal s = (Env s, C s)

subst :: T s → SolverM s (T s)
subst t = do
  e ← ask
  return (cook (flip Map.lookup e) t)

solveFocus :: C s → SolverM s ()

solveFocus CTrue  = return ()
solveFocus CFalse = throwError UnsatisfiableError

solveFocus (CEq t1 t2) = do
  t1' ← subst t1
  t2' ← subst t2
  _ ← unifyOccurs t1' t2' {- TODO unify -}
  return ()

solveFocus (CAnd l r) = do
  pushGoal l
  solveFocus r

solveFocus (CEx []     c) = solveFocus c
solveFocus (CEx (n:ns) c) = do
  v ← freeVar
  local (Map.insert n v) (solveFocus (CEx ns c))

solveFocus (CNew t) = do
  t' ← subst t
  u  ← newNode ()
  unify t' (Node u)
  return ()
  
solveFocus c@(CEdge t₁ l t₂) = do
  t₁' ← subst t₁
  t₂' ← subst t₂
  case (t₁' , t₂') of
    (Node n, Node m) → newEdge (n, l, m)
    (UVar x, _)      → pushGoal (CEdge t₁' l t₂')
    (_ , UVar x)     → pushGoal (CEdge t₁' l t₂')
    otherwise        → throwError UnsatisfiableError

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

type Solution = Either StatixError (IntGraph Label ())

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
        ground (graph s)

ground :: STGraph s → SolverM s (IntGraph Label ())
ground stg = do
  ns ← (mapM _groundN stg)
  return (IM.fromList ns)
  where
    _groundE :: STEdge s l d → IntGraphEdge l
    _groundE (l , NRef i r) = IntEdge l i

    _groundN :: NodeRef s l d → SolverM s (Int, IntGraphNode l d)
    _groundN (NRef i r) = do
      (NData es d) ← liftST $ readSTRef r
      let es' = fmap _groundE es
      return (i , IntNode i es' d)

eval :: Constraint RawTerm → Solution
eval c = runSolver (kick c)

solve :: String → Solution
solve prog = eval (parser prog)

check :: String → Bool
check prog = isRight $ solve prog 
