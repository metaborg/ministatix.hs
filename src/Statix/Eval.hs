{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Statix.Eval where

import Prelude hiding (lookup, null)
import Data.Map.Strict hiding (map, null)
import qualified Data.Map.Strict as Map
import Data.Stream
import Data.Maybe
import Data.STRef
import Data.Sequence
import qualified Data.Sequence as Seq

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Trans
import Control.Unification

import Statix.Syntax.Constraint
import Statix.Syntax.Parser



{- ST unification variables with identity -}
data STVar s t =
    STVar
        {-# UNPACK #-} !Int
        {-# UNPACK #-} !(STRef s (Maybe (UTerm t (STVar s t))))

instance Show (STVar s t) where
    show (STVar i _) = "STVar " ++ show i

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
data NodeData s l d = NData [(l , NodeRef s l d)] d
data NodeRef  s l d = NRef !Int !(STRef s (NodeData s l d))

instance Eq (NodeRef s l d) where
  (NRef i _) == (NRef j _) = i == j

-- newtype STG s l d a = STG { unSTG :: ST s a}

-- instance Functor (STG s l d) where
--   fmap f = STG . fmap f . unSTG

-- instance Applicative (STG s l d) where
--   pure   = return
--   (<*>)  = ap
--   (*>)   = (>>)
--   x <* y = x >>= \a -> y >> return a

-- instance Monad (STG s l d) where
--   return v = STG (return v)
--   m >>= f  = STG (unSTG m >>= unSTG . f)

-- {- ST can be graph monad! -}
-- instance (Eq l) ⇒ MonadGraph (NodeRef s l d) l d (STG s l (NodeData s l d)) where
--   newNode d = do
--     r ← STG $ newSTRef (NData [] d)
--     i ← _
--     return (NRef i r)

--   newEdge (x, l, y) =
--     STG $ modifySTRef x (\case NData es d → NData ((l , y) : es) d)
    
--   datum n = do
--     NData _ d ← STG (readSTRef n)
--     return d

-- instance (MonadGraph n l d m) ⇒ MonadGraph n l d (ReaderT e m) where
--   newNode d = lift (newNode d)
--   newEdge e = lift (newEdge e)
--   datum n   = lift (datum n)

-- instance (MonadGraph n l d m) ⇒ MonadGraph n l d (StateT s m) where
--   newNode d = lift (newNode d)
--   newEdge e = lift (newEdge e)
--   datum n   = lift (datum n)

-- instance (Error e, MonadGraph n l d m) ⇒ MonadGraph n l d (ErrorT e m) where
--   newNode d = lift (newNode d)
--   newEdge e = lift (newEdge e)
--   datum n   = lift (datum n)






  
{- Specialize that stuff for our term language -}
type STN s = NodeRef s Label ()
type STU s = STVar s (TermF (STN s))

type Env s = Map RawVar (STU s)




{- Solver types -}
data Solver s = Solver
  { queue :: Seq (Env s, Constraint (UTerm (TermF (STN s)) (STU s)))
  , nextU :: Int
  , nextN :: Int
  }

data StatixError =
    UnificationError
  | UnboundVariable
  | UnsatisfiableError
  | Panic String

instance Error StatixError where
  strMsg = Panic

instance Fallible t v StatixError where
  occursFailure v t     = UnsatisfiableError
  mismatchFailure t1 t2 = UnsatisfiableError

type SolverM s =
  ReaderT (Env s)
  (StateT (Solver s)
   (ErrorT StatixError (ST s)))




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
    let xi = nextU sv
    xr     ← liftST $ newSTRef Nothing
    return (STVar xi xr)

  bindVar (STVar _ xr) t = do
    liftST $ writeSTRef xr (Just t)

instance MonadGraph (STN s) Label () (SolverM s) where
  newNode d = do
    ni ← freshNodeName
    nr ← liftST $ newSTRef (NData [] d)
    return (NRef ni nr)

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
  case (cook (\ x → Map.lookup x e) t) of
    Nothing → throwError UnboundVariable
    Just t  → return t

solve :: C s → SolverM s ()

solve CTrue  = return ()
solve CFalse = throwError UnsatisfiableError

solve (CEq t1 t2) = do
  t1' ← subst t1
  t2' ← subst t2
  _ ← t1' =:= t2'
  return ()

solve (CAnd l r) = do
  pushGoal l
  solve r

solve (CEx (n:ns) c) = do
  v ← freeVar
  local (Map.insert n v) (solve c)

solve (CNew t)
  | (UVar x) ← t = do
    u ← newNode ()
    bindVar x (Node u)
    return ()
  | otherwise =
    throwError UnsatisfiableError


solve c@(CEdge t₁ l t₂)
  | (Node n) ← t₁, (Node m) ← t₂ = newEdge (n, l, m)
  | (UVar x) ← t₁                = pushGoal c
  | (UVar x) ← t₂                = pushGoal c
  | otherwise                    = throwError UnsatisfiableError

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

eval :: SolverM s Bool
eval = do
  st ← get
  c  ← popGoal
  case c of
    Just (env , c) → do
      local (const env) (solve c)
      eval
    Nothing →
      return True
