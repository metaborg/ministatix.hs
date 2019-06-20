{-# LANGUAGE UndecidableInstances #-}
module Statix.Analysis.Permissions.Types where

import Data.Set
  (Set
  , empty, singleton, fromList, insert
  , union, intersection
  , lookupMin, deleteMin)
import Data.IntMap.Strict (IntMap, update, (!))
import qualified Data.IntMap.Strict as IM
import Data.List (find)
import qualified Data.HashMap.Strict as HM
import Data.Default

import Control.Monad.Unique
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens

import Statix.Syntax
import Statix.Analysis.Lexical
import Statix.Analysis.Permissions
import Statix.Analysis.Types hiding (PreSymbolTable)

reqDeps :: (Ord v) ⇒ ReqEqn a v → Set v
reqDeps RBot        = empty
reqDeps (RLit _)    = empty
reqDeps (RV v)      = singleton v
reqDeps (RDiff v w) = fromList (v:[w])

provDeps :: (Ord v) ⇒ ProvEqn a v → Set v
provDeps PBot        = empty
provDeps (PLit _)    = empty
provDeps (PV v)      = singleton v

data Entry v l = Entry
  { value :: (Bool, Set l)
  , reqs  :: [ReqEqn (Set l) v]
  , prov  :: [ProvEqn Bool v]
  , dependants :: Set v
  }

deriving instance (Show v, Show l) ⇒ Show (Entry v l)

instance Default (Entry v l) where
  def = Entry (False, empty) [] [] empty

addDependant :: Int → Int → Permalizer l ()
addDependant dep w = do
  _1 %= update (\entry → Just entry { dependants = insert dep (dependants entry) }) w

type PermTable l = IntMap (Entry Int l)

type Permalizer l =
  ReaderT ([[(Ident, Int)]], PreSymbolTable Int)
  (ExceptT TCError
  (State (PermTable l, Int, Set Int)))

runPermalizer :: Permalizer l a → Either TCError a
runPermalizer c = evalState (runExceptT (runReaderT c ([], HM.empty))) (IM.empty, 0, empty)

instance MonadLex (Ident, Int) IPath Int (Permalizer l) where
  type FrameDesc (Permalizer l) = ()

  enter _ = local (\(env, st) → ([]:env, st))

  intros bs = local (\(sc:env, st) → ((bs ++ sc):env, st))

  resolve pth = do
    env ← asks fst
    let v = (popAll pth env) >>= \(id, vs) → find ((==) id . fst) vs
    case v of
      Just (id, v) → return v
      Nothing      → throwError $ Panic "Permissions analysis bug: please report"

instance MonadPermission (Permalizer l) Int l where

  require v eq = do
    _1 %= (update (\entry →
                   Just entry
                     { reqs = eq : reqs entry }
                 ) v)

    -- add reverse dependencies
    forM_ (reqDeps eq) (addDependant v) 

  provide v eq = do
    _1 %= update (\entry →
                   Just entry
                     { prov = eq : prov entry }
                 ) v

    -- add reverse dependencies
    forM_ (provDeps eq) (addDependant v) 

instance MonadUnique Int (Permalizer l) where

  fresh = do
    v ← use _2

    -- update the seed
    _2 %= (+1)

    -- add the new variable to the table
    _1 %= (IM.insert v def)

    -- add the new variable to the worklist
    push (singleton v)

    return v

  updateSeed seed = _2 %= const seed
  
instance MonadPermAnalysis l Int (Permalizer l) where
  freshenEnvWith f c = do
    (env, symtab) ← ask
    newenv ← forMOf (each.each) env $ \(id,v) → do
      v' ← fresh
      f v v'
      return (id, v')
    local (const (newenv, symtab)) c

instance SortaLattice Bool where
  bot   = False
  lmeet = (&&)
  ljoin = (||)

instance Ord a ⇒ SortaLattice (Set a) where
  bot   = empty
  lmeet = intersection
  ljoin = union

pop :: Permalizer l (Maybe Int)
pop = do
  vs ← use _3
  let (v, vs') = (lookupMin vs, deleteMin vs)
  _3 %= const vs'
  return v

push :: Set Int → Permalizer l ()
push vs = do
  _3 %= union vs

-- | Compute the least fixedpoint over the equations in the permalizer
lfp :: (Ord l) ⇒ Permalizer l (IntMap (Bool, Set l))
lfp = do
  v ← pop

  case v of
    Nothing → do
      -- done; extract the results
      use (_1.to (fmap value))

    Just v  → do
      (Entry val reqEq provEq deps) ← use (_1.to (!v))

      -- build the environment for evaluation of equations
      table ← use _1
      let eqEnv = \v → value $ table ! v

      -- recompute the value using the equations
      let prov = foldl (\b eqn  → ljoin b  (provEval eqn (fst.eqEnv))) False provEq
      let reqs = foldl (\rs eqn → ljoin rs (reqEval eqn eqEnv)) empty reqEq

      -- push new work if value changed
      if (prov, reqs) /= val
        then do
          push deps
          _1 %= (update (\entry → Just $ entry { value = (prov, reqs) }) v)
        else return ()

      lfp
