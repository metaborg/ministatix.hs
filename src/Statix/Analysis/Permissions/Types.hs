{-# LANGUAGE UndecidableInstances #-}
module Statix.Analysis.Permissions.Types where

import Data.Set (Set, empty, singleton, fromList, insert)
import Data.IntMap.Strict (IntMap, update)
import Data.List (find)

import Control.Monad.Unique
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens

import Statix.Syntax
import Statix.Analysis.Lexical
import Statix.Analysis.Permissions
import Statix.Analysis.Types hiding (PreSymbolTable)

dependencies :: (Ord v) ⇒ Equation a v → Set v
dependencies Bot        = empty
dependencies (Lit _)    = empty
dependencies (V v)      = singleton v
dependencies (Diff v w) = fromList (v:[w])

data Entry v l = PrePerm
  { value :: (Bool, Set l)
  , reqs  :: [Equation (Set l) v]
  , prov  :: [Equation Bool    v]
  , dependants :: Set v
  }

addDependant :: Int → Int → Permalizer l ()
addDependant dep w = do
  _1 %= update (\entry → Just entry { dependants = insert dep (dependants entry) }) w

type PermTable l = IntMap (Entry Int l)

type Permalizer l =
  ReaderT ([[(Ident, Int)]], PreSymbolTable Int)
  (ExceptT TCError
  (State (PermTable l, Int)))

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
    forM_ (dependencies eq) (addDependant v) 

  provide v eq = do
    _1 %= update (\entry →
                   Just entry
                     { prov = eq : prov entry }
                 ) v

    -- add reverse dependencies
    forM_ (dependencies eq) (addDependant v) 

instance MonadUnique Int (Permalizer l) where

instance MonadPermAnalysis l Int (Permalizer l) where
  freshenEnvWith f c = do
    (env, symtab) ← ask
    newenv ← forMOf (each.each) env $ \(id,v) → do
      v' ← fresh
      f v v'
      return (id, v')
    local (const (newenv, symtab)) c
