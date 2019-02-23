{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Statix.Eval where

import Prelude hiding (lookup)
import Data.Map.Strict hiding (map)
import qualified Data.Map.Strict as Map
import Data.Stream
import Data.Maybe
import Data.STRef

import Control.Monad.ST
import Control.Monad.Reader
import Control.Unification

import Statix.Syntax.Constraint
import Statix.Syntax.Parser

class (Eq n, Eq l, Monad m) => GraphMonad n l d m where

  newNode :: d → m n
  newEdge :: (n , l , n) → m ()

  datum   :: n → m d

{- A GraphMonad based on ST -}
data NodeData s l d = NData [(l , NodeRef s l d)] d
type NodeRef  s l d = STRef s (NodeData s l d)
type M s l d = ST s (NodeData s l d)

instance (Eq l) => (GraphMonad (NodeRef s l d) l d (ST s)) where

  newNode d = do
    newSTRef (NData [] d)

  newEdge (x, l, y) = do
    modifySTRef x (\case NData es d → NData ((l , y) : es) d)
    
  datum n = do
    NData _ d ← readSTRef n
    return d

  
-- step :: Constraint → Eval Constraint
-- step CTrue       = return CTrue
-- step CFalse      = return CFalse
-- step (CEq t1 t2) = do
--   φ₁ ← unifier
--   case unify (subst t1) t2 of
--     Just φ₂ → updateUnifier φ₂
--     Nothing → _

-- step (CEx ns c)  = _
-- step (CNew x)    = _
-- step (CEdge s1 l s2) = _
