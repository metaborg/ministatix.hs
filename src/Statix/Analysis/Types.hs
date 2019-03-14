module Statix.Analysis.Types where

import Data.HashMap.Strict
import Control.Monad.Except

import Statix.Syntax.Constraint

data TCError =
    DuplicatePredicate String
  | UnboundPredicate String deriving (Show)

type TCM = Except TCError

type Context = HashMap String QName

runTC :: TCM a → Either TCError a
runTC c = runExcept c
