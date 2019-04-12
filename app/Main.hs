module Main where

import Data.Map.Strict
import Control.Monad.State

import qualified Statix.Repl as Repl

main :: IO ()
main = Repl.repl
