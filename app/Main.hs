module Main where

import System.Environment

import qualified Statix.Checker as Checker
import qualified Statix.Repl as Repl

main :: IO ()
main = do
  args ← getArgs
  case args of
    [spec, file] → Checker.main spec file
    otherwise    → Repl.repl
