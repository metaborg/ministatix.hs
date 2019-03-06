module Lib where

import Statix.Solver

repl :: IO ()
repl = do
  prog <- getContents
  print (solve prog)
