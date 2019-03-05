module Lib where

import Statix.Eval

repl :: IO ()
repl = do
  prog <- getContents
  print (solve prog)
