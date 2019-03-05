module Lib
    ( repl
    ) where

import Statix.Syntax.Parser
import Statix.Eval

repl :: IO ()
repl = do
  prog <- getContents
  let ast = parser prog
  print (eval ast)
