module Lib
    ( someFunc
    ) where

import Statix.Syntax.Parser

someFunc :: IO ()
someFunc = do
  prog <- getContents
  let ast = parser prog
  print ast
