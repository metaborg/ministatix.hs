module Lib
    ( someFunc
    ) where

import Statix.Syntax.Parser

someFunc :: IO ()
someFunc = do
  prog <- getContents
  print $ parseConstraint $ lexer prog
