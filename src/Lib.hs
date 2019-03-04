module Lib
    ( someFunc
    ) where

import Statix.Syntax.Parser

someFunc :: IO ()
someFunc = print "hi"
-- do
--   prog <- getContents
--   let ast = parser prog
--   print ast
