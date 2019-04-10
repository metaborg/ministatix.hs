module Statix.Repl.Errors where

import Statix.Analysis.Types

-- |A means to handling various errors in the REPL
class ReplError e where
  report :: e → IO ()

instance ReplError TCError where
  report = print

instance ReplError String where
  report = putStrLn
