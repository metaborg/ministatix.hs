module Statix.Repl.Errors where

import Data.List

import Statix.Syntax.Constraint
import Statix.Analysis.Types
import Statix.Solver.Types as RT
import Statix.IO

-- |A means to handling various errors in the REPL
class ReplError e where
  report :: e → IO ()

instance ReplError LoadError where
  report (LoadErr mod e) = do
    putStrLn $ "Loading " ++ mod ++ " failed."
    report e
  report (TypeErr mod e) = do
    putStrLn $ "Loading " ++ mod ++ " failed."
    report e

instance ReplError TCError where
  report e = do
    putStrLn $ "Typechecking failed: " ++ show e

instance ReplError String where
  report = putStrLn


-- 23 ├─ some-predicate (x, y, F())
-- 25 ├─ some-other-predicate (Q(), X())
-- 99 ├─ G() == F()
printTrace :: [Traceline] → IO ()
printTrace = mapM_ printEntry
  where
    printEntry :: Traceline → IO ()
    printEntry (Within c) = do
      putStrLn $ "├─ " ++ show c
    printEntry (Call qn params) = do
      putStrLn $ "├─ " ++ showQName qn ++ "(" ++ intercalate "," params ++ ")"

instance ReplError StatixError where
  report (Unsatisfiable tr msg) = do
    putStrLn $ "Constraint unsatisfiable: " ++ msg
    printTrace (reverse tr)
  report StuckError =
    putStrLn $ "Stuck"
  report (UnificationError msg) =
    putStrLn $ "Unification failed: " ++ msg
  report (RT.Panic msg) =
    putStrLn $ "Bug: " ++ msg
  report RT.TypeError =
    putStrLn $ "Type error at runtime"
