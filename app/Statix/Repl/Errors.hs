module Statix.Repl.Errors where

import System.Exit
import System.Console.ANSI

import Data.List

import Statix.Syntax
import Statix.Analysis.Types
import Statix.Solver.Types as RT

-- |A means to handling various errors in the REPL
class ReplError e where
  report :: e → IO ()

putBold :: String → IO ()
putBold str = do
  setSGR [SetConsoleIntensity BoldIntensity]
  putStr str
  setSGR []

instance ReplError TCError where
  report (ModuleLocal mod e) = do
    putStr $ "In module "
    putBold $ mod ++ " "
    report e
  report (WithPosition (Pos row col) e) = do
    putStr $ "on line " 
    putBold $ show row ++ "@" ++ show col
    putStrLn $ ":"
    report e
  report e = putStrLn (show e)

instance ReplError String where
  report = putStrLn

panic :: ReplError e ⇒ e → IO a
panic e = do
  report e
  exitFailure


-- 23 ├─ some-predicate (x, y, F())
-- 25 ├─ some-other-predicate (Q(), X())
-- 99 ├─ G() == F()
printTrace :: [Traceline] → IO ()
printTrace = mapM_ printEntry
  where
    printQn (mod, pred) = do
      putStr  $ mod ++ "."
      putBold $ pred

    printEntry :: Traceline → IO ()
    printEntry (Within pos c) = do
      putStr $ show pos ++ " ├─ "
      putBold $ c ++ "\n"
    printEntry (Call pos qn params) = do
      putStr   $ show pos ++ " ├─ "
      printQn  $ qn
      putStrLn $ "(" ++ intercalate "," params ++ ")"

instance ReplError StatixError where
  report (Unsatisfiable tr msg) = do
    putStr  $ "Constraint unsatisfiable: "
    putBold $ msg ++ "\n\n"
    printTrace (reverse tr)
  report StuckError =
    putStrLn $ "Stuck"
  report (UnificationError msg) =
    putStrLn $ "Unification failed: " ++ msg
  report (RT.Panic msg) =
    putStrLn $ "Bug: " ++ msg
  report RT.TypeError =
    putStrLn $ "Type error at runtime"
