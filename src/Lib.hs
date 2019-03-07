module Lib where

import Data.Either
import Statix.Solver

repl :: IO ()
repl = do
  prog     ← getContents
  let solution = solve prog
  case solution of
    Left e → putStrLn $ "Constraint NOT SOLVED" ++ show e
    Right (φ, g) → do
      putStrLn "Constraint SOLVED:"
      putStrLn "Unifier:"
      putStrLn φ
      putStrLn "Graph:"
      print g
