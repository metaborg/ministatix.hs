module Lib where

import System.IO
import System.Console.ANSI

import Data.Either
import Statix.Solver
import Statix.Solver.Types

prompt :: IO ()
prompt = do
  putStr "> "
  hFlush stdout

printSolution :: Solution → IO ()
printSolution solution =
  case solution of
    Left e → do
      setSGR [SetColor Foreground Vivid Red]
      putStrLn $ "∙ ⟨×⟩ - " ++ show e
      setSGR [Reset]
    Right (φ, g) → do
      setSGR [SetColor Foreground Dull Green]
      putStrLn "∙ ✓ Satisfiable"
      setSGR [SetColor Foreground Vivid White]
      putStrLn "▸ Unifier"
      setSGR [Reset]
      putStrLn φ
      setSGR [SetColor Foreground Vivid White]
      putStrLn "▸ Graph"
      setSGR [Reset]
      print g
      setSGR [Reset]

repl :: IO ()
repl = do
  prompt

  prog ← getLine

  let solution = solve prog
  printSolution solution

  repl
