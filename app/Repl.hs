module Repl where

import System.IO
import System.Console.ANSI

import Data.Map.Strict as Map
import Data.Char

import Statix.Syntax.Constraint
import Statix.Solver
import Statix.Solver.Types
import Statix.Syntax.Parser

data Cmd
  = Define (Predicate RawTerm)
  | Main RawConstraint
  | Load String

instance Read Cmd where

  readsPrec _ s

    -- if starts with a colon, then we parse a command
    | (':':xs) ← s =
        case (span isAlpha xs) of
          ("def", ys) →
            let p = parsePredicate (lexer ys) in
            [(Define p, [])]
          ("load", ys) →
            [(Load ys, [])]

    -- otherwise it is just a constraint
    | otherwise   =
      let c = parseConstraint (lexer s)
      in [(Main c, [])]

prompt :: IO ()
prompt = do
  putStr "► "
  hFlush stdout

printSolution :: Solution → IO ()
printSolution solution =
  case solution of
    Left e → do
      setSGR [SetColor Foreground Vivid Red]
      putStrLn $ "  ⟨×⟩ - " ++ show e
      putStrLn ""
      setSGR [Reset]
    Right (φ, g) → do
      setSGR [SetColor Foreground Dull Green]
      putStrLn "  ⟨✓⟩ Satisfiable"
      setSGR [SetColor Foreground Vivid White]
      putStrLn "  ♯ Unifier"
      setSGR [Reset]
      putStrLn φ
      setSGR [SetColor Foreground Vivid White]
      putStrLn "  ♯ Graph"
      setSGR [Reset]
      print g
      setSGR [Reset]

repl :: IO ()
repl = loop Map.empty
  where
  loop :: Program → IO ()
  loop preds = do
    prompt

    cmd ← read <$> getLine

    case cmd of
      (Main c)   → do
        let solution = solve preds c
        putStrLn ""
        printSolution solution
        loop preds
      (Define p) → do
        loop (Map.insert (predname p) p preds)
