module Statix.Syntax.Types where

import Data.Default

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

import Statix.Syntax.Terms
import Statix.Syntax.Constraint
import ATerms.Syntax.Types (remainder, input, ParseState)

data Token
  = TokName String | TokConstructor String
  | TokFalse | TokTrue | TokEq | TokNotEq | TokNew | TokQuery | TokMatch
  | TokIn | TokAs | TokWhere
  | TokOne | TokNonEmpty | TokEvery | TokMin | TokFilter | TokEdge | TokEnd | TokPathLT
  | TokEpsilon | TokRegexQuote | TokStar | TokPlus | TokTick | TokColon | TokPeriod
  | TokUnderscore | TokComma | TokOpenBr | TokCloseBr | TokOpenB | TokCloseB | TokOpenSB | TokCloseSB
  | TokOpenArr | TokCloseArr | TokQuote | TokLeftArrow | TokRightArrow | TokBar | TokAmp | TokTilde | TokQuestionmark
  | TokRAngle | TokLAngle | TokImport | TokNewline
  | TokModpath String | TEOF deriving Show

type ParserM a = ReaderT Ident (StateT ParseState (Except String)) a

evalParser :: Ident → String → ParserM a → Either String a
evalParser mod s c =
  runExcept $ evalStateT (runReaderT c mod) (def { input = def { remainder = s }})
