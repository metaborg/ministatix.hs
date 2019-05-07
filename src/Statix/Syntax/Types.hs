module Statix.Syntax.Types where

import Data.Default

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

import Statix.Syntax.Terms
import Statix.Syntax.Constraint
import ATerms.Syntax.Types (remainder, input, ParseState)

data Token
  = TokTrue | TokFalse | TokNew | TokIn | TokAs | TokWhere | TokQuery | TokOne
  | TokEvery | TokMin | TokFilter | TokMatch | TokEdge | TokEnd | TokImport
  | TokPathLT | TokEpsilon
  | TokQName String
  | TokName String
  | TokConstructor String
  | TokTilde | TokUnderscore | TokLAngle | TokRAngle | TokBar | TokAmp
  | TokLeftArrow | TokRightArrow | TokColon | TokSemicolon
  | TokOpenArr | TokCloseArr | TokRegexQuote
  | TokOpenB | TokCloseB | TokOpenBr | TokCloseBr | TokOpenSB | TokCloseSB
  | TokQuote | TokEq | TokTick | TokStar | TokPlus | TokPeriod | TokComma
  | TokQuestionmark
  | TNL
  | TEOF
  deriving Show

type ParserM a = ReaderT Ident (StateT ParseState (Except String)) a

evalParser :: Ident → String → ParserM a → Either String a
evalParser mod s c =
  runExcept $ evalStateT (runReaderT c mod) (def { input = def { remainder = s }})
