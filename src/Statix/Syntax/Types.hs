module Statix.Syntax.Types where

import Data.Default

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

import Statix.Syntax.Terms
import ATerms.Syntax.Types (remainder, input, ParseState)

data Token
  = TokTrue | TokFalse | TokNew | TokIn | TokAs | TokWhere | TokQuery | TokOne
  | TokEvery | TokNonEmpty | TokMin | TokFilter | TokMatch | TokEdge | TokEnd
  | TokPathLex | TokPathRevLex | TokEpsilon
  | TokImports String | TokQName String | TokName String | TokConstructor String
  | TokString String
  | TokTilde | TokUnderscore | TokDash | TokLAngle | TokRAngle | TokBar | TokAmp
  | TokLeftArrow | TokRightArrow | TokColon | TokSemicolon
  | TokOpenArr | TokCloseArr | TokEpsilonArr | TokRegexQuote
  | TokOpenB | TokCloseB | TokOpenBr | TokCloseBr | TokOpenSB | TokCloseSB
  | TokQuote | TokEq | TokNotEq | TokTick | TokStar | TokPlus | TokPeriod
  | TokComma | TokQuestionmark
  | TEOF
  deriving Show

type ParserM a = ReaderT Ident (StateT ParseState (Except String)) a

evalParser :: Ident → String → ParserM a → Either String a
evalParser mod s c =
  runExcept $ evalStateT (runReaderT c mod) (def { input = def { remainder = s }})
