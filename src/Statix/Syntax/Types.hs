module Statix.Syntax.Types where

import Data.Text (Text)
import Data.Default

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

import Statix.Syntax.Constraint
import ATerms.Syntax.Types (remainder, input, ParseState)

data Token
  = TokVar Text
  | TokFalse | TokTrue | TokEq | TokNew | TokQuery | TokMatch
  | TokIn | TokAs | TokWhere
  | TokOne | TokEvery | TokMin | TokFilter | TokEdge | TokEnd | TokPathLT
  | TokRegexQuote | TokStar | TokPlus | TokTick | TokColon | TokPeriod
  | TokComma | TokOpenBr | TokCloseBr | TokOpenB | TokCloseB | TokOpenSB | TokCloseSB
  | TokOpenArr | TokCloseArr | TokQuote | TokLeftArrow | TokRightArrow | TokBar
  | TokRAngle | TokLAngle | TokImport | TokNewline
  | TokModpath String | TEOF deriving Show

type ParserM a = ReaderT Ident (StateT ParseState (Except String)) a

evalParser :: Ident → String → ParserM a → Either String a
evalParser mod s c =
  runExcept $ evalStateT (runReaderT c mod) (def { input = def { remainder = s }})
