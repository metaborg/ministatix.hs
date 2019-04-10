{
module Statix.Syntax.Parser where

import Data.List
import qualified Data.Text as Text
import Data.Char
import Data.Default

import Control.Monad.Reader
import Control.Monad.Except

import Statix.Regex
import Statix.Syntax.Constraint

}

%name parseConstraint Constraint
%name parsePredicate  Predicate
%name parseModule     Predicates
%monad {ParserM}

%tokentype { Token }
%error { parseError }

%token
  name      { TokVar $$ }
  true      { TokTrue }
  false     { TokFalse }
  ','       { TokComma }
  '='       { TokEq }
  '{'       { TokOpenBr }
  '}'       { TokCloseBr }
  '('       { TokOpenB }
  ')'       { TokCloseB }
  '['       { TokOpenSB }
  ']'       { TokCloseSB }
  '`'       { TokTick }
  '*'       { TokStar }
  '+'       { TokPlus }
  new       { TokNew }
  arrL      { TokOpenArr }
  arrR      { TokCloseArr }
  query     { TokQuery }
  as        { TokAs }
  in        { TokIn }
  regexquote { TokRegexQuote }
  quote     { TokQuote }
  one       { TokOne }
  every     { TokEvery }
  leftarrow { TokLeftArrow }
  colon     { TokColon }
  period    { TokPeriod }

%%

Constraint : '{' Names '}' Constraint   { CEx $2 $4 }
           | Constraint ',' Constraint	{ CAnd $1 $3 }
           | Term '=' Term		{ CEq $1 $3 }
           | true			{ CTrue }
           | false			{ CFalse }
           | new name			{ CNew $2 }
           | name arrL name arrR name   { CEdge $1 (Lab $3) $5 }
           | query name Regex as name	{ CQuery $2 $3 $5 }
           | one  '(' name ',' Term ')' { COne $3 $5 }
           | every name name Constraint { CEvery $2 $3 $4 }
           | name '(' Terms ')'		{ CApply $1 $3 }
           | '(' Constraint ')'         { $2 }

RegexLit : '`' name          { RMatch (Lab $2) }
         | RegexLit RegexLit { RSeq $1 $2 }
         | RegexLit '*'      { RStar $1 }
         | RegexLit '+'      { rplus $1 }

Regex : RegexLit { $1 }

Names :                { [] }
      | name           { [ $1 ] }
      | Names ',' name { $3 : $1 }

Term  : name '(' Terms ')'      { Con $1 $3 }
      | name                    { Var $1 }

Terms :                         { []  }
       | Term                   { [$1] }
       | Terms ',' Term         { $3 : $1 }

Predicate :
  name '(' Names ')' leftarrow Constraint period
  {%
    do
      mod ← ask
      return (Pred (mod , $1) (mkParams $3) $6)
  }

Predicates :                           { []      }
           | Predicate                 { [$1]    }
           | Predicates Predicate      { $2 : $1 }

{

mkParams = fmap (\id → (id , TBot))

type ParserM a = ReaderT Text.Text (Except String) a

runParser :: Text.Text → ParserM a → Either String a
runParser mod c = runExcept $ runReaderT c mod

data Token
  = TokVar Text.Text
  | TokFalse
  | TokTrue
  | TokComma
  | TokEq
  | TokOpenBr
  | TokCloseBr
  | TokOpenB
  | TokCloseB
  | TokOpenSB
  | TokCloseSB
  | TokOpenArr
  | TokCloseArr
  | TokNew
  | TokQuery
  | TokIn
  | TokAs
  | TokRegexQuote
  | TokStar
  | TokPlus
  | TokQuote
  | TokTick
  | TokOne
  | TokEvery
  | TokLeftArrow
  | TokColon
  | TokPeriod
  deriving Show

parseError :: [Token] -> ParserM a
parseError toks = throwError $ "Parse error while parsing: " ++ show (take 1 toks)

varName :: Token -> Text.Text
varName (TokVar s) = s
varName _ = error "Parser error: not a name"

lexer :: String -> [Token]
lexer []		= []

lexer (c:cs)
  | isSpace c		= lexer cs
  | isAlpha c		= lexWord (c:cs)

lexer ('←':cs)	        = TokLeftArrow : lexer cs
lexer (':':'-':cs)	= TokLeftArrow : lexer cs
lexer (':':cs)		= TokColon : lexer cs
lexer (',':cs)		= TokComma   : lexer cs
lexer ('=':cs)          = TokEq      : lexer cs
lexer ('{':cs)		= TokOpenBr  : lexer cs
lexer ('}':cs)		= TokCloseBr : lexer cs
lexer ('(':cs)		= TokOpenB   : lexer cs
lexer (')':cs)		= TokCloseB  : lexer cs
lexer ('-':'[':cs)	= TokOpenArr : lexer cs
lexer (']':'-':'>':cs)	= TokCloseArr : lexer cs
lexer ('[':cs)		= TokOpenSB  : lexer cs
lexer (']':cs)		= TokCloseSB : lexer cs
lexer ('\'':cs)		= TokQuote : lexer cs
lexer ('`':cs)		= TokTick : lexer cs
lexer ('*':cs)		= TokStar : lexer cs
lexer ('+':cs)		= TokPlus : lexer cs
lexer ('.':cs)		= TokPeriod : lexer cs

lexWord :: String -> [Token]
lexWord cs =
  case span isAlpha cs of
    ("true", ds)  -> TokTrue    : lexer ds
    ("false", ds) -> TokFalse   : lexer ds
    ("new", ds)   -> TokNew     : lexer ds
    ("in", ds)    -> TokIn      : lexer ds
    ("as", ds)    -> TokAs      : lexer ds
    ("query", ds) -> TokQuery   : lexer ds
    ("only", ds)  -> TokOne     : lexer ds
    ("every", ds) -> TokEvery   : lexer ds
    (var, ds)     -> TokVar (Text.pack var) : lexer ds

}
