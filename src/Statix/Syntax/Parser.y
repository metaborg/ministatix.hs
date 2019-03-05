{
{-# LANGUAGE RankNTypes #-}
module Statix.Syntax.Parser where

import Data.List
import Data.Char

import Statix.Regex
import Statix.Syntax.Constraint

}

%name parseConstraint
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

%%

Constraint : '{' Names '}' Constraint { CEx $2 $4 }
           | Constraint ',' Constraint { CAnd $1 $3 }
           | Term '=' Term       { CEq $1 $3 }
           | true                { CTrue }
           | false               { CFalse }
           | new name            { CNew (RVar $2) }
           | Term arrL name arrR Term { CEdge $1 $3 $5 }
           | query name Regex as name { CQuery (RVar $2) $3 $5 }
           | one '(' name ',' Term ')' { COne $3 $5 }

RegexLit : '`' name          { RMatch $2  }
         | RegexLit RegexLit { RSeq $1 $2 }
         | RegexLit '*'      { RStar $1 }
         | RegexLit '+'      { rplus $1 }

Regex : RegexLit { $1 }

Names : name           { [ $1 ] }
      | Names ',' name { $3 : $1 }

Term  : name '(' Terms ')'      { RCon $1 $3 }
      | name                    { RVar $1 }

Terms :                         { []  }
       | Term                   { [$1] }
       | Terms ',' Term         { $3 : $1 }

{

data Token
  = TokVar String
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
  deriving Show

parseError :: [Token] -> error
parseError _ = error "Parse error!"

varName :: Token -> String
varName (TokVar s) = s
varName _ = error "Parser error: not a name"

lexer :: String -> [Token]
lexer [] = []

lexer (c:cs)
  | isSpace c = lexer cs
  | isAlpha c = lexWord (c:cs)

lexer (',':cs) = TokComma   : lexer cs
lexer ('=':cs) = TokEq      : lexer cs

lexer ('{':cs) = TokOpenBr  : lexer cs
lexer ('}':cs) = TokCloseBr : lexer cs

lexer ('(':cs) = TokOpenB   : lexer cs
lexer (')':cs) = TokCloseB  : lexer cs

lexer ('-':'[':cs) = TokOpenArr : lexer cs
lexer (']':'-':'>':cs) = TokCloseArr : lexer cs

lexer ('[':cs) = TokOpenSB  : lexer cs
lexer (']':cs) = TokCloseSB : lexer cs

lexer ('\'':cs) = TokQuote : lexer cs

lexer ('`':cs)  = TokTick : lexer cs
lexer ('*':cs)  = TokStar : lexer cs
lexer ('+':cs)  = TokPlus : lexer cs

lexWord :: String -> [Token]
lexWord cs =
  case span isAlpha cs of
    ("true", ds)  -> TokTrue    : lexer ds
    ("false", ds) -> TokFalse   : lexer ds
    ("new", ds)   -> TokNew     : lexer ds
    ("in", ds)    -> TokIn      : lexer ds
    ("as", ds)    -> TokAs      : lexer ds
    ("query", ds) -> TokQuery   : lexer ds
    ("one", ds)   -> TokOne     : lexer ds
    (var, ds)     -> TokVar var : lexer ds

parser :: String -> Constraint RawTerm 
parser = parseConstraint . lexer

}
