{
module Statix.Syntax.Parser where

import Data.List
import Data.Char

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

%%

Constraint : '{' Names '}' Constraint { CEx $2 $4 }
           | Constraint ',' Constraint { CAnd $1 $3 }
           | Term '=' Term       { CEq $1 $3 }
           | true                { CTrue }
           | false               { CFalse }

Names : name           { [ $1 ] }
      | Names ',' name { $3 : $1 }

Term  : name '(' Terms ')'      { TCon $1 $3 }

Terms :                         { []  }
       | Term                   { [$1] }
       | Terms ',' Term         { $3 : $1 }

{

parseError :: [Token] -> error
parseError _ = error "Parse error!"

data Term
  = TCon String ([ Term ])
  deriving Show

data Constraint
  = CTrue | CFalse
  | CAnd Constraint Constraint
  | CEq Term Term
  | CEx [String] Constraint
  deriving Show

data Token
  = TokVar String
  | TokTrue
  | TokFalse
  | TokComma
  | TokEq
  | TokOpenBr
  | TokCloseBr
  | TokOpenB
  | TokCloseB
  | TokOpenSB
  | TokCloseSB
  deriving Show

varName :: Token -> String
varName (TokVar s) = s
varName _ = error "Parser error: not a name"

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
  | isSpace c = lexer cs
  | isAlpha c = lexVar (c:cs)
lexer (',':cs) = TokComma   : lexer cs
lexer ('=':cs) = TokEq      : lexer cs
lexer ('{':cs) = TokOpenBr  : lexer cs
lexer ('}':cs) = TokCloseBr : lexer cs
lexer ('(':cs) = TokOpenB   : lexer cs
lexer (')':cs) = TokCloseB  : lexer cs
lexer ('[':cs) = TokOpenSB  : lexer cs
lexer (']':cs) = TokCloseSB : lexer cs

lexVar :: String -> [Token]
lexVar cs =
  case span isAlpha cs of
    ("true", ds)  -> TokTrue    : lexer ds
    ("false", ds) -> TokFalse   : lexer ds
    (var, ds)     -> TokVar var : lexer ds

parser = getContents >>= print . parseConstraint . lexer

}
