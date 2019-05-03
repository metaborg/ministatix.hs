{
module Statix.Syntax.Parser (parseConstraint, parsePredicate, parseModule) where

import Data.List
import qualified Data.Text as Text
import Data.Char
import Data.Default

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

import Statix.Regex

import Statix.Syntax.Constraint
import Statix.Syntax.Types
import Statix.Syntax.Lexer

import ATerms.Syntax.Types (input, remainder, line, prev)

}

%name parseConstraintAct Constraint
%name parsePredicateAct  Predicate
%name parseModuleAct     Module
%monad {ParserM}
%lexer {lexer} {TEOF}

%tokentype { Token }
%error { parseError }

%token
  name          { TokName $$ }
  constructor   { TokConstructor $$ }
  modpath       { TokModpath $$ }
  true          { TokTrue }
  false         { TokFalse }
  ','           { TokComma }
  '='           { TokEq }
  '{'           { TokOpenBr }
  '}'           { TokCloseBr }
  '('           { TokOpenB }
  ')'           { TokCloseB }
  '['           { TokOpenSB }
  ']'           { TokCloseSB }
  '`'           { TokTick }
  '*'           { TokStar }
  '+'           { TokPlus }
  '|'           { TokBar }
  '<'           { TokLAngle }
  where         { TokWhere }
  new           { TokNew }
  arrL          { TokOpenArr }
  arrR          { TokCloseArr }
  query         { TokQuery }
  as            { TokAs }
  in            { TokIn }
  regexquote    { TokRegexQuote }
  quote         { TokQuote }
  one           { TokOne }
  every         { TokEvery }
  min           { TokMin }
  filter        { TokFilter }
  leftarrow     { TokLeftArrow }
  colon         { TokColon }
  period        { TokPeriod }
  rightarrow    { TokRightArrow }
  match         { TokMatch }
  end           { TokEnd }
  edge          { TokEdge }
  import        { TokImport }
  lexico        { TokPathLT }
  newline       { TokNewline }

%%

Eq              : Term '=' Term                         { ($1, $3) }
Eqs             :                                       { [] }
                | Eq                                    { [ $1 ] }
                | Eqs ',' Eq                            { $3 : $1 }
WhereClause     :                                       { [] }
                | where Eqs                             { $2 }

Pattern         : Term                                  { $1 }
Matcher         : Pattern WhereClause                   { Matcher [] $1 $2 }

Branch          : Matcher rightarrow Constraint         { Branch $1 $3 }
Branches        : Branch                                { [ $1 ] }
                | Branches '|' Branch                   { $3 : $1 }

Lambda          : '(' Branch ')'                        { $2 }

LabelLT         : Label '<' Label                       { ($1, $3) }
LabelLTs        :                                       { [] }
                | LabelLT                               { [ $1 ] }
                | LabelLTs ',' LabelLT                  { $3 : $1 }

PathComp        : lexico '(' LabelLTs ')'               { Lex $3 }

Constraint      : '{' Names '}' Constraint              { CEx (reverse $2) $4 }
                | Constraint ',' Constraint             { CAnd $1 $3 }
                | Term '=' Term                         { CEq $1 $3 }
                | true                                  { CTrue }
                | false                                 { CFalse }
                | new name rightarrow Term              { CNew $2 $4 }
                | new name                              { CNew $2 unitTm }
                | name rightarrow Term                  { CData $1 $3 }
                | name arrL Term arrR name              { CEdge $1 $3 $5 }
                | query name Regex as name              { CQuery $2 $3 $5 }
                | one  '(' name ',' Term ')'            { COne $3 $5 }
                | every name Lambda                     { CEvery $2 $3 }
                | min name PathComp name                { CMin $2 $3 $4 }
                | filter name '(' Matcher ')' name      { CFilter $2 (MatchDatum $4) $6 }
                | name '(' Terms ')'                    { CApply $1 (reverse $3) }
                | '(' Constraint ')'                    { $2 }
                | Term match '{' Branches '}'           { CMatch $1 (reverse $4) }

RegexLit        : Label                                 { RMatch $1 }
                | RegexLit RegexLit                     { RSeq $1 $2 }
                | RegexLit '*'                          { RStar $1 }
                | RegexLit '+'                          { rplus $1 }

Regex           : RegexLit                              { $1 }

Names           :                                       { [] }
                | name                                  { [ $1 ] }
                | Names ',' name                        { $3 : $1 }

Label           : '`' constructor                       { Lab $2 }

Term            : Label                                 { Label $1 Nothing }
                | Label '(' Term ')'                    { Label $1 (Just $3) }
                | edge '(' name ',' Term ',' Term ')'   { PathCons $3 $5 $7 }
                | end  '(' name ')'                     { PathEnd $3 }
                | constructor '(' Terms ')'             { funcTm $1 (reverse $3) }
                | name                                  { Var $1 }
                | Term colon Term                       { consTm $1 $3 }
                | '[' ']'                               { nilTm }
                | '(' Terms ')'                         { tupleTm $2 }

Terms           :                                       { []  }
                | Term                                  { [$1] }
                | Terms ',' Term                        { $3 : $1 }

Predicate       :
  name '(' Names ')' leftarrow Constraint period        {%
    do
      mod ← ask
      return (Pred (mod , $1) (reverse $ mkParams $3) $6)
  }

Predicates      :                                       { []      }
                | Predicate                             { [$1]    }
                | Predicates Predicate                  { $2 : $1 }

Module          : Predicates                            { Mod [] $1 }

{

mkParams = fmap (\id → (id , TBot))

parseError :: Token -> ParserM a
parseError toks = do
  s ← gets input
  let rem = remainder s
  let c = prev s
  throwError $
    "Parse error:"
    ++ "\n" ++ show (line s) ++ " | ... " ++ c : takeWhile ((/=) '\n') rem
    ++ "\n" ++ take 8 (repeat ' ') ++ "^"

parseConstraint :: Ident → String → Either String Constraint₀
parseConstraint mod s = evalParser mod s parseConstraintAct

parsePredicate :: Ident → String → Either String Predicate₀
parsePredicate mod s = evalParser mod s parsePredicateAct

parseModule :: Ident → String → Either String RawModule
parseModule mod s = evalParser mod s parseModuleAct

}
