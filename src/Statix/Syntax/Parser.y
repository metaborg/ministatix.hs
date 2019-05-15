-- Module Header ---------------------------------------------------------------
{
{-# LANGUAGE CPP #-}

#undef __GLASGOW_HASKELL__
#define __GLASGOW_HASKELL__ 709
module Statix.Syntax.Parser (parseConstraint, parsePredicate, parseModule) where

import Data.List
import Data.Char
import Data.Default
import Data.Functor.Sum
import Data.Functor.Fixedpoint

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

import Statix.Regex

import Statix.Syntax.Terms
import Statix.Syntax.Constraint hiding (position)
import Statix.Syntax.Surface as Surf
import Statix.Syntax.Types
import Statix.Syntax.Typing
import Statix.Syntax.Lexer

import ATerms.Syntax.Types (input, remainder, position, prev, Pos(..))

}

%name parseConstraintAct Constraint
%name parsePredicateAct  Predicate
%name parseModuleAct     Module
%monad {ParserM}
%lexer {lexer} {TEOF}

%tokentype { Token }
%error { parseError }

%token
  NAME          { TokName $$ }
  CONSTRUCTOR   { TokConstructor $$ }
  QNAME         { TokQName $$ }
  true          { TokTrue }
  false         { TokFalse }
  eq            { TokEq }
  ineq          { TokNotEq }
  ','           { TokComma }
  '{'           { TokOpenBr }
  '}'           { TokCloseBr }
  '('           { TokOpenB }
  ')'           { TokCloseB }
  '['           { TokOpenSB }
  ']'           { TokCloseSB }
  '`'           { TokTick }
  '*'           { TokStar }
  '+'           { TokPlus }
  '?'           { TokQuestionmark }
  '|'           { TokBar }
  '&'           { TokAmp }
  '<'           { TokLAngle }
  '_'           { TokUnderscore }
  '~'           { TokTilde }
  'e'           { TokEpsilon }
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
  nempty        { TokNonEmpty }
  min           { TokMin }
  filter        { TokFilter }
  leftarrow     { TokLeftArrow }
  colon         { TokColon }
  semicolon     { TokSemicolon }
  period        { TokPeriod }
  rightarrow    { TokRightArrow }
  match         { TokMatch }
  end           { TokEnd }
  edge          { TokEdge }
  import        { TokImports $$ }
  lexico        { TokPathLT }

%left '|'
%left '&'
%right CONCAT
%left '?'
%left '+'
%left '*'
%left '~'

%right colon

%%

Guard           : Term eq Term                                  { GEq $1 $3 }
                | Term ineq Term                                { GNotEq $1 $3 }
WhereClause     :                                               { [] }
                | where sep(Guard, ',')                         { $2 }

Pattern         : Label                                         { PatTm $ TLabelF $1 Nothing }
                | Label '(' Pattern ')'                         { PatTm $ TLabelF $1 (Just $3) }
                | edge '(' Pattern ',' Pattern ',' Pattern ')'  { PatTm $ TPathConsF $3 $5 $7 }
                | end  '(' Pattern ')'                          { PatTm $ TPathEndF $3 }
                | NAME                                          { PatTm $ TVarF $1 }

                | CONSTRUCTOR '(' Patterns ')'                  { funcPat $1 $3 }
                | Pattern colon Pattern                         { consPat $1 $3 }
                | '[' ']'                                       { nilPat }
                | '(' Pattern ',' PatternsPlus ')'              { tuplePat ($2:$4) }

                | '_'                                           { Wildcard }
                | '(' Pattern ')'                               { $2 }

Patterns        : sep(Pattern, ',')                             { $1 }
PatternsPlus    : sep1(Pattern, ',')                            { $1 }

Matcher         : Pattern WhereClause                           { Surf.Matcher [] $1 $2 }

Branch          : Matcher rightarrow Constraint                 { Surf.Branch $1 $3 }
Branches        : sep(Branch, '|')                              { $1 }

Lambda          : '(' Branch ')'                                { $2 }

LabelLT         : Label '<' Label                               { ($1, $3) }
LabelLTs        : sep(LabelLT, ',')                             { $1 }
PathComp        : lexico '(' LabelLTs ')'                       { Lex $3 }
Constraint      : '{' Names '}' Constraint                      { core $ CExF $2 $4 }
                | Constraint ',' Constraint                     { core $ CAndF $1 $3 }
                | Term eq Term                                  { core $ CEqF $1 $3 }
                | Term ineq Term                                { core $ CNotEqF $1 $3 }
                | true                                          { core $ CTrueF }
                | false                                         { core $ CFalseF }
                | new NAME rightarrow Term                      { core $ CNewF $2 $4 }
                | new NAME                                      { core $ CNewF $2 unitTm }
                | NAME rightarrow Term                          { core $ CDataF $1 $3 }
                | NAME arrL Term arrR NAME                      { core $ CEdgeF $1 $3 $5 }
                | query NAME Regex as NAME                      { core $ CQueryF $2 $3 $5 }
                | one  '(' NAME ',' Term ')'                    { core $ COneF $3 $5 }
                | nempty '(' NAME  ')'                          { core $ CNonEmptyF $3 }
                | min NAME PathComp NAME                        { core $ CMinF $2 $3 $4 }
                | NAME '('  sep(Term, ',') ')'                  { core $ CApplyF $1 $3 }

                | every NAME Lambda                             { ext $ SEveryF $2 $3 }
                | filter NAME '(' Matcher ')' NAME              { ext $ SFilterF $2 (Surf.MatchDatum $4) $6 }
                | Term match '{' Branches '}'                   { ext $ SMatchF $1 $4 }

                | '(' Constraint ')'                            { $2 }

RegexLit        : Label                                         { RMatch $1 }
                | RegexLit RegexLit %prec CONCAT                { RSeq $1 $2 }
                | RegexLit '|' RegexLit                         { RAlt $1 $3 }
                | RegexLit '&' RegexLit                         { RAnd $1 $3 }
                | RegexLit '*'                                  { RStar $1 }
                | RegexLit '+'                                  { rplus $1 }
                | RegexLit '?'                                  { rquestion $1 }
                | '~' RegexLit                                  { RNeg $2 }
                | 'e'                                           { Rε }
                | '(' RegexLit ')'                              { $2 }

Regex           : RegexLit                                      { $1 }

Names           : sep(NAME, ',')                                { $1 }

Label           : '`' CONSTRUCTOR                               { Lab $2 }

Term            : Label                                         { Label $1 Nothing }
                | Label '(' Term ')'                            { Label $1 (Just $3) }
                | CONSTRUCTOR '(' sep(Term, ',') ')'            { funcTm $1 $3 }
                | NAME                                          { Var $1 }
                | Term colon Term                               { consTm $1 $3 }
                | '[' ']'                                       { nilTm }
                | '(' Term ',' sep1(Term, ',') ')'              { tupleTm ($2:$4) }
                | '(' Term ')'                                  { $2 }

Predicate       :
  NAME '(' Names ')' leftarrow Constraint period                {%
    do
      mod ← ask
      return (Pred (mod , $1) $3 $6)
  }
Predicates      : list(Predicate)                               { $1 }

Import          : import                                        { $1 }
Imports         : list(Import)                                  { $1 }

Module          : Imports Predicates                            {%
    do
      mod <- ask
      return (RawMod mod $1 $2)
  }

either(p, q)    : p                                             { Left  $1 }
                | q                                             { Right $1 }
or(p, q)        : p                                             { $1 }
                | q                                             { $1 }

opt(p)          : {- empty -}                                   { Nothing }
                | p                                             { Just $1 }

sep1(p, q)      : p list(snd(q, p))                             { $1 : $2 }
sep(p, q)       : {- empty -}                                   { [] }
                | sep1(p, q)                                    { $1 }

fst(p, q)       : p q                                           { $1 }
snd(p, q)       : p q                                           { $2 }

list1(p)        : rev_list1(p)                                  { reverse $1 }
list(p)         : {- empty -}                                   { [] }
                | list1(p)                                      { $1 }

rev_list1(p)    : p                                             { [$1] }
                | rev_list1(p) p                                { $2 : $1 }

{

core c = do
  pos ← gets (position.input)
  return $ Ann pos (InL c)

ext c = do
  pos ← gets (position.input)
  return $ Ann pos (InR c)

parseError :: Token -> ParserM a
parseError toks = do
  s ← gets input
  let rem = remainder s
  let c = prev s
  throwError $
    "Parse error:"
    ++ "\n" ++ show (row $ position s) ++ " | ... " ++ c : takeWhile ((/=) '\n') rem
    ++ "\n" ++ take 8 (repeat ' ') ++ "^"

parseConstraint :: Ident → String → Either String SurfaceC
parseConstraint mod s = evalParser mod s parseConstraintAct

parsePredicate :: Ident → String → Either String SurfaceP
parsePredicate mod s = evalParser mod s parsePredicateAct

parseModule :: Ident → String → Either String (SurfaceM SurfaceP)
parseModule mod s = evalParser mod s parseModuleAct

}
