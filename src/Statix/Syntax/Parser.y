{
module Statix.Syntax.Parser (parseConstraint, parsePredicate, parseModule) where

import Data.List
import qualified Data.Text as Text
import Data.Char
import Data.Default
import Data.Functor.Sum
import Data.Functor.Fixedpoint

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State

import Statix.Regex

import Statix.Syntax.Terms
import Statix.Syntax.Constraint
import Statix.Syntax.Surface as Surf
import Statix.Syntax.Types
import Statix.Syntax.Typing
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
  '?'           { TokQuestionmark }
  '|'           { TokBar }
  '&'           { TokAmp }
  '<'           { TokLAngle }
  '_'           { TokUnderscore }
  '~'           { TokTilde }
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

%left '|'
%left '&'
%right CONCAT
%left '?'
%left '+'
%left '*'
%left '~'

%%

Eq              : Term '=' Term                         { ($1, $3) }
Eqs             :                                       { [] }
                | Eq                                    { [ $1 ] }
                | Eqs ',' Eq                            { $3 : $1 }
WhereClause     :                                       { [] }
                | where Eqs                             { $2 }

Pattern         : Label						{ PatTm $ TLabelF $1 Nothing }
                | Label '(' Pattern ')'				{ PatTm $ TLabelF $1 (Just $3) }
                | edge '(' name ',' Pattern ',' Pattern ')'	{ PatTm $ TPathConsF $3 $5 $7 }
                | end  '(' name ')'				{ PatTm $ TPathEndF $3 }
                | name						{ PatTm $ TVarF $1 }

                | constructor '(' Patterns ')'			{ funcPat $1 (reverse $3) }
                | Pattern colon Pattern				{ consPat $1 $3 }
                | '[' ']'					{ nilPat }
                | '(' Patterns ')'				{ tuplePat (reverse $2) }

                | '_'						{ Wildcard }

Patterns        :                                       { []  }
                | Pattern                               { [$1] }
                | Patterns ',' Pattern                  { $3 : $1 }

Matcher         : Pattern WhereClause                   { Surf.Matcher [] $1 $2 }

Branch          : Matcher rightarrow Constraint         { Surf.Branch $1 $3 }
Branches        : Branch                                { [ $1 ] }
                | Branches '|' Branch                   { $3 : $1 }

Lambda          : '(' Branch ')'                        { $2 }

LabelLT         : Label '<' Label                       { ($1, $3) }
LabelLTs        :                                       { [] }
                | LabelLT                               { [ $1 ] }
                | LabelLTs ',' LabelLT                  { $3 : $1 }

PathComp        : lexico '(' LabelLTs ')'               { Lex $3 }

Constraint      : '{' Names '}' Constraint              { core $ CExF (reverse $2) $4 }
                | Constraint ',' Constraint             { core $ CAndF $1 $3 }
                | Term '=' Term                         { core $ CEqF $1 $3 }
                | true                                  { core $ CTrueF }
                | false                                 { core $ CFalseF }
                | new name rightarrow Term              { core $ CNewF $2 $4 }
                | new name                              { core $ CNewF $2 unitTm }
                | name rightarrow Term                  { core $ CDataF $1 $3 }
                | name arrL Term arrR name              { core $ CEdgeF $1 $3 $5 }
                | query name Regex as name              { core $ CQueryF $2 $3 $5 }
                | one  '(' name ',' Term ')'            { core $ COneF $3 $5 }
                | min name PathComp name                { core $ CMinF $2 $3 $4 }
                | name '(' Terms ')'                    { core $ CApplyF $1 (reverse $3) }

                -- /* | every name Lambda                     { ext $ CEveryF $2 $3 } */
                -- /* | filter name '(' Matcher ')' name      { ext $ CFilterF $2 (MatchDatum $4) $6 } */
                | Term match '{' Branches '}'           { ext $ SMatchF $1 (reverse $4) }

                | '(' Constraint ')'                    { $2 }

RegexLit        : Label                                 { RMatch $1 }
                | RegexLit RegexLit %prec CONCAT        { RSeq $1 $2 }
                | RegexLit '|' RegexLit                 { RAlt $1 $3 }
                | RegexLit '&' RegexLit                 { RAnd $1 $3 }
                | RegexLit '*'                          { RStar $1 }
                | RegexLit '+'                          { rplus $1 }
                | RegexLit '?'                          { rquestion $1 }
                | '~' RegexLit                          { RNeg $2 }
                | '(' RegexLit ')'                      { $2 }

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
                | '(' Terms ')'                         { tupleTm (reverse $2) }

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
  
core = \c → Fix (InL c)
ext  = \c → Fix (InR c)

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

parseConstraint :: Ident → String → Either String SurfaceC
parseConstraint mod s = evalParser mod s parseConstraintAct

parsePredicate :: Ident → String → Either String SurfaceP
parsePredicate mod s = evalParser mod s parsePredicateAct

parseModule :: Ident → String → Either String SurfaceM
parseModule mod s = evalParser mod s parseModuleAct

}
