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
import Statix.Syntax.Lexer

}

%name parseConstraint Constraint
%name parsePredicate  Predicate
%name parseModule     Module
%monad {ParserM}

%tokentype { Token }
%error { parseError }

%token
  NAME          { TokName $$ }
  QNAME         { TokQName $$ }
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
  semicolon     { TokSemicolon }
  period        { TokPeriod }
  rightarrow    { TokRightArrow }
  match         { TokMatch }
  end           { TokEnd }
  edge          { TokEdge }
  import        { TokImport }
  lexico        { TokPathLT }
  newline       { TokNL }

%%

many0(p)        :                                       { []      }
                | p                                     { [$1]    }
                | many0(p) p                            { $2 : $1 }

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
                | new NAME                              { CNew $2 }
                | NAME rightarrow Term                  { CData $1 $3 }
                | NAME arrL NAME arrR NAME              { CEdge $1 (Lab $3) $5 }
                | query NAME Regex as NAME              { CQuery $2 $3 $5 }
                | one  '(' NAME ',' Term ')'            { COne $3 $5 }
                | every NAME Lambda                     { CEvery $2 $3 }
                | min NAME PathComp NAME                { CMin $2 $3 $4 }
                | filter NAME '(' Matcher ')' NAME      { CFilter $2 (MatchDatum $4) $6 }
                | NAME '(' Terms ')'                    { CApply $1 (reverse $3) }
                | '(' Constraint ')'                    { $2 }
                | Term match '{' Branches '}'           { CMatch $1 (reverse $4) }

RegexLit        : '`' NAME                              { RMatch (Lab $2) }
                | RegexLit RegexLit                     { RSeq $1 $2 }
                | RegexLit '*'                          { RStar $1 }
                | RegexLit '+'                          { rplus $1 }

Regex           : RegexLit                              { $1 }

Names           :                                       { [] }
                | NAME                                  { [ $1 ] }
                | Names ',' NAME                        { $3 : $1 }

Label           : NAME                                  { Lab $1 }

Term            : '`' Label                             { Label $2 }
                | edge '(' NAME ',' Term ',' Term ')'   { PathCons $3 $5 $7 }
                | end  '(' NAME ')'                     { PathEnd $3 }
                | NAME '(' Terms ')'                    { Con $1 (reverse $3) }
                | NAME                                  { Var $1 }

Terms           :                                       { []  }
                | Term                                  { [$1] }
                | Terms ',' Term                        { $3 : $1 }

Predicate       :
  NAME '(' Names ')' leftarrow Constraint period        {%
    do
      mod ← ask
      return (Pred (mod , $1) (reverse $ mkParams $3) $6)
  }

Import          : import NAME Eol                       { $2 }
                | import QNAME Eol                      { $2 }

-- TODO: newline is lexed and ignored, make it explicit?
Eol             : newline                               { $1 }
                | semicolon                             { $1 }

Module          : many0(Import) many0(Predicate)        { Mod (reverse $1) (reverse $2) }

{

mkParams = fmap (\id → (id , TBot))

type ParserM a = ReaderT Text.Text (Except String) a

runParser :: Text.Text → ParserM a → Either String a
runParser mod c = runExcept $ runReaderT c mod

parseError :: [Token] -> ParserM a
parseError toks = throwError $ "Parse error while parsing: " ++ show (take 5 toks)

varName :: Token -> Text.Text
varName (TokName s) = s
varName _ = error "Parser error: not a name"

}
