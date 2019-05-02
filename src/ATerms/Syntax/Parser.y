{
module ATerms.Syntax.Parser where

import Data.List
import Data.Char
import Data.Default

import Control.Monad.Except
import Control.Monad.State

import ATerms.Syntax.Types

import ATerms.Syntax.ATerm
import ATerms.Syntax.Lexer

}

%name parseAct ATerm
%monad {ParserM}
%lexer {lexer} {TokEOF} 

%tokentype { AToken }
%error { parseError }

%token
  symbol        { TokSymbol $$ }
  str           { TokString $$ }
  ','           { TokComma }
  '"'           { TokQuote }
  '('           { TokOpenB }
  ')'           { TokCloseB }
  '['           { TokOpenSB }
  ']'           { TokCloseSB }
  ':'           { TokColon }
 
%%

ATerm : symbol '(' ATerms ')' { AFunc $1 $3 }
      | '(' ATermList ')'     { $2 }
      | str                   { AStr $1 }

ATermList : ATerm ':' ATermList { ACons $1 $3 }
          | '[' ']'             { ANil }

ATerms :                      { [] }
       | ATerm                { [ $1 ] }
       | ATerms ',' ATerm     { $3 : $1 }

{

parseError :: AToken -> ParserM a
parseError _ = do
  s ← gets input
  let rem = remainder s
  throwError $ "Parse error on line " ++ show (line s) ++ ": " ++ take 80 rem

parse :: String → Either String ATerm
parse s = evalParser parseAct s

}
