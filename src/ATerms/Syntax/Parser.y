{
module ATerms.Syntax.Parser where

import Data.List
import qualified Data.Text as Text
import Data.Char
import Data.Default

import Control.Monad.Except

import ATerms.Syntax.ATerm
import ATerms.Syntax.Lexer

}

%name parse ATerm
%monad {ParserM}

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
 
%%

ATerm : symbol '(' ATerms ')' { AFunc $1 $3 }
      | '[' ATerms ']'        { AList (reverse $2) }
      | '"' str '"'           { AStr $2 }

ATerms : ATerm                { [ $1 ] }
       | ATerms ',' ATerm     { $3 : $1 }

{

type ParserM a = Except String a

runParser :: Text.Text → ParserM a → Either String a
runParser mod c = runExcept c

parseError :: [AToken] -> ParserM a
parseError toks = throwError $ "Parse error while parsing: " ++ show (take 5 toks)

}
