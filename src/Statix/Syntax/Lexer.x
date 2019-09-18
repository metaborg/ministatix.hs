{
module Statix.Syntax.Lexer (lexer, Token(..)) where

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

import Statix.Syntax.Types
import Statix.Syntax.Terms

import Debug.Trace

import ATerms.Syntax.Types
  ( AlexInput(..), ParseState, Pos(..)
  , alexGetByte, lexState, stringBuf, input)
}

$space       = [\ ]
$white       = [\ \t\f\v]
$nl          = [\r\n]
$digit       = 0-9
$alpha       = [a-zA-Z]
$upper       = [A-Z]
$lower       = [a-z]

@name        = $lower [$alpha $digit \_ \- ']*
@constructor = $upper [$alpha $digit \_ \- ']*
@qname       = (@name [\.])+ @name

tokens :-

  <0> $white+                       ;
  <0> $nl+                          ;
  <0> "//".*                        ;

  <0> true                          { plain TokTrue }
  <0> false                         { plain TokFalse }
  <0> new                           { plain TokNew }
  <0> in                            { plain TokIn }
  <0> as                            { plain TokAs }
  <0> where                         { plain TokWhere }
  <0> query                         { plain TokQuery }
  <0> only                          { plain TokOne }
  <0> every                         { plain TokEvery }
  <0> inhabited                     { plain TokNonEmpty }
  <0> min                           { plain TokMin }
  <0> filter                        { plain TokFilter }
  <0> match                         { plain TokMatch }
  <0> Edge                          { plain TokEdge }
  <0> End                           { plain TokEnd }
  <0> reverse\-lexico               { plain TokPathRevLex }
  <0> lexico                        { plain TokPathLex }
  <0> eps                           { plain TokEpsilon }
  <0> scala                         { plain TokScalaOrd }

  <0> import                        { beginImport }
  <imports> $space+                 ;
  <imports> @qname                  { importing }
  <imports> @name                   { importing }

  <0> order                         { plain TokOrder }

  <0> @qname                        { qname }
  <0> @name                         { name }
  <0> @constructor                  { constructor }

  <0> "~"                           { plain TokTilde }
  <0> "_"                           { plain TokUnderscore }
  <0> "-"                           { plain TokDash }
  <0> "<"                           { plain TokLAngle }
  <0> ">"                           { plain TokRAngle }
  <0> "|"                           { plain TokBar }
  <0> "&"                           { plain TokAmp }
  <0> ":-"                          { plain TokLeftArrow }
  <0> "<-"                          { plain TokLeftArrow }
  <0> "->"                          { plain TokRightArrow }
  <0> ":"                           { plain TokColon }
  <0> ";"                           { plain TokSemicolon }
  <0> "-["                          { plain TokOpenArr }
  <0> "]->"                         { plain TokCloseArr }

  <0> \(                            { plain TokOpenB }
  <0> \)                            { plain TokCloseB }
  <0> \{                            { plain TokOpenBr }
  <0> \}                            { plain TokCloseBr }
  <0> \[                            { plain TokOpenSB }
  <0> \]                            { plain TokCloseSB }
  <0> \'                            { plain TokQuote }
  <0> \=\=                          { plain TokEq }
  <0> \!\=                          { plain TokNotEq }
  <0> [`]                           { plain TokTick }
  <0> [\*]                          { plain TokStar }
  <0> [\+]                          { plain TokPlus }
  <0> [\.]                          { plain TokPeriod }
  <0> [\,]                          { plain TokComma }
  <0> [\?]                          { plain TokQuestionmark }

  <0> \"                            { beginString }
  <string> \"                       { endString }
  <string> .                        { appendString }
  <string> \\[\"]                   { escapeQuote }

{

type LexAction = Int → String → ParserM (Maybe Token)

plain :: Token → LexAction
plain tok _ _ = return (Just tok)

name :: LexAction
name _ str = return (Just (TokName str))

qname :: LexAction
qname _ str = return (Just (TokQName str))

importing :: LexAction
importing _ str = do
  modify (\st → st { lexState = 0 })
  return $ Just (TokImports str)

constructor :: LexAction
constructor _ str = return (Just (TokConstructor str))

beginImport :: LexAction
beginImport _ _ = do
  modify (\st → st { lexState = imports })
  return Nothing

beginNormal :: LexAction
beginNormal _ _ = do
  modify (\st → st { lexState = 0 })
  return Nothing

beginString :: LexAction
beginString _ _ = do
  modify (\st → st { lexState = string })
  return Nothing

escapeQuote :: LexAction
escapeQuote _ _ = do
  modify (\st → st { stringBuf = '"' : stringBuf st })
  return Nothing

appendString :: LexAction
appendString _ (c:_) = do
  modify (\st → st { stringBuf = c : stringBuf st })
  return Nothing

endString :: LexAction
endString _ _ = do
  s ← gets stringBuf
  modify (\st → st { lexState = 0, stringBuf = "" })
  return (Just (TokString (reverse s)))

readToken :: ParserM Token
readToken = do
  s ← get

  case alexScan (input s) (lexState s) of
    AlexEOF        → return TEOF
    AlexError inp' →
      throwError $ "Lexical error on line " ++ (show $ row $ position inp')
      		 ++ "(\"" ++ (take 5 (remainder inp')) ++ "\")"
    AlexSkip inp' _ → do
      put s { input = inp' }
      readToken
    AlexToken inp' n act → do
      let (AlexInput { remainder = buf }) = input s
      put s { input = inp' }
      res ← act n (take n buf)
      case res of
        Nothing → readToken
        Just t  → return t

lexer :: (Token → ParserM a) → ParserM a
lexer cont = do
  tok ← readToken
  cont tok

}
