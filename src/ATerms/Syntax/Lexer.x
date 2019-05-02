{
module ATerms.Syntax.Lexer (lexer, AToken(..)) where

import Data.Text (Text, pack)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad
import Data.Word
import Debug.Trace

import ATerms.Syntax.Types

}

$digit = 0-9
$alpha = [a-zA-Z]
$Alpha = [A-Z]

tokens :-

  <0> $white+                   ;
  <0> $Alpha [$alpha $digit \_]*{ symbol }

  <0> \:                        { plain TokColon}
  <0> \[                        { plain TokOpenSB }
  <0> \]                        { plain TokCloseSB }
  <0> \(                        { plain TokOpenB }
  <0> \)                        { plain TokCloseB }
  <0> [\,]                      { plain TokComma }

  <0> \"                        { beginString }
  <string> \"			{ endString }
  <string> .                    { appendString }
  <string> \\[\"]               { escapeQuote }

{

type LexAction = Int → String → ParserM (Maybe AToken)

plain :: AToken → LexAction
plain tok _ _ = return (Just tok)

symbol :: LexAction
symbol _ str = return (Just (TokSymbol (pack str)))

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
  return (Just (TokString (pack (reverse s)))) 

readToken :: ParserM AToken
readToken = do
  s ← get

  case alexScan (input s) (lexState s) of
    AlexEOF        → return TokEOF
    AlexError inp' → throwError $ "Lexical error on line " ++ (show $ line inp')      
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

lexer :: (AToken → ParserM a) → ParserM a
lexer cont = do
  tok ← readToken
  cont tok

}
