{
module ATerms.Syntax.Lexer (lexer, AToken(..)) where

import qualified Data.Text as Text

}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$Alpha = [A-Z]
$strchar = [^\"]

tokens :-

  $white+                       ;
  $Alpha [$alpha $digit \_]*    { TokSymbol . Text.pack }

  \[                            { const TokOpenSB }
  \]                            { const TokCloseSB }
  \(                            { const TokOpenB }
  \)                            { const TokCloseB }
  \"                            { const TokQuote }
  [\,]                          { const TokComma }
  $strchar*                     { TokString . Text.pack }

{

data AToken
  = TokSymbol Text.Text | TokString Text.Text
  | TokComma | TokOpenB | TokCloseB | TokOpenSB | TokCloseSB | TokQuote
  deriving Show

lexer :: String -> Either String [AToken]
lexer str = go ('\n',[],str)
  where
    go inp@(_,_bs,str) =
      case alexScan inp 0 of
        AlexEOF                -> Right []
        AlexError _            -> Left "lexical error"
        AlexSkip  inp' len     -> go inp'
        AlexToken inp' len act -> ((act (take len str)):) <$> go inp'

}
