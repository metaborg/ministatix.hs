{
module Statix.Syntax.Lexer (lexer, Token(..)) where

import qualified Data.Text as Text

}

%wrapper "basic"

$digit = 0-9	  -- digits
$alpha = [a-zA-Z] -- alphabetic characters

tokens :-

  $white+				;

  true					{ const TokTrue }
  false                                 { const TokFalse }
  new                                   { const TokNew }
  in                                    { const TokIn }
  as                                    { const TokAs }
  query                                 { const TokQuery }
  only                                  { const TokOne }
  every                                 { const TokEvery }

  $alpha [$alpha $digit \_ ]*		{ TokVar . Text.pack }

  ":-"                                  { const TokLeftArrow }
  "<-"                                  { const TokLeftArrow }
  "->"                                  { const TokRightArrow }
  ":"                                   { const TokColon }
  "-["                                  { const TokOpenArr }
  "]->"                                 { const TokCloseArr }

  \(                                    { const TokOpenB }
  \)                                    { const TokCloseB }
  \{                                    { const TokOpenBr }
  \}                                    { const TokCloseBr }
  \[                                    { const TokOpenSB }
  \]                                    { const TokCloseSB }
  \'                                    { const TokQuote }
  \=                                    { const TokEq }
  [`]                                   { const TokTick }
  [\*]                                  { const TokStar }
  [\+]                                  { const TokPlus }
  [\.]                                  { const TokPeriod }
  [\,]                                  { const TokComma }


{

data Token
  = TokVar Text.Text
  | TokFalse
  | TokTrue
  | TokComma
  | TokEq
  | TokOpenBr
  | TokCloseBr
  | TokOpenB
  | TokCloseB
  | TokOpenSB
  | TokCloseSB
  | TokOpenArr
  | TokCloseArr
  | TokNew
  | TokQuery
  | TokIn
  | TokAs
  | TokRegexQuote
  | TokStar
  | TokPlus
  | TokQuote
  | TokTick
  | TokOne
  | TokEvery
  | TokLeftArrow
  | TokColon
  | TokPeriod
  | TokRightArrow
  deriving Show
 

lexer :: String -> Either String [Token]
lexer str = go ('\n',[],str)
  where
    go inp@(_,_bs,str) =
      case alexScan inp 0 of
        AlexEOF                -> Right []
        AlexError _            -> Left "lexical error"
        AlexSkip  inp' len     -> go inp'
        AlexToken inp' len act -> ((act (take len str)):) <$> go inp'

}
