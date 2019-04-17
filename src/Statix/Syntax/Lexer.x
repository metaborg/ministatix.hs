{
module Statix.Syntax.Lexer (lexer, Token(..)) where

import qualified Data.Text as Text

}

%wrapper "basic"

$white = [\ \t\f\v]
$nl    = [\r\n]
$digit = 0-9
$alpha = [a-zA-Z]
@name  = $alpha [$alpha $digit \_ ]*

tokens :-

  $white+                       ;
  "//".*                        ;
  $nl+                          ;

  true                          { const TokTrue }
  false                         { const TokFalse }
  new                           { const TokNew }
  in                            { const TokIn }
  as                            { const TokAs }
  where                         { const TokWhere }
  query                         { const TokQuery }
  only                          { const TokOne }
  every                         { const TokEvery }
  min                           { const TokMin }
  filter                        { const TokFilter }
  match                         { const TokMatch }
  edge                          { const TokEdge }
  end                           { const TokEnd }
  import                        { const TokImport }
  lexico                        { const TokPathLT }

  @name                         { TokName . Text.pack }

  "<"                           { const TokLAngle }
  ">"                           { const TokRAngle }
  "|"                           { const TokBar }
  ":-"                          { const TokLeftArrow }
  "<-"                          { const TokLeftArrow }
  "->"                          { const TokRightArrow }
  ":"                           { const TokColon }
  ";"                           { const TokSemicolon }
  "-["                          { const TokOpenArr }
  "]->"                         { const TokCloseArr }

  \(                            { const TokOpenB }
  \)                            { const TokCloseB }
  \{                            { const TokOpenBr }
  \}                            { const TokCloseBr }
  \[                            { const TokOpenSB }
  \]                            { const TokCloseSB }
  \'                            { const TokQuote }
  \=                            { const TokEq }
  [`]                           { const TokTick }
  [\*]                          { const TokStar }
  [\+]                          { const TokPlus }
  [\.]                          { const TokPeriod }
  [\,]                          { const TokComma }


{

data Token
  = TokName Text.Text
  | TokPath Text.Text
  | TokFalse | TokTrue | TokEq | TokNew | TokQuery | TokMatch
  | TokIn | TokAs | TokWhere
  | TokOne | TokEvery | TokMin | TokFilter | TokEdge | TokEnd | TokPathLT
  | TokRegexQuote | TokStar | TokPlus | TokTick | TokColon | TokSemicolon | TokPeriod
  | TokComma | TokOpenBr | TokCloseBr | TokOpenB | TokCloseB | TokOpenSB | TokCloseSB
  | TokOpenArr | TokCloseArr | TokQuote | TokLeftArrow | TokRightArrow | TokBar
  | TokRAngle | TokLAngle | TokImport | TokNL
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
