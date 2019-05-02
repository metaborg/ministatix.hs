module ATerms.Syntax.Types where

import qualified Data.Text as Text
import Control.Monad.State
import Control.Monad.Except
import Control.Monad
import Data.Word
import Data.Default

import Codec.Binary.UTF8.String (encode)

data AToken
  = TokSymbol Text.Text | TokString Text.Text
  | TokComma | TokOpenB | TokCloseB | TokOpenSB | TokCloseSB | TokQuote
  | TokEOF
  deriving Show

data Token 
     = TCat
     | TEOF
     | TString String
     deriving (Eq,Show)

data AlexInput = AlexInput
  { prev      :: Char
  , bytes     :: [Word8]
  , remainder :: String
  , line      :: Int
  } deriving Show

alexGetByte :: AlexInput → Maybe (Word8, AlexInput)
alexGetByte inp = case (bytes inp) of
  (b:bs) → Just (b, inp { bytes = bs })
  []     → case (remainder inp) of
    []     → Nothing
    (c:cs) →
      let
        n      = (line inp)
        n'     = if c == '\n' then n+1 else n
        (b:_)  = encode [ c ]
      in Just (b, AlexInput { prev = c, bytes = [], remainder = cs, line = n'})

data ParseState = ParseState
  { input    :: AlexInput
  , lexState :: Int
  , stringBuf:: String
  } deriving Show

instance Default AlexInput where
  def = AlexInput { prev = '\n', bytes = [], remainder = "", line = 1}

instance Default ParseState where
  def = ParseState
    { input = def
    , lexState = 0
    , stringBuf = ""
    }

type ParserM a = StateT ParseState (Except String) a

evalParser :: ParserM a → String → Either String a
evalParser m s = runExcept $ evalStateT m (def { input = def { remainder = s }})

