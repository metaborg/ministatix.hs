module ATerms.Syntax.Types where

import Control.Monad.State
import Control.Monad.Except

import Data.Word
import Data.Default

import Codec.Binary.UTF8.String (encode)

------------------------------------------------------------------
-- | Positions in the source file

data Pos = Pos
  { row    :: Int
  , column :: Int
  } deriving (Eq)

instance Show Pos where
  show (Pos row col) = pad 4 $ show row
    where
      pad n s = replicate (n - length s) ' ' ++ s

instance Default Pos where
  def = Pos 0 0

------------------------------------------------------------------
-- | The Tokens

data AToken
  = TokSymbol String | TokString String
  | TokColon | TokComma | TokOpenB | TokCloseB | TokOpenSB | TokCloseSB | TokQuote
  | TokEOF
  deriving Show

data AlexInput = AlexInput
  { prev      :: Char
  , bytes     :: [Word8]
  , remainder :: String
  , position  :: Pos
  } deriving Show

alexGetByte :: AlexInput → Maybe (Word8, AlexInput)
alexGetByte inp = case (bytes inp) of
  (b:bs) → Just (b, inp { bytes = bs })
  []     → case (remainder inp) of
    []     → Nothing
    (c:cs) →
      let
        Pos row col = position inp
        (row', col')= if c == '\n' then (row+1, 0) else (row, col+1)
        (b:_)       = encode [ c ]
      in Just (b, AlexInput
                { prev = c
                , bytes = []
                , remainder = cs
                , position = Pos row' col'
                }
              )

data ParseState = ParseState
  { input    :: AlexInput
  , lexState :: Int
  , stringBuf:: String
  } deriving Show

instance Default AlexInput where
  def = AlexInput { prev = '\n', bytes = [], remainder = "", position = Pos 1 0 }

instance Default ParseState where
  def = ParseState
    { input = def
    , lexState = 0
    , stringBuf = ""
    }

type ParserM a = StateT ParseState (Except String) a

evalParser :: ParserM a → String → Either String a
evalParser m s = runExcept $ evalStateT m (def { input = def { remainder = s }})
