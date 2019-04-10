{-# LANGUAGE TupleSections #-}

module Statix.Repl.Command where

import Text.Read hiding (lift, get, lex)

import Data.Maybe
import Data.Char
import Data.Text hiding (all, span)

data Cmd
  = Define String
  | Main String
  | Import String
  | Nop
  | Help
  | Quit

instance Read Cmd where

  readsPrec _ s
    -- if it's empty, just continue
    | all isSpace s = [(Nop, "")]
    -- if starts with a colon, then we parse a command
    | (':':xs) ← s =
        maybeToList $ (,"")
        <$> uncurry
        readCmd (span isAlpha xs)
    -- otherwise it is just a constraint
    | otherwise    = [(Main s, "")]

readCmd :: String -> String -> Maybe Cmd
readCmd "def"    = Just <$> Define
readCmd "d"      = readCmd "def"
readCmd "import" = Just <$> Import . unpack . strip . pack
readCmd "i"      = readCmd "import"
readCmd "help"   = Just <$> const Help
readCmd "h"      = readCmd "help"
readCmd "quit"   = Just <$> const Quit
readCmd "q"      = readCmd "quit"
readCmd _        = const Nothing
