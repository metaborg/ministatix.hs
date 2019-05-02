module ATerms.Syntax.ATerm where

import Data.Text (Text)
import Data.Functor.Fixedpoint

import Unification

data ATermF r = AFuncF Text [r]
              | AStrF Text
              | AListF [r] deriving (Functor, Foldable, Traversable, Show, Eq)

type ATerm = Fix ATermF

pattern AFunc sym ts = Fix (AFuncF sym ts)
pattern AStr  txt    = Fix (AStrF txt)
pattern AList ts     = Fix (AListF ts)

instance Unifiable ATermF where

  zipMatch (AFuncF sym ts) (AFuncF sym' ts')
    | sym == sym' = Just (AFuncF sym (zip ts ts'))
    | otherwise   = Nothing
  zipMatch (AStrF txt) (AStrF txt')
    | txt == txt' = Just (AStrF txt)
    | otherwise   = Nothing
  zipMatch (AListF ts) (AListF ts') = Just (AListF (zip ts ts'))
  zipMatch _ _ = Nothing
