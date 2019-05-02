module ATerms.Syntax.ATerm where

import Data.Text (Text, unpack)
import Data.List
import Data.Functor.Fixedpoint

import Unification

data ATermF r = AFuncF Text [r]
              | AStrF Text
              | AListF [r] deriving (Functor, Foldable, Traversable, Eq)

type ATerm = Fix ATermF

pattern AFunc sym ts = Fix (AFuncF sym ts)
pattern AStr  txt    = Fix (AStrF txt)
pattern AList ts     = Fix (AListF ts)

instance Unifiable ATermF where

  zipMatch (AFuncF sym ts) (AFuncF sym' ts')
    | sym == sym', length ts == length ts' = Just (AFuncF sym (zip ts ts'))
    | otherwise   = Nothing
  zipMatch (AStrF txt) (AStrF txt')
    | txt == txt' = Just (AStrF txt)
    | otherwise   = Nothing
  zipMatch (AListF ts) (AListF ts')
    | length ts == length ts' = Just (AListF (zip ts ts'))
    | otherwise = Nothing
  zipMatch _ _ = Nothing

instance (Show r) ⇒ Show (ATermF r) where

  show (AFuncF sym rs) = unpack sym ++ "(" ++ intercalate "," (fmap show rs) ++ ")"
  show (AStrF txt)     = "\"" ++ unpack txt ++ "\""
  show (AListF rs)     = "[" ++ intercalate "," (fmap show rs) ++ "]"
