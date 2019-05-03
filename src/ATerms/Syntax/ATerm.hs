module ATerms.Syntax.ATerm where

import Data.Text (Text, unpack)
import Data.List
import Data.Functor.Fixedpoint

import Unification

data ATermF r = AFuncF Text [r]
              | AStrF Text
              | AConsF r r
              | ANilF
              | ATupleF [r]
              | AWildCardF deriving (Functor, Foldable, Traversable, Eq)

type ATerm = Fix ATermF

pattern AFunc sym ts = Fix (AFuncF sym ts)
pattern AStr  txt    = Fix (AStrF txt)
pattern ACons x xs   = Fix (AConsF x xs)
pattern ANil         = Fix ANilF
pattern AWildCard    = Fix AWildCardF
pattern ATuple ts    = Fix (ATupleF ts)

instance Unifiable ATermF where

  zipMatch (AFuncF sym ts) (AFuncF sym' ts')
    | sym == sym', length ts == length ts' = Just (AFuncF sym (zip ts ts'))
    | otherwise   = Nothing
  zipMatch (AStrF txt) (AStrF txt')
    | txt == txt' = Just (AStrF txt)
    | otherwise   = Nothing
  zipMatch (AConsF t ts) (AConsF t' ts') = Just (AConsF (t, t') (ts, ts'))
  zipMatch ANilF ANilF = Just ANilF
  zipMatch (ATupleF ts) (ATupleF ts')
    | length ts == length ts' = Just (ATupleF (zip ts ts'))

  zipMatch AWildCardF t = Just (fmap (\t → (t, t)) t)
  zipMatch t AWildCardF = Just (fmap (\t → (t, t)) t)

  zipMatch _ _ = Nothing

instance (Show r) ⇒ Show (ATermF r) where

  show (AFuncF sym rs) = unpack sym ++ "(" ++ intercalate "," (fmap show rs) ++ ")"
  show (AStrF txt)     = "\"" ++ unpack txt ++ "\""
  show (AConsF r rs)   = show r ++ ":" ++ show rs
  show ANilF           = "[]"
  show (ATupleF ts)    = "(" ++ intercalate "," (fmap show ts) ++ ")"
  show AWildCardF      = "_"
