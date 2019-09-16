{-
This module implements the scala ordering used for the Scala imports case-study.

It is defined well for paths of the form B*(PB*)*(I|W)?.*
and is defined as:

Bⁿ(PB*)ᵐx.* < Bᵒ(PB*)ᵖy.* iff { (m < p and x ≤ y) or (m == p and x < y)}

for < the label order (ε < I < W) and ≤ the reflexive closure of <.
-}
module Statix.Solver.Scala (scala) where

import Data.Maybe
import Data.Relation as Rel
import Statix.Syntax

-- [] < [I] < [W]
lt :: Maybe Label → Maybe Label → Bool
lt _ Nothing                         = False
lt Nothing _                         = True
lt (Just (Lab "I")) (Just (Lab "W")) = True
lt _ _                               = False

span_parents :: [Label] → (Int, [Label])
span_parents (Lab "P":ls) =
  let
    (_, ls')  = span (== Lab "B") ls
    (n, ls'') = span_parents ls'
  in (n+1, ls'')
span_parents ls = (0, ls)

scala_path :: [Label] → (Int, Maybe Label)
scala_path p = 
  let
    (bs , p1) = span (== (Lab "B")) p
    (ps , p2) = span_parents p1
    (is, _ )  = span (\l → l == Lab "I" || l == Lab "W") p2
    i         = listToMaybe is
  in (ps, i)
  
scala :: Rel [Label] [Label]
scala p q =
  let
    (ps , i) = scala_path p
    (ps', i') = scala_path q
  in
    (ps == ps' && lt i i')
    || (ps < ps' && (i == i' || lt i i'))
