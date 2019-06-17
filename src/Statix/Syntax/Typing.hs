module Statix.Syntax.Typing where
import Data.Set as Set

import Control.Applicative
import Statix.Syntax.Terms
import Unification

-- | Node permission modes:
-- `In` denotes that the node requires extension permission.
-- `Out` denotes that we have extension permission on the variable.
-- `InOut` means we both require and have extension permission.
data Mode
  = None
  | Out
  | In    (Set Label)
  | InOut (Set Label) deriving (Eq, Show)

modeJoin :: Mode → Mode → Mode
modeJoin m None             = m
modeJoin None m             = m
modeJoin (In ls) (In ks)    = In (ls `Set.union` ks)
modeJoin (In ls) Out        = In ls
modeJoin Out (In ls)        = In ls
modeJoin Out Out            = Out
modeJoin (InOut ks) (In ls) = InOut (ls `Set.union` ks)
modeJoin (In ls) (InOut ks) = InOut (ls `Set.union` ks)
modeJoin (InOut ks) Out     = InOut ks
modeJoin Out (InOut ks)     = InOut ks
modeJoin (InOut ls) (InOut ks) = InOut (ls `Set.union` ks)

data Type
  = TNode Mode
  | TPath
  | TLabel
  | TAns
  | TBot deriving (Eq)

instance Unifiable (Const Type) where

  zipMatch (Const (TNode m)) (Const (TNode n))
    = Just (Const (TNode (modeJoin m n)))
  zipMatch ty ty'
    | ty == ty'         = Just ((\r → (r,r)) <$> ty)
    | ty == Const TBot  = Just ((\r → (r,r)) <$> ty')
    | ty' == Const TBot = Just ((\r → (r,r)) <$> ty)
    | otherwise = Nothing

instance Show Type where
  show (TNode m) = "Node " ++ show m
  show TPath = "Path"
  show TAns  = "{Path}"
  show TBot  = "⊥"
  show TLabel = "Label"
