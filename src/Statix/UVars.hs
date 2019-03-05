module Statix.UVars where

import Data.STRef
import Control.Unification

{- ST unification variables with identity -}
data STVar s t =
    STVar
        {-# UNPACK #-} !Int
        {-# UNPACK #-} !(STRef s (Maybe (UTerm t (STVar s t))))

instance Show (STVar s t) where
  show (STVar i _) = "UVar " ++ show i

instance Eq (STVar s t) where
  (STVar i _) == (STVar j _) = (i == j)

instance Variable (STVar s t) where
  getVarID (STVar i _) = i
