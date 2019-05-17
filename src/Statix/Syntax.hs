module Statix.Syntax
  ( module Statix.Syntax.Types
  , module Statix.Syntax.Typing
  , module Statix.Syntax.Terms
  , module Statix.Syntax.Constraint
  , module ATerms.Syntax.Types
  , module ATerms.Syntax.ATerm
  ) where

import ATerms.Syntax.ATerm (ATerm(..))
import ATerms.Syntax.Types (Pos(..))
import Statix.Syntax.Types
import Statix.Syntax.Typing
import Statix.Syntax.Terms
import Statix.Syntax.Constraint
