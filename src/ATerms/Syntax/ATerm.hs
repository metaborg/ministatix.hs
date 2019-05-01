module ATerms.Syntax.ATerm where

import Data.Text (Text)

data ATerm = AFunc Text [ATerm]
           | AStr Text
           | AList [ATerm]
