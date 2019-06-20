-- | The permission analysis
--
-- The scope for permissions are determined by conditionals.
-- At the scope boundary we are pessimistic about permissions:
--   1) requirements are additive (assuming the branch will be taken)
--   2) provisions are subtractive (assuming the branch will not be taken)
-- With the sidenote that if a permission is required but also satisfied by a branch,
-- it is not required on the outside.

-- If we combine multiple branches we take the intersection of the provided permissions
-- and the union of the required permissions.
--
-- The solver first collects all the constraints by a single traversal over the program,
-- then it iteratively solves them using a workslist until it reaches a fixedpoint.
module Statix.Analysis.Permissions where

import Data.Set (Set, singleton)

import Control.Monad.Unique
import Control.Monad.Except
import Control.Monad.Reader
import Control.Lens

import Statix.Syntax
import Statix.Analysis.Lexical
import Statix.Analysis.Types hiding (PreSymbolTable)

-- data PermDep

-- data PrePermission v = PrePerm
--   { value :: Mode
--   , dependants :: [v]
--   }
-- type PermTable v = HashMap v (PrePermission v)

data Equation a v
 = Lit a
 | Bot
 | Diff v v
 | V v

class Eq a ⇒ SortaLattice a where
  bot  :: a
  meet :: a → a → a
  join :: a → a → a

eval :: SortaLattice a ⇒ Equation a v → (v → (Bool, a)) → a
eval Bot env            = bot
eval (Lit s) env        = s
eval (Diff w v) env
  | True  ← fst $ env w = snd $ env v
  | False ← fst $ env w = bot
eval (V v) env          = snd $ env v

-- meets :: (SortaLattice a) ⇒ [Equation a v] → (v → a) → a
-- meets eqs env = _

-- joins :: (SortaLattice a) ⇒ [Equation a v] → (v → a) → a
-- joins [] env = bot
-- joins (eq:eqs) env = foldl _ (fmap (flip eval env) eqs) bot

class MonadPermission m v l | m → v l where
  require :: v → Equation (Set l) v → m () 
  provide :: v → Equation Bool v → m ()     

type PreSymbolTable v = SymbolTable (Ident, Type, v) Constraint₁

class
  ( MonadLex (Ident, v) IPath v m
  , MonadReader (PreSymbolTable v) m
  , MonadUnique v m
  , MonadError TCError m
  , MonadPermission m v l
  , FrameDesc m ~ ()
  ) ⇒ MonadPermAnalysis l v m | m → l v where

  -- | Copy the entire local environment and add inheritance dependencies between
  -- the fresh variables and their 'old' counterparts.
  -- This implements the behavior add the boundary of a permission scope.
  freshenEnvWith :: (v → v → m ()) → m a → m a


scopeDependency :: MonadPermAnalysis l v m ⇒ v → v → m ()
scopeDependency outer inner = do
  require outer (Diff inner inner)
  provide outer (V inner)

mkBinder id = do v ← fresh; return (id, v)

getPredVars :: MonadPermAnalysis l v m ⇒ QName → m [v]
getPredVars qn = do
 fms ← view (sigOf qn)
 return (fmap (^._3) fms)
  
permAnalysis :: MonadPermAnalysis Label v m ⇒ Constraint₁ → m ()

-- uninteresting base cases
permAnalysis (CTrue _)         = return ()
permAnalysis (CFalse _)        = return ()
permAnalysis (CEq _ t s)       = return ()
permAnalysis (CNotEq _ t s)    = return ()
permAnalysis (CData _ x t)     = return ()
permAnalysis (CQuery _ n r x)  = return ()
permAnalysis (COne _ x t)      = return ()
permAnalysis (CNonEmpty _ x)   = return ()
permAnalysis (CMin _ x p y)    = return ()
permAnalysis (CFilter _ x p y) = return ()

-- interesting base cases
permAnalysis (CEdge pos n e m)
  | Label l t ← e = do
      nv ← resolve n
      require nv (Lit (singleton l))
  | otherwise = throwError $ Panic "Permission analysis bug, please report"
permAnalysis (CNew _ n t)      = do
  nv ← resolve n
  provide nv (Lit True)

-- closure
permAnalysis (CAnd _ c d)      = do
  permAnalysis c
  permAnalysis d

permAnalysis (CEx _ ns c)      = do
  bs ← forM ns mkBinder
  enters () bs $ permAnalysis c

permAnalysis (CEvery _ x (Branch m c)) = do
  freshenEnvWith scopeDependency $ do
    permAnalysis c

permAnalysis (CApply _ qn ts)  = do
  fms ← getPredVars qn
  forM_ (zip ts fms) $ \case
    (Var x, v) → do
      xv ← resolve x
      require xv (V v)
      provide xv (V v)
    otherwise → return ()

permAnalysis (CMatch _ t brs) = do
  forM_ brs $ \(Branch (Matcher ns t g) c) →
    freshenEnvWith scopeDependency $ do
      bs ← forM ns mkBinder
      enters () bs $ permAnalysis c

predPermAnalysis :: MonadPermAnalysis Label v m ⇒ Predicate₂ → m ()
predPermAnalysis (Pred _ qn sig body) = do
  vs ← getPredVars qn
  let bs = zip (fmap fst sig) vs
  enters () bs $ permAnalysis body
