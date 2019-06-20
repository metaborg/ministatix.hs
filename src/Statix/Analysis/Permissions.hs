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

data ReqEqn a v
 = RLit a
 | RBot
 | RDiff v v
 | RV v deriving (Show)

data ProvEqn a v
 = PLit a
 | PBot
 | PV v deriving (Show)

class Eq a ⇒ SortaLattice a where
  bot   :: a
  lmeet :: a → a → a
  ljoin :: a → a → a

reqEval :: SortaLattice a ⇒ ReqEqn a v → (v → (Bool, a)) → a
reqEval RBot env            = bot
reqEval (RLit s) env        = s
reqEval (RDiff w v) env
  | True  ← fst $ env w = snd $ env v
  | False ← fst $ env w = bot
reqEval (RV v) env          = snd $ env v

provEval :: SortaLattice a ⇒ ProvEqn a v → (v → a) → a
provEval PBot env     = bot
provEval (PLit s) env = s
provEval (PV v) env   = env v

class MonadPermission m v l | m → v l where
  require :: v → ReqEqn (Set l) v → m () 
  provide :: v → ProvEqn Bool v → m ()     

type PreSymbolTable v = SymbolTable (Ident, Type, v) Constraint₁

class
  ( MonadLex (Ident, v) IPath v m
  , MonadReader ([[(Ident, v)]], PreSymbolTable v) m
  , MonadError TCError m
  , MonadUnique v m
  , MonadPermission m v l
  , FrameDesc m ~ ()
  ) ⇒ MonadPermAnalysis l v m | m → l v where

  -- | Copy the entire local environment.
  -- Running `f` original and copy.
  freshenEnvWith :: (v → v → m ()) → m a → m a

withSymtab :: (MonadPermAnalysis l v m) ⇒ SymbolTable₂ → m a → m a
withSymtab symtab ma = do
  preST ← forMOf eachFormal symtab (\(id, ty) → do v ← fresh; return (id, ty, v))
  local (\(env,_) → (env, preST)) ma

scopeDependency :: MonadPermAnalysis l v m ⇒ v → v → m ()
scopeDependency outer inner = do
  require outer (RDiff inner inner)

mkBinder :: MonadPermAnalysis l v m ⇒ Ident → m (Ident, v)
mkBinder id = do
  v ← fresh
  return (id, v)

getPredVars :: MonadPermAnalysis l v m ⇒ QName → m [v]
getPredVars qn = do
 fms ← view (_2.sigOf qn)
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
      require nv (RLit (singleton l))
  | otherwise = throwError $ Panic "Permission analysis bug, please report"
permAnalysis (CNew _ n t)      = do
  nv ← resolve n
  provide nv (PLit True)

-- closure
permAnalysis (CAnd _ c d)      = do
  permAnalysis c
  permAnalysis d

permAnalysis (CEx _ ns c)      = do
  bs ← forM ns mkBinder
  enters () bs $ permAnalysis c

permAnalysis (CEvery _ x (Branch (Matcher ns t g) c)) = do
  freshenEnvWith scopeDependency $ do
    bs ← forM ns mkBinder
    enters () bs $ permAnalysis c

permAnalysis (CApply _ qn ts)  = do
  fms ← getPredVars qn
  forM_ (zip ts fms) $ \case
    (Var x, v) → do
      xv ← resolve x
      require xv (RV v)
      provide xv (PV v)
    otherwise → return ()

permAnalysis (CMatch _ t brs) = do
  forM_ brs $ \(Branch (Matcher ns t g) c) →
    freshenEnvWith scopeDependency $ do
      bs ← forM ns mkBinder
      enters () bs $ permAnalysis c

  -- TODO we can take the intersection of all provided permissions for the branches
  -- to contribute permission to the outer variables

predPermAnalysis :: MonadPermAnalysis Label v m ⇒ Predicate₂ → m ()
predPermAnalysis (Pred _ qn sig body) = do
  vs ← getPredVars qn
  let bs = zip (fmap fst sig) vs
  enters () bs $ permAnalysis body
