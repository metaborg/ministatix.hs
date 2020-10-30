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

import Data.Set (Set, singleton, empty)
import Data.Default
import Data.Maybe
import Data.List (transpose)
import qualified Data.HashMap.Strict as HM

import Control.Monad.Except
import Control.Monad.Reader
import Control.Lens

import Statix.Syntax
import Statix.Analysis.Lexical
import Statix.Analysis.Types hiding (PreSymbolTable, symtab, locals)

data ReqEqn a v
 = RLit a
 | RBot
 | RDiff v v
 | RV v deriving (Show)

data ProvEqn a v
 = PLit a
 | PBot
 | PCap [v] -- the meet of a nonempty list
 | PV v deriving (Show)

class Eq a ⇒ SortaLattice a where
  bot   :: a
  lmeet :: a → a → a
  ljoin :: a → a → a

reqEval :: SortaLattice a ⇒ ReqEqn a v → (v → (Bool, a)) → a
reqEval RBot env            = bot
reqEval (RLit s) env        = s
reqEval (RDiff w v) env
  | True  ← fst $ env w = bot
  | False ← fst $ env w = snd $ env v
reqEval (RV v) env          = snd $ env v

provEval :: (Show a, SortaLattice a) ⇒ ProvEqn a v → (v → a) → a
provEval PBot env        = bot
provEval (PLit s) env    = s
provEval (PCap as) env
  | b:bs ← as = foldl lmeet (env b) (fmap env bs)
  | []   ← as = bot
provEval (PV v) env      = env v

class MonadPermission m v l | m → v l where
  require :: v → ReqEqn (Set l) v → m () 
  provide :: v → ProvEqn Bool v → m ()     

type PreSymbolTable v = SymbolTable QName (Ident, Type, v) Constraint₁
data PermEnv v = PermEnv
  { _locals :: [[(Ident, v)]]
  , _pretab :: PreSymbolTable v
  , _symtab :: SymbolTable₃
  }

instance Default (PermEnv v) where
  def = PermEnv [] HM.empty HM.empty

makeLenses ''PermEnv

class
  ( MonadLex (Ident, v) IPath v m
  , MonadReader (PermEnv v) m
  , MonadError TCError m
  , MonadPermission m v l
  , FrameDesc m ~ ()
  ) ⇒ MonadPermAnalysis l v m | m → l v where

  newVar :: QName → Pos → Bool → Ident → m v

  -- | Copy the entire local environment.
  -- `f` receives the original and the copy in that order.
  -- `g` is run inside the freshened environment
  freshenEnvWith :: Pos → (v → v → m ()) → m a → m a

withSymtab :: (MonadPermAnalysis l v m) ⇒ SymbolTable₂ → m a → m a
withSymtab symtab ma = do
  preST ← forMOf (each.definitions.each) symtab $
    \(Pred pos qn sig c) → do
      sig' ← forM sig (\ (id, ty) → do
         v ← newVar qn pos False id
         return (id, ty, v))

      return (Pred pos qn sig' c)
  local (over pretab (const preST)) ma

scopeDependency :: MonadPermAnalysis l v m ⇒ v → v → m ()
scopeDependency outer inner = do
  require inner (RV outer)
  provide inner (PV outer)
  require outer (RDiff inner inner)

mkBinder :: MonadPermAnalysis l v m ⇒ QName → Pos → Bool → Ident → m (Ident, v)
mkBinder qn pos check id = do
  v ← newVar qn pos check id
  return (id, v)

getPredVars :: MonadPermAnalysis l v m ⇒ QName → m (Maybe [v])
getPredVars qn = do
 pred ← view (pretab.lookupPred qn)
 forM pred $ \ pred → do
   let fms = pred^.sig
   return (fmap (^._3) fms)
  
permAnalysis :: MonadPermAnalysis Label v m ⇒ QName → Constraint₁ → m ()

-- uninteresting base cases
permAnalysis qn (CTrue _)         = return ()
permAnalysis qn (CFalse _)        = return ()
permAnalysis qn (CEq _ t s)       = return ()
permAnalysis qn (CNotEq _ t s)    = return ()
permAnalysis qn (CData _ x t)     = return ()
permAnalysis qn (CQuery _ n r x)  = return ()
permAnalysis qn (COne _ x t)      = return ()
permAnalysis qn (CNonEmpty _ x)   = return ()
permAnalysis qn (CMin _ x p y)    = return ()
permAnalysis qn (CFilter _ x p y) = return ()

-- interesting base cases
permAnalysis qn (CEdge pos n e m)
  | Label l t ← e = do
      nv ← resolve n
      require nv (RLit (singleton l))
  | otherwise = throwError $ Panic "Permission analysis bug, please report"
permAnalysis qn (CNew _ n t)      = do
  nv ← resolve n
  provide nv (PLit True)

-- closure
permAnalysis qn (CAnd _ c d)      = do
  permAnalysis qn c
  permAnalysis qn d

permAnalysis qn (CEx pos ns c)      = do
  bs ← forM ns (mkBinder qn pos True)
  enters () bs $ permAnalysis qn c

permAnalysis qn (CEvery pos x (Branch (Matcher ns t g) c)) = do
  freshenEnvWith pos scopeDependency $ do
    bs ← forM ns (mkBinder qn pos True)
    enters () bs $ permAnalysis qn c

permAnalysis _ (CApply _ qn ts)  = do
  fms ← getPredVars qn
  case fms of
    -- apparently a symbol that is already tc'ed
    Nothing → do
      perms ← view (symtab.sigOf qn.to (fmap (^._3)))
      forM_ (zip ts perms) $ \case
        (Var x, (outs, ins)) → do
          xv ← resolve x
          require xv (RLit (if outs then empty else ins))
          provide xv (PLit outs)
        otherwise → return ()

    Just fms → 
      forM_ (zip ts fms) $ \case
        (Var x, v) → do
          xv ← resolve x
          require xv (RDiff v v)
          provide xv (PV v)
        otherwise → return ()

permAnalysis qn (CMatch pos t brs) = do
  -- we analyze the branches all separately
  -- with their own copies of the local environment.
  branchEnvs ← forM brs $ \(Branch (Matcher ns t g) c) →
    freshenEnvWith pos scopeDependency $ do
      env ← view locals

      -- create the variables of the branch
      bs ← forM ns (mkBinder qn pos True)

      -- analyze the branch
      enters () bs $ permAnalysis qn c

      -- return the surrounding environment of the branch
      return env

  -- together the branches provide a 'meet' of the individual
  -- branch permissions
  env ← view locals
  let envs = transpose branchEnvs
  forM_ (zip env envs) $ \(scope, brScopes) → do
    forM_ (zip scope (transpose brScopes)) $ \(v, vs) → do
      provide (snd v) (PCap (fmap snd vs))

predPermAnalysis :: MonadPermAnalysis Label v m ⇒ Predicate₂ → m ()
predPermAnalysis (Pred _ qn sig body) = do
  vs ← fromJust <$> getPredVars qn
  let bs = zip (fmap fst sig) vs
  enters () bs $ permAnalysis qn body
