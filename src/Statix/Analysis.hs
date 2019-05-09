module Statix.Analysis where

import Data.HashMap.Strict as HM
import Data.Default

import Control.Monad.State
import Control.Monad.Unique
import Control.Monad.Except
import Control.Monad.ST
import Control.Lens

import Statix.Syntax

import Statix.Analysis.Symboltable
import Statix.Analysis.Types
import Statix.Analysis.Typer
import Statix.Analysis.Typer.ST
import Statix.Analysis.Namer
import Statix.Analysis.Namer.Simple

-- | Compute the signature of a module if it is consistent.
namecheck :: (MonadError TCError m) ⇒ Ident → Qualifier → [Predicate₀] → m Module
namecheck mname q defs = do
  -- collect signatures and bind them in the context,
  -- because modules are defined as a big mutual block
  mod ← execStateT (mapM_ collect defs) HM.empty
  let q' = (HM.mapWithKey (\k _ → (mname, k)) mod) `HM.union` q

  -- namecheck it
  liftEither $ runNC (set qualifier q' def) (mapM checkPredicate mod)

  where
    -- | Collect a signature from a raw Predicate.
    -- Checks against duplicate definitions.
    collect :: (MonadError TCError m) ⇒ Predicate₀ → StateT (HashMap Ident Predicate₀) m ()
    collect p = do
      let name = snd $ qname p
      bound ← gets (member name)
      if bound
        then throwError $ DuplicatePredicate name
        else modify (HM.insert name p)

typecheck ::
  ( MonadError TCError m
  , MonadUnique Integer m
  ) ⇒ Ident → Module → SymbolTable → m Module
typecheck this mod symtab = do
  i ← fresh
  (mod, i') ← liftEither $ runST $ _type i
  updateSeed i'
  return mod

  where
    _type :: Integer → ST s (Either TCError (Module, Integer))
    _type i = do
      pretype ← evalStateT (modInitialTyping mod :: StateT Integer (ST s) (PreModuleTyping (TyRef s))) 0
      let tyenv = def { _self = this , _modtable = pretype , _symty = symtab }

      runTC tyenv i $ do
        forM mod typecheckPredicate
        sig ← solution

        case annotateModule sig mod of
          Just annotated → return annotated
          Nothing        → throwError $ Panic "Module signature incomplete"

analyze ::
  ( MonadError TCError m
  , MonadUnique Integer m
  ) ⇒ SymbolTable → RawModule₀ → m Module
analyze symtab (Mod name imports defs) = do
  -- first construct the initial context from the import list
  let q = importsQualifier imports symtab

  -- namecheck the module
  mod ← namecheck name q defs

  -- typecheck the module and compute a symboltable for it
  typecheck name mod symtab 
