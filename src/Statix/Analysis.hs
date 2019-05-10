module Statix.Analysis where

import Data.Default
import Data.HashMap.Strict as HM

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Unique
import Control.Monad.Except
import Control.Monad.ST
import Control.Lens

import Statix.Syntax
import Statix.Syntax.Surface

import Statix.Analysis.Types
import Statix.Analysis.Typer
import Statix.Analysis.Typer.ST
import Statix.Analysis.Namer
import Statix.Analysis.Namer.Simple

    -- collect signatures and bind them in the context,
    -- because modules are defined as a big mutual block
    -- mod ← execStateT (mapM_ collect defs) HM.empty
    -- let q' = (HM.mapWithKey (\k _ → (mname, k)) mod) `HM.union` q

  -- where
    -- | Collect a signature from a raw Predicate.
    -- Checks against duplicate definitions.
    -- collect :: (MonadError TCError m) ⇒ Predicate₀ → StateT (HashMap Ident Predicate₀) m ()
    -- collect p = do
    --   let name = p^.qname._2
    --   bound ← gets (member name)
    --   if bound
    --     then throwError $ DuplicatePredicate name
    --     else modify (HM.insert name p)


namecheck :: (MonadError TCError m) ⇒ SymbolTable₀ → m SymbolTable₁
namecheck symtab = do
  forM symtab $ \(Mod name imps defs) → do
    let q = importQualifier imps symtab

    -- namecheck it
    defs ← forM defs $ \pred → do
      liftEither $ runNC (set qualifier q def) (checkPredicate pred)

    return (Mod name imps defs)

typecheck ::
  ( MonadError TCError m
  , MonadUnique Integer m
  ) ⇒ SymbolTable₁ → m SymbolTable₂
typecheck mods = do
  i ← fresh

  (symtab, i') ← liftEither $ runST $ runTC def i $ do
    -- construct the pretying
    table ← initialTable mods

    -- run the type analysis
    local (over symtab $ const table) $ do
      forM mods typecheckModule
      solution

  updateSeed i'

  return symtab

deduplicate :: (MonadError TCError m) ⇒ [SurfaceM Predicate₀] → m SymbolTable₀
deduplicate mods = HM.fromList <$> do
  forM mods $ \(RawMod name imps defs) → do
    -- run a stateful computation over the list of definitions
    -- adding things to the hashmap if we haven't seen them yet,
    -- or throwing an error otherwise
    mod' ← flip execStateT HM.empty $ forM_ defs $ \pred → do
      let predName = pred^.qname._2
      seen ← use $ to $ HM.member $ predName
      if seen
        then throwError $ DuplicatePredicate predName
        else modify (HM.insert predName pred)
    return $ (name, Mod name imps mod')

analyze ::
  ( MonadError TCError m
  , MonadUnique Integer m
  ) ⇒ [SurfaceM Predicate₀] → m SymbolTable₂
analyze rawmods = do
  modules   ← deduplicate rawmods
  namedmods ← namecheck modules
  typecheck namedmods
