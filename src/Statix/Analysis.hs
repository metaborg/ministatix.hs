module Statix.Analysis where

import Data.Default
import qualified Data.Set as Set
import Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict as IM

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
import Statix.Analysis.Permissions
import Statix.Analysis.Permissions.Types

namecheck :: (MonadError TCError m) ⇒ SymbolTable₀ → m SymbolTable₁
namecheck symtab = do
  forM symtab $ \(Mod name imps defs) → do
    -- build a qualifier for the predicate names in scope;
    -- which is everything imported
    let importQ = importQualifier imps symtab
    -- and everything in the module
    let localQ = fmap _qname defs
    let q = localQ `HM.union` importQ

    -- namecheck it
    defs ← forM defs $ \pred → do
      catchError (liftEither $ runNC (set qualifier q def) (checkPredicate pred)) $
        -- localize errors
        throwError . ModuleLocal name
      

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
      -- typecheck all the modules
      forM mods $ \mod → do
        catchError (typecheckModule mod) $
          -- localize errors
          throwError . ModuleLocal (mod^.moduleName)
      solution

  updateSeed i'

  return symtab

permcheck :: (MonadError TCError m) ⇒ SymbolTable₂ → m SymbolTable₃
permcheck symtab = liftEither $ runPermalizer $ do
  withSymtab symtab $ do
    -- perform the analysis collection permission equations for all
    -- predicates in the symbol table
    forMOf_ (each.definitions.each) symtab predPermAnalysis

    -- compute the least fixedpoint
    lfp
    table  ← use _1

    -- check that every variable has sufficient permissions
    forM_ table (\entry → do
                   let (up, down) = value entry
                   if not (Set.null down || up)
                     then throwError PermissionError
                     else return ()
                )

    -- extract the result
    preTab ← view _2
    return $ over (eachFormal._3) (\v → snd $ value $ table IM.! v) preTab

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
  ) ⇒ [SurfaceM Predicate₀] → m SymbolTable₃
analyze rawmods = do
  modules   ← deduplicate rawmods
  namedmods ← namecheck modules
  symtab₂   ← typecheck namedmods
  permcheck symtab₂
