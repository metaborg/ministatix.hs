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

import Statix.Analysis.Types as A
import Statix.Analysis.Typer
import Statix.Analysis.Typer.ST
import Statix.Analysis.Namer
import Statix.Analysis.Namer.Simple
import Statix.Analysis.Permissions as P
import Statix.Analysis.Permissions.Types

namecheck :: (MonadError TCError m) ⇒ SymbolTable₀ → SymbolTable₃ → m SymbolTable₁
namecheck presyms postsyms = do
  forM presyms $ \(Mod name imps orders defs) → do
    -- build a qualifier for the predicate names in scope;
    -- which is everything imported...
    let importQ = importQualifier imps (\modname →
          case HM.lookup modname presyms of
            -- for predicates being namechecked
            Just q  → moduleQualifier q
            -- for predicates already namechecked
            Nothing → moduleQualifier (postsyms ! modname))

    -- and everything in the module...
    let localQ = fmap _qname defs
    let q = localQ `HM.union` importQ

    -- namecheck it
    defs ← forM defs $ \pred → do
      catchError (liftEither $ runNC (set qualifier q def) (checkPredicate pred)) $
        -- localize errors
        throwError . ModuleLocal name

    return (Mod name imps orders defs)

typecheck ::
  ( MonadError TCError m
  , MonadUnique Integer m
  ) ⇒ SymbolTable₁ → SymbolTable₃ → m SymbolTable₂
typecheck mods syms = do
  i ← fresh

  (symtab, i') ← liftEither $ runST $ runTC def i $ do
    -- construct the pretyping
    table ← initialTable mods

    -- run the type analysis
    local (over presymtab (const table) . over A.symtab (const syms)) $ do
      -- typecheck all the modules
      forM mods $ \mod → do
        catchError (typecheckModule mod) $
          -- localize errors
          throwError . ModuleLocal (mod^.moduleName)
      solution

  updateSeed i'

  return symtab

permcheck :: (MonadError TCError m) ⇒ SymbolTable₂ → SymbolTable₃ → m SymbolTable₃
permcheck pretab syms = liftEither $ runPermalizer $ do
  withSymtab pretab $ local (over P.symtab (const syms)) $ do
    -- perform the analysis collection permission equations for all
    -- predicates in the symbol table
    forMOf_ (each.definitions.each) pretab predPermAnalysis

    -- compute the least fixedpoint
    lfp
    table  ← use _1

    -- check that every variable has sufficient permissions
    forM_ table (\entry → do
                   let (up, down) = value entry
                   if doCheck entry && not (Set.null down || up)
                     then throwError $
                       WithPredicate (predicate entry) $
                       WithPosition (pos entry) $
                       PermissionError (name entry) down
                     else return ()
                )

    -- extract the result
    presyms ← view P.pretab
    return $ over (eachFormal._3) (value . (table IM.!)) presyms

deduplicate :: (MonadError TCError m) ⇒ [SurfaceM Predicate₀] → m SymbolTable₀
deduplicate mods = HM.fromList <$> do
  forM mods $ \(RawMod name imps orders defs) → do
    -- run a stateful computation over the list of definitions
    -- adding things to the hashmap if we haven't seen them yet,
    -- or throwing an error otherwise
    mod' ← flip execStateT HM.empty $ forM_ defs $ \pred → do
      let predName = pred^.qname._2
      seen ← use $ to $ HM.member $ predName
      if seen
        then throwError $ DuplicatePredicate predName
        else modify (HM.insert predName pred)
    return $ (name, Mod name imps orders mod')

-- | During the analysis we typically have two symboltables:
-- one for symbols that are completely analyzed and whose type is immutable,
-- and one for symbols that are still being analyzed in this round.
-- At the moment the only way to find out which category a symbol is in,
-- is to try to look it up in the latter table.
-- If it is not in there, it should already been typechecked and exist in the former.
analyze ::
  ( MonadError TCError m
  , MonadUnique Integer m
  ) ⇒ [SurfaceM Predicate₀] → SymbolTable₃ → m SymbolTable₃
analyze rawmods syms = do
  modules   ← deduplicate rawmods
  namedmods ← namecheck modules syms
  symtab₂   ← typecheck namedmods syms
  permcheck symtab₂ syms
