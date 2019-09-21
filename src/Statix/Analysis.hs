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

onMod :: SymbolTable₀ → SymbolTable₃ → (forall ℓ σ c. Module ℓ σ c → r) → Ident → r
onMod presyms postsyms f modname =
  case HM.lookup modname presyms of
    -- for predicates being namechecked
    Just q  → f q
    -- for predicates already namechecked
    Nothing → f (postsyms ! modname)

-- localize errors
withLocalError name ma = catchError ma (throwError . ModuleLocal name)

namecheck :: (MonadError TCError m) ⇒ SymbolTable₀ → SymbolTable₃ → m SymbolTable₁
namecheck presyms postsyms = do
  forM presyms $ \(Mod name imps orders defs) → do
    -- build a qualifier for the predicate names in scope;
    -- which is everything imported...
    let importQ = importQualifier imps (onMod presyms postsyms moduleQualifier) 

    -- and everything in the module...
    let localQ = fmap _qname defs
    let q = localQ `HM.union` importQ

    -- similarly build a qualifier for the order names in scope 
    let localOrderQ = mapWithKey (\k v → (name, k)) orders
    let orderQ =
          localOrderQ `HM.union`
          (importQualifier imps (onMod presyms postsyms moduleOrderQualifier))

    -- build the name context
    let nc = set orderQualifier orderQ $ set qualifier q $ def

    -- namecheck the definitions
    defs ← forM defs $ \pred → do
      withLocalError name (liftEither $ runNC nc (checkPredicate pred))

    -- namecheck the orders
    orders ← forM orders $ \ord → do
      withLocalError name (liftEither $ runNC nc (checkComp ord))

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
    defs' ← flip execStateT HM.empty $ forM_ defs $ \pred → do
      let predName = pred^.qname._2
      seen ← use $ to $ HM.member $ predName
      if seen
        then throwError $ DuplicatePredicate predName
        else modify (HM.insert predName pred)

    -- do the same for orders/regexes
    orders' ← flip execStateT HM.empty $ forM_ orders $ \(name, ord) → do
      seen ← use $ to (HM.member name)
      if seen
        then throwError $ DuplicateOrder name
        else modify (HM.insert name ord)

    return $ (name, Mod name imps orders' defs')

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
  -- First reorganize top-level definitions into hashmaps.
  -- This errors on duplicate entries
  modules   ← deduplicate rawmods

  -- resolve names and perform a simple type analysis
  namedmods ← namecheck modules syms
  symtab₂   ← typecheck namedmods syms

  -- perform the permission analysis as described in the paper
  permcheck symtab₂ syms
