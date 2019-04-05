module Statix.Solver where

import Prelude hiding (lookup, null)
import Data.Map.Strict as Map hiding (map, null)
import Data.HashMap.Strict as HM
import Data.HashSet as HS
import Data.Set as Set
import Data.Either
import Data.Maybe
import Data.STRef
import Data.Functor.Fixedpoint
import Data.List as List
import Data.Default
import qualified Data.Text as Text
import qualified Data.Sequence as Seq

import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans
import Control.Monad.Equiv

import Debug.Trace

import Statix.Regex as Re
import Statix.Syntax.Constraint
import Statix.Graph
import Statix.Graph.Paths
import Statix.Graph.Types
import Statix.Analysis.Symboltable
import Statix.Analysis.Lexical
import Statix.Solver.Types
import Statix.Solver.Reify
import Statix.Solver.Monad
import Statix.Solver.Unification

panic :: String → SolverM s a
panic s = throwError (Panic s)

-- | Push a constraint to the work queue
pushGoal :: Constraint₁ → SolverM s ()
pushGoal c = do
  st  ← get
  env ← ask
  put (st { queue = queue st Seq.|> (env , c)})

-- | Pop a constraint to the work queue if it is non-empty
popGoal :: SolverM s (Maybe (Goal s))
popGoal = do
  st ← get
  case Seq.viewl (queue st) of
    Seq.EmptyL    → return Nothing
    (c Seq.:< cs) → do
      liftState $ put (st { queue = cs })
      return (Just c)

-- | Continue with the next goal
next :: SolverM s ()
next = return ()

-- | Open existential quantifier and run the continuation in the
-- resulting context
openExist :: [Param] → SolverM s a → SolverM s a
openExist ns c = do
  let ids = fmap pname ns
  bs ← mapM mkBinder ids
  enters bs c

  where
    mkBinder name = do
      v ← freshExistential name
      return (name, v)

checkCritical :: Map (SNode s) (Regex Label) → Constraint₁ → SolverM s (Set (SNode s, Label))
checkCritical ces c = cataM check c
  where
    check (CAndF l r) = return (l `Set.union` r)
    check (CExF xs c) = return c
    check (CEdgeF x l y) = do
      t₁ ← resolve x >>= getSchema
      case t₁ of
        (SNode n) → 
          case ces Map.!? n of
            Nothing  → return Set.empty
            Just re  →
              if not $ Re.empty $ match l re
              then return $ Set.singleton (n, l)
              else return Set.empty
        _ → return Set.empty
    check (CApplyF p ts) = return Set.empty -- TODO!
    check _ = return Set.empty

queryGuard :: Map (SNode s) (Regex Label) → SolverM s (Set (SNode s, Label))
queryGuard ce = do
  cs ← liftState $ gets queue
  Set.unions <$> mapM (\(e, c) → local (const e) $ checkCritical ce c) cs

-- | Embedding of syntactical terms into the DAG representation of terms
toDag :: Term₁ → SolverM s (STmRef s)
toDag (Var p)    =
  resolve p
toDag (Con c ts) = do
  id  ← freshVarName
  ts' ← mapM toDag ts
  newClass (Rep (SCon c ts') id)
toDag (Label l) = do
  id ← freshVarName
  newClass (Rep (SLabel l) id)

-- | Try to solve a focused constraint
solveFocus :: Constraint₁ → SolverM s ()

solveFocus CTrue  = return ()
solveFocus CFalse = throwError (Unsatisfiable "Derived ⊥")

solveFocus (CEq t1 t2) = do
  t1' ← toDag t1
  t2' ← toDag t2
  unify t1' t2'
  next

solveFocus (CAnd l r) = do
  pushGoal r
  solveFocus l

solveFocus (CEx ns c) = do
  openExist ns (solveFocus c)

solveFocus (CNew x) = do
  t  ← resolve x
  u  ← newNode Nothing
  t' ← freshTmClass (SNode u)
  catchError
    (unify t t')
    (\ err → throwError (Unsatisfiable "Not fresh!"))
  next

solveFocus c@(CEdge x l y) = do
  t₁ ← resolve x >>= getSchema
  t₂ ← resolve y >>= getSchema
  case (t₁ , t₂) of
    (SNode n, SNode m) → newEdge (n, l, m)
    (GVar _, _)        → pushGoal c
    (_ , GVar _)       → pushGoal c
    otherwise          → throwError TypeError

solveFocus c@(CQuery x r y) = do
  t ← resolve x >>= getSchema
  case t of
    -- If the source node is ground
    -- then we can attempt to solve the query
    (SNode n)  → do
      -- first we check the guard
      es ← findReachable n r
      stuckOn ← queryGuard es

      if List.null stuckOn then do
        -- if it passes we solve the query
        ans    ← runQuery n r
        ansRef ← freshTmClass (SAns ans)
        b      ← resolve y
        unify b ansRef
        next
      else do
        pushGoal (trace "Delaying query" c)
        next

    (GVar _)  → pushGoal c
    otherwise → throwError TypeError

solveFocus c@(COne x t) = do
  t   ← toDag t
  ans ← resolve x >>= getSchema
  case ans of
    (GVar x)        → pushGoal c
    (SAns (p : [])) → throwError $ Panic "Not implemented" -- do unify (reify p) t ; return ()
    (SAns [])       → throwError (Unsatisfiable $ show c ++ " (No paths)")
    (SAns ps)       → throwError (Unsatisfiable $ show c ++ " (More than one path: " ++ show ps ++ ")")
    t               → throwError TypeError

solveFocus (CApply p ts) = do
   mp ← getPredicate p <$> ask
   case mp of
     Just (Pred σ c) → do
       -- normalize the parameters
       ts' ← mapM toDag ts

       -- bind the parameters
       enters (List.zip (fmap pname $ params σ) ts') $ do
         -- solve the body
         solveFocus c

     Nothing → panic "Unbound predicate"

type Unifier s = HashMap Ident (STree s)

-- | A simple means to getting a unifier out of ST, convert everything to a string
unifier :: SolverM s (Unifier s)
unifier = do
  e  ← locals <$> ask
  mapM toTree (head e)

formatUnifier :: Unifier s → String
formatUnifier fr =
  let bs = fmap formatBinding (HM.toList fr)
  in intercalate "\n" bs
  where
    formatBinding (k , t) = "  " ++ Text.unpack k ++ " ↦ " ++ (show t)

-- | Construct a solver for a raw constraint
kick :: SymTab → Constraint₁ → (forall s. SolverM s (String, IntGraph Label ()))
kick sym c =
  -- convert the raw constraint to the internal representatio
  local (\_ → def { symbols = sym }) $ do
    case c of
      -- open the top level exists if it exists
      (CEx ns b) → openExist ns $ do
        pushGoal b
        loop
      c → do
        pushGoal c
        loop

  where
  -- | The solver loop just continuously checks the work queue,
  -- steals an item and focuses it down, until nothing remains.
  -- When the work is done it grounds the solution and returns it.
  loop :: SolverM s (String, IntGraph Label ())
  loop = do
    st ← get
    c  ← popGoal
    case c of
      Just (env , c) → do
        local (const env) (solveFocus c)
        loop
      Nothing → do
        -- done, gather up the solution (graph and top-level unifier)
        s ← get
        g ← liftST $ (toIntGraph (graph s))
        φ ← unifier
        return (show φ, fmap (const ()) g)

-- | Construct and run a solver for a constraint
solve :: SymTab → Constraint₁ → Solution
solve p c = runSolver (kick p c)

-- | Check satisfiability of a program
check :: SymTab → Constraint₁ → Bool
check p c = isRight $ solve p c
