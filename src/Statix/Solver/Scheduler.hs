module Statix.Solver.Scheduler where

import Prelude hiding (lookup, null)
import Data.Sequence as Seq

import Control.Lens
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import ATerms.Syntax.Types()
import Statix.Syntax as Syn

import Statix.Solver.Types
import Statix.Solver.Terms
import Statix.Solver.Debug

-- | Push a goal to the queue with a given generation number.
pushGoal :: SGen → Constraint₁ → SolverM s ()
pushGoal i c = do
  env ← ask
  queue %= (\q → q Seq.|> (env, c, i))

-- | Delay a constraint by pushing it back on the work queue.
-- The constraint gets tagged by the current solver generation,
-- marking the fact that we have tried solving it in this generation,
-- but could not.
delay :: Constraint₁ → SolverM s ()
delay c = do
  gen ← use generation
  tracer ("Delaying") $ pushGoal gen c

newGoal :: Constraint₁ → SolverM s ()
newGoal c = do
  pushGoal minBound c
  next -- fresh meat

-- | Pop a constraint from the work queue if it is non-empty,
-- and if the constraint was put in the queue before the current solver
-- generation.
-- 
-- If the queue contains only goals that were created in the current
-- generation of the solver, the solver has made no progress and
-- cannot make progress: the solver is stuck.
popGoal :: SolverM s (Maybe (Goal s))
popGoal = do
  q   ← use queue
  gen ← use generation

  -- If we pop a goal and we find that its generation is
  -- at or after the solver's current generation,
  -- then the solver has made no progress and we are stuck.
  -- As the generation is monotonically increasing for goals
  -- pushed to the end of the queue, we know the queue contains
  -- no more goals from an earlier generation.
  case Seq.viewl $ q of
    Seq.EmptyL           → return Nothing
    c@(_, _, lasttry) Seq.:< cs
      | lasttry >= gen → do
          throwError StuckError
      | otherwise          → do
          queue %= const cs
          return (Just c)

-- | Continue with the next goal.
-- As we are making progress, we increment
-- the solver's generation counter by one.
next :: SolverM s ()
next = do
  st <- get
  generation %= (+1)
  return ()

-- | Constraint scheduler
-- The solver loop just continuously checks the work queue,
-- steals an item and focuses it down, until nothing remains.
-- When the work is done it grounds the solution and returns it.
schedule :: (Constraint₁ → SolverM s ()) → SolverM s ()
schedule solver = do
  st ← get
  c  ← popGoal
  case c of
    Just (env, c@(Ann pos _), _) → do
      local (const env) $ do
        catchError (solver c)
          (\case
            -- reschedule stuck goals
            StuckError → do
              delay c
            Unsatisfiable tr msg → do
              c ← instantConstraint 5 c
              throwError $ Unsatisfiable (Within pos c:tr) msg
            e → throwError e
          )

      -- repeat
      schedule solver

    -- done, gather up the solution (graph and top-level unifier)
    Nothing → return ()
