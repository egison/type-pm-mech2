import TypePM.Runtime.FuelResult

/-!
# Ordered depth-first search

Matching explores an ordered list of states.  A state either produces one
answer or expands to an ordered list of successor states.  Successors are
prepended to the remaining worklist, so the first successor is explored to
completion before later branches.

This module is independent of the eventual matching-state representation.
It supplies the executable search loop, its relational specification, finite
completeness, and the no-`stuck` lifting theorem used by M5.
-/

namespace TypePM.Runtime

/-- The observable outcome of taking one search-state step. -/
inductive SearchStep (State : Type u) (Answer : Type v) where
  | yield (answer : Answer)
  | expand (successors : List State)
deriving Repr, DecidableEq

/-- Ordered depth-first execution with a bound on the number of visited
states.  An empty worklist succeeds even with zero fuel. -/
def depthFirstFuel
    (step : State → FuelResult (SearchStep State Answer)) :
    Nat → List State → FuelResult (List Answer)
  | _, [] => .ok []
  | 0, _ :: _ => .timeout
  | fuel + 1, state :: rest =>
      FuelResult.bind (step state) fun observation =>
        match observation with
        | .yield answer =>
            FuelResult.map (answer :: ·) (depthFirstFuel step fuel rest)
        | .expand successors =>
            depthFirstFuel step fuel (successors ++ rest)

/-- Relational specification of complete ordered depth-first search. -/
inductive DepthFirst
    (step : State → FuelResult (SearchStep State Answer)) :
    List State → List Answer → Prop where
  | nil : DepthFirst step [] []
  | yield
      (head : step state = .ok (.yield answer))
      (tail : DepthFirst step rest answers) :
      DepthFirst step (state :: rest) (answer :: answers)
  | expand
      (head : step state = .ok (.expand successors))
      (next : DepthFirst step (successors ++ rest) answers) :
      DepthFirst step (state :: rest) answers

@[simp] theorem depthFirstFuel_nil
    (step : State → FuelResult (SearchStep State Answer)) (fuel : Nat) :
    depthFirstFuel step fuel [] = .ok [] := by
  cases fuel <;> rfl

@[simp] theorem depthFirstFuel_zero_cons
    (step : State → FuelResult (SearchStep State Answer))
    (state : State) (rest : List State) :
    depthFirstFuel step 0 (state :: rest) = .timeout := by
  rfl

/-- Every executable successful search has an independent relational
derivation with exactly the same answer order. -/
theorem depthFirstFuel_sound
    (step : State → FuelResult (SearchStep State Answer))
    {fuel : Nat} {states : List State} {answers : List Answer}
    (success : depthFirstFuel step fuel states = .ok answers) :
    DepthFirst step states answers := by
  induction fuel generalizing states answers with
  | zero =>
      cases states with
      | nil =>
          simp only [depthFirstFuel] at success
          cases success
          exact .nil
      | cons state rest =>
          simp [depthFirstFuel] at success
  | succ fuel ih =>
      cases states with
      | nil =>
          simp only [depthFirstFuel] at success
          cases success
          exact .nil
      | cons state rest =>
          simp only [depthFirstFuel] at success
          rw [FuelResult.bind_eq_ok_iff] at success
          rcases success with ⟨observation, head, continued⟩
          cases observation with
          | yield answer =>
              rw [FuelResult.map_eq_ok_iff] at continued
              rcases continued with ⟨tailAnswers, tailResult, outputEq⟩
              subst answers
              exact .yield head (ih tailResult)
          | expand successors =>
              exact .expand head (ih continued)

/-- Every finite relational search succeeds with some finite fuel. -/
theorem DepthFirst.complete
    {step : State → FuelResult (SearchStep State Answer)}
    {states : List State} {answers : List Answer}
    (search : DepthFirst step states answers) :
    ∃ fuel, depthFirstFuel step fuel states = .ok answers := by
  induction search with
  | nil =>
      exact ⟨0, rfl⟩
  | yield head tail ih =>
      rcases ih with ⟨fuel, success⟩
      refine ⟨fuel + 1, ?_⟩
      simp [depthFirstFuel, head, success]
  | expand head next ih =>
      rcases ih with ⟨fuel, success⟩
      refine ⟨fuel + 1, ?_⟩
      simp [depthFirstFuel, head, success]

/-- Adding fuel cannot change a completed search result. -/
theorem depthFirstFuel_ok_add
    (step : State → FuelResult (SearchStep State Answer))
    {fuel : Nat} {states : List State} {answers : List Answer}
    (success : depthFirstFuel step fuel states = .ok answers)
    (extra : Nat) :
    depthFirstFuel step (fuel + extra) states = .ok answers := by
  induction fuel generalizing states answers with
  | zero =>
      cases states with
      | nil =>
          simp only [depthFirstFuel] at success
          cases success
          simp
      | cons state rest =>
          simp [depthFirstFuel] at success
  | succ fuel ih =>
      cases states with
      | nil =>
          simp only [depthFirstFuel] at success
          cases success
          simp
      | cons state rest =>
          simp only [depthFirstFuel] at success
          rw [FuelResult.bind_eq_ok_iff] at success
          rcases success with ⟨observation, head, continued⟩
          cases observation with
          | yield answer =>
              rw [FuelResult.map_eq_ok_iff] at continued
              rcases continued with ⟨tailAnswers, tailResult, outputEq⟩
              subst answers
              simp only [Nat.succ_add, depthFirstFuel, head,
                FuelResult.bind_ok, FuelResult.map]
              exact congrArg (FuelResult.map (answer :: ·))
                (ih tailResult)
          | expand successors =>
              simp only [Nat.succ_add, depthFirstFuel, head,
                FuelResult.bind_ok]
              exact ih continued

/-- A pointwise non-stuck state step makes the whole bounded search
non-stuck.  Fuel exhaustion remains the separate `timeout` result. -/
theorem depthFirstFuel_notStuck
    (step : State → FuelResult (SearchStep State Answer))
    (safe : ∀ state, (step state).NotStuck)
    (fuel : Nat) (states : List State) :
    (depthFirstFuel step fuel states).NotStuck := by
  induction fuel generalizing states with
  | zero =>
      cases states <;> trivial
  | succ fuel ih =>
      cases states with
      | nil => trivial
      | cons state rest =>
          simp only [depthFirstFuel]
          apply FuelResult.bind_notStuck (resultSafe := safe state)
          intro observation
          cases observation with
          | yield answer => exact FuelResult.map_notStuck _ (ih rest)
          | expand successors => exact ih (successors ++ rest)

end TypePM.Runtime
