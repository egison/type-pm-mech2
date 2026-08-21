import TypePM.Runtime.DepthFirstSearch
import TypePM.Runtime.MatchingState

/-!
# Matching-state stepping and bounded ordered DFS

This module turns atom reductions into concrete matching-state transitions.
An atom reduction supplies an ordered list of alternative worklists.  Each
alternative is placed before the state's remaining work, while new bindings
are appended to the existing source-ordered pattern-binding group.  A completed
state yields those bindings; zero alternatives are normal match failure.

The atom reducer is a parameter so that syntax-directed rules and matcher
clause dispatch can be composed without changing the state or search rules.
An unhandled atom (`DispatchResult.miss`) is the only local coverage failure.
-/

namespace TypePM.Runtime

/-- Insert one ordered atom-reduction branch into the current state. -/
def MatchingState.continueWith
    (state : MatchingState) (remaining : List MatchingAtom)
    (reduction : AtomReduction) (branch : List MatchingAtom) :
    MatchingState :=
  { work := branch ++ remaining
    environment := state.environment
    bindings := state.bindings ++ reduction.bindings }

/-- All successor states, in the exact order supplied by the atom rule. -/
def MatchingState.successors
    (state : MatchingState) (remaining : List MatchingAtom)
    (reduction : AtomReduction) : List MatchingState :=
  reduction.branches.map (state.continueWith remaining reduction)

/-- Take one concrete matching-state step. -/
def stepMatchingState
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (state : MatchingState) :
    FuelResult (SearchStep MatchingState (List Value)) :=
  match state.work with
  | [] => .ok (.yield state.bindings)
  | atom :: remaining =>
      FuelResult.bind
        (reduceAtom (state.bindings ++ state.environment) atom) fun outcome =>
        match outcome with
        | .miss => .stuck
        | .hit reduction =>
            .ok (.expand (state.successors remaining reduction))

/-- Independent one-step relation for matching states. -/
inductive MatchingStateSteps
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)) :
    MatchingState → SearchStep MatchingState (List Value) → Prop where
  | yield :
      MatchingStateSteps reduceAtom
        ⟨[], environment, bindings⟩ (.yield bindings)
  | expand
      (reduced : reduceAtom (bindings ++ environment) atom =
        .ok (.hit reduction)) :
      MatchingStateSteps reduceAtom
        ⟨atom :: remaining, environment, bindings⟩
        (.expand
          ((reduction.branches.map fun branch =>
            ⟨branch ++ remaining, environment,
              bindings ++ reduction.bindings⟩)))

/-- Every completed executable state step has its structural derivation. -/
theorem stepMatchingState_sound
    {reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)}
    {state : MatchingState}
    {observation : SearchStep MatchingState (List Value)}
    (success : stepMatchingState reduceAtom state = .ok observation) :
    MatchingStateSteps reduceAtom state observation := by
  rcases state with ⟨work, environment, bindings⟩
  cases work with
  | nil =>
      cases success
      exact .yield
  | cons atom remaining =>
      simp only [stepMatchingState] at success
      rw [FuelResult.bind_eq_ok_iff] at success
      rcases success with ⟨outcome, reduced, continued⟩
      cases outcome with
      | miss => simp at continued
      | hit reduction =>
          cases continued
          exact .expand reduced

/-- Every structural state step executes with the same observation. -/
theorem MatchingStateSteps.complete
    {reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)}
    {state : MatchingState}
    {observation : SearchStep MatchingState (List Value)}
    (step : MatchingStateSteps reduceAtom state observation) :
    stepMatchingState reduceAtom state = .ok observation := by
  cases step with
  | yield => rfl
  | expand reduced =>
      simp [stepMatchingState, reduced, MatchingState.successors,
        MatchingState.continueWith]

theorem stepMatchingState_eq_ok_iff
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (state : MatchingState)
    (observation : SearchStep MatchingState (List Value)) :
    stepMatchingState reduceAtom state = .ok observation ↔
      MatchingStateSteps reduceAtom state observation :=
  ⟨stepMatchingState_sound, MatchingStateSteps.complete⟩

/-- Every atom is handled by the combined reducer. -/
def AtomReducerTotal
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)) : Prop :=
  ∀ environment atom, reduceAtom environment atom ≠ .ok .miss

/-- A non-stuck, total atom reducer gives a non-stuck state step. -/
theorem stepMatchingState_notStuck
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (safe : ∀ environment atom, (reduceAtom environment atom).NotStuck)
    (total : AtomReducerTotal reduceAtom)
    (state : MatchingState) :
    (stepMatchingState reduceAtom state).NotStuck := by
  rcases state with ⟨work, environment, bindings⟩
  cases work with
  | nil => trivial
  | cons atom remaining =>
      simp only [stepMatchingState]
      cases result : reduceAtom (bindings ++ environment) atom with
      | timeout => trivial
      | stuck =>
          have contradiction := safe (bindings ++ environment) atom
          simp [result, FuelResult.NotStuck] at contradiction
      | ok outcome =>
          cases outcome with
          | miss => exact (total (bindings ++ environment) atom result).elim
          | hit reduction => trivial

/-- Execute all matching alternatives by bounded ordered depth-first search.
This is the `match-all-dfs` lane.  Fair `matchAll` traverses the separate
binary reduction tree and exposes finite result prefixes instead. -/
def searchMatchingFuel
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (fuel : Nat) (initial : MatchingState) :
    FuelResult (List (List Value)) :=
  depthFirstFuel (stepMatchingState reduceAtom) fuel [initial]

/-- Successful matching search has an independent depth-first derivation. -/
theorem searchMatchingFuel_sound
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    {fuel : Nat} {initial : MatchingState}
    {answers : List (List Value)}
    (success : searchMatchingFuel reduceAtom fuel initial = .ok answers) :
    DepthFirst (stepMatchingState reduceAtom) [initial] answers :=
  depthFirstFuel_sound _ success

/-- A safe total atom reducer makes every bounded matching search non-stuck. -/
theorem searchMatchingFuel_notStuck
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (safe : ∀ environment atom, (reduceAtom environment atom).NotStuck)
    (total : AtomReducerTotal reduceAtom)
    (fuel : Nat) (initial : MatchingState) :
    (searchMatchingFuel reduceAtom fuel initial).NotStuck :=
  depthFirstFuel_notStuck _
    (stepMatchingState_notStuck reduceAtom safe total) fuel [initial]

end TypePM.Runtime
