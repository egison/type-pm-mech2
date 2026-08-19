import TypePM.Runtime.MatchingSearch

/-!
# Ordered composition of matching-atom reducers

Built-in atom rules are attempted before user-defined matcher-clause rules.
Only a normal `miss` falls through to the second reducer; a hit, timeout, or
stuck result is preserved.  This module fixes that composition boundary before
the concrete matcher-clause reducer is connected.
-/

namespace TypePM.Runtime

/-- The common callable shape of a matching-atom rule family. -/
abbrev AtomReducer := ValueEnvironment → MatchingAtom →
  FuelResult (DispatchResult AtomReduction)

/-- Try the first atom rule family, then the fallback only on normal miss. -/
def combineAtomReducers
    (primary fallback : AtomReducer) : AtomReducer :=
  fun environment atom =>
    FuelResult.bind (primary environment atom) fun outcome =>
      match outcome with
      | .hit reduction => .ok (.hit reduction)
      | .miss => fallback environment atom

@[simp] theorem combineAtomReducers_primary_hit
    (primary fallback : AtomReducer)
    {environment : ValueEnvironment} {atom : MatchingAtom}
    {reduction : AtomReduction}
    (hit : primary environment atom = .ok (.hit reduction)) :
    combineAtomReducers primary fallback environment atom =
      .ok (.hit reduction) := by
  simp [combineAtomReducers, hit]

@[simp] theorem combineAtomReducers_primary_miss
    (primary fallback : AtomReducer)
    {environment : ValueEnvironment} {atom : MatchingAtom}
    (miss : primary environment atom = .ok .miss) :
    combineAtomReducers primary fallback environment atom =
      fallback environment atom := by
  simp [combineAtomReducers, miss]

@[simp] theorem combineAtomReducers_primary_timeout
    (primary fallback : AtomReducer)
    {environment : ValueEnvironment} {atom : MatchingAtom}
    (timeout : primary environment atom = .timeout) :
    combineAtomReducers primary fallback environment atom = .timeout := by
  simp [combineAtomReducers, timeout]

@[simp] theorem combineAtomReducers_primary_stuck
    (primary fallback : AtomReducer)
    {environment : ValueEnvironment} {atom : MatchingAtom}
    (stuck : primary environment atom = .stuck) :
    combineAtomReducers primary fallback environment atom = .stuck := by
  simp [combineAtomReducers, stuck]

/-- If both rule families are non-stuck, their ordered composition is too. -/
theorem combineAtomReducers_notStuck
    (primary fallback : AtomReducer)
    (primarySafe : ∀ environment atom,
      (primary environment atom).NotStuck)
    (fallbackSafe : ∀ environment atom,
      (fallback environment atom).NotStuck)
    (environment : ValueEnvironment) (atom : MatchingAtom) :
    (combineAtomReducers primary fallback environment atom).NotStuck := by
  unfold combineAtomReducers
  apply FuelResult.bind_notStuck (resultSafe := primarySafe environment atom)
  intro outcome
  cases outcome with
  | hit reduction => trivial
  | miss => exact fallbackSafe environment atom

/-- A total fallback makes the combined reducer total. -/
theorem combineAtomReducers_total
    (primary fallback : AtomReducer)
    (fallbackTotal : AtomReducerTotal fallback) :
    AtomReducerTotal (combineAtomReducers primary fallback) := by
  intro environment atom combinedMiss
  cases primaryResult : primary environment atom with
  | timeout => simp [combineAtomReducers, primaryResult] at combinedMiss
  | stuck => simp [combineAtomReducers, primaryResult] at combinedMiss
  | ok outcome =>
      cases outcome with
      | hit reduction =>
          simp [combineAtomReducers, primaryResult] at combinedMiss
      | miss =>
          have fallbackMiss : fallback environment atom = .ok .miss := by
            simpa [combineAtomReducers, primaryResult] using combinedMiss
          exact fallbackTotal environment atom fallbackMiss

/-- Safe built-in and total fallback families make bounded matching search
non-stuck. -/
theorem searchMatchingFuel_combined_notStuck
    (primary fallback : AtomReducer)
    (primarySafe : ∀ environment atom,
      (primary environment atom).NotStuck)
    (fallbackSafe : ∀ environment atom,
      (fallback environment atom).NotStuck)
    (fallbackTotal : AtomReducerTotal fallback)
    (fuel : Nat) (initial : MatchingState) :
    (searchMatchingFuel (combineAtomReducers primary fallback)
      fuel initial).NotStuck :=
  searchMatchingFuel_notStuck _
    (combineAtomReducers_notStuck primary fallback primarySafe fallbackSafe)
    (combineAtomReducers_total primary fallback fallbackTotal) fuel initial

end TypePM.Runtime
