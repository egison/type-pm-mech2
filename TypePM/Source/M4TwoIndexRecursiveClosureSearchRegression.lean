import TypePM.TwoIndexMatchingSearchSafety
import TypePM.StepIndexedPaper1ListSafetyRegression
import TypePM.Source.M4Paper1RecursiveClosureTypingBoundary

/-!
# Two-index search result containing an actual recursive closure

This regression separates the DFS budget from the logical index retained on
answers.  The fixed environment and the completed answer both contain the
actual Paper 1 recursive List closure.  That value is safe in the
fuel-indexed relation but is provably unavailable to the traditional
`EnvironmentTyping` / `ValueTypings` layer.

The state is already a yield state, so this regression isolates the result
side of the generalized DFS theorem.  User-dispatch preservation remains a
separate local-reducer obligation.
-/

namespace TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression

open TypePM.Runtime
open TypePM.StepIndexedPaper1ListSafetyRegression
open TypePM.Source.MatcherTyping.M4Paper1RecursiveClosureTypingBoundary
open TypePM.Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression

def recursiveClosureType : Ty :=
  .fn concreteListDomain concreteListCodomain

def recursiveClosureYieldState : MatchingState :=
  ⟨[], [listRecursiveClosure], [listRecursiveClosure]⟩

theorem recursiveClosureEnvironment_fuelSafe (index : Nat) :
    FuelEnvironmentSafe index [listRecursiveClosure] [recursiveClosureType] := by
  exact FuelEnvironmentSafe.cons
    (listRecursiveClosure_concreteFuelValueSafe index)
    (FuelEnvironmentSafe.nil index)

/-- Search fuel one reserves index two for the state and retains index one on
the completed answer. -/
theorem recursiveClosureYield_twoIndex
    (reduceAtom : AtomReducer) :
    TwoIndexMatchingStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
      reduceAtom 1 1 recursiveClosureYieldState [recursiveClosureType] := by
  exact .yield (recursiveClosureEnvironment_fuelSafe 2)
    (recursiveClosureEnvironment_fuelSafe 2)

theorem recursiveClosureYield_exact (reduceAtom : AtomReducer) :
    depthFirstFuel (stepMatchingState reduceAtom) 1
      [recursiveClosureYieldState] =
        .ok [[listRecursiveClosure]] := by
  simp [recursiveClosureYieldState, depthFirstFuel, stepMatchingState,
    FuelResult.map]

/-- The generic DFS theorem returns a genuinely fuel-indexed answer, rather
than converting through structural `ValueTypings`. -/
theorem recursiveClosureYield_searchSafe (reduceAtom : AtomReducer) :
    MatchingSearchResultSafeWith (FuelEnvironmentSafe 1)
      [recursiveClosureType]
      (depthFirstFuel (stepMatchingState reduceAtom) 1
        [recursiveClosureYieldState]) := by
  apply depthFirstMatching_twoIndexSafe
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact recursiveClosureYield_twoIndex reduceAtom

theorem recursiveClosureYield_neverStuck (reduceAtom : AtomReducer) :
    (depthFirstFuel (stepMatchingState reduceAtom) 1
      [recursiveClosureYieldState]).NotStuck :=
  (recursiveClosureYield_searchSafe reduceAtom).notStuck

/-- The same environment cannot be certified by the traditional structural
runtime judgment. -/
theorem recursiveClosureEnvironment_not_environmentTyping :
    ¬ EnvironmentTyping [listRecursiveClosure] [recursiveClosureType] := by
  intro typed
  cases typed with
  | cons head tail =>
      exact listRecursiveClosure_not_valueTyping _ _ head

/-- Nor can the completed binding group be certified by structural
`ValueTypings`; the fuel-indexed result is not a repackaging of that proof. -/
theorem recursiveClosureBindings_not_valueTypings :
    ¬ ValueTypings [listRecursiveClosure] [recursiveClosureType] := by
  intro typed
  cases typed with
  | cons head tail =>
      exact listRecursiveClosure_not_valueTyping _ _ head

end TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression
