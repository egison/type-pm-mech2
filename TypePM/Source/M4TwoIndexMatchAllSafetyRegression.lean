import TypePM.TwoIndexMatchAllSafety
import TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression

/-!
# Non-vacuous recursive-closure `matchAll` composition regression

This fixture evaluates the actual Paper 1 recursive List constructor from the
ordinary runtime environment, binds it with the built-in `something` matcher,
and returns that binding from the body.  Both the matching environment and
the answer relation are `FuelEnvironmentSafe`; the recursive closure is not
classified by the structural `EnvironmentTyping` / `ValueTyping` judgments
defined in this repository.

The local built-in reducer step and its immediate yield successor are supplied
explicitly.  Thus this regression exercises the generic composition theorem,
but does not claim that M4 typing already generates every initial-state and
atom-reducer certificate needed by `commonFuelSafety`.
-/

namespace TypePM.Source.M4TwoIndexMatchAllSafetyRegression

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open TypePM.Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open TypePM.StepIndexedPaper1ListSafetyRegression

def recursiveClosureType : Ty :=
  TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureType

def recursiveClosureEnvironment : ValueEnvironment := [listRecursiveClosure]

def recursiveClosureMatchAll : Source.Expr :=
  .matchAll (.var 0) .something .var (.var 0)

def recursiveClosurePrimitiveAtom : MatchingAtom :=
  ⟨.var, .something, listRecursiveClosure⟩

theorem recursiveClosureEnvironment_fuelSafe (index : Nat) :
    FuelEnvironmentSafe index recursiveClosureEnvironment
      [recursiveClosureType] := by
  simpa [recursiveClosureEnvironment, recursiveClosureType] using
    TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureEnvironment_fuelSafe
      index

theorem targetEvaluation_safe :
    FuelResultSafe 2 recursiveClosureType
      (evalFuel 2 recursiveClosureEnvironment (.var 0)) := by
  exact .inr ⟨listRecursiveClosure, rfl,
    listRecursiveClosure_concreteFuelValueSafe 2⟩

theorem matcherEvaluation_safe :
    FuelResultSafe 2 (.matcher .any recursiveClosureType)
      (evalFuel 2 recursiveClosureEnvironment .something) := by
  exact .inr ⟨.something, rfl,
    fuelValueSafe_something recursiveClosureType 2⟩

/-- The built-in variable atom returns the recursive closure as its one
immediate binding, independently of the ambient atom environment. -/
theorem recursiveClosurePrimitive_reducer_exact
    (atomEnvironment : ValueEnvironment) :
    evaluationAtomReducer (evalFuel 2) atomEnvironment
      recursiveClosurePrimitiveAtom =
        .ok (.hit ⟨[[]], [listRecursiveClosure]⟩) := by
  rfl

/-- Two DFS visits suffice: one for the primitive atom and one for the
resulting yield state.  Search answers retain logical index two. -/
theorem recursiveClosurePrimitive_initialTwoIndex :
    TwoIndexMatchingStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
      (evaluationAtomReducer (evalFuel 2)) 2 2
      ⟨[recursiveClosurePrimitiveAtom], recursiveClosureEnvironment, []⟩
      [recursiveClosureType] := by
  apply TwoIndexMatchingStateTyping.reduce
    (recursiveClosureEnvironment_fuelSafe 4)
    (FuelEnvironmentSafe.nil 4)
  let reduction : AtomReduction := ⟨[[]], [listRecursiveClosure]⟩
  apply TwoIndexAtomReducerCertificate.hit reduction
  · simpa [reduction] using
      recursiveClosurePrimitive_reducer_exact recursiveClosureEnvironment
  · intro successor member
    simp only [MatchingState.successors] at member
    rcases List.mem_map.mp member with ⟨branch, branchMember, rfl⟩
    simp only [reduction, List.mem_singleton] at branchMember
    subst branch
    simpa [MatchingState.continueWith, reduction] using
      (TwoIndexMatchingStateTyping.yield
        (recursiveClosureEnvironment_fuelSafe 3)
        (FuelEnvironmentSafe.cons
          (listRecursiveClosure_concreteFuelValueSafe 3)
          (FuelEnvironmentSafe.nil 3)))

/-- Successful target and matcher evaluations select exactly the concrete
initial state above.  No result of the complete search is recorded here. -/
theorem recursiveClosureMatchAll_initialTwoIndex :
    EvaluatedTwoIndexInitialStateTyping FuelEnvironmentSafe
      FuelEnvironmentSafe 2 2 recursiveClosureEnvironment (.var 0)
      .something .var [recursiveClosureType] := by
  intro targetValue matcherValue targetSuccess matcherSuccess
  change FuelResult.ok listRecursiveClosure = FuelResult.ok targetValue
    at targetSuccess
  cases targetSuccess
  change FuelResult.ok Value.something = FuelResult.ok matcherValue
    at matcherSuccess
  cases matcherSuccess
  simpa [recursiveClosurePrimitiveAtom] using
    recursiveClosurePrimitive_initialTwoIndex

/-- Every index-two answer can evaluate the variable body at operational
fuel two and return an index-one recursive closure. -/
theorem recursiveClosureMatchAll_bodySafe :
    EvaluatedBindingBodySafeUnder (FuelEnvironmentSafe 2) 2 1
      recursiveClosureEnvironment [recursiveClosureType] (.var 0)
      recursiveClosureType := by
  intro bindings bindingsSafe
  cases bindings with
  | nil =>
      have impossible := bindingsSafe.1
      simp at impossible
  | cons value values =>
      have valuesLength : values.length = 0 := by
        simpa using bindingsSafe.1
      have valuesEq : values = [] := by simpa using valuesLength
      subst values
      obtain ⟨foundValue, found, foundSafe⟩ :=
        bindingsSafe.2 0 recursiveClosureType (by simp)
      have valueEq : value = foundValue := by simpa using found
      subst foundValue
      exact .inr ⟨value, rfl, foundSafe.previous⟩

/-- Whole-expression safety follows by composition.  Binding answers are
retained at index two, while the final List result is requested at the
independent index one. -/
theorem recursiveClosureMatchAll_twoIndexSafe :
    FuelResultSafe 1 (TypePM.DataTypes.list recursiveClosureType)
      (evalFuel 3 recursiveClosureEnvironment recursiveClosureMatchAll) := by
  simpa [recursiveClosureMatchAll] using
    (matchAllFuel_twoIndexSafe
      IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
      IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
      targetEvaluation_safe matcherEvaluation_safe
      recursiveClosureMatchAll_initialTwoIndex
      recursiveClosureMatchAll_bodySafe)

set_option maxRecDepth 100000 in
/-- Independent execution witness: the safe evaluation really succeeds and
returns a singleton List containing the recursive closure.  This equation is
not a premise of the safety theorem above. -/
theorem recursiveClosureMatchAll_eval_exact :
    evalFuel 3 recursiveClosureEnvironment recursiveClosureMatchAll =
      .ok (Value.buildList [listRecursiveClosure]) := by
  with_unfolding_all rfl

theorem recursiveClosureMatchAll_neverStuck :
    (evalFuel 3 recursiveClosureEnvironment recursiveClosureMatchAll).NotStuck :=
  recursiveClosureMatchAll_twoIndexSafe.notStuck

/-- The positive regression genuinely lies outside the structural runtime
environment relation. -/
theorem recursiveClosureEnvironment_not_environmentTyping :
    ¬ EnvironmentTyping recursiveClosureEnvironment
      [recursiveClosureType] := by
  simpa [recursiveClosureEnvironment, recursiveClosureType] using
    TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureEnvironment_not_environmentTyping

/-- Its concrete successful binding is likewise unavailable to structural
`ValueTypings`. -/
theorem recursiveClosureBinding_not_valueTypings :
    ¬ ValueTypings [listRecursiveClosure] [recursiveClosureType] := by
  simpa [recursiveClosureType] using
    TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureBindings_not_valueTypings

end TypePM.Source.M4TwoIndexMatchAllSafetyRegression
