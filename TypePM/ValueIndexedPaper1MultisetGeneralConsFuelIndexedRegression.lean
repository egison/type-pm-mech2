import TypePM.Source.M4PatternIndexedRecursiveDispatchBridge
import TypePM.ValueIndexedPaper1MultisetGeneralConsAllCallbackSafety

/-!
# Fuel-indexed Paper 1 general-cons regression

The actual P1-L05 general-cons search returns three source-ordered branches.
Each branch first binds the chosen integer with the built-in `something`
matcher, then delegates the preserved variable pattern to the same closed
multiset matcher.  This regression constructs the bounded recursive
certificates directly from the two real dispatch classifications:

* `generalCons_dispatch_allCallback` for the outer constructor pattern;
* `variable_dispatch_allFuel` for each recursive variable atom.

No unbounded recursive certificate, successful whole-search computation, or
search-fuel monotonicity theorem is used.
-/

namespace TypePM.ValueIndexedPaper1MultisetGeneralConsFuelIndexedRegression

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open Source.MatcherTyping.M4Paper1MultisetSearchSafety
open ValueIndexedPaper1MultisetGeneralConsSafety
open ValueIndexedPaper1MultisetGeneralConsAllCallbackSafety

abbrev CoreExpressionTyping : EmbeddedExpressionTyping :=
  fun context expression target => TotalCoreTyping expression target context

private theorem intList_itemsValueTyping : ∀ literals : List Int,
    ListValueTypings (literals.map Value.int) .int
  | [] => .nil
  | literal :: literals =>
      .cons (.int literal) (intList_itemsValueTyping literals)

private theorem intList_valueTyping (literals : List Int) :
    ValueTyping (Value.buildList (literals.map Value.int))
      (DataTypes.list .int) :=
  .list (intList_itemsValueTyping literals)

/-- The sole branch returned by the catch-all variable clause is bounded at
exactly the remaining search index. -/
theorem variableBranch_fuelIndexedWork
    (targetTyped : ValueTyping target targetType) : ∀ searchFuel,
    FuelIndexedRecursiveMatchingAtomsTyping expressionTyping
      (evalFuel callbackFuel) searchFuel environmentTypes bindingTypes
      [⟨.var, .something, target⟩] [targetType]
  | 0 => .zero (by simp)
  | searchPredecessor + 1 =>
      .cons (.builtin (.somethingVar targetTyped)) .nil

/-- The exact one-branch result of variable dispatch retains its source
pattern and carries only the bounded built-in work needed at this index. -/
theorem variableBranches_fuelIndexedTyping
    (targetTyped : ValueTyping target targetType) (searchFuel : Nat) :
    FuelIndexedPatternBranchesTyping expressionTyping
      (evalFuel callbackFuel) searchFuel environmentTypes bindingTypes
      [targetType] [.var] (variableBranches target) := by
  exact .cons rfl
    (variableBranch_fuelIndexedWork targetTyped searchFuel) .nil

/-- Direct fuel-indexed classification of the actual seventh-clause variable
dispatch. -/
theorem variable_dispatch_fuelIndexedTyping
    (targetTyped : ValueTyping target targetType)
    (atomEnvironment : ValueEnvironment) (searchFuel : Nat) :
    FuelIndexedPatternDispatchTyping expressionTyping
      (evalFuel callbackFuel) searchFuel environmentTypes bindingTypes
      [targetType]
      (dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses .var target) := by
  rcases variable_dispatch_allFuel callbackFuel atomEnvironment target with
    timeout | success
  · rw [timeout]
    exact .timeout
  · rw [success]
    exact .hit (variableBranches_fuelIndexedTyping targetTyped searchFuel)

/-- One positive-index recursive variable atom.  Its successful dispatch is
checked at the strictly smaller index. -/
theorem variable_fuelIndexedAtom
    (targetTyped : ValueTyping target targetType)
    (searchPredecessor : Nat) :
    FuelIndexedRecursiveMatchingAtomTyping expressionTyping
      (evalFuel callbackFuel) (searchPredecessor + 1) environmentTypes
      bindingTypes ⟨.var, closedMultisetMatcherValue, target⟩ [targetType] := by
  apply FuelIndexedRecursiveMatchingAtomTyping.user
  · intro atomEnvironment
    simp [reduceBuiltinAtom]
  · intro atomEnvironment _
    exact variable_dispatch_fuelIndexedTyping targetTyped atomEnvironment
      searchPredecessor

/-- Initial work for a recursive variable atom at every search index. -/
theorem variable_fuelIndexedWork
    (targetTyped : ValueTyping target targetType) : ∀ searchFuel,
    FuelIndexedRecursiveMatchingAtomsTyping expressionTyping
      (evalFuel callbackFuel) searchFuel environmentTypes bindingTypes
      [⟨.var, closedMultisetMatcherValue, target⟩] [targetType]
  | 0 => .zero (by simp)
  | searchPredecessor + 1 =>
      .singletonOfAtom
        (variable_fuelIndexedAtom targetTyped searchPredecessor)

/-- One concrete general-cons successor branch: the integer head is built-in
work and the residual list is delegated recursively at the predecessor
index. -/
theorem generalConsBranch_fuelIndexedWork
    (literal : Int) (rest : List Int) : ∀ searchFuel,
    FuelIndexedRecursiveMatchingAtomsTyping CoreExpressionTyping
      (evalFuel callbackFuel) searchFuel [] []
      [⟨.var, .something, .int literal⟩,
        ⟨.var, closedMultisetMatcherValue,
          Value.buildList (rest.map Value.int)⟩]
      [.int, DataTypes.list .int]
  | 0 => .zero (by simp)
  | searchPredecessor + 1 => by
      exact .cons (.builtin (.somethingVar (.int literal)))
        (variable_fuelIndexedWork
          (expressionTyping := CoreExpressionTyping)
          (callbackFuel := callbackFuel)
          (environmentTypes := []) (bindingTypes := [.int])
          (intList_valueTyping rest) searchPredecessor)

/-- The three exact P1-L05 branches are retained in executable source order,
with the source pattern list `[.var, .var]` proved separately for each one. -/
theorem multisetConsBranches_fuelIndexedTyping
    (callbackFuel searchFuel : Nat) :
    FuelIndexedPatternBranchesTyping CoreExpressionTyping
      (evalFuel callbackFuel) searchFuel [] []
      [.int, DataTypes.list .int] [.var, .var] multisetConsBranches := by
  exact .cons rfl
    (generalConsBranch_fuelIndexedWork (callbackFuel := callbackFuel)
      1 [2, 3] searchFuel)
    (.cons rfl
      (generalConsBranch_fuelIndexedWork (callbackFuel := callbackFuel)
        2 [1, 3] searchFuel)
      (.cons rfl
        (generalConsBranch_fuelIndexedWork (callbackFuel := callbackFuel)
          3 [1, 2] searchFuel)
        .nil))

/-- Direct bounded classification of the outer general-cons dispatch for
every evaluator callback and every predecessor search index. -/
theorem generalCons_dispatch_fuelIndexedTyping
    (callbackFuel searchFuel : Nat) (atomEnvironment : ValueEnvironment) :
    FuelIndexedPatternDispatchTyping CoreExpressionTyping
      (evalFuel callbackFuel) searchFuel [] []
      [.int, DataTypes.list .int]
      (dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
        multisetConsTarget) := by
  rcases generalCons_dispatch_allCallback callbackFuel atomEnvironment with
    timeout | success
  · rw [timeout]
    exact .timeout
  · rw [success]
    exact .hit
      (multisetConsBranches_fuelIndexedTyping callbackFuel searchFuel)

def multisetConsAtom : MatchingAtom :=
  ⟨multisetConsPattern, closedMultisetMatcherValue, multisetConsTarget⟩

/-- Positive-index certificate for the actual recursive constructor atom. -/
theorem generalCons_fuelIndexedAtom
    (callbackFuel searchPredecessor : Nat) :
    FuelIndexedRecursiveMatchingAtomTyping CoreExpressionTyping
      (evalFuel callbackFuel) (searchPredecessor + 1) [] []
      multisetConsAtom [.int, DataTypes.list .int] := by
  apply FuelIndexedRecursiveMatchingAtomTyping.user
  · intro atomEnvironment
    simp [multisetConsPattern, reduceBuiltinAtom]
  · intro atomEnvironment _
    exact generalCons_dispatch_fuelIndexedTyping callbackFuel
      searchPredecessor atomEnvironment

/-- Initial general-cons work at every DFS bound, constructed directly from
the fuel-indexed atom above. -/
theorem generalCons_fuelIndexedWork
    (callbackFuel : Nat) : ∀ searchFuel,
    FuelIndexedRecursiveMatchingAtomsTyping CoreExpressionTyping
      (evalFuel callbackFuel) searchFuel [] [] [multisetConsAtom]
      [.int, DataTypes.list .int]
  | 0 => .zero (by simp)
  | searchPredecessor + 1 =>
      .singleOfAtom
        (generalCons_fuelIndexedAtom callbackFuel searchPredecessor)

/-- For all callback and DFS bounds, every completed general-cons search
returns bindings of the P1-L05 result types. -/
theorem multisetCons_search_fuelIndexedTypedSafe
    (callbackFuel searchFuel : Nat) :
    TypedMatchingSearchResult [.int, DataTypes.list .int]
      (searchPatternFuel (evalFuel callbackFuel) searchFuel []
        multisetConsPattern closedMultisetMatcherValue multisetConsTarget) := by
  exact searchPatternFuel_fuelIndexedTypedSafe
    (expressionTyping := CoreExpressionTyping)
    (eval := evalFuel callbackFuel)
    (evalFuel_totalCore_embeddedSafe callbackFuel) .nil
    (by simpa [multisetConsAtom] using
      generalCons_fuelIndexedWork callbackFuel searchFuel)

/-- Arbitrary evaluator-callback and DFS bounds cannot make the actual
general-cons search get stuck. -/
theorem multisetCons_search_fuelIndexedNeverStuck
    (callbackFuel searchFuel : Nat) :
    (searchPatternFuel (evalFuel callbackFuel) searchFuel []
      multisetConsPattern closedMultisetMatcherValue
      multisetConsTarget).NotStuck := by
  rcases multisetCons_search_fuelIndexedTypedSafe callbackFuel searchFuel with
    timeout | ⟨answers, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TypePM.ValueIndexedPaper1MultisetGeneralConsFuelIndexedRegression
