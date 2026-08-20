import TypePM.Source.M4PatternIndexedRecursiveDispatchBridge
import TypePM.Source.M4Paper1RecursiveSafetyBoundaryRegression

/-!
# Fuel-indexed recursive-dispatch bridge regression

The real closed Paper 1 multiset matcher captures recursive closures that the
old `EnvironmentTyping` judgment cannot represent.  Its nil-constructor path
is nevertheless a useful minimal check of the new boundary: actual ordered
dispatch either times out or returns `[[]]`, and the successful empty branch
is checked at the strictly smaller search index.
-/

namespace TypePM.M4PatternIndexedRecursiveDispatchBridgeRegression

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression

abbrev CoreExpressionTyping : EmbeddedExpressionTyping :=
  fun context expression target => TotalCoreTyping expression target context

def closedMultisetNilAtom : MatchingAtom :=
  ⟨.ctor PatternCtor.nil [], closedMultisetMatcherValue, Value.nilValue⟩

/-- One bounded user atom, constructed without assigning ordinary value
typing to `closedMultisetMatcherEnvironment`. -/
theorem closedMultisetNil_fuelIndexedAtom
    (callbackFuel searchPredecessor : Nat) :
    FuelIndexedRecursiveMatchingAtomTyping CoreExpressionTyping
      (evalFuel callbackFuel) (searchPredecessor + 1) [] []
      closedMultisetNilAtom [] := by
  apply FuelIndexedRecursiveMatchingAtomTyping.user
  · intro atomEnvironment
    exact Source.MatcherTyping.reduceBuiltinAtom_constructor_miss _ _ _ _
  · intro atomEnvironment atomEnvironmentTyped
    rcases nilConstructor_dispatch_exact callbackFuel atomEnvironment
        closedMultisetMatcherEnvironment with timeout | success
    · rw [timeout]
      exact .timeout
    · rw [success]
      exact .hit (.cons rfl .nil .nil)

theorem closedMultisetNil_fuelIndexedWork
    (callbackFuel searchFuel : Nat) :
    FuelIndexedRecursiveMatchingAtomsTyping CoreExpressionTyping
      (evalFuel callbackFuel) searchFuel [] [] [closedMultisetNilAtom] [] := by
  cases searchFuel with
  | zero => exact .singleZero
  | succ searchPredecessor =>
      exact .singleOfAtom
        (closedMultisetNil_fuelIndexedAtom callbackFuel searchPredecessor)

/-- For arbitrary evaluator and DFS bounds, the actual recursive closure's
nil search is typed without the old closure-environment judgment. -/
theorem closedMultisetNil_search_fuelIndexedTypedSafe
    (callbackFuel searchFuel : Nat) :
    TypedMatchingSearchResult []
      (searchPatternFuel (evalFuel callbackFuel) searchFuel []
        (.ctor PatternCtor.nil []) closedMultisetMatcherValue
        Value.nilValue) := by
  exact searchPatternFuel_fuelIndexedTypedSafe
    (expressionTyping := CoreExpressionTyping) (eval := evalFuel callbackFuel)
    (evalFuel_totalCore_embeddedSafe callbackFuel) .nil
    (closedMultisetNil_fuelIndexedWork callbackFuel searchFuel)

theorem closedMultisetNil_search_fuelIndexedNeverStuck
    (callbackFuel searchFuel : Nat) :
    (searchPatternFuel (evalFuel callbackFuel) searchFuel []
      (.ctor PatternCtor.nil []) closedMultisetMatcherValue
      Value.nilValue).NotStuck := by
  rcases closedMultisetNil_search_fuelIndexedTypedSafe callbackFuel searchFuel with
    timeout | ⟨answers, success, answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-- Static M4 acceptance, construction of the real matcher value, and the new
bounded recursive search theorem remain about the same concrete fixture. -/
theorem closedMultisetNil_staticEvaluationAndFuelIndexedSearch :
    M4.Typing Paper1FrozenSignature.signature [] closedMultisetDefinition
        M4Paper1ClosedMultisetExactRegression.closedMultisetType ∧
      evalFuel 20 [] multisetSomething = .ok closedMultisetMatcherValue ∧
      ∀ callbackFuel searchFuel,
        (searchPatternFuel (evalFuel callbackFuel) searchFuel []
          (.ctor PatternCtor.nil []) closedMultisetMatcherValue
          Value.nilValue).NotStuck := by
  exact ⟨M4Paper1ClosedMultisetExactRegression.typing,
    closedMultisetMatcher_eval_exact,
    closedMultisetNil_search_fuelIndexedNeverStuck⟩

end TypePM.M4PatternIndexedRecursiveDispatchBridgeRegression
