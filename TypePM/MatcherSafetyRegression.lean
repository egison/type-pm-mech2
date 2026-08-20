import TypePM.MatcherSafety
import TypePM.Runtime.ClauseDispatchRegression

/-!
# Matching-safety regressions

The first examples instantiate the conditional safety theorem with the
certified integer/tuple expression core.  The final examples exercise the
Paper-1 clause boundary dynamically.  They are intentionally not presented as
typed list/multiset preservation: runtime typing for data constructors and
matcher closures is still a separate milestone.
-/

namespace TypePM.MatcherSafetyRegression

open TypePM.Source
open TypePM.Runtime

/-- Reuse the certified runtime typing for expressions embedded in value
patterns.  The context records the types of the binding prefix and ordinary
environment in the same order used by the evaluator. -/
def CoreEmbeddedTyping : EmbeddedExpressionTyping :=
  fun context expression target => RuntimeTyping expression target context

theorem coreEvaluatorSafe (fuel : Nat) :
    EmbeddedEvaluatorSafe CoreEmbeddedTyping (evalFuel fuel) := by
  intro environmentTypes environment expression target environmentTyped
    expressionTyped
  exact expressionTyped.coreSafety fuel environment environmentTyped

theorem tuple_pattern_binding_types_preserve_source_order :
    PatternBinds CoreEmbeddedTyping [] []
      (.tuple [.var, .value (.lit 1), .var])
      (.prod [.int, .int, .int]) [.int, .int] := by
  apply PatternBinds.tuple
  apply PatternsBind.cons (headBindings := [.int])
  · exact .var
  · apply PatternsBind.cons (headBindings := [])
    · exact .value (.lit 1)
    · apply PatternsBind.cons (headBindings := [.int])
      · exact .var
      · exact .nil

def tupleAtom : MatchingAtom :=
  ⟨.tuple [.var, .wild], .tuple [.something, .something],
    .tuple [.int 1, .int 2]⟩

def tupleState : MatchingState := ⟨[tupleAtom], [], []⟩

theorem tuple_atom_typed :
    MatchingAtomTyping CoreEmbeddedTyping [] [] tupleAtom [.int] := by
  apply MatchingAtomTyping.tuple
    [⟨.var, .something, .int 1⟩,
      ⟨.wild, .something, .int 2⟩]
  · exact .cons (.cons .nil)
  · exact MatchingAtomsTyping.cons _ _ [.int] []
      (.somethingVar (.int 1))
      (MatchingAtomsTyping.cons _ _ [] []
        (.somethingWild (.int 2)) .nil)

theorem tuple_state_typed :
    MatchingStateTyping CoreEmbeddedTyping tupleState [.int] := by
  exact .mk .nil .nil
    (MatchingAtomsTyping.cons tupleAtom [] [.int] [] tuple_atom_typed .nil)

theorem tuple_search_exact :
    searchMatchingFuel (reduceBuiltinAtom (evalFuel 1)) 4 tupleState =
      .ok [[.int 1]] := by
  rfl

theorem tuple_search_preserves_binding_type :
    TypedMatchingSearchResult [.int]
      (searchMatchingFuel (reduceBuiltinAtom (evalFuel 1)) 4 tupleState) :=
  searchMatchingFuel_typedSafe
    (reduceBuiltinAtom_typedSafe CoreEmbeddedTyping (evalFuel 1)
      (coreEvaluatorSafe 1)) tuple_state_typed 4

theorem tuple_search_never_stuck :
    (searchMatchingFuel (reduceBuiltinAtom (evalFuel 1)) 4 tupleState).NotStuck :=
  searchMatchingFuel_typed_notStuck
    (reduceBuiltinAtom_typedSafe CoreEmbeddedTyping (evalFuel 1)
      (coreEvaluatorSafe 1)) tuple_state_typed 4

def conjunctionAtom : MatchingAtom :=
  ⟨.and .var (.value (.lit 1)), .something, .int 1⟩

def conjunctionState : MatchingState := ⟨[conjunctionAtom], [], []⟩

theorem conjunction_atom_typed :
    MatchingAtomTyping CoreEmbeddedTyping [] [] conjunctionAtom [.int] := by
  exact .and (.somethingVar (.int 1))
    (.somethingValue (.lit 1) (.int 1))

theorem conjunction_state_typed :
    MatchingStateTyping CoreEmbeddedTyping conjunctionState [.int] := by
  exact .mk .nil .nil
    (MatchingAtomsTyping.cons conjunctionAtom [] [.int] []
      conjunction_atom_typed .nil)

theorem conjunction_search_exact :
    searchMatchingFuel (reduceBuiltinAtom (evalFuel 1)) 4 conjunctionState =
      .ok [[.int 1]] := by
  rfl

theorem conjunction_search_preserves_binding_type :
    TypedMatchingSearchResult [.int]
      (searchMatchingFuel (reduceBuiltinAtom (evalFuel 1)) 4
        conjunctionState) :=
  searchMatchingFuel_typedSafe
    (reduceBuiltinAtom_typedSafe CoreEmbeddedTyping (evalFuel 1)
      (coreEvaluatorSafe 1)) conjunction_state_typed 4

def mismatchAtom : MatchingAtom :=
  ⟨.value (.lit 1), .something, .int 2⟩

def mismatchState : MatchingState := ⟨[mismatchAtom], [], []⟩

theorem mismatch_state_typed :
    MatchingStateTyping CoreEmbeddedTyping mismatchState [] := by
  exact .mk .nil .nil
    (MatchingAtomsTyping.cons mismatchAtom [] [] []
      (.somethingValue (.lit 1) (.int 2)) .nil)

theorem typed_value_mismatch_is_empty_not_stuck :
    searchMatchingFuel (reduceBuiltinAtom (evalFuel 1)) 1 mismatchState =
      .ok [] := by
  rfl

/-! ## Paper-1 matcher-clause boundary

These state-step equalities use the concrete seven-clause fixture's evaluator
and matcher values.  They establish the dynamic boundary needed by the later
data/matcher runtime typing: source order is retained, and a selected clause
whose data arms all miss expands to zero states rather than becoming `stuck`.
-/

open TypePM.Runtime.ClauseDispatchRegression

def selectedEmptyMatcher : Value :=
  .matcherV [] [allDataArmsMissClause, laterCatchClause]
    [allDataArmsMissClause, laterCatchClause]

def selectedEmptyState : MatchingState :=
  ⟨[⟨.tuple [], selectedEmptyMatcher, list12⟩], [], []⟩

theorem paper_selected_clause_empty_is_normal_state_expansion :
    stepMatchingState
        (combineAtomReducers (reduceBuiltinAtom shapeEval)
          (reduceMatcherAtom shapeEval)) selectedEmptyState =
      .ok (.expand []) := by
  have builtinMiss :
      reduceBuiltinAtom shapeEval []
          ⟨.tuple [], selectedEmptyMatcher, list12⟩ = .ok .miss := by
    rfl
  have matcherHit :
      reduceMatcherAtom shapeEval []
          ⟨.tuple [], selectedEmptyMatcher, list12⟩ =
        .ok (.hit ⟨[], []⟩) := by
    simp only [reduceMatcherAtom, selectedEmptyMatcher]
    rw [selected_pattern_clause_does_not_fall_through_after_data_mismatch]
    rfl
  have combinedHit := combineAtomReducers_primary_miss
    (reduceBuiltinAtom shapeEval) (reduceMatcherAtom shapeEval) builtinMiss
  simp only [selectedEmptyState, stepMatchingState]
  simp only [List.nil_append]
  rw [combinedHit, matcherHit]
  rfl

def orderedMultisetState : MatchingState :=
  ⟨[⟨.tuple [], cursorMatcher, list12⟩], [], []⟩

theorem paper_multiset_state_keeps_clause_branch_order :
    stepMatchingState
        (combineAtomReducers (reduceBuiltinAtom shapeEval)
          (reduceMatcherAtom shapeEval)) orderedMultisetState =
      .ok (.expand
        [⟨[⟨.tuple [], elementMatcher, .int 1⟩], [], []⟩,
          ⟨[⟨.tuple [], elementMatcher, .int 2⟩], [], []⟩]) := by
  have hit := builtin_miss_falls_through_to_concrete_matcher_handler
  simp [stepMatchingState, orderedMultisetState, hit,
    MatchingState.successors, MatchingState.continueWith]

end TypePM.MatcherSafetyRegression
