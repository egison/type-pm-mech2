import TypePM.Source.M4TwoIndexPatternDispatchProducer

/-!
# Canonical two-index evidence for M4 built-in atoms

This module replaces fixture-specific atom relations for the built-in matcher
fragment.  The relation retains an M4-derived `PatternBinds` derivation, the
concrete built-in matcher shape, and step-indexed safety of the actual target.
Its reducer theorem is local: it classifies one reducer call as timeout or a
typed hit and does not mention a completed search or a fixed fuel value.
-/

namespace TypePM.Runtime

open TypePM.Source
open TypePM.Source.MatcherTyping

/-- The embedded evaluator contract needed by one built-in atom step. -/
def TwoIndexEmbeddedEvaluatorSafe
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value) : Prop :=
  ∀ {searchFuel residual environmentTypes bindingTypes environment bindings
      expression target},
    FuelEnvironmentSafe (searchFuel + 1 + residual)
      (bindings ++ environment) (bindingTypes ++ environmentTypes) →
    expressionTyping (bindingTypes ++ environmentTypes) expression target →
    FuelResultSafe (searchFuel + residual) target
      (eval (bindings ++ environment) expression)

/-- Canonical M4 evidence for one atom owned by the built-in reducer. -/
inductive M4BuiltinTwoIndexMatchingAtomEvidence
    (expressionTyping : EmbeddedExpressionTyping) :
    TwoIndexMatchingAtomRelation where
  | intro
      (patternTyped : PatternBinds expressionTyping environmentTypes
        bindingTypes pattern targetType newBindings)
      (matcherShape : DirectPatternMatcherShape pattern matcher)
      (targetSafe : FuelValueSafe (searchFuel + residual) target targetType) :
      M4BuiltinTwoIndexMatchingAtomEvidence expressionTyping searchFuel residual
        environmentTypes bindingTypes ⟨pattern, matcher, target⟩ newBindings

/-- Canonical built-in evidence is independent of an extra available DFS
visit, apart from the cumulative target-safety index. -/
theorem m4BuiltinTwoIndexMatchingAtomEvidence_downwardClosed :
    TwoIndexMatchingAtomRelation.DownwardClosed
      (M4BuiltinTwoIndexMatchingAtomEvidence expressionTyping) := by
  intro searchFuel residual environmentTypes bindingTypes atom newBindings typed
  cases typed with
  | intro patternTyped matcherShape targetSafe =>
      exact .intro patternTyped matcherShape (targetSafe.mono (by omega))

private theorem FuelEnvironmentSafe.tail
    (safe : FuelEnvironmentSafe fuel (value :: values) (target :: targets)) :
    FuelEnvironmentSafe fuel values targets := by
  refine ⟨by simpa using safe.1, ?_⟩
  intro index tailTarget found
  simpa only [List.getElem?_cons_succ] using
    safe.2 (index + 1) tailTarget (by
      simpa only [List.getElem?_cons_succ] using found)

private theorem FuelEnvironmentSafe.head
    (safe : FuelEnvironmentSafe fuel (value :: values) (target :: targets)) :
    FuelValueSafe fuel value target := by
  obtain ⟨foundValue, found, valueSafe⟩ := safe.2 0 target (by simp)
  simp at found
  subst foundValue
  exact valueSafe

private theorem FuelValueSafe.singletonEnvironment
    (safe : FuelValueSafe fuel value target) :
    ∃ targets, FuelEnvironmentSafe fuel [value] targets ∧ targets = [target] :=
  ⟨[target], .cons safe (.nil _), rfl⟩

private theorem PositiveValueSafes.toFuelEnvironmentSafe
    (safe : PositiveValueSafes fuel (FuelValueSafe fuel) values targets) :
    FuelEnvironmentSafe (fuel + 1) values targets := by
  induction values generalizing targets with
  | nil =>
      cases safe
      exact .nil _
  | cons value values induction =>
      cases safe with
      | cons head tail => exact .cons head (induction tail)

private theorem PatternsBind.zipMatchingAtoms
    (binds : PatternsBind expressionTyping environmentTypes bindingTypes
      patterns targetTypes newBindings)
    (shapes : DirectPatternsMatcherShape patterns matchers)
    (targetsSafe : FuelEnvironmentSafe fuel targets targetTypes) :
    ∃ atoms, MatchingAtomsZip patterns matchers targets atoms := by
  induction patterns generalizing bindingTypes targetTypes newBindings matchers
      targets with
  | nil =>
      cases binds
      cases shapes
      have empty : targets = [] := by
        cases targets <;> simp_all [FuelEnvironmentSafe]
      subst targets
      exact ⟨[], .nil⟩
  | cons pattern patterns induction =>
      cases binds with
      | cons headBinds tailBinds =>
          cases shapes with
          | cons headShape tailShapes =>
              cases targets with
              | nil => simp [FuelEnvironmentSafe] at targetsSafe
              | cons target targets =>
                  obtain ⟨atoms, zipped⟩ :=
                    induction tailBinds tailShapes targetsSafe.tail
                  exact ⟨_ :: atoms, .cons zipped⟩

/-- M4 pattern-list typing, concrete built-in matcher shapes, and target
safety construct the predecessor-indexed branch relation structurally. -/
private theorem PatternsBind.toM4BuiltinTwoIndexBranchTyping
    (binds : PatternsBind expressionTyping environmentTypes bindingTypes
      patterns targetTypes newBindings)
    (zipped : MatchingAtomsZip patterns matchers targets atoms)
    (shapes : DirectPatternsMatcherShape patterns matchers)
    (targetsSafe : FuelEnvironmentSafe (searchFuel + 1 + residual)
      targets targetTypes) :
    RelationalTwoIndexMatchingBranchTyping
      (M4BuiltinTwoIndexMatchingAtomEvidence expressionTyping)
      searchFuel residual environmentTypes bindingTypes atoms newBindings := by
  induction searchFuel generalizing bindingTypes patterns targetTypes
      newBindings matchers targets atoms with
  | zero =>
      cases atoms with
      | nil =>
          cases zipped
          cases binds
          exact .nil
      | cons atom atoms => exact .zero (by simp)
  | succ searchFuel induction =>
      cases zipped with
      | nil =>
          cases binds
          exact .nil
      | cons zippedTail =>
          cases shapes with
          | cons headShape tailShapes =>
              cases binds with
              | cons headBinds tailBinds =>
                  apply RelationalTwoIndexMatchingBranchTyping.cons
                  · exact M4BuiltinTwoIndexMatchingAtomEvidence.intro
                      headBinds headShape
                      (targetsSafe.head.mono (by omega))
                  · apply induction tailBinds zippedTail tailShapes
                    exact targetsSafe.tail.mono (by omega)

/-- One canonical M4 built-in atom is preserved by the syntax-directed
reducer for arbitrary callback and logical indices. -/
theorem reduceBuiltinAtom_m4TwoIndexTypedSafe
    (evalSafe : TwoIndexEmbeddedEvaluatorSafe expressionTyping eval) :
    TwoIndexRelationalAtomReducerTypedSafe FuelEnvironmentSafe
      FuelEnvironmentSafe
      (M4BuiltinTwoIndexMatchingAtomEvidence expressionTyping)
      (reduceBuiltinAtom eval) := by
  intro searchFuel residual environmentTypes bindingTypes environment bindings
    atom newBindings environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | intro patternTyped matcherShape targetSafe =>
      have completeEnvironment := bindingsTyped.append environmentTyped
      cases patternTyped with
      | var =>
          rename_i targetType target
          cases matcherShape with
          | somethingVar =>
              have targetAtSuccessor : FuelValueSafe
                  (searchFuel + residual) target _ :=
                targetSafe.mono (by omega)
              obtain ⟨immediateTypes, immediateTyped, immediateTypesEq⟩ :=
                targetAtSuccessor.singletonEnvironment
              refine .inr ⟨_, rfl,
                .intro immediateTypes immediateTyped ?_⟩
              · intro branch member
                simp at member
                subst branch
                exact ⟨[], .nil, by simp [immediateTypesEq]⟩
          | productVar =>
              refine .inr ⟨_, rfl, .intro [] (.nil _) ?_⟩
              intro branch member
              simp at member
              subst branch
              refine ⟨_, ?_, rfl⟩
              simpa using
                (PatternsBind.cons (.var) (.nil)).toM4BuiltinTwoIndexBranchTyping
                  (.cons .nil) (.cons .somethingVar .nil)
                  (.cons targetSafe (.nil _))
      | wild =>
          rename_i targetType target
          cases matcherShape with
          | somethingWild =>
              refine .inr ⟨_, rfl, .intro [] (.nil _) ?_⟩
              intro branch member
              simp [AtomReduction.success] at member
              subst branch
              exact ⟨[], .nil, rfl⟩
          | productWild =>
              refine .inr ⟨_, rfl, .intro [] (.nil _) ?_⟩
              intro branch member
              simp at member
              subst branch
              refine ⟨[], ?_, rfl⟩
              simpa using
                (PatternsBind.cons (.wild) (.nil)).toM4BuiltinTwoIndexBranchTyping
                  (.cons .nil) (.cons .somethingWild .nil)
                  (.cons targetSafe (.nil _))
      | value expressionTyped =>
          rename_i targetType target expression
          cases matcherShape with
          | somethingValue =>
              rcases evalSafe completeEnvironment expressionTyped with
                timeout | ⟨actual, success, actualSafe⟩
              · exact .inl (by
                  simp [reduceBuiltinAtom, timeout, FuelResult.map])
              · by_cases equal : Value.structuralEq actual target = true
                · refine .inr ⟨AtomReduction.success, by
                      simp [reduceBuiltinAtom, success, equal, FuelResult.map],
                    .intro [] (.nil _) ?_⟩
                  intro branch member
                  simp [AtomReduction.success] at member
                  subst branch
                  exact ⟨[], .nil, rfl⟩
                · have unequal : Value.structuralEq actual target = false := by
                    cases check : Value.structuralEq actual target <;> simp_all
                  exact .inr ⟨AtomReduction.failure, by
                    simp [reduceBuiltinAtom, success, unequal, FuelResult.map],
                    .intro [] (.nil _) (by simp [AtomReduction.failure])⟩
          | productValue =>
              refine .inr ⟨_, rfl, .intro [] (.nil _) ?_⟩
              intro branch member
              simp at member
              subst branch
              refine ⟨[], ?_, rfl⟩
              simpa using
                (PatternsBind.cons (.value expressionTyped)
                  (.nil)).toM4BuiltinTwoIndexBranchTyping
                    (.cons .nil) (.cons .somethingValue .nil)
                    (.cons targetSafe (.nil _))
      | ctor declaration fields => cases matcherShape
      | tuple items =>
          cases matcherShape with
          | tuple itemShapes =>
              have indexEq : searchFuel + 1 + residual =
                  (searchFuel + residual) + 1 := by omega
              rw [indexEq] at targetSafe
              cases targetSafe with
              | tuple lower targetItemsSafe =>
                  obtain ⟨atoms, zipped⟩ := items.zipMatchingAtoms
                    itemShapes targetItemsSafe.toFuelEnvironmentSafe
                  refine .inr ⟨⟨[atoms], []⟩, by
                    simp [reduceBuiltinAtom, zipped.complete],
                    .intro [] (.nil _) ?_⟩
                  intro branch member
                  simp at member
                  subst branch
                  refine ⟨_, ?_, rfl⟩
                  simpa using items.toM4BuiltinTwoIndexBranchTyping
                    (searchFuel := searchFuel) (residual := residual)
                    zipped itemShapes
                    (by simpa [indexEq] using
                      targetItemsSafe.toFuelEnvironmentSafe)
      | and left right =>
          cases matcherShape with
          | and leftShape rightShape =>
              refine .inr ⟨_, rfl, .intro [] (.nil _) ?_⟩
              intro branch member
              simp at member
              subst branch
              refine ⟨_, ?_, rfl⟩
              simpa using (PatternsBind.cons left
                (PatternsBind.cons right .nil)).toM4BuiltinTwoIndexBranchTyping
                  (.cons (.cons .nil)) (.cons leftShape (.cons rightShape .nil))
                  (.cons targetSafe (.cons targetSafe (.nil _)))
      | or left right =>
          cases matcherShape with
          | or leftShape rightShape =>
              refine .inr ⟨_, rfl, .intro [] (.nil _) ?_⟩
              intro branch member
              simp at member
              rcases member with rfl | rfl
              · refine ⟨_, ?_, rfl⟩
                simpa using
                  (PatternsBind.cons left .nil).toM4BuiltinTwoIndexBranchTyping
                    (.cons .nil) (.cons leftShape .nil)
                    (.cons targetSafe (.nil _))
              · refine ⟨_, ?_, rfl⟩
                simpa using
                  (PatternsBind.cons right .nil).toM4BuiltinTwoIndexBranchTyping
                    (.cons .nil) (.cons rightShape .nil)
                    (.cons targetSafe (.nil _))

/-- The combined evaluation atom reducer inherits the canonical built-in
local theorem because every related atom is a primary built-in hit or timeout. -/
theorem evaluationAtomReducer_m4BuiltinTwoIndexTypedSafe
    (evalSafe : TwoIndexEmbeddedEvaluatorSafe expressionTyping eval) :
    TwoIndexRelationalAtomReducerTypedSafe FuelEnvironmentSafe
      FuelEnvironmentSafe
      (M4BuiltinTwoIndexMatchingAtomEvidence expressionTyping)
      (evaluationAtomReducer eval) := by
  intro searchFuel residual environmentTypes bindingTypes environment bindings
    atom newBindings environmentTyped bindingsTyped atomTyped
  rcases reduceBuiltinAtom_m4TwoIndexTypedSafe evalSafe environmentTyped
      bindingsTyped atomTyped with timeout | ⟨reduction, success, typed⟩
  · exact .inl (by
      simp [evaluationAtomReducer, combineAtomReducers, timeout])
  · exact .inr ⟨reduction, by
      simp [evaluationAtomReducer, combineAtomReducers, success], typed⟩

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- A solved direct-fragment M4 pattern derivation produces the canonical
two-index atom relation for the actual built-in matcher and target values. -/
theorem PatternElaborates.toM4BuiltinTwoIndexMatchingAtomEvidence
    (elaboration : PatternElaborates signature context arguments pattern
      bindings supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : DirectRuntimePatternSupported pattern)
    (semantic : GeneratedPatternRuntimeSolution generated solution)
    (contextCompatible :
      MonomorphicContextCompatible context environmentTypes solution)
    (matcherShape : DirectPatternMatcherShape pattern matcherValue)
    (targetSafe : FuelValueSafe (searchFuel + residual) targetValue
      (generated.dual.target.apply solution)) :
    ∃ newBindings,
      M4BuiltinTwoIndexMatchingAtomEvidence
        (fun runtimeContext expression target =>
          RuntimeTyping expression target runtimeContext)
        searchFuel residual environmentTypes (Ty.applyList solution bindings)
        ⟨pattern, matcherValue, targetValue⟩ newBindings ∧
      Ty.applyList solution generated.bindings =
        Ty.applyList solution bindings ++ newBindings := by
  obtain ⟨newBindings, patternTyped, bindingsEq⟩ :=
    PatternElaborates.toDirectRuntimePatternBinds elaboration compatible
      supported semantic contextCompatible
  exact ⟨newBindings,
    .intro patternTyped matcherShape targetSafe, bindingsEq⟩

end TypePM.Source.MatcherTyping
