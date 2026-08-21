import TypePM.ValueIndexedMatchingSearchSafety

/-!
# Value-indexed common-fuel safety for `matchAll`

The search premise below is tied to the values actually returned by the
target and matcher expressions.  It does not quantify over unrelated values
that happen to share the same matcher type.
-/

namespace TypePM.Runtime

/-- Search safety indexed by the exact successful results of the target and
matcher evaluations at one common fuel. -/
def EvaluatedPatternSearchSafe
    (fuel : Nat) (environment : ValueEnvironment)
    (targetExpression matcherExpression : Source.Expr)
    (pattern : Source.Pattern) (bindingTypes : List Ty) : Prop :=
  ∀ targetValue matcherValue,
    evalFuel fuel environment targetExpression = .ok targetValue →
    evalFuel fuel environment matcherExpression = .ok matcherValue →
      searchPatternFuel (evalFuel fuel) fuel environment pattern
          matcherValue targetValue = .timeout ∨
        ∃ answers,
          searchPatternFuel (evalFuel fuel) fuel environment pattern
              matcherValue targetValue = .ok answers ∧
            TotalPlainMatchingAnswersTyping answers bindingTypes

/-- Search safety with a caller-selected relation for every completed binding
group.  This separates the answer relation from the evaluator callback fuel. -/
def EvaluatedPatternSearchSafeUnder
    (bindingsInvariant : MatchingBindingsInvariant)
    (fuel : Nat) (environment : ValueEnvironment)
    (targetExpression matcherExpression : Source.Expr)
    (pattern : Source.Pattern) (bindingTypes : List Ty) : Prop :=
  ∀ targetValue matcherValue,
    evalFuel fuel environment targetExpression = .ok targetValue →
    evalFuel fuel environment matcherExpression = .ok matcherValue →
      MatchingSearchResultSafeWith bindingsInvariant bindingTypes
        (searchPatternFuel (evalFuel fuel) fuel environment pattern
          matcherValue targetValue)

/-- Per-binding safety of the body selected by one successful search. -/
def EvaluatedBindingBodySafe
    (fuel : Nat) (environment : ValueEnvironment)
    (bindingTypes : List Ty) (bodyExpression : Source.Expr)
    (bodyTarget : Ty) : Prop :=
  ∀ bindings,
    TotalPlainValueTypings bindings bindingTypes →
      FuelResultSafe fuel bodyTarget
        (evalFuel fuel (bindings ++ environment) bodyExpression)

/-- Per-binding body preservation with an independently selected binding
relation and logical result index.  Evaluation fuel and logical result index
are intentionally separate arguments. -/
def EvaluatedBindingBodySafeUnder
    (bindingsInvariant : MatchingBindingsInvariant)
    (evaluationFuel resultIndex : Nat) (environment : ValueEnvironment)
    (bindingTypes : List Ty) (bodyExpression : Source.Expr)
    (bodyTarget : Ty) : Prop :=
  ∀ bindings,
    bindingsInvariant bindings bindingTypes →
      FuelResultSafe resultIndex bodyTarget
        (evalFuel evaluationFuel (bindings ++ environment) bodyExpression)

private theorem traverseEvaluatedBindingBodiesUnder
    (answersSafe : MatchingAnswersSafeWith bindingsInvariant answers bindingTypes)
    (bodySafe : EvaluatedBindingBodySafeUnder bindingsInvariant evaluationFuel
      resultIndex environment bindingTypes bodyExpression bodyTarget) :
    FuelResult.traverse
        (fun bindings =>
          evalFuel evaluationFuel (bindings ++ environment) bodyExpression)
        answers = .timeout ∨
      ∃ values,
        FuelResult.traverse
            (fun bindings =>
              evalFuel evaluationFuel (bindings ++ environment) bodyExpression)
            answers = .ok values ∧
          ∀ value ∈ values, FuelValueSafe resultIndex value bodyTarget := by
  induction answers with
  | nil => exact .inr ⟨[], rfl, by simp⟩
  | cons bindings answers induction =>
      have bindingsSafe := answersSafe bindings (by simp)
      have tailSafe : MatchingAnswersSafeWith bindingsInvariant answers
          bindingTypes := by
        intro candidate member
        exact answersSafe candidate (by simp [member])
      rcases bodySafe bindings bindingsSafe with bodyTimeout |
        ⟨value, bodySuccess, valueSafe⟩
      · exact .inl (by simp [FuelResult.traverse, bodyTimeout])
      · rcases induction tailSafe with tailTimeout |
          ⟨values, tailSuccess, valuesSafe⟩
        · exact .inl (by
            simp [FuelResult.traverse, bodySuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨value :: values, by
            simp [FuelResult.traverse, bodySuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with equality | member
            · simpa [equality] using valueSafe
            · exact valuesSafe candidate member⟩

/-- A `matchAll` rule whose search answers and body result use caller-selected
fuel-indexed relations.  The outer evaluator still uses one common callback
and search fuel, but its successful result may be requested at a distinct
logical index. -/
theorem matchAllFuel_valueAndBindingIndexedSafe
    (targetSafe : FuelResultSafe fuel matcherTarget
      (evalFuel fuel environment targetExpression))
    (matcherSafe : FuelResultSafe fuel (.matcher capability matcherTarget)
      (evalFuel fuel environment matcherExpression))
    (searchSafe : EvaluatedPatternSearchSafeUnder bindingsInvariant fuel
      environment targetExpression matcherExpression pattern bindingTypes)
    (bodySafe : EvaluatedBindingBodySafeUnder bindingsInvariant fuel
      resultIndex environment bindingTypes bodyExpression bodyTarget) :
    FuelResultSafe resultIndex (TypePM.DataTypes.list bodyTarget)
      (evalFuel (fuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern bodyExpression)) := by
  rcases targetSafe with targetTimeout |
    ⟨targetValue, targetSuccess, _targetValueSafe⟩
  · exact .inl (by
      simp [evalFuel, targetTimeout, FuelResult.bind])
  · rcases matcherSafe with matcherTimeout |
      ⟨matcherValue, matcherSuccess, _matcherValueSafe⟩
    · exact .inl (by
        simp [evalFuel, targetSuccess, matcherTimeout, FuelResult.bind])
    · rcases searchSafe targetValue matcherValue targetSuccess matcherSuccess with
        searchTimeout | ⟨answers, searchSuccess, answersSafe⟩
      · exact .inl (by
          simp [evalFuel, targetSuccess, matcherSuccess, searchTimeout,
            FuelResult.bind])
      · rcases traverseEvaluatedBindingBodiesUnder answersSafe bodySafe with
          bodiesTimeout | ⟨values, bodiesSuccess, valuesSafe⟩
        · exact .inl (by
            simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
              bodiesTimeout, FuelResult.bind, FuelResult.map])
        · exact .inr ⟨Value.buildList values, by
            simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
              bodiesSuccess, FuelResult.bind, FuelResult.map],
            fuelValueSafe_list_of_forall bodyTarget resultIndex values
              valuesSafe⟩

private theorem traverseEvaluatedBindingBodies
    (answersTyped : TotalPlainMatchingAnswersTyping answers bindingTypes)
    (bodySafe : EvaluatedBindingBodySafe fuel environment bindingTypes
      bodyExpression bodyTarget) :
    FuelResult.traverse
        (fun bindings => evalFuel fuel (bindings ++ environment) bodyExpression)
        answers = .timeout ∨
      ∃ values,
        FuelResult.traverse
            (fun bindings =>
              evalFuel fuel (bindings ++ environment) bodyExpression)
            answers = .ok values ∧
          ∀ value ∈ values, FuelValueSafe fuel value bodyTarget := by
  induction answers with
  | nil => exact .inr ⟨[], rfl, by simp⟩
  | cons bindings answers induction =>
      have bindingsTyped := answersTyped bindings (by simp)
      have tailTyped : TotalPlainMatchingAnswersTyping answers bindingTypes := by
        intro candidate member
        exact answersTyped candidate (by simp [member])
      rcases bodySafe bindings bindingsTyped with bodyTimeout |
        ⟨value, bodySuccess, valueSafe⟩
      · exact .inl (by simp [FuelResult.traverse, bodyTimeout])
      · rcases induction tailTyped with tailTimeout |
          ⟨values, tailSuccess, valuesSafe⟩
        · exact .inl (by
            simp [FuelResult.traverse, bodySuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨value :: values, by
            simp [FuelResult.traverse, bodySuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with equality | member
            · simpa [equality] using valueSafe
            · exact valuesSafe candidate member⟩

/-- One common-fuel `matchAll` rule.  Target and matcher evaluation are
checked in the step-indexed relation; search is certified only for their
actual successful values; and every typed binding group is passed to the
body certificate. -/
theorem matchAllFuel_valueIndexedSafe
    (targetSafe : FuelResultSafe fuel matcherTarget
      (evalFuel fuel environment targetExpression))
    (matcherSafe : FuelResultSafe fuel (.matcher capability matcherTarget)
      (evalFuel fuel environment matcherExpression))
    (searchSafe : EvaluatedPatternSearchSafe fuel environment
      targetExpression matcherExpression pattern bindingTypes)
    (bodySafe : EvaluatedBindingBodySafe fuel environment bindingTypes
      bodyExpression bodyTarget) :
    FuelResultSafe fuel (TypePM.DataTypes.list bodyTarget)
      (evalFuel (fuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern bodyExpression)) := by
  rcases targetSafe with targetTimeout |
    ⟨targetValue, targetSuccess, targetValueSafe⟩
  · exact .inl (by
      simp [evalFuel, targetTimeout, FuelResult.bind])
  · rcases matcherSafe with matcherTimeout |
      ⟨matcherValue, matcherSuccess, matcherValueSafe⟩
    · exact .inl (by
        simp [evalFuel, targetSuccess, matcherTimeout, FuelResult.bind])
    · rcases searchSafe targetValue matcherValue targetSuccess matcherSuccess with
        searchTimeout | ⟨answers, searchSuccess, answersTyped⟩
      · exact .inl (by
          simp [evalFuel, targetSuccess, matcherSuccess, searchTimeout,
            FuelResult.bind])
      · rcases traverseEvaluatedBindingBodies answersTyped bodySafe with
          bodiesTimeout | ⟨values, bodiesSuccess, valuesSafe⟩
        · exact .inl (by
            simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
              bodiesTimeout, FuelResult.bind, FuelResult.map])
        · exact .inr ⟨Value.buildList values, by
            simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
              bodiesSuccess, FuelResult.bind, FuelResult.map],
            fuelValueSafe_list_of_forall bodyTarget fuel values valuesSafe⟩

theorem matchAllFuel_valueIndexedNeverStuck
    (targetSafe : FuelResultSafe fuel matcherTarget
      (evalFuel fuel environment targetExpression))
    (matcherSafe : FuelResultSafe fuel (.matcher capability matcherTarget)
      (evalFuel fuel environment matcherExpression))
    (searchSafe : EvaluatedPatternSearchSafe fuel environment
      targetExpression matcherExpression pattern bindingTypes)
    (bodySafe : EvaluatedBindingBodySafe fuel environment bindingTypes
      bodyExpression bodyTarget) :
    (evalFuel (fuel + 1) environment
      (.matchAll targetExpression matcherExpression pattern bodyExpression)).NotStuck :=
  (matchAllFuel_valueIndexedSafe targetSafe matcherSafe searchSafe bodySafe).notStuck

end TypePM.Runtime
