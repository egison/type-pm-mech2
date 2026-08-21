import TypePM.Source.M4OriginMatchingEvaluationBridge
import TypePM.Source.M5TracedOriginSafety

/-!
# Trace-refined matching-expression safety

This module joins the arbitrary-demand M4 matching boundary with the complete
evaluation trace.  The result observation and the event coverage are proved
for the same execution, so callback and selected-body traces cannot be
discarded between separate preservation arguments.
-/

namespace TypePM.Runtime

/-- Trace-refined body preservation for every binding group returned by one
two-index search. -/
def EvaluatedTracedOriginBindingBodySafeUnder
    (eventSafe : MatchingSearchTraceEvent → Prop)
    (bindingsInvariant : MatchingBindingsInvariant)
    (operationalFuel : Nat) (resultDemand : OriginDemand)
    (environment : ValueEnvironment) (bindingTypes : List Ty)
    (bodyExpression : Source.Expr) (bodyTarget : Ty) : Prop :=
  ∀ bindings,
    bindingsInvariant bindings bindingTypes →
      TracedOriginResultSafe eventSafe resultDemand bodyTarget
        (evalFuel operationalFuel (bindings ++ environment) bodyExpression)
        (evalFuelTrace operationalFuel (bindings ++ environment)
          bodyExpression)

private theorem traceTraverseEvaluatedBodiesSafe
    (answersSafe : MatchingAnswersSafeWith bindingsInvariant answers
      bindingTypes)
    (bodySafe : EvaluatedTracedOriginBindingBodySafeUnder eventSafe
      bindingsInvariant operationalFuel resultDemand environment bindingTypes
      bodyExpression bodyTarget) :
    ∀ event,
      event ∈ traceTraverse
        (fun bindings =>
          evalFuel operationalFuel (bindings ++ environment) bodyExpression)
        (fun bindings =>
          evalFuelTrace operationalFuel (bindings ++ environment)
            bodyExpression)
        answers →
      eventSafe event := by
  induction answers with
  | nil => simp [traceTraverse]
  | cons bindings answers induction =>
      have bindingsSafe := answersSafe bindings (by simp)
      have headSafe := bodySafe bindings bindingsSafe
      have tailSafe : MatchingAnswersSafeWith bindingsInvariant answers
          bindingTypes := by
        intro candidate member
        exact answersSafe candidate (by simp [member])
      intro event member
      cases result : evalFuel operationalFuel (bindings ++ environment)
          bodyExpression with
      | timeout =>
          simp [traceTraverse, result] at member
          exact headSafe.2 event member
      | stuck =>
          simp [traceTraverse, result] at member
          exact headSafe.2 event member
      | ok value =>
          simp only [traceTraverse, result] at member
          rcases List.mem_append.mp member with headMember | tailMember
          · exact headSafe.2 event headMember
          · exact induction tailSafe event tailMember

private theorem traverseEvaluatedTracedBodiesResultSafe
    (answersSafe : MatchingAnswersSafeWith bindingsInvariant answers
      bindingTypes)
    (bodySafe : EvaluatedTracedOriginBindingBodySafeUnder eventSafe
      bindingsInvariant operationalFuel resultDemand environment bindingTypes
      bodyExpression bodyTarget) :
    FuelResult.traverse
        (fun bindings =>
          evalFuel operationalFuel (bindings ++ environment) bodyExpression)
        answers = .timeout ∨
      ∃ values,
        FuelResult.traverse
            (fun bindings =>
              evalFuel operationalFuel (bindings ++ environment)
                bodyExpression)
            answers = .ok values ∧
          ∀ value ∈ values,
            TracedOriginValueSafe eventSafe resultDemand value bodyTarget := by
  induction answers with
  | nil => exact .inr ⟨[], rfl, by simp⟩
  | cons bindings answers induction =>
      have bindingsSafe := answersSafe bindings (by simp)
      have tailSafe : MatchingAnswersSafeWith bindingsInvariant answers
          bindingTypes := by
        intro candidate member
        exact answersSafe candidate (by simp [member])
      rcases (bodySafe bindings bindingsSafe).1 with bodyTimeout |
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
            rcases member with rfl | member
            · exact valueSafe
            · exact valuesSafe candidate member⟩

private theorem tracedOriginValueSafe_buildList
    (itemsSafe : ∀ value ∈ values,
      TracedOriginValueSafe eventSafe elementDemand value elementType) :
    TracedOriginValueSafe eventSafe (.listOf elementDemand)
      (Value.buildList values) (DataTypes.list elementType) := by
  simp only [TracedOriginValueSafe]
  exact ⟨elementType, values, rfl, rfl, itemsSafe⟩

private def TraceEventsSafe
    (eventSafe : MatchingSearchTraceEvent → Prop)
    (trace : List MatchingSearchTraceEvent) : Prop :=
  ∀ event, event ∈ trace → eventSafe event

private theorem TraceEventsSafe.append
    (leftSafe : TraceEventsSafe eventSafe left)
    (rightSafe : TraceEventsSafe eventSafe right) :
    TraceEventsSafe eventSafe (left ++ right) := by
  intro event member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftSafe event leftMember
  · exact rightSafe event rightMember

private theorem TraceEventsSafe.singleton
    (safe : eventSafe event) : TraceEventsSafe eventSafe [event] := by
  intro candidate member
  simp only [List.mem_singleton] at member
  subst candidate
  exact safe

/-- Complete trace-refined `matchAll` composition.  The outer event is
annotated separately from the callback events emitted while executing its
bounded DFS.  Every selected body is then covered using the exact binding
invariant returned by that same search. -/
theorem matchAllFuel_twoIndexTracedOriginSafe
    (eventSafe : MatchingSearchTraceEvent → Prop)
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (targetSafe : TracedOriginResultSafe eventSafe (.fuel operationalFuel)
      matcherTarget (evalFuel operationalFuel environment targetExpression)
      (evalFuelTrace operationalFuel environment targetExpression))
    (matcherSafe : TracedOriginResultSafe eventSafe (.fuel operationalFuel)
      (.matcher capability matcherTarget)
      (evalFuel operationalFuel environment matcherExpression)
      (evalFuelTrace operationalFuel environment matcherExpression))
    (initialTyped : EvaluatedTwoIndexInitialStateTyping environmentInvariant
      bindingsInvariant operationalFuel bindingIndex environment
      targetExpression matcherExpression pattern bindingTypes)
    (outerEventSafe : ∀ targetValue matcherValue,
      evalFuel operationalFuel environment targetExpression = .ok targetValue →
      evalFuel operationalFuel environment matcherExpression = .ok matcherValue →
        eventSafe ⟨operationalFuel, environment, pattern, matcherValue,
          targetValue⟩)
    (callbackTraceSafe : ∀ targetValue matcherValue,
      evalFuel operationalFuel environment targetExpression = .ok targetValue →
      evalFuel operationalFuel environment matcherExpression = .ok matcherValue →
        ∀ event,
          event ∈ searchPatternFuelTrace (evalFuel operationalFuel)
            (evalFuelTrace operationalFuel) operationalFuel environment pattern
            matcherValue targetValue →
          eventSafe event)
    (bodySafe : EvaluatedTracedOriginBindingBodySafeUnder eventSafe
      (bindingsInvariant bindingIndex) operationalFuel resultDemand environment
      bindingTypes bodyExpression bodyTarget) :
    TracedOriginResultSafe eventSafe (.listOf resultDemand)
      (DataTypes.list bodyTarget)
      (evalFuel (operationalFuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern bodyExpression))
      (evalFuelTrace (operationalFuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern bodyExpression)) := by
  constructor
  · rcases targetSafe.forget.toFuel with targetTimeout |
      ⟨targetValue, targetSuccess, _targetValueSafe⟩
    · exact .inl (by
        simp [evalFuel, targetTimeout, FuelResult.bind])
    · rcases matcherSafe.forget.toFuel with matcherTimeout |
        ⟨matcherValue, matcherSuccess, _matcherValueSafe⟩
      · exact .inl (by
          simp [evalFuel, targetSuccess, matcherTimeout, FuelResult.bind])
      · have searchSafe := searchPatternFuel_twoIndexSafe
          environmentDownward bindingsDownward
          (initialTyped targetValue matcherValue targetSuccess matcherSuccess)
        rcases searchSafe with searchTimeout |
          ⟨answers, searchSuccess, answersSafe⟩
        · exact .inl (by
            simp [evalFuel, targetSuccess, matcherSuccess, searchTimeout,
              FuelResult.bind])
        · rcases traverseEvaluatedTracedBodiesResultSafe answersSafe
            bodySafe with bodiesTimeout |
            ⟨values, bodiesSuccess, valuesSafe⟩
          · exact .inl (by
              simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
                bodiesTimeout, FuelResult.bind, FuelResult.map])
          · exact .inr ⟨Value.buildList values, by
              simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
                bodiesSuccess, FuelResult.bind, FuelResult.map],
              tracedOriginValueSafe_buildList valuesSafe⟩
  · intro event member
    cases targetResult : evalFuel operationalFuel environment targetExpression with
    | timeout =>
        apply targetSafe.2 event
        simpa [evalFuelTrace, targetResult] using member
    | stuck =>
        apply targetSafe.2 event
        simpa [evalFuelTrace, targetResult] using member
    | ok targetValue =>
        cases matcherResult : evalFuel operationalFuel environment
            matcherExpression with
        | timeout =>
            have combined := TraceEventsSafe.append targetSafe.2 matcherSafe.2
            apply combined event
            simpa [evalFuelTrace, targetResult, matcherResult] using member
        | stuck =>
            have combined := TraceEventsSafe.append targetSafe.2 matcherSafe.2
            apply combined event
            simpa [evalFuelTrace, targetResult, matcherResult] using member
        | ok matcherValue =>
            let searchTrace := searchPatternFuelTrace (evalFuel operationalFuel)
              (evalFuelTrace operationalFuel) operationalFuel environment
              pattern matcherValue targetValue
            have outerSafe : eventSafe
                ⟨operationalFuel, environment, pattern, matcherValue,
                  targetValue⟩ :=
              outerEventSafe targetValue matcherValue targetResult matcherResult
            have callbacksSafe : ∀ candidate, candidate ∈ searchTrace →
                eventSafe candidate :=
              callbackTraceSafe targetValue matcherValue targetResult
                matcherResult
            cases searchResult : searchPatternFuel (evalFuel operationalFuel)
                operationalFuel environment pattern matcherValue targetValue with
            | timeout =>
                have combined := TraceEventsSafe.append
                  (TraceEventsSafe.append
                    (TraceEventsSafe.append targetSafe.2 matcherSafe.2)
                    (TraceEventsSafe.singleton outerSafe))
                  callbacksSafe
                apply combined event
                simpa [evalFuelTrace, targetResult, matcherResult,
                  searchResult, searchTrace] using member
            | stuck =>
                have combined := TraceEventsSafe.append
                  (TraceEventsSafe.append
                    (TraceEventsSafe.append targetSafe.2 matcherSafe.2)
                    (TraceEventsSafe.singleton outerSafe))
                  callbacksSafe
                apply combined event
                simpa [evalFuelTrace, targetResult, matcherResult,
                  searchResult, searchTrace] using member
            | ok answers =>
                have searchSafe := searchPatternFuel_twoIndexSafe
                  environmentDownward bindingsDownward
                  (initialTyped targetValue matcherValue targetResult
                    matcherResult)
                rcases searchSafe with impossible | ⟨actualAnswers, success,
                  answersSafe⟩
                · rw [searchResult] at impossible
                  contradiction
                · rw [searchResult] at success
                  cases success
                  have bodiesSafe : TraceEventsSafe eventSafe
                      (traceTraverse
                        (fun bindings => evalFuel operationalFuel
                          (bindings ++ environment) bodyExpression)
                        (fun bindings => evalFuelTrace operationalFuel
                          (bindings ++ environment) bodyExpression)
                        answers) :=
                    traceTraverseEvaluatedBodiesSafe answersSafe bodySafe
                  have combined := TraceEventsSafe.append
                    (TraceEventsSafe.append
                      (TraceEventsSafe.append
                        (TraceEventsSafe.append targetSafe.2 matcherSafe.2)
                        (TraceEventsSafe.singleton outerSafe))
                      callbacksSafe)
                    bodiesSafe
                  apply combined event
                  simpa [evalFuelTrace, targetResult, matcherResult,
                    searchResult, searchTrace] using member

end TypePM.Runtime
