import TypePM.PatternFunctionPrivateSuccessfulConstructorActualEvaluationRegression

/-!
# All-callback execution of the frozen successful constructor fixture

The fixed-callback regression proves exact execution with the real evaluator
at callback fuel four.  This module classifies the complete callback range
without asserting a global equality between reducers:

* callback fuel zero and one time out at the opened user-matcher atom;
* every callback fuel at least two returns the same single delegated branch;
* consequently, for every callback fuel and every DFS fuel, the actual search
  either times out or returns well-typed answers and never gets stuck.

The completed answer is retained only in the successful callback range.  The
proof compares reducers solely along the five states reachable in this frozen
fixture.
-/

namespace TypePM.PatternFunctionPrivateSuccessfulConstructorAllCallbackEvaluationRegression

open Runtime Source
open PatternFunctionPrivateBodyPlanAutomationRegression
open PatternFunctionPrivateSuccessfulConstructorActualEvaluationRegression

abbrev definitions : PatternFunctionDefinitions :=
  frozenPrivateSuccessfulConstructor.definitions

def actualReducerAt (callbackFuel : Nat) : AtomReducer :=
  evaluationAtomReducer (evalFuel callbackFuel)

private theorem decompositionBody_eval_from_two
    (extra : Nat) (environment : ValueEnvironment) :
    evalFuel (extra + 2) (.int 7 :: environment)
        successfulConstructorDecompositionBody =
      .ok (Value.buildList [.int 7]) := by
  cases extra <;> rfl

private theorem nextMatcher_eval_from_two
    (extra : Nat) (environment : ValueEnvironment) :
    evalFuel (extra + 2) environment .something = .ok .something := by
  cases extra <;> rfl

theorem successfulConstructor_dispatch_zero
    (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel 0) atomEnvironment []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget =
      .timeout := by
  with_unfolding_all rfl

theorem successfulConstructor_dispatch_one
    (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel 1) atomEnvironment []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget =
      .timeout := by
  with_unfolding_all rfl

/-- Callback fuel two is the first successful dispatch.  Every larger callback
fuel produces exactly the same source-ordered singleton branch. -/
theorem successfulConstructor_dispatch_from_two
    (extra : Nat) (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel (extra + 2)) atomEnvironment []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget =
      .ok (.hit [[⟨.var, .something, .int 7⟩]]) := by
  simp [dispatchMatcherClauses, firstHit, tryMatcherClause,
    inspectPatternPattern, inspectPatternPatterns, FuelResult.traverse,
    tryMatcherArm, matchValueDataPattern, matchValueDataPatterns,
    PatternDispatch.empty, PatternDispatch.append,
    successfulConstructorClause,
    privateSuccessfulConstructorBody, successfulConstructorTarget,
    decompositionBody_eval_from_two extra,
    nextMatcher_eval_from_two extra,
    Value.consValue, Value.buildList, Value.nilValue, Value.viewList,
    decodeDecompositions, closeMatcherArmsResult,
    buildMatchingBranches, zipMatchingAtoms, List.mapM_cons,
    FuelResult.bind, FuelResult.map]

/-- Complete callback classification for the concrete user-matcher atom. -/
theorem successfulConstructor_dispatch_allCallback
    (callbackFuel : Nat) (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget =
        .timeout ∨
      dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget =
        .ok (.hit [[⟨.var, .something, .int 7⟩]]) := by
  cases callbackFuel with
  | zero => exact .inl (successfulConstructor_dispatch_zero atomEnvironment)
  | succ callbackFuel =>
      cases callbackFuel with
      | zero => exact .inl (successfulConstructor_dispatch_one atomEnvironment)
      | succ extra =>
          have callbackEq : extra + 1 + 1 = extra + 2 := by omega
          rw [callbackEq]
          exact .inr
            (successfulConstructor_dispatch_from_two extra atomEnvironment)

private theorem successfulConstructor_actualReduction_from_two
    (extra : Nat) (environment : ValueEnvironment) :
    actualReducerAt (extra + 2) environment
        ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
          successfulConstructorTarget⟩ =
      .ok (.hit successfulConstructorReduction) := by
  have dispatched := successfulConstructor_dispatch_from_two extra environment
  have dispatched' :
      dispatchMatcherClauses (evalFuel (extra + 2)) environment []
          [successfulConstructorClause, successfulConstructorFallbackClause]
          (.ctor PatternCtor.cons [.var, .wild])
          (.data DataCtor.cons [.int 7, .data DataCtor.nil []]) =
        .ok (.hit [[⟨.var, .something, .int 7⟩]]) := by
    simpa [privateSuccessfulConstructorBody, successfulConstructorTarget] using
      dispatched
  simp only [actualReducerAt, evaluationAtomReducer, combineAtomReducers,
    privateSuccessfulConstructorBody, successfulConstructorMatcher,
    successfulConstructorTarget, reduceBuiltinAtom, FuelResult.bind,
    reduceMatcherAtom]
  rw [dispatched']
  rfl

private theorem successfulConstructor_actualReduction_zero
    (environment : ValueEnvironment) :
    actualReducerAt 0 environment
        ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
          successfulConstructorTarget⟩ = .timeout := by
  have dispatched := successfulConstructor_dispatch_zero environment
  have dispatched' :
      dispatchMatcherClauses (evalFuel 0) environment []
          [successfulConstructorClause, successfulConstructorFallbackClause]
          (.ctor PatternCtor.cons [.var, .wild])
          (.data DataCtor.cons [.int 7, .data DataCtor.nil []]) = .timeout := by
    simpa [privateSuccessfulConstructorBody, successfulConstructorTarget] using
      dispatched
  simp only [actualReducerAt, evaluationAtomReducer, combineAtomReducers,
    privateSuccessfulConstructorBody, successfulConstructorMatcher,
    successfulConstructorTarget, reduceBuiltinAtom, FuelResult.bind,
    reduceMatcherAtom]
  rw [dispatched']
  rfl

private theorem successfulConstructor_actualReduction_one
    (environment : ValueEnvironment) :
    actualReducerAt 1 environment
        ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
          successfulConstructorTarget⟩ = .timeout := by
  have dispatched := successfulConstructor_dispatch_one environment
  have dispatched' :
      dispatchMatcherClauses (evalFuel 1) environment []
          [successfulConstructorClause, successfulConstructorFallbackClause]
          (.ctor PatternCtor.cons [.var, .wild])
          (.data DataCtor.cons [.int 7, .data DataCtor.nil []]) = .timeout := by
    simpa [privateSuccessfulConstructorBody, successfulConstructorTarget] using
      dispatched
  simp only [actualReducerAt, evaluationAtomReducer, combineAtomReducers,
    privateSuccessfulConstructorBody, successfulConstructorMatcher,
    successfulConstructorTarget, reduceBuiltinAtom, FuelResult.bind,
    reduceMatcherAtom]
  rw [dispatched']
  rfl

private theorem initial_actualStep (callbackFuel : Nat) :
    stepPatternFunctionState definitions (actualReducerAt callbackFuel)
        privateSuccessfulConstructorInitialState =
      .ok (.expand [openedState]) := by
  unfold definitions
  rw [frozenPrivateSuccessfulConstructor_definitions_exact]
  rfl

private theorem opened_actualStep_from_two (extra : Nat) :
    stepPatternFunctionState definitions (actualReducerAt (extra + 2))
        openedState = .ok (.expand [delegatedState]) := by
  have reduced : actualReducerAt (extra + 2) []
      ⟨Pattern.ctor PatternCtor.cons [.var, .wild],
        successfulConstructorMatcher, successfulConstructorTarget⟩ =
        .ok (.hit successfulConstructorReduction) := by
    simpa [privateSuccessfulConstructorBody] using
      successfulConstructor_actualReduction_from_two extra []
  simp only [openedState, privateSuccessfulConstructorBody,
    stepPatternFunctionState, stepPatternFunctionHead, List.nil_append,
    FuelResult.map]
  rw [reduced]
  rfl

private theorem opened_actualStep_zero :
    stepPatternFunctionState definitions (actualReducerAt 0) openedState =
      .timeout := by
  have reduced : actualReducerAt 0 []
      ⟨Pattern.ctor PatternCtor.cons [.var, .wild],
        successfulConstructorMatcher, successfulConstructorTarget⟩ =
        .timeout := by
    simpa [privateSuccessfulConstructorBody] using
      successfulConstructor_actualReduction_zero []
  simp only [openedState, privateSuccessfulConstructorBody,
    stepPatternFunctionState, stepPatternFunctionHead, List.nil_append,
    FuelResult.map]
  rw [reduced]
  rfl

private theorem opened_actualStep_one :
    stepPatternFunctionState definitions (actualReducerAt 1) openedState =
      .timeout := by
  have reduced : actualReducerAt 1 []
      ⟨Pattern.ctor PatternCtor.cons [.var, .wild],
        successfulConstructorMatcher, successfulConstructorTarget⟩ =
        .timeout := by
    simpa [privateSuccessfulConstructorBody] using
      successfulConstructor_actualReduction_one []
  simp only [openedState, privateSuccessfulConstructorBody,
    stepPatternFunctionState, stepPatternFunctionHead, List.nil_append,
    FuelResult.map]
  rw [reduced]
  rfl

private theorem delegated_actualStep (callbackFuel : Nat) :
    stepPatternFunctionState definitions (actualReducerAt callbackFuel)
        delegatedState = .ok (.expand [privateBoundState]) := by
  rfl

private theorem privateBound_actualStep (callbackFuel : Nat) :
    stepPatternFunctionState definitions (actualReducerAt callbackFuel)
        privateBoundState = .ok (.expand [finishedState]) := by
  rfl

private theorem finished_actualStep (callbackFuel : Nat) :
    stepPatternFunctionState definitions (actualReducerAt callbackFuel)
        finishedState = .ok (.yield []) := by
  rfl

private theorem initial_checkedStep :
    stepPatternFunctionState definitions successfulConstructorReducer
        privateSuccessfulConstructorInitialState =
      .ok (.expand [openedState]) := by
  unfold definitions
  rw [frozenPrivateSuccessfulConstructor_definitions_exact]
  rfl

private theorem opened_checkedStep :
    stepPatternFunctionState definitions successfulConstructorReducer
        openedState = .ok (.expand [delegatedState]) := by
  rfl

private theorem delegated_checkedStep :
    stepPatternFunctionState definitions successfulConstructorReducer
        delegatedState = .ok (.expand [privateBoundState]) := by
  rfl

private theorem privateBound_checkedStep :
    stepPatternFunctionState definitions successfulConstructorReducer
        privateBoundState = .ok (.expand [finishedState]) := by
  rfl

private theorem finished_checkedStep :
    stepPatternFunctionState definitions successfulConstructorReducer
        finishedState = .ok (.yield []) := by
  rfl

/-- In the successful callback range, the actual and certified searches agree
at every DFS bound.  Agreement is proved only along the concrete state chain. -/
theorem actual_depthFirst_from_two_eq_checked (extra searchFuel : Nat) :
    depthFirstFuel
        (stepPatternFunctionState definitions (actualReducerAt (extra + 2)))
        searchFuel [privateSuccessfulConstructorInitialState] =
      depthFirstFuel
        (stepPatternFunctionState definitions successfulConstructorReducer)
        searchFuel [privateSuccessfulConstructorInitialState] := by
  cases searchFuel with
  | zero => rfl
  | succ searchFuel =>
      simp only [depthFirstFuel, initial_actualStep, initial_checkedStep,
        FuelResult.bind]
      cases searchFuel with
      | zero => rfl
      | succ searchFuel =>
          simp only [depthFirstFuel, opened_actualStep_from_two,
            opened_checkedStep, List.singleton_append, FuelResult.bind]
          cases searchFuel with
          | zero => rfl
          | succ searchFuel =>
              simp only [depthFirstFuel, delegated_actualStep,
                delegated_checkedStep, List.singleton_append, FuelResult.bind]
              cases searchFuel with
              | zero => rfl
              | succ searchFuel =>
                  simp only [depthFirstFuel, privateBound_actualStep,
                    privateBound_checkedStep, List.singleton_append,
                    FuelResult.bind]
                  cases searchFuel with
                  | zero => rfl
                  | succ searchFuel =>
                      simp [depthFirstFuel, finished_actualStep,
                        finished_checkedStep, FuelResult.bind, FuelResult.map]

/-- At callback fuel zero the actual search times out at every DFS bound. -/
theorem actual_depthFirst_zero_timeout (searchFuel : Nat) :
    depthFirstFuel (stepPatternFunctionState definitions (actualReducerAt 0))
        searchFuel [privateSuccessfulConstructorInitialState] = .timeout := by
  cases searchFuel with
  | zero => rfl
  | succ searchFuel =>
      simp only [depthFirstFuel, initial_actualStep, FuelResult.bind]
      cases searchFuel with
      | zero => rfl
      | succ searchFuel =>
          simp [depthFirstFuel, opened_actualStep_zero, FuelResult.bind]

/-- At callback fuel one the actual search likewise times out at every DFS
bound. -/
theorem actual_depthFirst_one_timeout (searchFuel : Nat) :
    depthFirstFuel (stepPatternFunctionState definitions (actualReducerAt 1))
        searchFuel [privateSuccessfulConstructorInitialState] = .timeout := by
  cases searchFuel with
  | zero => rfl
  | succ searchFuel =>
      simp only [depthFirstFuel, initial_actualStep, FuelResult.bind]
      cases searchFuel with
      | zero => rfl
      | succ searchFuel =>
          simp [depthFirstFuel, opened_actualStep_one, FuelResult.bind]

/-- For arbitrary callback fuel and DFS fuel, every completed answer produced
by the actual evaluator is well typed. -/
theorem actual_depthFirst_typed_allCallback
    (callbackFuel searchFuel : Nat) :
    TypedMatchingSearchResult []
      (depthFirstFuel
        (stepPatternFunctionState definitions (actualReducerAt callbackFuel))
        searchFuel [privateSuccessfulConstructorInitialState]) := by
  cases callbackFuel with
  | zero =>
      rw [actual_depthFirst_zero_timeout]
      exact .inl rfl
  | succ callbackFuel =>
      cases callbackFuel with
      | zero =>
          rw [actual_depthFirst_one_timeout]
          exact .inl rfl
      | succ extra =>
          rw [actual_depthFirst_from_two_eq_checked extra]
          exact public_frozen_private_successful_constructor_typed searchFuel

/-- Arbitrary evaluator callback fuel and arbitrary DFS fuel cannot make the
frozen successful-constructor search get stuck. -/
theorem actual_depthFirst_neverStuck_allCallback
    (callbackFuel searchFuel : Nat) :
    (depthFirstFuel
      (stepPatternFunctionState definitions (actualReducerAt callbackFuel))
      searchFuel [privateSuccessfulConstructorInitialState]).NotStuck := by
  rcases actual_depthFirst_typed_allCallback callbackFuel searchFuel with
    timeout | ⟨answers, success, _answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-- In the successful callback range, five DFS steps produce the exact empty
binding answer.  No exact answer is claimed at callback fuel zero or one. -/
theorem actual_depthFirst_exact5_from_two (extra : Nat) :
    depthFirstFuel
      (stepPatternFunctionState definitions (actualReducerAt (extra + 2))) 5
      [privateSuccessfulConstructorInitialState] = .ok [[]] := by
  simp [depthFirstFuel, initial_actualStep, opened_actualStep_from_two,
    delegated_actualStep, privateBound_actualStep, finished_actualStep,
    FuelResult.bind, FuelResult.map]

end TypePM.PatternFunctionPrivateSuccessfulConstructorAllCallbackEvaluationRegression
