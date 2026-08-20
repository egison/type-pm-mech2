import TypePM.PatternFunctionPrivateBodyPlanAutomationRegression

/-!
# Actual-evaluator execution of the frozen successful constructor fixture

The public-freeze regression already checks the source definition and gives
an exact, dispatch-indexed certificate for its successful `cons` body atom.
It then runs the checked MNode search with a small certified reducer.

This module closes the remaining concrete operational gap at evaluator
callback fuel four.  It enumerates the complete reachable-state chain, proves
that the real `evaluationAtomReducer (evalFuel 4)` takes exactly the same step
as the certified reducer at every state in that chain, and transfers the
checked DFS theorem for every search fuel.  The exact completed answer is
proved separately at DFS fuel five.

Nothing here claims agreement away from the reachable fixture states, at a
different callback fuel, or for a general user matcher.
-/

namespace TypePM.PatternFunctionPrivateSuccessfulConstructorActualEvaluationRegression

open Runtime Source
open PatternFunctionPrivateBodyPlanAutomationRegression

abbrev definitions : PatternFunctionDefinitions :=
  frozenPrivateSuccessfulConstructor.definitions

abbrev actualReducer : AtomReducer :=
  evaluationAtomReducer (evalFuel 4)

def openedState : PatternFunctionState :=
  ⟨[.node
      [.atom ⟨privateSuccessfulConstructorBody,
        successfulConstructorMatcher, successfulConstructorTarget⟩]
      [] [] []], [], []⟩

def delegatedState : PatternFunctionState :=
  ⟨[.node
      [.atom ⟨.var, .something, .int 7⟩]
      [] [] []], [], []⟩

def privateBoundState : PatternFunctionState :=
  ⟨[.node [] [] [.int 7] []], [], []⟩

def finishedState : PatternFunctionState :=
  ⟨[], [], []⟩

set_option maxRecDepth 100000 in
private theorem successfulConstructor_actualReduction
    (environment : ValueEnvironment) :
    actualReducer environment
        ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
          successfulConstructorTarget⟩ =
      .ok (.hit successfulConstructorReduction) := by
  with_unfolding_all rfl

/-- The exact dispatcher-indexed certificate is used by the checked reducer;
the real reducer computes that same certified reduction in every environment
needed by the fixture. -/
theorem successfulConstructor_reducerAgreement
    (environment : ValueEnvironment) :
    actualReducer environment
        ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
          successfulConstructorTarget⟩ =
      successfulConstructorReducer environment
        ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
          successfulConstructorTarget⟩ := by
  rw [successfulConstructor_actualReduction]
  rfl

theorem delegatedVariable_reducerAgreement
    (environment : ValueEnvironment) :
    actualReducer environment ⟨.var, .something, .int 7⟩ =
      successfulConstructorReducer environment
        ⟨.var, .something, .int 7⟩ := by
  rfl

theorem initial_actualStep :
    stepPatternFunctionState definitions actualReducer
        privateSuccessfulConstructorInitialState =
      .ok (.expand [openedState]) := by
  unfold definitions
  rw [frozenPrivateSuccessfulConstructor_definitions_exact]
  rfl

theorem opened_actualStep :
    stepPatternFunctionState definitions actualReducer openedState =
      .ok (.expand [delegatedState]) := by
  have reduced : actualReducer []
      ⟨Pattern.ctor PatternCtor.cons [.var, .wild],
        successfulConstructorMatcher, successfulConstructorTarget⟩ =
        .ok (.hit successfulConstructorReduction) := by
    simpa [privateSuccessfulConstructorBody] using
      successfulConstructor_actualReduction []
  simp only [openedState, privateSuccessfulConstructorBody,
    stepPatternFunctionState, stepPatternFunctionHead, List.nil_append,
    FuelResult.map]
  rw [reduced]
  rfl

theorem delegated_actualStep :
    stepPatternFunctionState definitions actualReducer delegatedState =
      .ok (.expand [privateBoundState]) := by
  rfl

theorem privateBound_actualStep :
    stepPatternFunctionState definitions actualReducer privateBoundState =
      .ok (.expand [finishedState]) := by
  rfl

theorem finished_actualStep :
    stepPatternFunctionState definitions actualReducer finishedState =
      .ok (.yield []) := by
  rfl

/-- Reachability uses only successful expansion steps of the real evaluator.
It contains no progress or preservation assumption. -/
inductive ActualReachable : PatternFunctionState → Prop where
  | initial : ActualReachable privateSuccessfulConstructorInitialState
  | expand
      (reachable : ActualReachable state)
      (stepped : stepPatternFunctionState definitions actualReducer state =
        .ok (.expand successors))
      (member : successor ∈ successors) :
      ActualReachable successor

theorem opened_reachable : ActualReachable openedState :=
  .expand .initial initial_actualStep (by simp)

theorem delegated_reachable : ActualReachable delegatedState :=
  .expand opened_reachable opened_actualStep (by simp)

theorem privateBound_reachable : ActualReachable privateBoundState :=
  .expand delegated_reachable delegated_actualStep (by simp)

theorem finished_reachable : ActualReachable finishedState :=
  .expand privateBound_reachable privateBound_actualStep (by simp)

/-- Exact closure of the real evaluator's reachable state space. -/
theorem reachable_cases {state : PatternFunctionState}
    (reachable : ActualReachable state) :
    state = privateSuccessfulConstructorInitialState ∨
    state = openedState ∨
    state = delegatedState ∨
    state = privateBoundState ∨
    state = finishedState := by
  induction reachable with
  | initial => exact .inl rfl
  | @expand state successors successor _ stepped member induction =>
      rcases induction with rfl | rfl | rfl | rfl | rfl
      · rw [initial_actualStep] at stepped
        cases stepped
        simp only [List.mem_singleton] at member
        subst successor
        exact .inr (.inl rfl)
      · rw [opened_actualStep] at stepped
        cases stepped
        simp only [List.mem_singleton] at member
        subst successor
        exact .inr (.inr (.inl rfl))
      · rw [delegated_actualStep] at stepped
        cases stepped
        simp only [List.mem_singleton] at member
        subst successor
        exact .inr (.inr (.inr (.inl rfl)))
      · rw [privateBound_actualStep] at stepped
        cases stepped
        simp only [List.mem_singleton] at member
        subst successor
        exact .inr (.inr (.inr (.inr rfl)))
      · rw [finished_actualStep] at stepped
        simp at stepped

/-- Every actually reachable state takes a non-stuck step. -/
theorem reachable_step_notStuck {state : PatternFunctionState}
    (reachable : ActualReachable state) :
    (stepPatternFunctionState definitions actualReducer state).NotStuck := by
  rcases reachable_cases reachable with rfl | rfl | rfl | rfl | rfl
  · rw [initial_actualStep]
    trivial
  · rw [opened_actualStep]
    trivial
  · rw [delegated_actualStep]
    trivial
  · rw [privateBound_actualStep]
    trivial
  · rw [finished_actualStep]
    trivial

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

private theorem checked_successor
    (stateTyped : CheckedScopedStateTyping
      frozenPrivateSuccessfulConstructor.signature definitions state [])
    (stepped : stepPatternFunctionState definitions
      successfulConstructorReducer state = .ok (.expand successors))
    (member : successor ∈ successors) :
    CheckedScopedStateTyping frozenPrivateSuccessfulConstructor.signature
      definitions successor [] := by
  rcases stepPatternFunctionState_checkedScopedSafe
      successfulConstructorReducer_checkedSafe
      successfulConstructorReducer_structuralSafe stateTyped with
    timeout | ⟨observation, success, observationTyped⟩
  · rw [stepped] at timeout
    contradiction
  · rw [stepped] at success
    cases success
    cases observationTyped with
    | expand _ successorsTyped => exact successorsTyped successor member

theorem opened_checked :
    CheckedScopedStateTyping frozenPrivateSuccessfulConstructor.signature
      definitions openedState [] :=
  checked_successor privateSuccessfulConstructorInitialState_checked_automatic
    initial_checkedStep (by simp)

theorem delegated_checked :
    CheckedScopedStateTyping frozenPrivateSuccessfulConstructor.signature
      definitions delegatedState [] :=
  checked_successor opened_checked opened_checkedStep (by simp)

theorem privateBound_checked :
    CheckedScopedStateTyping frozenPrivateSuccessfulConstructor.signature
      definitions privateBoundState [] :=
  checked_successor delegated_checked delegated_checkedStep (by simp)

theorem finished_checked :
    CheckedScopedStateTyping frozenPrivateSuccessfulConstructor.signature
      definitions finishedState [] :=
  checked_successor privateBound_checked privateBound_checkedStep (by simp)

/-- Every state reached by the real evaluator carries the checked MNode state
invariant.  The proof propagates the imported dispatch-indexed certificate
along the independently computed state chain. -/
theorem reachable_checked {state : PatternFunctionState}
    (reachable : ActualReachable state) :
    CheckedScopedStateTyping frozenPrivateSuccessfulConstructor.signature
      definitions state [] := by
  rcases reachable_cases reachable with rfl | rfl | rfl | rfl | rfl
  · exact privateSuccessfulConstructorInitialState_checked_automatic
  · exact opened_checked
  · exact delegated_checked
  · exact privateBound_checked
  · exact finished_checked

/-- State-level simulation boundary: agreement is asserted only after an
independent real-evaluator reachability derivation, and is discharged from
the five exact state equations above. -/
theorem reachable_step_agreement {state : PatternFunctionState}
    (reachable : ActualReachable state) :
    stepPatternFunctionState definitions actualReducer state =
      stepPatternFunctionState definitions successfulConstructorReducer
        state := by
  rcases reachable_cases reachable with rfl | rfl | rfl | rfl | rfl
  · rw [initial_actualStep, initial_checkedStep]
  · rw [opened_actualStep, opened_checkedStep]
  · rw [delegated_actualStep, delegated_checkedStep]
  · rw [privateBound_actualStep, privateBound_checkedStep]
  · rw [finished_actualStep, finished_checkedStep]

/-- The real and certified searches coincide for every DFS bound.  This is a
consequence of the closed state chain, not a global reducer equation. -/
theorem actual_depthFirst_eq_checked (fuel : Nat) :
    depthFirstFuel (stepPatternFunctionState definitions actualReducer) fuel
        [privateSuccessfulConstructorInitialState] =
      depthFirstFuel
        (stepPatternFunctionState definitions successfulConstructorReducer)
        fuel [privateSuccessfulConstructorInitialState] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [depthFirstFuel, initial_actualStep, initial_checkedStep,
        FuelResult.bind]
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [depthFirstFuel, opened_actualStep, opened_checkedStep,
            FuelResult.bind, List.singleton_append]
          cases fuel with
          | zero => rfl
          | succ fuel =>
              simp only [depthFirstFuel, delegated_actualStep,
                delegated_checkedStep, FuelResult.bind,
                List.singleton_append]
              cases fuel with
              | zero => rfl
              | succ fuel =>
                  simp only [depthFirstFuel, privateBound_actualStep,
                    privateBound_checkedStep, FuelResult.bind,
                    List.singleton_append]
                  cases fuel with
                  | zero => rfl
                  | succ fuel =>
                      simp [depthFirstFuel, finished_actualStep,
                        finished_checkedStep, FuelResult.bind, FuelResult.map]

/-- Checked answer typing for arbitrary DFS fuel with the actual evaluator
reducer at callback fuel four. -/
theorem actual_depthFirst_typed (fuel : Nat) :
    TypedMatchingSearchResult []
      (depthFirstFuel (stepPatternFunctionState definitions actualReducer)
        fuel [privateSuccessfulConstructorInitialState]) := by
  rw [actual_depthFirst_eq_checked]
  exact public_frozen_private_successful_constructor_typed fuel

/-- The actual evaluator search cannot get stuck at any DFS bound. -/
theorem actual_depthFirst_neverStuck (fuel : Nat) :
    (depthFirstFuel (stepPatternFunctionState definitions actualReducer)
      fuel [privateSuccessfulConstructorInitialState]).NotStuck := by
  rcases actual_depthFirst_typed fuel with timeout |
    ⟨answers, success, _answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-- The five visited states suffice for the exact answer.
This result is separate from the arbitrary-fuel safety theorem. -/
theorem actual_depthFirst_exact5 :
    depthFirstFuel (stepPatternFunctionState definitions actualReducer) 5
      [privateSuccessfulConstructorInitialState] = .ok [[]] := by
  simp [depthFirstFuel, initial_actualStep, opened_actualStep,
    delegated_actualStep, privateBound_actualStep, finished_actualStep,
    FuelResult.bind, FuelResult.map]

end TypePM.PatternFunctionPrivateSuccessfulConstructorActualEvaluationRegression
