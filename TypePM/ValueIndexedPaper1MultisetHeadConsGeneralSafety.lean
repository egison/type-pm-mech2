import TypePM.ValueIndexedPaper1MultisetHeadConsSafety

/-!
# General all-fuel safety of the Paper 1 multiset head-cons clause

This module generalizes the concrete `$ :: _` execution proof from three
integers to every canonical runtime list.  The operational result depends only
on the source order of that list; it does not inspect its element values.
-/

namespace TypePM.ValueIndexedPaper1MultisetHeadConsGeneralSafety

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open Source.MatcherTyping.M4Paper1RecursiveClosureTotalTyping
open ValueIndexedPaper1MultisetHeadConsSafety

def headConsTargetOf (values : List Value) : Value :=
  Value.buildList values

def headConsBranchesOf (values : List Value) : MatchingBranches :=
  values.map fun value => [⟨.var, .something, value⟩]

def headConsAnswersOf (values : List Value) : List (List Value) :=
  values.map fun value => [value]

def headConsSuccessorStatesOf (values : List Value) : List MatchingState :=
  values.map fun value =>
    ⟨[⟨.var, .something, value⟩], [], []⟩

private theorem decodeProducts_one (values : List Value) :
    values.mapM (decodeProduct 1) = some (values.map fun value => [value]) := by
  induction values with
  | nil => rfl
  | cons value values induction => simp [decodeProduct, induction]

private theorem buildHeadConsBranches (values : List Value) :
    values.mapM (zipMatchingAtoms [.var] [.something] ∘ fun value => [value]) =
      some (headConsBranchesOf values) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [zipMatchingAtoms, headConsBranchesOf, induction]

theorem nilClause_headConsOf_miss
    (values : List Value) (fuel : Nat)
    (atomEnvironment matcherEnvironment : ValueEnvironment) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      headConsPattern (headConsTargetOf values) nilClause = .ok .miss := by
  rfl

theorem headOnlyClause_headConsOf_try :
    ∀ values fuel atomEnvironment,
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment headConsPattern
        (headConsTargetOf values) headOnlyClause = .timeout ∨
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment headConsPattern
        (headConsTargetOf values) headOnlyClause =
          .ok (.hit (headConsBranchesOf values))
  | _, 0, _ => .inl rfl
  | values, _ + 1, _ => .inr (by
      simp [tryMatcherClause, headOnlyClause, headConsTargetOf,
        headConsBranchesOf, headConsPattern,
        closedMultisetMatcherEnvironment, evalFuel, firstHit, tryMatcherArm,
        buildMatchingBranches, decodeDecompositions,
        inspectPatternPattern, inspectPatternPatterns,
        PatternDispatch.append, PatternDispatch.empty,
        matchValueDataPattern, FuelResult.traverse, decodeProduct,
        closeMatcherArmsResult,
        Value.viewList_buildList, decodeProducts_one,
        buildHeadConsBranches])

theorem headConsOf_dispatch :
    ∀ values fuel atomEnvironment,
      dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses headConsPattern
        (headConsTargetOf values) = .timeout ∨
      dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses headConsPattern
        (headConsTargetOf values) =
          .ok (.hit (headConsBranchesOf values)) := by
  intro values fuel atomEnvironment
  simpa [multisetClauses] using
    (dispatch_of_firstMiss_secondHitOrTimeout
      (nilClause_headConsOf_miss values fuel atomEnvironment
        closedMultisetMatcherEnvironment)
      (headOnlyClause_headConsOf_try values fuel atomEnvironment)
      (remaining := [valueConsClause, generalConsClause, joinClause,
        wholeValueClause, catchAllClause]))

theorem headConsOf_initialReduction :
    ∀ values callbackFuel atomEnvironment,
      evaluationAtomReducer (evalFuel callbackFuel) atomEnvironment
        ⟨headConsPattern, closedMultisetMatcherValue,
          headConsTargetOf values⟩ = .timeout ∨
      evaluationAtomReducer (evalFuel callbackFuel) atomEnvironment
        ⟨headConsPattern, closedMultisetMatcherValue,
          headConsTargetOf values⟩ =
          .ok (.hit ⟨headConsBranchesOf values, []⟩) := by
  intro values callbackFuel atomEnvironment
  rcases headConsOf_dispatch values callbackFuel atomEnvironment with
    timeout | success
  · exact .inl (by
      rw [show headConsPattern = .ctor PatternCtor.cons [.var, .wild] by rfl]
        at timeout ⊢
      unfold evaluationAtomReducer combineAtomReducers
      rw [Source.MatcherTyping.reduceBuiltinAtom_constructor_miss]
      simp only [FuelResult.bind]
      simpa [reduceMatcherAtom, closedMultisetMatcherValue] using
        congrArg (FuelResult.map clauseResultToAtomReduction) timeout)
  · exact .inr (by
      rw [show headConsPattern = .ctor PatternCtor.cons [.var, .wild] by rfl]
        at success ⊢
      unfold evaluationAtomReducer combineAtomReducers
      rw [Source.MatcherTyping.reduceBuiltinAtom_constructor_miss]
      simp only [FuelResult.bind]
      simpa [reduceMatcherAtom, closedMultisetMatcherValue,
        clauseResultToAtomReduction] using
        congrArg (FuelResult.map clauseResultToAtomReduction) success)

theorem headConsOf_initialStep :
    ∀ values callbackFuel,
      stepMatchingState (evaluationAtomReducer (evalFuel callbackFuel))
        ⟨[⟨headConsPattern, closedMultisetMatcherValue,
          headConsTargetOf values⟩], [], []⟩ = .timeout ∨
      stepMatchingState (evaluationAtomReducer (evalFuel callbackFuel))
        ⟨[⟨headConsPattern, closedMultisetMatcherValue,
          headConsTargetOf values⟩], [], []⟩ =
          .ok (.expand (headConsSuccessorStatesOf values)) := by
  intro values callbackFuel
  rcases headConsOf_initialReduction values callbackFuel [] with
    timeout | success
  · exact .inl (by simp [stepMatchingState, timeout])
  · exact .inr (by
      simp [stepMatchingState, success, MatchingState.successors,
        MatchingState.continueWith, headConsBranchesOf,
        headConsSuccessorStatesOf])

theorem headConsSuccessorSearchOf :
    ∀ values callbackFuel fuel,
      depthFirstFuel
        (stepMatchingState (evaluationAtomReducer (evalFuel callbackFuel)))
        fuel (headConsSuccessorStatesOf values) = .timeout ∨
      depthFirstFuel
        (stepMatchingState (evaluationAtomReducer (evalFuel callbackFuel)))
        fuel (headConsSuccessorStatesOf values) =
          .ok (headConsAnswersOf values)
  | [], _, _ => .inr (by
      simp [headConsSuccessorStatesOf, headConsAnswersOf])
  | _ :: _, _, 0 => .inl rfl
  | value :: values, callbackFuel, 1 => .inl (by
      simp [headConsSuccessorStatesOf, depthFirstFuel, stepMatchingState,
        evaluationAtomReducer, combineAtomReducers, reduceBuiltinAtom,
        MatchingState.successors, MatchingState.continueWith])
  | value :: values, callbackFuel, fuel + 2 => by
      rcases headConsSuccessorSearchOf values callbackFuel fuel with
        timeout | success
      · exact .inl (by
          simp [headConsSuccessorStatesOf, depthFirstFuel, stepMatchingState,
            evaluationAtomReducer, combineAtomReducers, reduceBuiltinAtom,
            MatchingState.successors, MatchingState.continueWith]
          change FuelResult.map (fun answers => [value] :: answers)
            (depthFirstFuel
              (stepMatchingState
                (evaluationAtomReducer (evalFuel callbackFuel))) fuel
              (headConsSuccessorStatesOf values)) = .timeout
          rw [timeout]
          rfl)
      · exact .inr (by
          simp [headConsSuccessorStatesOf, headConsAnswersOf,
            depthFirstFuel, stepMatchingState, evaluationAtomReducer,
            combineAtomReducers, reduceBuiltinAtom, MatchingState.successors,
            MatchingState.continueWith]
          change FuelResult.map (fun answers => [value] :: answers)
            (depthFirstFuel
              (stepMatchingState
                (evaluationAtomReducer (evalFuel callbackFuel))) fuel
              (headConsSuccessorStatesOf values)) =
                .ok ([value] :: headConsAnswersOf values)
          rw [success]
          rfl)

theorem headConsOf_search :
    ∀ values callbackFuel searchFuel,
      searchPatternFuel (evalFuel callbackFuel) searchFuel [] headConsPattern
        closedMultisetMatcherValue (headConsTargetOf values) = .timeout ∨
      searchPatternFuel (evalFuel callbackFuel) searchFuel [] headConsPattern
        closedMultisetMatcherValue (headConsTargetOf values) =
          .ok (headConsAnswersOf values) := by
  intro values callbackFuel searchFuel
  rcases headConsOf_initialStep values callbackFuel with
    stepTimeout | stepSuccess
  · cases searchFuel with
    | zero => exact .inl rfl
    | succ fuel => exact .inl (by
        unfold searchPatternFuel searchMatchingFuel
        simp only [depthFirstFuel, stepTimeout, FuelResult.bind])
  · cases searchFuel with
    | zero => exact .inl rfl
    | succ fuel =>
      rcases headConsSuccessorSearchOf values callbackFuel fuel with
        timeout | success
      · exact .inl (by
          unfold searchPatternFuel searchMatchingFuel
          simp only [depthFirstFuel, stepSuccess, FuelResult.bind]
          simpa using timeout)
      · exact .inr (by
          unfold searchPatternFuel searchMatchingFuel
          simp only [depthFirstFuel, stepSuccess, FuelResult.bind]
          simpa using success)

@[simp] theorem headConsAnswersOf_eq_nil_iff :
    headConsAnswersOf values = [] ↔ values = [] := by
  simp [headConsAnswersOf]

/-- For a nonempty target list, every completed search has at least one
binding group.  Fuel exhaustion remains `timeout`; it cannot be confused with
an empty successful result. -/
theorem headConsOf_completedSearch_nonempty
    (targetNonempty : values ≠ [])
    (success : searchPatternFuel (evalFuel callbackFuel) searchFuel []
      headConsPattern closedMultisetMatcherValue (headConsTargetOf values) =
        .ok answers) :
    answers ≠ [] := by
  rcases headConsOf_search values callbackFuel searchFuel with timeout | exact
  · rw [success] at timeout
    contradiction
  · rw [success] at exact
    cases exact
    simpa using targetNonempty

theorem headConsAnswersOf_totalPlainTyping
    (typed : TotalPlainListValueTypings values element) :
    TotalPlainMatchingAnswersTyping (headConsAnswersOf values) [element] := by
  induction values with
  | nil => simp [headConsAnswersOf, TotalPlainMatchingAnswersTyping]
  | cons value values induction =>
      cases typed with
      | cons head tail =>
          intro bindings member
          simp only [headConsAnswersOf, List.map_cons, List.mem_cons] at member
          rcases member with rfl | member
          · exact .cons head .nil
          · exact (induction tail) bindings member

theorem headConsBranchesOf_delegatedTyping
    (typed : ∀ value ∈ values, ValueTyping value element) :
    DelegatedMatchingBranchesTyping [⟨.any, element⟩]
      (headConsBranchesOf values) := by
  induction values with
  | nil => exact .nil
  | cons value values induction =>
      have headTyped : ValueTyping value element := typed value (by simp)
      have tailTyped : ∀ candidate ∈ values,
          ValueTyping candidate element := by
        intro candidate member
        exact typed candidate (by simp [member])
      exact .cons
        (.cons
          (.checked (.something element) (.matcherToSlot .equal))
          headTyped .nil)
        (induction tailTyped)

theorem headConsBranchesOf_patternIndexedTyping
    (typed : ∀ value ∈ values, ValueTyping value element) :
    Source.MatcherTyping.PatternIndexedDelegatedMatchingBranchesTyping
      [.var] [⟨.any, element⟩] (headConsBranchesOf values) := by
  induction values with
  | nil => exact .nil
  | cons value values induction =>
      have headTyped : ValueTyping value element := typed value (by simp)
      have tailTyped : ∀ candidate ∈ values,
          ValueTyping candidate element := by
        intro candidate member
        exact typed candidate (by simp [member])
      exact .cons
        (.cons
          (.checked (.something element) (.matcherToSlot .equal))
          headTyped .nil)
        (induction tailTyped)

private theorem headConsBranch_recursiveTyping
    (typed : ∀ value ∈ values, ValueTyping value element)
    (member : branch ∈ headConsBranchesOf values) :
    RecursiveTotalMatchingAtomsTyping expressionTyping (evalFuel callbackFuel)
      environmentTypes bindingTypes branch [element] := by
  simp only [headConsBranchesOf, List.mem_map] at member
  rcases member with ⟨value, valueMember, rfl⟩
  exact .cons (.builtin (.somethingVar (typed value valueMember))) .nil

theorem headConsOf_patternIndexedRecursiveDispatchTyping
    (typed : ∀ value ∈ values, ValueTyping value element) :
    ∀ atomEnvironment,
      PatternIndexedRecursiveDispatchTyping expressionTyping
        (evalFuel callbackFuel) environmentTypes bindingTypes [element]
        (dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
          closedMultisetMatcherEnvironment multisetClauses headConsPattern
          (headConsTargetOf values)) := by
  intro atomEnvironment
  rcases headConsOf_dispatch values callbackFuel atomEnvironment with
    timeout | success
  · rw [timeout]
    exact .timeout
  · rw [success]
    exact .hit (patterns := [.var]) (by
      intro branch member
      simp only [headConsBranchesOf, List.mem_map] at member
      rcases member with ⟨value, _, rfl⟩
      rfl) (by
      intro branch member
      exact headConsBranch_recursiveTyping typed member)

/-- The generalized concrete dispatch is accepted by the callback-indexed
recursive reducer without an `EnvironmentTyping` proof for the recursive
matcher closure. -/
theorem headConsOf_recursiveAtomTyping
    (typed : ∀ value ∈ values, ValueTyping value element) :
    RecursiveTotalMatchingAtomTyping expressionTyping (evalFuel callbackFuel)
      environmentTypes bindingTypes
      ⟨headConsPattern, closedMultisetMatcherValue,
        headConsTargetOf values⟩ [element] := by
  apply RecursiveTotalMatchingAtomTyping.patternIndexedUser
  · intro atomEnvironment
    simp [headConsPattern, reduceBuiltinAtom]
  · intro atomEnvironment _
    exact headConsOf_patternIndexedRecursiveDispatchTyping typed
      atomEnvironment

theorem headConsOf_dispatch_preserves_source_pattern :
    Source.MatcherTyping.M4Paper1ListJoinSearchSafety.ConcreteDispatchPreservesPatterns
      (headConsBranchesOf values) [.var] := by
  intro branch member
  simp only [headConsBranchesOf, List.mem_map] at member
  rcases member with ⟨value, _, rfl⟩
  rfl

/-- Direct all-fuel safety for the actual seven-clause matcher and every
canonical list.  No successful run at a chosen fuel and no fuel-monotonicity
lemma is used. -/
theorem headConsOf_concretePatternSearchSafe
    (typed : TotalPlainListValueTypings values element) :
    Source.MatcherTyping.M4Paper1ListJoinSearchSafety.ConcretePatternSearchSafe
      [] headConsPattern closedMultisetMatcherValue (headConsTargetOf values)
      [element] := by
  intro fuel
  rcases headConsOf_search values fuel fuel with timeout | success
  · exact .inl timeout
  · exact .inr ⟨headConsAnswersOf values, success,
      headConsAnswersOf_totalPlainTyping typed⟩

/-- One reusable certificate combining the actual M4-derived multiset body
with the general operational theorem.  The older delegated-atom layer uses
`ValueTyping`, while answer safety uses the more general
`TotalPlainValueTyping`; both element hypotheses are therefore explicit. -/
structure ActualHeadConsM4SearchCertificateOf
    (values : List Value) (element : Ty) : Prop where
  sourceBodies : ClosedMultisetConcreteBodyTyping
  target : TotalPlainValueTyping (headConsTargetOf values)
    (DataTypes.list element)
  dispatch : ∀ callbackFuel atomEnvironment,
    dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
      closedMultisetMatcherEnvironment multisetClauses headConsPattern
      (headConsTargetOf values) = .timeout ∨
    dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
      closedMultisetMatcherEnvironment multisetClauses headConsPattern
      (headConsTargetOf values) =
        .ok (.hit (headConsBranchesOf values))
  delegatedValues : DelegatedMatchingBranchesTyping [⟨.any, element⟩]
    (headConsBranchesOf values)
  sourcePattern :
    Source.MatcherTyping.M4Paper1ListJoinSearchSafety.ConcreteDispatchPreservesPatterns
      (headConsBranchesOf values) [.var]
  search :
    Source.MatcherTyping.M4Paper1ListJoinSearchSafety.ConcretePatternSearchSafe
      [] headConsPattern closedMultisetMatcherValue (headConsTargetOf values)
      [element]

theorem actualHeadConsM4SearchCertificateOf
    (plainTyped : TotalPlainListValueTypings values element)
    (delegatedTyped : ∀ value ∈ values, ValueTyping value element) :
    ActualHeadConsM4SearchCertificateOf values element :=
  ⟨closedMultiset_concreteBodyTyping,
    .list plainTyped,
    headConsOf_dispatch values,
    headConsBranchesOf_delegatedTyping delegatedTyped,
    headConsOf_dispatch_preserves_source_pattern,
    headConsOf_concretePatternSearchSafe plainTyped⟩

end TypePM.ValueIndexedPaper1MultisetHeadConsGeneralSafety
