import TypePM.ValueIndexedPaper1MultisetTopLevelSafety

/-!
# M4-indexed safety of the Paper 1 multiset head-cons clause

This module gives an all-fuel proof for the actual `$ :: _` clause of the
seven-clause Paper 1 multiset matcher.  Unlike the larger concrete regressions,
the proof does not start from one successful search at a fixed fuel.
-/

namespace TypePM.ValueIndexedPaper1MultisetHeadConsSafety

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open Source.MatcherTyping.M4Paper1RecursiveClosureTotalTyping

def headConsPattern : Pattern :=
  .ctor PatternCtor.cons [.var, .wild]

def headConsTarget : Value :=
  Value.buildList [.int 1, .int 2, .int 3]

def headConsBranches : MatchingBranches :=
  [ [⟨.var, .something, .int 1⟩],
    [⟨.var, .something, .int 2⟩],
    [⟨.var, .something, .int 3⟩] ]

def headConsAnswers : List (List Value) :=
  [[.int 1], [.int 2], [.int 3]]

/-- Reusable ordered-dispatch rule for a statically selected two-clause
prefix.  It does not assume anything about the unvisited tail. -/
theorem dispatch_of_firstMiss_secondHitOrTimeout
    (firstMiss : tryMatcherClause eval atomEnvironment matcherEnvironment
      pattern target firstClause = .ok .miss)
    (second : tryMatcherClause eval atomEnvironment matcherEnvironment
        pattern target secondClause = .timeout ∨
      tryMatcherClause eval atomEnvironment matcherEnvironment
        pattern target secondClause = .ok (.hit branches)) :
    dispatchMatcherClauses eval atomEnvironment matcherEnvironment
        (firstClause :: secondClause :: remaining) pattern target = .timeout ∨
      dispatchMatcherClauses eval atomEnvironment matcherEnvironment
        (firstClause :: secondClause :: remaining) pattern target =
          .ok (.hit branches) := by
  rcases second with timeout | success
  · exact .inl (by
      simp [dispatchMatcherClauses, firstHit, firstMiss, timeout])
  · exact .inr (by
      simp [dispatchMatcherClauses, firstHit, firstMiss, success])

theorem nilClause_headCons_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      headConsPattern headConsTarget nilClause = .ok .miss := by
  rfl

theorem headOnlyClause_headCons_try :
    ∀ fuel atomEnvironment,
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment headConsPattern headConsTarget
        headOnlyClause = .timeout ∨
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment headConsPattern headConsTarget
        headOnlyClause = .ok (.hit headConsBranches)
  | 0, _ => .inl rfl
  | _ + 1, _ => .inr (by with_unfolding_all rfl)

theorem headCons_dispatch :
    ∀ fuel atomEnvironment,
      dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses headConsPattern
        headConsTarget = .timeout ∨
      dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses headConsPattern
        headConsTarget = .ok (.hit headConsBranches) := by
  intro fuel atomEnvironment
  simpa [multisetClauses] using
    (dispatch_of_firstMiss_secondHitOrTimeout
      (nilClause_headCons_miss fuel atomEnvironment
        closedMultisetMatcherEnvironment)
      (headOnlyClause_headCons_try fuel atomEnvironment)
      (remaining := [valueConsClause, generalConsClause, joinClause,
        wholeValueClause, catchAllClause]))

theorem headCons_initialReduction :
    ∀ callbackFuel atomEnvironment,
      evaluationAtomReducer (evalFuel callbackFuel) atomEnvironment
        ⟨headConsPattern, closedMultisetMatcherValue, headConsTarget⟩ =
          .timeout ∨
      evaluationAtomReducer (evalFuel callbackFuel) atomEnvironment
        ⟨headConsPattern, closedMultisetMatcherValue, headConsTarget⟩ =
          .ok (.hit ⟨headConsBranches, []⟩) := by
  intro callbackFuel atomEnvironment
  rcases headCons_dispatch callbackFuel atomEnvironment with timeout | success
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

def headConsSuccessorStates : List MatchingState :=
  [ ⟨[⟨.var, .something, .int 1⟩], [], []⟩,
    ⟨[⟨.var, .something, .int 2⟩], [], []⟩,
    ⟨[⟨.var, .something, .int 3⟩], [], []⟩ ]

theorem headCons_initialStep :
    ∀ callbackFuel,
      stepMatchingState (evaluationAtomReducer (evalFuel callbackFuel))
        ⟨[⟨headConsPattern, closedMultisetMatcherValue,
          headConsTarget⟩], [], []⟩ = .timeout ∨
      stepMatchingState (evaluationAtomReducer (evalFuel callbackFuel))
        ⟨[⟨headConsPattern, closedMultisetMatcherValue,
          headConsTarget⟩], [], []⟩ =
          .ok (.expand headConsSuccessorStates) := by
  intro callbackFuel
  rcases headCons_initialReduction callbackFuel [] with timeout | success
  · exact .inl (by simp [stepMatchingState, timeout])
  · exact .inr (by
      simp [stepMatchingState, success, MatchingState.successors,
        MatchingState.continueWith, headConsBranches,
        headConsSuccessorStates])

theorem headConsSuccessorSearch :
    ∀ callbackFuel fuel,
      depthFirstFuel
        (stepMatchingState (evaluationAtomReducer (evalFuel callbackFuel)))
        fuel headConsSuccessorStates = .timeout ∨
      depthFirstFuel
        (stepMatchingState (evaluationAtomReducer (evalFuel callbackFuel)))
        fuel headConsSuccessorStates = .ok headConsAnswers
  | _, 0 => .inl rfl
  | _, 1 => .inl (by with_unfolding_all rfl)
  | _, 2 => .inl (by with_unfolding_all rfl)
  | _, 3 => .inl (by with_unfolding_all rfl)
  | _, 4 => .inl (by with_unfolding_all rfl)
  | _, 5 => .inl (by with_unfolding_all rfl)
  | _, fuel + 6 => .inr (by
      simp [headConsSuccessorStates, headConsAnswers, depthFirstFuel,
        stepMatchingState, evaluationAtomReducer, combineAtomReducers,
        reduceBuiltinAtom, reduceMatcherAtom,
        MatchingState.successors, MatchingState.continueWith])

theorem headCons_search :
    ∀ callbackFuel searchFuel,
      searchPatternFuel (evalFuel callbackFuel) searchFuel [] headConsPattern
        closedMultisetMatcherValue headConsTarget = .timeout ∨
      searchPatternFuel (evalFuel callbackFuel) searchFuel [] headConsPattern
        closedMultisetMatcherValue headConsTarget = .ok headConsAnswers := by
  intro callbackFuel searchFuel
  rcases headCons_initialStep callbackFuel with stepTimeout | stepSuccess
  · cases searchFuel with
    | zero => exact .inl rfl
    | succ fuel => exact .inl (by
        unfold searchPatternFuel searchMatchingFuel
        simp only [depthFirstFuel, stepTimeout, FuelResult.bind])
  · cases searchFuel with
    | zero => exact .inl rfl
    | succ fuel =>
      rcases headConsSuccessorSearch callbackFuel fuel with timeout | success
      · exact .inl (by
          unfold searchPatternFuel searchMatchingFuel
          simp only [depthFirstFuel, stepSuccess, FuelResult.bind]
          exact timeout)
      · exact .inr (by
          unfold searchPatternFuel searchMatchingFuel
          simp only [depthFirstFuel, stepSuccess, FuelResult.bind]
          exact success)

private theorem intList_totalPlainTyping (values : List Int) :
    TotalPlainValueTyping (Value.buildList (values.map Value.int))
      (DataTypes.list .int) := by
  apply TotalPlainValueTyping.list
  induction values with
  | nil => exact .nil
  | cons value values induction =>
      exact .cons (.existing (.ordinary (.int value))) induction

theorem headConsAnswers_totalPlainTyping :
    TotalPlainMatchingAnswersTyping headConsAnswers [.int] := by
  intro answer member
  simp only [headConsAnswers, List.mem_cons] at member
  rcases member with rfl | member
  · exact .cons (.existing (.ordinary (.int 1))) .nil
  · rcases member with rfl | member
    · exact .cons (.existing (.ordinary (.int 2))) .nil
    · rcases member with rfl | member
      · exact .cons (.existing (.ordinary (.int 3))) .nil
      · simp at member

theorem headConsBranches_delegatedTyping :
    DelegatedMatchingBranchesTyping [⟨.any, .int⟩] headConsBranches := by
  have matcherTyped : ValueTyping .something (.slot .any .int) :=
    .checked (.something .int) (.matcherToSlot .equal)
  exact .cons
    (.cons matcherTyped (.int 1) .nil)
    (.cons (.cons matcherTyped (.int 2) .nil)
      (.cons (.cons matcherTyped (.int 3) .nil) .nil))

theorem headCons_dispatch_preserves_source_pattern :
    Source.MatcherTyping.M4Paper1ListJoinSearchSafety.ConcreteDispatchPreservesPatterns
      headConsBranches [.var] := by
  intro branch member
  simp [headConsBranches] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- No fixed successful run seeds this proof: each callback/search fuel is
analyzed directly, and every completed search result is typed. -/
theorem headCons_concretePatternSearchSafe :
    Source.MatcherTyping.M4Paper1ListJoinSearchSafety.ConcretePatternSearchSafe
      [] headConsPattern closedMultisetMatcherValue headConsTarget
      [.int] := by
  intro callbackFuel
  rcases headCons_search callbackFuel callbackFuel with timeout | success
  · exact .inl timeout
  · exact .inr ⟨headConsAnswers, success,
      headConsAnswers_totalPlainTyping⟩

/-- The static side is the premise-free body certificate extracted from the
public closed-multiset principal derivation.  The dynamic side is the
all-fuel search proof above, indexed by the actual matcher and target values.
-/
structure ActualHeadConsM4SearchCertificate : Prop where
  sourceBodies : ClosedMultisetConcreteBodyTyping
  target : TotalPlainValueTyping headConsTarget (DataTypes.list .int)
  dispatch : ∀ callbackFuel atomEnvironment,
    dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
      closedMultisetMatcherEnvironment multisetClauses headConsPattern
      headConsTarget = .timeout ∨
    dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
      closedMultisetMatcherEnvironment multisetClauses headConsPattern
      headConsTarget = .ok (.hit headConsBranches)
  delegatedValues : DelegatedMatchingBranchesTyping [⟨.any, .int⟩]
    headConsBranches
  sourcePattern :
    Source.MatcherTyping.M4Paper1ListJoinSearchSafety.ConcreteDispatchPreservesPatterns
      headConsBranches [.var]
  search :
    Source.MatcherTyping.M4Paper1ListJoinSearchSafety.ConcretePatternSearchSafe
      [] headConsPattern closedMultisetMatcherValue headConsTarget
      [.int]

theorem actualHeadConsM4SearchCertificate :
    ActualHeadConsM4SearchCertificate :=
  ⟨closedMultiset_concreteBodyTyping,
    by simpa [headConsTarget] using intList_totalPlainTyping [1, 2, 3],
    headCons_dispatch,
    headConsBranches_delegatedTyping,
    headCons_dispatch_preserves_source_pattern,
    headCons_concretePatternSearchSafe⟩

end TypePM.ValueIndexedPaper1MultisetHeadConsSafety
