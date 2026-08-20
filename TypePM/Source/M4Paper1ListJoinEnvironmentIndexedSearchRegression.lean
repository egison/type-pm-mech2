import TypePM.Source.M4EnvironmentIndexedRecursiveSearchBridge
import TypePM.ValueIndexedPaper1ListClauseBodySafety

/-!
# Environment-indexed search for the actual inner List join

The selected Paper 1 List `cons` arm evaluates its recursive inner `matchAll`
in `actualJoinConsEnvironment`.  Its final entry is the real recursive List
closure, so the old `EnvironmentTyping` judgment cannot classify this state.

This regression uses the parallel environment-indexed search layer.  Direct
computations classify callback fuels 0 through 12 as timeouts and callback
fuel 13 as a local hit; callback monotonicity preserves that hit above 13.
The resulting finite transition tree then supplies every DFS bound.  It does
not use `list23Join_search_exact`, `ConcretePatternSearchSafe`, or any equation
for the complete search.

The transition tree is deliberately a fixture-specific operational
certificate.  It is not claimed to be generated automatically from an M4
derivation; that general producer bridge remains a separate boundary.
-/

namespace TypePM.Source.MatcherTyping.M4Paper1ListJoinEnvironmentIndexedSearchRegression

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open TypePM.StepIndexedPaper1ListSafetyRegression
open TypePM.ValueIndexedPaper1ListClauseBodySafety
open M4Paper1ListJoinSearchSafety

def listType : Ty := DataTypes.list .int

def actualJoinEnvironmentInvariant (callbackFuel : Nat) :
    MatchingEnvironmentInvariant :=
  fun environment context =>
    environment = actualJoinConsEnvironment ∧
      context = actualJoinConsContext ∧
      FuelEnvironmentSafe callbackFuel environment context

theorem actualJoinEnvironmentInvariant_holds (callbackFuel : Nat) :
    actualJoinEnvironmentInvariant callbackFuel actualJoinConsEnvironment
      actualJoinConsContext := by
  exact ⟨rfl, rfl, actualJoinConsEnvironment_fuelSafe callbackFuel⟩

def list23JoinBranches : MatchingBranches :=
  [ [⟨.var, listMatcherSomethingValue, Value.nilValue⟩,
      ⟨.var, listMatcherSomethingValue, list23Value⟩],
    [⟨.var, listMatcherSomethingValue, Value.buildList [.int 2]⟩,
      ⟨.var, listMatcherSomethingValue, Value.buildList [.int 3]⟩],
    [⟨.var, listMatcherSomethingValue, list23Value⟩,
      ⟨.var, listMatcherSomethingValue, Value.nilValue⟩] ]

def innerJoinAtom : MatchingAtom :=
  ⟨TotalPlainClosureSafetyRegression.listJoinPattern,
    listMatcherSomethingValue, list23Value⟩

def delegatedVarAtom (target : Value) : MatchingAtom :=
  ⟨.var, listMatcherSomethingValue, target⟩

def primitiveVarAtom (target : Value) : MatchingAtom :=
  ⟨.var, .something, target⟩

set_option maxRecDepth 100000 in
theorem innerJoin_reducer_exact_13 :
    evaluationAtomReducer (evalFuel 13) actualJoinConsEnvironment innerJoinAtom =
      .ok (.hit ⟨list23JoinBranches, []⟩) := by
  with_unfolding_all rfl

theorem innerJoin_reducer_approximates_succ (callbackFuel : Nat) :
    FuelResult.Approximates
      (evaluationAtomReducer (evalFuel callbackFuel)
        actualJoinConsEnvironment innerJoinAtom)
      (evaluationAtomReducer (evalFuel (callbackFuel + 1))
        actualJoinConsEnvironment innerJoinAtom) := by
  simpa [evaluationAtomReducer, combineAtomReducers, innerJoinAtom,
      reduceBuiltinAtom, reduceMatcherAtom, listMatcherSomethingValue,
      TotalPlainClosureSafetyRegression.listJoinPattern] using
    (FuelResult.Approximates.map
      (dispatchMatcherClauses_evalFuel_approximates_succ
        (fuel := callbackFuel)
        (atomEnvironment := actualJoinConsEnvironment)
        (matcherEnvironment := [.something,
          M4Paper1RecursiveSafetyBoundaryRegression.listRecursiveClosure])
        (clauses := listMatcherClauses)
        (pattern := TotalPlainClosureSafetyRegression.listJoinPattern)
        (target := list23Value))
      clauseResultToAtomReduction)

theorem innerJoin_reducer_approximates_add (callbackFuel extra : Nat) :
    FuelResult.Approximates
      (evaluationAtomReducer (evalFuel callbackFuel)
        actualJoinConsEnvironment innerJoinAtom)
      (evaluationAtomReducer (evalFuel (callbackFuel + extra))
        actualJoinConsEnvironment innerJoinAtom) := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      exact FuelResult.Approximates.refl _
  | succ extra induction =>
      rw [Nat.add_succ]
      exact induction.trans
        (innerJoin_reducer_approximates_succ (callbackFuel + extra))

theorem innerJoin_reducer_exact_from_13 (extra : Nat) :
    evaluationAtomReducer (evalFuel (13 + extra)) actualJoinConsEnvironment
        innerJoinAtom =
      .ok (.hit ⟨list23JoinBranches, []⟩) := by
  have related := innerJoin_reducer_approximates_add 13 extra
  rw [innerJoin_reducer_exact_13] at related
  exact related.ok_eq

theorem innerJoin_reducer_exact_of_13_le
    (enough : 13 ≤ callbackFuel) :
    evaluationAtomReducer (evalFuel callbackFuel) actualJoinConsEnvironment
        innerJoinAtom =
      .ok (.hit ⟨list23JoinBranches, []⟩) := by
  obtain ⟨extra, equality⟩ : ∃ extra, callbackFuel = 13 + extra := by
    exact ⟨callbackFuel - 13, by omega⟩
  subst callbackFuel
  exact innerJoin_reducer_exact_from_13 extra

theorem innerJoin_reducer_timeout_of_lt_13 : ∀ callbackFuel,
    callbackFuel < 13 →
      evaluationAtomReducer (evalFuel callbackFuel)
        actualJoinConsEnvironment innerJoinAtom = .timeout
  | 0, _ => by with_unfolding_all rfl
  | 1, _ => by with_unfolding_all rfl
  | 2, _ => by with_unfolding_all rfl
  | 3, _ => by with_unfolding_all rfl
  | 4, _ => by with_unfolding_all rfl
  | 5, _ => by with_unfolding_all rfl
  | 6, _ => by with_unfolding_all rfl
  | 7, _ => by with_unfolding_all rfl
  | 8, _ => by with_unfolding_all rfl
  | 9, _ => by with_unfolding_all rfl
  | 10, _ => by with_unfolding_all rfl
  | 11, _ => by with_unfolding_all rfl
  | 12, _ => by with_unfolding_all rfl
  | _ + 13, below => by omega

theorem catchAllBody_eval_exact_2 (target : Value) :
    evalFuel 2
      [target, .something,
        M4Paper1RecursiveSafetyBoundaryRegression.listRecursiveClosure]
      (sourceList [.var 0]) = .ok (Value.buildList [target]) := by
  rfl

theorem catchAllMatcher_eval_exact_2 :
    evalFuel 2
      [.something,
        M4Paper1RecursiveSafetyBoundaryRegression.listRecursiveClosure]
      .something = .ok .something := by
  rfl

set_option maxRecDepth 100000 in
theorem delegatedVar_reducer_exact_2 (atomEnvironment : ValueEnvironment)
    (target : Value) :
    evaluationAtomReducer (evalFuel 2) atomEnvironment
      (delegatedVarAtom target) =
        .ok (.hit ⟨[[primitiveVarAtom target]], []⟩) := by
  unfold evaluationAtomReducer combineAtomReducers
  simp only [delegatedVarAtom, listMatcherSomethingValue, reduceBuiltinAtom,
    FuelResult.bind]
  unfold reduceMatcherAtom
  simp only [FuelResult.map]
  simp [dispatchMatcherClauses, listMatcherClauses, firstHit,
    tryMatcherClause, listMatcherNilClause, listMatcherConsClause,
    listMatcherJoinClause, listMatcherCatchAllClause, nilClause,
    catchAllClause, inspectPatternPattern, FuelResult.traverse, tryMatcherArm,
    matchValueDataPattern, decodeDecompositions, decodeProduct,
    buildMatchingBranches, zipMatchingAtoms, closeMatcherArmsResult,
    clauseResultToAtomReduction, primitiveVarAtom, catchAllBody_eval_exact_2,
    catchAllMatcher_eval_exact_2]

theorem delegatedVar_reducer_approximates_succ (callbackFuel : Nat)
    (atomEnvironment : ValueEnvironment) (target : Value) :
    FuelResult.Approximates
      (evaluationAtomReducer (evalFuel callbackFuel) atomEnvironment
        (delegatedVarAtom target))
      (evaluationAtomReducer (evalFuel (callbackFuel + 1)) atomEnvironment
        (delegatedVarAtom target)) := by
  simpa [evaluationAtomReducer, combineAtomReducers, delegatedVarAtom,
      reduceBuiltinAtom, reduceMatcherAtom, listMatcherSomethingValue] using
    (FuelResult.Approximates.map
      (dispatchMatcherClauses_evalFuel_approximates_succ
        (fuel := callbackFuel) (atomEnvironment := atomEnvironment)
        (matcherEnvironment := [.something,
          M4Paper1RecursiveSafetyBoundaryRegression.listRecursiveClosure])
        (clauses := listMatcherClauses) (pattern := .var) (target := target))
      clauseResultToAtomReduction)

theorem delegatedVar_reducer_approximates_add (callbackFuel extra : Nat)
    (atomEnvironment : ValueEnvironment) (target : Value) :
    FuelResult.Approximates
      (evaluationAtomReducer (evalFuel callbackFuel) atomEnvironment
        (delegatedVarAtom target))
      (evaluationAtomReducer (evalFuel (callbackFuel + extra)) atomEnvironment
        (delegatedVarAtom target)) := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      exact FuelResult.Approximates.refl _
  | succ extra induction =>
      rw [Nat.add_succ]
      exact induction.trans
        (delegatedVar_reducer_approximates_succ (callbackFuel + extra)
          atomEnvironment target)

theorem delegatedVar_reducer_exact_from_2 (extra : Nat)
    (atomEnvironment : ValueEnvironment) (target : Value) :
    evaluationAtomReducer (evalFuel (2 + extra)) atomEnvironment
        (delegatedVarAtom target) =
      .ok (.hit ⟨[[primitiveVarAtom target]], []⟩) := by
  have related := delegatedVar_reducer_approximates_add 2 extra
    atomEnvironment target
  rw [delegatedVar_reducer_exact_2] at related
  exact related.ok_eq

theorem delegatedVar_reducer_exact_of_two_le
    (enough : 2 ≤ callbackFuel) (atomEnvironment : ValueEnvironment)
    (target : Value) :
    evaluationAtomReducer (evalFuel callbackFuel) atomEnvironment
        (delegatedVarAtom target) =
      .ok (.hit ⟨[[primitiveVarAtom target]], []⟩) := by
  obtain ⟨extra, equality⟩ : ∃ extra, callbackFuel = 2 + extra := by
    exact ⟨callbackFuel - 2, by omega⟩
  subst callbackFuel
  exact delegatedVar_reducer_exact_from_2 extra atomEnvironment target

theorem primitiveVar_reducer_exact (callbackFuel : Nat)
    (atomEnvironment : ValueEnvironment)
    (target : Value) :
    evaluationAtomReducer (evalFuel callbackFuel) atomEnvironment
      (primitiveVarAtom target) =
        .ok (.hit ⟨[[]], [target]⟩) := by
  rfl

private theorem intValues_typed : ∀ literals : List Int,
    ListValueTypings (literals.map Value.int) .int
  | [] => .nil
  | literal :: literals => .cons (.int literal) (intValues_typed literals)

private theorem intList_typed (literals : List Int) :
    ValueTyping (Value.buildList (literals.map Value.int)) listType := by
  exact .list (intValues_typed literals)

private theorem nil_typed : ValueTyping Value.nilValue listType := by
  simpa [listType, Value.nilValue, Value.buildList] using intList_typed []

private theorem list2_typed :
    ValueTyping (Value.buildList [.int 2]) listType := by
  simpa [listType] using intList_typed [2]

private theorem list3_typed :
    ValueTyping (Value.buildList [.int 3]) listType := by
  simpa [listType] using intList_typed [3]

private theorem list23_typed : ValueTyping list23Value listType := by
  simpa [listType, list23Value] using intList_typed [2, 3]

/-- One delegated variable atom takes exactly two local reducer steps: the
List catch-all delegates to `something`, and the built-in variable rule then
appends the target. -/
private theorem delegatedVar_then
    (callbackFuel : Nat) (enough : 2 ≤ callbackFuel)
    (environmentTyped : environmentInvariant environment environmentTypes)
    (bindingsTyped : ValueTypings bindings bindingTypes)
    (tailTyped : EnvironmentIndexedFiniteMatchingStateTyping
      environmentInvariant (evaluationAtomReducer (evalFuel callbackFuel))
      ⟨remaining, environment, bindings ++ [target]⟩ answerTypes) :
    EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
      (evaluationAtomReducer (evalFuel callbackFuel))
      ⟨delegatedVarAtom target :: remaining, environment, bindings⟩
      answerTypes := by
  apply EnvironmentIndexedFiniteMatchingStateTyping.hit environmentTyped
    bindingsTyped ⟨[[primitiveVarAtom target]], []⟩
    (delegatedVar_reducer_exact_of_two_le enough
      (bindings ++ environment) target)
  intro successor member
  simp only [MatchingState.successors, MatchingState.continueWith,
    List.map_singleton, List.mem_singleton] at member
  subst successor
  have primitiveStep : EnvironmentIndexedFiniteMatchingStateTyping
      environmentInvariant (evaluationAtomReducer (evalFuel callbackFuel))
      ⟨primitiveVarAtom target :: remaining, environment, bindings⟩
      answerTypes := by
    apply EnvironmentIndexedFiniteMatchingStateTyping.hit environmentTyped
      bindingsTyped ⟨[[]], [target]⟩
      (primitiveVar_reducer_exact callbackFuel (bindings ++ environment) target)
    intro successor member
    simp only [MatchingState.successors, MatchingState.continueWith,
      List.map_singleton, List.mem_singleton, List.nil_append] at member
    subst successor
    exact tailTyped
  simpa using primitiveStep

/-- A two-hole branch returned by the List join clause is certified only from
its two concrete delegated-variable reducer chains. -/
private theorem delegatedVarPair_finiteTyped
    (callbackFuel : Nat) (enough : 2 ≤ callbackFuel)
    (environmentTyped : environmentInvariant environment environmentTypes)
    (firstTyped : ValueTyping first listType)
    (secondTyped : ValueTyping second listType) :
    EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
      (evaluationAtomReducer (evalFuel callbackFuel))
      ⟨[delegatedVarAtom first, delegatedVarAtom second], environment, []⟩
      [listType, listType] := by
  have done : EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
      (evaluationAtomReducer (evalFuel callbackFuel))
      ⟨[], environment, [first, second]⟩ [listType, listType] :=
    .yield environmentTyped (.cons firstTyped (.cons secondTyped .nil))
  have second : EnvironmentIndexedFiniteMatchingStateTyping
      environmentInvariant (evaluationAtomReducer (evalFuel callbackFuel))
      ⟨[delegatedVarAtom second], environment, [first]⟩
      [listType, listType] := by
    apply delegatedVar_then callbackFuel enough environmentTyped
      (.cons firstTyped .nil)
    simpa using done
  apply delegatedVar_then callbackFuel enough environmentTyped .nil
  simpa using second

/-- The same finite local transition proof for every evaluator callback bound.
Below 13 the initial reducer itself times out; at and above 13 the one local
join dispatch is the stable three-branch hit and every delegated variable atom
is also a stable local hit. -/
theorem innerJoin_finiteStateTyped_allCallbacks (callbackFuel : Nat) :
    EnvironmentIndexedFiniteMatchingStateTyping
      (actualJoinEnvironmentInvariant callbackFuel)
      (evaluationAtomReducer (evalFuel callbackFuel))
      ⟨[innerJoinAtom], actualJoinConsEnvironment, []⟩
      [listType, listType] := by
  by_cases enough : 13 ≤ callbackFuel
  · apply EnvironmentIndexedFiniteMatchingStateTyping.hit
      (actualJoinEnvironmentInvariant_holds callbackFuel) .nil
      ⟨list23JoinBranches, []⟩
      (innerJoin_reducer_exact_of_13_le enough)
    intro successor member
    simp only [MatchingState.successors, MatchingState.continueWith,
      list23JoinBranches, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact delegatedVarPair_finiteTyped callbackFuel (by omega)
        (actualJoinEnvironmentInvariant_holds callbackFuel)
        nil_typed list23_typed
    · exact delegatedVarPair_finiteTyped callbackFuel (by omega)
        (actualJoinEnvironmentInvariant_holds callbackFuel)
        list2_typed list3_typed
    · exact delegatedVarPair_finiteTyped callbackFuel (by omega)
        (actualJoinEnvironmentInvariant_holds callbackFuel)
        list23_typed nil_typed
  · apply EnvironmentIndexedFiniteMatchingStateTyping.timeout
      (actualJoinEnvironmentInvariant_holds callbackFuel) .nil
    exact innerJoin_reducer_timeout_of_lt_13 callbackFuel (by omega)

/-- Actual P1-L01 inner List-join search safety for arbitrary, independently
chosen evaluator callback and DFS bounds.  The recursive closure remains in
`actualJoinConsEnvironment`; only accumulated first-order answers use the old
`ValueTypings` relation. -/
theorem innerJoin_search_environmentIndexedTypedSafe_allCallbacks
    (callbackFuel searchFuel : Nat) :
    TypedMatchingSearchResult [listType, listType]
      (searchPatternFuel (evalFuel callbackFuel) searchFuel
        actualJoinConsEnvironment
        TotalPlainClosureSafetyRegression.listJoinPattern
        listMatcherSomethingValue list23Value) := by
  apply searchPatternFuel_environmentIndexedTypedSafe
    (environmentInvariant := actualJoinEnvironmentInvariant callbackFuel)
  exact (innerJoin_finiteStateTyped_allCallbacks callbackFuel).toFuel searchFuel

/-- Search premise consumed by the value-indexed `matchAll` rule, now derived
from the environment-indexed local reducer tree.  Target and matcher expression
evaluation are used only to identify the two already evaluated concrete values;
the search itself does not use the old whole-search exact theorem. -/
theorem innerJoin_evaluatedPatternSearchSafe_environmentIndexed (fuel : Nat) :
    EvaluatedPatternSearchSafe fuel actualJoinConsEnvironment (.var 1)
      (.app (.var 3) (.var 2))
      TotalPlainClosureSafetyRegression.listJoinPattern
      innerJoinBindingTypes := by
  intro targetValue matcherValue targetSuccess matcherSuccess
  rcases actualTail_evaluation_shape fuel with targetTimeout | targetExact
  · rw [targetSuccess] at targetTimeout
    contradiction
  · have target_eq : targetValue = list23Value := by
      rw [targetSuccess] at targetExact
      exact FuelResult.ok.inj targetExact
    rcases actualSelfApplication_evaluation_shape fuel with matcherTimeout |
      matcherExact
    · rw [matcherSuccess] at matcherTimeout
      contradiction
    · have matcher_eq : matcherValue = listMatcherSomethingValue := by
        rw [matcherSuccess] at matcherExact
        exact FuelResult.ok.inj matcherExact
      subst targetValue
      subst matcherValue
      rcases innerJoin_search_environmentIndexedTypedSafe_allCallbacks fuel fuel with
        timeout | ⟨answers, success, answersTyped⟩
      · exact .inl timeout
      · exact .inr ⟨answers, success, by
          intro bindings member
          exact TotalPlainValueTypings.ofTotal
            (TotalValueTypings.ofValueTypings
              (answersTyped bindings member))⟩

/-- Actual recursive inner `matchAll` result safety without using
`list23Join_search_exact` or `ConcretePatternSearchSafe`. -/
theorem actualListSplitTailResults_environmentIndexed_fuelResultSafe
    (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel (fuel + 1) actualJoinConsEnvironment
        listSplitTailResults) := by
  exact matchAllFuel_valueIndexedSafe
    (actualTail_evaluation_fuelSafe fuel)
    (actualSelfApplication_evaluation_fuelSafe fuel)
    (innerJoin_evaluatedPatternSearchSafe_environmentIndexed fuel)
    (actualInnerJoinTupleBody_fuelSafe fuel)

/-- Pair-shaped postcondition for the actual recursive inner `matchAll`,
derived from the environment-indexed local transition certificate. -/
theorem actualListSplitTailResults_environmentIndexed_pairSafe (fuel : Nat) :
    ListResultSafeWith
      (PairValueSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int))
      (evalFuel (fuel + 1) actualJoinConsEnvironment
        listSplitTailResults) := by
  exact matchAllFuel_valueIndexedListSafeWith
    (actualTail_evaluation_fuelSafe fuel)
    (actualSelfApplication_evaluation_fuelSafe fuel)
    (innerJoin_evaluatedPatternSearchSafe_environmentIndexed fuel)
    (actualInnerJoinTupleBody_pairSafe fuel)

theorem actualListSplitTailResults_environmentIndexed_pairSafe_all :
    ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel actualJoinConsEnvironment listSplitTailResults)
  | 0 => .inl rfl
  | fuel + 1 =>
      actualListSplitTailResults_environmentIndexed_pairSafe fuel

/-- Full selected `cons` body safety obtained by passing the new inner-search
postcondition through the shared public `letE`/`map`/`append` continuation.
The operational seed remains the fixture-specific local dispatch tree. -/
theorem actualListJoinConsBody_environmentIndexed_listPairSafe :
    ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) :=
  actualListJoinConsBody_listPairSafe_of_splitTailResults
    actualListSplitTailResults_environmentIndexed_pairSafe_all

theorem actualListJoinConsBody_environmentIndexed_fuelResultSafe
    (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) := by
  have stable : AllFuelListResultSafe innerJoinBodyTarget
      (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) :=
    ListResultSafeWith.mono
      (actualListJoinConsBody_environmentIndexed_listPairSafe fuel)
      (fun _ safe => listPairPost_toAllFuelValueSafe safe)
  exact stable.toAllFuelResultSafe.toFuelResultSafe fuel

theorem actualListJoinConsBody_environmentIndexed_neverStuck (fuel : Nat) :
    (evalFuel fuel actualJoinConsEnvironment listJoinConsBody).NotStuck :=
  (actualListJoinConsBody_environmentIndexed_fuelResultSafe fuel).notStuck

theorem actualListSplitTailResults_environmentIndexed_neverStuck
    (fuel : Nat) :
    (evalFuel fuel actualJoinConsEnvironment listSplitTailResults).NotStuck := by
  cases fuel with
  | zero => simp [evalFuel, FuelResult.NotStuck]
  | succ fuel =>
      exact
        (actualListSplitTailResults_environmentIndexed_fuelResultSafe fuel).notStuck

end TypePM.Source.MatcherTyping.M4Paper1ListJoinEnvironmentIndexedSearchRegression
