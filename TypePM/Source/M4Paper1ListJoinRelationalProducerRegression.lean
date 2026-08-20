import TypePM.Source.M4EnvironmentIndexedRelationalProducer
import TypePM.Source.M4Paper1ListJoinEnvironmentIndexedSearchRegression

/-!
# Relational producer for the actual inner List join

This regression replaces the explicit finite transition tree used by
`M4Paper1ListJoinEnvironmentIndexedSearchRegression` with the generic
relation-parametric producer.  Its fixture-specific atom relation has exactly
three cases: the initial List join atom, a delegated List variable atom, and
the final built-in `something` variable atom.

The local operational seed is unchanged and deliberately narrow.  Callback
fuels 0 through 12 are classified by direct timeout computations, callback
fuel 13 by the exact local join dispatch, and larger callback fuels by reducer
approximation.  Delegated and primitive variable steps use their corresponding
local exact reducer lemmas.  No complete-search equation, desired answer list,
`ConcretePatternSearchSafe`, or `EnvironmentIndexedFiniteMatchingStateTyping`
is used.

This is still a fixture-specific relation and local law, rather than an
automatically generated M4 derivation.  In particular, the existing M4
fuel-indexed `user` constructor retains old `EnvironmentTyping`; replacing
these three constructors by general M4-produced relational evidence requires
a relational dispatcher/evaluator preservation theorem for recursive-closure
environment invariants.
-/

namespace TypePM.Source.MatcherTyping.M4Paper1ListJoinRelationalProducerRegression

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open TypePM.StepIndexedPaper1ListSafetyRegression
open TypePM.ValueIndexedPaper1ListClauseBodySafety
open M4Paper1ListJoinSearchSafety
open M4Paper1ListJoinEnvironmentIndexedSearchRegression

/-- The minimal atom relation reached by the actual inner join.  The fuel
parameter is structural: each constructor is available at every positive
state index, while recursive work controls strict predecessor use. -/
inductive ActualInnerJoinAtomRelation (callbackFuel : Nat) :
    FuelIndexedMatchingAtomRelation where
  | initial {fuel : Nat} :
      ActualInnerJoinAtomRelation callbackFuel (fuel + 1)
        actualJoinConsContext [] innerJoinAtom [listType, listType]
  | delegated {fuel : Nat} {bindingTypes : List Ty} {target : Value}
      (enough : 2 ≤ callbackFuel)
      (targetTyped : ValueTyping target listType) :
      ActualInnerJoinAtomRelation callbackFuel (fuel + 1)
        actualJoinConsContext bindingTypes (delegatedVarAtom target) [listType]
  | primitive {fuel : Nat} {bindingTypes : List Ty} {target : Value}
      (targetTyped : ValueTyping target listType) :
      ActualInnerJoinAtomRelation callbackFuel (fuel + 1)
        actualJoinConsContext bindingTypes (primitiveVarAtom target) [listType]

/-- The actual three-atom relation is independent of the numeric fuel beyond
positivity, hence it satisfies the generic downward-closure requirement. -/
theorem actualInnerJoinAtomRelation_downwardClosed (callbackFuel : Nat) :
    FuelIndexedMatchingAtomRelation.DownwardClosed
      (ActualInnerJoinAtomRelation callbackFuel) := by
  intro fuel environmentTypes bindingTypes atom newBindings typed
  cases typed with
  | initial => exact .initial
  | delegated enough targetTyped => exact .delegated enough targetTyped
  | primitive targetTyped => exact .primitive targetTyped

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

private theorem primitiveVar_relationalWork
    (callbackFuel fuel : Nat) (bindingTypes : List Ty)
    (targetTyped : ValueTyping target listType) :
    RelationalFuelIndexedMatchingAtomsTyping
      (ActualInnerJoinAtomRelation callbackFuel) fuel actualJoinConsContext
      bindingTypes [primitiveVarAtom target] [listType] := by
  cases fuel with
  | zero => exact .zero (by simp)
  | succ fuel =>
      simpa using
        (RelationalFuelIndexedMatchingAtomsTyping.cons
          (ActualInnerJoinAtomRelation.primitive targetTyped)
          (RelationalFuelIndexedMatchingAtomsTyping.nil
            (fuel := fuel)
            (bindingTypes := bindingTypes ++ [listType])))

private theorem delegatedVar_relationalWork
    (callbackFuel fuel : Nat) (enough : 2 ≤ callbackFuel)
    (bindingTypes : List Ty) (targetTyped : ValueTyping target listType) :
    RelationalFuelIndexedMatchingAtomsTyping
      (ActualInnerJoinAtomRelation callbackFuel) fuel actualJoinConsContext
      bindingTypes [delegatedVarAtom target] [listType] := by
  cases fuel with
  | zero => exact .zero (by simp)
  | succ fuel =>
      simpa using
        (RelationalFuelIndexedMatchingAtomsTyping.cons
          (ActualInnerJoinAtomRelation.delegated enough targetTyped)
          (RelationalFuelIndexedMatchingAtomsTyping.nil
            (fuel := fuel)
            (bindingTypes := bindingTypes ++ [listType])))

private theorem delegatedVarPair_relationalWork
    (callbackFuel fuel : Nat) (enough : 2 ≤ callbackFuel)
    (bindingTypes : List Ty)
    (firstTyped : ValueTyping first listType)
    (secondTyped : ValueTyping second listType) :
    RelationalFuelIndexedMatchingAtomsTyping
      (ActualInnerJoinAtomRelation callbackFuel) fuel actualJoinConsContext
      bindingTypes [delegatedVarAtom first, delegatedVarAtom second]
      [listType, listType] := by
  have firstWork := delegatedVar_relationalWork callbackFuel fuel enough
    bindingTypes firstTyped
  have secondWork := delegatedVar_relationalWork callbackFuel fuel enough
    (bindingTypes ++ [listType]) secondTyped
  simpa using
    (RelationalFuelIndexedMatchingAtomsTyping.append
      (actualInnerJoinAtomRelation_downwardClosed callbackFuel) fuel
      firstWork secondWork)

/-- Initial relational work for every DFS bound.  Index zero is the
noninspection timeout case; a positive index exposes exactly the initial atom
and leaves an empty tail at the predecessor. -/
theorem innerJoin_relationalWork_allCallbacks
    (callbackFuel searchFuel : Nat) :
    RelationalFuelIndexedMatchingAtomsTyping
      (ActualInnerJoinAtomRelation callbackFuel) searchFuel
      actualJoinConsContext [] [innerJoinAtom] [listType, listType] := by
  cases searchFuel with
  | zero => exact .zero (by simp)
  | succ searchFuel =>
      simpa using
        (RelationalFuelIndexedMatchingAtomsTyping.cons
          (ActualInnerJoinAtomRelation.initial (callbackFuel := callbackFuel))
          (RelationalFuelIndexedMatchingAtomsTyping.nil
            (fuel := searchFuel)
            (bindingTypes := [listType, listType])))

/-- Fixture-specific local reducer preservation for the three reachable atom
forms.  Successful reductions return only predecessor-indexed relational
branch work; they do not contain environment-indexed states or search output. -/
theorem actualInnerJoin_relationalAtomReducerTypedSafe (callbackFuel : Nat) :
    EnvironmentIndexedRelationalAtomReducerTypedSafe
      (actualJoinEnvironmentInvariant callbackFuel)
      (ActualInnerJoinAtomRelation callbackFuel)
      (evaluationAtomReducer (evalFuel callbackFuel)) := by
  intro fuel environmentTypes bindingTypes environment bindings atom
    newBindings environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | initial =>
      cases bindingsTyped
      rcases environmentTyped with ⟨rfl, _, _⟩
      by_cases enough : 13 ≤ callbackFuel
      · refine .inr ⟨⟨list23JoinBranches, []⟩,
          innerJoin_reducer_exact_of_13_le enough, ?_⟩
        apply RelationalFuelIndexedAtomReductionTyping.intro [] .nil
        intro branch member
        simp only [list23JoinBranches, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ⟨[listType, listType],
            delegatedVarPair_relationalWork callbackFuel fuel (by omega) []
              nil_typed list23_typed,
            rfl⟩
        · exact ⟨[listType, listType],
            delegatedVarPair_relationalWork callbackFuel fuel (by omega) []
              list2_typed list3_typed,
            rfl⟩
        · exact ⟨[listType, listType],
            delegatedVarPair_relationalWork callbackFuel fuel (by omega) []
              list23_typed nil_typed,
            rfl⟩
      · exact .inl
          (innerJoin_reducer_timeout_of_lt_13 callbackFuel (by omega))
  | delegated enough targetTyped =>
      rename_i target
      have environmentEq := environmentTyped.1
      subst environment
      refine .inr ⟨⟨[[primitiveVarAtom target]], []⟩,
        delegatedVar_reducer_exact_of_two_le enough
          (bindings ++ actualJoinConsEnvironment) target, ?_⟩
      apply RelationalFuelIndexedAtomReductionTyping.intro [] .nil
      intro branch member
      simp only [List.mem_singleton] at member
      subst branch
      refine ⟨[listType], ?_, rfl⟩
      simpa using
        (primitiveVar_relationalWork callbackFuel fuel bindingTypes targetTyped)
  | primitive targetTyped =>
      rename_i target
      have environmentEq := environmentTyped.1
      subst environment
      refine .inr ⟨⟨[[]], [target]⟩,
        primitiveVar_reducer_exact callbackFuel
          (bindings ++ actualJoinConsEnvironment) target, ?_⟩
      apply RelationalFuelIndexedAtomReductionTyping.intro [listType]
        (.cons targetTyped .nil)
      intro branch member
      simp only [List.mem_singleton] at member
      subst branch
      exact ⟨[], .nil, by simp⟩

/-- Actual inner List-join search safety for arbitrary, independently chosen
callback and DFS fuels, produced compositionally from the relational work and
local reducer law. -/
theorem innerJoin_search_relationalTypedSafe_allCallbacks
    (callbackFuel searchFuel : Nat) :
    TypedMatchingSearchResult [listType, listType]
      (searchPatternFuel (evalFuel callbackFuel) searchFuel
        actualJoinConsEnvironment
        TotalPlainClosureSafetyRegression.listJoinPattern
        listMatcherSomethingValue list23Value) := by
  exact searchPatternFuel_environmentIndexedRelationalTypedSafe
    (atomRelation := ActualInnerJoinAtomRelation callbackFuel)
    (environmentInvariant := actualJoinEnvironmentInvariant callbackFuel)
    (actualInnerJoinAtomRelation_downwardClosed callbackFuel)
    (actualInnerJoin_relationalAtomReducerTypedSafe callbackFuel)
    (actualJoinEnvironmentInvariant_holds callbackFuel)
    (innerJoin_relationalWork_allCallbacks callbackFuel searchFuel)

/-- Value-indexed search premise for the actual inner `matchAll`, now produced
from relational local preservation rather than a finite transition tree. -/
theorem innerJoin_evaluatedPatternSearchSafe_relationalProducer (fuel : Nat) :
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
      rcases innerJoin_search_relationalTypedSafe_allCallbacks fuel fuel with
        timeout | ⟨answers, success, answersTyped⟩
      · exact .inl timeout
      · exact .inr ⟨answers, success, by
          intro answer member
          exact TotalPlainValueTypings.ofTotal
            (TotalValueTypings.ofValueTypings
              (answersTyped answer member))⟩

/-- The actual inner `matchAll` result is fuel-safe through the relational
producer. -/
theorem actualListSplitTailResults_relationalProducer_fuelResultSafe
    (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel (fuel + 1) actualJoinConsEnvironment
        listSplitTailResults) := by
  exact matchAllFuel_valueIndexedSafe
    (actualTail_evaluation_fuelSafe fuel)
    (actualSelfApplication_evaluation_fuelSafe fuel)
    (innerJoin_evaluatedPatternSearchSafe_relationalProducer fuel)
    (actualInnerJoinTupleBody_fuelSafe fuel)

/-- Pair-shaped postcondition used by the shared full-arm continuation. -/
theorem actualListSplitTailResults_relationalProducer_pairSafe (fuel : Nat) :
    ListResultSafeWith
      (PairValueSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int))
      (evalFuel (fuel + 1) actualJoinConsEnvironment
        listSplitTailResults) := by
  exact matchAllFuel_valueIndexedListSafeWith
    (actualTail_evaluation_fuelSafe fuel)
    (actualSelfApplication_evaluation_fuelSafe fuel)
    (innerJoin_evaluatedPatternSearchSafe_relationalProducer fuel)
    (actualInnerJoinTupleBody_pairSafe fuel)

theorem actualListSplitTailResults_relationalProducer_pairSafe_all :
    ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel actualJoinConsEnvironment listSplitTailResults)
  | 0 => .inl rfl
  | fuel + 1 =>
      actualListSplitTailResults_relationalProducer_pairSafe fuel

/-- Full selected `cons` body postcondition obtained by instantiating the
public continuation theorem with the relationally produced inner result. -/
theorem actualListJoinConsBody_relationalProducer_listPairSafe :
    ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) :=
  actualListJoinConsBody_listPairSafe_of_splitTailResults
    actualListSplitTailResults_relationalProducer_pairSafe_all

theorem actualListJoinConsBody_relationalProducer_fuelResultSafe
    (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) := by
  have stable : AllFuelListResultSafe innerJoinBodyTarget
      (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) :=
    ListResultSafeWith.mono
      (actualListJoinConsBody_relationalProducer_listPairSafe fuel)
      (fun _ safe => listPairPost_toAllFuelValueSafe safe)
  exact stable.toAllFuelResultSafe.toFuelResultSafe fuel

theorem actualListJoinConsBody_relationalProducer_neverStuck (fuel : Nat) :
    (evalFuel fuel actualJoinConsEnvironment listJoinConsBody).NotStuck :=
  (actualListJoinConsBody_relationalProducer_fuelResultSafe fuel).notStuck

theorem actualListSplitTailResults_relationalProducer_neverStuck
    (fuel : Nat) :
    (evalFuel fuel actualJoinConsEnvironment listSplitTailResults).NotStuck := by
  cases fuel with
  | zero => simp [evalFuel, FuelResult.NotStuck]
  | succ fuel =>
      exact
        (actualListSplitTailResults_relationalProducer_fuelResultSafe fuel).notStuck

end TypePM.Source.MatcherTyping.M4Paper1ListJoinRelationalProducerRegression
