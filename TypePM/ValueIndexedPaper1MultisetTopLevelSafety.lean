import TypePM.ValueIndexedStableFirstOrderSafety
import TypePM.StepIndexedPaper1ListSafetyRegression
import TypePM.Source.M4Paper1MultisetSearchSafety

/-!
# Value-indexed safety of the Paper 1 multiset examples

The public principal M4 derivation supplies the exact postcomposed List and
multiset clause-body certificates used at the recursive boundary.  From those
certificates this module proves step-indexed safety of the actual closed
matcher cursor and then uses the value-indexed `matchAll` rule for the complete
P1-L05 and P1-L02 source expressions.  Search is restricted to the values
those expressions actually evaluate to.
-/

namespace TypePM.ValueIndexedPaper1MultisetTopLevelSafety

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open Source.MatcherTyping.M4Paper1RecursiveClosureTotalTyping
open Source.MatcherTyping.M4Paper1MultisetSearchSafety
open StepIndexedPaper1ListSafetyRegression

abbrev concreteMultisetDomain : Ty := concreteListDomain
abbrev concreteMultisetCodomain : Ty := concreteListCodomain
abbrev ConcreteMultisetBodyCertificate : Prop :=
  ClosedMultisetConcreteBodyTyping

theorem concreteMultisetBodyCertificate : ConcreteMultisetBodyCertificate :=
  closedMultiset_concreteBodyTyping

private theorem listRecursiveClosure_totalPlainTyping_of_body
    (body : TotalRecursiveClosureBodyTyping
      [capturedListDomain,
        .fn capturedListDomain (.matcher listCapability listTarget)]
      (.matcher listMatcherClauses) (.matcher listCapability listTarget)) :
    TotalPlainValueTyping listRecursiveClosure
      (.fn capturedListDomain (.matcher listCapability listTarget)) :=
  .existing (.recursiveClosure .nil body)

mutual

  private theorem listRecursiveClosure_fuelValueSafe_of_body
      (body : TotalRecursiveClosureBodyTyping
        [capturedListDomain,
          .fn capturedListDomain (.matcher listCapability listTarget)]
        (.matcher listMatcherClauses) (.matcher listCapability listTarget)) :
      ∀ fuel, FuelValueSafe fuel listRecursiveClosure
        (.fn capturedListDomain (.matcher listCapability listTarget))
    | 0 => fuelValueSafe_zero _ _
    | fuel + 1 => by
        exact .function
          (listRecursiveClosure_fuelValueSafe_of_body body fuel)
          (listRecursiveClosure_totalPlainTyping_of_body body) (by
            intro argument argumentSafe
            cases fuel with
            | zero => exact .inl rfl
            | succ residual =>
                exact .inr ⟨.matcherV [argument, listRecursiveClosure]
                    listMatcherClauses listMatcherClauses,
                  rfl,
                  listMatcherClosure_fuelValueSafe_of_body body argument
                    (residual + 1) argumentSafe⟩)

  private theorem listMatcherClosure_fuelValueSafe_of_body
      (body : TotalRecursiveClosureBodyTyping
        [capturedListDomain,
          .fn capturedListDomain (.matcher listCapability listTarget)]
        (.matcher listMatcherClauses) (.matcher listCapability listTarget))
      (argument : Value) :
      ∀ fuel, FuelValueSafe fuel argument capturedListDomain →
        FuelValueSafe fuel
          (.matcherV [argument, listRecursiveClosure]
            listMatcherClauses listMatcherClauses)
          (.matcher listCapability listTarget)
    | 0, _ => fuelValueSafe_zero _ _
    | fuel + 1, argumentSafe => by
        exact PositiveValueSafe.generatedMatcher
          (environmentTypes :=
            [capturedListDomain,
              .fn capturedListDomain (.matcher listCapability listTarget)])
          (listMatcherClosure_fuelValueSafe_of_body body argument fuel
            argumentSafe.previous)
          rfl rfl (by
            intro index target found
            cases index with
            | zero =>
                simp at found
                subst target
                exact ⟨argument, rfl, argumentSafe.previous⟩
            | succ index =>
                cases index with
                | zero =>
                    simp at found
                    subst target
                    exact ⟨listRecursiveClosure, rfl,
                      listRecursiveClosure_fuelValueSafe_of_body body fuel⟩
                | succ index => simp at found)
          body

end


private theorem multisetRecursiveClosure_totalPlainTyping_of_bodies
    (listBody : TotalRecursiveClosureBodyTyping
      [capturedListDomain,
        .fn capturedListDomain (.matcher listCapability listTarget)]
      (.matcher listMatcherClauses) (.matcher listCapability listTarget))
    (multisetBody : TotalRecursiveClosureBodyTyping
      [concreteMultisetDomain,
        .fn concreteMultisetDomain concreteMultisetCodomain,
        .fn capturedListDomain (.matcher listCapability listTarget)]
      (.matcher multisetClauses) concreteMultisetCodomain) :
    TotalPlainValueTyping multisetRecursiveClosure
      (.fn concreteMultisetDomain concreteMultisetCodomain) := by
  exact .existing (.recursiveClosure
    (.cons (.recursiveClosure .nil listBody) .nil)
    multisetBody)

mutual

  private theorem multisetRecursiveClosure_fuelValueSafe_of_bodies
      (listBody : TotalRecursiveClosureBodyTyping
        [capturedListDomain,
          .fn capturedListDomain (.matcher listCapability listTarget)]
        (.matcher listMatcherClauses) (.matcher listCapability listTarget))
      (multisetBody : TotalRecursiveClosureBodyTyping
        [concreteMultisetDomain,
          .fn concreteMultisetDomain concreteMultisetCodomain,
          .fn capturedListDomain (.matcher listCapability listTarget)]
        (.matcher multisetClauses) concreteMultisetCodomain) :
      ∀ fuel, FuelValueSafe fuel multisetRecursiveClosure
        (.fn concreteMultisetDomain concreteMultisetCodomain)
    | 0 => fuelValueSafe_zero _ _
    | fuel + 1 => by
        exact .function
          (multisetRecursiveClosure_fuelValueSafe_of_bodies
            listBody multisetBody fuel)
          (multisetRecursiveClosure_totalPlainTyping_of_bodies
            listBody multisetBody) (by
            intro argument argumentSafe
            cases fuel with
            | zero => exact .inl rfl
            | succ residual =>
                exact .inr ⟨.matcherV
                    [argument, multisetRecursiveClosure, listRecursiveClosure]
                    multisetClauses multisetClauses,
                  rfl,
                  multisetMatcherClosure_fuelValueSafe_of_bodies
                    listBody multisetBody argument (residual + 1) argumentSafe⟩)

  private theorem multisetMatcherClosure_fuelValueSafe_of_bodies
      (listBody : TotalRecursiveClosureBodyTyping
        [capturedListDomain,
          .fn capturedListDomain (.matcher listCapability listTarget)]
        (.matcher listMatcherClauses) (.matcher listCapability listTarget))
      (multisetBody : TotalRecursiveClosureBodyTyping
        [concreteMultisetDomain,
          .fn concreteMultisetDomain concreteMultisetCodomain,
          .fn capturedListDomain (.matcher listCapability listTarget)]
        (.matcher multisetClauses) concreteMultisetCodomain)
      (argument : Value) :
      ∀ fuel, FuelValueSafe fuel argument concreteMultisetDomain →
        FuelValueSafe fuel
          (.matcherV
            [argument, multisetRecursiveClosure, listRecursiveClosure]
            multisetClauses multisetClauses)
          concreteMultisetCodomain
    | 0, _ => fuelValueSafe_zero _ _
    | fuel + 1, argumentSafe => by
        exact PositiveValueSafe.generatedMatcher
          (environmentTypes :=
            [concreteMultisetDomain,
              .fn concreteMultisetDomain concreteMultisetCodomain,
              .fn capturedListDomain (.matcher listCapability listTarget)])
          (multisetMatcherClosure_fuelValueSafe_of_bodies
            listBody multisetBody argument fuel argumentSafe.previous)
          rfl rfl (by
            intro index target found
            cases index with
            | zero =>
                simp at found
                subst target
                exact ⟨argument, rfl, argumentSafe.previous⟩
            | succ index =>
                cases index with
                | zero =>
                    simp at found
                    subst target
                    exact ⟨multisetRecursiveClosure, rfl,
                      multisetRecursiveClosure_fuelValueSafe_of_bodies
                        listBody multisetBody fuel⟩
                | succ index =>
                    cases index with
                    | zero =>
                        simp at found
                        subst target
                        exact ⟨listRecursiveClosure, rfl,
                          listRecursiveClosure_fuelValueSafe_of_body
                            listBody fuel⟩
                    | succ index => simp at found)
          multisetBody

end


/-- Premise-free all-index safety of the exact matcher value returned by
`multiset something`. -/
theorem closedMultisetMatcherValue_fuelValueSafe (fuel : Nat) :
    FuelValueSafe fuel closedMultisetMatcherValue
      concreteMultisetCodomain := by
  obtain ⟨listDomain, listCapability, listTarget, listBody, multisetBody⟩ :=
    concreteMultisetBodyCertificate
  exact multisetMatcherClosure_fuelValueSafe_of_bodies
    listBody multisetBody .something fuel
    (something_concreteListDomain_fuelValueSafe fuel)

private theorem evalFuel_approximates_of_le
    (le : firstFuel ≤ secondFuel) :
    FuelResult.Approximates
      (evalFuel firstFuel environment expression)
      (evalFuel secondFuel environment expression) := by
  rw [← Nat.add_sub_of_le le]
  induction secondFuel - firstFuel with
  | zero => simp
  | succ extra induction =>
      rw [Nat.add_succ]
      exact induction.trans (evalFuel_approximates_succ
        (fuel := firstFuel + extra))

private theorem successful_value_eq_of_eventual_exact
    (exact : evalFuel successfulFuel environment expression = .ok expected)
    (success : evalFuel fuel environment expression = .ok actual) :
    actual = expected := by
  by_cases le : fuel ≤ successfulFuel
  · have related := evalFuel_approximates_of_le
      (environment := environment) (expression := expression) le
    rw [success, exact] at related
    cases related
    rfl
  · have reverseLe : successfulFuel ≤ fuel := by omega
    have related := evalFuel_approximates_of_le
      (environment := environment) (expression := expression) reverseLe
    rw [exact, success] at related
    cases related
    rfl

private theorem evalFuel_notStuck_of_exact
    (exact : evalFuel successfulFuel environment expression = .ok expected)
    (fuel : Nat) :
    (evalFuel fuel environment expression).NotStuck :=
  evalFuel_neverStuck_of_eventual_success exact fuel

private theorem intList_fuelValueSafe (literals : List Int) (fuel : Nat) :
    FuelValueSafe fuel (Value.buildList (literals.map Value.int))
      (DataTypes.list .int) := by
  apply fuelValueSafe_list_of_forall .int fuel
  intro value member
  simp only [List.mem_map] at member
  obtain ⟨literal, _, rfl⟩ := member
  exact fuelValueSafe_int literal fuel

private theorem int_allFuelValueSafe (literal : Int) :
    AllFuelValueSafe (.int literal) .int :=
  fuelValueSafe_int literal

private theorem totalPlainInt_allFuelValueSafe
    (typed : TotalPlainValueTyping value .int) :
    AllFuelValueSafe value .int := by
  cases typed with
  | existing total =>
      cases total with
      | ordinary ordinary =>
          obtain ⟨literal, rfl⟩ := ordinary.int_canonical
          exact int_allFuelValueSafe literal

private theorem TotalPlainListValueTypings.intMembersAllFuelSafe :
    ∀ {values}, TotalPlainListValueTypings values .int →
      ∀ value ∈ values, AllFuelValueSafe value .int
  | _, .nil => by simp
  | _, .cons head tail => by
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact totalPlainInt_allFuelValueSafe head
      · exact TotalPlainListValueTypings.intMembersAllFuelSafe tail
          candidate member

private theorem totalPlainIntList_allFuelValueSafe
    (typed : TotalPlainValueTyping value (DataTypes.list .int)) :
    AllFuelValueSafe value (DataTypes.list .int) := by
  obtain ⟨values, rfl, items⟩ := typed.list_canonical
  intro fuel
  exact fuelValueSafe_list_of_forall .int fuel values (by
    intro item member
    exact TotalPlainListValueTypings.intMembersAllFuelSafe items item member fuel)

private theorem pair_allFuelValueSafe
    (firstSafe : AllFuelValueSafe first firstType)
    (secondSafe : AllFuelValueSafe second secondType) :
    AllFuelValueSafe (.tuple [first, second]) (.prod [firstType, secondType]) := by
  intro fuel
  induction fuel with
  | zero => exact fuelValueSafe_zero _ _
  | succ fuel induction =>
      exact fuelValueSafe_tuple induction
        (.cons (firstSafe (fuel + 1)) (.cons (secondSafe (fuel + 1)) .nil))

private theorem target123_evaluation_fuelSafe (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list .int)
      (evalFuel fuel [] Runtime.Paper1ExecutionRegression.target123) := by
  cases current : evalFuel fuel [] Runtime.Paper1ExecutionRegression.target123 with
  | timeout => exact .inl rfl
  | stuck =>
      have safe := evalFuel_notStuck_of_exact
        (by with_unfolding_all rfl :
          evalFuel 29 [] Runtime.Paper1ExecutionRegression.target123 =
            .ok multisetConsTarget)
        fuel
      rw [current] at safe
      contradiction
  | ok value =>
      have equality := successful_value_eq_of_eventual_exact
        (by with_unfolding_all rfl :
          evalFuel 29 [] Runtime.Paper1ExecutionRegression.target123 =
            .ok multisetConsTarget)
        current
      subst value
      exact .inr ⟨multisetConsTarget, rfl, by
        simpa [multisetConsTarget] using intList_fuelValueSafe [1, 2, 3] fuel⟩

private theorem successorTarget_evaluation_fuelSafe (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list .int)
      (evalFuel fuel []
        (sourceList [.lit 1, .lit 2, .lit 5, .lit 6])) := by
  cases current : evalFuel fuel []
      (sourceList [.lit 1, .lit 2, .lit 5, .lit 6]) with
  | timeout => exact .inl rfl
  | stuck =>
      have safe := evalFuel_notStuck_of_exact
        (by with_unfolding_all rfl :
          evalFuel 39 [] (sourceList [.lit 1, .lit 2, .lit 5, .lit 6]) =
            .ok successorTarget)
        fuel
      rw [current] at safe
      contradiction
  | ok value =>
      have equality := successful_value_eq_of_eventual_exact
        (by with_unfolding_all rfl :
          evalFuel 39 [] (sourceList [.lit 1, .lit 2, .lit 5, .lit 6]) =
            .ok successorTarget)
        current
      subst value
      exact .inr ⟨successorTarget, rfl, by
        simpa [successorTarget] using intList_fuelValueSafe [1, 2, 5, 6] fuel⟩

private theorem matcher_evaluation_fuelSafe
    (fuel : Nat) :
    FuelResultSafe fuel concreteMultisetCodomain
      (evalFuel fuel [] multisetSomething) := by
  cases current : evalFuel fuel [] multisetSomething with
  | timeout => exact .inl rfl
  | stuck =>
      have safe := evalFuel_notStuck_of_exact
        closedMultisetMatcher_eval_exact fuel
      rw [current] at safe
      contradiction
  | ok value =>
      have equality := successful_value_eq_of_eventual_exact
        closedMultisetMatcher_eval_exact current
      subst value
      exact .inr ⟨closedMultisetMatcherValue, rfl,
        closedMultisetMatcherValue_fuelValueSafe fuel⟩

private theorem multisetCons_evaluatedSearchSafe (fuel : Nat) :
    EvaluatedPatternSearchSafe fuel []
      Runtime.Paper1ExecutionRegression.target123 multisetSomething
      multisetConsPattern [.int, DataTypes.list .int] := by
  intro targetValue matcherValue targetSuccess matcherSuccess
  have target_eq := successful_value_eq_of_eventual_exact
    (by with_unfolding_all rfl :
      evalFuel 29 [] Runtime.Paper1ExecutionRegression.target123 =
        .ok multisetConsTarget)
    targetSuccess
  have matcher_eq := successful_value_eq_of_eventual_exact
    closedMultisetMatcher_eval_exact matcherSuccess
  subst targetValue
  subst matcherValue
  exact multisetCons_concretePatternSearchSafe fuel

private theorem successorPairs_evaluatedSearchSafe (fuel : Nat) :
    EvaluatedPatternSearchSafe fuel []
      (sourceList [.lit 1, .lit 2, .lit 5, .lit 6]) multisetSomething
      successorPattern [.int] := by
  intro targetValue matcherValue targetSuccess matcherSuccess
  have target_eq := successful_value_eq_of_eventual_exact
    (by with_unfolding_all rfl :
      evalFuel 39 [] (sourceList [.lit 1, .lit 2, .lit 5, .lit 6]) =
        .ok successorTarget)
    targetSuccess
  have matcher_eq := successful_value_eq_of_eventual_exact
    closedMultisetMatcher_eval_exact matcherSuccess
  subst targetValue
  subst matcherValue
  exact successorPairs_concretePatternSearchSafe fuel

private theorem multisetCons_bodySafeWith (fuel : Nat) :
    EvaluatedBindingBodySafeWith fuel []
      [.int, DataTypes.list .int] (.tuple [.var 0, .var 1])
      (fun value => AllFuelValueSafe value
        (.prod [.int, DataTypes.list .int])) := by
  intro bindings typed
  cases typed with
  | cons firstTyped tailTyped =>
      cases tailTyped with
      | cons secondTyped restTyped =>
          cases restTyped
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel =>
              cases fuel with
              | zero => exact .inl rfl
              | succ residual =>
                  exact .inr ⟨.tuple [_, _], rfl,
                    pair_allFuelValueSafe
                      (totalPlainInt_allFuelValueSafe firstTyped)
                      (totalPlainIntList_allFuelValueSafe secondTyped)⟩

private theorem successorPairs_bodySafeWith (fuel : Nat) :
    EvaluatedBindingBodySafeWith fuel [] [.int] (.var 0)
      (fun value => AllFuelValueSafe value .int) := by
  intro bindings typed
  cases typed with
  | cons firstTyped restTyped =>
      cases restTyped
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          exact .inr ⟨_, rfl, totalPlainInt_allFuelValueSafe firstTyped⟩

private theorem bindingBodySafe_of_allFuel
    (safeWith : EvaluatedBindingBodySafeWith fuel environment bindingTypes
      body (fun value => AllFuelValueSafe value target)) :
    EvaluatedBindingBodySafe fuel environment bindingTypes body target := by
  intro bindings typed
  rcases safeWith bindings typed with timeout | ⟨value, success, safe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, safe fuel⟩

/-- Direct use of the base value-indexed `matchAll` theorem at the common
child fuel. -/
theorem multisetCons_matchAllResidualSafe
    (fuel : Nat) :
    FuelResultSafe fuel
      (DataTypes.list (.prod [.int, DataTypes.list .int]))
      (evalFuel (fuel + 1) [] Runtime.Paper1ExecutionRegression.multisetCons) := by
  exact matchAllFuel_valueIndexedSafe
    (target123_evaluation_fuelSafe fuel)
    (matcher_evaluation_fuelSafe fuel)
    (multisetCons_evaluatedSearchSafe fuel)
    (bindingBodySafe_of_allFuel (multisetCons_bodySafeWith fuel))

theorem successorPairs_matchAllResidualSafe
    (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list .int)
      (evalFuel (fuel + 1) [] Runtime.Paper1ExecutionRegression.successorPairs) := by
  exact matchAllFuel_valueIndexedSafe
    (successorTarget_evaluation_fuelSafe fuel)
    (matcher_evaluation_fuelSafe fuel)
    (successorPairs_evaluatedSearchSafe fuel)
    (bindingBodySafe_of_allFuel (successorPairs_bodySafeWith fuel))

/-- Same-index safety of the full P1-L05 expression.  The all-index body
postcondition closes the one-index gap introduced by the outer evaluator
step. -/
theorem multisetCons_fuelResultSafe
    : ∀ fuel,
    FuelResultSafe fuel
      (DataTypes.list (.prod [.int, DataTypes.list .int]))
      (evalFuel fuel [] Runtime.Paper1ExecutionRegression.multisetCons)
  | 0 => .inl rfl
  | fuel + 1 => by
      exact (matchAllFuel_valueIndexedAllFuelSafe
        (target123_evaluation_fuelSafe fuel)
        (matcher_evaluation_fuelSafe fuel)
        (multisetCons_evaluatedSearchSafe fuel)
        (multisetCons_bodySafeWith fuel)).toAllFuelResultSafe.toFuelResultSafe
          (fuel + 1)

/-- Same-index safety of the complete value-dependent P1-L02 expression. -/
theorem successorPairs_fuelResultSafe
    : ∀ fuel,
    FuelResultSafe fuel (DataTypes.list .int)
      (evalFuel fuel [] Runtime.Paper1ExecutionRegression.successorPairs)
  | 0 => .inl rfl
  | fuel + 1 => by
      exact (matchAllFuel_valueIndexedAllFuelSafe
        (successorTarget_evaluation_fuelSafe fuel)
        (matcher_evaluation_fuelSafe fuel)
        (successorPairs_evaluatedSearchSafe fuel)
        (successorPairs_bodySafeWith fuel)).toAllFuelResultSafe.toFuelResultSafe
          (fuel + 1)

theorem multisetCons_neverStuck
    (fuel : Nat) :
    (evalFuel fuel [] Runtime.Paper1ExecutionRegression.multisetCons).NotStuck :=
  (multisetCons_fuelResultSafe fuel).notStuck

theorem successorPairs_neverStuck
    (fuel : Nat) :
    (evalFuel fuel [] Runtime.Paper1ExecutionRegression.successorPairs).NotStuck :=
  (successorPairs_fuelResultSafe fuel).notStuck

/-- A concrete milestone bundle.  Static construction comes from the public
principal M4 derivation, and the two search fields retain their actual source
patterns and matcher value.  The result fields combine step-indexed body
certificates with target, matcher, and search certificates that are currently
seeded by exact executions; this is not a general M4-to-runtime safety bridge. -/
structure ActualMultisetTopLevelSafety : Prop where
  staticMatcher : ∃ target,
    TotalValueTyping closedMultisetMatcherValue target
  multisetSearch : ActualMultisetConsSearchCertificate
  successorSearch : ActualSuccessorPairsSearchCertificate
  matcher : ∀ fuel,
    FuelValueSafe fuel closedMultisetMatcherValue concreteMultisetCodomain
  multisetResult : ∀ fuel,
    FuelResultSafe fuel
      (DataTypes.list (.prod [.int, DataTypes.list .int]))
      (evalFuel fuel [] Runtime.Paper1ExecutionRegression.multisetCons)
  successorResult : ∀ fuel,
    FuelResultSafe fuel (DataTypes.list .int)
      (evalFuel fuel [] Runtime.Paper1ExecutionRegression.successorPairs)

theorem actualMultisetTopLevelSafety
    : ActualMultisetTopLevelSafety :=
  ⟨closedMultisetMatcherValue_totalTyping,
    actualMultisetConsSearchCertificate,
    actualSuccessorPairsSearchCertificate,
    closedMultisetMatcherValue_fuelValueSafe,
    multisetCons_fuelResultSafe,
    successorPairs_fuelResultSafe⟩

end TypePM.ValueIndexedPaper1MultisetTopLevelSafety
