import TypePM.ValueIndexedMatchAllSafety
import TypePM.StepIndexedPaper1ListSafetyRegression
import TypePM.Source.M4Paper1ListJoinSearchSafety

/-!
# Value-indexed `matchAll` safety for the Paper 1 List join

This regression uses the actual target and matcher values produced by the
closed source program.  Its search premise is the concrete M4-backed List
join certificate, never a universal claim about values of the same type.
-/

namespace TypePM.ValueIndexedPaper1ListJoinMatchAllSafetyRegression

open Runtime Source
open Source.Paper1Programs
open Runtime.Paper1ExecutionRegression
open Source.MatcherTyping.M4Paper1ListJoinSearchSafety
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open StepIndexedPaper1ListSafetyRegression

def joinBindingTypes : List Ty :=
  [DataTypes.list .int, DataTypes.list .int]

def joinBodyTarget : Ty :=
  .prod [DataTypes.list .int, DataTypes.list .int]

private theorem totalPlainInt_fuelValueSafe
    (typed : TotalPlainValueTyping value .int) (fuel : Nat) :
    FuelValueSafe fuel value .int := by
  cases typed with
  | existing total =>
      cases total with
      | ordinary ordinary =>
          obtain ⟨literal, rfl⟩ := ordinary.int_canonical
          exact fuelValueSafe_int literal fuel

private theorem TotalPlainListValueTypings.intMembersFuelSafe
    (fuel : Nat) : ∀ {values},
    TotalPlainListValueTypings values .int →
      ∀ value ∈ values, FuelValueSafe fuel value .int
  | _, .nil => by simp
  | _, .cons head tail => by
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · simpa [equality] using totalPlainInt_fuelValueSafe head fuel
      · exact TotalPlainListValueTypings.intMembersFuelSafe fuel tail
          candidate member

private theorem totalPlainIntList_fuelValueSafe
    (typed : TotalPlainValueTyping value (DataTypes.list .int))
    (fuel : Nat) :
    FuelValueSafe fuel value (DataTypes.list .int) := by
  obtain ⟨values, rfl, items⟩ := typed.list_canonical
  exact fuelValueSafe_list_of_forall .int fuel values
    (TotalPlainListValueTypings.intMembersFuelSafe fuel items)

private theorem fuelValueSafe_pair
    (firstSafe : FuelValueSafe fuel first (DataTypes.list .int))
    (secondSafe : FuelValueSafe fuel second (DataTypes.list .int)) :
    FuelValueSafe fuel (.tuple [first, second]) joinBodyTarget := by
  induction fuel with
  | zero => exact fuelValueSafe_zero _ _
  | succ fuel induction =>
      exact fuelValueSafe_tuple
        (induction firstSafe.previous secondSafe.previous)
        (.cons firstSafe (.cons secondSafe .nil))

theorem list123_fuelValueSafe (fuel : Nat) :
    FuelValueSafe fuel list123Value (DataTypes.list .int) := by
  apply fuelValueSafe_list_of_forall .int fuel
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact fuelValueSafe_int 1 fuel
  · exact fuelValueSafe_int 2 fuel
  · exact fuelValueSafe_int 3 fuel

theorem target123_evaluation_fuelSafe :
    ∀ fuel, FuelResultSafe fuel (DataTypes.list .int)
      (evalFuel fuel [] target123)
  | 0 => .inl rfl
  | 1 => .inl rfl
  | 2 => .inl rfl
  | 3 => .inl rfl
  | fuel + 4 => .inr ⟨list123Value, rfl, list123_fuelValueSafe (fuel + 4)⟩

theorem target123_evaluation_shape :
    ∀ fuel, evalFuel fuel [] target123 = .timeout ∨
      evalFuel fuel [] target123 = .ok list123Value
  | 0 => .inl rfl
  | 1 => .inl rfl
  | 2 => .inl rfl
  | 3 => .inl rfl
  | _ + 4 => .inr rfl

theorem listMatcherSomething_evaluation_fuelSafe :
    ∀ fuel, FuelResultSafe fuel concreteListCodomain
      (evalFuel fuel [] (.app listMatcherDefinition .something))
  | 0 => .inl rfl
  | 1 => .inl rfl
  | 2 => .inl rfl
  | fuel + 3 => .inr ⟨listMatcherSomethingValue, rfl,
      listMatcherClosure_concreteFuelValueSafe .something (fuel + 3)
        (something_concreteListDomain_fuelValueSafe (fuel + 3))⟩

theorem listMatcherSomething_evaluation_shape :
    ∀ fuel,
      evalFuel fuel [] (.app listMatcherDefinition .something) = .timeout ∨
        evalFuel fuel [] (.app listMatcherDefinition .something) =
          .ok listMatcherSomethingValue
  | 0 => .inl rfl
  | 1 => .inl rfl
  | 2 => .inl rfl
  | _ + 3 => .inr rfl

/-- The concrete M4 search theorem is selected only after the two source
expressions are known to have returned its exact target and matcher values. -/
theorem listJoin_evaluatedPatternSearchSafe (fuel : Nat) :
    EvaluatedPatternSearchSafe fuel [] target123
      (.app listMatcherDefinition .something)
      TotalPlainClosureSafetyRegression.listJoinPattern joinBindingTypes := by
  intro targetValue matcherValue targetSuccess matcherSuccess
  rcases target123_evaluation_shape fuel with targetTimeout | targetExact
  · rw [targetSuccess] at targetTimeout
    contradiction
  · have target_eq : targetValue = list123Value := by
      rw [targetSuccess] at targetExact
      exact FuelResult.ok.inj targetExact
    rcases listMatcherSomething_evaluation_shape fuel with matcherTimeout |
      matcherExact
    · rw [matcherSuccess] at matcherTimeout
      contradiction
    · have matcher_eq : matcherValue = listMatcherSomethingValue := by
        rw [matcherSuccess] at matcherExact
        exact FuelResult.ok.inj matcherExact
      subst targetValue
      subst matcherValue
      exact listJoin_concretePatternSearchSafe fuel

theorem joinTupleBody_fuelSafe (fuel : Nat) :
    EvaluatedBindingBodySafe fuel [] joinBindingTypes
      (.tuple [.var 0, .var 1]) joinBodyTarget := by
  intro bindings bindingsTyped
  cases bindingsTyped with
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
                    fuelValueSafe_pair
                      (totalPlainIntList_fuelValueSafe firstTyped
                        (residual + 2))
                      (totalPlainIntList_fuelValueSafe secondTyped
                        (residual + 2))⟩

/-- All-fuel typed safety of the actual Paper 1 `listJoinAll` expression. -/
theorem listJoinAll_fuelResultSafe :
    ∀ fuel, FuelResultSafe fuel (DataTypes.list joinBodyTarget)
      (evalFuel (fuel + 1) [] listJoinAll)
  | fuel => by
      exact matchAllFuel_valueIndexedSafe
        (target123_evaluation_fuelSafe fuel)
        (listMatcherSomething_evaluation_fuelSafe fuel)
        (listJoin_evaluatedPatternSearchSafe fuel)
        (joinTupleBody_fuelSafe fuel)

theorem listJoinAll_neverStuck (fuel : Nat) :
    (evalFuel fuel [] listJoinAll).NotStuck := by
  cases fuel with
  | zero => simp [evalFuel, FuelResult.NotStuck]
  | succ fuel => exact (listJoinAll_fuelResultSafe fuel).notStuck

theorem listJoinAll_exact :
    evalFuel 25 [] listJoinAll = .ok expectedListJoin :=
  list_join_enumerates_all_prefixes_exact

end TypePM.ValueIndexedPaper1ListJoinMatchAllSafetyRegression
