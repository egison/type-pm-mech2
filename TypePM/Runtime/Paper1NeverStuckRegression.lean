import TypePM.Runtime.EvaluationStuckMonotonicity
import TypePM.Runtime.MultisetClauseExecutionRegression
import TypePM.Source.M4Paper1IntegratedPositiveRegression

/-!
# Paper 1 operational non-stuck regressions

These theorems combine a kernel-checked successful run at one concrete fuel
with preservation of `stuck` under increasing fuel.  They therefore show that
the same expression is not `stuck` at any fuel: smaller runs can only time out,
and larger runs preserve the known success.

This is an independent operational regression, not a general type-safety
theorem.  The three source-typed endpoints pair the operational fact with the
separately proved public M4 typing judgment; the typing proof is not used to
derive the non-stuck conclusion.
-/

namespace TypePM.Runtime.Paper1NeverStuckRegression

open FuelResult

open Paper1ExecutionRegression
open MultisetClauseExecutionRegression
open Source.M4Paper1IntegratedPositiveRegression

/-! ## Integrated Paper 1 programs -/

theorem list_join_all_never_stuck (fuel : Nat) :
    (evalFuel fuel [] listJoinAll).NotStuck :=
  evalFuel_neverStuck_of_eventual_success
    list_join_enumerates_all_prefixes_exact fuel

theorem multiset_cons_never_stuck (fuel : Nat) :
    (evalFuel fuel [] multisetCons).NotStuck :=
  evalFuel_neverStuck_of_eventual_success
    multiset_cons_preserves_three_source_order_choices_exact fuel

theorem successor_pairs_never_stuck (fuel : Nat) :
    (evalFuel fuel [] successorPairs).NotStuck :=
  evalFuel_neverStuck_of_eventual_success
    successor_pairs_exact fuel

/-- P1-L01 has both its public inferred type and its independent all-fuel
operational non-stuck regression. -/
theorem list_join_all_typed_and_never_stuck :
    Source.M4.Typing Source.Paper1FrozenSignature.signature []
        listJoinAll listJoinResultType ∧
      ∀ fuel, (evalFuel fuel [] listJoinAll).NotStuck :=
  ⟨list_join_typing, list_join_all_never_stuck⟩

/-- P1-L05 has both its public inferred type and its independent all-fuel
operational non-stuck regression. -/
theorem multiset_cons_typed_and_never_stuck :
    Source.M4.Typing Source.Paper1FrozenSignature.signature []
        multisetCons multisetConsResultType ∧
      ∀ fuel, (evalFuel fuel [] multisetCons).NotStuck :=
  ⟨multiset_cons_typing, multiset_cons_never_stuck⟩

/-- P1-L02 has both its public inferred type and its independent all-fuel
operational non-stuck regression. -/
theorem successor_pairs_typed_and_never_stuck :
    Source.M4.Typing Source.Paper1FrozenSignature.signature []
        successorPairs successorPairsResultType ∧
      ∀ fuel, (evalFuel fuel [] successorPairs).NotStuck :=
  ⟨successor_pairs_typing, successor_pairs_never_stuck⟩

/-! ## Individual successful multiset-clause fixtures -/

theorem nil_clause_never_stuck (fuel : Nat) :
    (evalFuel fuel [] nilClauseProgram).NotStuck :=
  evalFuel_neverStuck_of_eventual_success nil_clause_result_exact fuel

theorem head_only_clause_never_stuck (fuel : Nat) :
    (evalFuel fuel [] headOnlyClauseProgram).NotStuck :=
  evalFuel_neverStuck_of_eventual_success
    head_only_clause_result_exact fuel

theorem value_cons_clause_never_stuck (fuel : Nat) :
    (evalFuel fuel [] valueConsSuccessProgram).NotStuck :=
  evalFuel_neverStuck_of_eventual_success
    value_cons_clause_result_exact fuel

theorem general_cons_clause_never_stuck (fuel : Nat) :
    (evalFuel fuel [] generalConsClauseProgram).NotStuck := by
  simpa only [generalConsClauseProgram] using
    multiset_cons_never_stuck fuel

theorem join_clause_never_stuck (fuel : Nat) :
    (evalFuel fuel [] joinClauseProgram).NotStuck :=
  evalFuel_neverStuck_of_eventual_success join_clause_result_exact fuel

theorem whole_value_clause_never_stuck (fuel : Nat) :
    (evalFuel fuel [] wholeValueSuccessProgram).NotStuck :=
  evalFuel_neverStuck_of_eventual_success
    whole_value_clause_result_exact fuel

theorem catch_all_clause_never_stuck (fuel : Nat) :
    (evalFuel fuel [] catchAllClauseProgram).NotStuck :=
  evalFuel_neverStuck_of_eventual_success
    catch_all_clause_result_exact fuel

end TypePM.Runtime.Paper1NeverStuckRegression
