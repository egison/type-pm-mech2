import TypePM.Runtime.EvaluationCompleteness
import TypePM.Source.Paper1Programs

/-!
# End-to-end Paper 1 execution regressions

The programs in this module use the source-defined `list` matcher and the
exact seven-clause `multiset` matcher.  No evaluator callback or matcher
oracle replaces any source clause.
-/

namespace TypePM.Runtime.Paper1ExecutionRegression

open TypePM.Source
open TypePM.Source.Paper1Programs

def target123 : Source.Expr := sourceList [.lit 1, .lit 2, .lit 3]

def listJoinAll : Source.Expr :=
  .matchAll target123 (.app listMatcherDefinition .something)
    (.ctor PatternCtor.join [.var, .var])
    (.tuple [.var 0, .var 1])

def multisetCons : Source.Expr :=
  .matchAll target123 multisetSomething
    (.ctor PatternCtor.cons [.var, .var])
    (.tuple [.var 0, .var 1])

def successorPattern : Source.Pattern :=
  .ctor PatternCtor.cons
    [.var,
      .ctor PatternCtor.cons
        [.value (.prim .add [.var 0, .lit 1]), .wild]]

def successorPairs : Source.Expr :=
  .matchAll (sourceList [.lit 1, .lit 2, .lit 5, .lit 6])
    multisetSomething successorPattern (.var 0)

def groundList123 : GroundValue := GroundValue.buildList [.int 1, .int 2, .int 3]
def groundList12 : GroundValue := GroundValue.buildList [.int 1, .int 2]
def groundList23 : GroundValue := GroundValue.buildList [.int 2, .int 3]
def groundList1 : GroundValue := GroundValue.buildList [.int 1]
def groundList3 : GroundValue := GroundValue.buildList [.int 3]
def groundList13 : GroundValue := GroundValue.buildList [.int 1, .int 3]

def expectedListJoinGround : GroundValue :=
  GroundValue.buildList
    [GroundValue.tupleValue [GroundValue.nilValue, groundList123],
      GroundValue.tupleValue [groundList1, groundList23],
      GroundValue.tupleValue [groundList12, groundList3],
      GroundValue.tupleValue [groundList123, GroundValue.nilValue]]

def expectedMultisetConsGround : GroundValue :=
  GroundValue.buildList
    [GroundValue.tupleValue [.int 1, groundList23],
      GroundValue.tupleValue [.int 2, groundList13],
      GroundValue.tupleValue [.int 3, groundList12]]

def expectedSuccessorsGround : GroundValue :=
  GroundValue.buildList [.int 1, .int 5]

def expectedListJoin : Value := Value.ofGround expectedListJoinGround
def expectedMultisetCons : Value := Value.ofGround expectedMultisetConsGround
def expectedSuccessors : Value := Value.ofGround expectedSuccessorsGround

private theorem result_eq_ok_of_ground_projection
    (projected : FuelResult.map Value.toGround? result =
      .ok (some ground)) :
    result = .ok (Value.ofGround ground) := by
  cases result with
  | timeout => simp [FuelResult.map] at projected
  | stuck => simp [FuelResult.map] at projected
  | ok value =>
      simp only [FuelResult.map, FuelResult.ok.injEq] at projected
      rw [Value.eq_of_toGround?_eq_some projected]

set_option maxRecDepth 100000 in
theorem list_join_ground_projection_exact :
    FuelResult.map Value.toGround? (evalFuel 25 [] listJoinAll) =
      .ok (some expectedListJoinGround) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem multiset_cons_ground_projection_exact :
    FuelResult.map Value.toGround? (evalFuel 30 [] multisetCons) =
      .ok (some expectedMultisetConsGround) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem successor_pairs_ground_projection_exact :
    FuelResult.map Value.toGround? (evalFuel 40 [] successorPairs) =
      .ok (some expectedSuccessorsGround) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem list_join_enumerates_all_prefixes_exact :
    evalFuel 25 [] listJoinAll = .ok expectedListJoin := by
  exact result_eq_ok_of_ground_projection list_join_ground_projection_exact

set_option maxRecDepth 100000 in
theorem multiset_cons_preserves_three_source_order_choices_exact :
    evalFuel 30 [] multisetCons = .ok expectedMultisetCons := by
  exact result_eq_ok_of_ground_projection multiset_cons_ground_projection_exact

set_option maxRecDepth 100000 in
theorem successor_pairs_exact :
    evalFuel 40 [] successorPairs =
      .ok expectedSuccessors := by
  exact result_eq_ok_of_ground_projection successor_pairs_ground_projection_exact

theorem list_join_has_independent_derivation :
    Eval [] listJoinAll expectedListJoin :=
  evalFuel_sound list_join_enumerates_all_prefixes_exact

theorem multiset_cons_has_independent_derivation :
    Eval [] multisetCons expectedMultisetCons :=
  evalFuel_sound multiset_cons_preserves_three_source_order_choices_exact

theorem successor_pairs_has_independent_derivation :
    Eval [] successorPairs expectedSuccessors :=
  evalFuel_sound successor_pairs_exact

theorem list_join_has_finite_fuel :
    ∃ fuel, evalFuel fuel [] listJoinAll = .ok expectedListJoin :=
  list_join_has_independent_derivation.complete

theorem multiset_cons_has_finite_fuel :
    ∃ fuel, evalFuel fuel [] multisetCons = .ok expectedMultisetCons :=
  multiset_cons_has_independent_derivation.complete

theorem successor_pairs_has_finite_fuel :
    ∃ fuel, evalFuel fuel [] successorPairs =
      .ok expectedSuccessors :=
  successor_pairs_has_independent_derivation.complete

end TypePM.Runtime.Paper1ExecutionRegression
