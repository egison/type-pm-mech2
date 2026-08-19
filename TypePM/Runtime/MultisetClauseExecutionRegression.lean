import TypePM.Runtime.Paper1ExecutionRegression

/-!
# End-to-end regressions for all seven multiset clauses

Each program below uses the complete source-defined Paper 1 `multiset`
matcher.  The examples isolate the observable behavior selected by one of
its seven source-ordered clauses; no runtime oracle replaces the matcher.
-/

namespace TypePM.Runtime.MultisetClauseExecutionRegression

open TypePM.Source
open TypePM.Source.Paper1Programs
open TypePM.Runtime.Paper1ExecutionRegression

def targetEmpty : Source.Expr := sourceList []
def target112 : Source.Expr := sourceList [.lit 1, .lit 1, .lit 2]
def target23 : Source.Expr := sourceList [.lit 2, .lit 3]
def target21 : Source.Expr := sourceList [.lit 2, .lit 1]
def target13 : Source.Expr := sourceList [.lit 1, .lit 3]
def target1 : Source.Expr := sourceList [.lit 1]

def nilClauseProgram : Source.Expr :=
  .matchAll targetEmpty multisetSomething
    (.ctor PatternCtor.nil []) (.lit 0)

def nilClauseFailureProgram : Source.Expr :=
  .matchAll target1 multisetSomething
    (.ctor PatternCtor.nil []) (.lit 0)

def headOnlyClauseProgram : Source.Expr :=
  .matchAll target123 multisetSomething
    (.ctor PatternCtor.cons [.var, .wild]) (.var 0)

def valueConsSuccessProgram : Source.Expr :=
  .matchAll target112 multisetSomething
    (.ctor PatternCtor.cons [.value (.lit 1), .var]) (.var 0)

def valueConsFailureProgram : Source.Expr :=
  .matchAll target23 multisetSomething
    (.ctor PatternCtor.cons [.value (.lit 1), .var]) (.var 0)

def generalConsClauseProgram : Source.Expr := multisetCons

def joinClauseProgram : Source.Expr :=
  .matchAll target123 multisetSomething
    (.ctor PatternCtor.join [.var, .var])
    (.tuple [.var 0, .var 1])

def wholeValueSuccessProgram : Source.Expr :=
  .matchAll target21 multisetSomething
    (.value (sourceList [.lit 1, .lit 2])) unit

def wholeValueFailureProgram : Source.Expr :=
  .matchAll target13 multisetSomething
    (.value (sourceList [.lit 1, .lit 2])) unit

def catchAllClauseProgram : Source.Expr :=
  .matchAll target123 multisetSomething .var (.var 0)

def groundList112 : GroundValue :=
  GroundValue.buildList [.int 1, .int 1, .int 2]

def groundList21 : GroundValue := GroundValue.buildList [.int 2, .int 1]
def groundList2 : GroundValue := GroundValue.buildList [.int 2]

def expectedNil : GroundValue := GroundValue.buildList [.int 0]

def expectedHeads : GroundValue :=
  GroundValue.buildList [.int 1, .int 2, .int 3]

def expectedValueCons : GroundValue :=
  GroundValue.buildList [groundList12]

def expectedJoin : GroundValue :=
  GroundValue.buildList
    [GroundValue.tupleValue [GroundValue.nilValue, groundList123],
      GroundValue.tupleValue [groundList3, groundList12],
      GroundValue.tupleValue [groundList2, groundList13],
      GroundValue.tupleValue [groundList23, groundList1],
      GroundValue.tupleValue [groundList1, groundList23],
      GroundValue.tupleValue [groundList13, groundList2],
      GroundValue.tupleValue [groundList12, groundList3],
      GroundValue.tupleValue [groundList123, GroundValue.nilValue]]

def expectedWholeValue : GroundValue :=
  GroundValue.buildList [GroundValue.tupleValue []]

def expectedCatchAll : GroundValue :=
  GroundValue.buildList [groundList123]

private theorem result_eq_ok_of_ground_projection
    (projected : FuelResult.map Value.toGround? result = .ok (some ground)) :
    result = .ok (Value.ofGround ground) := by
  cases result with
  | timeout => simp [FuelResult.map] at projected
  | stuck => simp [FuelResult.map] at projected
  | ok value =>
      simp only [FuelResult.map, FuelResult.ok.injEq] at projected
      rw [Value.eq_of_toGround?_eq_some projected]

set_option maxRecDepth 100000 in
theorem nil_clause_executes_exact :
    FuelResult.map Value.toGround? (evalFuel 40 [] nilClauseProgram) =
      .ok (some expectedNil) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem nil_clause_nonempty_is_normal_failure :
    FuelResult.map Value.toGround? (evalFuel 40 [] nilClauseFailureProgram) =
      .ok (some GroundValue.nilValue) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem head_only_clause_executes_exact :
    FuelResult.map Value.toGround? (evalFuel 40 [] headOnlyClauseProgram) =
      .ok (some expectedHeads) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem value_cons_clause_executes_exact :
    FuelResult.map Value.toGround? (evalFuel 45 [] valueConsSuccessProgram) =
      .ok (some expectedValueCons) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem value_cons_absence_is_normal_failure :
    FuelResult.map Value.toGround? (evalFuel 45 [] valueConsFailureProgram) =
      .ok (some GroundValue.nilValue) := by
  with_unfolding_all rfl

theorem general_cons_clause_executes_exact :
    evalFuel 30 [] generalConsClauseProgram =
      .ok expectedMultisetCons :=
  multiset_cons_preserves_three_source_order_choices_exact

set_option maxRecDepth 100000 in
theorem join_clause_executes_exact :
    FuelResult.map Value.toGround? (evalFuel 55 [] joinClauseProgram) =
      .ok (some expectedJoin) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem whole_value_clause_executes_exact :
    FuelResult.map Value.toGround? (evalFuel 55 [] wholeValueSuccessProgram) =
      .ok (some expectedWholeValue) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem whole_value_mismatch_is_normal_failure :
    FuelResult.map Value.toGround? (evalFuel 55 [] wholeValueFailureProgram) =
      .ok (some GroundValue.nilValue) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem catch_all_clause_executes_exact :
    FuelResult.map Value.toGround? (evalFuel 40 [] catchAllClauseProgram) =
      .ok (some expectedCatchAll) := by
  with_unfolding_all rfl

theorem nil_clause_result_exact :
    evalFuel 40 [] nilClauseProgram = .ok (Value.ofGround expectedNil) :=
  result_eq_ok_of_ground_projection nil_clause_executes_exact

theorem head_only_clause_result_exact :
    evalFuel 40 [] headOnlyClauseProgram = .ok (Value.ofGround expectedHeads) :=
  result_eq_ok_of_ground_projection head_only_clause_executes_exact

theorem value_cons_clause_result_exact :
    evalFuel 45 [] valueConsSuccessProgram =
      .ok (Value.ofGround expectedValueCons) :=
  result_eq_ok_of_ground_projection value_cons_clause_executes_exact

theorem join_clause_result_exact :
    evalFuel 55 [] joinClauseProgram = .ok (Value.ofGround expectedJoin) :=
  result_eq_ok_of_ground_projection join_clause_executes_exact

theorem whole_value_clause_result_exact :
    evalFuel 55 [] wholeValueSuccessProgram =
      .ok (Value.ofGround expectedWholeValue) :=
  result_eq_ok_of_ground_projection whole_value_clause_executes_exact

theorem catch_all_clause_result_exact :
    evalFuel 40 [] catchAllClauseProgram =
      .ok (Value.ofGround expectedCatchAll) :=
  result_eq_ok_of_ground_projection catch_all_clause_executes_exact

theorem nil_clause_has_independent_derivation :
    Eval [] nilClauseProgram (Value.ofGround expectedNil) :=
  evalFuel_sound nil_clause_result_exact

theorem head_only_clause_has_independent_derivation :
    Eval [] headOnlyClauseProgram (Value.ofGround expectedHeads) :=
  evalFuel_sound head_only_clause_result_exact

theorem value_cons_clause_has_independent_derivation :
    Eval [] valueConsSuccessProgram (Value.ofGround expectedValueCons) :=
  evalFuel_sound value_cons_clause_result_exact

theorem general_cons_clause_has_independent_derivation :
    Eval [] generalConsClauseProgram expectedMultisetCons :=
  multiset_cons_has_independent_derivation

theorem join_clause_has_independent_derivation :
    Eval [] joinClauseProgram (Value.ofGround expectedJoin) :=
  evalFuel_sound join_clause_result_exact

theorem whole_value_clause_has_independent_derivation :
    Eval [] wholeValueSuccessProgram (Value.ofGround expectedWholeValue) :=
  evalFuel_sound whole_value_clause_result_exact

theorem catch_all_clause_has_independent_derivation :
    Eval [] catchAllClauseProgram (Value.ofGround expectedCatchAll) :=
  evalFuel_sound catch_all_clause_result_exact

end TypePM.Runtime.MultisetClauseExecutionRegression
