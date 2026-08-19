import TypePM.Runtime.EvaluationCompleteness

/-!
# Core evaluator regressions

The examples exercise every source-expression checkpoint handled by the core
evaluator, all five complete-value primitives, both closure layouts, exact
fuel outcomes, adequacy, completeness, and fuel monotonicity.
-/

namespace TypePM.Runtime.EvaluationRegression

open TypePM.Runtime

set_option linter.unusedSimpArgs false

private def sourceList : List Source.Expr → Source.Expr
  | [] => .ctor DataCtor.nil []
  | head :: tail => .ctor DataCtor.cons [head, sourceList tail]

private def valueList (items : List Value) : Value := Value.buildList items

def identityApplication : Source.Expr :=
  .app (.lam (.var 0)) (.lit 7)

def recursiveSelfApplication : Source.Expr :=
  .app (.fixE (.var 1)) (.lit 5)

def incrementMap : Source.Expr :=
  .prim .map
    [ .lam (.prim .add [.var 0, .lit 1]),
      sourceList [.lit 1, .lit 2, .lit 3] ]

theorem variable_exact :
    evalFuel 1 [.int 9, .int 8] (.var 1) = .ok (.int 8) := by
  rfl

theorem literal_exact : evalFuel 1 [] (.lit 42) = .ok (.int 42) := by
  rfl

theorem something_exact : evalFuel 1 [] .something = .ok .something := by
  rfl

theorem lambda_captures_environment_exact :
    evalFuel 1 [.int 4] (.lam (.var 1)) =
      .ok (Value.plainClosure [.int 4] (.var 1)) := by
  rfl

theorem plain_application_exact :
    evalFuel 3 [] identityApplication = .ok (.int 7) := by
  rfl

theorem tuple_left_to_right_exact :
    evalFuel 2 [] (.tuple [.lit 1, .lit 2]) =
      .ok (.tuple [.int 1, .int 2]) := by
  rfl

theorem let_newest_binding_exact :
    evalFuel 3 [.int 3] (.letE (.lit 9) (.tuple [.var 0, .var 1])) =
      .ok (.tuple [.int 9, .int 3]) := by
  rfl

theorem constructor_arguments_exact :
    evalFuel 2 [] (.ctor DataCtor.cons [.lit 1, .ctor DataCtor.nil []]) =
      .ok (.data DataCtor.cons [.int 1, .data DataCtor.nil []]) := by
  rfl

theorem add_exact :
    evalFuel 2 [] (.prim .add [.lit 20, .lit 22]) = .ok (.int 42) := by
  rfl

theorem append_exact :
    evalFuel 6 []
      (.prim .append [sourceList [.lit 1], sourceList [.lit 2, .lit 3]]) =
      .ok (valueList [.int 1, .int 2, .int 3]) := by
  simp [sourceList, valueList, evalFuel, evalPrimitive, Value.viewList,
    Value.buildList, FuelResult.traverse]

theorem member_exact :
    evalFuel 6 []
      (.prim .member [.lit 2, sourceList [.lit 1, .lit 2, .lit 3]]) =
      .ok (Value.boolValue true) := by
  simp [sourceList, evalFuel, evalPrimitive, Value.viewList,
    Value.buildList, Value.boolValue, Value.memberStructural,
    Value.structuralEq, FuelResult.traverse]

theorem delete_first_preserves_later_duplicate_exact :
    evalFuel 6 []
      (.prim .deleteFirst
        [.lit 1, sourceList [.lit 1, .lit 1, .lit 2]]) =
      .ok (valueList [.int 1, .int 2]) := by
  simp [sourceList, valueList, evalFuel, evalPrimitive, Value.viewList,
    Value.buildList, Value.deleteFirstStructural, Value.structuralEq,
    FuelResult.traverse]

theorem map_applies_closure_left_to_right_exact :
    evalFuel 8 [] incrementMap =
      .ok (valueList [.int 2, .int 3, .int 4]) := by
  simp [incrementMap, sourceList, valueList, evalFuel, evalPrimitive,
    applyFuel, Value.plainClosure, Value.viewList, Value.buildList,
    FuelResult.traverse]

theorem if_true_exact :
    evalFuel 3 []
      (.ifE (.ctor DataCtor.true []) (.lit 1) (.lit 2)) =
      .ok (.int 1) := by
  rfl

theorem if_false_exact :
    evalFuel 3 []
      (.ifE (.ctor DataCtor.false []) (.lit 1) (.lit 2)) =
      .ok (.int 2) := by
  rfl

/-- The recursive body sees its argument at zero and the recursive closure at
one.  This example returns the self value and therefore distinguishes the two
positions. -/
theorem recursive_self_index_exact :
    evalFuel 3 [] recursiveSelfApplication =
      .ok (Value.recursiveClosure [] (.var 1)) := by
  rfl

private def oneClause : Source.MatcherClause :=
  .mk .wild .something [.mk .wild (.lit 0)]

theorem matcher_literal_captures_environment_exact :
    evalFuel 1 [.int 6] (.matcher [oneClause]) =
      .ok (Value.matcherClosure [.int 6] [oneClause]) := by
  rfl

/-- The integrated matching engine evaluates one wildcard result body. -/
theorem matchAll_something_wild_exact :
    evalFuel 5 []
      (.matchAll (.lit 1) .something .wild (.lit 0)) =
        .ok (Value.buildList [.int 0]) := by
  rfl

theorem matchAll_zero_fuel_is_timeout :
    evalFuel 0 []
      (.matchAll (.lit 1) .something .wild (.lit 0)) = .timeout := by
  rfl

theorem map_success_has_relational_derivation :
    Eval [] incrementMap (valueList [.int 2, .int 3, .int 4]) :=
  evalFuel_sound map_applies_closure_left_to_right_exact

theorem identity_success_has_relational_derivation :
    Eval [] identityApplication (.int 7) :=
  evalFuel_sound plain_application_exact

theorem finite_relational_derivation_has_fuel
    (derivation : Eval [] identityApplication (.int 7)) :
    ∃ fuel, evalFuel fuel [] identityApplication = .ok (.int 7) :=
  derivation.complete

theorem identity_success_is_fuel_monotone (extra : Nat) :
    evalFuel (3 + extra) [] identityApplication = .ok (.int 7) :=
  evalFuel_ok_add plain_application_exact extra

/-- Operational normality is the no-`stuck` condition consumed by the later
runtime-typing bridge.  It deliberately permits `timeout`. -/
def CoreNeverStuck
    (environment : ValueEnvironment) (expression : Source.Expr) : Prop :=
  ∀ fuel, (evalFuel fuel environment expression).NotStuck

theorem identity_core_never_stuck : CoreNeverStuck [] identityApplication := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      cases fuel with
      | zero => trivial
      | succ fuel =>
          cases fuel with
          | zero => trivial
          | succ fuel =>
              have success := identity_success_is_fuel_monotone fuel
              rw [show fuel + 1 + 1 + 1 = 3 + fuel by omega, success]
              trivial

end TypePM.Runtime.EvaluationRegression
