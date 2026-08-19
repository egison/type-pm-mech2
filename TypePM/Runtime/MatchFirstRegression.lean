import TypePM.Runtime.EvaluationCompleteness
import TypePM.Source.M4MatchFirstTyping

/-!
# Derived single-result match regressions

These examples execute Paper 1's derived `match` form.  They cover the tuple
pattern lambda used by `map`, source-ordered whole-value-style arm selection,
and the independent relational correspondence.
-/

namespace TypePM.Runtime.MatchFirstRegression

open TypePM.Source

/-- Paper 1 tuple-pattern lambda, applied to a tuple.  The body observes the
two pattern bindings in source order. -/
def tuplePatternLambdaApplication : Source.Expr :=
  .app (Source.Expr.tuplePatternLambda (.tuple [.var 0, .var 1]))
    (.tuple [.lit 4, .lit 5])

theorem tuple_pattern_lambda_executes_exactly :
    evalFuel 30 [] tuplePatternLambdaApplication =
      .ok (.tuple [.int 4, .int 5]) := by
  rfl

theorem tuple_pattern_lambda_has_independent_derivation :
    Eval [] tuplePatternLambdaApplication (.tuple [.int 4, .int 5]) :=
  evalFuel_sound tuple_pattern_lambda_executes_exactly

/-- The control-flow shape of Paper 1's whole-value clause: a specific first
arm fails, then the next (irrefutable) tuple arm succeeds. -/
def wholeValueStyleFallthrough : Source.Expr :=
  .matchFirst (.tuple [.lit 1, .lit 2])
    (.tuple [.something, .something])
    [ .mk (.tuple [.value (.lit 0), .wild]) (.lit 10)
    , .mk (.tuple [.value (.lit 1), .var]) (.tuple [.lit 1, .var 0])
    , .mk (.tuple [.wild, .wild]) (.lit 99) ]

theorem whole_value_style_uses_first_successful_arm :
    evalFuel 5 [] wholeValueStyleFallthrough =
      .ok (.tuple [.int 1, .int 2]) := by
  rfl

/-- When the first arm succeeds, a later irrefutable arm is not evaluated. -/
def wholeValueStyleFirstArmWins : Source.Expr :=
  .matchFirst (.tuple [.lit 1, .lit 2])
    (.tuple [.something, .something])
    [ .mk (.tuple [.value (.lit 1), .wild]) (.lit 10)
    , .mk (.tuple [.var, .var]) (.lit 20) ]

theorem whole_value_style_preserves_source_arm_order :
    evalFuel 5 [] wholeValueStyleFirstArmWins = .ok (.int 10) := by
  rfl

theorem matchFirst_success_has_finite_fuel :
    ∃ fuel, evalFuel fuel [] wholeValueStyleFallthrough =
      .ok (.tuple [.int 1, .int 2]) :=
  (evalFuel_sound whole_value_style_uses_first_successful_arm).complete

theorem empty_runtime_arm_list_is_stuck :
    evalFuel 3 [] (.matchFirst (.lit 1) .something []) = .stuck := by
  rfl

theorem matching_timeout_propagates :
    evalFuel 1 []
      (.matchFirst (.lit 1) .something [.mk .wild (.lit 0)]) = .timeout := by
  rfl

theorem selected_body_stuck_propagates :
    evalFuel 4 []
      (.matchFirst (.lit 1) .something [.mk .wild (.var 0)]) = .stuck := by
  rfl

end TypePM.Runtime.MatchFirstRegression
