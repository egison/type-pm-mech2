import TypePM.Runtime.EvaluationCompleteness
import TypePM.Source.M4MatchFirstTyping
import TypePM.Source.PairDestructuring

/-!
# Core single-result match regressions

These examples execute Paper 1's single-result `match` form.  They cover pair
destructuring used by `map`, source-ordered whole-value-style arm selection,
explicit fallback, and the independent relational correspondence.
-/

namespace TypePM.Runtime.MatchFirstRegression

open TypePM.Source

/-- Paper 1 pair destructuring, applied to a tuple.  The body observes the two
projected fields in source order. -/
def pairDestructuringApplication : Source.Expr :=
  .app (Source.Expr.pairDestructuringLambda (.tuple [.var 0, .var 1]))
    (.tuple [.lit 4, .lit 5])

theorem pair_destructuring_executes_exactly :
    evalFuel 30 [] pairDestructuringApplication =
      .ok (.tuple [.int 4, .int 5]) := by
  rfl

theorem pair_destructuring_has_independent_derivation :
    Eval [] pairDestructuringApplication (.tuple [.int 4, .int 5]) :=
  evalFuel_sound pair_destructuring_executes_exactly

/-- The control-flow shape of Paper 1's whole-value clause: a specific first
arm fails, then the next ordinary arm succeeds before the explicit fallback. -/
def wholeValueStyleFallthrough : Source.Expr :=
  .matchFirst (.tuple [.lit 1, .lit 2])
    (.tuple [.something, .something])
    [ .mk (.tuple [.value (.lit 0), .wild]) (.lit 10)
    , .mk (.tuple [.value (.lit 1), .var]) (.tuple [.lit 1, .var 0]) ]
    (.lit 99)

theorem whole_value_style_uses_first_successful_arm :
    evalFuel 5 [] wholeValueStyleFallthrough =
      .ok (.tuple [.int 1, .int 2]) := by
  rfl

/-- When the first arm succeeds, later ordinary arms and the explicit
fallback are not evaluated. -/
def wholeValueStyleFirstArmWins : Source.Expr :=
  .matchFirst (.tuple [.lit 1, .lit 2])
    (.tuple [.something, .something])
    [ .mk (.tuple [.value (.lit 1), .wild]) (.lit 10)
    , .mk (.tuple [.var, .var]) (.lit 20) ]
    (.var 99)

theorem whole_value_style_preserves_source_arm_order :
    evalFuel 5 [] wholeValueStyleFirstArmWins = .ok (.int 10) := by
  rfl

theorem matchFirst_success_has_finite_fuel :
    ∃ fuel, evalFuel fuel [] wholeValueStyleFallthrough =
      .ok (.tuple [.int 1, .int 2]) :=
  (evalFuel_sound whole_value_style_uses_first_successful_arm).complete

theorem empty_runtime_arm_list_uses_fallback :
    evalFuel 3 [] (.matchFirst (.lit 1) .something [] (.lit 9)) =
      .ok (.int 9) := by
  rfl

/-- The fallback does not bypass call-by-value evaluation of the target. -/
theorem target_stuck_precedes_fallback :
    evalFuel 3 [] (.matchFirst (.var 0) .something [] (.lit 9)) = .stuck := by
  rfl

/-- After a successful target, matcher evaluation still precedes arm
exhaustion and fallback evaluation. -/
theorem matcher_stuck_precedes_fallback :
    evalFuel 3 [] (.matchFirst (.lit 1) (.var 0) [] (.lit 9)) = .stuck := by
  rfl

theorem matching_timeout_propagates :
    evalFuel 1 []
      (.matchFirst (.lit 1) .something [.mk .wild (.lit 0)] (.lit 9)) =
        .timeout := by
  rfl

theorem selected_body_stuck_propagates :
    evalFuel 4 []
      (.matchFirst (.lit 1) .something [.mk .wild (.var 0)] (.lit 9)) =
        .stuck := by
  rfl

/-- A user matcher may return zero decompositions even for a wildcard arm.
Arm exhaustion selects the explicit fallback, evaluated in the original
environment rather than under any pattern bindings. -/
def noDecompositions : Source.Expr := .ctor DataCtor.nil []

def emptyMatcherClause : Source.MatcherClause :=
  .mk .hole .something [.mk .var noDecompositions]

def emptyUserMatcher : Source.Expr := .matcher [emptyMatcherClause]

theorem zero_decomposition_wildcard_selects_else_in_original_environment :
    evalFuel 21 [.int 7]
      (.matchFirst (.lit 0) emptyUserMatcher [.mk .wild (.lit 42)] (.var 0)) =
        .ok (.int 7) := by
  with_unfolding_all rfl

end TypePM.Runtime.MatchFirstRegression
