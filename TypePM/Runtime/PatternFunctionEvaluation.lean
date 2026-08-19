import TypePM.Runtime.EvaluationCompleteness
import TypePM.Source.PatternFunctionExpansion

/-!
# Evaluation after checked inline pattern-function expansion

Inline-safe pattern functions are a source-level elaboration feature, not a
second evaluator primitive.  The complete source tree is expanded first and
then evaluated by the ordinary M5 relation and fuel-bounded evaluator.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Fuel-bounded execution through the checked inline expansion boundary. -/
def evalPatternFunctionsFuel
    (definitions : PatternFunctionDefinitions) (fuel : Nat)
    (environment : ValueEnvironment) (expression : Source.Expr) : FuelResult Value :=
  match PatternFunctionExpansion.expandExpr definitions expression with
  | none => .stuck
  | some expanded => evalFuel fuel environment expanded

/-- Independent relational meaning of successful inline expansion followed
by ordinary evaluation. -/
inductive EvalPatternFunctions
    (definitions : PatternFunctionDefinitions) :
    ValueEnvironment → Source.Expr → Value → Prop where
  | expanded
      (expansion :
        PatternFunctionExpansion.expandExpr definitions expression =
          some expanded)
      (evaluation : Eval environment expanded value) :
      EvalPatternFunctions definitions environment expression value

theorem evalPatternFunctionsFuel_sound
    {definitions : PatternFunctionDefinitions} {fuel : Nat}
    {environment : ValueEnvironment} {expression : Source.Expr} {value : Value}
    (success :
      evalPatternFunctionsFuel definitions fuel environment expression =
        .ok value) :
    EvalPatternFunctions definitions environment expression value := by
  unfold evalPatternFunctionsFuel at success
  cases expansion : PatternFunctionExpansion.expandExpr definitions expression with
  | none => simp [expansion] at success
  | some expanded =>
      exact .expanded expansion (evalFuel_sound (by simpa [expansion] using success))

theorem EvalPatternFunctions.complete
    {definitions : PatternFunctionDefinitions}
    {environment : ValueEnvironment} {expression : Source.Expr} {value : Value}
    (derivation : EvalPatternFunctions definitions environment expression value) :
    ∃ fuel,
      evalPatternFunctionsFuel definitions fuel environment expression =
        .ok value := by
  cases derivation with
  | expanded expansion evaluation =>
      obtain ⟨fuel, success⟩ := evaluation.complete
      exact ⟨fuel, by simp [evalPatternFunctionsFuel, expansion, success]⟩

theorem evalPatternFunctionsFuel_ok_of_le
    {definitions : PatternFunctionDefinitions}
    {firstFuel secondFuel : Nat} {environment : ValueEnvironment}
    {expression : Source.Expr} {value : Value}
    (le : firstFuel ≤ secondFuel)
    (success :
      evalPatternFunctionsFuel definitions firstFuel environment expression =
        .ok value) :
    evalPatternFunctionsFuel definitions secondFuel environment expression =
      .ok value := by
  unfold evalPatternFunctionsFuel at success ⊢
  cases expansion : PatternFunctionExpansion.expandExpr definitions expression with
  | none => simp [expansion] at success
  | some expanded =>
      have oldSuccess : evalFuel firstFuel environment expanded = .ok value := by
        simpa only [expansion] using success
      exact evalFuel_ok_of_le le oldSuccess

end TypePM.Runtime
