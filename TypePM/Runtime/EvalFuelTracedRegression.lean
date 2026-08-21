import TypePM.Runtime.EvalFuelTraced

/-!
# Regression checks for the trace-preserving evaluator

These examples fix the operational points that motivated the trace boundary:
one direct match, one selected `matchFirst` arm, and a match reached through a
closure body with its actual argument environment.
-/

namespace TypePM.Runtime.EvalFuelTracedRegression

open TypePM.Source

def directMatch : Expr :=
  .matchAll (.lit 1) .something .wild (.lit 2)

theorem directMatch_result_projection :
    (evalFuelTraced 2 [] directMatch).1 = evalFuel 2 [] directMatch :=
  rfl

theorem directMatch_trace :
    evalFuelTrace 2 [] directMatch =
      [⟨1, [], .wild, .something, .int 1⟩] := by
  rfl

def firstMatch : Expr :=
  .matchFirst (.lit 1) .something
    [.mk .wild (.lit 2), .mk .wild (.lit 3)] (.lit 4)

/-- The second arm is not recorded after the first arm succeeds. -/
theorem firstMatch_trace_stops_at_selected_arm :
    evalFuelTrace 2 [] firstMatch =
      [⟨1, [], .wild, .something, .int 1⟩] := by
  rfl

def closureBodyMatch : Expr :=
  .app (.lam (.matchAll (.var 0) .something .wild (.lit 2))) (.lit 7)

/-- A search reached through application records the closure body's actual
runtime environment, including the evaluated argument. -/
theorem closureBodyMatch_trace_environment :
    evalFuelTrace 4 [] closureBodyMatch =
      [⟨1, [.int 7], .wild, .something, .int 7⟩] := by
  rfl

def openVariableClosureBodyMatch : Expr :=
  .app (.var 0) (.lit 7)

/-- An open expression whose syntax contains no matching form can still emit
a search event when its runtime environment supplies a closure with a matching
body.  Consequently, open-context trace completeness needs a provenance-aware
value/environment relation; expression syntax alone is insufficient. -/
theorem openVariableClosureBodyMatch_trace_from_environment :
    evalFuelTrace 4
        [.plainClosure []
          (.matchAll (.var 0) .something .wild (.lit 2))]
        openVariableClosureBodyMatch =
      [⟨1, [.int 7], .wild, .something, .int 7⟩] := by
  rfl

end TypePM.Runtime.EvalFuelTracedRegression
