import TypePM.Runtime.ValueDataPattern

/-!
# Runtime-value data-pattern regressions
-/

namespace TypePM.Runtime.ValueDataPatternRegression

open TypePM.Source

def closureValue : Value := Value.plainClosure [.int 9] (.var 0)
def matcherValue : Value := Value.matcherClosure [] []

def list12 : Value :=
  .data DataCtor.cons
    [.int 1, .data DataCtor.cons [.int 2, .data DataCtor.nil []]]

theorem variable_binds_closure :
    matchValueDataPattern .var closureValue = some [closureValue] := by
  rfl

theorem wildcard_ignores_matcher :
    matchValueDataPattern .wild matcherValue = some [] := by
  rfl

theorem constructor_does_not_destructure_closure :
    matchValueDataPattern (.ctor DataCtor.nil []) closureValue = none := by
  rfl

theorem cons_bindings_preserve_source_order :
    matchValueDataPattern (.ctor DataCtor.cons [.var, .var]) list12 =
      some
        [.int 1,
          .data DataCtor.cons [.int 2, .data DataCtor.nil []]] := by
  rfl

theorem tuple_may_bind_non_ground_values :
    matchValueDataPattern (.tuple [.var, .wild, .var])
        (.tuple [closureValue, .something, matcherValue]) =
      some [closureValue, matcherValue] := by
  rfl

theorem constructor_arity_mismatch_is_failure :
    matchValueDataPattern (.ctor DataCtor.cons [.var]) list12 = none := by
  rfl

theorem tuple_arity_mismatch_is_failure :
    matchValueDataPattern (.tuple [.var]) (.tuple [.int 1, .int 2]) =
      none := by
  rfl

theorem full_value_match_has_relational_derivation :
    ValueDataPatternMatches (.tuple [.var, .wild, .var])
      (.tuple [closureValue, .something, matcherValue])
      [closureValue, matcherValue] := by
  exact matchValueDataPattern_sound tuple_may_bind_non_ground_values

end TypePM.Runtime.ValueDataPatternRegression
