import TypePM.Runtime.MatchingState

/-!
# Syntax-directed matching atom regressions
-/

namespace TypePM.Runtime.MatchingStateRegression

open TypePM.Source

def literalEval (_ : ValueEnvironment) : Expr → FuelResult Value
  | .lit value => .ok (.int value)
  | _ => .stuck

def one : Value := .int 1
def two : Value := .int 2

theorem something_wildcard_succeeds_once :
    reduceBuiltinAtom literalEval [] ⟨.wild, .something, one⟩ =
      .ok (.hit ⟨[[]], []⟩) := by
  rfl

theorem something_variable_binds_target :
    reduceBuiltinAtom literalEval [] ⟨.var, .something, one⟩ =
      .ok (.hit ⟨[[]], [one]⟩) := by
  rfl

theorem something_value_success_exact :
    reduceBuiltinAtom literalEval []
        ⟨.value (.lit 1), .something, one⟩ =
      .ok (.hit ⟨[[]], []⟩) := by
  rfl

theorem something_value_mismatch_is_normal_failure :
    reduceBuiltinAtom literalEval []
        ⟨.value (.lit 1), .something, two⟩ =
      .ok (.hit ⟨[], []⟩) := by
  rfl

theorem value_pattern_does_not_equal_closure :
    let closure := Value.plainClosure [] (.var 0)
    reduceBuiltinAtom
        (fun _ _ => .ok closure) []
        ⟨.value (.lit 0), .something, closure⟩ =
      .ok (.hit ⟨[], []⟩) := by
  rfl

theorem tuple_children_preserve_source_order :
    reduceBuiltinAtom literalEval []
        ⟨.tuple [.var, .wild], .tuple [.something, .something],
          .tuple [one, two]⟩ =
      .ok
        (.hit
          ⟨[ [⟨.var, .something, one⟩,
                ⟨.wild, .something, two⟩] ], []⟩) := by
  rfl

theorem tuple_arity_mismatch_is_unhandled :
    reduceBuiltinAtom literalEval []
        ⟨.tuple [.var], .tuple [.something, .something],
          .tuple [one, two]⟩ =
      .ok .miss := by
  rfl

theorem product_matcher_delegates_scalar_pattern_once :
    reduceBuiltinAtom literalEval []
        ⟨.var, .tuple [.something, .something], one⟩ =
      .ok
        (.hit ⟨[[⟨.var, .something, one⟩]], []⟩) := by
  rfl

theorem builtin_success_has_relational_rule :
    BuiltinAtomReduces literalEval []
      ⟨.tuple [.var, .wild], .tuple [.something, .something],
        .tuple [one, two]⟩
      ⟨[[⟨.var, .something, one⟩,
          ⟨.wild, .something, two⟩]], []⟩ := by
  exact reduceBuiltinAtom_hit_sound tuple_children_preserve_source_order

end TypePM.Runtime.MatchingStateRegression
