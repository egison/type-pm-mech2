import TypePM.Runtime.DataPattern

/-!
# Ground data-pattern matching regressions

These examples cover the data-pattern arm shapes used by the seven-clause
multiset matcher: empty and nonempty lists, tuple decomposition, variables,
wildcards, exact constructor identity, and exact arity.
-/

namespace TypePM.Runtime.DataPatternRegression

open TypePM.Source

def one : GroundValue := .int 1
def two : GroundValue := .int 2
def three : GroundValue := .int 3

def list12 : GroundValue := GroundValue.buildList [one, two]

def consArm : DPat :=
  .ctor DataCtor.cons [.var, .var]

def tupleListArm : DPat :=
  .tuple [.var, .ctor DataCtor.cons [.var, .var]]

theorem nil_arm_matches_empty_exact :
    matchDataPattern (.ctor DataCtor.nil []) GroundValue.nilValue =
      some [] := by
  rfl

theorem cons_arm_bindings_source_order :
    matchDataPattern consArm list12 =
      some [one, GroundValue.buildList [two]] := by
  rfl

theorem tuple_arm_bindings_source_order :
    matchDataPattern tupleListArm
        (GroundValue.tupleValue [three, list12]) =
      some [three, one, GroundValue.buildList [two]] := by
  rfl

theorem wildcard_ignores_value :
    matchDataPattern .wild list12 = some [] := by
  rfl

theorem variable_binds_whole_value :
    matchDataPattern .var list12 = some [list12] := by
  rfl

theorem constructor_mismatch_rejected :
    matchDataPattern (.ctor DataCtor.nil [])
      GroundValue.trueValue = none := by
  rfl

theorem constructor_arity_mismatch_rejected :
    matchDataPattern (.ctor DataCtor.cons [.var]) list12 = none := by
  rfl

theorem tuple_arity_mismatch_rejected :
    matchDataPattern (.tuple [.var])
      (GroundValue.tupleValue [one, two]) = none := by
  rfl

theorem tuple_arm_has_relational_derivation :
    DataPatternMatches tupleListArm
      (GroundValue.tupleValue [three, list12])
      [three, one, GroundValue.buildList [two]] := by
  exact matchDataPattern_sound tuple_arm_bindings_source_order

end TypePM.Runtime.DataPatternRegression
