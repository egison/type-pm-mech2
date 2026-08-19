import TypePM.Runtime.ValueShape

/-!
# Runtime list and product convention regressions
-/

namespace TypePM.Runtime.ValueShapeRegression

def one : Value := .int 1
def two : Value := .int 2

theorem arbitrary_values_roundtrip_through_list :
    Value.viewList
      (Value.buildList
        [one, Value.plainClosure [] (.var 0), .something]) =
      some [one, Value.plainClosure [] (.var 0), .something] := by
  exact Value.viewList_buildList _

theorem zero_holes_require_unit_tuple :
    decodeProduct 0 (.tuple []) = some [] ∧
      decodeProduct 0 one = none := by
  exact ⟨rfl, rfl⟩

theorem one_hole_uses_scalar :
    decodeProduct 1 one = some [one] := by
  rfl

theorem two_holes_require_exact_tuple :
    decodeProduct 2 (.tuple [one, two]) = some [one, two] ∧
      decodeProduct 2 (.tuple [one]) = none ∧
      decodeProduct 2 one = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem decomposition_order_exact :
    decodeDecompositions 2
        (Value.buildList [.tuple [one, two], .tuple [two, one]]) =
      some [[one, two], [two, one]] := by
  simp [decodeDecompositions, decodeProduct]

theorem malformed_decomposition_element_rejected :
    decodeDecompositions 2
        (Value.buildList [.tuple [one, two], .tuple [one]]) = none := by
  simp [decodeDecompositions, decodeProduct]

theorem improper_list_rejected :
    Value.viewList (.data DataCtor.cons [one, two]) = none := by
  simp [Value.viewList, DataCtor.cons, one, two]

end TypePM.Runtime.ValueShapeRegression
