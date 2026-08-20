import TypePM.Runtime.GroundPrimitiveAdequacy

/-!
# Ground primitive regressions

These exact results cover the primitive behavior used by the paper's
user-defined multiset matcher.  They do not claim end-to-end expression or
matcher evaluation.
-/

namespace TypePM.Runtime.GroundPrimitiveRegression

open GroundValue FuelResult GroundPrimitive

private def integer (value : Int) : GroundValue := .int value

private def integers (items : List Int) : GroundValue :=
  buildList (items.map integer)

private def increment : GroundValue → FuelResult GroundValue
  | .int value => .ok (.int (value + 1))
  | _ => .stuck

theorem bool_true_encoding_exact :
    ofBool true = dataValue DataCtor.true [] := by
  rfl

theorem bool_false_encoding_exact :
    ofBool false = dataValue DataCtor.false [] := by
  rfl

theorem bool_views_exact :
    (viewBool (ofBool true), viewBool (ofBool false)) =
      (some true, some false) := by
  rfl

theorem list_encoding_exact :
    integers [1, 2] =
      consValue (.int 1) (consValue (.int 2) nilValue) := by
  rfl

theorem list_view_exact :
    (integers [1, 2]).viewList = some [.int 1, .int 2] := by
  simp [integers, integer]

/-- An improper `cons` tail is rejected instead of being assigned an
arbitrary list meaning. -/
theorem malformed_list_view_fails :
    (consValue (.int 1) (.int 2)).viewList = none := by
  simp [consValue, dataValue, GroundValues.ofList, viewList]

theorem add_exact :
    evalAdd [.int 20, .int 22] = .ok (.int 42) := by
  rfl

theorem append_exact :
    evalAppend [integers [1, 2], integers [3, 4]] =
      .ok (integers [1, 2, 3, 4]) := by
  simp [evalAppend, integers, integer]

theorem member_present_is_true :
    evalMember [.int 2, integers [1, 2, 3]] = .ok (ofBool true) := by
  simp [evalMember, integers, integer, ofBool]

/-- Absence is an ordinary Boolean result, not `stuck`.  The paper's matcher
clause turns this `false` into an empty list of matching alternatives. -/
theorem member_absent_is_false :
    evalMember [.int 4, integers [1, 2, 3]] = .ok (ofBool false) := by
  simp [evalMember, integers, integer, ofBool]

/-- Only the first of the duplicate occurrences is removed. -/
theorem deleteFirst_duplicate_exact :
    evalDeleteFirst [.int 1, integers [2, 1, 1, 3]] =
      .ok (integers [2, 1, 3]) := by
  simp [evalDeleteFirst, integers, integer, deleteFirst?]

theorem deleteFirst_absent_unchanged :
    evalDeleteFirst [.int 4, integers [1, 2, 3]] =
      .ok (integers [1, 2, 3]) := by
  simp [evalDeleteFirst, integers, integer, deleteFirst?]

theorem map_preserves_order :
    evalMap increment [integers [1, 2, 3]] =
      .ok (integers [2, 3, 4]) := by
  simp [evalMap, integers, integer, increment, FuelResult.traverse,
    FuelResult.bind, FuelResult.map]

theorem map_order_relational :
    Maps increment [integers [1, 2, 3]] (integers [2, 3, 4]) :=
  evalMap_adequate map_preserves_order

theorem pair_first_exact :
    evalPairFirst [tupleValue [.int 3, .int 4]] = .ok (.int 3) := by
  rfl

theorem pair_second_exact :
    evalPairSecond [tupleValue [.int 3, .int 4]] = .ok (.int 4) := by
  rfl

theorem pair_first_relational :
    ProjectsFirst [tupleValue [.int 3, .int 4]] (.int 3) :=
  evalPairFirst_adequate pair_first_exact

theorem pair_second_relational :
    ProjectsSecond [tupleValue [.int 3, .int 4]] (.int 4) :=
  evalPairSecond_adequate pair_second_exact

/-- Wrong primitive arity is an explicit rule-coverage failure. -/
theorem add_wrong_arity_stuck :
    evalAdd [.int 1] = .stuck := by
  rfl

/-- A list primitive rejects a well-formed ground value of the wrong shape. -/
theorem append_non_list_stuck :
    evalAppend [.int 1, integers [2]] = .stuck := by
  simp [evalAppend, integers, integer, viewList]

theorem pair_projection_wrong_shape_stuck :
    evalPairFirst [tupleValue [.int 1]] = .stuck := by
  rfl

/-- Callback failure stops `map` at that element. -/
theorem map_callback_stuck_propagates :
    evalMap (fun value => if value = (.int 2 : GroundValue) then .stuck
      else .ok value) [integers [1, 2, 3]] = .stuck := by
  simp [evalMap, integers, integer, FuelResult.traverse,
    FuelResult.bind, FuelResult.map]

/-- Fuel exhaustion remains distinct from malformed primitive input. -/
theorem map_callback_timeout_propagates :
    evalMap (fun value => if value = (.int 2 : GroundValue) then .timeout
      else .ok value) [integers [1, 2, 3]] = .timeout := by
  simp [evalMap, integers, integer, FuelResult.traverse,
    FuelResult.bind, FuelResult.map]

end TypePM.Runtime.GroundPrimitiveRegression
