import TypePM.Runtime.FuelResult

/-!
# Regressions for fuel-result propagation
-/

namespace TypePM.Runtime.FuelResultRegression

open FuelResult

private def increment (value : Nat) : FuelResult Nat := .ok (value + 1)

theorem traverse_success_exact :
    traverse increment [1, 2, 3] = .ok [2, 3, 4] := by
  rfl

theorem traverse_timeout_stops :
    traverse (fun value : Nat => if value = 2 then .timeout else .ok value)
      [1, 2, 3] = .timeout := by
  rfl

theorem traverse_stuck_distinct_from_timeout :
    traverse (fun value : Nat => if value = 2 then .stuck else .ok value)
      [1, 2, 3] = .stuck := by
  rfl

theorem success_relational_exact :
    Traverses increment [1, 2, 3] [2, 3, 4] :=
  (traverse_eq_ok_iff increment [1, 2, 3] [2, 3, 4]).mp
    traverse_success_exact

theorem success_notStuck :
    (traverse increment [1, 2, 3]).NotStuck := by
  apply traverse_notStuck
  intro value
  trivial

end TypePM.Runtime.FuelResultRegression
