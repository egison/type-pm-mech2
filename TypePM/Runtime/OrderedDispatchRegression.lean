import TypePM.Runtime.OrderedDispatch

/-!
# Ordered first-success dispatch regressions
-/

namespace TypePM.Runtime.OrderedDispatchRegression

def firstEven (value : Nat) : FuelResult (DispatchResult Nat) :=
  if value % 2 = 0 then .ok (.hit value) else .ok .miss

theorem first_success_preserves_source_order :
    firstHit firstEven [1, 4, 2] = .ok (.hit 4) := by
  rfl

theorem all_misses_are_normal_failure :
    firstHit firstEven [1, 3, 5] = .ok .miss := by
  rfl

def timeoutBeforeLaterHit (value : Nat) :
    FuelResult (DispatchResult Nat) :=
  if value = 1 then .timeout else .ok (.hit value)

theorem timeout_stops_before_later_success :
    firstHit timeoutBeforeLaterHit [1, 2] = .timeout := by
  rfl

def stuckBeforeLaterHit (value : Nat) :
    FuelResult (DispatchResult Nat) :=
  if value = 1 then .stuck else .ok (.hit value)

theorem stuck_stops_before_later_success :
    firstHit stuckBeforeLaterHit [1, 2] = .stuck := by
  rfl

theorem successful_dispatch_has_relational_derivation :
    FirstHit firstEven [1, 4, 2] (.hit 4) := by
  exact firstHit_sound first_success_preserves_source_order

theorem safe_candidate_dispatch_never_stuck (values : List Nat) :
    (firstHit firstEven values).NotStuck := by
  apply firstHit_notStuck
  intro value
  by_cases even : value % 2 = 0 <;>
    simp [firstEven, even, FuelResult.NotStuck]

end TypePM.Runtime.OrderedDispatchRegression
