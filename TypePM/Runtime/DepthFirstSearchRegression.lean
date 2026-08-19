import TypePM.Runtime.DepthFirstSearch

/-!
# Ordered depth-first search regressions
-/

namespace TypePM.Runtime.DepthFirstSearchRegression

open TypePM.Runtime

def exampleStep : Nat → FuelResult (SearchStep Nat Nat)
  | 0 => .ok (.expand [1, 2])
  | 1 => .ok (.expand [])
  | 2 => .ok (.expand [3, 4])
  | 3 => .ok (.yield 30)
  | 4 => .ok (.yield 40)
  | _ => .stuck

theorem depth_first_order_exact :
    depthFirstFuel exampleStep 5 [0] = .ok [30, 40] := by
  rfl

theorem one_less_fuel_times_out :
    depthFirstFuel exampleStep 4 [0] = .timeout := by
  rfl

theorem mismatch_continues_with_sibling :
    depthFirstFuel exampleStep 4 [1, 2] = .ok [30, 40] := by
  rfl

theorem successful_run_has_relational_derivation :
    DepthFirst exampleStep [0] [30, 40] := by
  exact depthFirstFuel_sound exampleStep depth_first_order_exact

def stuckStep : Nat → FuelResult (SearchStep Nat Nat)
  | 0 => .ok (.expand [9])
  | _ => .stuck

theorem stuck_is_not_timeout :
    depthFirstFuel stuckStep 2 [0] = .stuck := by
  rfl

def safeStep : Nat → FuelResult (SearchStep Nat Nat)
  | 0 => .ok (.expand [1, 2])
  | value => .ok (.yield value)

theorem safe_search_never_stuck (fuel : Nat) (states : List Nat) :
    (depthFirstFuel safeStep fuel states).NotStuck := by
  apply depthFirstFuel_notStuck
  intro state
  cases state <;> trivial

end TypePM.Runtime.DepthFirstSearchRegression
