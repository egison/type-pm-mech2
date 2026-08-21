import TypePM.Runtime.FairReductionTreeCompleteness

/-!
# Independent finite-fairness regression

This regression reconstructs the starving-right-sibling example using the
independent binary-tree relations, then obtains finite observation from the
general theorem rather than by reducing the executable expression directly.
-/

namespace TypePM.Runtime.FairReductionTreeCompletenessRegression

open TypePM.Runtime

def completeStep : Nat → FuelResult (SearchStep Nat Nat)
  | 0 => .ok (.expand [0])
  | 1 => .ok (.yield 42)
  | _ => .ok (.expand [])

def rootNode : List Nat := [0, 1]

theorem root_reachable :
    ReductionTreeReachable completeStep rootNode 0 rootNode := by
  exact .root (by decide)

theorem successful_sibling_is_right_child :
    ReductionRightChild rootNode [1] := by
  exact ⟨0, [1], rfl, by decide, rfl⟩

theorem successful_sibling_reachable_at_depth_one :
    ReductionTreeReachable completeStep rootNode 1 [1] := by
  simpa using ReductionTreeReachable.next root_reachable
    (Or.inr successful_sibling_is_right_child)

theorem right_answer_yield :
    ReductionTreeYields completeStep rootNode 1 42 := by
  exact ⟨1, [], successful_sibling_reachable_at_depth_one, rfl⟩

theorem reachable_steps_complete_through_one :
    ReachableStepsComplete completeStep rootNode 1 := by
  intro depth depthBound state tail reachable
  cases state with
  | zero => exact ⟨.expand [0], rfl⟩
  | succ state =>
      cases state with
      | zero => exact ⟨.yield 42, rfl⟩
      | succ state => exact ⟨.expand [], rfl⟩

/-- The independent depth-one yield is guaranteed to occur in the prefix
after two rounds. -/
theorem general_fairness_observes_right_sibling :
    ∃ output,
      fairReductionPrefix completeStep 2 rootNode = .ok output ∧
      42 ∈ output.answers := by
  exact reductionTreeYield_eventually_observed
    reachable_steps_complete_through_one right_answer_yield

theorem general_fairness_result_is_exact :
    fairReductionPrefix completeStep 2 rootNode =
      .ok { answers := [42], frontier := [[0]] } := by
  rfl

end TypePM.Runtime.FairReductionTreeCompletenessRegression
