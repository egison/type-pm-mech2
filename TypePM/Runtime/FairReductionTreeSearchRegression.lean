import TypePM.Runtime.FairReductionTreeSearch

/-!
# Fair reduction-tree search regressions

The finite node `[leftLoop, rightSuccess]` is the smallest witness separating
ordered depth-first search from fair reduction-tree search.  Depth-first
search keeps expanding `leftLoop` and cannot visit its sibling.  The fair
search splits the node into its left child and right tail in round one, then
visits both in round two.
-/

namespace TypePM.Runtime.FairReductionTreeSearchRegression

open TypePM.Runtime

def leftLoop : Nat := 0
def rightSuccess : Nat := 1

def unfairStep : Nat → FuelResult (SearchStep Nat Nat)
  | 0 => .ok (.expand [0])
  | 1 => .ok (.yield 42)
  | _ => .stuck

/-- No finite depth-first fuel reaches the successful right sibling. -/
theorem depth_first_times_out_for_every_fuel (fuel : Nat) :
    depthFirstFuel unfairStep fuel [leftLoop, rightSuccess] = .timeout := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simpa [depthFirstFuel, unfairStep, leftLoop, rightSuccess] using ih

/-- After exactly two rounds, fair search has observed the right sibling's
answer and retained the infinite left branch as its finite frontier. -/
theorem fair_prefix_observes_right_in_two_rounds :
    fairReductionPrefix unfairStep 2 [leftLoop, rightSuccess] =
      .ok { answers := [42], frontier := [[leftLoop]] } := by
  rfl

theorem fair_prefix_is_still_incomplete :
    ({ answers := [42], frontier := [[leftLoop]] } :
      FairSearchPrefix Nat Nat).isComplete = false := by
  rfl

theorem empty_nodes_count_as_complete :
    ({ answers := [], frontier := [[]] } :
      FairSearchPrefix Nat Nat).isComplete = true := by
  rfl

def multipleNodeStep : Nat → FuelResult (SearchStep Nat Nat)
  | 0 => .ok (.expand [10])
  | 1 => .ok (.expand [11])
  | _ => .stuck

/-- A round collects every generated left node before every copied right
tail, while preserving the order within both groups. -/
theorem all_left_nodes_precede_all_right_nodes :
    fairReductionRound multipleNodeStep [[0, 2], [1, 3]] =
      .ok
        { answers := []
          leftNodes := [[10], [11]]
          rightNodes := [[2], [3]] } := by
  rfl

def ExampleStateSafe (state : Nat) : Prop :=
  state = leftLoop ∨ state = rightSuccess

def ExampleAnswerSafe (answer : Nat) : Prop :=
  answer = 42

theorem unfairStep_preserves_example_safety :
    FairStepPreserves unfairStep ExampleStateSafe ExampleAnswerSafe := by
  intro state observation stateSafe stepped
  rcases stateSafe with left | right
  · subst state
    simp only [leftLoop, unfairStep] at stepped
    cases stepped
    intro candidate member
    simp only [List.mem_singleton] at member
    subst candidate
    exact Or.inl rfl
  · subst state
    simp only [rightSuccess, unfairStep] at stepped
    cases stepped
    rfl

theorem unfairStep_notStuck_on_example_states :
    FairStepNotStuck unfairStep ExampleStateSafe := by
  intro state stateSafe
  rcases stateSafe with left | right
  · subst state
    trivial
  · subst state
    trivial

theorem initial_node_safe :
    AllSafe ExampleStateSafe [leftLoop, rightSuccess] := by
  intro state member
  simpa [ExampleStateSafe] using member

/-- The executable example also instantiates the generic preservation
theorem for both the answer prefix and residual frontier. -/
theorem fair_example_prefix_safe :
    ({ answers := [42], frontier := [[leftLoop]] } :
      FairSearchPrefix Nat Nat).Safe ExampleStateSafe ExampleAnswerSafe := by
  apply fairReductionPrefix_safe unfairStep_preserves_example_safety 2
    initial_node_safe fair_prefix_observes_right_in_two_rounds

/-- Every finite observation of the example is distinct from `stuck`. -/
theorem fair_example_never_stuck (rounds : Nat) :
    (fairReductionPrefix unfairStep rounds
      [leftLoop, rightSuccess]).NotStuck := by
  exact fairReductionPrefix_notStuck unfairStep_preserves_example_safety
    unfairStep_notStuck_on_example_states rounds
    [leftLoop, rightSuccess] initial_node_safe

end TypePM.Runtime.FairReductionTreeSearchRegression
