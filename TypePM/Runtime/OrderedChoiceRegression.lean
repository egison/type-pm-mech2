import TypePM.Runtime.OrderedChoice

/-!
# Regressions for ordered matching choices

These examples freeze the branch order needed by the general-cons and join
clauses of the paper's multiset matcher.  They test the decomposition
helpers, not yet the complete matcher evaluator.
-/

namespace TypePM.Runtime.OrderedChoiceRegression

theorem choose_three_exact :
    chooseOne [1, 2, 3] =
      [(1, [2, 3]), (2, [1, 3]), (3, [1, 2])] := by
  rfl

/-- Equal values at different input positions remain separate branches. -/
theorem choose_duplicate_positions_preserved :
    chooseOne [1, 1] = [(1, [1]), (1, [1])] := by
  rfl

theorem split_empty_exact :
    splitAll ([] : List Nat) = [([], [])] := by
  rfl

theorem split_three_exact :
    splitAll [1, 2, 3] =
      [ ([], [1, 2, 3]),
        ([3], [1, 2]),
        ([2], [1, 3]),
        ([2, 3], [1]),
        ([1], [2, 3]),
        ([1, 3], [2]),
        ([1, 2], [3]),
        ([1, 2, 3], []) ] := by
  rfl

/-- Equal-position choices are not collapsed even when the resulting pairs
are extensionally equal as lists. -/
theorem split_duplicate_positions_preserved :
    splitAll [1, 1] =
      [([], [1, 1]), ([1], [1]), ([1], [1]), ([1, 1], [])] := by
  rfl

theorem delete_first_exact :
    deleteFirst? 1 [2, 1, 1, 3] = some [2, 1, 3] := by
  rfl

theorem choose_value_present_once :
    chooseValue 1 [2, 1, 1, 3] = [[2, 1, 3]] := by
  rfl

theorem choose_value_absent :
    chooseValue 4 [2, 1, 1, 3] = [] := by
  rfl

theorem choose_length_three : (chooseOne [1, 2, 3]).length = 3 := by
  exact chooseOne_length [1, 2, 3]

theorem split_length_three : (splitAll [1, 2, 3]).length = 8 := by
  exact splitAll_length [1, 2, 3]

end TypePM.Runtime.OrderedChoiceRegression
