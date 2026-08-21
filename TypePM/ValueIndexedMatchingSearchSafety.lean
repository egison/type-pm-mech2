import TypePM.StepIndexedClosureSafety

/-!
# Caller-selected value safety for matching answers

Bounded matching has two logically different collections of runtime values:
the fixed matcher environment used as input, and the binding groups returned
as answers.  They need not use the same safety relation or logical index.

This module defines the small relation-parametric result vocabulary shared by
the local-reducer DFS proof and the value-indexed `matchAll` rule.  It does not
assume a complete-search equation.
-/

namespace TypePM.Runtime

/-- A caller-selected relation for one accumulated binding environment or one
completed search answer. -/
abbrev MatchingBindingsInvariant := List Value → List Ty → Prop

namespace MatchingBindingsInvariant

/-- The closure law needed when one reducer step appends immediate bindings
after the bindings already accumulated by the current state. -/
def AppendClosed (bindingsInvariant : MatchingBindingsInvariant) : Prop :=
  ∀ {leftValues leftTypes rightValues rightTypes},
    bindingsInvariant leftValues leftTypes →
      bindingsInvariant rightValues rightTypes →
        bindingsInvariant (leftValues ++ rightValues)
          (leftTypes ++ rightTypes)

theorem valueTypings_appendClosed : AppendClosed ValueTypings := by
  intro leftValues leftTypes rightValues rightTypes left right
  exact left.append right

theorem fuelEnvironmentSafe_appendClosed (fuel : Nat) :
    AppendClosed (FuelEnvironmentSafe fuel) := by
  intro leftValues leftTypes rightValues rightTypes left right
  exact left.append right

end MatchingBindingsInvariant

/-- Every completed answer satisfies the selected binding relation. -/
def MatchingAnswersSafeWith
    (bindingsInvariant : MatchingBindingsInvariant)
    (answers : List (List Value)) (answerTypes : List Ty) : Prop :=
  ∀ answer ∈ answers, bindingsInvariant answer answerTypes

/-- Timeout or completed answers satisfying the selected binding relation. -/
def MatchingSearchResultSafeWith
    (bindingsInvariant : MatchingBindingsInvariant)
    (answerTypes : List Ty) (result : FuelResult (List (List Value))) : Prop :=
  result = .timeout ∨
    ∃ answers, result = .ok answers ∧
      MatchingAnswersSafeWith bindingsInvariant answers answerTypes

theorem MatchingSearchResultSafeWith.notStuck
    (safe : MatchingSearchResultSafeWith bindingsInvariant answerTypes result) :
    result.NotStuck := by
  rcases safe with timeout | ⟨answers, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TypePM.Runtime
