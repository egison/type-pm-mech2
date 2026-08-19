import TypePM.Runtime.CombinedAtomReducer

/-!
# Ordered atom-reducer composition regressions
-/

namespace TypePM.Runtime.CombinedAtomReducerRegression

open TypePM.Source

def atom : MatchingAtom := ⟨.wild, .something, .int 1⟩
def success : AtomReduction := ⟨[[]], []⟩
def failure : AtomReduction := ⟨[], []⟩

def misses : AtomReducer := fun _ _ => .ok .miss
def succeeds : AtomReducer := fun _ _ => .ok (.hit success)
def failsNormally : AtomReducer := fun _ _ => .ok (.hit failure)
def timesOut : AtomReducer := fun _ _ => .timeout
def getsStuck : AtomReducer := fun _ _ => .stuck

theorem miss_falls_through_to_fallback :
    combineAtomReducers misses succeeds [] atom =
      .ok (.hit success) := by
  rfl

theorem first_hit_suppresses_stuck_fallback :
    combineAtomReducers succeeds getsStuck [] atom =
      .ok (.hit success) := by
  rfl

theorem normal_failure_is_a_hit_and_does_not_fall_through :
    combineAtomReducers failsNormally succeeds [] atom =
      .ok (.hit failure) := by
  rfl

theorem timeout_is_not_hidden_by_later_success :
    combineAtomReducers timesOut succeeds [] atom = .timeout := by
  rfl

theorem stuck_is_not_hidden_by_later_success :
    combineAtomReducers getsStuck succeeds [] atom = .stuck := by
  rfl

def totalFailure : AtomReducer := fun _ _ => .ok (.hit failure)

theorem combined_total :
    AtomReducerTotal (combineAtomReducers misses totalFailure) := by
  exact combineAtomReducers_total _ _ (by simp [AtomReducerTotal, totalFailure])

theorem combined_search_normal_failure_exact :
    searchMatchingFuel (combineAtomReducers misses totalFailure) 1
        ⟨[atom], [], []⟩ = .ok [] := by
  rfl

end TypePM.Runtime.CombinedAtomReducerRegression
