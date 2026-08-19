import TypePM.Runtime.FuelResult

/-!
# Ordered first-success dispatch

Matcher clauses and their data-pattern arms are tried in source order.  A
normal mismatch continues to the next candidate, while `timeout` and `stuck`
stop dispatch immediately.  This module fixes that control-flow contract
independently of the eventual clause and value representations.
-/

namespace TypePM.Runtime

/-- A candidate either fails normally or supplies the selected result. -/
inductive DispatchResult (α : Type u) where
  | miss
  | hit (value : α)
deriving Repr, DecidableEq

/-- Try candidates in source order and stop at the first successful one. -/
def firstHit
    (tryOne : Candidate → FuelResult (DispatchResult Result)) :
    List Candidate → FuelResult (DispatchResult Result)
  | [] => .ok .miss
  | candidate :: rest =>
      FuelResult.bind (tryOne candidate) fun outcome =>
        match outcome with
        | .hit result => .ok (.hit result)
        | .miss => firstHit tryOne rest

/-- Independent relation for a completed ordered dispatch. -/
inductive FirstHit
    (tryOne : Candidate → FuelResult (DispatchResult Result)) :
    List Candidate → DispatchResult Result → Prop where
  | nil : FirstHit tryOne [] .miss
  | hit
      (selected : tryOne candidate = .ok (.hit result)) :
      FirstHit tryOne (candidate :: rest) (.hit result)
  | skip
      (missed : tryOne candidate = .ok .miss)
      (tail : FirstHit tryOne rest result) :
      FirstHit tryOne (candidate :: rest) result

/-- Successful execution has exactly the corresponding ordered derivation. -/
theorem firstHit_sound
    {tryOne : Candidate → FuelResult (DispatchResult Result)}
    {candidates : List Candidate} {result : DispatchResult Result}
    (success : firstHit tryOne candidates = .ok result) :
    FirstHit tryOne candidates result := by
  induction candidates generalizing result with
  | nil =>
      cases success
      exact .nil
  | cons candidate rest ih =>
      simp only [firstHit] at success
      rw [FuelResult.bind_eq_ok_iff] at success
      rcases success with ⟨outcome, tried, continued⟩
      cases outcome with
      | miss => exact .skip tried (ih continued)
      | hit selected =>
          cases continued
          exact .hit tried

/-- Every finite ordered derivation executes with the same selected result. -/
theorem FirstHit.complete
    {tryOne : Candidate → FuelResult (DispatchResult Result)}
    {candidates : List Candidate} {result : DispatchResult Result}
    (dispatch : FirstHit tryOne candidates result) :
    firstHit tryOne candidates = .ok result := by
  induction dispatch with
  | nil => rfl
  | hit selected => simp [firstHit, selected]
  | skip missed tail ih => simp [firstHit, missed, ih]

/-- Executable and relational first-success dispatch agree exactly. -/
theorem firstHit_eq_ok_iff
    (tryOne : Candidate → FuelResult (DispatchResult Result))
    (candidates : List Candidate) (result : DispatchResult Result) :
    firstHit tryOne candidates = .ok result ↔
      FirstHit tryOne candidates result :=
  ⟨firstHit_sound, FirstHit.complete⟩

/-- A pointwise non-stuck candidate test makes finite dispatch non-stuck. -/
theorem firstHit_notStuck
    (tryOne : Candidate → FuelResult (DispatchResult Result))
    (safe : ∀ candidate, (tryOne candidate).NotStuck)
    (candidates : List Candidate) :
    (firstHit tryOne candidates).NotStuck := by
  induction candidates with
  | nil => trivial
  | cons candidate rest ih =>
      apply FuelResult.bind_notStuck (resultSafe := safe candidate)
      intro outcome
      cases outcome with
      | miss => exact ih
      | hit result => trivial

end TypePM.Runtime
