import TypePM.Runtime.OrderedChoiceAdequacy

/-!
# Results of fuel-bounded runtime procedures

Fuel exhaustion and a missing runtime rule are distinct outcomes.  Later
evaluators use `ok` for a completed computation, `timeout` for insufficient
fuel, and `stuck` only for an actual rule-coverage failure.
-/

namespace TypePM.Runtime

/-- Observable result of a fuel-bounded runtime procedure. -/
inductive FuelResult (α : Type u) where
  | ok (value : α)
  | timeout
  | stuck
deriving Repr, DecidableEq

namespace FuelResult

def map (function : α → β) : FuelResult α → FuelResult β
  | .ok value => .ok (function value)
  | .timeout => .timeout
  | .stuck => .stuck

def bind (result : FuelResult α) (next : α → FuelResult β) : FuelResult β :=
  match result with
  | .ok value => next value
  | .timeout => .timeout
  | .stuck => .stuck

/-- Evaluate list elements from left to right, stopping at the first timeout
or stuck result. -/
def traverse (function : α → FuelResult β) : List α → FuelResult (List β)
  | [] => .ok []
  | value :: tail =>
      bind (function value) fun result =>
        map (result :: ·) (traverse function tail)

/-- The result is not the rule-coverage failure `stuck`. -/
def NotStuck : FuelResult α → Prop
  | .stuck => False
  | .ok _ | .timeout => True

/-- Pointwise relational specification of a successful list traversal. -/
inductive Traverses (function : α → FuelResult β) :
    List α → List β → Prop where
  | nil : Traverses function [] []
  | cons {input : α} {output : β} {inputs : List α} {outputs : List β} :
      function input = .ok output →
      Traverses function inputs outputs →
      Traverses function (input :: inputs) (output :: outputs)

@[simp] theorem map_ok (function : α → β) (value : α) :
    map function (.ok value) = .ok (function value) := by
  rfl

@[simp] theorem map_timeout (function : α → β) :
    map function .timeout = .timeout := by
  rfl

@[simp] theorem map_stuck (function : α → β) :
    map function .stuck = .stuck := by
  rfl

@[simp] theorem bind_ok (value : α) (next : α → FuelResult β) :
    bind (.ok value) next = next value := by
  rfl

@[simp] theorem bind_timeout (next : α → FuelResult β) :
    bind .timeout next = .timeout := by
  rfl

@[simp] theorem bind_stuck (next : α → FuelResult β) :
    bind .stuck next = .stuck := by
  rfl

theorem map_eq_ok_iff (function : α → β) (result : FuelResult α) (value : β) :
    map function result = .ok value ↔
      ∃ input, result = .ok input ∧ function input = value := by
  cases result <;> simp [map]

theorem bind_eq_ok_iff (result : FuelResult α)
    (next : α → FuelResult β) (value : β) :
    bind result next = .ok value ↔
      ∃ input, result = .ok input ∧ next input = .ok value := by
  cases result <;> simp [bind]

theorem traverse_eq_ok_iff (function : α → FuelResult β)
    (inputs : List α) (outputs : List β) :
    traverse function inputs = .ok outputs ↔
      Traverses function inputs outputs := by
  induction inputs generalizing outputs with
  | nil =>
      constructor
      · intro result
        simp [traverse] at result
        subst outputs
        exact .nil
      · intro related
        cases related
        rfl
  | cons input tail ih =>
      constructor
      · intro result
        simp only [traverse] at result
        rw [bind_eq_ok_iff] at result
        rcases result with ⟨headOutput, headResult, tailResult⟩
        rw [map_eq_ok_iff] at tailResult
        rcases tailResult with ⟨tailOutputs, traversed, outputEq⟩
        subst outputs
        exact .cons headResult ((ih tailOutputs).mp traversed)
      · intro related
        cases related with
        | cons headResult tailRelated =>
            simp [traverse, headResult, (ih _).mpr tailRelated]

theorem map_notStuck (function : α → β) {result : FuelResult α}
    (safe : result.NotStuck) : (map function result).NotStuck := by
  cases result <;> trivial

theorem bind_notStuck {result : FuelResult α} (next : α → FuelResult β)
    (resultSafe : result.NotStuck)
    (nextSafe : ∀ value, (next value).NotStuck) :
    (bind result next).NotStuck := by
  cases result <;> simp_all [bind, NotStuck]

theorem traverse_notStuck (function : α → FuelResult β)
    (inputs : List α) (safe : ∀ input, (function input).NotStuck) :
    (traverse function inputs).NotStuck := by
  induction inputs with
  | nil => trivial
  | cons input tail ih =>
      apply bind_notStuck (resultSafe := safe input)
      intro output
      exact map_notStuck _ ih

end FuelResult

end TypePM.Runtime
