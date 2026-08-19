import TypePM.Runtime.FuelResult

/-!
# Runtime environments

Runtime environments are newest-first lists, matching the de Bruijn indices
used by source expressions.  `Lookup` is the relational form of the
executable `List.getElem?` lookup.
-/

namespace TypePM.Runtime

/-- A newest-first runtime environment. -/
abbrev Environment (α : Type u) := List α

/-- Relational lookup at a de Bruijn index. -/
inductive Lookup : Environment α → Nat → α → Prop where
  | zero (value : α) (tail : Environment α) :
      Lookup (value :: tail) 0 value
  | succ {value : α} {tail : Environment α} {index : Nat} {result : α} :
      Lookup tail index result →
      Lookup (value :: tail) (index + 1) result

theorem getElem?_eq_some_iff_lookup
    (environment : Environment α) (index : Nat) (value : α) :
    environment[index]? = some value ↔ Lookup environment index value := by
  induction environment generalizing index with
  | nil =>
      constructor
      · simp
      · intro lookup
        cases lookup
  | cons head tail ih =>
      cases index with
      | zero =>
          constructor
          · intro result
            simp at result
            subst value
            exact .zero head tail
          · intro lookup
            cases lookup
            rfl
      | succ index =>
          constructor
          · intro result
            simp only [List.getElem?_cons_succ] at result
            exact .succ ((ih index).mp result)
          · intro lookup
            cases lookup with
            | succ tailLookup =>
                simp only [List.getElem?_cons_succ]
                exact (ih index).mpr tailLookup

theorem Lookup.deterministic
    (left : Lookup environment index leftValue)
    (right : Lookup environment index rightValue) :
    leftValue = rightValue := by
  induction left with
  | zero =>
      cases right
      rfl
  | succ _ ih =>
      cases right with
      | succ rightTail => exact ih rightTail

theorem Lookup.head (value : α) (environment : Environment α) :
    Lookup (value :: environment) 0 value :=
  .zero value environment

theorem Lookup.weaken
    {environment : Environment α} {index : Nat} {value : α}
    (lookup : Lookup environment index value) (newest : α) :
    Lookup (newest :: environment) (index + 1) value :=
  .succ lookup

theorem Lookup.of_append_left
    {front : Environment α} {index : Nat} {value : α}
    (lookup : Lookup front index value) (suffix : Environment α) :
    Lookup (front ++ suffix) index value := by
  induction lookup with
  | zero => exact .zero _ _
  | succ _ ih => exact .succ ih

theorem Lookup.index_lt_length
    (lookup : Lookup environment index value) :
    index < environment.length := by
  induction lookup with
  | zero => simp
  | succ _ ih => simpa using Nat.succ_lt_succ ih

end TypePM.Runtime
