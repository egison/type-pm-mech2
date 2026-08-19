import TypePM.Runtime.OrderedChoice

/-!
# Relational specification of ordered choices

`RemovesOne` and `Splits` describe the same decompositions as the executable
lists in `OrderedChoice`.  The equivalence theorems below are the local
adequacy and completeness facts later matching rules can reuse.
-/

namespace TypePM.Runtime

/-- Removing one input position while retaining every other value in order. -/
inductive RemovesOne (chosen : α) : List α → List α → Prop where
  | here (tail : List α) : RemovesOne chosen (chosen :: tail) tail
  | there {head : α} {target rest : List α} :
      RemovesOne chosen target rest →
      RemovesOne chosen (head :: target) (head :: rest)

/-- Assign each input position to a left or right output while preserving the
relative order inside both outputs. -/
inductive Splits : List α → List α → List α → Prop where
  | nil : Splits [] [] []
  | right {value : α} {target left right : List α} :
      Splits target left right →
      Splits (value :: target) left (value :: right)
  | left {value : α} {target left right : List α} :
      Splits target left right →
      Splits (value :: target) (value :: left) right

/-- Removing the first equal value: every skipped prefix value is known to
be different from the requested one. -/
inductive DeletesFirst [DecidableEq α] (chosen : α) :
    List α → List α → Prop where
  | here (tail : List α) : DeletesFirst chosen (chosen :: tail) tail
  | there {head : α} {target rest : List α} :
      chosen ≠ head →
      DeletesFirst chosen target rest →
      DeletesFirst chosen (head :: target) (head :: rest)

theorem mem_chooseOne_iff
    {chosen : α} {target rest : List α} :
    (chosen, rest) ∈ chooseOne target ↔ RemovesOne chosen target rest := by
  induction target generalizing rest with
  | nil =>
      constructor
      · simp [chooseOne]
      · intro removed
        cases removed
  | cons head tail ih =>
      constructor
      · intro member
        rw [chooseOne_cons] at member
        rcases List.mem_cons.mp member with first | later
        · cases first
          exact .here tail
        · rcases List.mem_map.mp later with ⟨⟨laterChosen, laterRest⟩,
            laterMember, pairEq⟩
          cases pairEq
          exact .there (ih.mp laterMember)
      · intro removed
        cases removed with
        | here =>
            exact List.mem_cons_self
        | there later =>
            apply List.mem_cons_of_mem
            exact List.mem_map.mpr ⟨(_, _), ih.mpr later, rfl⟩

theorem mem_splitAll_iff
    {target left right : List α} :
    (left, right) ∈ splitAll target ↔ Splits target left right := by
  induction target generalizing left right with
  | nil =>
      constructor
      · intro member
        simp only [splitAll_nil, List.mem_cons, List.not_mem_nil,
          or_false] at member
        cases member
        exact .nil
      · intro split
        cases split
        exact List.mem_cons_self
  | cons value tail ih =>
      constructor
      · intro member
        rw [splitAll_cons] at member
        rcases List.mem_append.mp member with onRight | onLeft
        · rcases List.mem_map.mp onRight with
            ⟨⟨tailLeft, tailRight⟩, tailMember, pairEq⟩
          cases pairEq
          exact .right (ih.mp tailMember)
        · rcases List.mem_map.mp onLeft with
            ⟨⟨tailLeft, tailRight⟩, tailMember, pairEq⟩
          cases pairEq
          exact .left (ih.mp tailMember)
      · intro split
        cases split with
        | right tailSplit =>
            apply List.mem_append.mpr
            left
            exact List.mem_map.mpr ⟨(_, _), ih.mpr tailSplit, rfl⟩
        | left tailSplit =>
            apply List.mem_append.mpr
            right
            exact List.mem_map.mpr ⟨(_, _), ih.mpr tailSplit, rfl⟩

theorem deleteFirst?_eq_some_iff [DecidableEq α]
    {chosen : α} {target rest : List α} :
    deleteFirst? chosen target = some rest ↔
      DeletesFirst chosen target rest := by
  induction target generalizing rest with
  | nil =>
      constructor
      · simp [deleteFirst?]
      · intro deleted
        cases deleted
  | cons head tail ih =>
      by_cases same : chosen = head
      · subst head
        constructor
        · intro result
          simp [deleteFirst?] at result
          subst rest
          exact .here tail
        · intro deleted
          cases deleted with
          | here => simp [deleteFirst?]
          | there different => exact (different rfl).elim
      · constructor
        · intro result
          rw [deleteFirst?, if_neg same] at result
          cases tailResult : deleteFirst? chosen tail with
          | none => simp [tailResult] at result
          | some tailRest =>
              simp [tailResult] at result
              subst rest
              exact .there same (ih.mp tailResult)
        · intro deleted
          cases deleted with
          | here => exact (same rfl).elim
          | there _ tailDeleted =>
              rw [deleteFirst?, if_neg same]
              simp [ih.mpr tailDeleted]

theorem deleteFirst?_eq_none_iff [DecidableEq α]
    {chosen : α} {target : List α} :
    deleteFirst? chosen target = none ↔ chosen ∉ target := by
  induction target with
  | nil => simp [deleteFirst?]
  | cons head tail ih =>
      by_cases same : chosen = head
      · subst head
        simp [deleteFirst?]
      · simp [deleteFirst?, same, ih]

theorem mem_chooseValue_iff [DecidableEq α]
    {chosen : α} {target rest : List α} :
    rest ∈ chooseValue chosen target ↔
      DeletesFirst chosen target rest := by
  rw [← deleteFirst?_eq_some_iff]
  unfold chooseValue
  cases result : deleteFirst? chosen target with
  | none => simp
  | some actualRest => simp [eq_comm]

theorem RemovesOne.perm (removed : RemovesOne chosen target rest) :
    target.Perm (chosen :: rest) := by
  induction removed with
  | here => exact List.Perm.refl _
  | @there head target rest removed ih =>
      exact (List.Perm.cons head ih).trans
        (List.Perm.swap chosen head rest)

theorem DeletesFirst.toRemovesOne {α : Type u} [DecidableEq α]
    {chosen : α} {target rest : List α}
    (deleted : DeletesFirst chosen target rest) :
    RemovesOne chosen target rest := by
  induction deleted with
  | here => exact .here _
  | there _ _ ih => exact .there ih

theorem DeletesFirst.perm {α : Type u} [DecidableEq α]
    {chosen : α} {target rest : List α}
    (deleted : DeletesFirst chosen target rest) :
    target.Perm (chosen :: rest) :=
  deleted.toRemovesOne.perm

private theorem perm_cons_append (value : α) (lhs rhs : List α) :
    (value :: (lhs ++ rhs)).Perm (lhs ++ value :: rhs) := by
  induction lhs with
  | nil => exact List.Perm.refl _
  | cons head tail ih =>
      exact (List.Perm.swap head value (tail ++ rhs)).trans
        (List.Perm.cons head ih)

theorem Splits.perm (split : Splits target lhs rhs) :
    target.Perm (lhs ++ rhs) := by
  induction split with
  | nil => exact List.Perm.refl []
  | @right value target lhs rhs split ih =>
      exact (List.Perm.cons value ih).trans
        (perm_cons_append value lhs rhs)
  | @left value target lhs rhs split ih =>
      simpa using List.Perm.cons value ih

end TypePM.Runtime
