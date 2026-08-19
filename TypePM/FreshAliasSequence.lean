import TypePM.FreshAliasSaturation

/-!
# Finite sequences of fresh aliases

An interface can differ from another interface by more than one auxiliary
variable, and the variables can belong to either of the two variable sorts.
This module packages the one-alias acceptance theorems into a finite mixed
sequence.  `Admissible` records freshness and literal invariance at each
intermediate block, after all preceding aliases have been added.
-/

namespace TypePM

namespace HardEquivalent

/-- A reflexive ordinary-type equation may be inserted or removed. -/
theorem cons_ty_refl (type : Ty) (equations : List Equation) :
    HardEquivalent (.ty type type :: equations) equations := by
  intro substitution
  simp [solves_cons, Equation.Holds]

/-- A reflexive capability equation may be inserted or removed. -/
theorem cons_cap_refl (capability : Cap) (equations : List Equation) :
    HardEquivalent (.cap capability capability :: equations) equations := by
  intro substitution
  simp [solves_cons, Equation.Holds]

end HardEquivalent

namespace FreshAliasSequence

/-- One ordinary-variable or capability-variable alias. -/
inductive Alias where
  | ty (fresh existing : TyVar)
  | cap (fresh existing : CapVar)
deriving DecidableEq, Repr

namespace Alias

/-- Add one alias equation to the front of a generated block's hard
worklist. -/
def add : Alias → Generated → Generated
  | .ty fresh existing, body =>
      FreshAliasElimination.addTyAlias fresh existing body
  | .cap fresh existing, body =>
      FreshAliasElimination.addCapAlias fresh existing body

/-- Freshness and invariance needed to add or remove this alias while
preserving general-pending block acceptance. -/
def Admissible : Alias → Generated → Prop
  | .ty fresh existing, body =>
      fresh ≠ existing ∧
        FreshAliasSaturation.TyInvariant
          fresh existing body.hard body.pending
  | .cap fresh existing, body =>
      fresh ≠ existing ∧
        FreshAliasSaturation.CapInvariant
          fresh existing body.hard body.pending

/-- One admissible mixed-sort alias preserves and reflects acceptance. -/
theorem blockAccepts_add_iff
    (alias : Alias) (body : Generated)
    (admissible : alias.Admissible body) :
    BlockAccepts (alias.add body) ↔ BlockAccepts body := by
  cases alias with
  | ty fresh existing =>
      exact FreshAliasSaturation.blockAccepts_addTyAlias_iff
        body fresh existing admissible.1 admissible.2
  | cap fresh existing =>
      exact FreshAliasSaturation.blockAccepts_addCapAlias_iff
        body fresh existing admissible.1 admissible.2

end Alias

/-- Add aliases from left to right.  Thus the admissibility premise for each
entry is checked after all earlier entries have already been added. -/
def addAll : List Alias → Generated → Generated
  | [], body => body
  | alias :: rest, body => addAll rest (alias.add body)

@[simp] theorem addAll_target (aliases : List Alias) (body : Generated) :
    (addAll aliases body).target = body.target := by
  induction aliases generalizing body with
  | nil => rfl
  | cons alias rest induction =>
      rw [addAll, induction]
      cases alias <;> rfl

@[simp] theorem addAll_pending (aliases : List Alias) (body : Generated) :
    (addAll aliases body).pending = body.pending := by
  induction aliases generalizing body with
  | nil => rfl
  | cons alias rest induction =>
      rw [addAll, induction]
      cases alias <;> rfl

/-- Stepwise freshness and invariance for a finite mixed-sort alias
sequence. -/
def Admissible : List Alias → Generated → Prop
  | [], _body => True
  | alias :: rest, body =>
      alias.Admissible body ∧ Admissible rest (alias.add body)

/-- Repeatedly adding or removing a finite admissible sequence of ordinary-
variable and capability-variable aliases preserves block acceptance. -/
theorem blockAccepts_addAll_iff
    (aliases : List Alias) (body : Generated)
    (admissible : Admissible aliases body) :
    BlockAccepts (addAll aliases body) ↔ BlockAccepts body := by
  induction aliases generalizing body with
  | nil => rfl
  | cons alias rest induction =>
      exact (induction (alias.add body) admissible.2).trans
        (alias.blockAccepts_add_iff body admissible.1)

/-- A semantically equivalent hard worklist may be used after adding the
alias sequence.  This permits harmless equation reordering, reversal, and
redundancy at an interface boundary. -/
theorem blockAccepts_iff_of_addAll_hardEquivalent
    (aliases : List Alias) (body other : Generated)
    (admissible : Admissible aliases body)
    (hardEquivalent : HardEquivalent
      (addAll aliases body).hard other.hard)
    (pendingEqual : (addAll aliases body).pending = other.pending) :
    BlockAccepts body ↔ BlockAccepts other :=
  (blockAccepts_addAll_iff aliases body admissible).symm.trans
    (BlockAccepts.iff_of_hardEquivalent hardEquivalent pendingEqual)

/-- A symmetric certificate that two generated blocks reduce to one common
core after independently removing finite mixed-sort alias sequences.  The
two `HardEquivalent` fields allow each concrete interface to contain
reordered, reversed, or redundant equations around its alias presentation.
-/
def CommonCoreEquivalent (left right : Generated) : Prop :=
  ∃ (core : Generated) (leftAliases rightAliases : List Alias),
    Admissible leftAliases core ∧
      Admissible rightAliases core ∧
      HardEquivalent (addAll leftAliases core).hard left.hard ∧
      HardEquivalent (addAll rightAliases core).hard right.hard ∧
      (addAll leftAliases core).pending = left.pending ∧
      (addAll rightAliases core).pending = right.pending

namespace CommonCoreEquivalent

theorem refl (body : Generated) : CommonCoreEquivalent body body := by
  exact ⟨body, [], [], trivial, trivial,
    HardEquivalent.refl body.hard, HardEquivalent.refl body.hard, rfl, rfl⟩

theorem symm {left right : Generated}
    (equivalent : CommonCoreEquivalent left right) :
    CommonCoreEquivalent right left := by
  rcases equivalent with
    ⟨core, leftAliases, rightAliases, leftAdmissible, rightAdmissible,
      leftHardEquivalent, rightHardEquivalent, leftPendingEqual,
      rightPendingEqual⟩
  exact ⟨core, rightAliases, leftAliases,
    rightAdmissible, leftAdmissible,
    rightHardEquivalent, leftHardEquivalent,
    rightPendingEqual, leftPendingEqual⟩

/-- The smallest representative-sensitive ordinary-variable example: a
fresh alias on one side and a reflexive equation on the other share the
unaltered body as their common core. -/
theorem tyAlias_refl
    (body : Generated) (fresh existing : TyVar)
    (different : fresh ≠ existing)
    (invariant : FreshAliasSaturation.TyInvariant
      fresh existing body.hard body.pending) :
    CommonCoreEquivalent
      (FreshAliasElimination.addTyAlias fresh existing body)
      { body with
        hard := .ty (.var existing) (.var existing) :: body.hard } := by
  refine ⟨body, [.ty fresh existing], [], ?_, trivial, ?_, ?_, rfl, rfl⟩
  · exact ⟨⟨different, invariant⟩, trivial⟩
  · exact HardEquivalent.refl _
  · exact (HardEquivalent.cons_ty_refl (.var existing) body.hard).symm

/-- Capability-variable counterpart of `tyAlias_refl`. -/
theorem capAlias_refl
    (body : Generated) (fresh existing : CapVar)
    (different : fresh ≠ existing)
    (invariant : FreshAliasSaturation.CapInvariant
      fresh existing body.hard body.pending) :
    CommonCoreEquivalent
      (FreshAliasElimination.addCapAlias fresh existing body)
      { body with
        hard := .cap (.var existing) (.var existing) :: body.hard } := by
  refine ⟨body, [.cap fresh existing], [], ?_, trivial, ?_, ?_, rfl, rfl⟩
  · exact ⟨⟨different, invariant⟩, trivial⟩
  · exact HardEquivalent.refl _
  · exact (HardEquivalent.cons_cap_refl (.var existing) body.hard).symm

/-- Both sides of a common-core certificate have equivalent block
acceptance, including arbitrary delayed checking obligations. -/
theorem blockAccepts_iff
    {left right : Generated}
    (equivalent : CommonCoreEquivalent left right) :
    BlockAccepts left ↔ BlockAccepts right := by
  rcases equivalent with
    ⟨core, leftAliases, rightAliases, leftAdmissible, rightAdmissible,
      leftHardEquivalent, rightHardEquivalent, leftPendingEqual,
      rightPendingEqual⟩
  exact
    (blockAccepts_iff_of_addAll_hardEquivalent
        leftAliases core left leftAdmissible leftHardEquivalent
        leftPendingEqual).symm.trans
      (blockAccepts_iff_of_addAll_hardEquivalent
        rightAliases core right rightAdmissible rightHardEquivalent
        rightPendingEqual)

end CommonCoreEquivalent

end FreshAliasSequence

end TypePM
