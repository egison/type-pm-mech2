import TypePM.SaturationRenaming

/-!
# Constraint-block order invariance

`BlockAccepts` forgets the administrative order of a generated hard-equation
worklist and delayed-check worklist.  Its invariance theorem states the
general order-independence property needed by M1: finite fresh-variable
renaming and reordering either worklist do not change solvability.

This theorem does not reorder source expressions.  Tuple positions remain
semantically significant; the executable boundary regressions separately
fix the source pairs for which both orders are intended to typecheck.
-/

namespace TypePM

/-- A generated constraint block is acceptable when hard saturation and the
remaining checking equations are both solvable. -/
def BlockAccepts (generated : Generated) : Prop :=
  ∃ finalHard finalPending hardSubstitution residualSubstitution,
    Saturated generated.hard generated.pending finalHard finalPending
        hardSubstitution ∧
      Solves residualSubstitution
        (residualEquations hardSubstitution finalPending)

namespace BlockAccepts

/-- Fresh ordinary-variable names do not affect block solvability. -/
theorem rename
    {generated : Generated} (rho : TyRenaming)
    (accepts : BlockAccepts generated) :
    BlockAccepts (generated.rename rho) := by
  rcases accepts with
    ⟨finalHard, finalPending, hardSubstitution, residualSubstitution,
      saturated, residualSolved⟩
  refine ⟨finalHard.map (Equation.rename rho),
    finalPending.map (CheckObligation.rename rho),
    Subst.renameSolution rho hardSubstitution,
    Subst.renameSolution rho residualSubstitution,
    saturated.rename rho, ?_⟩
  exact (solves_residualEquations_rename rho hardSubstitution
    residualSubstitution finalPending).mp residualSolved

/-- Reordering both initial worklists preserves block solvability. -/
theorem permute
    {left right : Generated}
    (hardPermutation : left.hard.Perm right.hard)
    (pendingPermutation : left.pending.Perm right.pending)
    (accepts : BlockAccepts left) :
    BlockAccepts right := by
  rcases accepts with
    ⟨finalHard, finalPending, hardSubstitution, residualSubstitution,
      saturated, residualSolved⟩
  obtain ⟨transportedHard, transportedPending, _hardPermutation,
      finalPendingPermutation, transportedSaturation⟩ :=
    saturated.permuteInitial hardPermutation pendingPermutation
  refine ⟨transportedHard, transportedPending, hardSubstitution,
    residualSubstitution, transportedSaturation, ?_⟩
  exact (solves_residualEquations_iff_of_perm hardSubstitution
    residualSubstitution finalPendingPermutation).mp residualSolved

end BlockAccepts

namespace Generated.AlphaEq

/-- One-way transport of acceptance along finite alpha-equivalence of
generated blocks. -/
theorem blockAccepts
    {left right : Generated} (equivalence : left.AlphaEq right)
    (accepts : BlockAccepts left) :
    BlockAccepts right := by
  rcases equivalence with
    ⟨rho, _finite, _targetEquality, hardPermutation,
      pendingPermutation⟩
  exact BlockAccepts.permute hardPermutation pendingPermutation
    (BlockAccepts.rename rho accepts)

/-- General M1 schedule invariance: changing finite fresh names and
permuting either generated worklist preserves and reflects acceptance. -/
theorem blockAccepts_iff
    {left right : Generated} (equivalence : left.AlphaEq right) :
    BlockAccepts left ↔ BlockAccepts right := by
  exact ⟨equivalence.blockAccepts,
    equivalence.symm.blockAccepts⟩

end Generated.AlphaEq

end TypePM
