import TypePM.Source.RecursiveLetInvariant

/-!
# Future-fixed finite closure renamings

The global renaming extending a finite partial bijection is assembled from
swaps of source and target names.  If both finite supports lie strictly
below a supply boundary, every name at or above that boundary is fixed.

This is deliberately weaker than fixing every name outside one allocation
interval.  A closure representative may rename an inherited variable below
the interval start; source body transport only needs the future fresh stream
at and above the value block's finishing supply to remain fixed.
-/

namespace TypePM.Source

namespace FinitePermutation

private theorem Permutation.forward_injective
    (rho : Permutation α) : Function.Injective rho.forward := by
  intro left right equality
  have restored := congrArg rho.backward equality
  simpa only [rho.backward_forward] using restored

private theorem extend_ty_fixesAtOrAbove
    (sources targets : List TyVar) (boundary : Nat)
    (sourcesBelow : ∀ index, index ∈ sources → index.index < boundary)
    (targetsBelow : ∀ index, index ∈ targets → index.index < boundary) :
    ∀ index : TyVar, boundary ≤ index.index →
      (extend sources targets).forward index = index := by
  induction sources generalizing targets with
  | nil =>
      intro index _above
      simp [extend, Permutation.refl]
  | cons source sources induction =>
      cases targets with
      | nil =>
          intro index _above
          simp [extend, Permutation.refl]
      | cons target targets =>
          have sourceBelow : source.index < boundary :=
            sourcesBelow source (by simp)
          have tailSourcesBelow : ∀ index, index ∈ sources →
              index.index < boundary := by
            intro index member
            exact sourcesBelow index (by simp [member])
          have targetBelow : target.index < boundary :=
            targetsBelow target (by simp)
          have tailTargetsBelow : ∀ index, index ∈ targets →
              index.index < boundary := by
            intro index member
            exact targetsBelow index (by simp [member])
          let tail := extend sources targets
          have tailFixed : ∀ index : TyVar, boundary ≤ index.index →
              tail.forward index = index :=
            induction targets tailSourcesBelow tailTargetsBelow
          have tailSourceBelow : (tail.forward source).index < boundary := by
            by_cases below : (tail.forward source).index < boundary
            · exact below
            · have above : boundary ≤ (tail.forward source).index :=
                Nat.le_of_not_gt below
              have fixed := tailFixed (tail.forward source) above
              have equality : tail.forward source = source :=
                tail.forward_injective (by simpa using fixed)
              rw [equality] at above
              exact False.elim ((Nat.not_le_of_gt sourceBelow) above)
          intro index above
          have tailIndex := tailFixed index above
          have notSource : index ≠ tail.forward source := by
            intro equality
            subst index
            exact (Nat.not_le_of_gt tailSourceBelow) above
          have notTarget : index ≠ target := by
            intro equality
            subst index
            exact (Nat.not_le_of_gt targetBelow) above
          simp [extend, tail, Permutation.trans, tailIndex,
            swap_fixed notSource notTarget]

private theorem extend_cap_fixesAtOrAbove
    (sources targets : List CapVar) (boundary : Nat)
    (sourcesBelow : ∀ index, index ∈ sources → index.index < boundary)
    (targetsBelow : ∀ index, index ∈ targets → index.index < boundary) :
    ∀ index : CapVar, boundary ≤ index.index →
      (extend sources targets).forward index = index := by
  induction sources generalizing targets with
  | nil =>
      intro index _above
      simp [extend, Permutation.refl]
  | cons source sources induction =>
      cases targets with
      | nil =>
          intro index _above
          simp [extend, Permutation.refl]
      | cons target targets =>
          have sourceBelow : source.index < boundary :=
            sourcesBelow source (by simp)
          have tailSourcesBelow : ∀ index, index ∈ sources →
              index.index < boundary := by
            intro index member
            exact sourcesBelow index (by simp [member])
          have targetBelow : target.index < boundary :=
            targetsBelow target (by simp)
          have tailTargetsBelow : ∀ index, index ∈ targets →
              index.index < boundary := by
            intro index member
            exact targetsBelow index (by simp [member])
          let tail := extend sources targets
          have tailFixed : ∀ index : CapVar, boundary ≤ index.index →
              tail.forward index = index :=
            induction targets tailSourcesBelow tailTargetsBelow
          have tailSourceBelow : (tail.forward source).index < boundary := by
            by_cases below : (tail.forward source).index < boundary
            · exact below
            · have above : boundary ≤ (tail.forward source).index :=
                Nat.le_of_not_gt below
              have fixed := tailFixed (tail.forward source) above
              have equality : tail.forward source = source :=
                tail.forward_injective (by simpa using fixed)
              rw [equality] at above
              exact False.elim ((Nat.not_le_of_gt sourceBelow) above)
          intro index above
          have tailIndex := tailFixed index above
          have notSource : index ≠ tail.forward source := by
            intro equality
            subst index
            exact (Nat.not_le_of_gt tailSourceBelow) above
          have notTarget : index ≠ target := by
            intro equality
            subst index
            exact (Nat.not_le_of_gt targetBelow) above
          simp [extend, tail, Permutation.trans, tailIndex,
            swap_fixed notSource notTarget]

end FinitePermutation

namespace SubstitutionPartialBijection

/-- A finite two-sort partial bijection whose source and target supports are
strictly below `boundary` extends to a renaming that fixes the complete
future fresh stream. -/
theorem toVariableRenaming_fixesAtOrAbove
    {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward)
    (boundary : Supply)
    (tySourceBelow : ∀ index, index ∈ data.ty.source →
      index.index < boundary.ty)
    (tyTargetBelow : ∀ index, index ∈ data.ty.target →
      index.index < boundary.ty)
    (capSourceBelow : ∀ index, index ∈ data.cap.source →
      index.index < boundary.cap)
    (capTargetBelow : ∀ index, index ∈ data.cap.target →
      index.index < boundary.cap) :
    data.toVariableRenaming.FixesAtOrAbove boundary := by
  constructor
  · exact FinitePermutation.extend_ty_fixesAtOrAbove
      data.ty.source (data.ty.source.map data.ty.forward) boundary.ty
      tySourceBelow (by
        intro index member
        obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
        exact tyTargetBelow _ (data.ty.forward_mem sourceMember))
  · exact FinitePermutation.extend_cap_fixesAtOrAbove
      data.cap.source (data.cap.source.map data.cap.forward) boundary.cap
      capSourceBelow (by
        intro index member
        obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
        exact capTargetBelow _ (data.cap.forward_mem sourceMember))

end SubstitutionPartialBijection

namespace ClosureSupportBijection

/-- Source-facing wrapper for closure-support data.  Numeric support bounds
are the only facts needed to obtain the future-fixed renaming consumed by
body elaboration transport. -/
theorem globalRenaming_fixesAtOrAbove
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    (boundary : Supply)
    (tySourceBelow : ∀ index, index ∈ data.support.ty.source →
      index.index < boundary.ty)
    (tyTargetBelow : ∀ index, index ∈ data.support.ty.target →
      index.index < boundary.ty)
    (capSourceBelow : ∀ index, index ∈ data.support.cap.source →
      index.index < boundary.cap)
    (capTargetBelow : ∀ index, index ∈ data.support.cap.target →
      index.index < boundary.cap) :
    data.globalRenaming.FixesAtOrAbove boundary :=
  data.support.toVariableRenaming_fixesAtOrAbove boundary
    tySourceBelow tyTargetBelow capSourceBelow capTargetBelow

end ClosureSupportBijection

end TypePM.Source
