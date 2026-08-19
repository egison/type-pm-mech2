import TypePM.Source.ElaborationTransport
import TypePM.SourcePermutation

/-!
# Finite renamings for allocated fresh-name intervals

Source elaboration only needs to align the finite intervals that were
actually allocated.  The permutations here move two equal-length half-open
intervals pointwise and leave every name below both interval starts fixed.
-/

namespace TypePM.Source

namespace FreshInterval

/-- Move `[source, source + count)` pointwise onto
`[target, target + count)`.  If the source lies first, rotate it past the
intervening block; otherwise rotate the source block to the left. -/
def align (source target count : Nat) : TyRenaming :=
  if source ≤ target then
    TyRenaming.swapAdjacentBlocks source count (target - source)
  else
    TyRenaming.swapAdjacentBlocks target (source - target) count

theorem align_maps (source target count offset : Nat)
    (inside : offset < count) :
    (align source target count ⟨source + offset⟩).index =
      target + offset := by
  by_cases order : source ≤ target
  · simp only [align, if_pos order]
    have lower : source ≤ source + offset := by omega
    have upper : source + offset < source + count := by omega
    rw [TyRenaming.swapAdjacentBlocks_left
      (start := source) (leftWidth := count)
      (rightWidth := target - source)
      (index := TyVar.mk (source + offset))
      lower upper]
    change source + offset + (target - source) = target + offset
    omega
  · simp only [align, if_neg order]
    have targetLe : target ≤ source := by omega
    have lower : target + (source - target) ≤ source + offset := by omega
    have upper :
        source + offset < target + (source - target) + count := by omega
    rw [TyRenaming.swapAdjacentBlocks_right
      (start := target) (leftWidth := source - target)
      (rightWidth := count)
      (index := TyVar.mk (source + offset))
      lower upper]
    change source + offset - (source - target) = target + offset
    omega

theorem align_fixed_below
    {source target count index : Nat}
    (belowSource : index < source) (belowTarget : index < target) :
    align source target count ⟨index⟩ = ⟨index⟩ := by
  by_cases order : source ≤ target
  · simp only [align, if_pos order]
    exact TyRenaming.swapAdjacentBlocks_before belowSource
  · simp only [align, if_neg order]
    exact TyRenaming.swapAdjacentBlocks_before belowTarget

theorem align_finiteSupport (source target count : Nat) :
    TyRenaming.FiniteSupport (align source target count) := by
  by_cases order : source ≤ target
  · simp only [align, if_pos order]
    exact TyRenaming.finiteSupport_swapAdjacentBlocks _ _ _
  · simp only [align, if_neg order]
    exact TyRenaming.finiteSupport_swapAdjacentBlocks _ _ _

end FreshInterval


namespace VariableRenaming

private def capForwardOf (rho : TyRenaming) (index : CapVar) : CapVar :=
  ⟨(rho.forward ⟨index.index⟩).index⟩

private def capBackwardOf (rho : TyRenaming) (index : CapVar) : CapVar :=
  ⟨(rho.backward ⟨index.index⟩).index⟩

/-- Independently align finite ordinary- and capability-variable prefixes. -/
def alignPrefixes (source target : Supply)
    (tyCount capCount : Nat) : VariableRenaming :=
  let ty := FreshInterval.align source.ty target.ty tyCount
  let cap := FreshInterval.align source.cap target.cap capCount
  { tyForward := ty.forward
    tyBackward := ty.backward
    capForward := capForwardOf cap
    capBackward := capBackwardOf cap
    ty_backward_forward := ty.backward_forward
    ty_forward_backward := ty.forward_backward
    cap_backward_forward := fun index => by
      cases index with
      | mk raw =>
          simp only [capForwardOf, capBackwardOf, CapVar.mk.injEq]
          exact congrArg TyVar.index (cap.backward_forward ⟨raw⟩)
    cap_forward_backward := fun index => by
      cases index with
      | mk raw =>
          simp only [capForwardOf, capBackwardOf, CapVar.mk.injEq]
          exact congrArg TyVar.index (cap.forward_backward ⟨raw⟩) }

theorem alignPrefixes_mapsPrefix
    (source target : Supply) (tyCount capCount : Nat) :
    source.MapsPrefix
      (alignPrefixes source target tyCount capCount)
      target tyCount capCount := by
  constructor
  · intro offset inside
    exact congrArg TyVar.mk
      (FreshInterval.align_maps source.ty target.ty tyCount offset inside)
  · intro offset inside
    exact congrArg CapVar.mk
      (FreshInterval.align_maps source.cap target.cap capCount offset inside)

/-- Names below both ordinary-variable interval starts are fixed. -/
theorem alignPrefixes_ty_fixed_below
    {source target : Supply} {tyCount capCount : Nat} {index : TyVar}
    (belowSource : index.index < source.ty)
    (belowTarget : index.index < target.ty) :
    (alignPrefixes source target tyCount capCount).tyForward index = index := by
  exact FreshInterval.align_fixed_below belowSource belowTarget

/-- Names below both capability-variable interval starts are fixed. -/
theorem alignPrefixes_cap_fixed_below
    {source target : Supply} {tyCount capCount : Nat} {index : CapVar}
    (belowSource : index.index < source.cap)
    (belowTarget : index.index < target.cap) :
    (alignPrefixes source target tyCount capCount).capForward index = index := by
  cases index with
  | mk raw =>
      exact congrArg (fun index : TyVar => CapVar.mk index.index)
        (FreshInterval.align_fixed_below belowSource belowTarget)

/-- Finite support for both independent variable sorts. -/
def FiniteSupport (rho : VariableRenaming) : Prop :=
  (∃ support : List TyVar,
      ∀ index, index ∉ support → rho.tyForward index = index) ∧
    (∃ support : List CapVar,
      ∀ index, index ∉ support → rho.capForward index = index)

theorem alignPrefixes_finiteSupport
    (source target : Supply) (tyCount capCount : Nat) :
    FiniteSupport (alignPrefixes source target tyCount capCount) := by
  obtain ⟨tySupport, tyFixed⟩ :=
    FreshInterval.align_finiteSupport source.ty target.ty tyCount
  obtain ⟨capSupport, capFixed⟩ :=
    FreshInterval.align_finiteSupport source.cap target.cap capCount
  refine ⟨⟨tySupport, ?_⟩,
    ⟨capSupport.map (fun index => CapVar.mk index.index), ?_⟩⟩
  · intro index outside
    exact tyFixed index outside
  · intro index outside
    cases index with
    | mk raw =>
        apply congrArg (fun index : TyVar => CapVar.mk index.index)
        apply capFixed ⟨raw⟩
        intro membership
        apply outside
        exact List.mem_map.mpr ⟨⟨raw⟩, membership, rfl⟩

end VariableRenaming


namespace Context

/-- If both interval starts lie above a context's free variables, aligning
the fresh prefixes fixes every free ordinary variable of that context. -/
theorem alignPrefixes_fixes_freeTy
    {context : Context} {source target : Supply}
    {tyCount capCount : Nat}
    (sourceAbove : context.initialSupply.ty ≤ source.ty)
    (targetAbove : context.initialSupply.ty ≤ target.ty)
    {index : TyVar} (member : index ∈ context.freeTyVars) :
    (VariableRenaming.alignPrefixes source target tyCount capCount).tyForward
        index = index := by
  apply VariableRenaming.alignPrefixes_ty_fixed_below
  · exact Nat.lt_of_lt_of_le
      (context.freeTy_index_lt_initialSupply member) sourceAbove
  · exact Nat.lt_of_lt_of_le
      (context.freeTy_index_lt_initialSupply member) targetAbove

/-- Capability counterpart of `alignPrefixes_fixes_freeTy`. -/
theorem alignPrefixes_fixes_freeCap
    {context : Context} {source target : Supply}
    {tyCount capCount : Nat}
    (sourceAbove : context.initialSupply.cap ≤ source.cap)
    (targetAbove : context.initialSupply.cap ≤ target.cap)
    {index : CapVar} (member : index ∈ context.freeCapVars) :
    (VariableRenaming.alignPrefixes source target tyCount capCount).capForward
        index = index := by
  apply VariableRenaming.alignPrefixes_cap_fixed_below
  · exact Nat.lt_of_lt_of_le
      (context.freeCap_index_lt_initialSupply member) sourceAbove
  · exact Nat.lt_of_lt_of_le
      (context.freeCap_index_lt_initialSupply member) targetAbove

end Context

end TypePM.Source
