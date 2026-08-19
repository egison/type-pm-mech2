import TypePM.SchemeTransport

/-!
# Coherence of generalization under two-sort rho

Generalization is not natural under an arbitrary substitution: a substitution
may identify variables or replace one by a proper type.  The valid transport
is a bijective change of names in both variable sorts.  This module states
that restriction explicitly.
-/

namespace TypePM.Source

/-- A global bijective change of ordinary and capability variable names. -/
structure VariableRenaming where
  tyForward : TyVar → TyVar
  tyBackward : TyVar → TyVar
  capForward : CapVar → CapVar
  capBackward : CapVar → CapVar
  ty_backward_forward : ∀ index, tyBackward (tyForward index) = index
  ty_forward_backward : ∀ index, tyForward (tyBackward index) = index
  cap_backward_forward : ∀ index, capBackward (capForward index) = index
  cap_forward_backward : ∀ index, capForward (capBackward index) = index

namespace VariableRenaming

def substitution (rho : VariableRenaming) : Subst :=
  { ty := fun index => .var (rho.tyForward index)
    cap := fun index => .var (rho.capForward index) }

theorem tyForward_injective (rho : VariableRenaming) :
    Function.Injective rho.tyForward := by
  intro left right equality
  have := congrArg rho.tyBackward equality
  simpa only [rho.ty_backward_forward] using this

theorem capForward_injective (rho : VariableRenaming) :
    Function.Injective rho.capForward := by
  intro left right equality
  have := congrArg rho.capBackward equality
  simpa only [rho.cap_backward_forward] using this

theorem mem_map_tyForward_iff (rho : VariableRenaming)
    (index : TyVar) (indices : List TyVar) :
    rho.tyForward index ∈ indices.map rho.tyForward ↔
      index ∈ indices := by
  constructor
  · intro membership
    obtain ⟨source, sourceMember, equality⟩ := List.mem_map.mp membership
    have : source = index := rho.tyForward_injective equality
    simpa [this] using sourceMember
  · intro membership
    exact List.mem_map.mpr ⟨index, membership, rfl⟩

theorem mem_map_capForward_iff (rho : VariableRenaming)
    (index : CapVar) (indices : List CapVar) :
    rho.capForward index ∈ indices.map rho.capForward ↔
      index ∈ indices := by
  constructor
  · intro membership
    obtain ⟨source, sourceMember, equality⟩ := List.mem_map.mp membership
    have : source = index := rho.capForward_injective equality
    simpa [this] using sourceMember
  · intro membership
    exact List.mem_map.mpr ⟨index, membership, rfl⟩

theorem idxOf_map_tyForward (rho : VariableRenaming)
    (index : TyVar) (indices : List TyVar) :
    (indices.map rho.tyForward).idxOf (rho.tyForward index) =
      indices.idxOf index := by
  induction indices with
  | nil => rfl
  | cons head tail induction =>
      by_cases equality : head = index
      · subst head
        simp
      · have mappedUnequal :
            rho.tyForward head ≠ rho.tyForward index :=
          fun mapped => equality (rho.tyForward_injective mapped)
        have sourceFalse : (head == index) = false := by
          apply Bool.eq_false_iff.mpr
          intro equal
          exact equality (beq_iff_eq.mp equal)
        have mappedFalse :
            (rho.tyForward head == rho.tyForward index) = false := by
          apply Bool.eq_false_iff.mpr
          intro equal
          exact mappedUnequal (beq_iff_eq.mp equal)
        simp [List.idxOf_cons, sourceFalse, mappedFalse, induction]

theorem idxOf_map_capForward (rho : VariableRenaming)
    (index : CapVar) (indices : List CapVar) :
    (indices.map rho.capForward).idxOf (rho.capForward index) =
      indices.idxOf index := by
  induction indices with
  | nil => rfl
  | cons head tail induction =>
      by_cases equality : head = index
      · subst head
        simp
      · have mappedUnequal :
            rho.capForward head ≠ rho.capForward index :=
          fun mapped => equality (rho.capForward_injective mapped)
        have sourceFalse : (head == index) = false := by
          apply Bool.eq_false_iff.mpr
          intro equal
          exact equality (beq_iff_eq.mp equal)
        have mappedFalse :
            (rho.capForward head == rho.capForward index) = false := by
          apply Bool.eq_false_iff.mpr
          intro equal
          exact mappedUnequal (beq_iff_eq.mp equal)
        simp [List.idxOf_cons, sourceFalse, mappedFalse, induction]

end VariableRenaming


theorem contains_map_of_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (mapping : α → β) (injective : Function.Injective mapping)
    (item : α) (items : List α) :
    (items.map mapping).contains (mapping item) = items.contains item := by
  cases source : items.contains item <;>
    cases mapped : (items.map mapping).contains (mapping item) <;>
    try rfl
  · have mappedMember : mapping item ∈ items.map mapping :=
      List.contains_iff_mem.mp mapped
    obtain ⟨sourceItem, sourceMember, equality⟩ :=
      List.mem_map.mp mappedMember
    have sourceEquality : sourceItem = item := injective equality
    subst sourceItem
    have sourceTrue := List.contains_iff_mem.mpr sourceMember
    rw [source] at sourceTrue
    contradiction
  · have sourceMember : item ∈ items :=
      List.contains_iff_mem.mp source
    have mappedMember : mapping item ∈ items.map mapping :=
      List.mem_map.mpr ⟨item, sourceMember, rfl⟩
    have mappedTrue := List.contains_iff_mem.mpr mappedMember
    rw [mapped] at mappedTrue
    contradiction

theorem dedup_map_of_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (mapping : α → β) (injective : Function.Injective mapping)
    (items : List α) :
    dedup (items.map mapping) = (dedup items).map mapping := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.map_cons, dedup]
      rw [contains_map_of_injective mapping injective item items]
      split <;> simp [induction]

theorem dedupFirst_map_of_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (mapping : α → β) (injective : Function.Injective mapping)
    (items : List α) :
    dedupFirst (items.map mapping) =
      (dedupFirst items).map mapping := by
  unfold dedupFirst
  rw [← List.map_reverse,
    dedup_map_of_injective mapping injective,
    List.map_reverse]

theorem filterMap_excluding_of_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (mapping : α → β) (injective : Function.Injective mapping)
    (items excluded : List α) :
    (items.map mapping).filter
        (fun item => !(excluded.map mapping).contains item) =
      (items.filter fun item => !excluded.contains item).map mapping := by
  rw [List.filter_map]
  apply congrArg (List.map mapping)
  apply congrArg (fun predicate => items.filter predicate)
  funext item
  exact congrArg (fun value => !value) (contains_map_of_injective
    mapping injective item excluded)


mutual

@[simp] theorem Cap.capVars_apply_variableRenaming
    (rho : VariableRenaming) (capability : Cap) :
    (capability.apply rho.substitution.cap).capVars =
      capability.capVars.map rho.capForward := by
  cases capability with
  | any => rfl
  | var index => rfl
  | prod items =>
      simp [Cap.apply, Cap.capVars, Cap.capVarsList_apply_variableRenaming]

@[simp] theorem Cap.capVarsList_apply_variableRenaming
    (rho : VariableRenaming) (items : List Cap) :
    Cap.capVarsList (Cap.applyList rho.substitution.cap items) =
      (Cap.capVarsList items).map rho.capForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Cap.applyList, Cap.capVarsList,
        Cap.capVars_apply_variableRenaming,
        Cap.capVarsList_apply_variableRenaming]

end


mutual

@[simp] theorem PolyCap.freeCapVars_apply_variableRenaming
    (rho : VariableRenaming) (capability : PolyCap) :
    (capability.applyFree rho.substitution.cap).freeCapVars =
      capability.freeCapVars.map rho.capForward := by
  cases capability with
  | any => rfl
  | free index => rfl
  | bound index => rfl
  | prod items =>
      simp [PolyCap.applyFree, PolyCap.freeCapVars,
        PolyCap.freeCapVarsList_apply_variableRenaming]

@[simp] theorem PolyCap.freeCapVarsList_apply_variableRenaming
    (rho : VariableRenaming) (items : List PolyCap) :
    PolyCap.freeCapVarsList
        (PolyCap.applyFreeList rho.substitution.cap items) =
      (PolyCap.freeCapVarsList items).map rho.capForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.applyFreeList, PolyCap.freeCapVarsList,
        PolyCap.freeCapVars_apply_variableRenaming,
        PolyCap.freeCapVarsList_apply_variableRenaming]

end


mutual

@[simp] theorem PolyTy.freeTyVars_apply_variableRenaming
    (rho : VariableRenaming) (target : PolyTy) :
    (target.applyFree rho.substitution).freeTyVars =
      target.freeTyVars.map rho.tyForward := by
  cases target with
  | free index => rfl
  | bound index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVars_apply_variableRenaming]
  | prod items =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVarsList_apply_variableRenaming]
  | matcher capability target =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVars_apply_variableRenaming]
  | slot capability target =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVars_apply_variableRenaming]

@[simp] theorem PolyTy.freeTyVarsList_apply_variableRenaming
    (rho : VariableRenaming) (items : List PolyTy) :
    PolyTy.freeTyVarsList (PolyTy.applyFreeList rho.substitution items) =
      (PolyTy.freeTyVarsList items).map rho.tyForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.applyFreeList, PolyTy.freeTyVarsList,
        PolyTy.freeTyVars_apply_variableRenaming,
        PolyTy.freeTyVarsList_apply_variableRenaming]

end


mutual

@[simp] theorem PolyTy.freeCapVars_apply_variableRenaming
    (rho : VariableRenaming) (target : PolyTy) :
    (target.applyFree rho.substitution).freeCapVars =
      target.freeCapVars.map rho.capForward := by
  cases target with
  | free index => rfl
  | bound index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVars_apply_variableRenaming]
  | prod items =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVarsList_apply_variableRenaming]
  | matcher capability target =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVars_apply_variableRenaming,
        PolyCap.freeCapVars_apply_variableRenaming]
  | slot capability target =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVars_apply_variableRenaming,
        PolyCap.freeCapVars_apply_variableRenaming]

@[simp] theorem PolyTy.freeCapVarsList_apply_variableRenaming
    (rho : VariableRenaming) (items : List PolyTy) :
    PolyTy.freeCapVarsList (PolyTy.applyFreeList rho.substitution items) =
      (PolyTy.freeCapVarsList items).map rho.capForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.applyFreeList, PolyTy.freeCapVarsList,
        PolyTy.freeCapVars_apply_variableRenaming,
        PolyTy.freeCapVarsList_apply_variableRenaming]

end


namespace Scheme

@[simp] theorem freeTyVars_apply_variableRenaming
    (rho : VariableRenaming) (scheme : Scheme) :
    (scheme.applyFree rho.substitution).freeTyVars =
      scheme.freeTyVars.map rho.tyForward := by
  unfold Scheme.freeTyVars
  change
    dedupFirst (scheme.body.applyFree rho.substitution).freeTyVars = _
  rw [PolyTy.freeTyVars_apply_variableRenaming,
    dedupFirst_map_of_injective rho.tyForward rho.tyForward_injective]

@[simp] theorem freeCapVars_apply_variableRenaming
    (rho : VariableRenaming) (scheme : Scheme) :
    (scheme.applyFree rho.substitution).freeCapVars =
      scheme.freeCapVars.map rho.capForward := by
  unfold Scheme.freeCapVars
  change
    dedupFirst (scheme.body.applyFree rho.substitution).freeCapVars = _
  rw [PolyTy.freeCapVars_apply_variableRenaming,
    dedupFirst_map_of_injective rho.capForward rho.capForward_injective]

end Scheme


namespace Context

theorem flatMap_freeTyVars_apply_variableRenaming
    (rho : VariableRenaming) (context : Context) :
    (context.applyFree rho.substitution).flatMap Scheme.freeTyVars =
      (context.flatMap Scheme.freeTyVars).map rho.tyForward := by
  induction context with
  | nil => rfl
  | cons scheme context induction =>
      change
        List.flatMap Scheme.freeTyVars
            (List.map (Scheme.applyFree rho.substitution) context) =
          (List.flatMap Scheme.freeTyVars context).map rho.tyForward
        at induction
      simp [Context.applyFree, Scheme.freeTyVars_apply_variableRenaming,
        induction]

theorem flatMap_freeCapVars_apply_variableRenaming
    (rho : VariableRenaming) (context : Context) :
    (context.applyFree rho.substitution).flatMap Scheme.freeCapVars =
      (context.flatMap Scheme.freeCapVars).map rho.capForward := by
  induction context with
  | nil => rfl
  | cons scheme context induction =>
      change
        List.flatMap Scheme.freeCapVars
            (List.map (Scheme.applyFree rho.substitution) context) =
          (List.flatMap Scheme.freeCapVars context).map rho.capForward
        at induction
      simp [Context.applyFree, Scheme.freeCapVars_apply_variableRenaming,
        induction]

@[simp] theorem freeTyVars_apply_variableRenaming
    (rho : VariableRenaming) (context : Context) :
    (context.applyFree rho.substitution).freeTyVars =
      context.freeTyVars.map rho.tyForward := by
  unfold Context.freeTyVars
  rw [flatMap_freeTyVars_apply_variableRenaming,
    dedupFirst_map_of_injective rho.tyForward rho.tyForward_injective]

@[simp] theorem freeCapVars_apply_variableRenaming
    (rho : VariableRenaming) (context : Context) :
    (context.applyFree rho.substitution).freeCapVars =
      context.freeCapVars.map rho.capForward := by
  unfold Context.freeCapVars
  rw [flatMap_freeCapVars_apply_variableRenaming,
    dedupFirst_map_of_injective rho.capForward rho.capForward_injective]

end Context


mutual

@[simp] theorem Ty.tyVars_apply_variableRenaming
    (rho : VariableRenaming) (target : Ty) :
    (target.apply rho.substitution).tyVars =
      target.tyVars.map rho.tyForward := by
  cases target with
  | var index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [Ty.apply, Ty.tyVars, Ty.tyVars_apply_variableRenaming]
  | prod items =>
      simp [Ty.apply, Ty.tyVars, Ty.tyVarsList_apply_variableRenaming]
  | matcher capability target =>
      simp [Ty.apply, Ty.tyVars, Ty.tyVars_apply_variableRenaming]
  | slot capability target =>
      simp [Ty.apply, Ty.tyVars, Ty.tyVars_apply_variableRenaming]

@[simp] theorem Ty.tyVarsList_apply_variableRenaming
    (rho : VariableRenaming) (items : List Ty) :
    Ty.tyVarsList (Ty.applyList rho.substitution items) =
      (Ty.tyVarsList items).map rho.tyForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Ty.applyList, Ty.tyVarsList,
        Ty.tyVars_apply_variableRenaming,
        Ty.tyVarsList_apply_variableRenaming]

end


mutual

@[simp] theorem Ty.capVars_apply_variableRenaming
    (rho : VariableRenaming) (target : Ty) :
    (target.apply rho.substitution).capVars =
      target.capVars.map rho.capForward := by
  cases target with
  | var index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [Ty.apply, Ty.capVars, Ty.capVars_apply_variableRenaming]
  | prod items =>
      simp [Ty.apply, Ty.capVars, Ty.capVarsList_apply_variableRenaming]
  | matcher capability target =>
      simp [Ty.apply, Ty.capVars, Ty.capVars_apply_variableRenaming,
        Cap.capVars_apply_variableRenaming]
  | slot capability target =>
      simp [Ty.apply, Ty.capVars, Ty.capVars_apply_variableRenaming,
        Cap.capVars_apply_variableRenaming]

@[simp] theorem Ty.capVarsList_apply_variableRenaming
    (rho : VariableRenaming) (items : List Ty) :
    Ty.capVarsList (Ty.applyList rho.substitution items) =
      (Ty.capVarsList items).map rho.capForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Ty.applyList, Ty.capVarsList,
        Ty.capVars_apply_variableRenaming,
        Ty.capVarsList_apply_variableRenaming]

end


mutual

theorem PolyCap.close_variableRenaming
    (rho : VariableRenaming) (boundCap : List CapVar)
    (capability : Cap) :
    PolyCap.close (boundCap.map rho.capForward)
        (capability.apply rho.substitution.cap) =
      (PolyCap.close boundCap capability).applyFree
        rho.substitution.cap := by
  cases capability with
  | any => rfl
  | var index =>
      change
        PolyCap.close (boundCap.map rho.capForward)
            (.var (rho.capForward index)) =
          (PolyCap.close boundCap (.var index)).applyFree
            rho.substitution.cap
      simp only [PolyCap.close]
      by_cases membership : index ∈ boundCap
      · have mappedMembership :
            rho.capForward index ∈
              boundCap.map rho.capForward :=
          (rho.mem_map_capForward_iff index boundCap).mpr membership
        rw [if_pos (List.contains_iff_mem.mpr membership),
          if_pos (List.contains_iff_mem.mpr mappedMembership)]
        simp [PolyCap.applyFree, rho.idxOf_map_capForward]
      · have mappedMembership :
            rho.capForward index ∉
              boundCap.map rho.capForward := by
          intro mapped
          exact membership ((rho.mem_map_capForward_iff index boundCap).mp mapped)
        have sourceFalse : boundCap.contains index = false := by
          apply Bool.eq_false_iff.mpr
          intro present
          exact membership (List.contains_iff_mem.mp present)
        have mappedFalse :
            (boundCap.map rho.capForward).contains
                (rho.capForward index) = false := by
          apply Bool.eq_false_iff.mpr
          intro present
          exact mappedMembership (List.contains_iff_mem.mp present)
        rw [sourceFalse, mappedFalse]
        rfl
  | prod items =>
      simp [Cap.apply, PolyCap.close, PolyCap.applyFree,
        PolyCap.closeList_variableRenaming]

theorem PolyCap.closeList_variableRenaming
    (rho : VariableRenaming) (boundCap : List CapVar)
    (items : List Cap) :
    PolyCap.closeList (boundCap.map rho.capForward)
        (Cap.applyList rho.substitution.cap items) =
      PolyCap.applyFreeList rho.substitution.cap
        (PolyCap.closeList boundCap items) := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Cap.applyList, PolyCap.closeList, PolyCap.applyFreeList,
        PolyCap.close_variableRenaming,
        PolyCap.closeList_variableRenaming]

end


mutual

theorem PolyTy.close_variableRenaming
    (rho : VariableRenaming)
    (boundTy : List TyVar) (boundCap : List CapVar) (target : Ty) :
    PolyTy.close (boundTy.map rho.tyForward)
        (boundCap.map rho.capForward)
        (target.apply rho.substitution) =
      (PolyTy.close boundTy boundCap target).applyFree
        rho.substitution := by
  cases target with
  | var index =>
      change
        PolyTy.close (boundTy.map rho.tyForward)
            (boundCap.map rho.capForward) (.var (rho.tyForward index)) =
          (PolyTy.close boundTy boundCap (.var index)).applyFree
            rho.substitution
      simp only [PolyTy.close]
      by_cases membership : index ∈ boundTy
      · have mappedMembership :
            rho.tyForward index ∈ boundTy.map rho.tyForward :=
          (rho.mem_map_tyForward_iff index boundTy).mpr membership
        rw [if_pos (List.contains_iff_mem.mpr membership),
          if_pos (List.contains_iff_mem.mpr mappedMembership)]
        simp [PolyTy.applyFree, rho.idxOf_map_tyForward]
      · have mappedMembership :
            rho.tyForward index ∉ boundTy.map rho.tyForward := by
          intro mapped
          exact membership ((rho.mem_map_tyForward_iff index boundTy).mp mapped)
        have sourceFalse : boundTy.contains index = false := by
          apply Bool.eq_false_iff.mpr
          intro present
          exact membership (List.contains_iff_mem.mp present)
        have mappedFalse :
            (boundTy.map rho.tyForward).contains
                (rho.tyForward index) = false := by
          apply Bool.eq_false_iff.mpr
          intro present
          exact mappedMembership (List.contains_iff_mem.mp present)
        rw [sourceFalse, mappedFalse]
        rfl
  | int => rfl
  | fn domain codomain =>
      simp [Ty.apply, PolyTy.close, PolyTy.applyFree,
        PolyTy.close_variableRenaming]
  | prod items =>
      simp [Ty.apply, PolyTy.close, PolyTy.applyFree,
        PolyTy.closeList_variableRenaming]
  | matcher capability target =>
      simp [Ty.apply, PolyTy.close, PolyTy.applyFree,
        PolyTy.close_variableRenaming, PolyCap.close_variableRenaming]
  | slot capability target =>
      simp [Ty.apply, PolyTy.close, PolyTy.applyFree,
        PolyTy.close_variableRenaming, PolyCap.close_variableRenaming]

theorem PolyTy.closeList_variableRenaming
    (rho : VariableRenaming)
    (boundTy : List TyVar) (boundCap : List CapVar) (items : List Ty) :
    PolyTy.closeList (boundTy.map rho.tyForward)
        (boundCap.map rho.capForward)
        (Ty.applyList rho.substitution items) =
      PolyTy.applyFreeList rho.substitution
        (PolyTy.closeList boundTy boundCap items) := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Ty.applyList, PolyTy.closeList, PolyTy.applyFreeList,
        PolyTy.close_variableRenaming,
        PolyTy.closeList_variableRenaming]

end


namespace Context

theorem generalizedTyVars_variableRenaming_of_freeVars
    (rho : VariableRenaming) (context : Context) (target : Ty)
    (targetFreeVars :
      (target.apply rho.substitution).tyVars =
        target.tyVars.map rho.tyForward)
    (contextFreeVars :
      (context.applyFree rho.substitution).freeTyVars =
        context.freeTyVars.map rho.tyForward) :
    (context.applyFree rho.substitution).generalizedTyVars
        (target.apply rho.substitution) =
      (context.generalizedTyVars target).map rho.tyForward := by
  unfold Context.generalizedTyVars
  rw [targetFreeVars, contextFreeVars,
    filterMap_excluding_of_injective rho.tyForward
      rho.tyForward_injective,
    dedupFirst_map_of_injective rho.tyForward
      rho.tyForward_injective]

theorem generalizedCapVars_variableRenaming_of_freeVars
    (rho : VariableRenaming) (context : Context) (target : Ty)
    (targetFreeVars :
      (target.apply rho.substitution).capVars =
        target.capVars.map rho.capForward)
    (contextFreeVars :
      (context.applyFree rho.substitution).freeCapVars =
        context.freeCapVars.map rho.capForward) :
    (context.applyFree rho.substitution).generalizedCapVars
        (target.apply rho.substitution) =
      (context.generalizedCapVars target).map rho.capForward := by
  unfold Context.generalizedCapVars
  rw [targetFreeVars, contextFreeVars,
    filterMap_excluding_of_injective rho.capForward
      rho.capForward_injective,
    dedupFirst_map_of_injective rho.capForward
      rho.capForward_injective]

/-- Generalization commutes with a genuine two-sort rho once the
canonical generalized-variable lists have been transported pointwise.  The
list premises are intentionally explicit: they are false for arbitrary
substitutions and are discharged later from bijectivity plus free-variable
transport. -/
theorem generalize_variableRenaming
    (rho : VariableRenaming) (context : Context) (target : Ty)
    (tyGeneralized :
      (context.applyFree rho.substitution).generalizedTyVars
          (target.apply rho.substitution) =
        (context.generalizedTyVars target).map rho.tyForward)
    (capGeneralized :
      (context.applyFree rho.substitution).generalizedCapVars
          (target.apply rho.substitution) =
        (context.generalizedCapVars target).map rho.capForward) :
    (context.generalize target).applyFree rho.substitution =
      (context.applyFree rho.substitution).generalize
        (target.apply rho.substitution) := by
  apply Scheme.eq_of_fields
  · change
      (context.generalizedTyVars target).length =
        ((context.applyFree rho.substitution).generalizedTyVars
          (target.apply rho.substitution)).length
    rw [tyGeneralized, List.length_map]
  · change
      (context.generalizedCapVars target).length =
        ((context.applyFree rho.substitution).generalizedCapVars
          (target.apply rho.substitution)).length
    rw [capGeneralized, List.length_map]
  · simp only [Context.generalize, Scheme.applyFree]
    rw [tyGeneralized, capGeneralized]
    exact (PolyTy.close_variableRenaming rho
      (context.generalizedTyVars target)
      (context.generalizedCapVars target) target).symm

/-- Convenient form of `generalize_variableRenaming` whose premises are only
the four finite free-variable transport equations. -/
theorem generalize_variableRenaming_of_freeVars
    (rho : VariableRenaming) (context : Context) (target : Ty)
    (targetTyVars :
      (target.apply rho.substitution).tyVars =
        target.tyVars.map rho.tyForward)
    (targetCapVars :
      (target.apply rho.substitution).capVars =
        target.capVars.map rho.capForward)
    (contextTyVars :
      (context.applyFree rho.substitution).freeTyVars =
        context.freeTyVars.map rho.tyForward)
    (contextCapVars :
      (context.applyFree rho.substitution).freeCapVars =
        context.freeCapVars.map rho.capForward) :
    (context.generalize target).applyFree rho.substitution =
      (context.applyFree rho.substitution).generalize
        (target.apply rho.substitution) := by
  apply Context.generalize_variableRenaming rho context target
  · exact Context.generalizedTyVars_variableRenaming_of_freeVars
      rho context target targetTyVars contextTyVars
  · exact Context.generalizedCapVars_variableRenaming_of_freeVars
      rho context target targetCapVars contextCapVars

/-- Unconditional coherence for a genuine bijective two-sort change of
names.  The restriction is on `rho`: no corresponding theorem is valid for
an arbitrary substitution. -/
theorem generalize_variableRenaming_exact
    (rho : VariableRenaming) (context : Context) (target : Ty) :
    (context.generalize target).applyFree rho.substitution =
      (context.applyFree rho.substitution).generalize
        (target.apply rho.substitution) := by
  apply Context.generalize_variableRenaming_of_freeVars rho context target
  · exact Ty.tyVars_apply_variableRenaming rho target
  · exact Ty.capVars_apply_variableRenaming rho target
  · exact Context.freeTyVars_apply_variableRenaming rho context
  · exact Context.freeCapVars_apply_variableRenaming rho context

end Context

end TypePM.Source
