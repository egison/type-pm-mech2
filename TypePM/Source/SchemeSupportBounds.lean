import TypePM.AbsorbingSupportRange
import TypePM.Source.SupplyWellFormed

/-!
# Support bounds through scheme and context substitution

This module transports two-sorted support information through the
capture-free substitution operation on polymorphic schemes.  Its endpoint
turns localization of a substitution into the numeric `initialSupply` bound
needed at a source `letE` boundary.
-/

namespace TypePM
namespace Source

mutual

@[simp] theorem PolyCap.freeCapVars_ofCap (capability : Cap) :
    (PolyCap.ofCap capability).freeCapVars = capability.capVars := by
  cases capability with
  | any => rfl
  | var index => rfl
  | prod items =>
      simp [PolyCap.ofCap, PolyCap.freeCapVars,
        PolyCap.freeCapVarsList_ofCapList, Cap.capVars]

@[simp] theorem PolyCap.freeCapVarsList_ofCapList (items : List Cap) :
    PolyCap.freeCapVarsList (PolyCap.ofCapList items) =
      Cap.capVarsList items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.ofCapList, PolyCap.freeCapVarsList,
        PolyCap.freeCapVars_ofCap,
        PolyCap.freeCapVarsList_ofCapList, Cap.capVarsList]

end

mutual

theorem Cap.mem_capVars_iff_unificationVars
    (index : CapVar) (capability : Cap) :
    index ∈ capability.capVars ↔ .cap index ∈ capability.unificationVars := by
  cases capability with
  | any => simp [Cap.capVars, Cap.unificationVars]
  | var candidate => simp [Cap.capVars, Cap.unificationVars]
  | prod items =>
      exact Cap.mem_capVarsList_iff_unificationVarsList index items

theorem Cap.mem_capVarsList_iff_unificationVarsList
    (index : CapVar) (items : List Cap) :
    index ∈ Cap.capVarsList items ↔
      .cap index ∈ Cap.unificationVarsList items := by
  cases items with
  | nil => simp [Cap.capVarsList, Cap.unificationVarsList]
  | cons item items =>
      simp [Cap.capVarsList, Cap.unificationVarsList,
        Cap.mem_capVars_iff_unificationVars,
        Cap.mem_capVarsList_iff_unificationVarsList]

end

mutual

theorem Ty.mem_tyVars_iff_unificationVars
    (index : TyVar) (target : Ty) :
    index ∈ target.tyVars ↔ .ty index ∈ target.unificationVars := by
  cases target with
  | var candidate => simp [Ty.tyVars, Ty.unificationVars]
  | int => simp [Ty.tyVars, Ty.unificationVars]
  | fn domain codomain =>
      simp [Ty.tyVars, Ty.unificationVars,
        Ty.mem_tyVars_iff_unificationVars]
  | prod items => exact Ty.mem_tyVarsList_iff_unificationVarsList index items
  | matcher capability target =>
      simp [Ty.tyVars, Ty.unificationVars,
        Ty.mem_tyVars_iff_unificationVars]
  | slot capability target =>
      simp [Ty.tyVars, Ty.unificationVars,
        Ty.mem_tyVars_iff_unificationVars]

theorem Ty.mem_tyVarsList_iff_unificationVarsList
    (index : TyVar) (items : List Ty) :
    index ∈ Ty.tyVarsList items ↔ .ty index ∈ Ty.unificationVarsList items := by
  cases items with
  | nil => simp [Ty.tyVarsList, Ty.unificationVarsList]
  | cons item items =>
      simp [Ty.tyVarsList, Ty.unificationVarsList,
        Ty.mem_tyVars_iff_unificationVars,
        Ty.mem_tyVarsList_iff_unificationVarsList]

end

mutual

theorem Ty.mem_capVars_iff_unificationVars
    (index : CapVar) (target : Ty) :
    index ∈ target.capVars ↔ .cap index ∈ target.unificationVars := by
  cases target with
  | var candidate => simp [Ty.capVars, Ty.unificationVars]
  | int => simp [Ty.capVars, Ty.unificationVars]
  | fn domain codomain =>
      simp [Ty.capVars, Ty.unificationVars,
        Ty.mem_capVars_iff_unificationVars]
  | prod items => exact Ty.mem_capVarsList_iff_unificationVarsList index items
  | matcher capability target =>
      simp [Ty.capVars, Ty.unificationVars,
        Cap.mem_capVars_iff_unificationVars,
        Ty.mem_capVars_iff_unificationVars]
  | slot capability target =>
      simp [Ty.capVars, Ty.unificationVars,
        Cap.mem_capVars_iff_unificationVars,
        Ty.mem_capVars_iff_unificationVars]

theorem Ty.mem_capVarsList_iff_unificationVarsList
    (index : CapVar) (items : List Ty) :
    index ∈ Ty.capVarsList items ↔ .cap index ∈ Ty.unificationVarsList items := by
  cases items with
  | nil => simp [Ty.capVarsList, Ty.unificationVarsList]
  | cons item items =>
      simp [Ty.capVarsList, Ty.unificationVarsList,
        Ty.mem_capVars_iff_unificationVars,
        Ty.mem_capVarsList_iff_unificationVarsList]

end

mutual

@[simp] theorem PolyTy.freeTyVars_ofTy (target : Ty) :
    (PolyTy.ofTy target).freeTyVars = target.tyVars := by
  cases target with
  | var index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.ofTy, PolyTy.freeTyVars,
        PolyTy.freeTyVars_ofTy, Ty.tyVars]
  | prod items =>
      simp [PolyTy.ofTy, PolyTy.freeTyVars,
        PolyTy.freeTyVarsList_ofTyList, Ty.tyVars]
  | matcher capability target =>
      simp [PolyTy.ofTy, PolyTy.freeTyVars,
        PolyTy.freeTyVars_ofTy, Ty.tyVars]
  | slot capability target =>
      simp [PolyTy.ofTy, PolyTy.freeTyVars,
        PolyTy.freeTyVars_ofTy, Ty.tyVars]

@[simp] theorem PolyTy.freeTyVarsList_ofTyList (items : List Ty) :
    PolyTy.freeTyVarsList (PolyTy.ofTyList items) = Ty.tyVarsList items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.ofTyList, PolyTy.freeTyVarsList,
        PolyTy.freeTyVars_ofTy,
        PolyTy.freeTyVarsList_ofTyList, Ty.tyVarsList]

end

mutual

@[simp] theorem PolyTy.freeCapVars_ofTy (target : Ty) :
    (PolyTy.ofTy target).freeCapVars = target.capVars := by
  cases target with
  | var index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.ofTy, PolyTy.freeCapVars,
        PolyTy.freeCapVars_ofTy, Ty.capVars]
  | prod items =>
      simp [PolyTy.ofTy, PolyTy.freeCapVars,
        PolyTy.freeCapVarsList_ofTyList, Ty.capVars]
  | matcher capability target =>
      simp [PolyTy.ofTy, PolyTy.freeCapVars,
        PolyCap.freeCapVars_ofCap, PolyTy.freeCapVars_ofTy, Ty.capVars]
  | slot capability target =>
      simp [PolyTy.ofTy, PolyTy.freeCapVars,
        PolyCap.freeCapVars_ofCap, PolyTy.freeCapVars_ofTy, Ty.capVars]

@[simp] theorem PolyTy.freeCapVarsList_ofTyList (items : List Ty) :
    PolyTy.freeCapVarsList (PolyTy.ofTyList items) = Ty.capVarsList items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.ofTyList, PolyTy.freeCapVarsList,
        PolyTy.freeCapVars_ofTy,
        PolyTy.freeCapVarsList_ofTyList, Ty.capVarsList]

end

mutual

/-- Every free capability name after applying a capability substitution
comes from the image of a free capability name before substitution. -/
theorem PolyCap.freeCap_applyFree_origin
    (substitution : CapSubst) (capability : PolyCap)
    {candidate : CapVar}
    (member : candidate ∈ (capability.applyFree substitution).freeCapVars) :
    ∃ input, input ∈ capability.freeCapVars ∧
      .cap candidate ∈ (substitution input).unificationVars := by
  cases capability with
  | any => simp [PolyCap.applyFree, PolyCap.freeCapVars] at member
  | free input =>
      refine ⟨input, by simp [PolyCap.freeCapVars], ?_⟩
      apply (Cap.mem_capVars_iff_unificationVars candidate
        (substitution input)).mp
      simpa [PolyCap.applyFree, PolyCap.freeCapVars_ofCap] using member
  | bound position => simp [PolyCap.applyFree, PolyCap.freeCapVars] at member
  | prod items =>
      exact PolyCap.freeCapList_applyFree_origin substitution items member

theorem PolyCap.freeCapList_applyFree_origin
    (substitution : CapSubst) (items : List PolyCap)
    {candidate : CapVar}
    (member : candidate ∈
      PolyCap.freeCapVarsList (PolyCap.applyFreeList substitution items)) :
    ∃ input, input ∈ PolyCap.freeCapVarsList items ∧
      .cap candidate ∈ (substitution input).unificationVars := by
  cases items with
  | nil => simp [PolyCap.applyFreeList, PolyCap.freeCapVarsList] at member
  | cons item items =>
      simp only [PolyCap.applyFreeList, PolyCap.freeCapVarsList,
        List.mem_append] at member
      rcases member with head | tail
      · obtain ⟨input, inputMember, imageMember⟩ :=
          PolyCap.freeCap_applyFree_origin substitution item head
        exact ⟨input, by
          simpa [PolyCap.freeCapVarsList] using Or.inl inputMember,
          imageMember⟩
      · obtain ⟨input, inputMember, imageMember⟩ :=
          PolyCap.freeCapList_applyFree_origin substitution items tail
        exact ⟨input, by
          simpa [PolyCap.freeCapVarsList] using Or.inr inputMember,
          imageMember⟩

end


mutual

/-- Every free ordinary type variable after applying a substitution comes
from the type image of an originally free ordinary variable. -/
theorem PolyTy.freeTy_applyFree_origin
    (substitution : Subst) (target : PolyTy) {candidate : TyVar}
    (member : candidate ∈ (target.applyFree substitution).freeTyVars) :
    ∃ input, input ∈ target.freeTyVars ∧
      .ty candidate ∈ (substitution.ty input).unificationVars := by
  cases target with
  | free input =>
      refine ⟨input, by simp [PolyTy.freeTyVars], ?_⟩
      apply (Ty.mem_tyVars_iff_unificationVars candidate
        (substitution.ty input)).mp
      simpa [PolyTy.applyFree, PolyTy.freeTyVars_ofTy] using member
  | bound position => simp [PolyTy.applyFree, PolyTy.freeTyVars] at member
  | int => simp [PolyTy.applyFree, PolyTy.freeTyVars] at member
  | fn domain codomain =>
      simp only [PolyTy.applyFree, PolyTy.freeTyVars,
        List.mem_append] at member
      rcases member with left | right
      · obtain ⟨input, inputMember, imageMember⟩ :=
          PolyTy.freeTy_applyFree_origin substitution domain left
        exact ⟨input, by
          simpa [PolyTy.freeTyVars] using Or.inl inputMember, imageMember⟩
      · obtain ⟨input, inputMember, imageMember⟩ :=
          PolyTy.freeTy_applyFree_origin substitution codomain right
        exact ⟨input, by
          simpa [PolyTy.freeTyVars] using Or.inr inputMember, imageMember⟩
  | prod items =>
      exact PolyTy.freeTyList_applyFree_origin substitution items member
  | matcher capability target =>
      obtain ⟨input, inputMember, imageMember⟩ :=
        PolyTy.freeTy_applyFree_origin substitution target member
      exact ⟨input, by simpa [PolyTy.freeTyVars] using inputMember,
        imageMember⟩
  | slot capability target =>
      obtain ⟨input, inputMember, imageMember⟩ :=
        PolyTy.freeTy_applyFree_origin substitution target member
      exact ⟨input, by simpa [PolyTy.freeTyVars] using inputMember,
        imageMember⟩

theorem PolyTy.freeTyList_applyFree_origin
    (substitution : Subst) (items : List PolyTy) {candidate : TyVar}
    (member : candidate ∈
      PolyTy.freeTyVarsList (PolyTy.applyFreeList substitution items)) :
    ∃ input, input ∈ PolyTy.freeTyVarsList items ∧
      .ty candidate ∈ (substitution.ty input).unificationVars := by
  cases items with
  | nil => simp [PolyTy.applyFreeList, PolyTy.freeTyVarsList] at member
  | cons item items =>
      simp only [PolyTy.applyFreeList, PolyTy.freeTyVarsList,
        List.mem_append] at member
      rcases member with head | tail
      · obtain ⟨input, inputMember, imageMember⟩ :=
          PolyTy.freeTy_applyFree_origin substitution item head
        exact ⟨input, by
          simpa [PolyTy.freeTyVarsList] using Or.inl inputMember, imageMember⟩
      · obtain ⟨input, inputMember, imageMember⟩ :=
          PolyTy.freeTyList_applyFree_origin substitution items tail
        exact ⟨input, by
          simpa [PolyTy.freeTyVarsList] using Or.inr inputMember, imageMember⟩

end


mutual

/-- A free capability name after applying a type substitution comes either
from a type image or from a capability image of an original free name. -/
theorem PolyTy.freeCap_applyFree_origin
    (substitution : Subst) (target : PolyTy) {candidate : CapVar}
    (member : candidate ∈ (target.applyFree substitution).freeCapVars) :
    (∃ input, input ∈ target.freeTyVars ∧
      .cap candidate ∈ (substitution.ty input).unificationVars) ∨
    (∃ input, input ∈ target.freeCapVars ∧
      .cap candidate ∈ (substitution.cap input).unificationVars) := by
  cases target with
  | free input =>
      apply Or.inl
      refine ⟨input, by simp [PolyTy.freeTyVars], ?_⟩
      apply (Ty.mem_capVars_iff_unificationVars candidate
        (substitution.ty input)).mp
      simpa [PolyTy.applyFree, PolyTy.freeCapVars_ofTy] using member
  | bound position => simp [PolyTy.applyFree, PolyTy.freeCapVars] at member
  | int => simp [PolyTy.applyFree, PolyTy.freeCapVars] at member
  | fn domain codomain =>
      simp only [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeTyVars, List.mem_append] at member ⊢
      rcases member with left | right
      · rcases PolyTy.freeCap_applyFree_origin substitution domain left with
        tyOrigin | capOrigin
        · obtain ⟨input, inputMember, imageMember⟩ := tyOrigin
          exact Or.inl ⟨input, Or.inl inputMember, imageMember⟩
        · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
          exact Or.inr ⟨input, Or.inl inputMember, imageMember⟩
      · rcases PolyTy.freeCap_applyFree_origin substitution codomain right with
        tyOrigin | capOrigin
        · obtain ⟨input, inputMember, imageMember⟩ := tyOrigin
          exact Or.inl ⟨input, Or.inr inputMember, imageMember⟩
        · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
          exact Or.inr ⟨input, Or.inr inputMember, imageMember⟩
  | prod items =>
      exact PolyTy.freeCapList_applyFree_origin substitution items member
  | matcher capability target =>
      simp only [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeTyVars, List.mem_append] at member ⊢
      rcases member with capabilityMember | targetMember
      · obtain ⟨input, inputMember, imageMember⟩ :=
          PolyCap.freeCap_applyFree_origin substitution.cap capability
            capabilityMember
        exact Or.inr ⟨input, Or.inl inputMember, imageMember⟩
      · rcases PolyTy.freeCap_applyFree_origin substitution target targetMember with
          tyOrigin | capOrigin
        · exact Or.inl tyOrigin
        · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
          exact Or.inr ⟨input, Or.inr inputMember, imageMember⟩
  | slot capability target =>
      simp only [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeTyVars, List.mem_append] at member ⊢
      rcases member with capabilityMember | targetMember
      · obtain ⟨input, inputMember, imageMember⟩ :=
          PolyCap.freeCap_applyFree_origin substitution.cap capability
            capabilityMember
        exact Or.inr ⟨input, Or.inl inputMember, imageMember⟩
      · rcases PolyTy.freeCap_applyFree_origin substitution target targetMember with
          tyOrigin | capOrigin
        · exact Or.inl tyOrigin
        · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
          exact Or.inr ⟨input, Or.inr inputMember, imageMember⟩

theorem PolyTy.freeCapList_applyFree_origin
    (substitution : Subst) (items : List PolyTy) {candidate : CapVar}
    (member : candidate ∈
      PolyTy.freeCapVarsList (PolyTy.applyFreeList substitution items)) :
    (∃ input, input ∈ PolyTy.freeTyVarsList items ∧
      .cap candidate ∈ (substitution.ty input).unificationVars) ∨
    (∃ input, input ∈ PolyTy.freeCapVarsList items ∧
      .cap candidate ∈ (substitution.cap input).unificationVars) := by
  cases items with
  | nil => simp [PolyTy.applyFreeList, PolyTy.freeCapVarsList] at member
  | cons item items =>
      simp only [PolyTy.applyFreeList, PolyTy.freeCapVarsList,
        PolyTy.freeTyVarsList, List.mem_append] at member ⊢
      rcases member with head | tail
      · rcases PolyTy.freeCap_applyFree_origin substitution item head with
        tyOrigin | capOrigin
        · obtain ⟨input, inputMember, imageMember⟩ := tyOrigin
          exact Or.inl ⟨input, Or.inl inputMember, imageMember⟩
        · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
          exact Or.inr ⟨input, Or.inl inputMember, imageMember⟩
      · rcases PolyTy.freeCapList_applyFree_origin substitution items tail with
        tyOrigin | capOrigin
        · obtain ⟨input, inputMember, imageMember⟩ := tyOrigin
          exact Or.inl ⟨input, Or.inr inputMember, imageMember⟩
        · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
          exact Or.inr ⟨input, Or.inr inputMember, imageMember⟩

end


mutual

theorem PolyCap.openBound_supply_cap_origin
    (capability : PolyCap) (capArity : Nat) (supply : Supply)
    (wellScoped : capability.WellScoped capArity) {candidate : CapVar}
    (member : candidate ∈
      (capability.openBound
        (fun position => .var (Scheme.boundCapInstance supply position))).capVars) :
    candidate ∈ capability.freeCapVars ∨
      ∃ position, position < capArity ∧
        candidate = Scheme.boundCapInstance supply position := by
  cases capability with
  | any => simp [PolyCap.openBound, Cap.capVars] at member
  | free index =>
      exact Or.inl (by simpa [PolyCap.openBound, Cap.capVars,
        PolyCap.freeCapVars] using member)
  | bound position =>
      have valid : position < capArity := by
        simpa [PolyCap.WellScoped] using wellScoped
      exact Or.inr ⟨position, valid, by
        simpa [PolyCap.openBound, Cap.capVars] using member⟩
  | prod items =>
      have itemsScoped : ∀ item ∈ items, item.WellScoped capArity := by
        simpa [PolyCap.WellScoped] using wellScoped
      exact PolyCap.openBoundList_supply_cap_origin items capArity supply
        itemsScoped member

theorem PolyCap.openBoundList_supply_cap_origin
    (items : List PolyCap) (capArity : Nat) (supply : Supply)
    (wellScoped : ∀ item ∈ items, item.WellScoped capArity)
    {candidate : CapVar}
    (member : candidate ∈ Cap.capVarsList
      (PolyCap.openBoundList
        (fun position => .var (Scheme.boundCapInstance supply position))
        items)) :
    candidate ∈ PolyCap.freeCapVarsList items ∨
      ∃ position, position < capArity ∧
        candidate = Scheme.boundCapInstance supply position := by
  cases items with
  | nil => simp [PolyCap.openBoundList, Cap.capVarsList] at member
  | cons item items =>
      simp only [PolyCap.openBoundList, Cap.capVarsList,
        List.mem_append] at member
      rcases member with head | tail
      · rcases PolyCap.openBound_supply_cap_origin item capArity supply
          (wellScoped item (by simp)) head with free | bound
        · exact Or.inl (by
            simpa [PolyCap.freeCapVarsList] using Or.inl free)
        · exact Or.inr bound
      · rcases PolyCap.openBoundList_supply_cap_origin items capArity supply
          (fun candidate candidateMember => wellScoped candidate (by simp [candidateMember]))
          tail with free | bound
        · exact Or.inl (by
            simpa [PolyCap.freeCapVarsList] using Or.inr free)
        · exact Or.inr bound

end


mutual

theorem PolyTy.openBound_supply_ty_origin
    (target : PolyTy) (tyArity capArity : Nat) (supply : Supply)
    (wellScoped : target.WellScoped tyArity capArity) {candidate : TyVar}
    (member : candidate ∈
      (target.openBound
        (fun position => .var (Scheme.boundTyInstance supply position))
        (fun position => .var (Scheme.boundCapInstance supply position))).tyVars) :
    candidate ∈ target.freeTyVars ∨
      ∃ position, position < tyArity ∧
        candidate = Scheme.boundTyInstance supply position := by
  cases target with
  | free index =>
      exact Or.inl (by simpa [PolyTy.openBound, Ty.tyVars,
        PolyTy.freeTyVars] using member)
  | bound position =>
      have valid : position < tyArity := by
        simpa [PolyTy.WellScoped] using wellScoped
      exact Or.inr ⟨position, valid, by
        simpa [PolyTy.openBound, Ty.tyVars] using member⟩
  | int => simp [PolyTy.openBound, Ty.tyVars] at member
  | fn domain codomain =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.openBound, Ty.tyVars, List.mem_append] at member
      rcases member with left | right
      · rcases PolyTy.openBound_supply_ty_origin domain tyArity capArity
          supply wellScoped.1 left with free | bound
        · exact Or.inl (by simpa [PolyTy.freeTyVars] using Or.inl free)
        · exact Or.inr bound
      · rcases PolyTy.openBound_supply_ty_origin codomain tyArity capArity
          supply wellScoped.2 right with free | bound
        · exact Or.inl (by simpa [PolyTy.freeTyVars] using Or.inr free)
        · exact Or.inr bound
  | prod items =>
      have itemsScoped : ∀ item ∈ items,
          item.WellScoped tyArity capArity := by
        simpa [PolyTy.WellScoped] using wellScoped
      exact PolyTy.openBoundList_supply_ty_origin items tyArity capArity
        supply itemsScoped member
  | matcher capability target =>
      have parts : capability.WellScoped capArity ∧
          target.WellScoped tyArity capArity := by
        simpa [PolyTy.WellScoped] using wellScoped
      exact PolyTy.openBound_supply_ty_origin target tyArity capArity supply
        parts.2 member
  | slot capability target =>
      have parts : capability.WellScoped capArity ∧
          target.WellScoped tyArity capArity := by
        simpa [PolyTy.WellScoped] using wellScoped
      exact PolyTy.openBound_supply_ty_origin target tyArity capArity supply
        parts.2 member

theorem PolyTy.openBoundList_supply_ty_origin
    (items : List PolyTy) (tyArity capArity : Nat) (supply : Supply)
    (wellScoped : ∀ item ∈ items, item.WellScoped tyArity capArity)
    {candidate : TyVar}
    (member : candidate ∈ Ty.tyVarsList
      (PolyTy.openBoundList
        (fun position => .var (Scheme.boundTyInstance supply position))
        (fun position => .var (Scheme.boundCapInstance supply position))
        items)) :
    candidate ∈ PolyTy.freeTyVarsList items ∨
      ∃ position, position < tyArity ∧
        candidate = Scheme.boundTyInstance supply position := by
  cases items with
  | nil => simp [PolyTy.openBoundList, Ty.tyVarsList] at member
  | cons item items =>
      simp only [PolyTy.openBoundList, Ty.tyVarsList,
        List.mem_append] at member
      rcases member with head | tail
      · rcases PolyTy.openBound_supply_ty_origin item tyArity capArity supply
          (wellScoped item (by simp)) head with free | bound
        · exact Or.inl (by simpa [PolyTy.freeTyVarsList] using Or.inl free)
        · exact Or.inr bound
      · rcases PolyTy.openBoundList_supply_ty_origin items tyArity capArity
          supply
          (fun candidate candidateMember => wellScoped candidate (by simp [candidateMember]))
          tail with free | bound
        · exact Or.inl (by simpa [PolyTy.freeTyVarsList] using Or.inr free)
        · exact Or.inr bound

end


mutual

theorem PolyTy.openBound_supply_cap_origin
    (target : PolyTy) (tyArity capArity : Nat) (supply : Supply)
    (wellScoped : target.WellScoped tyArity capArity) {candidate : CapVar}
    (member : candidate ∈
      (target.openBound
        (fun position => .var (Scheme.boundTyInstance supply position))
        (fun position => .var (Scheme.boundCapInstance supply position))).capVars) :
    candidate ∈ target.freeCapVars ∨
      ∃ position, position < capArity ∧
        candidate = Scheme.boundCapInstance supply position := by
  cases target with
  | free index => simp [PolyTy.openBound, Ty.capVars] at member
  | bound position => simp [PolyTy.openBound, Ty.capVars] at member
  | int => simp [PolyTy.openBound, Ty.capVars] at member
  | fn domain codomain =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.openBound, Ty.capVars, List.mem_append] at member
      rcases member with left | right
      · rcases PolyTy.openBound_supply_cap_origin domain tyArity capArity
          supply wellScoped.1 left with free | bound
        · exact Or.inl (by simpa [PolyTy.freeCapVars] using Or.inl free)
        · exact Or.inr bound
      · rcases PolyTy.openBound_supply_cap_origin codomain tyArity capArity
          supply wellScoped.2 right with free | bound
        · exact Or.inl (by simpa [PolyTy.freeCapVars] using Or.inr free)
        · exact Or.inr bound
  | prod items =>
      have itemsScoped : ∀ item ∈ items,
          item.WellScoped tyArity capArity := by
        simpa [PolyTy.WellScoped] using wellScoped
      exact PolyTy.openBoundList_supply_cap_origin items tyArity capArity
        supply itemsScoped member
  | matcher capability target =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.openBound, Ty.capVars, List.mem_append] at member
      rcases member with capabilityMember | targetMember
      · rcases PolyCap.openBound_supply_cap_origin capability capArity supply
          wellScoped.1 capabilityMember with free | bound
        · exact Or.inl (by simpa [PolyTy.freeCapVars] using Or.inl free)
        · exact Or.inr bound
      · rcases PolyTy.openBound_supply_cap_origin target tyArity capArity
          supply wellScoped.2 targetMember with free | bound
        · exact Or.inl (by simpa [PolyTy.freeCapVars] using Or.inr free)
        · exact Or.inr bound
  | slot capability target =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.openBound, Ty.capVars, List.mem_append] at member
      rcases member with capabilityMember | targetMember
      · rcases PolyCap.openBound_supply_cap_origin capability capArity supply
          wellScoped.1 capabilityMember with free | bound
        · exact Or.inl (by simpa [PolyTy.freeCapVars] using Or.inl free)
        · exact Or.inr bound
      · rcases PolyTy.openBound_supply_cap_origin target tyArity capArity
          supply wellScoped.2 targetMember with free | bound
        · exact Or.inl (by simpa [PolyTy.freeCapVars] using Or.inr free)
        · exact Or.inr bound

theorem PolyTy.openBoundList_supply_cap_origin
    (items : List PolyTy) (tyArity capArity : Nat) (supply : Supply)
    (wellScoped : ∀ item ∈ items, item.WellScoped tyArity capArity)
    {candidate : CapVar}
    (member : candidate ∈ Ty.capVarsList
      (PolyTy.openBoundList
        (fun position => .var (Scheme.boundTyInstance supply position))
        (fun position => .var (Scheme.boundCapInstance supply position))
        items)) :
    candidate ∈ PolyTy.freeCapVarsList items ∨
      ∃ position, position < capArity ∧
        candidate = Scheme.boundCapInstance supply position := by
  cases items with
  | nil => simp [PolyTy.openBoundList, Ty.capVarsList] at member
  | cons item items =>
      simp only [PolyTy.openBoundList, Ty.capVarsList,
        List.mem_append] at member
      rcases member with head | tail
      · rcases PolyTy.openBound_supply_cap_origin item tyArity capArity supply
          (wellScoped item (by simp)) head with free | bound
        · exact Or.inl (by simpa [PolyTy.freeCapVarsList] using Or.inl free)
        · exact Or.inr bound
      · rcases PolyTy.openBoundList_supply_cap_origin items tyArity capArity
          supply
          (fun candidate candidateMember => wellScoped candidate (by simp [candidateMember]))
          tail with free | bound
        · exact Or.inl (by simpa [PolyTy.freeCapVarsList] using Or.inr free)
        · exact Or.inr bound

end


/-- Ordinary-variable provenance for canonical scheme instantiation. -/
theorem Scheme.instantiate_ty_origin
    (scheme : Scheme) (supply : Supply) {candidate : TyVar}
    (member : .ty candidate ∈ (scheme.instantiate supply).1.unificationVars) :
    candidate ∈ scheme.freeTyVars ∨
      (supply.ty ≤ candidate.index ∧
        candidate.index < (scheme.instantiate supply).2.ty) := by
  have tyMember : candidate ∈ (scheme.instantiate supply).1.tyVars :=
    (Ty.mem_tyVars_iff_unificationVars candidate _).mpr member
  rcases PolyTy.openBound_supply_ty_origin scheme.body scheme.tyArity
      scheme.capArity supply scheme.wellScoped tyMember with free | bound
  · exact Or.inl (Scheme.mem_freeTyVars.mpr free)
  · obtain ⟨position, valid, rfl⟩ := bound
    exact Or.inr ⟨Scheme.boundTyInstance_ge_start supply position,
      Scheme.boundTyInstance_lt_end scheme supply valid⟩

/-- Capability-variable provenance for canonical scheme instantiation. -/
theorem Scheme.instantiate_cap_origin
    (scheme : Scheme) (supply : Supply) {candidate : CapVar}
    (member : .cap candidate ∈ (scheme.instantiate supply).1.unificationVars) :
    candidate ∈ scheme.freeCapVars ∨
      (supply.cap ≤ candidate.index ∧
        candidate.index < (scheme.instantiate supply).2.cap) := by
  have capMember : candidate ∈ (scheme.instantiate supply).1.capVars :=
    (Ty.mem_capVars_iff_unificationVars candidate _).mpr member
  rcases PolyTy.openBound_supply_cap_origin scheme.body scheme.tyArity
      scheme.capArity supply scheme.wellScoped capMember with free | bound
  · exact Or.inl (Scheme.mem_freeCapVars.mpr free)
  · obtain ⟨position, valid, rfl⟩ := bound
    exact Or.inr ⟨Scheme.boundCapInstance_ge_start supply position,
      Scheme.boundCapInstance_lt_end scheme supply valid⟩


/-- Scheme-level ordinary-variable membership transport. -/
theorem Scheme.freeTy_applyFree_origin
    (substitution : Subst) (scheme : Scheme) {candidate : TyVar}
    (member : candidate ∈ (scheme.applyFree substitution).freeTyVars) :
    ∃ input, input ∈ scheme.freeTyVars ∧
      .ty candidate ∈ (substitution.ty input).unificationVars := by
  rw [Scheme.mem_freeTyVars] at member
  obtain ⟨input, inputMember, imageMember⟩ :=
    PolyTy.freeTy_applyFree_origin substitution scheme.body member
  exact ⟨input, Scheme.mem_freeTyVars.mpr inputMember, imageMember⟩

/-- Scheme-level capability-variable membership transport. -/
theorem Scheme.freeCap_applyFree_origin
    (substitution : Subst) (scheme : Scheme) {candidate : CapVar}
    (member : candidate ∈ (scheme.applyFree substitution).freeCapVars) :
    (∃ input, input ∈ scheme.freeTyVars ∧
      .cap candidate ∈ (substitution.ty input).unificationVars) ∨
    (∃ input, input ∈ scheme.freeCapVars ∧
      .cap candidate ∈ (substitution.cap input).unificationVars) := by
  rw [Scheme.mem_freeCapVars] at member
  rcases PolyTy.freeCap_applyFree_origin substitution scheme.body member with
    tyOrigin | capOrigin
  · obtain ⟨input, inputMember, imageMember⟩ := tyOrigin
    exact Or.inl ⟨input, Scheme.mem_freeTyVars.mpr inputMember, imageMember⟩
  · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
    exact Or.inr ⟨input, Scheme.mem_freeCapVars.mpr inputMember, imageMember⟩


/-- Context-level ordinary-variable membership transport. -/
theorem Context.freeTy_applyFree_origin
    (substitution : Subst) (context : Context) {candidate : TyVar}
    (member : candidate ∈ (context.applyFree substitution).freeTyVars) :
    ∃ input, input ∈ context.freeTyVars ∧
      .ty candidate ∈ (substitution.ty input).unificationVars := by
  rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap] at member
  obtain ⟨appliedScheme, appliedMember, candidateMember⟩ := member
  rw [Context.applyFree, List.mem_map] at appliedMember
  obtain ⟨scheme, schemeMember, rfl⟩ := appliedMember
  obtain ⟨input, inputMember, imageMember⟩ :=
    Scheme.freeTy_applyFree_origin substitution scheme candidateMember
  exact ⟨input, by
    rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
    exact ⟨scheme, schemeMember, inputMember⟩, imageMember⟩

/-- Context-level capability-variable membership transport. -/
theorem Context.freeCap_applyFree_origin
    (substitution : Subst) (context : Context) {candidate : CapVar}
    (member : candidate ∈ (context.applyFree substitution).freeCapVars) :
    (∃ input, input ∈ context.freeTyVars ∧
      .cap candidate ∈ (substitution.ty input).unificationVars) ∨
    (∃ input, input ∈ context.freeCapVars ∧
      .cap candidate ∈ (substitution.cap input).unificationVars) := by
  rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap] at member
  obtain ⟨appliedScheme, appliedMember, candidateMember⟩ := member
  rw [Context.applyFree, List.mem_map] at appliedMember
  obtain ⟨scheme, schemeMember, rfl⟩ := appliedMember
  rcases Scheme.freeCap_applyFree_origin substitution scheme candidateMember with
    tyOrigin | capOrigin
  · obtain ⟨input, inputMember, imageMember⟩ := tyOrigin
    exact Or.inl ⟨input, by
      rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
      exact ⟨scheme, schemeMember, inputMember⟩, imageMember⟩
  · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
    exact Or.inr ⟨input, by
      rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap]
      exact ⟨scheme, schemeMember, inputMember⟩, imageMember⟩


theorem TyVar.next_le_of_forall_lt
    {indices : List TyVar} {bound : Nat}
    (bounded : ∀ index, index ∈ indices → index.index < bound) :
    TyVar.next indices ≤ bound := by
  induction indices with
  | nil => simp [TyVar.next]
  | cons index indices induction =>
      simp only [TyVar.next]
      have head := bounded index (by simp)
      have tail := induction (fun candidate member =>
        bounded candidate (by simp [member]))
      omega

theorem CapVar.next_le_of_forall_lt
    {indices : List CapVar} {bound : Nat}
    (bounded : ∀ index, index ∈ indices → index.index < bound) :
    CapVar.next indices ≤ bound := by
  induction indices with
  | nil => simp [CapVar.next]
  | cons index indices induction =>
      simp only [CapVar.next]
      have head := bounded index (by simp)
      have tail := induction (fun candidate member =>
        bounded candidate (by simp [member]))
      omega

/-- Main endpoint: a localized substitution whose finite support is below a
bound keeps the substituted context's root supply below that bound. -/
theorem Context.applyFree_initialSupply_le_of_localized
    {support : List UnificationVar} {substitution : Subst}
    (localized : Subst.Localized support substitution)
    (context : Context) (bound : Supply)
    (contextBelow : context.initialSupply.Le bound)
    (supportBelow : ∀ candidate, candidate ∈ support →
      candidate.Below bound.ty bound.cap) :
    (context.applyFree substitution).initialSupply.Le bound := by
  constructor
  · apply TyVar.next_le_of_forall_lt
    intro candidate member
    obtain ⟨input, inputMember, imageMember⟩ :=
      context.freeTy_applyFree_origin substitution
        (mem_dedupFirst.mpr member)
    have inputBelow := Nat.lt_of_lt_of_le
      (context.freeTy_index_lt_initialSupply inputMember) contextBelow.1
    exact localized.tyImage_below supportBelow input inputBelow
      (.ty candidate) imageMember
  · apply CapVar.next_le_of_forall_lt
    intro candidate member
    rcases context.freeCap_applyFree_origin substitution
        (mem_dedupFirst.mpr member) with
      tyOrigin | capOrigin
    · obtain ⟨input, inputMember, imageMember⟩ := tyOrigin
      have inputBelow := Nat.lt_of_lt_of_le
        (context.freeTy_index_lt_initialSupply inputMember) contextBelow.1
      exact localized.tyImage_below supportBelow input inputBelow
        (.cap candidate) imageMember
    · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
      have inputBelow := Nat.lt_of_lt_of_le
        (context.freeCap_index_lt_initialSupply inputMember) contextBelow.2
      exact localized.capImage_below supportBelow input inputBelow
        (.cap candidate) imageMember

end Source

end TypePM
