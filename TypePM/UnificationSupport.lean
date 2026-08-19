import TypePM.AbsorbingUnification

/-!
# Finite support of executable unification

The concrete unifier only mentions variables already present in its input.
This is stronger than the usual frame property: images of mentioned
variables cannot contain newly invented variables either.
-/

namespace TypePM

/-- A substitution is confined to a finite list of two-sorted variables. -/
structure Subst.Localized (support : List UnificationVar)
    (substitution : Subst) : Prop where
  fixesTy : ∀ index, .ty index ∉ support →
    substitution.ty index = .var index
  fixesCap : ∀ index, .cap index ∉ support →
    substitution.cap index = .var index
  tyRange : ∀ index, .ty index ∈ support →
    ∀ candidate, candidate ∈ (substitution.ty index).unificationVars →
      candidate ∈ support
  capRange : ∀ index, .cap index ∈ support →
    ∀ candidate, candidate ∈ (substitution.cap index).unificationVars →
      candidate ∈ support

namespace Subst.Localized

theorem id (support : List UnificationVar) :
    Subst.Localized support Subst.id := by
  constructor
  · intro index _
    rfl
  · intro index _
    rfl
  · intro index member candidate imageMember
    have equality : candidate = .ty index := by
      simpa [Subst.id, Ty.unificationVars] using imageMember
    simpa [equality] using member
  · intro index member candidate imageMember
    have equality : candidate = .cap index := by
      simpa [Subst.id, Cap.unificationVars] using imageMember
    simpa [equality] using member

mutual

theorem cap_apply_mem
    {support : List UnificationVar} {substitution : Subst}
    (localized : Subst.Localized support substitution)
    (capability : Cap)
    (covered : ∀ candidate, candidate ∈ capability.unificationVars →
      candidate ∈ support) :
    ∀ candidate,
      candidate ∈ (capability.apply substitution.cap).unificationVars →
        candidate ∈ support := by
  intro candidate member
  cases capability with
  | any => simp [Cap.apply, Cap.unificationVars] at member
  | var index =>
      simp only [Cap.apply] at member
      by_cases inSupport : .cap index ∈ support
      · exact localized.capRange index inSupport candidate (by
          simpa [Cap.apply] using member)
      · rw [localized.fixesCap index inSupport] at member
        have equality : candidate = .cap index := by
          simpa [Cap.unificationVars] using member
        subst candidate
        exact covered (.cap index) (by simp [Cap.unificationVars])
  | prod items =>
      exact capList_apply_mem localized items (by
        intro candidate candidateMember
        exact covered candidate (by
          simpa [Cap.unificationVars] using candidateMember)) candidate (by
            simpa [Cap.apply, Cap.unificationVars] using member)
  | con former arguments =>
      exact capList_apply_mem localized arguments (by
        intro candidate candidateMember
        exact covered candidate (by
          simpa [Cap.unificationVars] using candidateMember)) candidate (by
            simpa [Cap.apply, Cap.unificationVars] using member)

theorem capList_apply_mem
    {support : List UnificationVar} {substitution : Subst}
    (localized : Subst.Localized support substitution)
    (items : List Cap)
    (covered : ∀ candidate, candidate ∈ Cap.unificationVarsList items →
      candidate ∈ support) :
    ∀ candidate,
      candidate ∈ Cap.unificationVarsList
        (Cap.applyList substitution.cap items) →
        candidate ∈ support := by
  intro candidate member
  cases items with
  | nil => simp [Cap.applyList, Cap.unificationVarsList] at member
  | cons item items =>
      simp only [Cap.applyList, Cap.unificationVarsList,
        List.mem_append] at member
      rcases member with head | tail
      · apply cap_apply_mem localized item
          (fun candidate candidateMember => covered candidate (by
            simpa [Cap.unificationVarsList] using Or.inl candidateMember))
          candidate head
      · apply capList_apply_mem localized items
          (fun candidate candidateMember => covered candidate (by
            simpa [Cap.unificationVarsList] using Or.inr candidateMember))
          candidate tail

end

mutual

theorem ty_apply_mem
    {support : List UnificationVar} {substitution : Subst}
    (localized : Subst.Localized support substitution)
    (target : Ty)
    (covered : ∀ candidate, candidate ∈ target.unificationVars →
      candidate ∈ support) :
    ∀ candidate,
      candidate ∈ (target.apply substitution).unificationVars →
        candidate ∈ support := by
  intro candidate member
  cases target with
  | var index =>
      simp only [Ty.apply] at member
      by_cases inSupport : .ty index ∈ support
      · exact localized.tyRange index inSupport candidate (by
          simpa [Ty.apply] using member)
      · rw [localized.fixesTy index inSupport] at member
        have equality : candidate = .ty index := by
          simpa [Ty.unificationVars] using member
        subst candidate
        exact covered (.ty index) (by simp [Ty.unificationVars])
  | int => simp [Ty.apply, Ty.unificationVars] at member
  | fn domain codomain =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member
      rcases member with left | right
      · apply ty_apply_mem localized domain
          (fun candidate candidateMember => covered candidate (by
            simpa [Ty.unificationVars] using Or.inl candidateMember))
          candidate left
      · apply ty_apply_mem localized codomain
          (fun candidate candidateMember => covered candidate (by
            simpa [Ty.unificationVars] using Or.inr candidateMember))
          candidate right
  | prod items =>
      exact tyList_apply_mem localized items (by
        intro candidate candidateMember
        exact covered candidate (by
          simpa [Ty.unificationVars] using candidateMember)) candidate (by
            simpa [Ty.apply, Ty.unificationVars] using member)
  | data former arguments =>
      exact tyList_apply_mem localized arguments (by
        intro candidate candidateMember
        exact covered candidate (by
          simpa [Ty.unificationVars] using candidateMember)) candidate (by
            simpa [Ty.apply, Ty.unificationVars] using member)
  | matcher capability target =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member
      rcases member with left | right
      · apply cap_apply_mem localized capability
          (fun candidate candidateMember => covered candidate (by
            simpa [Ty.unificationVars] using Or.inl candidateMember))
          candidate left
      · apply ty_apply_mem localized target
          (fun candidate candidateMember => covered candidate (by
            simpa [Ty.unificationVars] using Or.inr candidateMember))
          candidate right
  | slot capability target =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member
      rcases member with left | right
      · apply cap_apply_mem localized capability
          (fun candidate candidateMember => covered candidate (by
            simpa [Ty.unificationVars] using Or.inl candidateMember))
          candidate left
      · apply ty_apply_mem localized target
          (fun candidate candidateMember => covered candidate (by
            simpa [Ty.unificationVars] using Or.inr candidateMember))
          candidate right

theorem tyList_apply_mem
    {support : List UnificationVar} {substitution : Subst}
    (localized : Subst.Localized support substitution)
    (items : List Ty)
    (covered : ∀ candidate, candidate ∈ Ty.unificationVarsList items →
      candidate ∈ support) :
    ∀ candidate,
      candidate ∈ Ty.unificationVarsList
        (Ty.applyList substitution items) →
        candidate ∈ support := by
  intro candidate member
  cases items with
  | nil => simp [Ty.applyList, Ty.unificationVarsList] at member
  | cons item items =>
      simp only [Ty.applyList, Ty.unificationVarsList,
        List.mem_append] at member
      rcases member with head | tail
      · apply ty_apply_mem localized item
          (fun candidate candidateMember => covered candidate (by
            simpa [Ty.unificationVarsList] using Or.inl candidateMember))
          candidate head
      · apply tyList_apply_mem localized items
          (fun candidate candidateMember => covered candidate (by
            simpa [Ty.unificationVarsList] using Or.inr candidateMember))
          candidate tail

end

/-- Enlarging the finite support preserves locality. -/
theorem mono {small large : List UnificationVar} {substitution : Subst}
    (localized : Subst.Localized small substitution)
    (subset : ∀ candidate, candidate ∈ small → candidate ∈ large) :
    Subst.Localized large substitution := by
  constructor
  · intro index absent
    exact localized.fixesTy index (fun member => absent (subset _ member))
  · intro index absent
    exact localized.fixesCap index (fun member => absent (subset _ member))
  · intro index inLarge candidate member
    by_cases old : .ty index ∈ small
    · exact subset candidate (localized.tyRange index old candidate member)
    · rw [localized.fixesTy index old] at member
      have equality : candidate = .ty index := by
        simpa [Ty.unificationVars] using member
      simpa [equality] using inLarge
  · intro index inLarge candidate member
    by_cases old : .cap index ∈ small
    · exact subset candidate (localized.capRange index old candidate member)
    · rw [localized.fixesCap index old] at member
      have equality : candidate = .cap index := by
        simpa [Cap.unificationVars] using member
      simpa [equality] using inLarge

/-- Composition of substitutions confined to the same support remains
confined to that support. -/
theorem compose {support : List UnificationVar} {later earlier : Subst}
    (laterLocalized : Subst.Localized support later)
    (earlierLocalized : Subst.Localized support earlier) :
    Subst.Localized support (Subst.compose later earlier) := by
  constructor
  · intro index absent
    simp [Subst.compose, earlierLocalized.fixesTy index absent,
      laterLocalized.fixesTy index absent, Ty.apply]
  · intro index absent
    simp [Subst.compose, earlierLocalized.fixesCap index absent,
      laterLocalized.fixesCap index absent, Cap.apply]
  · intro index inSupport candidate member
    exact ty_apply_mem laterLocalized (earlier.ty index)
      (earlierLocalized.tyRange index inSupport) candidate (by
        simpa [Subst.compose] using member)
  · intro index inSupport candidate member
    exact cap_apply_mem laterLocalized (earlier.cap index)
      (earlierLocalized.capRange index inSupport) candidate (by
        simpa [Subst.compose] using member)

end Subst.Localized

/-- The elementary substitution emitted by a reduction is confined to the
variables in the input worklist. -/
theorem Reduces.substitution_localized
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining) :
    Subst.Localized (unificationVars input) first := by
  cases reduction <;>
    constructor <;>
    simp_all [unificationVars, Equation.unificationVars,
      Cap.unificationVars, Ty.unificationVars, Subst.singleCap,
      Subst.singleTy, Subst.id]
  case capVarLeft.capRange index replacement rest notOccurs =>
    intro source sourceMember candidate imageMember
    by_cases same : source = index
    · subst source
      simp only [if_pos] at imageMember
      exact Or.inr (Or.inl imageMember)
    · simp only [if_neg same] at imageMember
      have equality : candidate = .cap source := by
        simpa [Cap.unificationVars] using imageMember
      subst candidate
      simpa only [UnificationVar.cap.injEq,
        Cap.cap_mem_unificationVars_iff] using Or.inr sourceMember
  case capVarRight.capRange index replacement rest notOccurs =>
    intro source sourceMember candidate imageMember
    by_cases same : source = index
    · subst source
      simp only [if_pos] at imageMember
      exact Or.inl imageMember
    · simp only [if_neg same] at imageMember
      have equality : candidate = .cap source := by
        simpa [Cap.unificationVars] using imageMember
      subst candidate
      simpa only [UnificationVar.cap.injEq,
        Cap.cap_mem_unificationVars_iff] using sourceMember
  case tyVarLeft.tyRange index replacement rest notOccurs =>
    intro source sourceMember candidate imageMember
    by_cases same : source = index
    · subst source
      simp only [if_pos] at imageMember
      exact Or.inr (Or.inl imageMember)
    · simp only [if_neg same] at imageMember
      have equality : candidate = .ty source := by
        simpa [Ty.unificationVars] using imageMember
      subst candidate
      simpa only [UnificationVar.ty.injEq,
        Ty.ty_mem_unificationVars_iff] using Or.inr sourceMember
  case tyVarRight.tyRange index replacement rest notOccurs =>
    intro source sourceMember candidate imageMember
    by_cases same : source = index
    · subst source
      simp only [if_pos] at imageMember
      exact Or.inl imageMember
    · simp only [if_neg same] at imageMember
      have equality : candidate = .ty source := by
        simpa [Ty.unificationVars] using imageMember
      subst candidate
      simpa only [UnificationVar.ty.injEq,
        Ty.ty_mem_unificationVars_iff] using sourceMember

/-- A successful fuel-bounded unification run is confined to its input
variables. -/
theorem unifyWithFuel_localized
    {fuel : Nat} {equations : List Equation} {principal : Subst}
    (success : unifyWithFuel fuel equations = some principal) :
    Subst.Localized (unificationVars equations) principal := by
  induction fuel generalizing equations principal with
  | zero =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst principal
          exact Subst.Localized.id []
      | cons equation equations => simp [unifyWithFuel] at success
  | succ fuel induction =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst principal
          exact Subst.Localized.id []
      | cons equation equations =>
          simp only [unifyWithFuel] at success
          cases reduced : reduce (equation :: equations) with
          | none => simp_all
          | some reduction =>
              cases recursive : unifyWithFuel fuel reduction.equations with
              | none => simp_all
              | some later =>
                  simp_all only [Option.some.injEq]
                  subst principal
                  have laterLocalized := (induction recursive).mono
                    reduction.valid.unificationVars_subset
                  exact laterLocalized.compose
                    reduction.valid.substitution_localized

/-- The public total unifier neither changes nor introduces variables outside
the variables of its input worklist. -/
theorem unify_localized
    {equations : List Equation} {principal : Subst}
    (success : unify equations = some principal) :
    Subst.Localized (unificationVars equations) principal := by
  change unifyLoop (unificationVars equations) (rawNodeCount equations)
    equations = some principal at success
  obtain ⟨fuel, fuelSuccess⟩ := unifyLoop_success_has_fuel success
  exact unifyWithFuel_localized fuelSuccess

end TypePM
