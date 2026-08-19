import TypePM.UnificationSupport

/-!
# Support range of declarative absorbing unifiers

Executable unification is already known to be localized to its input
variables.  This module proves the corresponding semantic theorem for every
`AbsorbingPrincipal` representative: absorption prevents images of input
variables from mentioning a variable outside the input equation support.
-/

namespace TypePM

def Subst.setTy
    (substitution : Subst) (index : TyVar) (replacement : Ty) : Subst :=
  { cap := substitution.cap
    ty := fun candidate =>
      if candidate = index then replacement else substitution.ty candidate }

def Subst.setCap
    (substitution : Subst) (index : CapVar) (replacement : Cap) : Subst :=
  { ty := substitution.ty
    cap := fun candidate =>
      if candidate = index then replacement else substitution.cap candidate }

mutual

theorem Cap.nodeCount_le_apply_any
    (substitution : CapSubst) (capability : Cap) :
    capability.nodeCount ≤ (capability.apply substitution).nodeCount := by
  cases capability with
  | any => simp [Cap.nodeCount, Cap.apply]
  | var index => exact Cap.nodeCount_pos (substitution index)
  | prod items =>
      simp only [Cap.nodeCount, Cap.apply]
      exact Nat.add_le_add_left
        (Cap.nodeCountList_le_apply_any substitution items) 1

theorem Cap.nodeCountList_le_apply_any
    (substitution : CapSubst) (items : List Cap) :
    Cap.nodeCountList items ≤
      Cap.nodeCountList (Cap.applyList substitution items) := by
  cases items with
  | nil => simp [Cap.nodeCountList, Cap.applyList]
  | cons item items =>
      simp only [Cap.nodeCountList, Cap.applyList]
      exact Nat.add_le_add
        (Cap.nodeCount_le_apply_any substitution item)
        (Cap.nodeCountList_le_apply_any substitution items)

end

mutual

theorem Ty.nodeCount_le_apply_any
    (substitution : Subst) (target : Ty) :
    target.nodeCount ≤ (target.apply substitution).nodeCount := by
  cases target with
  | var index => exact Ty.nodeCount_pos (substitution.ty index)
  | int => simp [Ty.nodeCount, Ty.apply]
  | fn domain codomain =>
      simp only [Ty.nodeCount, Ty.apply]
      have domainLe := Ty.nodeCount_le_apply_any substitution domain
      have codomainLe := Ty.nodeCount_le_apply_any substitution codomain
      omega
  | prod items =>
      simp only [Ty.nodeCount, Ty.apply]
      exact Nat.add_le_add_left
        (Ty.nodeCountList_le_apply_any substitution items) 1
  | matcher capability target =>
      simp only [Ty.nodeCount, Ty.apply]
      have capLe := Cap.nodeCount_le_apply_any substitution.cap capability
      have targetLe := Ty.nodeCount_le_apply_any substitution target
      omega
  | slot capability target =>
      simp only [Ty.nodeCount, Ty.apply]
      have capLe := Cap.nodeCount_le_apply_any substitution.cap capability
      have targetLe := Ty.nodeCount_le_apply_any substitution target
      omega

theorem Ty.nodeCountList_le_apply_any
    (substitution : Subst) (items : List Ty) :
    Ty.nodeCountList items ≤
      Ty.nodeCountList (Ty.applyList substitution items) := by
  cases items with
  | nil => simp [Ty.nodeCountList, Ty.applyList]
  | cons item items =>
      simp only [Ty.nodeCountList, Ty.applyList]
      exact Nat.add_le_add
        (Ty.nodeCount_le_apply_any substitution item)
        (Ty.nodeCountList_le_apply_any substitution items)

end

mutual

theorem Cap.nodeCount_lt_apply_of_cap_occurs
    (substitution : CapSubst) (index : CapVar) (capability : Cap)
    (large : 1 < (substitution index).nodeCount)
    (occurs : capability.occurs index = true) :
    capability.nodeCount < (capability.apply substitution).nodeCount := by
  cases capability with
  | any => simp [Cap.occurs] at occurs
  | var candidate =>
      have equality : candidate = index := by
        simpa [Cap.occurs] using occurs
      subst candidate
      simpa [Cap.nodeCount, Cap.apply] using large
  | prod items =>
      simp only [Cap.nodeCount, Cap.apply]
      exact Nat.add_lt_add_left
        (Cap.nodeCountList_lt_apply_of_cap_occurs
          substitution index items large occurs) 1

theorem Cap.nodeCountList_lt_apply_of_cap_occurs
    (substitution : CapSubst) (index : CapVar) (items : List Cap)
    (large : 1 < (substitution index).nodeCount)
    (occurs : Cap.occursList index items = true) :
    Cap.nodeCountList items <
      Cap.nodeCountList (Cap.applyList substitution items) := by
  cases items with
  | nil => simp [Cap.occursList] at occurs
  | cons item items =>
      simp only [Cap.occursList] at occurs
      simp only [Cap.nodeCountList, Cap.applyList]
      cases itemOccurs : item.occurs index with
      | false =>
          have tailOccurs : Cap.occursList index items = true := by
            simpa [itemOccurs] using occurs
          have headLe := Cap.nodeCount_le_apply_any substitution item
          have tailLt := Cap.nodeCountList_lt_apply_of_cap_occurs
            substitution index items large tailOccurs
          omega
      | true =>
          have headLt := Cap.nodeCount_lt_apply_of_cap_occurs
            substitution index item large itemOccurs
          have tailLe := Cap.nodeCountList_le_apply_any substitution items
          omega

end

mutual

theorem Ty.nodeCount_lt_apply_of_cap_occurs
    (substitution : Subst) (index : CapVar) (target : Ty)
    (large : 1 < (substitution.cap index).nodeCount)
    (occurs : target.occursCap index = true) :
    target.nodeCount < (target.apply substitution).nodeCount := by
  cases target with
  | var candidate => simp [Ty.occursCap] at occurs
  | int => simp [Ty.occursCap] at occurs
  | fn domain codomain =>
      simp only [Ty.occursCap] at occurs
      simp only [Ty.nodeCount, Ty.apply]
      cases domainOccurs : domain.occursCap index with
      | false =>
          have codomainOccurs : codomain.occursCap index = true := by
            simpa [domainOccurs] using occurs
          have domainLe := Ty.nodeCount_le_apply_any substitution domain
          have codomainLt := Ty.nodeCount_lt_apply_of_cap_occurs
            substitution index codomain large codomainOccurs
          omega
      | true =>
          have domainLt := Ty.nodeCount_lt_apply_of_cap_occurs
            substitution index domain large domainOccurs
          have codomainLe := Ty.nodeCount_le_apply_any substitution codomain
          omega
  | prod items =>
      simp only [Ty.nodeCount, Ty.apply]
      exact Nat.add_lt_add_left
        (Ty.nodeCountList_lt_apply_of_cap_occurs
          substitution index items large occurs) 1
  | matcher capability target =>
      simp only [Ty.occursCap] at occurs
      simp only [Ty.nodeCount, Ty.apply]
      cases capabilityOccurs : capability.occurs index with
      | false =>
          have targetOccurs : target.occursCap index = true := by
            simpa [capabilityOccurs] using occurs
          have capabilityLe := Cap.nodeCount_le_apply_any
            substitution.cap capability
          have targetLt := Ty.nodeCount_lt_apply_of_cap_occurs
            substitution index target large targetOccurs
          omega
      | true =>
          have capabilityLt := Cap.nodeCount_lt_apply_of_cap_occurs
            substitution.cap index capability large capabilityOccurs
          have targetLe := Ty.nodeCount_le_apply_any substitution target
          omega
  | slot capability target =>
      simp only [Ty.occursCap] at occurs
      simp only [Ty.nodeCount, Ty.apply]
      cases capabilityOccurs : capability.occurs index with
      | false =>
          have targetOccurs : target.occursCap index = true := by
            simpa [capabilityOccurs] using occurs
          have capabilityLe := Cap.nodeCount_le_apply_any
            substitution.cap capability
          have targetLt := Ty.nodeCount_lt_apply_of_cap_occurs
            substitution index target large targetOccurs
          omega
      | true =>
          have capabilityLt := Cap.nodeCount_lt_apply_of_cap_occurs
            substitution.cap index capability large capabilityOccurs
          have targetLe := Ty.nodeCount_le_apply_any substitution target
          omega

theorem Ty.nodeCountList_lt_apply_of_cap_occurs
    (substitution : Subst) (index : CapVar) (items : List Ty)
    (large : 1 < (substitution.cap index).nodeCount)
    (occurs : Ty.occursCapList index items = true) :
    Ty.nodeCountList items <
      Ty.nodeCountList (Ty.applyList substitution items) := by
  cases items with
  | nil => simp [Ty.occursCapList] at occurs
  | cons item items =>
      simp only [Ty.occursCapList] at occurs
      simp only [Ty.nodeCountList, Ty.applyList]
      cases itemOccurs : item.occursCap index with
      | false =>
          have tailOccurs : Ty.occursCapList index items = true := by
            simpa [itemOccurs] using occurs
          have headLe := Ty.nodeCount_le_apply_any substitution item
          have tailLt := Ty.nodeCountList_lt_apply_of_cap_occurs
            substitution index items large tailOccurs
          omega
      | true =>
          have headLt := Ty.nodeCount_lt_apply_of_cap_occurs
            substitution index item large itemOccurs
          have tailLe := Ty.nodeCountList_le_apply_any substitution items
          omega

end

mutual

theorem Ty.apply_setTy_of_absent
    (substitution : Subst) (index : TyVar) (replacement : Ty)
    (target : Ty) (absent : .ty index ∉ target.unificationVars) :
    target.apply (substitution.setTy index replacement) =
      target.apply substitution := by
  cases target with
  | var candidate =>
      have different : candidate ≠ index := by
        intro equality
        subst candidate
        exact absent (by simp [Ty.unificationVars])
      simp [Ty.apply, Subst.setTy, different]
  | int => rfl
  | fn domain codomain =>
      simp only [Ty.unificationVars, List.mem_append] at absent
      simp [Ty.apply,
        Ty.apply_setTy_of_absent substitution index replacement domain
          (fun member => absent (Or.inl member)),
        Ty.apply_setTy_of_absent substitution index replacement codomain
          (fun member => absent (Or.inr member))]
  | prod items =>
      simp only [Ty.unificationVars] at absent
      rw [Ty.apply]
      congr 1
      exact Ty.applyList_setTy_of_absent substitution index replacement
        items absent
  | matcher capability target =>
      simp only [Ty.unificationVars, List.mem_append] at absent
      rw [Ty.apply]
      congr 1
      exact Ty.apply_setTy_of_absent substitution index replacement target
        (fun member => absent (Or.inr member))
  | slot capability target =>
      simp only [Ty.unificationVars, List.mem_append] at absent
      rw [Ty.apply]
      congr 1
      exact Ty.apply_setTy_of_absent substitution index replacement target
        (fun member => absent (Or.inr member))

theorem Ty.applyList_setTy_of_absent
    (substitution : Subst) (index : TyVar) (replacement : Ty)
    (items : List Ty) (absent : .ty index ∉ Ty.unificationVarsList items) :
    Ty.applyList (substitution.setTy index replacement) items =
      Ty.applyList substitution items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [Ty.unificationVarsList, List.mem_append] at absent
      simp [Ty.applyList,
        Ty.apply_setTy_of_absent substitution index replacement item
          (fun member => absent (Or.inl member)),
        Ty.applyList_setTy_of_absent substitution index replacement items
          (fun member => absent (Or.inr member))]

end

mutual

theorem Cap.apply_setCap_of_absent
    (substitution : Subst) (index : CapVar) (replacement : Cap)
    (capability : Cap) (absent : .cap index ∉ capability.unificationVars) :
    capability.apply (substitution.setCap index replacement).cap =
      capability.apply substitution.cap := by
  cases capability with
  | any => rfl
  | var candidate =>
      have different : candidate ≠ index := by
        intro equality
        subst candidate
        exact absent (by simp [Cap.unificationVars])
      simp [Cap.apply, Subst.setCap, different]
  | prod items =>
      simp only [Cap.unificationVars] at absent
      rw [Cap.apply]
      congr 1
      exact Cap.applyList_setCap_of_absent substitution index replacement
        items absent

theorem Cap.applyList_setCap_of_absent
    (substitution : Subst) (index : CapVar) (replacement : Cap)
    (items : List Cap)
    (absent : .cap index ∉ Cap.unificationVarsList items) :
    Cap.applyList (substitution.setCap index replacement).cap items =
      Cap.applyList substitution.cap items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [Cap.unificationVarsList, List.mem_append] at absent
      simp [Cap.applyList,
        Cap.apply_setCap_of_absent substitution index replacement item
          (fun member => absent (Or.inl member)),
        Cap.applyList_setCap_of_absent substitution index replacement items
          (fun member => absent (Or.inr member))]

end

mutual

theorem Ty.apply_setCap_of_absent
    (substitution : Subst) (index : CapVar) (replacement : Cap)
    (target : Ty) (absent : .cap index ∉ target.unificationVars) :
    target.apply (substitution.setCap index replacement) =
      target.apply substitution := by
  cases target with
  | var candidate => rfl
  | int => rfl
  | fn domain codomain =>
      simp only [Ty.unificationVars, List.mem_append] at absent
      simp [Ty.apply,
        Ty.apply_setCap_of_absent substitution index replacement domain
          (fun member => absent (Or.inl member)),
        Ty.apply_setCap_of_absent substitution index replacement codomain
          (fun member => absent (Or.inr member))]
  | prod items =>
      simp only [Ty.unificationVars] at absent
      rw [Ty.apply]
      congr 1
      exact Ty.applyList_setCap_of_absent substitution index replacement
        items absent
  | matcher capability target =>
      simp only [Ty.unificationVars, List.mem_append] at absent
      simp [Ty.apply,
        Cap.apply_setCap_of_absent substitution index replacement capability
          (fun member => absent (Or.inl member)),
        Ty.apply_setCap_of_absent substitution index replacement target
          (fun member => absent (Or.inr member))]
  | slot capability target =>
      simp only [Ty.unificationVars, List.mem_append] at absent
      simp [Ty.apply,
        Cap.apply_setCap_of_absent substitution index replacement capability
          (fun member => absent (Or.inl member)),
        Ty.apply_setCap_of_absent substitution index replacement target
          (fun member => absent (Or.inr member))]

theorem Ty.applyList_setCap_of_absent
    (substitution : Subst) (index : CapVar) (replacement : Cap)
    (items : List Ty) (absent : .cap index ∉ Ty.unificationVarsList items) :
    Ty.applyList (substitution.setCap index replacement) items =
      Ty.applyList substitution items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [Ty.unificationVarsList, List.mem_append] at absent
      simp [Ty.applyList,
        Ty.apply_setCap_of_absent substitution index replacement item
          (fun member => absent (Or.inl member)),
        Ty.applyList_setCap_of_absent substitution index replacement items
          (fun member => absent (Or.inr member))]

end


theorem Equation.holds_setTy_of_absent
    (equation : Equation) (substitution : Subst)
    (index : TyVar) (replacement : Ty)
    (absent : .ty index ∉ equation.unificationVars)
    (holds : equation.Holds substitution) :
    equation.Holds (substitution.setTy index replacement) := by
  cases equation with
  | cap left right => exact holds
  | ty left right =>
      simp only [Equation.unificationVars, List.mem_append] at absent
      simpa only [Equation.Holds,
        Ty.apply_setTy_of_absent substitution index replacement left
          (fun member => absent (Or.inl member)),
        Ty.apply_setTy_of_absent substitution index replacement right
          (fun member => absent (Or.inr member))] using holds

theorem Equation.holds_setCap_of_absent
    (equation : Equation) (substitution : Subst)
    (index : CapVar) (replacement : Cap)
    (absent : .cap index ∉ equation.unificationVars)
    (holds : equation.Holds substitution) :
    equation.Holds (substitution.setCap index replacement) := by
  cases equation with
  | cap left right =>
      simp only [Equation.unificationVars, List.mem_append] at absent
      simpa only [Equation.Holds,
        Cap.apply_setCap_of_absent substitution index replacement left
          (fun member => absent (Or.inl member)),
        Cap.apply_setCap_of_absent substitution index replacement right
          (fun member => absent (Or.inr member))] using holds
  | ty left right =>
      simp only [Equation.unificationVars, List.mem_append] at absent
      simpa only [Equation.Holds,
        Ty.apply_setCap_of_absent substitution index replacement left
          (fun member => absent (Or.inl member)),
        Ty.apply_setCap_of_absent substitution index replacement right
          (fun member => absent (Or.inr member))] using holds

theorem solves_setTy_of_not_mem
    (equations : List Equation) (substitution : Subst)
    (index : TyVar) (replacement : Ty)
    (absent : .ty index ∉ unificationVars equations)
    (solves : Solves substitution equations) :
    Solves (substitution.setTy index replacement) equations := by
  intro equation member
  apply equation.holds_setTy_of_absent substitution index replacement
  · intro equationMember
    apply absent
    clear solves absent
    induction equations with
    | nil => simp at member
    | cons head tail induction =>
        simp only [List.mem_cons] at member
        simp only [unificationVars, List.mem_append]
        rcases member with rfl | member
        · exact Or.inl equationMember
        · exact Or.inr (induction member)
  · exact solves equation member

theorem solves_setCap_of_not_mem
    (equations : List Equation) (substitution : Subst)
    (index : CapVar) (replacement : Cap)
    (absent : .cap index ∉ unificationVars equations)
    (solves : Solves substitution equations) :
    Solves (substitution.setCap index replacement) equations := by
  intro equation member
  apply equation.holds_setCap_of_absent substitution index replacement
  · intro equationMember
    apply absent
    clear solves absent
    induction equations with
    | nil => simp at member
    | cons head tail induction =>
        simp only [List.mem_cons] at member
        simp only [unificationVars, List.mem_append]
        rcases member with rfl | member
        · exact Or.inl equationMember
        · exact Or.inr (induction member)
  · exact solves equation member


/-- Component-sensitive numeric bound for a two-sorted unification
variable. -/
def UnificationVar.Below
    (tyBound capBound : Nat) : UnificationVar → Prop
  | .ty index => index.index < tyBound
  | .cap index => index.index < capBound

theorem Subst.Localized.tyImage_below
    {support : List UnificationVar} {substitution : Subst}
    (localized : Subst.Localized support substitution)
    {tyBound capBound : Nat}
    (supportBelow : ∀ candidate, candidate ∈ support →
      candidate.Below tyBound capBound)
    (index : TyVar) (indexBelow : index.index < tyBound)
    (candidate : UnificationVar)
    (member : candidate ∈ (substitution.ty index).unificationVars) :
    candidate.Below tyBound capBound := by
  by_cases supported : .ty index ∈ support
  · exact supportBelow candidate
      (localized.tyRange index supported candidate member)
  · rw [localized.fixesTy index supported] at member
    have equality : candidate = .ty index := by
      simpa [Ty.unificationVars] using member
    subst candidate
    exact indexBelow

theorem Subst.Localized.capImage_below
    {support : List UnificationVar} {substitution : Subst}
    (localized : Subst.Localized support substitution)
    {tyBound capBound : Nat}
    (supportBelow : ∀ candidate, candidate ∈ support →
      candidate.Below tyBound capBound)
    (index : CapVar) (indexBelow : index.index < capBound)
    (candidate : UnificationVar)
    (member : candidate ∈ (substitution.cap index).unificationVars) :
    candidate.Below tyBound capBound := by
  by_cases supported : .cap index ∈ support
  · exact supportBelow candidate
      (localized.capRange index supported candidate member)
  · rw [localized.fixesCap index supported] at member
    have equality : candidate = .cap index := by
      simpa [Cap.unificationVars] using member
    subst candidate
    exact indexBelow

/-- An absorbing principal solution cannot introduce an unsupported variable
in the image of a supported ordinary type variable. -/
theorem AbsorbingPrincipal.tyRange
    {equations : List Equation} {principal : Subst}
    (absorbing : AbsorbingPrincipal equations principal)
    (index : TyVar) (indexMember : .ty index ∈ unificationVars equations)
    (candidate : UnificationVar)
    (candidateMember : candidate ∈ (principal.ty index).unificationVars) :
    candidate ∈ unificationVars equations := by
  by_cases candidateIn : candidate ∈ unificationVars equations
  · exact candidateIn
  · exfalso
    cases candidate with
    | ty outside =>
      have different : index ≠ outside := by
        intro equality
        subst outside
        exact candidateIn indexMember
      have occurs : (principal.ty index).occursTy outside = true :=
        (Ty.ty_mem_unificationVars_iff outside (principal.ty index)).mp
          candidateMember
      by_cases variableImage : principal.ty index = .var outside
      · let modified := principal.setTy outside .int
        have modifiedSolves : Solves modified equations :=
          solves_setTy_of_not_mem equations principal outside .int
            candidateIn absorbing.solves
        have absorbed := absorbing.absorbs modifiedSolves
        have atIndex := congrArg (fun substitution => substitution.ty index) absorbed
        change (principal.ty index).apply modified = modified.ty index at atIndex
        have modifiedIndex : modified.ty index = principal.ty index := by
          simp [modified, Subst.setTy, different]
        rw [modifiedIndex, variableImage] at atIndex
        simp [modified, Subst.setTy, Ty.apply] at atIndex
      · let image := principal.ty index
        let modified := principal.setTy outside image
        have modifiedSolves : Solves modified equations :=
          solves_setTy_of_not_mem equations principal outside image
            candidateIn absorbing.solves
        have absorbed := absorbing.absorbs modifiedSolves
        have atIndex := congrArg (fun substitution => substitution.ty index) absorbed
        change image.apply modified = modified.ty index at atIndex
        have modifiedIndex : modified.ty index = image := by
          simp [modified, image, Subst.setTy, different]
        rw [modifiedIndex] at atIndex
        have modifiedOutside : modified.ty outside = image := by
          simp [modified, Subst.setTy]
        exact Ty.occurs_equation_impossible modified outside image occurs
          variableImage (modifiedOutside.trans atIndex.symm)
    | cap outside =>
      have occurs : (principal.ty index).occursCap outside = true :=
        (Ty.cap_mem_unificationVars_iff outside (principal.ty index)).mp
          candidateMember
      let expansion : Cap := .prod [.var outside]
      let modified := principal.setCap outside expansion
      have modifiedSolves : Solves modified equations :=
        solves_setCap_of_not_mem equations principal outside expansion
          candidateIn absorbing.solves
      have absorbed := absorbing.absorbs modifiedSolves
      have atIndex := congrArg (fun substitution => substitution.ty index) absorbed
      change (principal.ty index).apply modified = modified.ty index at atIndex
      have modifiedIndex : modified.ty index = principal.ty index := by
        rfl
      rw [modifiedIndex] at atIndex
      have expansionLarge : 1 < (modified.cap outside).nodeCount := by
        simp only [modified, Subst.setCap, if_pos, expansion]
        simp [Cap.nodeCount, Cap.nodeCountList]
      have strict := Ty.nodeCount_lt_apply_of_cap_occurs
        modified outside (principal.ty index) expansionLarge occurs
      have same := congrArg Ty.nodeCount atIndex
      omega

/-- Capability-variable image counterpart of `tyRange`. -/
theorem AbsorbingPrincipal.capRange
    {equations : List Equation} {principal : Subst}
    (absorbing : AbsorbingPrincipal equations principal)
    (index : CapVar) (indexMember : .cap index ∈ unificationVars equations)
    (candidate : UnificationVar)
    (candidateMember : candidate ∈ (principal.cap index).unificationVars) :
    candidate ∈ unificationVars equations := by
  by_cases candidateIn : candidate ∈ unificationVars equations
  · exact candidateIn
  · exfalso
    cases candidate with
    | ty outside =>
      exact False.elim
        ((Cap.ty_not_mem_unificationVars outside (principal.cap index))
          candidateMember)
    | cap outside =>
      have different : index ≠ outside := by
        intro equality
        subst outside
        exact candidateIn indexMember
      have occurs : (principal.cap index).occurs outside = true :=
        (Cap.cap_mem_unificationVars_iff outside (principal.cap index)).mp
          candidateMember
      by_cases variableImage : principal.cap index = .var outside
      · let modified := principal.setCap outside .any
        have modifiedSolves : Solves modified equations :=
          solves_setCap_of_not_mem equations principal outside .any
            candidateIn absorbing.solves
        have absorbed := absorbing.absorbs modifiedSolves
        have atIndex := congrArg (fun substitution => substitution.cap index) absorbed
        change (principal.cap index).apply modified.cap = modified.cap index at atIndex
        have modifiedIndex : modified.cap index = principal.cap index := by
          simp [modified, Subst.setCap, different]
        rw [modifiedIndex, variableImage] at atIndex
        simp [modified, Subst.setCap, Cap.apply] at atIndex
      · let image := principal.cap index
        let modified := principal.setCap outside image
        have modifiedSolves : Solves modified equations :=
          solves_setCap_of_not_mem equations principal outside image
            candidateIn absorbing.solves
        have absorbed := absorbing.absorbs modifiedSolves
        have atIndex := congrArg (fun substitution => substitution.cap index) absorbed
        change image.apply modified.cap = modified.cap index at atIndex
        have modifiedIndex : modified.cap index = image := by
          simp [modified, image, Subst.setCap, different]
        rw [modifiedIndex] at atIndex
        have modifiedOutside : modified.cap outside = image := by
          simp [modified, Subst.setCap]
        exact Cap.occurs_equation_impossible modified.cap outside image occurs
          variableImage (modifiedOutside.trans atIndex.symm)

/-- An absorbing principal solution fixes every ordinary variable absent
from its equation support. -/
theorem AbsorbingPrincipal.fixesTyOutside
    {equations : List Equation} {principal : Subst}
    (absorbing : AbsorbingPrincipal equations principal)
    (index : TyVar) (absent : .ty index ∉ unificationVars equations) :
    principal.ty index = .var index := by
  let modified := principal.setTy index (.var index)
  have modifiedSolves : Solves modified equations :=
    solves_setTy_of_not_mem equations principal index (.var index)
      absent absorbing.solves
  have absorbed := absorbing.absorbs modifiedSolves
  have atIndex := congrArg (fun substitution => substitution.ty index) absorbed
  change (principal.ty index).apply modified = modified.ty index at atIndex
  have modifiedAt : modified.ty index = .var index := by
    simp [modified, Subst.setTy]
  rw [modifiedAt] at atIndex
  cases imageEquality : principal.ty index with
  | var image =>
      by_cases same : image = index
      · subst image
        rfl
      · have modifiedImage : principal.ty image = .var index := by
          rw [imageEquality] at atIndex
          simpa [Ty.apply, modified, Subst.setTy, same] using atIndex
        have idempotentAtImage := congrArg
          (fun substitution => substitution.ty image) absorbing.idempotent
        change (principal.ty image).apply principal =
          principal.ty image at idempotentAtImage
        rw [modifiedImage] at idempotentAtImage
        simp only [Ty.apply] at idempotentAtImage
        have principalFixed : principal.ty index = .var index :=
          idempotentAtImage
        exact imageEquality.symm.trans principalFixed
  | int => simp [Ty.apply, imageEquality] at atIndex
  | fn => simp [Ty.apply, imageEquality] at atIndex
  | prod => simp [Ty.apply, imageEquality] at atIndex
  | matcher => simp [Ty.apply, imageEquality] at atIndex
  | slot => simp [Ty.apply, imageEquality] at atIndex

/-- Capability-variable counterpart of `fixesTyOutside`. -/
theorem AbsorbingPrincipal.fixesCapOutside
    {equations : List Equation} {principal : Subst}
    (absorbing : AbsorbingPrincipal equations principal)
    (index : CapVar) (absent : .cap index ∉ unificationVars equations) :
    principal.cap index = .var index := by
  let modified := principal.setCap index (.var index)
  have modifiedSolves : Solves modified equations :=
    solves_setCap_of_not_mem equations principal index (.var index)
      absent absorbing.solves
  have absorbed := absorbing.absorbs modifiedSolves
  have atIndex := congrArg (fun substitution => substitution.cap index) absorbed
  change (principal.cap index).apply modified.cap = modified.cap index at atIndex
  have modifiedAt : modified.cap index = .var index := by
    simp [modified, Subst.setCap]
  rw [modifiedAt] at atIndex
  cases imageEquality : principal.cap index with
  | any => simp [Cap.apply, imageEquality] at atIndex
  | var image =>
      by_cases same : image = index
      · subst image
        rfl
      · have modifiedImage : principal.cap image = .var index := by
          rw [imageEquality] at atIndex
          simpa [Cap.apply, modified, Subst.setCap, same] using atIndex
        have idempotentAtImage := congrArg
          (fun substitution => substitution.cap image) absorbing.idempotent
        change (principal.cap image).apply principal.cap =
          principal.cap image at idempotentAtImage
        rw [modifiedImage] at idempotentAtImage
        simp only [Cap.apply] at idempotentAtImage
        have principalFixed : principal.cap index = .var index :=
          idempotentAtImage
        exact imageEquality.symm.trans principalFixed
  | prod => simp [Cap.apply, imageEquality] at atIndex

/-- Every declarative absorbing principal solution is fully localized to its
input equation support. -/
theorem AbsorbingPrincipal.localized
    {equations : List Equation} {principal : Subst}
    (absorbing : AbsorbingPrincipal equations principal) :
    Subst.Localized (unificationVars equations) principal :=
  { fixesTy := absorbing.fixesTyOutside
    fixesCap := absorbing.fixesCapOutside
    tyRange := absorbing.tyRange
    capRange := absorbing.capRange }

end TypePM
