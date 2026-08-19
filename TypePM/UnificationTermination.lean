import TypePM.UnificationCorrectness

/-!
# Semantic termination measure for hard unification

For a fixed solution, the size of a worklist after applying that solution is
a natural-number ranking function.  Every certified reduction strictly
decreases it: elimination substitutions are absorbed by the solution, while
constructor decomposition removes outer nodes.  This supplies the semantic
termination argument used to prove that every solvable worklist succeeds for
some finite fuel.
-/

namespace TypePM

/-- A tag joining the two disjoint unification-variable sorts. -/
inductive UnificationVar where
  | cap (index : CapVar)
  | ty (index : TyVar)
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

mutual

def Cap.unificationVars : Cap → List UnificationVar
  | .any => []
  | .var index => [.cap index]
  | .prod items => Cap.unificationVarsList items
  | .con _ arguments => Cap.unificationVarsList arguments

def Cap.unificationVarsList : List Cap → List UnificationVar
  | [] => []
  | item :: items => item.unificationVars ++ Cap.unificationVarsList items

end


mutual

def Ty.unificationVars : Ty → List UnificationVar
  | .var index => [.ty index]
  | .int => []
  | .fn domain codomain => domain.unificationVars ++ codomain.unificationVars
  | .prod items => Ty.unificationVarsList items
  | .data _ arguments => Ty.unificationVarsList arguments
  | .matcher capability target =>
      capability.unificationVars ++ target.unificationVars
  | .slot capability target =>
      capability.unificationVars ++ target.unificationVars

def Ty.unificationVarsList : List Ty → List UnificationVar
  | [] => []
  | item :: items => item.unificationVars ++ Ty.unificationVarsList items

end

mutual

def Cap.nodeCount : Cap → Nat
  | .any => 1
  | .var _ => 1
  | .prod items => 1 + Cap.nodeCountList items
  | .con _ arguments => 1 + Cap.nodeCountList arguments

def Cap.nodeCountList : List Cap → Nat
  | [] => 0
  | item :: items => item.nodeCount + Cap.nodeCountList items

end

mutual

theorem Cap.mem_unificationVars_apply_singleCap
    (candidateVar : UnificationVar) (index : CapVar) (replacement capability : Cap)
    (member : candidateVar ∈
      (capability.apply (Subst.singleCap index replacement).cap).unificationVars) :
    candidateVar ∈ capability.unificationVars ∨
      candidateVar ∈ replacement.unificationVars := by
  cases capability with
  | any => simp [Cap.apply, Cap.unificationVars] at member
  | var candidate =>
      by_cases same : candidate = index
      · subst candidate
        exact Or.inr (by
          simpa [Cap.apply, Subst.singleCap] using member)
      · exact Or.inl (by
          simpa [Cap.apply, Subst.singleCap, same,
            Cap.unificationVars] using member)
  | prod items =>
      exact Cap.mem_unificationVarsList_apply_singleCap
        candidateVar index replacement items member
  | con former arguments =>
      exact Cap.mem_unificationVarsList_apply_singleCap
        candidateVar index replacement arguments member

theorem Cap.mem_unificationVarsList_apply_singleCap
    (candidateVar : UnificationVar) (index : CapVar) (replacement : Cap)
    (items : List Cap)
    (member : candidateVar ∈
      Cap.unificationVarsList
        (Cap.applyList (Subst.singleCap index replacement).cap items)) :
    candidateVar ∈ Cap.unificationVarsList items ∨
      candidateVar ∈ replacement.unificationVars := by
  cases items with
  | nil => simp [Cap.applyList, Cap.unificationVarsList] at member
  | cons item items =>
      simp only [Cap.applyList, Cap.unificationVarsList,
        List.mem_append] at member ⊢
      rcases member with head | tail
      · rcases Cap.mem_unificationVars_apply_singleCap
          candidateVar index replacement item head with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Cap.mem_unificationVarsList_apply_singleCap
          candidateVar index replacement items tail with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

end


mutual

theorem Ty.mem_unificationVars_apply_singleCap
    (candidateVar : UnificationVar) (index : CapVar) (replacement : Cap)
    (target : Ty)
    (member : candidateVar ∈
      (target.apply (Subst.singleCap index replacement)).unificationVars) :
    candidateVar ∈ target.unificationVars ∨
      candidateVar ∈ replacement.unificationVars := by
  cases target with
  | var candidate =>
      exact Or.inl (by
        simpa [Ty.apply, Subst.singleCap, Ty.unificationVars] using member)
  | int => simp [Ty.apply, Ty.unificationVars] at member
  | fn domain codomain =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with inDomain | inCodomain
      · rcases Ty.mem_unificationVars_apply_singleCap
          candidateVar index replacement domain inDomain with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Ty.mem_unificationVars_apply_singleCap
          candidateVar index replacement codomain inCodomain with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced
  | prod items =>
      exact Ty.mem_unificationVarsList_apply_singleCap
        candidateVar index replacement items member
  | data former arguments =>
      exact Ty.mem_unificationVarsList_apply_singleCap
        candidateVar index replacement arguments member
  | matcher capability target =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with inCapability | inTarget
      · rcases Cap.mem_unificationVars_apply_singleCap
          candidateVar index replacement capability inCapability with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Ty.mem_unificationVars_apply_singleCap
          candidateVar index replacement target inTarget with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced
  | slot capability target =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with inCapability | inTarget
      · rcases Cap.mem_unificationVars_apply_singleCap
          candidateVar index replacement capability inCapability with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Ty.mem_unificationVars_apply_singleCap
          candidateVar index replacement target inTarget with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

theorem Ty.mem_unificationVarsList_apply_singleCap
    (candidateVar : UnificationVar) (index : CapVar) (replacement : Cap)
    (items : List Ty)
    (member : candidateVar ∈
      Ty.unificationVarsList
        (Ty.applyList (Subst.singleCap index replacement) items)) :
    candidateVar ∈ Ty.unificationVarsList items ∨
      candidateVar ∈ replacement.unificationVars := by
  cases items with
  | nil => simp [Ty.applyList, Ty.unificationVarsList] at member
  | cons item items =>
      simp only [Ty.applyList, Ty.unificationVarsList,
        List.mem_append] at member ⊢
      rcases member with head | tail
      · rcases Ty.mem_unificationVars_apply_singleCap
          candidateVar index replacement item head with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Ty.mem_unificationVarsList_apply_singleCap
          candidateVar index replacement items tail with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

end


mutual

theorem Ty.mem_unificationVars_apply_singleTy
    (candidateVar : UnificationVar) (index : TyVar) (replacement target : Ty)
    (member : candidateVar ∈
      (target.apply (Subst.singleTy index replacement)).unificationVars) :
    candidateVar ∈ target.unificationVars ∨
      candidateVar ∈ replacement.unificationVars := by
  cases target with
  | var candidate =>
      by_cases same : candidate = index
      · subst candidate
        exact Or.inr (by
          simpa [Ty.apply, Subst.singleTy] using member)
      · exact Or.inl (by
          simpa [Ty.apply, Subst.singleTy, same,
            Ty.unificationVars] using member)
  | int => simp [Ty.apply, Ty.unificationVars] at member
  | fn domain codomain =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with inDomain | inCodomain
      · rcases Ty.mem_unificationVars_apply_singleTy
          candidateVar index replacement domain inDomain with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Ty.mem_unificationVars_apply_singleTy
          candidateVar index replacement codomain inCodomain with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced
  | prod items =>
      exact Ty.mem_unificationVarsList_apply_singleTy
        candidateVar index replacement items member
  | data former arguments =>
      exact Ty.mem_unificationVarsList_apply_singleTy
        candidateVar index replacement arguments member
  | matcher capability target =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with inCapability | inTarget
      · exact Or.inl (Or.inl (by
          simpa [show (Subst.singleTy index replacement).cap = Subst.id.cap by rfl,
            Cap.apply_id] using inCapability))
      · rcases Ty.mem_unificationVars_apply_singleTy
          candidateVar index replacement target inTarget with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced
  | slot capability target =>
      simp only [Ty.apply, Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with inCapability | inTarget
      · exact Or.inl (Or.inl (by
          simpa [show (Subst.singleTy index replacement).cap = Subst.id.cap by rfl,
            Cap.apply_id] using inCapability))
      · rcases Ty.mem_unificationVars_apply_singleTy
          candidateVar index replacement target inTarget with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

theorem Ty.mem_unificationVarsList_apply_singleTy
    (candidateVar : UnificationVar) (index : TyVar) (replacement : Ty)
    (items : List Ty)
    (member : candidateVar ∈
      Ty.unificationVarsList
        (Ty.applyList (Subst.singleTy index replacement) items)) :
    candidateVar ∈ Ty.unificationVarsList items ∨
      candidateVar ∈ replacement.unificationVars := by
  cases items with
  | nil => simp [Ty.applyList, Ty.unificationVarsList] at member
  | cons item items =>
      simp only [Ty.applyList, Ty.unificationVarsList,
        List.mem_append] at member ⊢
      rcases member with head | tail
      · rcases Ty.mem_unificationVars_apply_singleTy
          candidateVar index replacement item head with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Ty.mem_unificationVarsList_apply_singleTy
          candidateVar index replacement items tail with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

end

mutual

theorem Cap.occurs_apply_singleCap_eq_false
    (index : CapVar) (replacement capability : Cap)
    (notOccurs : replacement.occurs index = false) :
    (capability.apply (Subst.singleCap index replacement).cap).occurs index =
      false := by
  cases capability with
  | any => rfl
  | var candidate =>
      by_cases same : candidate = index
      · subst candidate
        simpa [Cap.apply, Subst.singleCap] using notOccurs
      · simp [Cap.apply, Subst.singleCap, same, Cap.occurs]
  | prod items =>
      exact Cap.occursList_apply_singleCap_eq_false
        index replacement items notOccurs
  | con former arguments =>
      exact Cap.occursList_apply_singleCap_eq_false
        index replacement arguments notOccurs

theorem Cap.occursList_apply_singleCap_eq_false
    (index : CapVar) (replacement : Cap) (items : List Cap)
    (notOccurs : replacement.occurs index = false) :
    Cap.occursList index
      (Cap.applyList (Subst.singleCap index replacement).cap items) = false := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Cap.applyList, Cap.occursList,
        Cap.occurs_apply_singleCap_eq_false index replacement item notOccurs,
        Cap.occursList_apply_singleCap_eq_false index replacement items notOccurs]

end


mutual

theorem Ty.occursCap_apply_singleCap_eq_false
    (index : CapVar) (replacement : Cap) (target : Ty)
    (notOccurs : replacement.occurs index = false) :
    (target.apply (Subst.singleCap index replacement)).occursCap index = false := by
  cases target with
  | var candidate => rfl
  | int => rfl
  | fn domain codomain =>
      simp [Ty.apply, Ty.occursCap,
        Ty.occursCap_apply_singleCap_eq_false index replacement domain notOccurs,
        Ty.occursCap_apply_singleCap_eq_false index replacement codomain notOccurs]
  | prod items =>
      exact Ty.occursCapList_apply_singleCap_eq_false
        index replacement items notOccurs
  | data former arguments =>
      exact Ty.occursCapList_apply_singleCap_eq_false
        index replacement arguments notOccurs
  | matcher capability target =>
      simp [Ty.apply, Ty.occursCap,
        Cap.occurs_apply_singleCap_eq_false index replacement capability notOccurs,
        Ty.occursCap_apply_singleCap_eq_false index replacement target notOccurs]
  | slot capability target =>
      simp [Ty.apply, Ty.occursCap,
        Cap.occurs_apply_singleCap_eq_false index replacement capability notOccurs,
        Ty.occursCap_apply_singleCap_eq_false index replacement target notOccurs]

theorem Ty.occursCapList_apply_singleCap_eq_false
    (index : CapVar) (replacement : Cap) (items : List Ty)
    (notOccurs : replacement.occurs index = false) :
    Ty.occursCapList index
      (Ty.applyList (Subst.singleCap index replacement) items) = false := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Ty.applyList, Ty.occursCapList,
        Ty.occursCap_apply_singleCap_eq_false index replacement item notOccurs,
        Ty.occursCapList_apply_singleCap_eq_false index replacement items notOccurs]

end


mutual

theorem Ty.occursTy_apply_singleTy_eq_false
    (index : TyVar) (replacement target : Ty)
    (notOccurs : replacement.occursTy index = false) :
    (target.apply (Subst.singleTy index replacement)).occursTy index = false := by
  cases target with
  | var candidate =>
      by_cases same : candidate = index
      · subst candidate
        simpa [Ty.apply, Subst.singleTy] using notOccurs
      · simp [Ty.apply, Subst.singleTy, same, Ty.occursTy]
  | int => rfl
  | fn domain codomain =>
      simp [Ty.apply, Ty.occursTy,
        Ty.occursTy_apply_singleTy_eq_false index replacement domain notOccurs,
        Ty.occursTy_apply_singleTy_eq_false index replacement codomain notOccurs]
  | prod items =>
      exact Ty.occursTyList_apply_singleTy_eq_false
        index replacement items notOccurs
  | data former arguments =>
      exact Ty.occursTyList_apply_singleTy_eq_false
        index replacement arguments notOccurs
  | matcher capability target =>
      simpa [Ty.apply, Ty.occursTy] using
        Ty.occursTy_apply_singleTy_eq_false index replacement target notOccurs
  | slot capability target =>
      simpa [Ty.apply, Ty.occursTy] using
        Ty.occursTy_apply_singleTy_eq_false index replacement target notOccurs

theorem Ty.occursTyList_apply_singleTy_eq_false
    (index : TyVar) (replacement : Ty) (items : List Ty)
    (notOccurs : replacement.occursTy index = false) :
    Ty.occursTyList index
      (Ty.applyList (Subst.singleTy index replacement) items) = false := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Ty.applyList, Ty.occursTyList,
        Ty.occursTy_apply_singleTy_eq_false index replacement item notOccurs,
        Ty.occursTyList_apply_singleTy_eq_false index replacement items notOccurs]

end

theorem Cap.nodeCount_pos (capability : Cap) :
    0 < capability.nodeCount := by
  cases capability <;> simp only [Cap.nodeCount] <;> omega

mutual

def Ty.nodeCount : Ty → Nat
  | .var _ => 1
  | .int => 1
  | .fn domain codomain => 1 + domain.nodeCount + codomain.nodeCount
  | .prod items => 1 + Ty.nodeCountList items
  | .data _ arguments => 1 + Ty.nodeCountList arguments
  | .matcher capability target =>
      1 + capability.nodeCount + target.nodeCount
  | .slot capability target =>
      1 + capability.nodeCount + target.nodeCount

def Ty.nodeCountList : List Ty → Nat
  | [] => 0
  | item :: items => item.nodeCount + Ty.nodeCountList items

end

theorem Ty.nodeCount_pos (target : Ty) :
    0 < target.nodeCount := by
  cases target <;> simp only [Ty.nodeCount] <;> omega


mutual

theorem Cap.nodeCount_le_apply_of_occurs
    (substitution : CapSubst) (index : CapVar) (capability : Cap)
    (occurs : capability.occurs index = true) :
    (substitution index).nodeCount ≤
      (capability.apply substitution).nodeCount := by
  cases capability with
  | any => simp [Cap.occurs] at occurs
  | var candidate =>
      have equality : candidate = index := by
        simpa [Cap.occurs] using occurs
      subst candidate
      simp [Cap.apply]
  | prod items =>
      have bounded := Cap.nodeCount_le_applyList_of_occurs
        substitution index items occurs
      simp only [Cap.apply, Cap.nodeCount]
      omega
  | con former arguments =>
      have bounded := Cap.nodeCount_le_applyList_of_occurs
        substitution index arguments occurs
      simp only [Cap.apply, Cap.nodeCount]
      omega

theorem Cap.nodeCount_le_applyList_of_occurs
    (substitution : CapSubst) (index : CapVar) (items : List Cap)
    (occurs : Cap.occursList index items = true) :
    (substitution index).nodeCount ≤
      Cap.nodeCountList (Cap.applyList substitution items) := by
  cases items with
  | nil => simp [Cap.occursList] at occurs
  | cons item items =>
      cases itemOccurs : item.occurs index with
      | false =>
          have tailOccurs : Cap.occursList index items = true := by
            simpa [Cap.occursList, itemOccurs] using occurs
          have bounded := Cap.nodeCount_le_applyList_of_occurs
            substitution index items tailOccurs
          simp only [Cap.applyList, Cap.nodeCountList]
          omega
      | true =>
          have bounded := Cap.nodeCount_le_apply_of_occurs
            substitution index item itemOccurs
          simp only [Cap.applyList, Cap.nodeCountList]
          omega

end

theorem Cap.nodeCount_lt_apply_of_proper_occurs
    (substitution : CapSubst) (index : CapVar) (capability : Cap)
    (occurs : capability.occurs index = true)
    (proper : capability ≠ .var index) :
    (substitution index).nodeCount <
      (capability.apply substitution).nodeCount := by
  cases capability with
  | any => simp [Cap.occurs] at occurs
  | var candidate =>
      have equality : candidate = index := by
        simpa [Cap.occurs] using occurs
      subst candidate
      exact False.elim (proper rfl)
  | prod items =>
      have bounded := Cap.nodeCount_le_applyList_of_occurs
        substitution index items occurs
      simp only [Cap.apply, Cap.nodeCount]
      omega
  | con former arguments =>
      have bounded := Cap.nodeCount_le_applyList_of_occurs
        substitution index arguments occurs
      simp only [Cap.apply, Cap.nodeCount]
      omega

mutual

theorem Ty.nodeCount_le_apply_of_occursTy
    (substitution : Subst) (index : TyVar) (target : Ty)
    (occurs : target.occursTy index = true) :
    (substitution.ty index).nodeCount ≤
      (target.apply substitution).nodeCount := by
  cases target with
  | var candidate =>
      have equality : candidate = index := by
        simpa [Ty.occursTy] using occurs
      subst candidate
      simp [Ty.apply]
  | int => simp [Ty.occursTy] at occurs
  | fn domain codomain =>
      cases domainOccurs : domain.occursTy index with
      | false =>
          have codomainOccurs : codomain.occursTy index = true := by
            simpa [Ty.occursTy, domainOccurs] using occurs
          have bounded := Ty.nodeCount_le_apply_of_occursTy
            substitution index codomain codomainOccurs
          simp only [Ty.apply, Ty.nodeCount]
          omega
      | true =>
          have bounded := Ty.nodeCount_le_apply_of_occursTy
            substitution index domain domainOccurs
          simp only [Ty.apply, Ty.nodeCount]
          omega
  | prod items =>
      have bounded := Ty.nodeCount_le_applyList_of_occursTy
        substitution index items occurs
      simp only [Ty.apply, Ty.nodeCount]
      omega
  | data former arguments =>
      have bounded := Ty.nodeCount_le_applyList_of_occursTy
        substitution index arguments occurs
      simp only [Ty.apply, Ty.nodeCount]
      omega
  | matcher capability target =>
      have bounded := Ty.nodeCount_le_apply_of_occursTy
        substitution index target occurs
      simp only [Ty.apply, Ty.nodeCount]
      omega
  | slot capability target =>
      have bounded := Ty.nodeCount_le_apply_of_occursTy
        substitution index target occurs
      simp only [Ty.apply, Ty.nodeCount]
      omega

theorem Ty.nodeCount_le_applyList_of_occursTy
    (substitution : Subst) (index : TyVar) (items : List Ty)
    (occurs : Ty.occursTyList index items = true) :
    (substitution.ty index).nodeCount ≤
      Ty.nodeCountList (Ty.applyList substitution items) := by
  cases items with
  | nil => simp [Ty.occursTyList] at occurs
  | cons item items =>
      cases itemOccurs : item.occursTy index with
      | false =>
          have tailOccurs : Ty.occursTyList index items = true := by
            simpa [Ty.occursTyList, itemOccurs] using occurs
          have bounded := Ty.nodeCount_le_applyList_of_occursTy
            substitution index items tailOccurs
          simp only [Ty.applyList, Ty.nodeCountList]
          omega
      | true =>
          have bounded := Ty.nodeCount_le_apply_of_occursTy
            substitution index item itemOccurs
          simp only [Ty.applyList, Ty.nodeCountList]
          omega

end

theorem Ty.nodeCount_lt_apply_of_proper_occursTy
    (substitution : Subst) (index : TyVar) (target : Ty)
    (occurs : target.occursTy index = true)
    (proper : target ≠ .var index) :
    (substitution.ty index).nodeCount <
      (target.apply substitution).nodeCount := by
  cases target with
  | var candidate =>
      have equality : candidate = index := by
        simpa [Ty.occursTy] using occurs
      subst candidate
      exact False.elim (proper rfl)
  | int => simp [Ty.occursTy] at occurs
  | fn domain codomain =>
      cases domainOccurs : domain.occursTy index with
      | false =>
          have codomainOccurs : codomain.occursTy index = true := by
            simpa [Ty.occursTy, domainOccurs] using occurs
          have bounded := Ty.nodeCount_le_apply_of_occursTy
            substitution index codomain codomainOccurs
          simp only [Ty.apply, Ty.nodeCount]
          omega
      | true =>
          have bounded := Ty.nodeCount_le_apply_of_occursTy
            substitution index domain domainOccurs
          simp only [Ty.apply, Ty.nodeCount]
          omega
  | prod items =>
      have bounded := Ty.nodeCount_le_applyList_of_occursTy
        substitution index items occurs
      simp only [Ty.apply, Ty.nodeCount]
      omega
  | data former arguments =>
      have bounded := Ty.nodeCount_le_applyList_of_occursTy
        substitution index arguments occurs
      simp only [Ty.apply, Ty.nodeCount]
      omega
  | matcher capability target =>
      have bounded := Ty.nodeCount_le_apply_of_occursTy
        substitution index target occurs
      simp only [Ty.apply, Ty.nodeCount]
      omega
  | slot capability target =>
      have bounded := Ty.nodeCount_le_apply_of_occursTy
        substitution index target occurs
      simp only [Ty.apply, Ty.nodeCount]
      omega

theorem Cap.occurs_equation_impossible
    (substitution : CapSubst) (index : CapVar) (capability : Cap)
    (occurs : capability.occurs index = true)
    (proper : capability ≠ .var index)
    (equality : substitution index = capability.apply substitution) : False := by
  have smaller := Cap.nodeCount_lt_apply_of_proper_occurs
    substitution index capability occurs proper
  have sameSize := congrArg Cap.nodeCount equality
  omega

theorem Ty.occurs_equation_impossible
    (substitution : Subst) (index : TyVar) (target : Ty)
    (occurs : target.occursTy index = true)
    (proper : target ≠ .var index)
    (equality : substitution.ty index = target.apply substitution) : False := by
  have smaller := Ty.nodeCount_lt_apply_of_proper_occursTy
    substitution index target occurs proper
  have sameSize := congrArg Ty.nodeCount equality
  omega

@[simp] theorem Cap.length_applyList
    (substitution : CapSubst) (items : List Cap) :
    (Cap.applyList substitution items).length = items.length := by
  induction items with
  | nil => rfl
  | cons item items induction => simp [Cap.applyList, induction]

@[simp] theorem Ty.length_applyList
    (substitution : Subst) (items : List Ty) :
    (Ty.applyList substitution items).length = items.length := by
  induction items with
  | nil => rfl
  | cons item items induction => simp [Ty.applyList, induction]

theorem capEquations_exists_of_length_eq
    {left right : List Cap} (length : left.length = right.length) :
    ∃ equations, capEquations left right = some equations := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact ⟨[], rfl⟩
      | cons right rights => simp at length
  | cons left lefts induction =>
      cases right with
      | nil => simp at length
      | cons right rights =>
          simp only [List.length_cons, Nat.succ.injEq] at length
          obtain ⟨equations, paired⟩ := induction length
          exact ⟨.cap left right :: equations, by simp [capEquations, paired]⟩

theorem tyEquations_exists_of_length_eq
    {left right : List Ty} (length : left.length = right.length) :
    ∃ equations, tyEquations left right = some equations := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact ⟨[], rfl⟩
      | cons right rights => simp at length
  | cons left lefts induction =>
      cases right with
      | nil => simp at length
      | cons right rights =>
          simp only [List.length_cons, Nat.succ.injEq] at length
          obtain ⟨equations, paired⟩ := induction length
          exact ⟨.ty left right :: equations, by simp [tyEquations, paired]⟩

namespace Equation

/-- Node count of both sides after applying a candidate solution. -/
def solvedNodeCount (substitution : Subst) : Equation → Nat
  | .cap left right =>
      (left.apply substitution.cap).nodeCount +
        (right.apply substitution.cap).nodeCount
  | .ty left right =>
      (left.apply substitution).nodeCount +
        (right.apply substitution).nodeCount

theorem solvedNodeCount_pos (substitution : Subst) (equation : Equation) :
    0 < equation.solvedNodeCount substitution := by
  cases equation with
  | cap left right =>
      simp only [solvedNodeCount]
      have leftPositive := Cap.nodeCount_pos (left.apply substitution.cap)
      have rightPositive := Cap.nodeCount_pos (right.apply substitution.cap)
      omega
  | ty left right =>
      simp only [solvedNodeCount]
      have leftPositive := Ty.nodeCount_pos (left.apply substitution)
      have rightPositive := Ty.nodeCount_pos (right.apply substitution)
      omega

@[simp] theorem solvedNodeCount_apply
    (later earlier : Subst) (equation : Equation) :
    (equation.apply earlier).solvedNodeCount later =
      equation.solvedNodeCount (Subst.compose later earlier) := by
  cases equation <;>
    simp [Equation.apply, solvedNodeCount, Cap.apply_compose, Ty.apply_compose]

end Equation

/-- Semantic worklist size under a fixed solution. -/
def solvedNodeCount (substitution : Subst) : List Equation → Nat
  | [] => 0
  | equation :: equations =>
      equation.solvedNodeCount substitution + solvedNodeCount substitution equations

@[simp] theorem solvedNodeCount_append
    (substitution : Subst) (left right : List Equation) :
    solvedNodeCount substitution (left ++ right) =
      solvedNodeCount substitution left + solvedNodeCount substitution right := by
  induction left with
  | nil => simp [solvedNodeCount]
  | cons equation equations induction =>
      simp [solvedNodeCount, induction, Nat.add_assoc]

@[simp] theorem solvedNodeCount_map_apply
    (later earlier : Subst) (equations : List Equation) :
    solvedNodeCount later (equations.map (Equation.apply earlier)) =
      solvedNodeCount (Subst.compose later earlier) equations := by
  induction equations with
  | nil => rfl
  | cons equation equations induction =>
      simp [solvedNodeCount, induction]

theorem capEquations_solvedNodeCount
    {left right : List Cap} {equations : List Equation}
    (paired : capEquations left right = some equations)
    (substitution : Subst) :
    solvedNodeCount substitution equations =
      Cap.nodeCountList (Cap.applyList substitution.cap left) +
        Cap.nodeCountList (Cap.applyList substitution.cap right) := by
  induction left generalizing right equations with
  | nil =>
      cases right with
      | nil =>
          simp [capEquations] at paired
          subst equations
          rfl
      | cons right rights => simp [capEquations] at paired
  | cons left lefts induction =>
      cases right with
      | nil => simp [capEquations] at paired
      | cons right rights =>
          simp only [capEquations] at paired
          cases pairedRest : capEquations lefts rights with
          | none => simp [pairedRest] at paired
          | some children =>
              simp [pairedRest] at paired
              subst equations
              simp [solvedNodeCount, Equation.solvedNodeCount,
                Cap.applyList, Cap.nodeCountList, induction pairedRest]
              omega

theorem tyEquations_solvedNodeCount
    {left right : List Ty} {equations : List Equation}
    (paired : tyEquations left right = some equations)
    (substitution : Subst) :
    solvedNodeCount substitution equations =
      Ty.nodeCountList (Ty.applyList substitution left) +
        Ty.nodeCountList (Ty.applyList substitution right) := by
  induction left generalizing right equations with
  | nil =>
      cases right with
      | nil =>
          simp [tyEquations] at paired
          subst equations
          rfl
      | cons right rights => simp [tyEquations] at paired
  | cons left lefts induction =>
      cases right with
      | nil => simp [tyEquations] at paired
      | cons right rights =>
          simp only [tyEquations] at paired
          cases pairedRest : tyEquations lefts rights with
          | none => simp [pairedRest] at paired
          | some children =>
              simp [pairedRest] at paired
              subst equations
              simp [solvedNodeCount, Equation.solvedNodeCount,
                Ty.applyList, Ty.nodeCountList, induction pairedRest]
              omega

theorem solvedNodeCount_tail_lt
    (substitution : Subst) (equation : Equation) (equations : List Equation) :
    solvedNodeCount substitution equations <
      solvedNodeCount substitution (equation :: equations) := by
  have positive := Equation.solvedNodeCount_pos substitution equation
  simp only [solvedNodeCount]
  omega

/-- A certified reduction strictly decreases the instantiated worklist size
under every solution of its input. -/
theorem Reduces.solvedNodeCount_lt
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining)
    {solution : Subst} (solved : Solves solution input) :
    solvedNodeCount solution remaining < solvedNodeCount solution input := by
  have absorbed := reduction.absorbed solved
  cases reduction with
  | capAny =>
      exact solvedNodeCount_tail_lt _ _ _
  | capVarRefl =>
      exact solvedNodeCount_tail_lt _ _ _
  | capVarLeft =>
      simp only [solvedNodeCount_map_apply, absorbed]
      exact solvedNodeCount_tail_lt _ _ _
  | capVarRight =>
      simp only [solvedNodeCount_map_apply, absorbed]
      exact solvedNodeCount_tail_lt _ _ _
  | capProd paired =>
      simp only [solvedNodeCount_append, solvedNodeCount,
        Equation.solvedNodeCount, Cap.apply, Cap.nodeCount]
      rw [capEquations_solvedNodeCount paired]
      omega
  | capCon paired =>
      simp only [solvedNodeCount_append, solvedNodeCount,
        Equation.solvedNodeCount, Cap.apply, Cap.nodeCount]
      rw [capEquations_solvedNodeCount paired]
      omega
  | tyVarRefl =>
      exact solvedNodeCount_tail_lt _ _ _
  | tyVarLeft =>
      simp only [solvedNodeCount_map_apply, absorbed]
      exact solvedNodeCount_tail_lt _ _ _
  | tyVarRight =>
      simp only [solvedNodeCount_map_apply, absorbed]
      exact solvedNodeCount_tail_lt _ _ _
  | tyInt =>
      exact solvedNodeCount_tail_lt _ _ _
  | tyFn =>
      simp [solvedNodeCount, Equation.solvedNodeCount, Ty.apply, Ty.nodeCount]
      omega
  | tyProd paired =>
      simp only [solvedNodeCount_append, solvedNodeCount,
        Equation.solvedNodeCount, Ty.apply, Ty.nodeCount]
      rw [tyEquations_solvedNodeCount paired]
      omega
  | tyData paired =>
      simp only [solvedNodeCount_append, solvedNodeCount,
        Equation.solvedNodeCount, Ty.apply, Ty.nodeCount]
      rw [tyEquations_solvedNodeCount paired]
      omega
  | tyMatcher =>
      simp [solvedNodeCount, Equation.solvedNodeCount, Ty.apply, Ty.nodeCount]
      omega
  | tySlot =>
      simp [solvedNodeCount, Equation.solvedNodeCount, Ty.apply, Ty.nodeCount]
      omega

/-- A nonempty solvable worklist cannot fail during its next deterministic
reduction. -/
theorem reduce_some_of_solves
    {equation : Equation} {equations : List Equation} {solution : Subst}
    (solved : Solves solution (equation :: equations)) :
    ∃ result, reduce (equation :: equations) = some result := by
  cases reduced : reduce (equation :: equations) with
  | some result => exact ⟨result, rfl⟩
  | none =>
      obtain ⟨head, _⟩ := (solves_cons solution equation equations).mp solved
      cases equation with
      | cap left right =>
          cases left with
          | any =>
              cases right with
              | any => simp [reduce] at reduced
              | var index => simp [reduce, Cap.occurs] at reduced
              | prod items => simp [Equation.Holds, Cap.apply] at head
              | con former arguments => simp [Equation.Holds, Cap.apply] at head
          | var index =>
              cases right with
              | any => simp [reduce, Cap.occurs] at reduced
              | var candidate =>
                  by_cases same : index = candidate
                  · subst candidate
                    simp [reduce] at reduced
                  · simp [reduce, same] at reduced
              | prod items =>
                  by_cases occurs : (Cap.prod items).occurs index = true
                  · simp only [Equation.Holds, Cap.apply] at head
                    exact False.elim (Cap.occurs_equation_impossible
                      solution.cap index (.prod items) occurs (by intro equality; cases equality)
                      head)
                  · have notOccurs : (Cap.prod items).occurs index = false := by
                      cases found : (Cap.prod items).occurs index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | con former arguments =>
                  by_cases occurs : (Cap.con former arguments).occurs index = true
                  · simp only [Equation.Holds, Cap.apply] at head
                    exact False.elim (Cap.occurs_equation_impossible
                      solution.cap index (.con former arguments) occurs
                      (by intro equality; cases equality) head)
                  · have notOccurs :
                        (Cap.con former arguments).occurs index = false := by
                      cases found : (Cap.con former arguments).occurs index <;> simp_all
                    simp [reduce, notOccurs] at reduced
          | prod leftItems =>
              cases right with
              | any => simp [Equation.Holds, Cap.apply] at head
              | var index =>
                  by_cases occurs : (Cap.prod leftItems).occurs index = true
                  · simp only [Equation.Holds, Cap.apply] at head
                    exact False.elim (Cap.occurs_equation_impossible
                      solution.cap index (.prod leftItems) occurs
                      (by intro equality; cases equality) head.symm)
                  · have notOccurs : (Cap.prod leftItems).occurs index = false := by
                      cases found : (Cap.prod leftItems).occurs index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | prod rightItems =>
                  simp only [Equation.Holds, Cap.apply] at head
                  injection head with itemEquality
                  have length : leftItems.length = rightItems.length := by
                    have appliedLength := congrArg List.length itemEquality
                    simpa using appliedLength
                  obtain ⟨children, paired⟩ :=
                    capEquations_exists_of_length_eq length
                  simp only [reduce] at reduced
                  split at reduced <;> simp_all
              | con former arguments => simp [Equation.Holds, Cap.apply] at head
          | con leftFormer leftArguments =>
              cases right with
              | any => simp [Equation.Holds, Cap.apply] at head
              | var index =>
                  by_cases occurs :
                      (Cap.con leftFormer leftArguments).occurs index = true
                  · simp only [Equation.Holds, Cap.apply] at head
                    exact False.elim (Cap.occurs_equation_impossible
                      solution.cap index (.con leftFormer leftArguments) occurs
                      (by intro equality; cases equality) head.symm)
                  · have notOccurs :
                        (Cap.con leftFormer leftArguments).occurs index = false := by
                      cases found :
                        (Cap.con leftFormer leftArguments).occurs index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | prod rightItems => simp [Equation.Holds, Cap.apply] at head
              | con rightFormer rightArguments =>
                  simp only [Equation.Holds, Cap.apply] at head
                  injection head with formerEquality argumentEquality
                  subst rightFormer
                  have length : leftArguments.length = rightArguments.length := by
                    have appliedLength := congrArg List.length argumentEquality
                    simpa using appliedLength
                  obtain ⟨children, paired⟩ :=
                    capEquations_exists_of_length_eq length
                  simp only [reduce] at reduced
                  split at reduced
                  · split at reduced <;> simp_all
                  · simp_all
      | ty left right =>
          cases left with
          | var index =>
              cases right with
              | var candidate =>
                  by_cases same : index = candidate
                  · subst candidate
                    simp [reduce] at reduced
                  · simp [reduce, same] at reduced
              | int => simp [reduce, Ty.occursTy] at reduced
              | fn domain codomain =>
                  by_cases occurs : (Ty.fn domain codomain).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.fn domain codomain) occurs
                      (by intro equality; cases equality) head)
                  · have notOccurs : (Ty.fn domain codomain).occursTy index = false := by
                      cases found : (Ty.fn domain codomain).occursTy index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | prod items =>
                  by_cases occurs : (Ty.prod items).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.prod items) occurs
                      (by intro equality; cases equality) head)
                  · have notOccurs : (Ty.prod items).occursTy index = false := by
                      cases found : (Ty.prod items).occursTy index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | data former arguments =>
                  by_cases occurs : (Ty.data former arguments).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.data former arguments) occurs
                      (by intro equality; cases equality) head)
                  · have notOccurs :
                        (Ty.data former arguments).occursTy index = false := by
                      cases found : (Ty.data former arguments).occursTy index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | matcher capability target =>
                  by_cases occurs : (Ty.matcher capability target).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.matcher capability target) occurs
                      (by intro equality; cases equality) head)
                  · have notOccurs :
                        (Ty.matcher capability target).occursTy index = false := by
                      cases found : (Ty.matcher capability target).occursTy index <;>
                        simp_all
                    simp [reduce, notOccurs] at reduced
              | slot capability target =>
                  by_cases occurs : (Ty.slot capability target).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.slot capability target) occurs
                      (by intro equality; cases equality) head)
                  · have notOccurs :
                        (Ty.slot capability target).occursTy index = false := by
                      cases found : (Ty.slot capability target).occursTy index <;>
                        simp_all
                    simp [reduce, notOccurs] at reduced
          | int =>
              cases right with
              | var index => simp [reduce, Ty.occursTy] at reduced
              | int => simp [reduce] at reduced
              | fn domain codomain => simp [Equation.Holds, Ty.apply] at head
              | prod items => simp [Equation.Holds, Ty.apply] at head
              | data former arguments => simp [Equation.Holds, Ty.apply] at head
              | matcher capability target => simp [Equation.Holds, Ty.apply] at head
              | slot capability target => simp [Equation.Holds, Ty.apply] at head
          | fn leftDomain leftCodomain =>
              cases right with
              | var index =>
                  by_cases occurs :
                      (Ty.fn leftDomain leftCodomain).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.fn leftDomain leftCodomain) occurs
                      (by intro equality; cases equality) head.symm)
                  · have notOccurs :
                        (Ty.fn leftDomain leftCodomain).occursTy index = false := by
                      cases found :
                        (Ty.fn leftDomain leftCodomain).occursTy index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | int => simp [Equation.Holds, Ty.apply] at head
              | fn rightDomain rightCodomain => simp [reduce] at reduced
              | prod items => simp [Equation.Holds, Ty.apply] at head
              | data former arguments => simp [Equation.Holds, Ty.apply] at head
              | matcher capability target => simp [Equation.Holds, Ty.apply] at head
              | slot capability target => simp [Equation.Holds, Ty.apply] at head
          | prod leftItems =>
              cases right with
              | var index =>
                  by_cases occurs : (Ty.prod leftItems).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.prod leftItems) occurs
                      (by intro equality; cases equality) head.symm)
                  · have notOccurs : (Ty.prod leftItems).occursTy index = false := by
                      cases found : (Ty.prod leftItems).occursTy index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | int => simp [Equation.Holds, Ty.apply] at head
              | fn domain codomain => simp [Equation.Holds, Ty.apply] at head
              | prod rightItems =>
                  simp only [Equation.Holds, Ty.apply] at head
                  injection head with itemEquality
                  have length : leftItems.length = rightItems.length := by
                    have appliedLength := congrArg List.length itemEquality
                    simpa using appliedLength
                  obtain ⟨children, paired⟩ :=
                    tyEquations_exists_of_length_eq length
                  simp only [reduce] at reduced
                  split at reduced <;> simp_all
              | data former arguments => simp [Equation.Holds, Ty.apply] at head
              | matcher capability target => simp [Equation.Holds, Ty.apply] at head
              | slot capability target => simp [Equation.Holds, Ty.apply] at head
          | matcher leftCapability leftTarget =>
              cases right with
              | var index =>
                  by_cases occurs :
                      (Ty.matcher leftCapability leftTarget).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.matcher leftCapability leftTarget) occurs
                      (by intro equality; cases equality) head.symm)
                  · have notOccurs :
                        (Ty.matcher leftCapability leftTarget).occursTy index = false := by
                      cases found :
                        (Ty.matcher leftCapability leftTarget).occursTy index <;>
                        simp_all
                    simp [reduce, notOccurs] at reduced
              | int => simp [Equation.Holds, Ty.apply] at head
              | fn domain codomain => simp [Equation.Holds, Ty.apply] at head
              | prod items => simp [Equation.Holds, Ty.apply] at head
              | data former arguments => simp [Equation.Holds, Ty.apply] at head
              | matcher rightCapability rightTarget => simp [reduce] at reduced
              | slot capability target => simp [Equation.Holds, Ty.apply] at head
          | slot leftCapability leftTarget =>
              cases right with
              | var index =>
                  by_cases occurs :
                      (Ty.slot leftCapability leftTarget).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.slot leftCapability leftTarget) occurs
                      (by intro equality; cases equality) head.symm)
                  · have notOccurs :
                        (Ty.slot leftCapability leftTarget).occursTy index = false := by
                      cases found :
                        (Ty.slot leftCapability leftTarget).occursTy index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | int => simp [Equation.Holds, Ty.apply] at head
              | fn domain codomain => simp [Equation.Holds, Ty.apply] at head
              | prod items => simp [Equation.Holds, Ty.apply] at head
              | data former arguments => simp [Equation.Holds, Ty.apply] at head
              | matcher capability target => simp [Equation.Holds, Ty.apply] at head
              | slot rightCapability rightTarget => simp [reduce] at reduced
          | data leftFormer leftArguments =>
              cases right with
              | var index =>
                  by_cases occurs :
                      (Ty.data leftFormer leftArguments).occursTy index = true
                  · simp only [Equation.Holds, Ty.apply] at head
                    exact False.elim (Ty.occurs_equation_impossible
                      solution index (.data leftFormer leftArguments) occurs
                      (by intro equality; cases equality) head.symm)
                  · have notOccurs :
                        (Ty.data leftFormer leftArguments).occursTy index = false := by
                      cases found :
                        (Ty.data leftFormer leftArguments).occursTy index <;> simp_all
                    simp [reduce, notOccurs] at reduced
              | int => simp [Equation.Holds, Ty.apply] at head
              | fn domain codomain => simp [Equation.Holds, Ty.apply] at head
              | prod items => simp [Equation.Holds, Ty.apply] at head
              | data rightFormer rightArguments =>
                  simp only [Equation.Holds, Ty.apply] at head
                  injection head with formerEquality argumentEquality
                  subst rightFormer
                  have length : leftArguments.length = rightArguments.length := by
                    have appliedLength := congrArg List.length argumentEquality
                    simpa using appliedLength
                  obtain ⟨children, paired⟩ :=
                    tyEquations_exists_of_length_eq length
                  simp only [reduce] at reduced
                  split at reduced
                  · split at reduced <;> simp_all
                  · simp_all
              | matcher capability target => simp [Equation.Holds, Ty.apply] at head
              | slot capability target => simp [Equation.Holds, Ty.apply] at head

/-- Any fuel at least as large as the instantiated worklist measure is
sufficient for a known solution.  The bound is semantic--it is computable once
the solution is supplied--and is used here to establish finite success. -/
theorem unifyWithFuel_complete_of_solvedNodeCount_le
    {fuel : Nat} {equations : List Equation} {solution : Subst}
    (solved : Solves solution equations)
    (bounded : solvedNodeCount solution equations ≤ fuel) :
    ∃ result, unifyWithFuel fuel equations = some result := by
  induction fuel generalizing equations with
  | zero =>
      cases equations with
      | nil => exact ⟨Subst.id, rfl⟩
      | cons equation equations =>
          have positive := solvedNodeCount_tail_lt solution equation equations
          simp only [solvedNodeCount] at bounded positive
          omega
  | succ fuel induction =>
      cases equations with
      | nil => exact ⟨Subst.id, rfl⟩
      | cons equation equations =>
          obtain ⟨reduction, reduced⟩ := reduce_some_of_solves solved
          have remainingSolved := reduction.valid.complete solved
          have decreases := reduction.valid.solvedNodeCount_lt solved
          have remainingBounded :
              solvedNodeCount solution reduction.equations ≤ fuel := by
            omega
          obtain ⟨later, recursive⟩ :=
            induction remainingSolved remainingBounded
          refine ⟨Subst.compose later reduction.substitution, ?_⟩
          simp only [unifyWithFuel]
          simp [reduced, recursive]

/-- The instantiated node count is a sufficient fuel value for its solution. -/
theorem unifyWithFuel_complete_at_solvedNodeCount
    {equations : List Equation} {solution : Subst}
    (solved : Solves solution equations) :
    ∃ result,
      unifyWithFuel (solvedNodeCount solution equations) equations = some result :=
  unifyWithFuel_complete_of_solvedNodeCount_le solved (Nat.le_refl _)

/-- Solvability is equivalent to success at some finite fuel. -/
theorem solvable_iff_unifyWithFuel_succeeds (equations : List Equation) :
    (∃ solution, Solves solution equations) ↔
      ∃ fuel result, unifyWithFuel fuel equations = some result := by
  constructor
  · rintro ⟨solution, solved⟩
    obtain ⟨result, success⟩ :=
      unifyWithFuel_complete_at_solvedNodeCount solved
    exact ⟨solvedNodeCount solution equations, result, success⟩
  · rintro ⟨fuel, result, success⟩
    exact ⟨result, unifyWithFuel_sound success⟩

/-- Unsatisfiability is exactly failure for every finite fuel. -/
theorem all_fuels_fail_iff_unsatisfiable (equations : List Equation) :
    (∀ fuel, unifyWithFuel fuel equations = none) ↔
      ¬ ∃ solution, Solves solution equations := by
  rw [solvable_iff_unifyWithFuel_succeeds]
  constructor
  · intro allFail ⟨fuel, result, success⟩
    rw [allFail fuel] at success
    cases success
  · intro noSuccess fuel
    cases computed : unifyWithFuel fuel equations with
    | none => rfl
    | some result =>
        exact False.elim (noSuccess ⟨fuel, result, computed⟩)

/-- Every solvable worklist has a successful run returning an MGU. -/
theorem solvable_has_finite_mgu
    {equations : List Equation} (solvable : ∃ solution, Solves solution equations) :
    ∃ fuel result,
      unifyWithFuel fuel equations = some result ∧
        MostGeneral equations result := by
  obtain ⟨fuel, result, success⟩ :=
    (solvable_iff_unifyWithFuel_succeeds equations).mp solvable
  exact ⟨fuel, result, success, unifyWithFuel_mostGeneral success⟩

/-! ## Fuel-free executable driver -/


def Equation.unificationVars : Equation → List UnificationVar
  | .cap left right => left.unificationVars ++ right.unificationVars
  | .ty left right => left.unificationVars ++ right.unificationVars

def unificationVars : List Equation → List UnificationVar
  | [] => []
  | equation :: equations =>
      equation.unificationVars ++ unificationVars equations

mutual

@[simp] theorem Cap.cap_mem_unificationVars_iff
    (index : CapVar) (capability : Cap) :
    .cap index ∈ capability.unificationVars ↔
      capability.occurs index = true := by
  cases capability with
  | any => simp [Cap.unificationVars, Cap.occurs]
  | var candidate => simp [Cap.unificationVars, Cap.occurs, eq_comm]
  | prod items =>
      exact Cap.cap_mem_unificationVarsList_iff index items
  | con former arguments =>
      exact Cap.cap_mem_unificationVarsList_iff index arguments

@[simp] theorem Cap.cap_mem_unificationVarsList_iff
    (index : CapVar) (items : List Cap) :
    .cap index ∈ Cap.unificationVarsList items ↔
      Cap.occursList index items = true := by
  cases items with
  | nil => simp [Cap.unificationVarsList, Cap.occursList]
  | cons item items =>
      simp [Cap.unificationVarsList, Cap.occursList,
        Cap.cap_mem_unificationVars_iff,
        Cap.cap_mem_unificationVarsList_iff]

end

mutual

@[simp] theorem Cap.ty_not_mem_unificationVars
    (index : TyVar) (capability : Cap) :
    .ty index ∉ capability.unificationVars := by
  cases capability with
  | any => simp [Cap.unificationVars]
  | var candidate => simp [Cap.unificationVars]
  | prod items => exact Cap.ty_not_mem_unificationVarsList index items
  | con former arguments => exact Cap.ty_not_mem_unificationVarsList index arguments

@[simp] theorem Cap.ty_not_mem_unificationVarsList
    (index : TyVar) (items : List Cap) :
    .ty index ∉ Cap.unificationVarsList items := by
  cases items with
  | nil => simp [Cap.unificationVarsList]
  | cons item items =>
      simp [Cap.unificationVarsList, Cap.ty_not_mem_unificationVars,
        Cap.ty_not_mem_unificationVarsList]

end


mutual

@[simp] theorem Ty.ty_mem_unificationVars_iff
    (index : TyVar) (target : Ty) :
    .ty index ∈ target.unificationVars ↔
      target.occursTy index = true := by
  cases target with
  | var candidate => simp [Ty.unificationVars, Ty.occursTy, eq_comm]
  | int => simp [Ty.unificationVars, Ty.occursTy]
  | fn domain codomain =>
      simp [Ty.unificationVars, Ty.occursTy,
        Ty.ty_mem_unificationVars_iff]
  | prod items => exact Ty.ty_mem_unificationVarsList_iff index items
  | data former arguments => exact Ty.ty_mem_unificationVarsList_iff index arguments
  | matcher capability target =>
      simp [Ty.unificationVars, Ty.occursTy,
        Ty.ty_mem_unificationVars_iff]
  | slot capability target =>
      simp [Ty.unificationVars, Ty.occursTy,
        Ty.ty_mem_unificationVars_iff]

@[simp] theorem Ty.ty_mem_unificationVarsList_iff
    (index : TyVar) (items : List Ty) :
    .ty index ∈ Ty.unificationVarsList items ↔
      Ty.occursTyList index items = true := by
  cases items with
  | nil => simp [Ty.unificationVarsList, Ty.occursTyList]
  | cons item items =>
      simp [Ty.unificationVarsList, Ty.occursTyList,
        Ty.ty_mem_unificationVars_iff,
        Ty.ty_mem_unificationVarsList_iff]

end

mutual

@[simp] theorem Ty.cap_mem_unificationVars_iff
    (index : CapVar) (target : Ty) :
    .cap index ∈ target.unificationVars ↔
      target.occursCap index = true := by
  cases target with
  | var candidate => simp [Ty.unificationVars, Ty.occursCap]
  | int => simp [Ty.unificationVars, Ty.occursCap]
  | fn domain codomain =>
      simp [Ty.unificationVars, Ty.occursCap,
        Ty.cap_mem_unificationVars_iff]
  | prod items => exact Ty.cap_mem_unificationVarsList_iff index items
  | data former arguments => exact Ty.cap_mem_unificationVarsList_iff index arguments
  | matcher capability target =>
      simp [Ty.unificationVars, Ty.occursCap,
        Ty.cap_mem_unificationVars_iff]
  | slot capability target =>
      simp [Ty.unificationVars, Ty.occursCap,
        Ty.cap_mem_unificationVars_iff]

@[simp] theorem Ty.cap_mem_unificationVarsList_iff
    (index : CapVar) (items : List Ty) :
    .cap index ∈ Ty.unificationVarsList items ↔
      Ty.occursCapList index items = true := by
  cases items with
  | nil => simp [Ty.unificationVarsList, Ty.occursCapList]
  | cons item items =>
      simp [Ty.unificationVarsList, Ty.occursCapList,
        Ty.cap_mem_unificationVars_iff,
        Ty.cap_mem_unificationVarsList_iff]

end

theorem Equation.mem_unificationVars_apply_singleCap
    (candidateVar : UnificationVar) (index : CapVar) (replacement : Cap)
    (equation : Equation)
    (member : candidateVar ∈
      (equation.apply (Subst.singleCap index replacement)).unificationVars) :
    candidateVar ∈ equation.unificationVars ∨
      candidateVar ∈ replacement.unificationVars := by
  cases equation with
  | cap left right =>
      simp only [Equation.apply, Equation.unificationVars,
        List.mem_append] at member ⊢
      rcases member with inLeft | inRight
      · rcases Cap.mem_unificationVars_apply_singleCap
          candidateVar index replacement left inLeft with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Cap.mem_unificationVars_apply_singleCap
          candidateVar index replacement right inRight with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced
  | ty left right =>
      simp only [Equation.apply, Equation.unificationVars,
        List.mem_append] at member ⊢
      rcases member with inLeft | inRight
      · rcases Ty.mem_unificationVars_apply_singleCap
          candidateVar index replacement left inLeft with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Ty.mem_unificationVars_apply_singleCap
          candidateVar index replacement right inRight with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

theorem Equation.mem_unificationVars_apply_singleTy
    (candidateVar : UnificationVar) (index : TyVar) (replacement : Ty)
    (equation : Equation)
    (member : candidateVar ∈
      (equation.apply (Subst.singleTy index replacement)).unificationVars) :
    candidateVar ∈ equation.unificationVars ∨
      candidateVar ∈ replacement.unificationVars := by
  cases equation with
  | cap left right =>
      exact Or.inl (by
        simpa [Equation.apply, Equation.unificationVars,
          show (Subst.singleTy index replacement).cap = Subst.id.cap by rfl,
          Cap.apply_id] using member)
  | ty left right =>
      simp only [Equation.apply, Equation.unificationVars,
        List.mem_append] at member ⊢
      rcases member with inLeft | inRight
      · rcases Ty.mem_unificationVars_apply_singleTy
          candidateVar index replacement left inLeft with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases Ty.mem_unificationVars_apply_singleTy
          candidateVar index replacement right inRight with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

theorem mem_unificationVars_map_apply_singleCap
    (candidateVar : UnificationVar) (index : CapVar) (replacement : Cap)
    (equations : List Equation)
    (member : candidateVar ∈ unificationVars
      (equations.map (Equation.apply (Subst.singleCap index replacement)))) :
    candidateVar ∈ unificationVars equations ∨
      candidateVar ∈ replacement.unificationVars := by
  induction equations with
  | nil => simp [unificationVars] at member
  | cons equation equations induction =>
      simp only [List.map_cons, unificationVars, List.mem_append] at member ⊢
      rcases member with head | tail
      · rcases Equation.mem_unificationVars_apply_singleCap
          candidateVar index replacement equation head with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases induction tail with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

theorem mem_unificationVars_map_apply_singleTy
    (candidateVar : UnificationVar) (index : TyVar) (replacement : Ty)
    (equations : List Equation)
    (member : candidateVar ∈ unificationVars
      (equations.map (Equation.apply (Subst.singleTy index replacement)))) :
    candidateVar ∈ unificationVars equations ∨
      candidateVar ∈ replacement.unificationVars := by
  induction equations with
  | nil => simp [unificationVars] at member
  | cons equation equations induction =>
      simp only [List.map_cons, unificationVars, List.mem_append] at member ⊢
      rcases member with head | tail
      · rcases Equation.mem_unificationVars_apply_singleTy
          candidateVar index replacement equation head with original | introduced
        · exact Or.inl (Or.inl original)
        · exact Or.inr introduced
      · rcases induction tail with original | introduced
        · exact Or.inl (Or.inr original)
        · exact Or.inr introduced

theorem capEquations_mem_unificationVars
    {left right : List Cap} {children : List Equation}
    (paired : capEquations left right = some children)
    (candidateVar : UnificationVar)
    (member : candidateVar ∈ unificationVars children) :
    candidateVar ∈ Cap.unificationVarsList left ∨
      candidateVar ∈ Cap.unificationVarsList right := by
  induction left generalizing right children with
  | nil =>
      cases right <;> simp [capEquations] at paired
      subst children
      simp [unificationVars] at member
  | cons left lefts induction =>
      cases right with
      | nil => simp [capEquations] at paired
      | cons right rights =>
          simp only [capEquations] at paired
          cases pairedRest : capEquations lefts rights with
          | none => simp [pairedRest] at paired
          | some rest =>
              simp [pairedRest] at paired
              subst children
              simp only [unificationVars, Equation.unificationVars,
                Cap.unificationVarsList, List.mem_append] at member ⊢
              rcases member with (inLeft | inRight) | inRest
              · exact Or.inl (Or.inl inLeft)
              · exact Or.inr (Or.inl inRight)
              · rcases induction pairedRest inRest with
                    restLeft | restRight
                · exact Or.inl (Or.inr restLeft)
                · exact Or.inr (Or.inr restRight)

theorem tyEquations_mem_unificationVars
    {left right : List Ty} {children : List Equation}
    (paired : tyEquations left right = some children)
    (candidateVar : UnificationVar)
    (member : candidateVar ∈ unificationVars children) :
    candidateVar ∈ Ty.unificationVarsList left ∨
      candidateVar ∈ Ty.unificationVarsList right := by
  induction left generalizing right children with
  | nil =>
      cases right <;> simp [tyEquations] at paired
      subst children
      simp [unificationVars] at member
  | cons left lefts induction =>
      cases right with
      | nil => simp [tyEquations] at paired
      | cons right rights =>
          simp only [tyEquations] at paired
          cases pairedRest : tyEquations lefts rights with
          | none => simp [pairedRest] at paired
          | some rest =>
              simp [pairedRest] at paired
              subst children
              simp only [unificationVars, Equation.unificationVars,
                Ty.unificationVarsList, List.mem_append] at member ⊢
              rcases member with (inLeft | inRight) | inRest
              · exact Or.inl (Or.inl inLeft)
              · exact Or.inr (Or.inl inRight)
              · rcases induction pairedRest inRest with
                    restLeft | restRight
                · exact Or.inl (Or.inr restLeft)
                · exact Or.inr (Or.inr restRight)

@[simp] theorem unificationVars_append
    (left right : List Equation) :
    unificationVars (left ++ right) =
      unificationVars left ++ unificationVars right := by
  induction left with
  | nil => rfl
  | cons equation equations induction =>
      simp [unificationVars, induction, List.append_assoc]

/-- One reduction never introduces a variable absent from its input. -/
theorem Reduces.unificationVars_subset
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining) :
    ∀ candidateVar, candidateVar ∈ unificationVars remaining →
      candidateVar ∈ unificationVars input := by
  intro candidateVar member
  cases reduction with
  | capAny =>
      simpa [unificationVars, Equation.unificationVars,
        Cap.unificationVars] using member
  | capVarRefl =>
      simp [unificationVars, Equation.unificationVars,
        Cap.unificationVars, member]
  | capVarLeft notOccurs =>
      rcases mem_unificationVars_map_apply_singleCap
          candidateVar _ _ _ member with original | introduced
      · simp [unificationVars, Equation.unificationVars,
          Cap.unificationVars, original]
      · simp [unificationVars, Equation.unificationVars,
          Cap.unificationVars, introduced]
  | capVarRight notOccurs =>
      rcases mem_unificationVars_map_apply_singleCap
          candidateVar _ _ _ member with original | introduced
      · simp [unificationVars, Equation.unificationVars,
          Cap.unificationVars, original]
      · simp [unificationVars, Equation.unificationVars,
          Cap.unificationVars, introduced]
  | capProd paired =>
      simp only [unificationVars_append, List.mem_append] at member
      rcases member with child | rest
      · rcases capEquations_mem_unificationVars paired candidateVar child with
            inLeft | inRight
        · simp [unificationVars, Equation.unificationVars,
            Cap.unificationVars, inLeft]
        · simp [unificationVars, Equation.unificationVars,
            Cap.unificationVars, inRight]
      · simp [unificationVars, Equation.unificationVars,
          Cap.unificationVars, rest]
  | capCon paired =>
      simp only [unificationVars_append, List.mem_append] at member
      rcases member with child | rest
      · rcases capEquations_mem_unificationVars paired candidateVar child with
            inLeft | inRight
        · simp [unificationVars, Equation.unificationVars,
            Cap.unificationVars, inLeft]
        · simp [unificationVars, Equation.unificationVars,
            Cap.unificationVars, inRight]
      · simp [unificationVars, Equation.unificationVars,
          Cap.unificationVars, rest]
  | tyVarRefl =>
      simp [unificationVars, Equation.unificationVars,
        Ty.unificationVars, member]
  | tyVarLeft notOccurs =>
      rcases mem_unificationVars_map_apply_singleTy
          candidateVar _ _ _ member with original | introduced
      · simp [unificationVars, Equation.unificationVars,
          Ty.unificationVars, original]
      · simp [unificationVars, Equation.unificationVars,
          Ty.unificationVars, introduced]
  | tyVarRight notOccurs =>
      rcases mem_unificationVars_map_apply_singleTy
          candidateVar _ _ _ member with original | introduced
      · simp [unificationVars, Equation.unificationVars,
          Ty.unificationVars, original]
      · simp [unificationVars, Equation.unificationVars,
          Ty.unificationVars, introduced]
  | tyInt =>
      simpa [unificationVars, Equation.unificationVars,
        Ty.unificationVars] using member
  | tyFn =>
      simpa [unificationVars, Equation.unificationVars,
        Ty.unificationVars, List.append_assoc, or_comm, or_left_comm,
        or_assoc] using member
  | tyProd paired =>
      simp only [unificationVars_append, List.mem_append] at member
      rcases member with child | rest
      · rcases tyEquations_mem_unificationVars paired candidateVar child with
            inLeft | inRight
        · simp [unificationVars, Equation.unificationVars,
            Ty.unificationVars, inLeft]
        · simp [unificationVars, Equation.unificationVars,
            Ty.unificationVars, inRight]
      · simp [unificationVars, Equation.unificationVars,
          Ty.unificationVars, rest]
  | tyData paired =>
      simp only [unificationVars_append, List.mem_append] at member
      rcases member with child | rest
      · rcases tyEquations_mem_unificationVars paired candidateVar child with
            inLeft | inRight
        · simp [unificationVars, Equation.unificationVars,
            Ty.unificationVars, inLeft]
        · simp [unificationVars, Equation.unificationVars,
            Ty.unificationVars, inRight]
      · simp [unificationVars, Equation.unificationVars,
          Ty.unificationVars, rest]
  | tyMatcher =>
      simpa [unificationVars, Equation.unificationVars,
        Ty.unificationVars, List.append_assoc, or_comm, or_left_comm,
        or_assoc] using member
  | tySlot =>
      simpa [unificationVars, Equation.unificationVars,
        Ty.unificationVars, List.append_assoc, or_comm, or_left_comm,
        or_assoc] using member

/-- The variable eliminated by a successful step, if that step is an
elimination rather than a constructor decomposition. -/
def eliminatedVariable? : List Equation → Option UnificationVar
  | .cap (.var left) (.var right) :: _ =>
      if left = right then none else some (.cap left)
  | .cap (.var index) _ :: _ => some (.cap index)
  | .cap _ (.var index) :: _ => some (.cap index)
  | .ty (.var left) (.var right) :: _ =>
      if left = right then none else some (.ty left)
  | .ty (.var index) _ :: _ => some (.ty index)
  | .ty _ (.var index) :: _ => some (.ty index)
  | _ => none

theorem Equation.cap_not_mem_unificationVars_apply_singleCap
    (index : CapVar) (replacement : Cap)
    (notOccurs : replacement.occurs index = false)
    (equation : Equation) :
    .cap index ∉
      (equation.apply (Subst.singleCap index replacement)).unificationVars := by
  cases equation with
  | cap left right =>
      simp [Equation.apply, Equation.unificationVars,
        Cap.occurs_apply_singleCap_eq_false index replacement left notOccurs,
        Cap.occurs_apply_singleCap_eq_false index replacement right notOccurs]
  | ty left right =>
      simp [Equation.apply, Equation.unificationVars,
        Ty.occursCap_apply_singleCap_eq_false index replacement left notOccurs,
        Ty.occursCap_apply_singleCap_eq_false index replacement right notOccurs]

theorem Equation.ty_not_mem_unificationVars_apply_singleTy
    (index : TyVar) (replacement : Ty)
    (notOccurs : replacement.occursTy index = false)
    (equation : Equation) :
    .ty index ∉
      (equation.apply (Subst.singleTy index replacement)).unificationVars := by
  cases equation with
  | cap left right =>
      simp [Equation.apply, Equation.unificationVars]
  | ty left right =>
      simp [Equation.apply, Equation.unificationVars,
        Ty.occursTy_apply_singleTy_eq_false index replacement left notOccurs,
        Ty.occursTy_apply_singleTy_eq_false index replacement right notOccurs]

theorem cap_not_mem_unificationVars_map_apply_singleCap
    (index : CapVar) (replacement : Cap)
    (notOccurs : replacement.occurs index = false)
    (equations : List Equation) :
    .cap index ∉ unificationVars
      (equations.map (Equation.apply (Subst.singleCap index replacement))) := by
  induction equations with
  | nil => simp [unificationVars]
  | cons equation equations induction =>
      simp [unificationVars,
        Equation.cap_not_mem_unificationVars_apply_singleCap
          index replacement notOccurs equation,
        induction]

theorem ty_not_mem_unificationVars_map_apply_singleTy
    (index : TyVar) (replacement : Ty)
    (notOccurs : replacement.occursTy index = false)
    (equations : List Equation) :
    .ty index ∉ unificationVars
      (equations.map (Equation.apply (Subst.singleTy index replacement))) := by
  induction equations with
  | nil => simp [unificationVars]
  | cons equation equations induction =>
      simp [unificationVars,
        Equation.ty_not_mem_unificationVars_apply_singleTy
          index replacement notOccurs equation,
        induction]

theorem Cap.occurs_var_eq_false_of_ne
    (left right : CapVar) (different : left ≠ right) :
    (Cap.var right).occurs left = false := by
  have reverse : right ≠ left := fun equality => different equality.symm
  simp [Cap.occurs, reverse]

theorem Ty.occursTy_var_eq_false_of_ne
    (left right : TyVar) (different : left ≠ right) :
    (Ty.var right).occursTy left = false := by
  have reverse : right ≠ left := fun equality => different equality.symm
  simp [Ty.occursTy, reverse]

theorem bool_eq_false_of_not_true {value : Bool}
    (notTrue : ¬ value = true) : value = false := by
  cases value <;> simp_all

/-- If the classifier reports an elimination, that variable occurs in the
current worklist. -/
theorem eliminatedVariable_mem_unificationVars
    {input : List Equation} {eliminated : UnificationVar}
    (classified : eliminatedVariable? input = some eliminated) :
    eliminated ∈ unificationVars input := by
  cases input with
  | nil => simp [eliminatedVariable?] at classified
  | cons equation equations =>
      cases equation with
      | cap left right =>
          cases left <;> cases right <;>
            simp_all [eliminatedVariable?, unificationVars,
              Equation.unificationVars, Cap.unificationVars]
      | ty left right =>
          cases left <;> cases right <;>
            simp_all [eliminatedVariable?, unificationVars,
              Equation.unificationVars, Ty.unificationVars]

/-- A deterministic elimination removes exactly the variable reported by the
classifier. -/
theorem reduce_eliminated_not_mem_unificationVars
    {input : List Equation} {result : ReductionResult input}
    {eliminated : UnificationVar}
    (computed : reduce input = some result)
    (classified : eliminatedVariable? input = some eliminated) :
    eliminated ∉ unificationVars result.equations := by
  cases input with
  | nil => simp [reduce] at computed
  | cons equation equations =>
      cases equation with
      | cap left right =>
          cases left <;> cases right <;>
            simp only [reduce] at computed
          all_goals try split at computed
          all_goals simp [eliminatedVariable?] at classified
          all_goals try simp at computed
          all_goals try simp_all
          all_goals
            try subst result
            try subst eliminated
            apply cap_not_mem_unificationVars_map_apply_singleCap
            first
            | exact bool_eq_false_of_not_true (by assumption)
            | apply Cap.occurs_var_eq_false_of_ne
              assumption
      | ty left right =>
          cases left <;> cases right <;>
            simp only [reduce] at computed
          all_goals try split at computed
          all_goals simp [eliminatedVariable?] at classified
          all_goals try simp at computed
          all_goals try simp_all
          all_goals
            try subst result
            try subst eliminated
            apply ty_not_mem_unificationVars_map_apply_singleTy
            first
            | exact bool_eq_false_of_not_true (by assumption)
            | apply Ty.occursTy_var_eq_false_of_ne
              assumption

/-- Raw syntax size used between two variable eliminations. -/
def rawNodeCount (equations : List Equation) : Nat :=
  solvedNodeCount Subst.id equations

/-- Constructor decomposition strictly decreases raw syntax size.  The
classifier hypothesis rules out the variable-elimination constructors. -/
theorem Reduces.rawNodeCount_lt_of_no_elimination
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining)
    (classified : eliminatedVariable? input = none) :
    rawNodeCount remaining < rawNodeCount input := by
  cases reduction with
  | capAny =>
      exact solvedNodeCount_tail_lt Subst.id _ _
  | capVarRefl =>
      exact solvedNodeCount_tail_lt Subst.id _ _
  | capVarLeft notOccurs =>
      rename_i index replacement rest
      cases replacement <;>
        simp_all [eliminatedVariable?, Cap.occurs]
  | capVarRight notOccurs =>
      rename_i index replacement rest
      cases replacement <;>
        simp_all [eliminatedVariable?, Cap.occurs]
  | capProd paired =>
      simp only [rawNodeCount, solvedNodeCount_append, solvedNodeCount,
        Equation.solvedNodeCount, Cap.apply, Cap.nodeCount]
      rw [capEquations_solvedNodeCount paired]
      omega
  | capCon paired =>
      simp only [rawNodeCount, solvedNodeCount_append, solvedNodeCount,
        Equation.solvedNodeCount, Cap.apply, Cap.nodeCount]
      rw [capEquations_solvedNodeCount paired]
      omega
  | tyVarRefl =>
      exact solvedNodeCount_tail_lt Subst.id _ _
  | tyVarLeft notOccurs =>
      rename_i index replacement rest
      cases replacement <;>
        simp_all [eliminatedVariable?, Ty.occursTy]
  | tyVarRight notOccurs =>
      rename_i index replacement rest
      cases replacement <;>
        simp_all [eliminatedVariable?, Ty.occursTy]
  | tyInt =>
      exact solvedNodeCount_tail_lt Subst.id _ _
  | tyFn =>
      simp [rawNodeCount, solvedNodeCount, Equation.solvedNodeCount,
        Ty.apply, Ty.nodeCount]
      omega
  | tyProd paired =>
      simp only [rawNodeCount, solvedNodeCount_append, solvedNodeCount,
        Equation.solvedNodeCount, Ty.apply, Ty.nodeCount]
      rw [tyEquations_solvedNodeCount paired]
      omega
  | tyData paired =>
      simp only [rawNodeCount, solvedNodeCount_append, solvedNodeCount,
        Equation.solvedNodeCount, Ty.apply, Ty.nodeCount]
      rw [tyEquations_solvedNodeCount paired]
      omega
  | tyMatcher =>
      simp [rawNodeCount, solvedNodeCount, Equation.solvedNodeCount,
        Ty.apply, Ty.nodeCount]
      omega
  | tySlot =>
      simp [rawNodeCount, solvedNodeCount, Equation.solvedNodeCount,
        Ty.apply, Ty.nodeCount]
      omega

/-- Every variable in the current worklist is present in the first termination
clock. -/
def VariablesCovered
    (available : List UnificationVar) (equations : List Equation) : Prop :=
  ∀ candidateVar, candidateVar ∈ unificationVars equations →
    candidateVar ∈ available

theorem variablesCovered_initial (equations : List Equation) :
    VariablesCovered (unificationVars equations) equations := by
  intro candidateVar member
  exact member

theorem Reduces.variablesCovered
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining)
    {available : List UnificationVar}
    (covered : VariablesCovered available input) :
    VariablesCovered available remaining := by
  intro candidateVar member
  exact covered candidateVar
    (reduction.unificationVars_subset candidateVar member)

theorem reduction_variablesCovered_erase
    {input : List Equation} {result : ReductionResult input}
    {available : List UnificationVar} {eliminated : UnificationVar}
    (computed : reduce input = some result)
    (classified : eliminatedVariable? input = some eliminated)
    (covered : VariablesCovered available input) :
    VariablesCovered (available.erase eliminated) result.equations := by
  intro candidateVar member
  have inAvailable : candidateVar ∈ available :=
    covered candidateVar
      (result.valid.unificationVars_subset candidateVar member)
  have eliminatedAbsent : eliminated ∉ unificationVars result.equations :=
    reduce_eliminated_not_mem_unificationVars computed classified
  have different : candidateVar ≠ eliminated := by
    intro equality
    subst candidateVar
    exact eliminatedAbsent member
  exact (List.mem_erase_of_ne different).mpr inAvailable

/-- Total executable driver.  Its first clock decreases at variable
eliminations; its second clock decreases at constructor decompositions and is
reset after an elimination. -/
def unifyLoop : List UnificationVar → Nat → List Equation → Option Subst
  | _, _, [] => some Subst.id
  | _, 0, _ :: _ => none
  | available, structuralFuel + 1, equations =>
      match _reduction : reduce equations with
      | none => none
      | some reduced =>
          let later :=
            match eliminatedVariable? equations with
            | some eliminated =>
                if _present : eliminated ∈ available then
                  unifyLoop (available.erase eliminated)
                    (rawNodeCount reduced.equations) reduced.equations
                else none
            | none =>
                unifyLoop available structuralFuel reduced.equations
          later.map (fun substitution =>
            Subst.compose substitution reduced.substitution)
termination_by available structuralFuel _equations =>
  (available.length, structuralFuel)
decreasing_by
  · apply Prod.Lex.left _ _
    rw [List.length_erase, if_pos _present]
    have positive : 0 < available.length := by
      cases available with
      | nil => simp at _present
      | cons head tail => simp
    omega
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)

/-- Fuel-free executable hard unification. -/
def unify (equations : List Equation) : Option Subst :=
  unifyLoop (unificationVars equations) (rawNodeCount equations) equations

/-- With all current variables covered and enough structural clock, every
solvable worklist succeeds. -/
theorem unifyLoop_complete
    {available : List UnificationVar} {structuralFuel : Nat}
    {equations : List Equation}
    (covered : VariablesCovered available equations)
    (bounded : rawNodeCount equations ≤ structuralFuel)
    (solvable : ∃ solution, Solves solution equations) :
    ∃ result, unifyLoop available structuralFuel equations = some result := by
  apply unifyLoop.induct
    (motive := fun available structuralFuel equations =>
      VariablesCovered available equations →
        rawNodeCount equations ≤ structuralFuel →
          (∃ solution, Solves solution equations) →
            ∃ result,
              unifyLoop available structuralFuel equations = some result)
  · intro available structuralFuel covered bounded solvable
    refine ⟨Subst.id, ?_⟩
    rw [unifyLoop.eq_def]
  · intro available equation equations covered bounded solvable
    have positive := Equation.solvedNodeCount_pos Subst.id equation
    simp only [rawNodeCount, solvedNodeCount] at bounded
    omega
  · intro available structuralFuel equations nonempty failed
      covered bounded solvable
    obtain ⟨solution, solved⟩ := solvable
    cases equations with
    | nil => exact False.elim (nonempty rfl)
    | cons equation equations =>
        obtain ⟨result, success⟩ := reduce_some_of_solves solved
        rw [failed] at success
        cases success
  · intro available structuralFuel equations nonempty reduced computed
      eliminationIH structuralIH covered bounded solvable
    obtain ⟨solution, solved⟩ := solvable
    have remainingSolved : Solves solution reduced.equations :=
      reduced.valid.complete solved
    cases classified : eliminatedVariable? equations with
    | some eliminated =>
        have present : eliminated ∈ available :=
          covered eliminated
            (eliminatedVariable_mem_unificationVars classified)
        have remainingCovered :
            VariablesCovered (available.erase eliminated) reduced.equations :=
          reduction_variablesCovered_erase computed classified covered
        obtain ⟨later, recursive⟩ :=
          eliminationIH eliminated present remainingCovered
            (Nat.le_refl _) ⟨solution, remainingSolved⟩
        refine ⟨Subst.compose later reduced.substitution, ?_⟩
        cases equations with
        | nil => exact False.elim (nonempty rfl)
        | cons equation equations =>
            rw [unifyLoop.eq_def]
            dsimp only
            rw [computed]
            simp [classified, present, recursive]
    | none =>
        have remainingCovered :
            VariablesCovered available reduced.equations :=
          reduced.valid.variablesCovered covered
        have decreases :
            rawNodeCount reduced.equations < rawNodeCount equations :=
          reduced.valid.rawNodeCount_lt_of_no_elimination classified
        have remainingBounded :
            rawNodeCount reduced.equations ≤ structuralFuel := by
          omega
        obtain ⟨later, recursive⟩ :=
          structuralIH remainingCovered remainingBounded
            ⟨solution, remainingSolved⟩
        refine ⟨Subst.compose later reduced.substitution, ?_⟩
        cases equations with
        | nil => exact False.elim (nonempty rfl)
        | cons equation equations =>
            rw [unifyLoop.eq_def]
            dsimp only
            rw [computed]
            simp [classified, recursive]
  · exact covered
  · exact bounded
  · exact solvable

/-- Every successful two-clock run is the same result as some ordinary
fuel-bounded run. -/
theorem unifyLoop_success_has_fuel
    {available : List UnificationVar} {structuralFuel : Nat}
    {equations : List Equation} {result : Subst}
    (success : unifyLoop available structuralFuel equations = some result) :
    ∃ fuel, unifyWithFuel fuel equations = some result := by
  refine unifyLoop.induct
    (motive := fun available structuralFuel equations =>
      ∀ result, unifyLoop available structuralFuel equations = some result →
        ∃ fuel, unifyWithFuel fuel equations = some result)
    ?_ ?_ ?_ ?_ available structuralFuel equations result success
  · intro available structuralFuel result success
    rw [unifyLoop.eq_def] at success
    dsimp only at success
    simp only [Option.some.injEq] at success
    subst result
    exact ⟨0, rfl⟩
  · intro available equation equations result success
    rw [unifyLoop.eq_def] at success
    cases success
  · intro available structuralFuel equations nonempty failed result success
    cases equations with
    | nil => exact False.elim (nonempty rfl)
    | cons equation equations =>
        rw [unifyLoop.eq_def] at success
        dsimp only at success
        rw [failed] at success
        cases success
  · intro available structuralFuel equations nonempty reduced computed
      eliminationIH structuralIH result success
    cases equations with
    | nil => exact False.elim (nonempty rfl)
    | cons equation equations =>
        rw [unifyLoop.eq_def] at success
        dsimp only at success
        rw [computed] at success
        cases classified : eliminatedVariable? (equation :: equations) with
        | some eliminated =>
            by_cases present : eliminated ∈ available
            · cases recursive : unifyLoop (available.erase eliminated)
                  (rawNodeCount reduced.equations) reduced.equations with
              | none => simp [classified, present, recursive] at success
              | some later =>
                  obtain ⟨fuel, fuelSuccess⟩ :=
                    eliminationIH eliminated present later recursive
                  simp [classified, present, recursive] at success
                  subst result
                  refine ⟨fuel + 1, ?_⟩
                  simp only [unifyWithFuel]
                  rw [computed]
                  dsimp only
                  rw [fuelSuccess]
            · simp [classified, present] at success
        | none =>
            cases recursive : unifyLoop available structuralFuel
                reduced.equations with
            | none => simp [classified, recursive] at success
            | some later =>
                obtain ⟨fuel, fuelSuccess⟩ := structuralIH later recursive
                simp [classified, recursive] at success
                subst result
                refine ⟨fuel + 1, ?_⟩
                simp only [unifyWithFuel]
                rw [computed]
                dsimp only
                rw [fuelSuccess]

/-- Every solvable hard worklist succeeds under the public executable
unifier. -/
theorem unify_complete
    {equations : List Equation}
    (solvable : ∃ solution, Solves solution equations) :
    ∃ result, unify equations = some result := by
  exact unifyLoop_complete (variablesCovered_initial equations)
    (Nat.le_refl _) solvable

/-- A successful public unification result solves every input equation. -/
theorem unify_sound
    {equations : List Equation} {result : Subst}
    (success : unify equations = some result) :
    Solves result equations := by
  change unifyLoop (unificationVars equations) (rawNodeCount equations)
    equations = some result at success
  obtain ⟨fuel, fuelSuccess⟩ := unifyLoop_success_has_fuel success
  exact unifyWithFuel_sound fuelSuccess

/-- Every successful public unification result is a most general unifier. -/
theorem unify_mostGeneral
    {equations : List Equation} {result : Subst}
    (success : unify equations = some result) :
    MostGeneral equations result := by
  change unifyLoop (unificationVars equations) (rawNodeCount equations)
    equations = some result at success
  obtain ⟨fuel, fuelSuccess⟩ := unifyLoop_success_has_fuel success
  exact unifyWithFuel_mostGeneral fuelSuccess

/-- The public unifier returns `none` exactly for unsatisfiable worklists. -/
theorem unify_none_iff_unsatisfiable (equations : List Equation) :
    unify equations = none ↔
      ¬ ∃ solution, Solves solution equations := by
  constructor
  · intro failed solvable
    obtain ⟨result, success⟩ := unify_complete solvable
    rw [failed] at success
    cases success
  · intro unsatisfiable
    cases computed : unify equations with
    | none => rfl
    | some result =>
        exact False.elim
          (unsatisfiable ⟨result, unify_sound computed⟩)

end TypePM
