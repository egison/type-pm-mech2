import TypePM.Source.InterfaceAliasDecomposition

/-!
# Reflection of free substitution through source contexts

Applying two substitutions to a source context is injective on the free
variables that actually occur in that context.  This is the converse, on the
finite observable support, of `Context.applyFree_eq_of_substitutionsAgree`.

The final interface theorem combines that reflection with the two finite
`let` interfaces.  A later substitution which solves both interfaces cannot
distinguish a closed context from its renamed image on any free variable of
that closed context.
-/

namespace TypePM

mutual

/-- Equality after applying two substitutions to a type reflects equality of
their ordinary-variable images at every occurring variable. -/
theorem Ty.apply_eq_implies_ty_eq
    (target : Ty) (left right : Subst)
    (equality : target.apply left = target.apply right) :
    ∀ index, index ∈ target.tyVars → left.ty index = right.ty index := by
  intro index member
  cases target with
  | var source =>
      have indexEq : index = source := by
        simpa [Ty.tyVars] using member
      subst index
      simpa [Ty.apply] using equality
  | int => simp [Ty.tyVars] at member
  | fn domain codomain =>
      have parts := Ty.fn.inj equality
      simp only [Ty.tyVars, List.mem_append] at member
      rcases member with domainMember | codomainMember
      · exact Ty.apply_eq_implies_ty_eq domain left right parts.1 _ domainMember
      · exact Ty.apply_eq_implies_ty_eq codomain left right parts.2 _
          codomainMember
  | prod items =>
      exact Ty.applyList_eq_implies_ty_eq items left right
        (Ty.prod.inj equality) index (by simpa [Ty.tyVars] using member)
  | data former arguments =>
      exact Ty.applyList_eq_implies_ty_eq arguments left right
        (Ty.data.inj equality).2 index (by simpa [Ty.tyVars] using member)
  | matcher capability body =>
      exact Ty.apply_eq_implies_ty_eq body left right
        (Ty.matcher.inj equality).2 index (by simpa [Ty.tyVars] using member)
  | slot capability body =>
      exact Ty.apply_eq_implies_ty_eq body left right
        (Ty.slot.inj equality).2 index (by simpa [Ty.tyVars] using member)

/-- List counterpart of `Ty.apply_eq_implies_ty_eq`. -/
theorem Ty.applyList_eq_implies_ty_eq
    (items : List Ty) (left right : Subst)
    (equality : Ty.applyList left items = Ty.applyList right items) :
    ∀ index, index ∈ Ty.tyVarsList items →
      left.ty index = right.ty index := by
  intro index member
  cases items with
  | nil => simp [Ty.tyVarsList] at member
  | cons item items =>
      have parts := List.cons.inj equality
      simp only [Ty.tyVarsList, List.mem_append] at member
      rcases member with itemMember | itemsMember
      · exact Ty.apply_eq_implies_ty_eq item left right parts.1 index itemMember
      · exact Ty.applyList_eq_implies_ty_eq items left right parts.2 index
          itemsMember

end

mutual

/-- Equality after applying two capability substitutions reflects equality
at every occurring capability variable. -/
theorem Cap.apply_eq_implies_cap_eq
    (capability : Cap) (left right : CapSubst)
    (equality : capability.apply left = capability.apply right) :
    ∀ index, index ∈ capability.capVars → left index = right index := by
  intro index member
  cases capability with
  | any => simp [Cap.capVars] at member
  | var source =>
      have indexEq : index = source := by
        simpa [Cap.capVars] using member
      subst index
      simpa [Cap.apply] using equality
  | prod items =>
      exact Cap.applyList_eq_implies_cap_eq items left right
        (Cap.prod.inj equality) index (by simpa [Cap.capVars] using member)
  | con former arguments =>
      exact Cap.applyList_eq_implies_cap_eq arguments left right
        (Cap.con.inj equality).2 index (by simpa [Cap.capVars] using member)

/-- List counterpart of `Cap.apply_eq_implies_cap_eq`. -/
theorem Cap.applyList_eq_implies_cap_eq
    (items : List Cap) (left right : CapSubst)
    (equality : Cap.applyList left items = Cap.applyList right items) :
    ∀ index, index ∈ Cap.capVarsList items →
      left index = right index := by
  intro index member
  cases items with
  | nil => simp [Cap.capVarsList] at member
  | cons item items =>
      have parts := List.cons.inj equality
      simp only [Cap.capVarsList, List.mem_append] at member
      rcases member with itemMember | itemsMember
      · exact Cap.apply_eq_implies_cap_eq item left right parts.1 index itemMember
      · exact Cap.applyList_eq_implies_cap_eq items left right parts.2 index
          itemsMember

end


mutual

/-- Equality after applying two substitutions to a type reflects equality of
their capability-variable images at every occurring capability variable. -/
theorem Ty.apply_eq_implies_cap_eq
    (target : Ty) (left right : Subst)
    (equality : target.apply left = target.apply right) :
    ∀ index, index ∈ target.capVars → left.cap index = right.cap index := by
  intro index member
  cases target with
  | var source => simp [Ty.capVars] at member
  | int => simp [Ty.capVars] at member
  | fn domain codomain =>
      have parts := Ty.fn.inj equality
      simp only [Ty.capVars, List.mem_append] at member
      rcases member with domainMember | codomainMember
      · exact Ty.apply_eq_implies_cap_eq domain left right parts.1 _ domainMember
      · exact Ty.apply_eq_implies_cap_eq codomain left right parts.2 _
          codomainMember
  | prod items =>
      exact Ty.applyList_eq_implies_cap_eq items left right
        (Ty.prod.inj equality) index (by simpa [Ty.capVars] using member)
  | data former arguments =>
      exact Ty.applyList_eq_implies_cap_eq arguments left right
        (Ty.data.inj equality).2 index (by simpa [Ty.capVars] using member)
  | matcher capability body =>
      have parts := Ty.matcher.inj equality
      simp only [Ty.capVars, List.mem_append] at member
      rcases member with capabilityMember | bodyMember
      · exact Cap.apply_eq_implies_cap_eq capability left.cap right.cap
          parts.1 index capabilityMember
      · exact Ty.apply_eq_implies_cap_eq body left right parts.2 index bodyMember
  | slot capability body =>
      have parts := Ty.slot.inj equality
      simp only [Ty.capVars, List.mem_append] at member
      rcases member with capabilityMember | bodyMember
      · exact Cap.apply_eq_implies_cap_eq capability left.cap right.cap
          parts.1 index capabilityMember
      · exact Ty.apply_eq_implies_cap_eq body left right parts.2 index bodyMember

/-- List counterpart of `Ty.apply_eq_implies_cap_eq`. -/
theorem Ty.applyList_eq_implies_cap_eq
    (items : List Ty) (left right : Subst)
    (equality : Ty.applyList left items = Ty.applyList right items) :
    ∀ index, index ∈ Ty.capVarsList items →
      left.cap index = right.cap index := by
  intro index member
  cases items with
  | nil => simp [Ty.capVarsList] at member
  | cons item items =>
      have parts := List.cons.inj equality
      simp only [Ty.capVarsList, List.mem_append] at member
      rcases member with itemMember | itemsMember
      · exact Ty.apply_eq_implies_cap_eq item left right parts.1 index itemMember
      · exact Ty.applyList_eq_implies_cap_eq items left right parts.2 index
          itemsMember

end


namespace Source

namespace Context

open InterfaceAliasDecomposition

/-- Context substitution equality reflects substitution agreement on the
context's finite free-variable interface. -/
theorem substitutionsAgree_of_applyFree_eq
    {context : Context} {left right : Subst}
    (equality : context.applyFree left = context.applyFree right) :
    context.SubstitutionsAgree left right := by
  have witnessEquality :
      (ObservableSupport.contextWitness context).apply left =
        (ObservableSupport.contextWitness context).apply right := by
    rw [← ObservableSupport.contextWitness_applyFree,
      ← ObservableSupport.contextWitness_applyFree, equality]
  constructor
  · intro index member
    exact Ty.apply_eq_implies_ty_eq
      (ObservableSupport.contextWitness context) left right witnessEquality
      index (ObservableSupport.contextWitness_ty context member)
  · intro index member
    exact Ty.apply_eq_implies_cap_eq
      (ObservableSupport.contextWitness context) left right witnessEquality
      index (ObservableSupport.contextWitness_cap context member)

/-- If one later substitution solves the interfaces of two closure
representatives, exact renaming of their closed contexts becomes pointwise
invisible on every free variable of the left closed context. -/
theorem substitutionsAgree_compose_renaming_of_interfaces
    (context : Context) (leftBlock rightBlock later : Subst)
    (rho : VariableRenaming)
    (leftSolved : Solves later (context.interfaceEquations leftBlock))
    (rightSolved : Solves later (context.interfaceEquations rightBlock))
    (closedExact :
      (context.applyFree leftBlock).applyFree rho.substitution =
        context.applyFree rightBlock) :
    (context.applyFree leftBlock).SubstitutionsAgree later
      (Subst.compose later rho.substitution) := by
  apply substitutionsAgree_of_applyFree_eq
  calc
    (context.applyFree leftBlock).applyFree later =
        context.applyFree later :=
      (context.applyFree_interface_transport leftBlock later leftSolved).symm
    _ = (context.applyFree rightBlock).applyFree later :=
      context.applyFree_interface_transport rightBlock later rightSolved
    _ = ((context.applyFree leftBlock).applyFree
        rho.substitution).applyFree later := by rw [closedExact]
    _ = (context.applyFree leftBlock).applyFree
        (Subst.compose later rho.substitution) := by
      rw [Context.applyFree_compose]

end Context

end Source

end TypePM
