import TypePM.ContextInterface

/-!
# Transport laws for bound-index source schemes

Bound positions make substitution transport literal equality.  This
module records the algebraic laws needed to compare nested source blocks
without choosing names for quantified variables.
-/

namespace TypePM.Source

mutual

@[simp] theorem PolyCap.ofCap_applyFree
    (substitution : Subst) (capability : Cap) :
    (PolyCap.ofCap capability).applyFree substitution.cap =
      PolyCap.ofCap (capability.apply substitution.cap) := by
  cases capability with
  | any => rfl
  | var => rfl
  | prod items =>
      simp [PolyCap.ofCap, PolyCap.applyFree, Cap.apply,
        PolyCap.ofCapList_applyFree]

@[simp] theorem PolyCap.ofCapList_applyFree
    (substitution : Subst) (items : List Cap) :
    PolyCap.applyFreeList substitution.cap (PolyCap.ofCapList items) =
      PolyCap.ofCapList (Cap.applyList substitution.cap items) := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.ofCapList, PolyCap.applyFreeList, Cap.applyList,
        PolyCap.ofCap_applyFree, PolyCap.ofCapList_applyFree]

end

mutual

@[simp] theorem PolyTy.ofTy_applyFree
    (substitution : Subst) (target : Ty) :
    (PolyTy.ofTy target).applyFree substitution =
      PolyTy.ofTy (target.apply substitution) := by
  cases target with
  | var => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.ofTy, PolyTy.applyFree, Ty.apply,
        PolyTy.ofTy_applyFree]
  | prod items =>
      simp [PolyTy.ofTy, PolyTy.applyFree, Ty.apply,
        PolyTy.ofTyList_applyFree]
  | matcher capability target =>
      simp [PolyTy.ofTy, PolyTy.applyFree, Ty.apply,
        PolyTy.ofTy_applyFree]
  | slot capability target =>
      simp [PolyTy.ofTy, PolyTy.applyFree, Ty.apply,
        PolyTy.ofTy_applyFree]

@[simp] theorem PolyTy.ofTyList_applyFree
    (substitution : Subst) (items : List Ty) :
    PolyTy.applyFreeList substitution (PolyTy.ofTyList items) =
      PolyTy.ofTyList (Ty.applyList substitution items) := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.ofTyList, PolyTy.applyFreeList, Ty.applyList,
        PolyTy.ofTy_applyFree, PolyTy.ofTyList_applyFree]

end


mutual

@[simp] theorem PolyCap.applyFree_compose
    (later earlier : Subst) (capability : PolyCap) :
    (capability.applyFree earlier.cap).applyFree later.cap =
      capability.applyFree (Subst.compose later earlier).cap := by
  cases capability with
  | any => rfl
  | free index =>
      simp [PolyCap.applyFree, Subst.compose]
  | bound index => rfl
  | prod items =>
      simp [PolyCap.applyFree, PolyCap.applyFreeList_compose]

@[simp] theorem PolyCap.applyFreeList_compose
    (later earlier : Subst) (items : List PolyCap) :
    PolyCap.applyFreeList later.cap
        (PolyCap.applyFreeList earlier.cap items) =
      PolyCap.applyFreeList (Subst.compose later earlier).cap items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.applyFreeList, PolyCap.applyFree_compose,
        PolyCap.applyFreeList_compose]

end


mutual

@[simp] theorem PolyTy.applyFree_compose
    (later earlier : Subst) (target : PolyTy) :
    (target.applyFree earlier).applyFree later =
      target.applyFree (Subst.compose later earlier) := by
  cases target with
  | free index =>
      simp [PolyTy.applyFree, Subst.compose]
  | bound index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.applyFree, PolyTy.applyFree_compose]
  | prod items =>
      simp [PolyTy.applyFree, PolyTy.applyFreeList_compose]
  | matcher capability target =>
      simp [PolyTy.applyFree, PolyTy.applyFree_compose,
        PolyCap.applyFree_compose]
  | slot capability target =>
      simp [PolyTy.applyFree, PolyTy.applyFree_compose,
        PolyCap.applyFree_compose]

@[simp] theorem PolyTy.applyFreeList_compose
    (later earlier : Subst) (items : List PolyTy) :
    PolyTy.applyFreeList later (PolyTy.applyFreeList earlier items) =
      PolyTy.applyFreeList (Subst.compose later earlier) items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.applyFreeList, PolyTy.applyFree_compose,
        PolyTy.applyFreeList_compose]

end


mutual

/-- Opening after transporting free names is the same as opening first and
transporting both the result and the chosen bound instances. -/
theorem PolyCap.openBound_applyFree
    (substitution : Subst) (boundCap : Nat → Cap)
    (capability : PolyCap) :
    (capability.applyFree substitution.cap).openBound
        (fun index => (boundCap index).apply substitution.cap) =
      (capability.openBound boundCap).apply substitution.cap := by
  cases capability with
  | any => rfl
  | free index =>
      change
        (PolyCap.ofCap (substitution.cap index)).openBound _ =
          substitution.cap index
      exact PolyCap.ofCap_open _ _
  | bound index => rfl
  | prod items =>
      simp [PolyCap.applyFree, PolyCap.openBound, Cap.apply,
        PolyCap.openBoundList_applyFree]

theorem PolyCap.openBoundList_applyFree
    (substitution : Subst) (boundCap : Nat → Cap)
    (items : List PolyCap) :
    PolyCap.openBoundList
        (fun index => (boundCap index).apply substitution.cap)
        (PolyCap.applyFreeList substitution.cap items) =
      Cap.applyList substitution.cap
        (PolyCap.openBoundList boundCap items) := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.openBoundList, PolyCap.applyFreeList, Cap.applyList,
        PolyCap.openBound_applyFree, PolyCap.openBoundList_applyFree]

end


mutual

theorem PolyTy.openBound_applyFree
    (substitution : Subst) (boundTy : Nat → Ty)
    (boundCap : Nat → Cap) (target : PolyTy) :
    (target.applyFree substitution).openBound
        (fun index => (boundTy index).apply substitution)
        (fun index => (boundCap index).apply substitution.cap) =
      (target.openBound boundTy boundCap).apply substitution := by
  cases target with
  | free index =>
      change
        (PolyTy.ofTy (substitution.ty index)).openBound _ _ =
          substitution.ty index
      exact PolyTy.ofTy_open _ _ _
  | bound index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.applyFree, PolyTy.openBound, Ty.apply,
        PolyTy.openBound_applyFree]
  | prod items =>
      simp [PolyTy.applyFree, PolyTy.openBound, Ty.apply,
        PolyTy.openBoundList_applyFree]
  | matcher capability target =>
      simp [PolyTy.applyFree, PolyTy.openBound, Ty.apply,
        PolyTy.openBound_applyFree, PolyCap.openBound_applyFree]
  | slot capability target =>
      simp [PolyTy.applyFree, PolyTy.openBound, Ty.apply,
        PolyTy.openBound_applyFree, PolyCap.openBound_applyFree]

theorem PolyTy.openBoundList_applyFree
    (substitution : Subst) (boundTy : Nat → Ty)
    (boundCap : Nat → Cap) (items : List PolyTy) :
    PolyTy.openBoundList
        (fun index => (boundTy index).apply substitution)
        (fun index => (boundCap index).apply substitution.cap)
        (PolyTy.applyFreeList substitution items) =
      Ty.applyList substitution
        (PolyTy.openBoundList boundTy boundCap items) := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.openBoundList, PolyTy.applyFreeList, Ty.applyList,
        PolyTy.openBound_applyFree, PolyTy.openBoundList_applyFree]

end


mutual

/-- Free-name substitution is extensional on the finite free-variable set of
a bound-index capability body. -/
theorem PolyCap.applyFree_eq_of_agree
    {left right : CapSubst} {capability : PolyCap}
    (agree : ∀ index ∈ capability.freeCapVars,
      left index = right index) :
    capability.applyFree left = capability.applyFree right := by
  cases capability with
  | any => rfl
  | free index =>
      simp only [PolyCap.applyFree]
      rw [agree index (by simp [PolyCap.freeCapVars])]
  | bound index => rfl
  | prod items =>
      simp only [PolyCap.applyFree]
      apply congrArg PolyCap.prod
      exact PolyCap.applyFreeList_eq_of_agree agree

theorem PolyCap.applyFreeList_eq_of_agree
    {left right : CapSubst} {items : List PolyCap}
    (agree : ∀ index ∈ PolyCap.freeCapVarsList items,
      left index = right index) :
    PolyCap.applyFreeList left items = PolyCap.applyFreeList right items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [PolyCap.applyFreeList]
      have headEquality :
          item.applyFree left = item.applyFree right := by
        apply PolyCap.applyFree_eq_of_agree
        intro index membership
        exact agree index (by
          simp [PolyCap.freeCapVarsList, membership])
      have tailEquality :
          PolyCap.applyFreeList left items =
            PolyCap.applyFreeList right items := by
        apply PolyCap.applyFreeList_eq_of_agree
        intro index membership
        exact agree index (by
          simp [PolyCap.freeCapVarsList, membership])
      rw [headEquality, tailEquality]

end


mutual

/-- Free-name substitution is extensional on both finite free-variable sets
of a bound-index type body. -/
theorem PolyTy.applyFree_eq_of_agree
    {left right : Subst} {target : PolyTy}
    (tyAgree : ∀ index ∈ target.freeTyVars,
      left.ty index = right.ty index)
    (capAgree : ∀ index ∈ target.freeCapVars,
      left.cap index = right.cap index) :
    target.applyFree left = target.applyFree right := by
  cases target with
  | free index =>
      simp only [PolyTy.applyFree]
      rw [tyAgree index (by simp [PolyTy.freeTyVars])]
  | bound index => rfl
  | int => rfl
  | fn domain codomain =>
      simp only [PolyTy.applyFree]
      have domainEquality :
          domain.applyFree left = domain.applyFree right := by
        apply PolyTy.applyFree_eq_of_agree
        · intro index membership
          exact tyAgree index (by
            simp [PolyTy.freeTyVars, membership])
        · intro index membership
          exact capAgree index (by
            simp [PolyTy.freeCapVars, membership])
      have codomainEquality :
          codomain.applyFree left = codomain.applyFree right := by
        apply PolyTy.applyFree_eq_of_agree
        · intro index membership
          exact tyAgree index (by
            simp [PolyTy.freeTyVars, membership])
        · intro index membership
          exact capAgree index (by
            simp [PolyTy.freeCapVars, membership])
      rw [domainEquality, codomainEquality]
  | prod items =>
      simp only [PolyTy.applyFree]
      apply congrArg PolyTy.prod
      exact PolyTy.applyFreeList_eq_of_agree tyAgree capAgree
  | matcher capability target =>
      simp only [PolyTy.applyFree]
      have capabilityEquality :
          capability.applyFree left.cap =
            capability.applyFree right.cap := by
        apply PolyCap.applyFree_eq_of_agree
        intro index membership
        exact capAgree index (by
          simp [PolyTy.freeCapVars, membership])
      have targetEquality :
          target.applyFree left = target.applyFree right := by
        apply PolyTy.applyFree_eq_of_agree
        · exact tyAgree
        · intro index membership
          exact capAgree index (by
            simp [PolyTy.freeCapVars, membership])
      rw [capabilityEquality, targetEquality]
  | slot capability target =>
      simp only [PolyTy.applyFree]
      have capabilityEquality :
          capability.applyFree left.cap =
            capability.applyFree right.cap := by
        apply PolyCap.applyFree_eq_of_agree
        intro index membership
        exact capAgree index (by
          simp [PolyTy.freeCapVars, membership])
      have targetEquality :
          target.applyFree left = target.applyFree right := by
        apply PolyTy.applyFree_eq_of_agree
        · exact tyAgree
        · intro index membership
          exact capAgree index (by
            simp [PolyTy.freeCapVars, membership])
      rw [capabilityEquality, targetEquality]

theorem PolyTy.applyFreeList_eq_of_agree
    {left right : Subst} {items : List PolyTy}
    (tyAgree : ∀ index ∈ PolyTy.freeTyVarsList items,
      left.ty index = right.ty index)
    (capAgree : ∀ index ∈ PolyTy.freeCapVarsList items,
      left.cap index = right.cap index) :
    PolyTy.applyFreeList left items = PolyTy.applyFreeList right items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [PolyTy.applyFreeList]
      have headEquality :
          item.applyFree left = item.applyFree right := by
        apply PolyTy.applyFree_eq_of_agree
        · intro index membership
          exact tyAgree index (by
            simp [PolyTy.freeTyVarsList, membership])
        · intro index membership
          exact capAgree index (by
            simp [PolyTy.freeCapVarsList, membership])
      have tailEquality :
          PolyTy.applyFreeList left items =
            PolyTy.applyFreeList right items := by
        apply PolyTy.applyFreeList_eq_of_agree
        · intro index membership
          exact tyAgree index (by
            simp [PolyTy.freeTyVarsList, membership])
        · intro index membership
          exact capAgree index (by
            simp [PolyTy.freeCapVarsList, membership])
      rw [headEquality, tailEquality]

end


namespace Scheme

/-- The proof of scope correctness does not affect scheme equality. -/
theorem eq_of_fields
    {left right : Scheme}
    (tyArityEquality : left.tyArity = right.tyArity)
    (capArityEquality : left.capArity = right.capArity)
    (bodyEquality : left.body = right.body) :
    left = right := by
  cases left with
  | mk leftTy leftCap leftBody leftScoped =>
      cases right with
      | mk rightTy rightCap rightBody rightScoped =>
          simp only at tyArityEquality capArityEquality bodyEquality
          subst rightTy
          subst rightCap
          subst rightBody
          rfl

@[simp] theorem applyFree_compose
    (later earlier : Subst) (scheme : Scheme) :
    (scheme.applyFree earlier).applyFree later =
      scheme.applyFree (Subst.compose later earlier) := by
  cases scheme
  simp [Scheme.applyFree]

/-- Substitution transport preserves declarative scheme instantiation. -/
theorem Instantiates.applyFree
    {scheme : Scheme} {target : Ty} (instantiation : scheme.Instantiates target)
    (substitution : Subst) :
    (scheme.applyFree substitution).Instantiates
      (target.apply substitution) := by
  rcases instantiation with ⟨boundTy, boundCap, rfl⟩
  refine ⟨fun index => (boundTy index).apply substitution,
    fun index => (boundCap index).apply substitution.cap, ?_⟩
  exact (PolyTy.openBound_applyFree substitution boundTy boundCap
    scheme.body).symm

theorem applyFree_eq_of_agree
    {left right : Subst} {scheme : Scheme}
    (tyAgree : ∀ index ∈ scheme.freeTyVars,
      left.ty index = right.ty index)
    (capAgree : ∀ index ∈ scheme.freeCapVars,
      left.cap index = right.cap index) :
    scheme.applyFree left = scheme.applyFree right := by
  cases scheme with
  | mk tyArity capArity body wellScoped =>
      simp only [Scheme.applyFree]
      have bodyEquality :
          body.applyFree left = body.applyFree right := by
        apply PolyTy.applyFree_eq_of_agree
        · intro index membership
          exact tyAgree index (Scheme.mem_freeTyVars.mpr membership)
        · intro index membership
          exact capAgree index (Scheme.mem_freeCapVars.mpr membership)
      exact Scheme.eq_of_fields rfl rfl bodyEquality

end Scheme


namespace Supply

/-- A substitution fixes the infinite fresh-name streams beginning at this
supply.  Completeness proofs use this condition when transporting an
executable bound-index instantiation through a substitution whose support lies
strictly below the current supply. -/
def FixedBy (supply : Supply) (substitution : Subst) : Prop :=
  (∀ offset,
      substitution.ty ⟨supply.ty + offset⟩ =
        .var ⟨supply.ty + offset⟩) ∧
    (∀ offset,
      substitution.cap ⟨supply.cap + offset⟩ =
        .var ⟨supply.cap + offset⟩)

@[simp] theorem fixedBy_id (supply : Supply) :
    supply.FixedBy Subst.id := by
  constructor <;> intro offset <;> rfl

end Supply


namespace Scheme

/-- Applying a substitution to free names commutes with the executable fresh
instantiation when that substitution leaves the fresh streams untouched. -/
theorem instantiate_applyFree_of_fixed
    (scheme : Scheme) (supply : Supply) (substitution : Subst)
    (fixed : supply.FixedBy substitution) :
    (scheme.applyFree substitution).instantiate supply =
      ((scheme.instantiate supply).1.apply substitution,
        (scheme.instantiate supply).2) := by
  apply Prod.ext
  · change
      (scheme.body.applyFree substitution).openBound
          (fun position => .var (Scheme.boundTyInstance supply position))
          (fun position => .var (Scheme.boundCapInstance supply position)) =
        (scheme.body.openBound
          (fun position => .var (Scheme.boundTyInstance supply position))
          (fun position => .var (Scheme.boundCapInstance supply position))).apply
            substitution
    have transported := PolyTy.openBound_applyFree substitution
      (fun position => .var (Scheme.boundTyInstance supply position))
      (fun position => .var (Scheme.boundCapInstance supply position))
      scheme.body
    have tyFixed :
        (fun position =>
          (Ty.var (Scheme.boundTyInstance supply position)).apply substitution) =
          (fun position =>
            Ty.var (Scheme.boundTyInstance supply position)) := by
      funext position
      exact fixed.1 position
    have capFixed :
        (fun position =>
          (Cap.var (Scheme.boundCapInstance supply position)).apply
            substitution.cap) =
          (fun position =>
            Cap.var (Scheme.boundCapInstance supply position)) := by
      funext position
      exact fixed.2 position
    rw [tyFixed, capFixed] at transported
    exact transported
  · rfl

end Scheme


namespace Context

@[simp] theorem applyFree_id (context : Context) :
    context.applyFree Subst.id = context := by
  induction context with
  | nil => rfl
  | cons scheme context induction =>
      change
        Scheme.applyFree Subst.id scheme ::
            List.map (Scheme.applyFree Subst.id) context =
          scheme :: context
      rw [Scheme.applyFree_id]
      change List.map (Scheme.applyFree Subst.id) context = context at induction
      rw [induction]

@[simp] theorem applyFree_compose
    (later earlier : Subst) (context : Context) :
    (context.applyFree earlier).applyFree later =
      context.applyFree (Subst.compose later earlier) := by
  simp [Context.applyFree, Scheme.applyFree_compose]

/-- Generalization really quantifies the variables selected by its
first-occurrence lists. -/
theorem generalize_instantiates (context : Context) (target : Ty) :
    (context.generalize target).Instantiates target := by
  exact ⟨tyNameAt (context.generalizedTyVars target),
    capNameAt (context.generalizedCapVars target),
    (context.generalize_open target).symm⟩

/-- Every ordinary type variable in a context is below its context-derived initial
supply. -/
theorem freeTyVar_lt_initialSupply
    {context : Context} {index : TyVar}
    (membership : index ∈ context.freeTyVars) :
    index.index < context.initialSupply.ty := by
  apply TyVar.index_lt_next
  exact mem_dedupFirst.mp membership

/-- Every capability variable in a context is below its context-derived initial
supply. -/
theorem freeCapVar_lt_initialSupply
    {context : Context} {index : CapVar}
    (membership : index ∈ context.freeCapVars) :
    index.index < context.initialSupply.cap := by
  apply CapVar.index_lt_next
  exact mem_dedupFirst.mp membership

/-- Context substitution is extensional on the context's finite interface. -/
theorem applyFree_eq_of_substitutionsAgree
    {context : Context} {left right : Subst}
    (agree : context.SubstitutionsAgree left right) :
    context.applyFree left = context.applyFree right := by
  induction context with
  | nil => rfl
  | cons scheme context induction =>
      simp only [Context.applyFree, List.map_cons]
      have headEquality :
          scheme.applyFree left = scheme.applyFree right := by
        apply Scheme.applyFree_eq_of_agree
        · intro index membership
          apply agree.1 index
          apply mem_dedupFirst.mpr
          exact List.mem_append_left _ membership
        · intro index membership
          apply agree.2 index
          apply mem_dedupFirst.mpr
          exact List.mem_append_left _ membership
      have tailEquality :
          Context.applyFree left context = Context.applyFree right context := by
        apply induction
        constructor
        · intro index membership
          apply agree.1 index
          apply mem_dedupFirst.mpr
          exact List.mem_append_right _
            (mem_dedupFirst.mp membership)
        · intro index membership
          apply agree.2 index
          apply mem_dedupFirst.mpr
          exact List.mem_append_right _
            (mem_dedupFirst.mp membership)
      change
        List.map (Scheme.applyFree left) context =
          List.map (Scheme.applyFree right) context at tailEquality
      rw [headEquality, tailEquality]

/-- Solving a finite let-boundary interface says exactly that substituting the
parent context directly or through the closed child block produces the same
bound-index context. -/
theorem applyFree_interface_transport
    (context : Context) (block later : Subst)
    (solved : Solves later (context.interfaceEquations block)) :
    context.applyFree later =
      (context.applyFree block).applyFree later := by
  have agree : context.SubstitutionsAgree later
      (Subst.compose later block) :=
    (context.solves_interfaceEquations_iff block later).mp solved
  calc
    context.applyFree later =
        context.applyFree (Subst.compose later block) :=
      applyFree_eq_of_substitutionsAgree agree
    _ = (context.applyFree block).applyFree later :=
      (Context.applyFree_compose later block context).symm

end Context

end TypePM.Source
