import TypePM.Source.GeneratedAcceptanceTransport
import TypePM.Source.InterfaceAliasCounterexample
import TypePM.Source.SchemeSupportBounds
import TypePM.GeneratedSupport

/-!
# Alias decomposition of representative-sensitive interfaces

Two absorbing principal closures can expose literally different `letE`
interface equations even after their closed contexts have been aligned by a
global two-sort renaming.  The difference is symmetric: either concrete side
may contain a local variable alias while the other contains a reflexive
equation.

This module first separates the equation-list algebra from source freshness.
`EquationCommonCore` records only hard-worklist equivalence after adding two
finite alias sequences to a shared equation list.  Turning that certificate
into `FreshAliasSequence.CommonCoreEquivalent` requires explicit
`Admissible` hypotheses for the body block; no body freshness is inferred from
closure data here.
-/

namespace TypePM.Source.InterfaceAliasDecomposition

/-! ## Support criterion for finite alias freshness

The ordering side condition of `FreshAliasSequence.Admissible` is discharged
once all existing endpoints lie in one common support, all fresh endpoints
lie outside it, and the fresh endpoints are duplicate-free.  This criterion
also covers delayed obligations because `Generated.unificationVars` includes
both sides of every pending obligation. -/

namespace AliasFreshness

open FreshAliasSequence

def freshVariable : Alias → UnificationVar
  | .ty fresh _ => .ty fresh
  | .cap fresh _ => .cap fresh

def existingVariable : Alias → UnificationVar
  | .ty _ existing => .ty existing
  | .cap _ existing => .cap existing

@[simp] theorem freshVariable_ty (fresh existing : TyVar) :
    freshVariable (.ty fresh existing) = .ty fresh := rfl

@[simp] theorem freshVariable_cap (fresh existing : CapVar) :
    freshVariable (.cap fresh existing) = .cap fresh := rfl

@[simp] theorem existingVariable_ty (fresh existing : TyVar) :
    existingVariable (.ty fresh existing) = .ty existing := rfl

@[simp] theorem existingVariable_cap (fresh existing : CapVar) :
    existingVariable (.cap fresh existing) = .cap existing := rfl

/-- A finite alias list is supported by `support` when its fresh endpoints
are distinct and outside `support`, while all existing endpoints are inside
`support`. -/
def ScopedBy (support : List UnificationVar) (aliases : List Alias) : Prop :=
  (aliases.map freshVariable).Nodup ∧
    ∀ alias, alias ∈ aliases →
      freshVariable alias ∉ support ∧ existingVariable alias ∈ support

private theorem Ty.apply_singleTy_eq_self_of_not_mem
    (target : Ty) (fresh existing : TyVar)
    (absent : .ty fresh ∉ target.unificationVars) :
    target.apply (Subst.singleTy fresh (.var existing)) = target := by
  calc
    target.apply (Subst.singleTy fresh (.var existing)) =
        target.apply Subst.id := by
      apply Ty.apply_eq_of_agree target
      · intro index member
        have different : index ≠ fresh := by
          intro equality
          subst index
          exact absent ((Ty.mem_tyVars_iff_unificationVars fresh target).mp
            member)
        simp [Subst.singleTy, Subst.id, different]
      · intro index _member
        rfl
    _ = target := Ty.apply_id target

private theorem Ty.apply_singleCap_eq_self_of_not_mem
    (target : Ty) (fresh existing : CapVar)
    (absent : .cap fresh ∉ target.unificationVars) :
    target.apply (Subst.singleCap fresh (.var existing)) = target := by
  calc
    target.apply (Subst.singleCap fresh (.var existing)) =
        target.apply Subst.id := by
      apply Ty.apply_eq_of_agree target
      · intro index _member
        rfl
      · intro index member
        have different : index ≠ fresh := by
          intro equality
          subst index
          exact absent ((Ty.mem_capVars_iff_unificationVars fresh target).mp
            member)
        simp [Subst.singleCap, Subst.id, different]
    _ = target := Ty.apply_id target

private theorem Cap.apply_singleCap_eq_self_of_not_mem
    (capability : Cap) (fresh existing : CapVar)
    (absent : .cap fresh ∉ capability.unificationVars) :
    capability.apply (Subst.singleCap fresh (.var existing)).cap =
      capability := by
  calc
    capability.apply (Subst.singleCap fresh (.var existing)).cap =
        capability.apply Subst.id.cap := by
      apply Cap.apply_eq_of_agree capability
      intro index member
      have different : index ≠ fresh := by
        intro equality
        subst index
        exact absent
          ((Cap.mem_capVars_iff_unificationVars fresh capability).mp member)
      simp [Subst.singleCap, Subst.id, different]
    _ = capability := Cap.apply_id capability

private theorem Equation.apply_singleTy_eq_self_of_not_mem
    (equation : Equation) (fresh existing : TyVar)
    (absent : .ty fresh ∉ equation.unificationVars) :
    equation.apply (Subst.singleTy fresh (.var existing)) = equation := by
  cases equation with
  | ty left right =>
      have leftAbsent : .ty fresh ∉ left.unificationVars := fun member =>
        absent (List.mem_append_left _ member)
      have rightAbsent : .ty fresh ∉ right.unificationVars := fun member =>
        absent (List.mem_append_right _ member)
      simp [Equation.apply,
        Ty.apply_singleTy_eq_self_of_not_mem left fresh existing leftAbsent,
        Ty.apply_singleTy_eq_self_of_not_mem right fresh existing rightAbsent]
  | cap left right =>
      simp only [Equation.apply]
      congr 1 <;> exact Cap.apply_id _

private theorem Equation.apply_singleCap_eq_self_of_not_mem
    (equation : Equation) (fresh existing : CapVar)
    (absent : .cap fresh ∉ equation.unificationVars) :
    equation.apply (Subst.singleCap fresh (.var existing)) = equation := by
  cases equation with
  | ty left right =>
      have leftAbsent : .cap fresh ∉ left.unificationVars := fun member =>
        absent (List.mem_append_left _ member)
      have rightAbsent : .cap fresh ∉ right.unificationVars := fun member =>
        absent (List.mem_append_right _ member)
      simp [Equation.apply,
        Ty.apply_singleCap_eq_self_of_not_mem left fresh existing leftAbsent,
        Ty.apply_singleCap_eq_self_of_not_mem right fresh existing rightAbsent]
  | cap left right =>
      have leftAbsent : .cap fresh ∉ left.unificationVars := fun member =>
        absent (List.mem_append_left _ member)
      have rightAbsent : .cap fresh ∉ right.unificationVars := fun member =>
        absent (List.mem_append_right _ member)
      simp [Equation.apply,
        Cap.apply_singleCap_eq_self_of_not_mem left fresh existing leftAbsent,
        Cap.apply_singleCap_eq_self_of_not_mem right fresh existing rightAbsent]

private theorem CheckObligation.apply_singleTy_eq_self_of_not_mem
    (obligation : CheckObligation) (fresh existing : TyVar)
    (absent : .ty fresh ∉ obligation.unificationVars) :
    obligation.apply (Subst.singleTy fresh (.var existing)) = obligation := by
  have sourceAbsent : .ty fresh ∉ obligation.source.unificationVars :=
    fun member => absent (List.mem_append_left _ member)
  have expectedAbsent : .ty fresh ∉ obligation.expected.unificationVars :=
    fun member => absent (List.mem_append_right _ member)
  cases obligation
  simp [CheckObligation.apply,
    Ty.apply_singleTy_eq_self_of_not_mem _ fresh existing sourceAbsent,
    Ty.apply_singleTy_eq_self_of_not_mem _ fresh existing expectedAbsent]

private theorem CheckObligation.apply_singleCap_eq_self_of_not_mem
    (obligation : CheckObligation) (fresh existing : CapVar)
    (absent : .cap fresh ∉ obligation.unificationVars) :
    obligation.apply (Subst.singleCap fresh (.var existing)) = obligation := by
  have sourceAbsent : .cap fresh ∉ obligation.source.unificationVars :=
    fun member => absent (List.mem_append_left _ member)
  have expectedAbsent : .cap fresh ∉ obligation.expected.unificationVars :=
    fun member => absent (List.mem_append_right _ member)
  cases obligation
  simp [CheckObligation.apply,
    Ty.apply_singleCap_eq_self_of_not_mem _ fresh existing sourceAbsent,
    Ty.apply_singleCap_eq_self_of_not_mem _ fresh existing expectedAbsent]

private theorem equations_singleTy_fixed
    (equations : List Equation) (fresh existing : TyVar)
    (absent : .ty fresh ∉ TypePM.unificationVars equations) :
    equations.map (Equation.apply (Subst.singleTy fresh (.var existing))) =
      equations := by
  induction equations with
  | nil => rfl
  | cons equation equations induction =>
      have headAbsent : .ty fresh ∉ equation.unificationVars := fun member =>
        absent (List.mem_append_left _ member)
      have tailAbsent : .ty fresh ∉ TypePM.unificationVars equations :=
        fun member => absent (List.mem_append_right _ member)
      simp [Equation.apply_singleTy_eq_self_of_not_mem equation fresh existing
        headAbsent, induction tailAbsent]

private theorem equations_singleCap_fixed
    (equations : List Equation) (fresh existing : CapVar)
    (absent : .cap fresh ∉ TypePM.unificationVars equations) :
    equations.map (Equation.apply (Subst.singleCap fresh (.var existing))) =
      equations := by
  induction equations with
  | nil => rfl
  | cons equation equations induction =>
      have headAbsent : .cap fresh ∉ equation.unificationVars := fun member =>
        absent (List.mem_append_left _ member)
      have tailAbsent : .cap fresh ∉ TypePM.unificationVars equations :=
        fun member => absent (List.mem_append_right _ member)
      simp [Equation.apply_singleCap_eq_self_of_not_mem equation fresh existing
        headAbsent, induction tailAbsent]

private theorem pending_singleTy_fixed
    (pending : List CheckObligation) (fresh existing : TyVar)
    (absent : .ty fresh ∉ pendingUnificationVars pending) :
    pending.map (CheckObligation.apply
      (Subst.singleTy fresh (.var existing))) = pending := by
  induction pending with
  | nil => rfl
  | cons obligation pending induction =>
      have headAbsent : .ty fresh ∉ obligation.unificationVars := fun member =>
        absent (List.mem_append_left _ member)
      have tailAbsent : .ty fresh ∉ pendingUnificationVars pending :=
        fun member => absent (List.mem_append_right _ member)
      simp [CheckObligation.apply_singleTy_eq_self_of_not_mem obligation fresh
        existing headAbsent, induction tailAbsent]

private theorem pending_singleCap_fixed
    (pending : List CheckObligation) (fresh existing : CapVar)
    (absent : .cap fresh ∉ pendingUnificationVars pending) :
    pending.map (CheckObligation.apply
      (Subst.singleCap fresh (.var existing))) = pending := by
  induction pending with
  | nil => rfl
  | cons obligation pending induction =>
      have headAbsent : .cap fresh ∉ obligation.unificationVars := fun member =>
        absent (List.mem_append_left _ member)
      have tailAbsent : .cap fresh ∉ pendingUnificationVars pending :=
        fun member => absent (List.mem_append_right _ member)
      simp [CheckObligation.apply_singleCap_eq_self_of_not_mem obligation fresh
        existing headAbsent, induction tailAbsent]

theorem tyInvariant_of_not_mem
    (body : Generated) (fresh existing : TyVar)
    (absent : .ty fresh ∉ body.unificationVars) :
    FreshAliasSaturation.TyInvariant fresh existing body.hard body.pending := by
  have hardAbsent : .ty fresh ∉ TypePM.unificationVars body.hard :=
    fun member => absent (by
      simp [Generated.unificationVars, member])
  have pendingAbsent : .ty fresh ∉ pendingUnificationVars body.pending :=
    fun member => absent (by
      simp [Generated.unificationVars, member])
  exact ⟨equations_singleTy_fixed body.hard fresh existing hardAbsent,
    pending_singleTy_fixed body.pending fresh existing pendingAbsent⟩

theorem capInvariant_of_not_mem
    (body : Generated) (fresh existing : CapVar)
    (absent : .cap fresh ∉ body.unificationVars) :
    FreshAliasSaturation.CapInvariant fresh existing body.hard body.pending := by
  have hardAbsent : .cap fresh ∉ TypePM.unificationVars body.hard :=
    fun member => absent (by
      simp [Generated.unificationVars, member])
  have pendingAbsent : .cap fresh ∉ pendingUnificationVars body.pending :=
    fun member => absent (by
      simp [Generated.unificationVars, member])
  exact ⟨equations_singleCap_fixed body.hard fresh existing hardAbsent,
    pending_singleCap_fixed body.pending fresh existing pendingAbsent⟩

theorem alias_admissible_of_not_mem
    (alias : Alias) (body : Generated)
    (different : freshVariable alias ≠ existingVariable alias)
    (absent : freshVariable alias ∉ body.unificationVars) :
    alias.Admissible body := by
  cases alias with
  | ty fresh existing =>
      exact ⟨by simpa using different,
        tyInvariant_of_not_mem body fresh existing absent⟩
  | cap fresh existing =>
      exact ⟨by simpa using different,
        capInvariant_of_not_mem body fresh existing absent⟩

theorem alias_mem_unificationVars_add_iff
    (alias : Alias) (body : Generated) (candidate : UnificationVar) :
    candidate ∈ (alias.add body).unificationVars ↔
      candidate = freshVariable alias ∨
        candidate = existingVariable alias ∨
          candidate ∈ body.unificationVars := by
  cases alias <;>
    simp [Alias.add, FreshAliasElimination.addTyAlias,
      FreshAliasElimination.addCapAlias, Generated.unificationVars,
      TypePM.unificationVars, Equation.unificationVars, Ty.unificationVars,
      Cap.unificationVars, or_comm, or_left_comm, or_assoc]

theorem ScopedBy.tail_extended
    {support : List UnificationVar} {alias : Alias} {aliases : List Alias}
    (scopeProof : ScopedBy support (alias :: aliases)) :
    ScopedBy (freshVariable alias :: support) aliases := by
  rcases scopeProof with ⟨nodup, pointwise⟩
  have split : freshVariable alias ∉ aliases.map freshVariable ∧
      (aliases.map freshVariable).Nodup := by
    simpa using (List.nodup_cons.mp nodup)
  refine ⟨split.2, ?_⟩
  intro later member
  have facts := pointwise later (by simp [member])
  constructor
  · simp only [List.mem_cons, not_or]
    exact ⟨by
      intro equality
      exact split.1 (List.mem_map.mpr ⟨later, member, equality⟩),
      facts.1⟩
  · exact List.mem_cons_of_mem _ facts.2

private theorem nodup_append_of_disjoint
    {α : Type} {left right : List α}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (disjoint : ∀ candidate, candidate ∈ left → candidate ∉ right) :
    (left ++ right).Nodup := by
  induction left with
  | nil => exact rightNodup
  | cons head tail induction =>
      have split := List.nodup_cons.mp leftNodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        rcases List.mem_append.mp member with tailMember | rightMember
        · exact split.1 tailMember
        · exact disjoint head (by simp) rightMember
      · exact induction split.2 (fun candidate member =>
          disjoint candidate (List.mem_cons_of_mem _ member))

theorem ScopedBy.append_one
    {support : List UnificationVar} {aliases : List Alias} {alias : Alias}
    (scopeProof : ScopedBy support aliases)
    (freshOutside : freshVariable alias ∉ support)
    (existingInside : existingVariable alias ∈ support)
    (freshNew : freshVariable alias ∉ aliases.map freshVariable) :
    ScopedBy support (aliases ++ [alias]) := by
  constructor
  · simp only [List.map_append, List.map_cons, List.map_nil]
    exact nodup_append_of_disjoint scopeProof.1 (by simp) (by
      intro candidate leftMember rightMember
      have equality : candidate = freshVariable alias := by simpa using rightMember
      subst candidate
      exact freshNew leftMember)
  · intro candidate member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact scopeProof.2 candidate old
    · exact ⟨freshOutside, existingInside⟩

theorem ScopedBy.append
    {support : List UnificationVar} {left right : List Alias}
    (leftScoped : ScopedBy support left)
    (rightScoped : ScopedBy support right)
    (disjointFresh : ∀ candidate,
      candidate ∈ left.map freshVariable →
      candidate ∉ right.map freshVariable) :
    ScopedBy support (left ++ right) := by
  constructor
  · simp only [List.map_append]
    exact nodup_append_of_disjoint leftScoped.1 rightScoped.1 (by
      intro candidate leftMember rightMember
      exact disjointFresh candidate leftMember rightMember)
  · intro alias member
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact leftScoped.2 alias leftMember
    · exact rightScoped.2 alias rightMember

theorem alias_add_support_subset
    {support : List UnificationVar} (alias : Alias) (body : Generated)
    (bodySupported : ∀ candidate, candidate ∈ body.unificationVars →
      candidate ∈ support)
    (existingSupported : existingVariable alias ∈ support) :
    ∀ candidate, candidate ∈ (alias.add body).unificationVars →
      candidate ∈ freshVariable alias :: support := by
  intro candidate member
  rcases (alias_mem_unificationVars_add_iff alias body candidate).mp member with
    rfl | rfl | original
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ existingSupported
  · exact List.mem_cons_of_mem _ (bodySupported candidate original)

/-- The common-support criterion automatically supplies every stepwise
freshness and invariance premise required by a finite alias sequence. -/
theorem admissible_of_scopedBy
    {support : List UnificationVar} {aliases : List Alias} {body : Generated}
    (scopeProof : ScopedBy support aliases)
    (bodySupported : ∀ candidate, candidate ∈ body.unificationVars →
      candidate ∈ support) :
    FreshAliasSequence.Admissible aliases body := by
  induction aliases generalizing support body with
  | nil => trivial
  | cons alias aliases induction =>
      have facts := scopeProof.2 alias (by simp)
      have different : freshVariable alias ≠ existingVariable alias := by
        intro equality
        exact facts.1 (equality ▸ facts.2)
      have absent : freshVariable alias ∉ body.unificationVars := by
        intro member
        exact facts.1 (bodySupported _ member)
      constructor
      · exact alias_admissible_of_not_mem alias body different absent
      · exact induction scopeProof.tail_extended
          (alias_add_support_subset alias body bodySupported facts.2)

end AliasFreshness

namespace EquationLists

open FreshAliasSequence

/-- Hard equation contributed by one mixed-sort alias. -/
def aliasEquation : Alias → Equation
  | .ty fresh existing => .ty (.var fresh) (.var existing)
  | .cap fresh existing => .cap (.var fresh) (.var existing)

/-- Add aliases in the same order as `FreshAliasSequence.addAll`. -/
def addAliases : List Alias → List Equation → List Equation
  | [], equations => equations
  | alias :: aliases, equations =>
      addAliases aliases (aliasEquation alias :: equations)

@[simp] theorem addAliases_nil (equations : List Equation) :
    addAliases [] equations = equations := rfl

@[simp] theorem addAliases_cons
    (alias : Alias) (aliases : List Alias) (equations : List Equation) :
    addAliases (alias :: aliases) equations =
      addAliases aliases (aliasEquation alias :: equations) := rfl

theorem addAliases_append
    (aliases : List Alias) (left right : List Equation) :
    addAliases aliases (left ++ right) =
      addAliases aliases left ++ right := by
  induction aliases generalizing left with
  | nil => rfl
  | cons alias aliases induction =>
      simpa [addAliases] using induction (aliasEquation alias :: left)

theorem addAliases_eq_reverse_map_append
    (aliases : List Alias) (equations : List Equation) :
    addAliases aliases equations =
      aliases.reverse.map aliasEquation ++ equations := by
  induction aliases generalizing equations with
  | nil => rfl
  | cons alias aliases induction =>
      simp [addAliases, induction, List.map_append, List.append_assoc]

/-- Alias equations may be moved past one ordinary equation because hard
worklists are interpreted as unordered conjunctions. -/
theorem addAliases_cons_equivalent
    (aliases : List Alias) (equation : Equation)
    (equations : List Equation) :
    HardEquivalent
      (addAliases aliases (equation :: equations))
      (equation :: addAliases aliases equations) := by
  intro substitution
  simp [addAliases_eq_reverse_map_append, and_left_comm]

@[simp] theorem addAliases_append_singleton
    (aliases : List Alias) (alias : Alias) (equations : List Equation) :
    addAliases (aliases ++ [alias]) equations =
      aliasEquation alias :: addAliases aliases equations := by
  simp [addAliases_eq_reverse_map_append]

/-- Equation-list projection of `FreshAliasSequence.addAll`. -/
theorem addAll_hard (aliases : List Alias) (body : Generated) :
    (FreshAliasSequence.addAll aliases body).hard =
      addAliases aliases body.hard := by
  induction aliases generalizing body with
  | nil => rfl
  | cons alias aliases induction =>
      rw [FreshAliasSequence.addAll, induction]
      cases alias <;>
        simp [FreshAliasSequence.Alias.add,
          FreshAliasElimination.addTyAlias,
          FreshAliasElimination.addCapAlias, addAliases, aliasEquation]

/-- Pure symmetric decomposition of two hard-equation lists through one
common list.  Freshness and delayed obligations deliberately do not occur in
this structure. -/
structure EquationCommonCore (left right : List Equation) where
  core : List Equation
  leftAliases : List Alias
  rightAliases : List Alias
  leftEquivalent : HardEquivalent (addAliases leftAliases core) left
  rightEquivalent : HardEquivalent (addAliases rightAliases core) right

namespace EquationCommonCore

def refl (equations : List Equation) :
    EquationCommonCore equations equations :=
  ⟨equations, [], [], HardEquivalent.refl equations,
    HardEquivalent.refl equations⟩

def symm {left right : List Equation}
    (decomposition : EquationCommonCore left right) :
    EquationCommonCore right left :=
  ⟨decomposition.core, decomposition.rightAliases,
    decomposition.leftAliases, decomposition.rightEquivalent,
    decomposition.leftEquivalent⟩

def transportLeft {left middle right : List Equation}
    (equivalent : HardEquivalent left middle)
    (decomposition : EquationCommonCore middle right) :
    EquationCommonCore left right :=
  ⟨decomposition.core, decomposition.leftAliases,
    decomposition.rightAliases,
    decomposition.leftEquivalent.trans equivalent.symm,
    decomposition.rightEquivalent⟩

def transportRight {left middle right : List Equation}
    (decomposition : EquationCommonCore left middle)
    (equivalent : HardEquivalent middle right) :
    EquationCommonCore left right :=
  ⟨decomposition.core, decomposition.leftAliases,
    decomposition.rightAliases, decomposition.leftEquivalent,
    decomposition.rightEquivalent.trans equivalent⟩

/-- Prepending the same concrete equation on both sides preserves a
decomposition.  Existing alias equations may commute past that equation. -/
def prependSame {left right : List Equation}
    (equation : Equation)
    (decomposition : EquationCommonCore left right) :
    EquationCommonCore (equation :: left) (equation :: right) :=
  ⟨equation :: decomposition.core,
    decomposition.leftAliases, decomposition.rightAliases,
    (addAliases_cons_equivalent _ _ _).trans
      (by
        simpa only [List.singleton_append] using
          decomposition.leftEquivalent.appendRight
            (initial := [equation])),
    (addAliases_cons_equivalent _ _ _).trans
      (by
        simpa only [List.singleton_append] using
          decomposition.rightEquivalent.appendRight
            (initial := [equation]))⟩

/-- Prepend a genuine ordinary-variable alias on the left and a reflexive
equation on the right. -/
def prependTyAliasRefl {left right : List Equation}
    (fresh existing : TyVar)
    (decomposition : EquationCommonCore left right) :
    EquationCommonCore
      (.ty (.var fresh) (.var existing) :: left)
      (.ty (.var existing) (.var existing) :: right) :=
  ⟨decomposition.core,
    decomposition.leftAliases ++ [.ty fresh existing],
    decomposition.rightAliases,
    by
      rw [addAliases_append_singleton]
      simpa only [aliasEquation, List.singleton_append] using
        decomposition.leftEquivalent.appendRight
          (initial := [.ty (.var fresh) (.var existing)]),
    decomposition.rightEquivalent.trans
      ((HardEquivalent.cons_ty_refl (.var existing) right).symm)⟩

/-- Capability-variable counterpart of `prependTyAliasRefl`. -/
def prependCapAliasRefl {left right : List Equation}
    (fresh existing : CapVar)
    (decomposition : EquationCommonCore left right) :
    EquationCommonCore
      (.cap (.var fresh) (.var existing) :: left)
      (.cap (.var existing) (.var existing) :: right) :=
  ⟨decomposition.core,
    decomposition.leftAliases ++ [.cap fresh existing],
    decomposition.rightAliases,
    by
      rw [addAliases_append_singleton]
      simpa only [aliasEquation, List.singleton_append] using
        decomposition.leftEquivalent.appendRight
          (initial := [.cap (.var fresh) (.var existing)]),
    decomposition.rightEquivalent.trans
      ((HardEquivalent.cons_cap_refl (.var existing) right).symm)⟩

def prependTyReflAlias {left right : List Equation}
    (fresh existing : TyVar)
    (decomposition : EquationCommonCore left right) :
    EquationCommonCore
      (.ty (.var existing) (.var existing) :: left)
      (.ty (.var fresh) (.var existing) :: right) :=
  (prependTyAliasRefl fresh existing decomposition.symm).symm

def prependCapReflAlias {left right : List Equation}
    (fresh existing : CapVar)
    (decomposition : EquationCommonCore left right) :
    EquationCommonCore
      (.cap (.var existing) (.var existing) :: left)
      (.cap (.var fresh) (.var existing) :: right) :=
  (prependCapAliasRefl fresh existing decomposition.symm).symm

/-- Nontrivial ordinary alias on the left and a tautology on the right. -/
def tyAlias_refl (fresh existing : TyVar) (tail : List Equation) :
    EquationCommonCore
      (.ty (.var fresh) (.var existing) :: tail)
      (.ty (.var existing) (.var existing) :: tail) :=
  ⟨tail, [.ty fresh existing], [],
    by
      simpa [addAliases, aliasEquation] using
        (HardEquivalent.refl
          (.ty (.var fresh) (.var existing) :: tail)),
    (HardEquivalent.cons_ty_refl (.var existing) tail).symm⟩

/-- Capability-variable counterpart of `tyAlias_refl`. -/
def capAlias_refl (fresh existing : CapVar) (tail : List Equation) :
    EquationCommonCore
      (.cap (.var fresh) (.var existing) :: tail)
      (.cap (.var existing) (.var existing) :: tail) :=
  ⟨tail, [.cap fresh existing], [],
    by
      simpa [addAliases, aliasEquation] using
        (HardEquivalent.refl
          (.cap (.var fresh) (.var existing) :: tail)),
    (HardEquivalent.cons_cap_refl (.var existing) tail).symm⟩

def refl_tyAlias (fresh existing : TyVar) (tail : List Equation) :
    EquationCommonCore
      (.ty (.var existing) (.var existing) :: tail)
      (.ty (.var fresh) (.var existing) :: tail) :=
  (tyAlias_refl fresh existing tail).symm

def refl_capAlias (fresh existing : CapVar) (tail : List Equation) :
    EquationCommonCore
      (.cap (.var existing) (.var existing) :: tail)
      (.cap (.var fresh) (.var existing) :: tail) :=
  (capAlias_refl fresh existing tail).symm

/-- Appending the same later hard worklist preserves a pure decomposition. -/
def appendSame {left right : List Equation}
    (decomposition : EquationCommonCore left right)
    (suffix : List Equation) :
    EquationCommonCore (left ++ suffix) (right ++ suffix) := by
  refine ⟨decomposition.core ++ suffix,
    decomposition.leftAliases, decomposition.rightAliases, ?_, ?_⟩
  · rw [addAliases_append]
    exact decomposition.leftEquivalent.appendLeft
  · rw [addAliases_append]
    exact decomposition.rightEquivalent.appendLeft

/-- Convert the pure equation certificate into the acceptance-level common
core once the caller supplies exactly the body freshness needed by each alias
sequence. -/
theorem toFreshAliasCommonCore
    {leftInterface rightInterface : List Equation}
    (decomposition : EquationCommonCore leftInterface rightInterface)
    (body : Generated)
    (leftAdmissible : FreshAliasSequence.Admissible
      decomposition.leftAliases
      (Generated.fromLet decomposition.core body))
    (rightAdmissible : FreshAliasSequence.Admissible
      decomposition.rightAliases
      (Generated.fromLet decomposition.core body)) :
    FreshAliasSequence.CommonCoreEquivalent
      (Generated.fromLet leftInterface body)
      (Generated.fromLet rightInterface body) := by
  let coreBlock := Generated.fromLet decomposition.core body
  refine ⟨coreBlock, decomposition.leftAliases,
    decomposition.rightAliases, leftAdmissible, rightAdmissible, ?_, ?_,
    ?_, ?_⟩
  · rw [addAll_hard]
    change HardEquivalent
      (addAliases decomposition.leftAliases
        (decomposition.core ++ body.hard))
      (leftInterface ++ body.hard)
    rw [addAliases_append]
    exact decomposition.leftEquivalent.appendLeft (suffix := body.hard)
  · rw [addAll_hard]
    change HardEquivalent
      (addAliases decomposition.rightAliases
        (decomposition.core ++ body.hard))
      (rightInterface ++ body.hard)
    rw [addAliases_append]
    exact decomposition.rightEquivalent.appendLeft (suffix := body.hard)
  · simp [coreBlock, Generated.fromLet]
  · simp [coreBlock, Generated.fromLet]

end EquationCommonCore

/-- Pointwise normal form produced by interface classification.  The only
non-identical pairs are a variable alias versus a reflexive equation. -/
inductive PairwiseAliasShape : List Equation → List Equation → Type where
  | nil : PairwiseAliasShape [] []
  | same (equation : Equation) {left right : List Equation}
      (tail : PairwiseAliasShape left right) :
      PairwiseAliasShape (equation :: left) (equation :: right)
  | tyAliasRefl (fresh existing : TyVar)
      {left right : List Equation}
      (tail : PairwiseAliasShape left right) :
      PairwiseAliasShape
        (.ty (.var fresh) (.var existing) :: left)
        (.ty (.var existing) (.var existing) :: right)
  | tyReflAlias (fresh existing : TyVar)
      {left right : List Equation}
      (tail : PairwiseAliasShape left right) :
      PairwiseAliasShape
        (.ty (.var existing) (.var existing) :: left)
        (.ty (.var fresh) (.var existing) :: right)
  | capAliasRefl (fresh existing : CapVar)
      {left right : List Equation}
      (tail : PairwiseAliasShape left right) :
      PairwiseAliasShape
        (.cap (.var fresh) (.var existing) :: left)
        (.cap (.var existing) (.var existing) :: right)
  | capReflAlias (fresh existing : CapVar)
      {left right : List Equation}
      (tail : PairwiseAliasShape left right) :
      PairwiseAliasShape
        (.cap (.var existing) (.var existing) :: left)
        (.cap (.var fresh) (.var existing) :: right)

/-- The variable at the left-hand side of an interface equation, when that
side is a bare variable. -/
def equationLeftVariable? : Equation → Option UnificationVar
  | .ty (.var index) _ => some (.ty index)
  | .cap (.var index) _ => some (.cap index)
  | _ => none

def equationLeftVariables (equations : List Equation) :
    List UnificationVar :=
  equations.filterMap equationLeftVariable?

namespace PairwiseAliasShape

noncomputable def append
    {left₁ right₁ left₂ right₂ : List Equation}
    (first : PairwiseAliasShape left₁ right₁)
    (second : PairwiseAliasShape left₂ right₂) :
    PairwiseAliasShape (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction first with
  | nil => exact second
  | same equation _ induction => exact .same equation induction
  | tyAliasRefl fresh existing _ induction =>
      exact .tyAliasRefl fresh existing induction
  | tyReflAlias fresh existing _ induction =>
      exact .tyReflAlias fresh existing induction
  | capAliasRefl fresh existing _ induction =>
      exact .capAliasRefl fresh existing induction
  | capReflAlias fresh existing _ induction =>
      exact .capReflAlias fresh existing induction

/-- Every pointwise interface classification gives the pure symmetric
common-core decomposition. -/
noncomputable def toEquationCommonCore {left right : List Equation}
    (shape : PairwiseAliasShape left right) :
    EquationCommonCore left right := by
  induction shape with
  | nil => exact EquationCommonCore.refl []
  | same equation _ induction =>
      exact EquationCommonCore.prependSame equation induction
  | tyAliasRefl fresh existing _ induction =>
      exact EquationCommonCore.prependTyAliasRefl fresh existing induction
  | tyReflAlias fresh existing _ induction =>
      exact EquationCommonCore.prependTyReflAlias fresh existing induction
  | capAliasRefl fresh existing _ induction =>
      exact EquationCommonCore.prependCapAliasRefl fresh existing induction
  | capReflAlias fresh existing _ induction =>
      exact EquationCommonCore.prependCapReflAlias fresh existing induction

theorem leftAliases_reverse_sublist {left right : List Equation}
    (shape : PairwiseAliasShape left right) :
    (((toEquationCommonCore shape).leftAliases.map
      AliasFreshness.freshVariable).reverse).Sublist
        (equationLeftVariables left) := by
  induction shape with
  | nil => exact .slnil
  | same equation tail induction =>
      change
        (((toEquationCommonCore tail).leftAliases.map
          AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables (equation :: _))
      cases option : equationLeftVariable? equation with
      | none =>
          unfold equationLeftVariables at induction ⊢
          simp only [List.filterMap_cons, option]
          exact induction
      | some item =>
          unfold equationLeftVariables at induction ⊢
          simp only [List.filterMap_cons, option]
          exact induction.cons item
  | tyAliasRefl fresh existing tail induction =>
      change
        ((((toEquationCommonCore tail).leftAliases ++
          [FreshAliasSequence.Alias.ty fresh existing]).map
            AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables
            (.ty (.var fresh) (.var existing) :: _))
      simpa [equationLeftVariables, equationLeftVariable?,
        AliasFreshness.freshVariable, List.map_append] using
        induction.cons_cons (.ty fresh)
  | tyReflAlias fresh existing tail induction =>
      change
        (((toEquationCommonCore tail).leftAliases.map
          AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables
            (.ty (.var existing) (.var existing) :: _))
      simpa [equationLeftVariables, equationLeftVariable?] using
        induction.cons (.ty existing)
  | capAliasRefl fresh existing tail induction =>
      change
        ((((toEquationCommonCore tail).leftAliases ++
          [FreshAliasSequence.Alias.cap fresh existing]).map
            AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables
            (.cap (.var fresh) (.var existing) :: _))
      simpa [equationLeftVariables, equationLeftVariable?,
        AliasFreshness.freshVariable, List.map_append] using
        induction.cons_cons (.cap fresh)
  | capReflAlias fresh existing tail induction =>
      change
        (((toEquationCommonCore tail).leftAliases.map
          AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables
            (.cap (.var existing) (.var existing) :: _))
      simpa [equationLeftVariables, equationLeftVariable?] using
        induction.cons (.cap existing)

theorem rightAliases_reverse_sublist {left right : List Equation}
    (shape : PairwiseAliasShape left right) :
    (((toEquationCommonCore shape).rightAliases.map
      AliasFreshness.freshVariable).reverse).Sublist
        (equationLeftVariables right) := by
  induction shape with
  | nil => exact .slnil
  | same equation tail induction =>
      change
        (((toEquationCommonCore tail).rightAliases.map
          AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables (equation :: _))
      cases option : equationLeftVariable? equation with
      | none =>
          unfold equationLeftVariables at induction ⊢
          simp only [List.filterMap_cons, option]
          exact induction
      | some item =>
          unfold equationLeftVariables at induction ⊢
          simp only [List.filterMap_cons, option]
          exact induction.cons item
  | tyAliasRefl fresh existing tail induction =>
      change
        (((toEquationCommonCore tail).rightAliases.map
          AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables
            (.ty (.var existing) (.var existing) :: _))
      simpa [equationLeftVariables, equationLeftVariable?] using
        induction.cons (.ty existing)
  | tyReflAlias fresh existing tail induction =>
      change
        ((((toEquationCommonCore tail).rightAliases ++
          [FreshAliasSequence.Alias.ty fresh existing]).map
            AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables
            (.ty (.var fresh) (.var existing) :: _))
      simpa [equationLeftVariables, equationLeftVariable?,
        AliasFreshness.freshVariable, List.map_append] using
        induction.cons_cons (.ty fresh)
  | capAliasRefl fresh existing tail induction =>
      change
        (((toEquationCommonCore tail).rightAliases.map
          AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables
            (.cap (.var existing) (.var existing) :: _))
      simpa [equationLeftVariables, equationLeftVariable?] using
        induction.cons (.cap existing)
  | capReflAlias fresh existing tail induction =>
      change
        ((((toEquationCommonCore tail).rightAliases ++
          [FreshAliasSequence.Alias.cap fresh existing]).map
            AliasFreshness.freshVariable).reverse).Sublist
          (equationLeftVariables
            (.cap (.var fresh) (.var existing) :: _))
      simpa [equationLeftVariables, equationLeftVariable?,
        AliasFreshness.freshVariable, List.map_append] using
        induction.cons_cons (.cap fresh)

private theorem nodup_of_reverse_nodup {α : Type} :
    ∀ items : List α, items.reverse.Nodup → items.Nodup := by
  intro items reversed
  have flipped := List.pairwise_reverse.mp reversed
  have convert : ∀ values : List α,
      List.Pairwise (fun left right => right ≠ left) values →
        values.Nodup := by
    intro values pairwise
    induction values with
    | nil => exact .nil
    | cons head tail induction =>
        apply List.nodup_cons.mpr
        constructor
        · intro member
          exact (List.pairwise_cons.mp pairwise).1 head member rfl
        · exact induction (List.pairwise_cons.mp pairwise).2
  exact convert items flipped

theorem leftAliases_fresh_nodup {left right : List Equation}
    (shape : PairwiseAliasShape left right)
    (leftNodup : (equationLeftVariables left).Nodup) :
    ((toEquationCommonCore shape).leftAliases.map
      AliasFreshness.freshVariable).Nodup :=
  nodup_of_reverse_nodup _
    ((leftAliases_reverse_sublist shape).nodup leftNodup)

theorem rightAliases_fresh_nodup {left right : List Equation}
    (shape : PairwiseAliasShape left right)
    (rightNodup : (equationLeftVariables right).Nodup) :
    ((toEquationCommonCore shape).rightAliases.map
      AliasFreshness.freshVariable).Nodup :=
  nodup_of_reverse_nodup _
    ((rightAliases_reverse_sublist shape).nodup rightNodup)

end PairwiseAliasShape

end EquationLists

/-! ## Fixed points exposed by an idempotent substitution

If a variable occurs in an image of an idempotent substitution, applying the
substitution once more leaves that occurrence unchanged.  These structural
lemmas are the reason a moved interface endpoint can only be a bare variable
alias rather than an alias to a structured type. -/

def SubstitutionFixes (substitution : Subst) : UnificationVar → Prop
  | .ty index => substitution.ty index = .var index
  | .cap index => substitution.cap index = .var index

mutual

theorem Cap.substitutionFixes_of_mem_apply_eq
    (substitution : Subst) (capability : Cap)
    (fixed : capability.apply substitution.cap = capability) :
    ∀ candidate, candidate ∈ capability.unificationVars →
      SubstitutionFixes substitution candidate := by
  intro candidate member
  cases capability with
  | any => simp [Cap.unificationVars] at member
  | var index =>
      have equality : candidate = .cap index := by
        simpa [Cap.unificationVars] using member
      subst candidate
      simpa [SubstitutionFixes, Cap.apply] using fixed
  | prod items =>
      exact Cap.substitutionFixesList_of_mem_apply_eq substitution items
        (Cap.prod.inj fixed) candidate
        (by simpa [Cap.unificationVars] using member)
  | con former arguments =>
      exact Cap.substitutionFixesList_of_mem_apply_eq substitution arguments
        (Cap.con.inj fixed).2 candidate
        (by simpa [Cap.unificationVars] using member)

theorem Cap.substitutionFixesList_of_mem_apply_eq
    (substitution : Subst) (items : List Cap)
    (fixed : Cap.applyList substitution.cap items = items) :
    ∀ candidate, candidate ∈ Cap.unificationVarsList items →
      SubstitutionFixes substitution candidate := by
  intro candidate member
  cases items with
  | nil => simp [Cap.unificationVarsList] at member
  | cons item items =>
      have parts := List.cons.inj fixed
      simp only [Cap.unificationVarsList, List.mem_append] at member
      rcases member with head | tail
      · exact Cap.substitutionFixes_of_mem_apply_eq substitution item
          parts.1 candidate head
      · exact Cap.substitutionFixesList_of_mem_apply_eq substitution items
          parts.2 candidate tail

theorem Ty.substitutionFixes_of_mem_apply_eq
    (substitution : Subst) (target : Ty)
    (fixed : target.apply substitution = target) :
    ∀ candidate, candidate ∈ target.unificationVars →
      SubstitutionFixes substitution candidate := by
  intro candidate member
  cases target with
  | var index =>
      have equality : candidate = .ty index := by
        simpa [Ty.unificationVars] using member
      subst candidate
      simpa [SubstitutionFixes, Ty.apply] using fixed
  | int => simp [Ty.unificationVars] at member
  | fn domain codomain =>
      have parts := Ty.fn.inj fixed
      simp only [Ty.unificationVars, List.mem_append] at member
      rcases member with left | right
      · exact Ty.substitutionFixes_of_mem_apply_eq substitution domain
          parts.1 candidate left
      · exact Ty.substitutionFixes_of_mem_apply_eq substitution codomain
          parts.2 candidate right
  | prod items =>
      exact Ty.substitutionFixesList_of_mem_apply_eq substitution items
        (Ty.prod.inj fixed) candidate
        (by simpa [Ty.unificationVars] using member)
  | data former arguments =>
      exact Ty.substitutionFixesList_of_mem_apply_eq substitution arguments
        (Ty.data.inj fixed).2 candidate
        (by simpa [Ty.unificationVars] using member)
  | matcher capability target =>
      have parts := Ty.matcher.inj fixed
      simp only [Ty.unificationVars, List.mem_append] at member
      rcases member with left | right
      · exact Cap.substitutionFixes_of_mem_apply_eq substitution capability
          parts.1 candidate left
      · exact Ty.substitutionFixes_of_mem_apply_eq substitution target
          parts.2 candidate right
  | slot capability target =>
      have parts := Ty.slot.inj fixed
      simp only [Ty.unificationVars, List.mem_append] at member
      rcases member with left | right
      · exact Cap.substitutionFixes_of_mem_apply_eq substitution capability
          parts.1 candidate left
      · exact Ty.substitutionFixes_of_mem_apply_eq substitution target
          parts.2 candidate right

theorem Ty.substitutionFixesList_of_mem_apply_eq
    (substitution : Subst) (items : List Ty)
    (fixed : Ty.applyList substitution items = items) :
    ∀ candidate, candidate ∈ Ty.unificationVarsList items →
      SubstitutionFixes substitution candidate := by
  intro candidate member
  cases items with
  | nil => simp [Ty.unificationVarsList] at member
  | cons item items =>
      have parts := List.cons.inj fixed
      simp only [Ty.unificationVarsList, List.mem_append] at member
      rcases member with head | tail
      · exact Ty.substitutionFixes_of_mem_apply_eq substitution item
          parts.1 candidate head
      · exact Ty.substitutionFixesList_of_mem_apply_eq substitution items
          parts.2 candidate tail

end

theorem SubstitutionFixes.of_tyImage
    {substitution : Subst}
    (idempotent : Subst.compose substitution substitution = substitution)
    (index : TyVar) {candidate : UnificationVar}
    (member : candidate ∈ (substitution.ty index).unificationVars) :
    SubstitutionFixes substitution candidate := by
  apply Ty.substitutionFixes_of_mem_apply_eq substitution
    (substitution.ty index) ?_ candidate member
  have atIndex := congrArg (fun current => current.ty index) idempotent
  simpa [Subst.compose] using atIndex

theorem SubstitutionFixes.of_capImage
    {substitution : Subst}
    (idempotent : Subst.compose substitution substitution = substitution)
    (index : CapVar) {candidate : UnificationVar}
    (member : candidate ∈ (substitution.cap index).unificationVars) :
    SubstitutionFixes substitution candidate := by
  apply Cap.substitutionFixes_of_mem_apply_eq substitution
    (substitution.cap index) ?_ candidate member
  have atIndex := congrArg (fun current => current.cap index) idempotent
  simpa [Subst.compose] using atIndex

/-- A two-sorted output variable occurs in the substitution image selected
by an input variable. -/
def SubstitutionImageContains (substitution : Subst) :
    UnificationVar → UnificationVar → Prop
  | .ty index, candidate =>
      candidate ∈ (substitution.ty index).unificationVars
  | .cap index, candidate =>
      candidate ∈ (substitution.cap index).unificationVars

mutual

theorem Cap.mem_apply_of_image
    (substitution : Subst) (capability : Cap)
    (input candidate : UnificationVar)
    (inputMember : input ∈ capability.unificationVars)
    (imageMember : SubstitutionImageContains substitution input candidate) :
    candidate ∈ (capability.apply substitution.cap).unificationVars := by
  cases capability with
  | any => simp [Cap.unificationVars] at inputMember
  | var index =>
      have equality : input = .cap index := by
        simpa [Cap.unificationVars] using inputMember
      subst input
      exact imageMember
  | prod items =>
      apply Cap.mem_applyList_of_image substitution items input candidate
      · simpa [Cap.unificationVars] using inputMember
      · exact imageMember
  | con former arguments =>
      apply Cap.mem_applyList_of_image substitution arguments input candidate
      · simpa [Cap.unificationVars] using inputMember
      · exact imageMember

theorem Cap.mem_applyList_of_image
    (substitution : Subst) (items : List Cap)
    (input candidate : UnificationVar)
    (inputMember : input ∈ Cap.unificationVarsList items)
    (imageMember : SubstitutionImageContains substitution input candidate) :
    candidate ∈
      Cap.unificationVarsList (Cap.applyList substitution.cap items) := by
  cases items with
  | nil => simp [Cap.unificationVarsList] at inputMember
  | cons item items =>
      simp only [Cap.applyList, Cap.unificationVarsList,
        List.mem_append] at inputMember ⊢
      rcases inputMember with head | tail
      · exact Or.inl
          (Cap.mem_apply_of_image substitution item input candidate
            head imageMember)
      · exact Or.inr
          (Cap.mem_applyList_of_image substitution items input candidate
            tail imageMember)

theorem Ty.mem_apply_of_image
    (substitution : Subst) (target : Ty)
    (input candidate : UnificationVar)
    (inputMember : input ∈ target.unificationVars)
    (imageMember : SubstitutionImageContains substitution input candidate) :
    candidate ∈ (target.apply substitution).unificationVars := by
  cases target with
  | var index =>
      have equality : input = .ty index := by
        simpa [Ty.unificationVars] using inputMember
      subst input
      exact imageMember
  | int => simp [Ty.unificationVars] at inputMember
  | fn domain codomain =>
      simp only [Ty.apply, Ty.unificationVars,
        List.mem_append] at inputMember ⊢
      rcases inputMember with left | right
      · exact Or.inl
          (Ty.mem_apply_of_image substitution domain input candidate
            left imageMember)
      · exact Or.inr
          (Ty.mem_apply_of_image substitution codomain input candidate
            right imageMember)
  | prod items =>
      apply Ty.mem_applyList_of_image substitution items input candidate
      · simpa [Ty.unificationVars] using inputMember
      · exact imageMember
  | data former arguments =>
      apply Ty.mem_applyList_of_image substitution arguments input candidate
      · simpa [Ty.unificationVars] using inputMember
      · exact imageMember
  | matcher capability target =>
      simp only [Ty.apply, Ty.unificationVars,
        List.mem_append] at inputMember ⊢
      rcases inputMember with left | right
      · exact Or.inl
          (Cap.mem_apply_of_image substitution capability input candidate
            left imageMember)
      · exact Or.inr
          (Ty.mem_apply_of_image substitution target input candidate
            right imageMember)
  | slot capability target =>
      simp only [Ty.apply, Ty.unificationVars,
        List.mem_append] at inputMember ⊢
      rcases inputMember with left | right
      · exact Or.inl
          (Cap.mem_apply_of_image substitution capability input candidate
            left imageMember)
      · exact Or.inr
          (Ty.mem_apply_of_image substitution target input candidate
            right imageMember)

theorem Ty.mem_applyList_of_image
    (substitution : Subst) (items : List Ty)
    (input candidate : UnificationVar)
    (inputMember : input ∈ Ty.unificationVarsList items)
    (imageMember : SubstitutionImageContains substitution input candidate) :
    candidate ∈
      Ty.unificationVarsList (Ty.applyList substitution items) := by
  cases items with
  | nil => simp [Ty.unificationVarsList] at inputMember
  | cons item items =>
      simp only [Ty.applyList, Ty.unificationVarsList,
        List.mem_append] at inputMember ⊢
      rcases inputMember with head | tail
      · exact Or.inl
          (Ty.mem_apply_of_image substitution item input candidate
            head imageMember)
      · exact Or.inr
          (Ty.mem_applyList_of_image substitution items input candidate
            tail imageMember)

end

/-! ## Support of the finite global extension -/

namespace GlobalExtension

/-- The extension algorithm fixes a name in both directions when that name
is absent from both finite endpoint lists. -/
theorem extend_fixed_outside
    { α : Type } [DecidableEq α]
    (sources targets : List α) (item : α)
    (outsideSources : item ∉ sources)
    (outsideTargets : item ∉ targets) :
    (TypePM.Source.FinitePermutation.extend sources targets).forward item = item ∧
      (TypePM.Source.FinitePermutation.extend sources targets).backward item = item := by
  induction sources generalizing targets with
  | nil =>
      cases targets <;> simp [TypePM.Source.FinitePermutation.extend,
        TypePM.Source.FinitePermutation.Permutation.refl]
  | cons source sources induction =>
      cases targets with
      | nil => simp [TypePM.Source.FinitePermutation.extend,
          TypePM.Source.FinitePermutation.Permutation.refl]
      | cons target targets =>
          have sourceFacts : item ≠ source ∧ item ∉ sources := by
            simpa using outsideSources
          have targetFacts : item ≠ target ∧ item ∉ targets := by
            simpa using outsideTargets
          have tailFixed := induction targets sourceFacts.2 targetFacts.2
          let tail := TypePM.Source.FinitePermutation.extend sources targets
          have notTailImage : item ≠ tail.forward source := by
            intro equality
            have sameImage : tail.forward item = tail.forward source := by
              rw [tailFixed.1, equality]
            have restored := congrArg tail.backward sameImage
            have same : item = source := by
              simpa only [tail.backward_forward] using restored
            exact sourceFacts.1 same
          have swapped :
              (TypePM.Source.FinitePermutation.swap
                (tail.forward source) target).forward item = item :=
            TypePM.Source.FinitePermutation.swap_fixed
              notTailImage targetFacts.1
          constructor
          · change
              (TypePM.Source.FinitePermutation.swap
                (tail.forward source) target).forward
                  (tail.forward item) = item
            rw [tailFixed.1]
            exact swapped
          · change tail.backward
                ((TypePM.Source.FinitePermutation.swap
                  (tail.forward source) target).backward item) = item
            have swappedBackward :
                (TypePM.Source.FinitePermutation.swap
                  (tail.forward source) target).backward item = item :=
              TypePM.Source.FinitePermutation.swap_fixed
                notTailImage targetFacts.1
            rw [swappedBackward]
            exact tailFixed.2

end GlobalExtension

namespace FinitePartialExtension

/-- A partial bijection's global extension introduces no movement outside
its declared source and target supports. -/
theorem extend_fixed_outside'
    { α : Type } [DecidableEq α]
    (data : FinitePartialBijection α) (item : α)
    (outsideSource : item ∉ data.source)
    (outsideTarget : item ∉ data.target) :
    data.extend.forward item = item ∧
      data.extend.backward item = item := by
  apply GlobalExtension.extend_fixed_outside
    data.source (data.source.map data.forward) item outsideSource
  intro member
  obtain ⟨source, sourceMember, equality⟩ := List.mem_map.mp member
  apply outsideTarget
  rw [← equality]
  exact data.forward_mem sourceMember

end FinitePartialExtension

/-! ## Observable support of a closed value block -/

namespace ObservableSupport

def schemeWitness (scheme : Scheme) : Ty :=
  scheme.body.openBound (fun _ => .int) (fun _ => .any)

def contextWitness (context : Context) : Ty :=
  .prod (context.map schemeWitness)

def closureWitness (context : Context) (target : Ty) : Ty :=
  .prod [contextWitness context, target]

mutual

@[simp] theorem PolyTy.openGround_tyVars (body : PolyTy) :
    (body.openBound (fun _ => .int) (fun _ => .any)).tyVars =
      body.freeTyVars := by
  cases body <;>
    simp [PolyTy.openBound, PolyTy.freeTyVars, Ty.tyVars,
      PolyTy.openGround_tyVars, PolyTy.openGroundList_tyVars]

@[simp] theorem PolyTy.openGroundList_tyVars (items : List PolyTy) :
    Ty.tyVarsList
        (PolyTy.openBoundList (fun _ => .int) (fun _ => .any) items) =
      PolyTy.freeTyVarsList items := by
  cases items <;>
    simp [PolyTy.openBoundList, PolyTy.freeTyVarsList, Ty.tyVarsList,
      PolyTy.openGround_tyVars, PolyTy.openGroundList_tyVars]

end


mutual

@[simp] theorem PolyCap.openGround_capVars (body : PolyCap) :
    (body.openBound (fun _ => .any)).capVars =
      body.freeCapVars := by
  cases body <;>
    simp [PolyCap.openBound, PolyCap.freeCapVars, Cap.capVars,
      PolyCap.openGroundList_capVars]

@[simp] theorem PolyCap.openGroundList_capVars (items : List PolyCap) :
    Cap.capVarsList
        (PolyCap.openBoundList (fun _ => .any) items) =
      PolyCap.freeCapVarsList items := by
  cases items <;>
    simp [PolyCap.openBoundList, PolyCap.freeCapVarsList, Cap.capVarsList,
      PolyCap.openGround_capVars, PolyCap.openGroundList_capVars]

end


mutual

@[simp] theorem PolyTy.openGround_capVars (body : PolyTy) :
    (body.openBound (fun _ => .int) (fun _ => .any)).capVars =
      body.freeCapVars := by
  cases body <;>
    simp [PolyTy.openBound, PolyTy.freeCapVars, Ty.capVars,
      PolyTy.openGround_capVars, PolyTy.openGroundList_capVars,
      PolyCap.openGround_capVars]

@[simp] theorem PolyTy.openGroundList_capVars (items : List PolyTy) :
    Ty.capVarsList
        (PolyTy.openBoundList (fun _ => .int) (fun _ => .any) items) =
      PolyTy.freeCapVarsList items := by
  cases items <;>
    simp [PolyTy.openBoundList, PolyTy.freeCapVarsList, Ty.capVarsList,
      PolyTy.openGround_capVars, PolyTy.openGroundList_capVars]

end


theorem Ty.mem_tyVarsList_of_mem
    {item : Ty} {items : List Ty} {index : TyVar}
    (itemMember : item ∈ items) (variableMember : index ∈ item.tyVars) :
    index ∈ Ty.tyVarsList items := by
  induction items with
  | nil => cases itemMember
  | cons head tail induction =>
      simp only [List.mem_cons] at itemMember
      simp only [Ty.tyVarsList, List.mem_append]
      rcases itemMember with rfl | tailMember
      · exact Or.inl variableMember
      · exact Or.inr (induction tailMember)

theorem Ty.mem_capVarsList_of_mem
    {item : Ty} {items : List Ty} {index : CapVar}
    (itemMember : item ∈ items) (variableMember : index ∈ item.capVars) :
    index ∈ Ty.capVarsList items := by
  induction items with
  | nil => cases itemMember
  | cons head tail induction =>
      simp only [List.mem_cons] at itemMember
      simp only [Ty.capVarsList, List.mem_append]
      rcases itemMember with rfl | tailMember
      · exact Or.inl variableMember
      · exact Or.inr (induction tailMember)

theorem contextWitness_ty
    (context : Context) {index : TyVar}
    (member : index ∈ context.freeTyVars) :
    index ∈ (contextWitness context).tyVars := by
  have flatMember := mem_dedupFirst.mp member
  obtain ⟨scheme, schemeMember, freeMember⟩ :=
    List.mem_flatMap.mp flatMember
  simp only [contextWitness, Ty.tyVars]
  apply Ty.mem_tyVarsList_of_mem
    (List.mem_map.mpr ⟨scheme, schemeMember, rfl⟩)
  simpa [schemeWitness] using (Scheme.mem_freeTyVars.mp freeMember)

theorem contextWitness_cap
    (context : Context) {index : CapVar}
    (member : index ∈ context.freeCapVars) :
    index ∈ (contextWitness context).capVars := by
  have flatMember := mem_dedupFirst.mp member
  obtain ⟨scheme, schemeMember, freeMember⟩ :=
    List.mem_flatMap.mp flatMember
  simp only [contextWitness, Ty.capVars]
  apply Ty.mem_capVarsList_of_mem
    (List.mem_map.mpr ⟨scheme, schemeMember, rfl⟩)
  simpa [schemeWitness] using (Scheme.mem_freeCapVars.mp freeMember)

theorem closureWitness_ty_of_context
    (context : Context) (target : Ty) {index : TyVar}
    (member : index ∈ context.freeTyVars) :
    .ty index ∈ (closureWitness context target).unificationVars := by
  apply (Ty.mem_tyVars_iff_unificationVars index _).mp
  simp only [closureWitness, Ty.tyVars, Ty.tyVarsList,
    List.mem_append, List.not_mem_nil, or_false]
  exact Or.inl (contextWitness_ty context member)

theorem closureWitness_cap_of_context
    (context : Context) (target : Ty) {index : CapVar}
    (member : index ∈ context.freeCapVars) :
    .cap index ∈ (closureWitness context target).unificationVars := by
  apply (Ty.mem_capVars_iff_unificationVars index _).mp
  simp only [closureWitness, Ty.capVars, Ty.capVarsList,
    List.mem_append, List.not_mem_nil, or_false]
  exact Or.inl (contextWitness_cap context member)

theorem schemeWitness_applyFree
    (scheme : Scheme) (substitution : Subst) :
    schemeWitness (scheme.applyFree substitution) =
      (schemeWitness scheme).apply substitution := by
  exact PolyTy.openBound_applyFree substitution
    (fun _ => .int) (fun _ => .any) scheme.body

theorem contextWitness_applyFree
    (context : Context) (substitution : Subst) :
    contextWitness (context.applyFree substitution) =
      (contextWitness context).apply substitution := by
  induction context with
  | nil => rfl
  | cons scheme context induction =>
      have tailEquality := Ty.prod.inj induction
      change List.map schemeWitness
          (List.map (Scheme.applyFree substitution) context) =
        Ty.applyList substitution
          (List.map schemeWitness context) at tailEquality
      simp only [contextWitness, Context.applyFree, List.map_cons,
        Ty.apply, Ty.applyList, schemeWitness_applyFree]
      rw [tailEquality]

theorem closureWitness_apply
    (context : Context) (target : Ty) (substitution : Subst) :
    closureWitness (context.applyFree substitution)
        (target.apply substitution) =
      (closureWitness context target).apply substitution := by
  simp [closureWitness, contextWitness_applyFree, Ty.apply, Ty.applyList]

/-- The observable closed context and target are fixed by an idempotent
closure substitution. -/
theorem closedClosureWitness_fixed
    {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) (context : Context) :
    (closureWitness (context.applyFree closure.substitution)
        closure.target).apply closure.substitution =
      closureWitness (context.applyFree closure.substitution)
        closure.target := by
  have represented := closureWitness_apply context generated.target
    closure.substitution
  change closureWitness (context.applyFree closure.substitution)
      (generated.target.apply closure.substitution) =
    (closureWitness context generated.target).apply
      closure.substitution at represented
  change
    (closureWitness (context.applyFree closure.substitution)
      (generated.target.apply closure.substitution)).apply
        closure.substitution =
      closureWitness (context.applyFree closure.substitution)
        (generated.target.apply closure.substitution)
  rw [represented, Ty.apply_compose,
    closure.substitution_idempotent absorbing]

end ObservableSupport

namespace BuiltSupport

def ContextContains (context : Context) : UnificationVar → Prop
  | .ty index => index ∈ context.freeTyVars
  | .cap index => index ∈ context.freeCapVars

def SourceContains
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection
      left right forward backward context) : UnificationVar → Prop
  | .ty index => index ∈ data.support.ty.source
  | .cap index => index ∈ data.support.cap.source

/-- Mixed-sort form of the observable support on the right representative. -/
def TargetVariables
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection
      left right forward backward context) : List UnificationVar :=
  data.support.ty.target.map UnificationVar.ty ++
    data.support.cap.target.map UnificationVar.cap

@[simp] theorem ty_mem_targetVariables
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection
      left right forward backward context) (index : TyVar) :
    .ty index ∈ TargetVariables data ↔ index ∈ data.support.ty.target := by
  simp [TargetVariables]

@[simp] theorem cap_mem_targetVariables
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection
      left right forward backward context) (index : CapVar) :
    .cap index ∈ TargetVariables data ↔ index ∈ data.support.cap.target := by
  simp [TargetVariables]

/-- Every variable in the image of an outer context variable belongs to the
constructed observable source support. -/
theorem build_image_covered
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input candidate : UnificationVar)
    (inputMember : ContextContains context input)
    (imageMember : SubstitutionImageContains
      left.substitution input candidate) :
    SourceContains
      (TypePM.Source.ClosureSupportConstruction.build
        transport context) candidate := by
  let original := ObservableSupport.closureWitness context generated.target
  have inputWitness : input ∈ original.unificationVars := by
    cases input with
    | ty index =>
        exact ObservableSupport.closureWitness_ty_of_context
          context generated.target inputMember
    | cap index =>
        exact ObservableSupport.closureWitness_cap_of_context
          context generated.target inputMember
  have appliedMember : candidate ∈
      (original.apply left.substitution).unificationVars :=
    Ty.mem_apply_of_image left.substitution original input candidate
      inputWitness imageMember
  have closedMember : candidate ∈
      (ObservableSupport.closureWitness
        (context.applyFree left.substitution) left.target).unificationVars := by
    rw [← ObservableSupport.closureWitness_apply
      context generated.target left.substitution] at appliedMember
    exact appliedMember
  cases candidate with
  | ty index =>
      change index ∈ dedupFirst
        (ObservableSupport.closureWitness
          (context.applyFree left.substitution) left.target).tyVars
      apply mem_dedupFirst.mpr
      exact (Ty.mem_tyVars_iff_unificationVars index _).mpr closedMember
  | cap index =>
      change index ∈ dedupFirst
        (ObservableSupport.closureWitness
          (context.applyFree left.substitution) left.target).capVars
      apply mem_dedupFirst.mpr
      exact (Ty.mem_capVars_iff_unificationVars index _).mpr closedMember

theorem build_tyImage_ty_covered
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input : TyVar)
    (inputMember : input ∈ context.freeTyVars)
    {candidate : TyVar}
    (imageMember : candidate ∈ (left.substitution.ty input).tyVars) :
    candidate ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.ty.source := by
  apply build_image_covered transport context (.ty input) (.ty candidate)
    inputMember
  exact (Ty.mem_tyVars_iff_unificationVars candidate _).mp imageMember

theorem build_tyImage_cap_covered
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input : TyVar)
    (inputMember : input ∈ context.freeTyVars)
    {candidate : CapVar}
    (imageMember : candidate ∈ (left.substitution.ty input).capVars) :
    candidate ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.source := by
  apply build_image_covered transport context (.ty input) (.cap candidate)
    inputMember
  exact (Ty.mem_capVars_iff_unificationVars candidate _).mp imageMember

theorem build_capImage_cap_covered
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input : CapVar)
    (inputMember : input ∈ context.freeCapVars)
    {candidate : CapVar}
    (imageMember : candidate ∈ (left.substitution.cap input).capVars) :
    candidate ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.source := by
  apply build_image_covered transport context (.cap input) (.cap candidate)
    inputMember
  exact (Cap.mem_capVars_iff_unificationVars candidate _).mp imageMember

/-- On every outer ordinary context variable, the global support renaming
transports the left closure image to the right closure image exactly. -/
theorem build_tyRhs_exact
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input : TyVar)
    (inputMember : input ∈ context.freeTyVars) :
    (left.substitution.ty input).apply
        (TypePM.Source.ClosureSupportConstruction.build
          transport context).globalRenaming.substitution =
      right.substitution.ty input := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  have agrees : (left.substitution.ty input).apply
        data.globalRenaming.substitution =
      (left.substitution.ty input).apply forward := by
    apply Ty.apply_eq_of_agree
    · intro candidate member
      exact data.support.substitution_ty_agrees
        (build_tyImage_ty_covered transport context input inputMember member)
    · intro candidate member
      exact data.support.substitution_cap_agrees
        (build_tyImage_cap_covered transport context input inputMember member)
  have factor := congrArg (fun substitution => substitution.ty input)
    transport.1
  change (left.substitution.ty input).apply forward =
    right.substitution.ty input at factor
  exact agrees.trans factor

/-- Capability-variable counterpart of `build_tyRhs_exact`. -/
theorem build_capRhs_exact
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input : CapVar)
    (inputMember : input ∈ context.freeCapVars) :
    (left.substitution.cap input).apply
        (TypePM.Source.ClosureSupportConstruction.build
          transport context).globalRenaming.substitution.cap =
      right.substitution.cap input := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  have agrees : (left.substitution.cap input).apply
        data.globalRenaming.substitution.cap =
      (left.substitution.cap input).apply forward.cap := by
    apply Cap.apply_eq_of_agree
    intro candidate member
    exact data.support.substitution_cap_agrees
      (build_capImage_cap_covered transport context input inputMember member)
  have factor := congrArg (fun substitution => substitution.cap input)
    transport.1
  change (left.substitution.cap input).apply forward.cap =
    right.substitution.cap input at factor
  exact agrees.trans factor

/-- Every ordinary variable in the constructed left observable support is
fixed by the left closure substitution. -/
theorem build_tySource_fixed
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (context : Context) (index : TyVar)
    (member : index ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.ty.source) :
    left.substitution.ty index = .var index := by
  change index ∈ dedupFirst
    (ObservableSupport.closureWitness
      (context.applyFree left.substitution) left.target).tyVars at member
  have variableMember := (Ty.mem_tyVars_iff_unificationVars index _).mp
    (mem_dedupFirst.mp member)
  exact Ty.substitutionFixes_of_mem_apply_eq left.substitution _
    (ObservableSupport.closedClosureWitness_fixed left leftAbsorbing context)
    (.ty index) variableMember

/-- Capability-variable counterpart of `build_tySource_fixed`. -/
theorem build_capSource_fixed
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (context : Context) (index : CapVar)
    (member : index ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.source) :
    left.substitution.cap index = .var index := by
  change index ∈ dedupFirst
    (ObservableSupport.closureWitness
      (context.applyFree left.substitution) left.target).capVars at member
  have variableMember := (Ty.mem_capVars_iff_unificationVars index _).mp
    (mem_dedupFirst.mp member)
  exact Ty.substitutionFixes_of_mem_apply_eq left.substitution _
    (ObservableSupport.closedClosureWitness_fixed left leftAbsorbing context)
    (.cap index) variableMember

/-- A target-support ordinary name is fixed by the right closure. -/
theorem build_tyTarget_fixed
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (index : TyVar)
    (member : index ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.ty.target) :
    right.substitution.ty index = .var index := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  let source := data.support.ty.backward index
  have sourceMember : source ∈ data.support.ty.source :=
    data.support.ty.backward_mem member
  have sourceFixed : left.substitution.ty source = .var source :=
    build_tySource_fixed transport leftAbsorbing context source sourceMember
  have factor := congrArg (fun substitution => substitution.ty source)
    transport.1
  change (left.substitution.ty source).apply forward =
    right.substitution.ty source at factor
  have forwardImage : forward.ty source =
      .var (data.support.ty.forward source) :=
    data.support.ty_forward sourceMember
  have rightImage : right.substitution.ty source = .var index := by
    rw [sourceFixed, Ty.apply, forwardImage,
      data.support.ty.forward_backward member] at factor
    exact factor.symm
  change SubstitutionFixes right.substitution (.ty index)
  apply SubstitutionFixes.of_tyImage
    (right.substitution_idempotent rightAbsorbing) source
  rw [rightImage]
  simp [Ty.unificationVars]

/-- Capability-variable counterpart of `build_tyTarget_fixed`. -/
theorem build_capTarget_fixed
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (index : CapVar)
    (member : index ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.target) :
    right.substitution.cap index = .var index := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  let source := data.support.cap.backward index
  have sourceMember : source ∈ data.support.cap.source :=
    data.support.cap.backward_mem member
  have sourceFixed : left.substitution.cap source = .var source :=
    build_capSource_fixed transport leftAbsorbing context source sourceMember
  have factor := congrArg (fun substitution => substitution.cap source)
    transport.1
  change (left.substitution.cap source).apply forward.cap =
    right.substitution.cap source at factor
  have forwardImage : forward.cap source =
      .var (data.support.cap.forward source) :=
    data.support.cap_forward sourceMember
  have rightImage : right.substitution.cap source = .var index := by
    rw [sourceFixed, Cap.apply, forwardImage,
      data.support.cap.forward_backward member] at factor
    exact factor.symm
  change SubstitutionFixes right.substitution (.cap index)
  apply SubstitutionFixes.of_capImage
    (right.substitution_idempotent rightAbsorbing) source
  rw [rightImage]
  simp [Cap.unificationVars]

/-- A moved source-support endpoint cannot also be a target-support endpoint.
Otherwise absorption fixes it on both representatives while exact RHS
transport says that the global renaming moves it. -/
theorem build_tyMovedSource_not_target
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (index : TyVar)
    (contextMember : index ∈ context.freeTyVars)
    (sourceMember : index ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.ty.source)
    (moved : (TypePM.Source.ClosureSupportConstruction.build
      transport context).globalRenaming.tyForward index ≠ index) :
    index ∉ (TypePM.Source.ClosureSupportConstruction.build
      transport context).support.ty.target := by
  intro targetMember
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  have leftFixed := build_tySource_fixed transport leftAbsorbing context
    index sourceMember
  have rightFixed := build_tyTarget_fixed transport leftAbsorbing
    rightAbsorbing context index targetMember
  have exact := build_tyRhs_exact transport context index contextMember
  have variableFixed :
      Ty.var (data.globalRenaming.tyForward index) = Ty.var index := by
    simpa only [data, leftFixed, rightFixed, VariableRenaming.substitution,
      Ty.apply] using exact
  have fixed : data.globalRenaming.tyForward index = index :=
    Ty.var.inj variableFixed
  exact moved fixed

/-- Target-only inputs have images outside the target support.  This follows
from injectivity of the global extension and exact agreement with the finite
partial bijection. -/
theorem build_tyForward_not_target_of_not_source
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (index : TyVar)
    (outsideSource : index ∉
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.ty.source) :
    (TypePM.Source.ClosureSupportConstruction.build
        transport context).globalRenaming.tyForward index ∉
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.ty.target := by
  intro imageMember
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  have sourceMember := data.support.ty.backward_mem imageMember
  have backwardExact := data.support.tyBackward_agrees imageMember
  have restored : data.support.ty.backward
      (data.globalRenaming.tyForward index) = index := by
    rw [← backwardExact]
    exact data.globalRenaming.ty_backward_forward index
  rw [restored] at sourceMember
  exact outsideSource sourceMember

theorem build_capMovedSource_not_target
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (index : CapVar)
    (contextMember : index ∈ context.freeCapVars)
    (sourceMember : index ∈
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.source)
    (moved : (TypePM.Source.ClosureSupportConstruction.build
      transport context).globalRenaming.capForward index ≠ index) :
    index ∉ (TypePM.Source.ClosureSupportConstruction.build
      transport context).support.cap.target := by
  intro targetMember
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  have leftFixed := build_capSource_fixed transport leftAbsorbing context
    index sourceMember
  have rightFixed := build_capTarget_fixed transport leftAbsorbing
    rightAbsorbing context index targetMember
  have exact := build_capRhs_exact transport context index contextMember
  have variableFixed :
      Cap.var (data.globalRenaming.capForward index) = Cap.var index := by
    simpa only [data, leftFixed, rightFixed, VariableRenaming.substitution,
      Cap.apply] using exact
  have fixed : data.globalRenaming.capForward index = index :=
    Cap.var.inj variableFixed
  exact moved fixed

theorem build_capForward_not_target_of_not_source
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (index : CapVar)
    (outsideSource : index ∉
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.source) :
    (TypePM.Source.ClosureSupportConstruction.build
        transport context).globalRenaming.capForward index ∉
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.target := by
  intro imageMember
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  have sourceMember := data.support.cap.backward_mem imageMember
  have backwardExact := data.support.capBackward_agrees imageMember
  have restored : data.support.cap.backward
      (data.globalRenaming.capForward index) = index := by
    rw [← backwardExact]
    exact data.globalRenaming.cap_backward_forward index
  rw [restored] at sourceMember
  exact outsideSource sourceMember

/-- Outside both finite endpoint supports, the constructed ordinary-name
renaming is the identity. -/
theorem build_tyForward_fixed_outside
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (index : TyVar)
    (outsideSource : index ∉
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.ty.source)
    (outsideTarget : index ∉
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.ty.target) :
    (TypePM.Source.ClosureSupportConstruction.build
      transport context).globalRenaming.tyForward index = index := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  exact (FinitePartialExtension.extend_fixed_outside'
    data.support.ty index outsideSource outsideTarget).1

/-- Capability-variable counterpart of `build_tyForward_fixed_outside`. -/
theorem build_capForward_fixed_outside
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (index : CapVar)
    (outsideSource : index ∉
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.source)
    (outsideTarget : index ∉
      (TypePM.Source.ClosureSupportConstruction.build
        transport context).support.cap.target) :
    (TypePM.Source.ClosureSupportConstruction.build
      transport context).globalRenaming.capForward index = index := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  exact (FinitePartialExtension.extend_fixed_outside'
    data.support.cap index outsideSource outsideTarget).1

end BuiltSupport

namespace Automatic

open EquationLists
open AliasFreshness

/-- A pointwise interface shape together with the support facts needed for
all aliases selected by that shape.  Duplicate-freedom is deliberately kept
separate and follows from the concrete interface left-hand sides. -/
structure EndpointScopedShape
    (support : List UnificationVar) (left right : List Equation) where
  shape : PairwiseAliasShape left right
  leftEndpoints : ∀ alias,
    alias ∈ shape.toEquationCommonCore.leftAliases →
      freshVariable alias ∉ support ∧ existingVariable alias ∈ support
  rightEndpoints : ∀ alias,
    alias ∈ shape.toEquationCommonCore.rightAliases →
      freshVariable alias ∉ support ∧ existingVariable alias ∈ support

namespace EndpointScopedShape

noncomputable def nil (support : List UnificationVar) :
    EndpointScopedShape support [] [] :=
  ⟨.nil,
    by
      intro alias member
      simp [PairwiseAliasShape.toEquationCommonCore,
        EquationCommonCore.refl] at member,
    by
      intro alias member
      simp [PairwiseAliasShape.toEquationCommonCore,
        EquationCommonCore.refl] at member⟩

noncomputable def same
    {support : List UnificationVar} {left right : List Equation}
    (equation : Equation) (tail : EndpointScopedShape support left right) :
    EndpointScopedShape support (equation :: left) (equation :: right) := by
  refine ⟨.same equation tail.shape, ?_, ?_⟩
  · change ∀ alias, alias ∈ tail.shape.toEquationCommonCore.leftAliases → _
    exact tail.leftEndpoints
  · change ∀ alias, alias ∈ tail.shape.toEquationCommonCore.rightAliases → _
    exact tail.rightEndpoints

noncomputable def tyAliasRefl
    {support : List UnificationVar} {left right : List Equation}
    (fresh existing : TyVar) (tail : EndpointScopedShape support left right)
    (freshOutside : .ty fresh ∉ support)
    (existingInside : .ty existing ∈ support) :
    EndpointScopedShape support
      (.ty (.var fresh) (.var existing) :: left)
      (.ty (.var existing) (.var existing) :: right) := by
  refine ⟨.tyAliasRefl fresh existing tail.shape, ?_, ?_⟩
  · change ∀ alias,
      alias ∈ tail.shape.toEquationCommonCore.leftAliases ++
        [FreshAliasSequence.Alias.ty fresh existing] → _
    intro alias member
    rcases List.mem_append.mp member with old | current
    · exact tail.leftEndpoints alias old
    · have equality : alias = .ty fresh existing := by simpa using current
      subst alias
      exact ⟨freshOutside, existingInside⟩
  · change ∀ alias, alias ∈ tail.shape.toEquationCommonCore.rightAliases → _
    exact tail.rightEndpoints

noncomputable def tyReflAlias
    {support : List UnificationVar} {left right : List Equation}
    (fresh existing : TyVar) (tail : EndpointScopedShape support left right)
    (freshOutside : .ty fresh ∉ support)
    (existingInside : .ty existing ∈ support) :
    EndpointScopedShape support
      (.ty (.var existing) (.var existing) :: left)
      (.ty (.var fresh) (.var existing) :: right) := by
  refine ⟨.tyReflAlias fresh existing tail.shape, ?_, ?_⟩
  · change ∀ alias, alias ∈ tail.shape.toEquationCommonCore.leftAliases → _
    exact tail.leftEndpoints
  · change ∀ alias,
      alias ∈ tail.shape.toEquationCommonCore.rightAliases ++
        [FreshAliasSequence.Alias.ty fresh existing] → _
    intro alias member
    rcases List.mem_append.mp member with old | current
    · exact tail.rightEndpoints alias old
    · have equality : alias = .ty fresh existing := by simpa using current
      subst alias
      exact ⟨freshOutside, existingInside⟩

noncomputable def capAliasRefl
    {support : List UnificationVar} {left right : List Equation}
    (fresh existing : CapVar) (tail : EndpointScopedShape support left right)
    (freshOutside : .cap fresh ∉ support)
    (existingInside : .cap existing ∈ support) :
    EndpointScopedShape support
      (.cap (.var fresh) (.var existing) :: left)
      (.cap (.var existing) (.var existing) :: right) := by
  refine ⟨.capAliasRefl fresh existing tail.shape, ?_, ?_⟩
  · change ∀ alias,
      alias ∈ tail.shape.toEquationCommonCore.leftAliases ++
        [FreshAliasSequence.Alias.cap fresh existing] → _
    intro alias member
    rcases List.mem_append.mp member with old | current
    · exact tail.leftEndpoints alias old
    · have equality : alias = .cap fresh existing := by simpa using current
      subst alias
      exact ⟨freshOutside, existingInside⟩
  · change ∀ alias, alias ∈ tail.shape.toEquationCommonCore.rightAliases → _
    exact tail.rightEndpoints

noncomputable def capReflAlias
    {support : List UnificationVar} {left right : List Equation}
    (fresh existing : CapVar) (tail : EndpointScopedShape support left right)
    (freshOutside : .cap fresh ∉ support)
    (existingInside : .cap existing ∈ support) :
    EndpointScopedShape support
      (.cap (.var existing) (.var existing) :: left)
      (.cap (.var fresh) (.var existing) :: right) := by
  refine ⟨.capReflAlias fresh existing tail.shape, ?_, ?_⟩
  · change ∀ alias, alias ∈ tail.shape.toEquationCommonCore.leftAliases → _
    exact tail.leftEndpoints
  · change ∀ alias,
      alias ∈ tail.shape.toEquationCommonCore.rightAliases ++
        [FreshAliasSequence.Alias.cap fresh existing] → _
    intro alias member
    rcases List.mem_append.mp member with old | current
    · exact tail.rightEndpoints alias old
    · have equality : alias = .cap fresh existing := by simpa using current
      subst alias
      exact ⟨freshOutside, existingInside⟩

theorem scopedBy
    {support : List UnificationVar} {left right : List Equation}
    (certificate : EndpointScopedShape support left right)
    (leftNodup : (EquationLists.equationLeftVariables left).Nodup)
    (rightNodup : (EquationLists.equationLeftVariables right).Nodup) :
    ScopedBy support certificate.shape.toEquationCommonCore.leftAliases ∧
      ScopedBy support certificate.shape.toEquationCommonCore.rightAliases :=
  ⟨⟨certificate.shape.leftAliases_fresh_nodup leftNodup,
      certificate.leftEndpoints⟩,
    ⟨certificate.shape.rightAliases_fresh_nodup rightNodup,
      certificate.rightEndpoints⟩⟩

end EndpointScopedShape

noncomputable def tyInterfaceShape
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (indices : List TyVar)
    (covered : ∀ index, index ∈ indices →
      index ∈ context.freeTyVars) :
    EquationLists.PairwiseAliasShape
      ((indices.map fun index =>
          Equation.ty (.var index) (left.substitution.ty index)).map
        (ElaborationRenaming.renameEquation
          (TypePM.Source.ClosureSupportConstruction.build
            transport context).globalRenaming))
      (indices.map fun index =>
        Equation.ty (.var index) (right.substitution.ty index)) := by
  induction indices with
  | nil => exact .nil
  | cons index indices induction =>
      have indexMember : index ∈ context.freeTyVars :=
        covered index (by simp)
      have tailCovered : ∀ candidate, candidate ∈ indices →
          candidate ∈ context.freeTyVars := by
        intro candidate member
        exact covered candidate (by simp [member])
      let tail := induction tailCovered
      let data := TypePM.Source.ClosureSupportConstruction.build
        transport context
      have rhsExact := BuiltSupport.build_tyRhs_exact
        transport context index indexMember
      have rhsExactData :
          (left.substitution.ty index).apply
              data.globalRenaming.substitution =
            right.substitution.ty index := by
        simpa only [data] using rhsExact
      have renamedHead :
          ElaborationRenaming.renameEquation data.globalRenaming
              (.ty (.var index) (left.substitution.ty index)) =
            .ty (.var (data.globalRenaming.tyForward index))
              (right.substitution.ty index) := by
        change
          Equation.ty (.var (data.globalRenaming.tyForward index))
              ((left.substitution.ty index).apply
                data.globalRenaming.substitution) =
            Equation.ty (.var (data.globalRenaming.tyForward index))
              (right.substitution.ty index)
        rw [rhsExactData]
      simp only [List.map_cons]
      rw [renamedHead]
      by_cases sourceMember : index ∈ data.support.ty.source
      · have leftFixed := BuiltSupport.build_tySource_fixed
          transport leftAbsorbing context index sourceMember
        have rightImage : right.substitution.ty index =
            .var (data.globalRenaming.tyForward index) := by
          simpa [leftFixed, VariableRenaming.substitution, Ty.apply] using
            rhsExact.symm
        by_cases same : data.globalRenaming.tyForward index = index
        · simpa [rightImage, same] using
            (EquationLists.PairwiseAliasShape.same
              (.ty (.var index) (.var index)) tail)
        · simpa [rightImage] using
            (EquationLists.PairwiseAliasShape.tyReflAlias
              index (data.globalRenaming.tyForward index) tail)
      · by_cases targetMember : index ∈ data.support.ty.target
        · have rightFixed := BuiltSupport.build_tyTarget_fixed
            transport leftAbsorbing rightAbsorbing context index targetMember
          by_cases same : data.globalRenaming.tyForward index = index
          · simpa [rightFixed, same] using
              (EquationLists.PairwiseAliasShape.same
                (.ty (.var index) (.var index)) tail)
          · simpa [rightFixed] using
              (EquationLists.PairwiseAliasShape.tyAliasRefl
                (data.globalRenaming.tyForward index) index tail)
        · have fixed := BuiltSupport.build_tyForward_fixed_outside
            transport context index sourceMember targetMember
          have fixedData : data.globalRenaming.tyForward index = index := by
            simpa only [data] using fixed
          simpa [fixedData] using
            (EquationLists.PairwiseAliasShape.same
              (.ty (.var index) (right.substitution.ty index)) tail)

noncomputable def capInterfaceShape
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (indices : List CapVar)
    (covered : ∀ index, index ∈ indices →
      index ∈ context.freeCapVars) :
    EquationLists.PairwiseAliasShape
      ((indices.map fun index =>
          Equation.cap (.var index) (left.substitution.cap index)).map
        (ElaborationRenaming.renameEquation
          (TypePM.Source.ClosureSupportConstruction.build
            transport context).globalRenaming))
      (indices.map fun index =>
        Equation.cap (.var index) (right.substitution.cap index)) := by
  induction indices with
  | nil => exact .nil
  | cons index indices induction =>
      have indexMember : index ∈ context.freeCapVars :=
        covered index (by simp)
      have tailCovered : ∀ candidate, candidate ∈ indices →
          candidate ∈ context.freeCapVars := by
        intro candidate member
        exact covered candidate (by simp [member])
      let tail := induction tailCovered
      let data := TypePM.Source.ClosureSupportConstruction.build
        transport context
      have rhsExact := BuiltSupport.build_capRhs_exact
        transport context index indexMember
      have rhsExactData :
          (left.substitution.cap index).apply
              data.globalRenaming.substitution.cap =
            right.substitution.cap index := by
        simpa only [data] using rhsExact
      have renamedHead :
          ElaborationRenaming.renameEquation data.globalRenaming
              (.cap (.var index) (left.substitution.cap index)) =
            .cap (.var (data.globalRenaming.capForward index))
              (right.substitution.cap index) := by
        change
          Equation.cap (.var (data.globalRenaming.capForward index))
              ((left.substitution.cap index).apply
                data.globalRenaming.substitution.cap) =
            Equation.cap (.var (data.globalRenaming.capForward index))
              (right.substitution.cap index)
        rw [rhsExactData]
      simp only [List.map_cons]
      rw [renamedHead]
      by_cases sourceMember : index ∈ data.support.cap.source
      · have leftFixed := BuiltSupport.build_capSource_fixed
          transport leftAbsorbing context index sourceMember
        have rightImage : right.substitution.cap index =
            .var (data.globalRenaming.capForward index) := by
          simpa [leftFixed, VariableRenaming.substitution, Cap.apply] using
            rhsExact.symm
        by_cases same : data.globalRenaming.capForward index = index
        · simpa [rightImage, same] using
            (EquationLists.PairwiseAliasShape.same
              (.cap (.var index) (.var index)) tail)
        · simpa [rightImage] using
            (EquationLists.PairwiseAliasShape.capReflAlias
              index (data.globalRenaming.capForward index) tail)
      · by_cases targetMember : index ∈ data.support.cap.target
        · have rightFixed := BuiltSupport.build_capTarget_fixed
            transport leftAbsorbing rightAbsorbing context index targetMember
          by_cases same : data.globalRenaming.capForward index = index
          · simpa [rightFixed, same] using
              (EquationLists.PairwiseAliasShape.same
                (.cap (.var index) (.var index)) tail)
          · simpa [rightFixed] using
              (EquationLists.PairwiseAliasShape.capAliasRefl
                (data.globalRenaming.capForward index) index tail)
        · have fixed := BuiltSupport.build_capForward_fixed_outside
            transport context index sourceMember targetMember
          have fixedData : data.globalRenaming.capForward index = index := by
            simpa only [data] using fixed
          simpa [fixedData] using
            (EquationLists.PairwiseAliasShape.same
              (.cap (.var index) (right.substitution.cap index)) tail)

/-- Automatic pointwise classification of the full two-sorted context
interface. -/
noncomputable def interfaceShape
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    EquationLists.PairwiseAliasShape
      ((context.interfaceEquations left.substitution).map
        (ElaborationRenaming.renameEquation
          (TypePM.Source.ClosureSupportConstruction.build
            transport context).globalRenaming))
      (context.interfaceEquations right.substitution) := by
  let tyShape := tyInterfaceShape transport leftAbsorbing rightAbsorbing
    context context.freeTyVars (fun _ member => member)
  let capShape := capInterfaceShape transport leftAbsorbing rightAbsorbing
    context context.freeCapVars (fun _ member => member)
  simpa [Context.interfaceEquations, List.map_append] using
    EquationLists.PairwiseAliasShape.append tyShape capShape

/-- Pure hard-equation decomposition obtained automatically from the two
absorbing representatives. -/
noncomputable def equationCommonCore
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    EquationLists.EquationCommonCore
      ((context.interfaceEquations left.substitution).map
        (ElaborationRenaming.renameEquation
          (TypePM.Source.ClosureSupportConstruction.build
            transport context).globalRenaming))
      (context.interfaceEquations right.substitution) :=
  EquationLists.PairwiseAliasShape.toEquationCommonCore
    (interfaceShape transport leftAbsorbing rightAbsorbing context)

end Automatic

/-- One package keeps the acceptance-facing interface decomposition together
with exact context, closure-target, and generalized-scheme transport.  The
`target_exact` field is the extra endpoint needed by principality; it does not
follow merely from block-acceptance equivalence. -/
structure ClosureInterfaceDecomposition
    {generated : Generated}
    (left right : PrincipalBlockClosure generated)
    (context : Context) where
  rho : VariableRenaming
  closedContext_exact :
    (context.applyFree left.substitution).applyFree rho.substitution =
      context.applyFree right.substitution
  target_exact : left.target.apply rho.substitution = right.target
  generalized_exact :
    ((context.applyFree left.substitution).generalize left.target).applyFree
        rho.substitution =
      (context.applyFree right.substitution).generalize right.target
  equations : EquationLists.EquationCommonCore
    ((context.interfaceEquations left.substitution).map
      (ElaborationRenaming.renameEquation rho))
    (context.interfaceEquations right.substitution)

namespace ClosureInterfaceDecomposition

/-- A two-sort variable renaming is a substitution instance in both
directions.  Keeping this elementary fact next to the interface package makes
the target-level consequence of `target_exact` available without appealing
to block acceptance. -/
theorem renameTy_mutualInstances
    (rho : VariableRenaming) (target : Ty) :
    IsInstance target (ElaborationRenaming.renameTy rho target) ∧
      IsInstance (ElaborationRenaming.renameTy rho target) target := by
  constructor
  · exact ⟨rho.substitution, rfl⟩
  · exact ⟨rho.symm.substitution, by
      exact ElaborationRenaming.renameTy_symm_apply rho target⟩

/-- Exact closure-target transport therefore yields mutual substitution
instances of the two closure targets. -/
theorem targets_mutualInstances
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {context : Context}
    (decomposition : ClosureInterfaceDecomposition left right context) :
    IsInstance left.target right.target ∧
      IsInstance right.target left.target := by
  rw [← decomposition.target_exact]
  exact renameTy_mutualInstances decomposition.rho left.target

/-- Fully automatic equation-level decomposition for two absorbing principal
closures of the same generated right-hand side. -/
noncomputable def build
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    ClosureInterfaceDecomposition left right context := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  exact
    { rho := data.globalRenaming
      closedContext_exact := data.closedContext_exact
      target_exact := data.target_exact
      generalized_exact := data.generalized_exact
      equations := Automatic.equationCommonCore
        transport leftAbsorbing rightAbsorbing context }

/-- Upgrade the automatic pure decomposition to the general-pending
acceptance certificate once source-specific body freshness is supplied for
the two finite alias sequences. -/
theorem toFreshAliasCommonCore
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {context : Context}
    (decomposition : ClosureInterfaceDecomposition left right context)
    (body : Generated)
    (leftAdmissible : FreshAliasSequence.Admissible
      decomposition.equations.leftAliases
      (Generated.fromLet decomposition.equations.core body))
    (rightAdmissible : FreshAliasSequence.Admissible
      decomposition.equations.rightAliases
      (Generated.fromLet decomposition.equations.core body)) :
    FreshAliasSequence.CommonCoreEquivalent
      (Generated.fromLet
        ((context.interfaceEquations left.substitution).map
          (ElaborationRenaming.renameEquation decomposition.rho)) body)
      (Generated.fromLet
        (context.interfaceEquations right.substitution) body) :=
  decomposition.equations.toFreshAliasCommonCore body
    leftAdmissible rightAdmissible

/-- Source-facing endpoint: rename the complete left `fromLet` block, then
remove the finite symmetric interface aliases.  Freshness is required only
for the already-renamed body block. -/
theorem fromLet_blockAccepts_iff
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {context : Context}
    (decomposition : ClosureInterfaceDecomposition left right context)
    (body : Generated)
    (leftAdmissible : FreshAliasSequence.Admissible
      decomposition.equations.leftAliases
      (Generated.fromLet decomposition.equations.core
        (ElaborationRenaming.renameGenerated decomposition.rho body)))
    (rightAdmissible : FreshAliasSequence.Admissible
      decomposition.equations.rightAliases
      (Generated.fromLet decomposition.equations.core
        (ElaborationRenaming.renameGenerated decomposition.rho body))) :
    BlockAccepts
        (Generated.fromLet
          (context.interfaceEquations left.substitution) body) ↔
      BlockAccepts
        (Generated.fromLet
          (context.interfaceEquations right.substitution)
          (ElaborationRenaming.renameGenerated decomposition.rho body)) := by
  let leftBlock := Generated.fromLet
    (context.interfaceEquations left.substitution) body
  have renamedAcceptance :=
    ElaborationRenaming.blockAccepts_renameVariables_iff
      decomposition.rho leftBlock
  have interfaceAcceptance :=
    (decomposition.toFreshAliasCommonCore
      (ElaborationRenaming.renameGenerated decomposition.rho body)
      leftAdmissible rightAdmissible).blockAccepts_iff
  exact renamedAcceptance.trans (by
    simpa [leftBlock, ElaborationRenaming.renameGenerated_fromLet] using
      interfaceAcceptance)

/-- The enclosing `let` target is transported exactly by the same renaming;
this is separate from acceptance and is the target-level probe needed by a
principality argument. -/
theorem fromLet_target_exact
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {context : Context}
    (decomposition : ClosureInterfaceDecomposition left right context)
    (body : Generated) :
    (Generated.fromLet
      (context.interfaceEquations right.substitution)
      (ElaborationRenaming.renameGenerated decomposition.rho body)).target =
    ElaborationRenaming.renameTy decomposition.rho
      (Generated.fromLet
        (context.interfaceEquations left.substitution) body).target := by
  rfl

end ClosureInterfaceDecomposition

/-! The existing directional counterexample must remain positive through the
symmetric common-core API. -/

def interfaceAliasCounterexample_regression :=
  InterfaceAliasCounterexample.commonCoreEquivalent_positive

end TypePM.Source.InterfaceAliasDecomposition
