import TypePM.Source.BodyRenamingSemantics

/-!
# Transporting finite aliases through a variable renaming

The left aliases of a transported body certificate are stated over the
renamed body.  Pulling both endpoints back through the inverse renaming
produces aliases whose existing endpoints belong to the original body
support.  This module provides the exact commuting and scope facts needed
to use that presentation at a whole-`let` boundary.
-/

namespace TypePM.Source

namespace AliasRenamingTransport

open InterfaceAliasDecomposition.AliasFreshness
open FreshAliasPrincipalClosure

def renameVariable (rho : VariableRenaming) : UnificationVar → UnificationVar
  | .ty index => .ty (rho.tyForward index)
  | .cap index => .cap (rho.capForward index)

def renameAlias (rho : VariableRenaming) :
    FreshAliasSequence.Alias → FreshAliasSequence.Alias
  | .ty fresh existing => .ty (rho.tyForward fresh) (rho.tyForward existing)
  | .cap fresh existing => .cap (rho.capForward fresh) (rho.capForward existing)

def renameAliases (rho : VariableRenaming)
    (aliases : List FreshAliasSequence.Alias) :
    List FreshAliasSequence.Alias :=
  aliases.map (renameAlias rho)

private theorem append_congr {left left' right right' : List α}
    (leftEq : left = left') (rightEq : right = right') :
    left ++ right = left' ++ right' := by
  rw [leftEq, rightEq]

@[simp] theorem renameVariable_symm_apply
    (rho : VariableRenaming) (candidate : UnificationVar) :
    renameVariable rho.symm (renameVariable rho candidate) = candidate := by
  cases candidate <;> simp [renameVariable]

theorem renameVariable_injective (rho : VariableRenaming) :
    Function.Injective (renameVariable rho) := by
  intro left right equality
  have restored := congrArg (renameVariable rho.symm) equality
  rw [renameVariable_symm_apply, renameVariable_symm_apply] at restored
  exact restored

@[simp] theorem variableRenaming_symm_symm (rho : VariableRenaming) :
    rho.symm.symm = rho := rfl

@[simp] theorem renameAlias_symm_apply
    (rho : VariableRenaming) (alias : FreshAliasSequence.Alias) :
    renameAlias rho.symm (renameAlias rho alias) = alias := by
  cases alias <;> simp [renameAlias]

@[simp] theorem renameAliases_symm_apply
    (rho : VariableRenaming) (aliases : List FreshAliasSequence.Alias) :
    renameAliases rho.symm (renameAliases rho aliases) = aliases := by
  simp [renameAliases, List.map_map, Function.comp_def]

@[simp] theorem renameVariable_apply_symm
    (rho : VariableRenaming) (candidate : UnificationVar) :
    renameVariable rho (renameVariable rho.symm candidate) = candidate := by
  simpa using renameVariable_symm_apply rho.symm candidate

@[simp] theorem renameAlias_apply_symm
    (rho : VariableRenaming) (alias : FreshAliasSequence.Alias) :
    renameAlias rho (renameAlias rho.symm alias) = alias := by
  simpa using renameAlias_symm_apply rho.symm alias

@[simp] theorem renameAliases_apply_symm
    (rho : VariableRenaming) (aliases : List FreshAliasSequence.Alias) :
    renameAliases rho (renameAliases rho.symm aliases) = aliases := by
  simp [renameAliases, List.map_map, Function.comp_def]

@[simp] theorem freshVariable_renameAlias
    (rho : VariableRenaming) (alias : FreshAliasSequence.Alias) :
    freshVariable (renameAlias rho alias) =
      renameVariable rho (freshVariable alias) := by
  cases alias <;> rfl

@[simp] theorem existingVariable_renameAlias
    (rho : VariableRenaming) (alias : FreshAliasSequence.Alias) :
    existingVariable (renameAlias rho alias) =
      renameVariable rho (existingVariable alias) := by
  cases alias <;> rfl

@[simp] theorem renameGenerated_add
    (rho : VariableRenaming) (alias : FreshAliasSequence.Alias)
    (body : Generated) :
    ElaborationRenaming.renameGenerated rho (alias.add body) =
      (renameAlias rho alias).add
        (ElaborationRenaming.renameGenerated rho body) := by
  cases alias <;> cases body <;>
    simp [FreshAliasSequence.Alias.add,
      FreshAliasElimination.addTyAlias,
      FreshAliasElimination.addCapAlias,
      ElaborationRenaming.renameGenerated,
      ElaborationRenaming.renameEquation,
      ElaborationRenaming.renameTy, Equation.apply,
      VariableRenaming.substitution, Ty.apply, Cap.apply,
      renameAlias]

@[simp] theorem renameGenerated_addAll
    (rho : VariableRenaming) (aliases : List FreshAliasSequence.Alias)
    (body : Generated) :
    ElaborationRenaming.renameGenerated rho
        (FreshAliasSequence.addAll aliases body) =
      FreshAliasSequence.addAll (renameAliases rho aliases)
        (ElaborationRenaming.renameGenerated rho body) := by
  induction aliases generalizing body with
  | nil => rfl
  | cons alias aliases induction =>
      simp only [FreshAliasSequence.addAll, renameAliases, List.map_cons,
        induction, renameGenerated_add]

mutual

private theorem capSupport_rename
    (rho : VariableRenaming) (capability : Cap) :
    (ElaborationRenaming.renameCap rho capability).unificationVars =
      capability.unificationVars.map (renameVariable rho) := by
  cases capability with
  | any => rfl
  | var index => rfl
  | prod items => exact capListSupport_rename rho items
  | con former arguments => exact capListSupport_rename rho arguments

private theorem capListSupport_rename
    (rho : VariableRenaming) (items : List Cap) :
    Cap.unificationVarsList (Cap.applyList rho.substitution.cap items) =
      (Cap.unificationVarsList items).map (renameVariable rho) := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [Cap.applyList, Cap.unificationVarsList, List.map_append]
      exact append_congr
        (capSupport_rename rho item) (capListSupport_rename rho items)

end

mutual

private theorem tySupport_rename
    (rho : VariableRenaming) (target : Ty) :
    (ElaborationRenaming.renameTy rho target).unificationVars =
      target.unificationVars.map (renameVariable rho) := by
  cases target with
  | var index => rfl
  | int => rfl
  | fn domain codomain =>
      simpa [ElaborationRenaming.renameTy, Ty.apply, Ty.unificationVars,
        List.map_append] using append_congr
          (tySupport_rename rho domain) (tySupport_rename rho codomain)
  | prod items => exact tyListSupport_rename rho items
  | data former arguments => exact tyListSupport_rename rho arguments
  | matcher capability target =>
      simpa [ElaborationRenaming.renameTy, ElaborationRenaming.renameCap,
        Ty.apply, Ty.unificationVars, List.map_append] using append_congr
          (capSupport_rename rho capability) (tySupport_rename rho target)
  | slot capability target =>
      simpa [ElaborationRenaming.renameTy, ElaborationRenaming.renameCap,
        Ty.apply, Ty.unificationVars, List.map_append] using append_congr
          (capSupport_rename rho capability) (tySupport_rename rho target)

private theorem tyListSupport_rename
    (rho : VariableRenaming) (items : List Ty) :
    Ty.unificationVarsList (Ty.applyList rho.substitution items) =
      (Ty.unificationVarsList items).map (renameVariable rho) := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [Ty.applyList, Ty.unificationVarsList, List.map_append]
      exact append_congr
        (tySupport_rename rho item) (tyListSupport_rename rho items)

end


private theorem equationSupport_rename
    (rho : VariableRenaming) (equation : Equation) :
    (ElaborationRenaming.renameEquation rho equation).unificationVars =
      equation.unificationVars.map (renameVariable rho) := by
  cases equation with
  | ty left right =>
      simpa [ElaborationRenaming.renameEquation, Equation.apply,
        Equation.unificationVars, ElaborationRenaming.renameTy,
        List.map_append] using append_congr
          (tySupport_rename rho left) (tySupport_rename rho right)
  | cap left right =>
      simpa [ElaborationRenaming.renameEquation, Equation.apply,
        Equation.unificationVars, ElaborationRenaming.renameCap,
        List.map_append] using append_congr
          (capSupport_rename rho left) (capSupport_rename rho right)

private theorem equationListSupport_rename
    (rho : VariableRenaming) (equations : List Equation) :
    TypePM.unificationVars
        (equations.map (ElaborationRenaming.renameEquation rho)) =
      (TypePM.unificationVars equations).map (renameVariable rho) := by
  induction equations with
  | nil => rfl
  | cons equation equations induction =>
      simp only [List.map_cons, TypePM.unificationVars, List.map_append]
      exact append_congr
        (equationSupport_rename rho equation) induction

private theorem obligationSupport_rename
    (rho : VariableRenaming) (obligation : CheckObligation) :
    (ElaborationRenaming.renameObligation rho obligation).unificationVars =
      obligation.unificationVars.map (renameVariable rho) := by
  cases obligation with
  | mk source expected =>
      simpa [ElaborationRenaming.renameObligation, CheckObligation.apply,
        CheckObligation.unificationVars, ElaborationRenaming.renameTy,
        List.map_append] using append_congr
          (tySupport_rename rho source) (tySupport_rename rho expected)

private theorem pendingSupport_rename
    (rho : VariableRenaming) (pending : List CheckObligation) :
    pendingUnificationVars
        (pending.map (ElaborationRenaming.renameObligation rho)) =
      (pendingUnificationVars pending).map (renameVariable rho) := by
  induction pending with
  | nil => rfl
  | cons obligation pending induction =>
      simp only [List.map_cons, pendingUnificationVars, List.map_append]
      exact append_congr
        (obligationSupport_rename rho obligation) induction

@[simp] theorem generatedSupport_rename
    (rho : VariableRenaming) (body : Generated) :
    (ElaborationRenaming.renameGenerated rho body).unificationVars =
      body.unificationVars.map (renameVariable rho) := by
  simp [Generated.unificationVars, ElaborationRenaming.renameGenerated,
    tySupport_rename, equationListSupport_rename, pendingSupport_rename,
    List.map_append]

/-- `ScopedBy` is equivariant under a bijective change of variable names. -/
theorem scopedBy_rename
    {support : List UnificationVar}
    {aliases : List FreshAliasSequence.Alias}
    (rho : VariableRenaming) (scopeProof : ScopedBy support aliases) :
    ScopedBy (support.map (renameVariable rho))
      (renameAliases rho aliases) := by
  constructor
  · have mapped :
        ((aliases.map freshVariable).map (renameVariable rho)).Nodup :=
      List.Pairwise.map (renameVariable rho)
        (fun left right different equality =>
          different (renameVariable_injective rho equality)) scopeProof.1
    simpa [renameAliases, List.map_map, Function.comp_def] using mapped
  · intro renamed renamedMember
    obtain ⟨alias, aliasMember, rfl⟩ := List.mem_map.mp renamedMember
    have endpoints := scopeProof.2 alias aliasMember
    constructor
    · intro member
      obtain ⟨candidate, candidateMember, equality⟩ := List.mem_map.mp member
      exact endpoints.1 (by
        have imageEquality : renameVariable rho candidate =
            renameVariable rho (freshVariable alias) := by
          simpa using equality
        have candidateEquality := renameVariable_injective rho imageEquality
        exact candidateEquality ▸ candidateMember)
    · exact List.mem_map.mpr ⟨existingVariable alias, endpoints.2, by simp⟩

/-- Pulling aliases back through `rho` restores a scope over the original
body whenever the input aliases are scoped over its renamed image. -/
theorem scopedBy_pullback
    {body : Generated} {aliases : List FreshAliasSequence.Alias}
    (rho : VariableRenaming)
    (scopeProof : ScopedBy
      (ElaborationRenaming.renameGenerated rho body).unificationVars aliases) :
    ScopedBy body.unificationVars (renameAliases rho.symm aliases) := by
  have transported := scopedBy_rename rho.symm scopeProof
  rw [generatedSupport_rename] at transported
  simpa [List.map_map, Function.comp_def] using transported

/-- The pulled aliases automatically retain the stepwise admissibility
needed by finite alias addition. -/
theorem admissible_pullback_of_scopedBy
    {body : Generated} {aliases : List FreshAliasSequence.Alias}
    (rho : VariableRenaming)
    (scopeProof : ScopedBy
      (ElaborationRenaming.renameGenerated rho body).unificationVars aliases) :
    FreshAliasSequence.Admissible (renameAliases rho.symm aliases) body :=
  InterfaceAliasDecomposition.AliasFreshness.admissible_of_scopedBy
    (scopedBy_pullback rho scopeProof) (fun _ member => member)

/-- Target invariance is recovered from the pulled scope certificate. -/
theorem targetFixed_pullback_of_scopedBy
    {body : Generated} {aliases : List FreshAliasSequence.Alias}
    (rho : VariableRenaming)
    (scopeProof : ScopedBy
      (ElaborationRenaming.renameGenerated rho body).unificationVars aliases) :
    SequenceTargetFixed (renameAliases rho.symm aliases) body :=
  SupportedEntailedAlignmentCertificate.sequenceTargetFixed_of_scopedBy
    (scopedBy_pullback rho scopeProof)

private theorem addAll_support_cases
    {body : Generated} (aliases : List FreshAliasSequence.Alias) :
    ∀ candidate,
      candidate ∈ (FreshAliasSequence.addAll aliases body).unificationVars →
        candidate ∈ aliases.map freshVariable ∨
          candidate ∈ aliases.map existingVariable ∨
            candidate ∈ body.unificationVars := by
  induction aliases generalizing body with
  | nil =>
      intro candidate member
      exact Or.inr (Or.inr member)
  | cons alias aliases induction =>
      intro candidate member
      have tailCases := induction candidate member
      rcases tailCases with tailFresh | tailExisting | addedMember
      · exact Or.inl (by simp [tailFresh])
      · exact Or.inr (Or.inl (by simp [tailExisting]))
      · rcases (alias_mem_unificationVars_add_iff alias body candidate).mp
            addedMember with rfl | rfl | original
        · exact Or.inl (by simp)
        · exact Or.inr (Or.inl (by simp))
        · exact Or.inr (Or.inr original)

/-- Local semantic fixedness extends through a scoped alias sequence when
all of its fresh endpoints lie in the future interval fixed by `rho`.
Existing endpoints need no new premise: `ScopedBy` places them in the
original body support. -/
theorem fixedOn_addAll_of_scopedBy_freshIn
    {reference : List Equation} {rho : VariableRenaming}
    {body : Generated} {aliases : List FreshAliasSequence.Alias}
    {boundary finish : Supply}
    (baseFixed : EntailedRenamingFixedOn reference rho body.unificationVars)
    (scopeProof : ScopedBy body.unificationVars aliases)
    (freshWithin : VariablesFreshIn boundary finish
      (aliases.map freshVariable))
    (futureFixed : rho.FixesAtOrAbove boundary) :
    EntailedRenamingFixedOn reference rho
      (FreshAliasSequence.addAll aliases body).unificationVars := by
  intro substitution solved
  have baseFacts := baseFixed substitution solved
  constructor
  · intro index member
    rcases addAll_support_cases aliases (.ty index) member with
      freshMember | existingMember | bodyMember
    · have within := freshWithin (.ty index) freshMember
      have fixed := futureFixed.1 index within.1
      rw [fixed]
    · obtain ⟨alias, aliasMember, equality⟩ := List.mem_map.mp existingMember
      have inside := (scopeProof.2 alias aliasMember).2
      exact baseFacts.1 index (by simpa using equality ▸ inside)
    · exact baseFacts.1 index bodyMember
  · intro index member
    rcases addAll_support_cases aliases (.cap index) member with
      freshMember | existingMember | bodyMember
    · have within := freshWithin (.cap index) freshMember
      have fixed := futureFixed.2 index within.1
      rw [fixed]
    · obtain ⟨alias, aliasMember, equality⟩ := List.mem_map.mp existingMember
      have inside := (scopeProof.2 alias aliasMember).2
      exact baseFacts.2 index (by simpa using equality ▸ inside)
    · exact baseFacts.2 index bodyMember

/-- Source-facing pullback endpoint.  The body certificate supplies scope
in the renamed namespace; the inverse aliases regain original scope, and
future freshness extends the body fixedness across their added equations. -/
theorem pulledFixedOn_of_certificate
    {start finish : Supply} {reference : List Equation}
    {rho : VariableRenaming} {body rightBody : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start finish
      (ElaborationRenaming.renameGenerated rho body) rightBody)
    (baseFixed : EntailedRenamingFixedOn reference rho body.unificationVars)
    (pulledFreshWithin : VariablesFreshIn start finish
      ((renameAliases rho.symm certificate.leftAliases).map freshVariable))
    (futureFixed : rho.FixesAtOrAbove start) :
    EntailedRenamingFixedOn reference rho
      (FreshAliasSequence.addAll
        (renameAliases rho.symm certificate.leftAliases) body).unificationVars :=
  fixedOn_addAll_of_scopedBy_freshIn baseFixed
    (scopedBy_pullback rho certificate.leftScoped)
    pulledFreshWithin futureFixed

/-- Future fixing makes inverse-renaming literal on every fresh endpoint of
the body certificate. -/
theorem freshVariable_pullback_eq_of_certificate
    {start finish : Supply} {rho : VariableRenaming}
    {body rightBody : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start finish
      (ElaborationRenaming.renameGenerated rho body) rightBody)
    (futureFixed : rho.FixesAtOrAbove start)
    (alias : FreshAliasSequence.Alias)
    (member : alias ∈ certificate.leftAliases) :
    freshVariable (renameAlias rho.symm alias) = freshVariable alias := by
  have hiddenMember := certificate.leftAliasFresh alias member
  have within := certificate.hiddenFresh _ hiddenMember
  cases alias with
  | ty fresh existing =>
      have forward := futureFixed.1 fresh within.1
      change UnificationVar.ty (rho.tyBackward fresh) =
        UnificationVar.ty fresh
      congr 1
      calc
        rho.tyBackward fresh = rho.tyBackward (rho.tyForward fresh) := by
          rw [forward]
        _ = fresh := rho.ty_backward_forward fresh
  | cap fresh existing =>
      have forward := futureFixed.2 fresh within.1
      change UnificationVar.cap (rho.capBackward fresh) =
        UnificationVar.cap fresh
      congr 1
      calc
        rho.capBackward fresh = rho.capBackward (rho.capForward fresh) := by
          rw [forward]
        _ = fresh := rho.cap_backward_forward fresh

/-- The pulled alias endpoints occupy the same source fresh interval as the
certificate endpoints. -/
theorem pulledFreshWithin_of_certificate
    {start finish : Supply} {rho : VariableRenaming}
    {body rightBody : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start finish
      (ElaborationRenaming.renameGenerated rho body) rightBody)
    (futureFixed : rho.FixesAtOrAbove start) :
    VariablesFreshIn start finish
      ((renameAliases rho.symm certificate.leftAliases).map freshVariable) := by
  intro candidate candidateMember
  obtain ⟨pulledAlias, pulledMember, rfl⟩ := List.mem_map.mp candidateMember
  obtain ⟨alias, aliasMember, rfl⟩ := List.mem_map.mp pulledMember
  rw [freshVariable_pullback_eq_of_certificate certificate futureFixed
    alias aliasMember]
  exact certificate.hiddenFresh _
    (certificate.leftAliasFresh alias aliasMember)

/-- Pulled fresh endpoints remain members of the certificate's hidden list,
so the original hidden-name witness can be reused unchanged. -/
theorem pulledAliasFresh_hidden_of_certificate
    {start finish : Supply} {rho : VariableRenaming}
    {body rightBody : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start finish
      (ElaborationRenaming.renameGenerated rho body) rightBody)
    (futureFixed : rho.FixesAtOrAbove start) :
    ∀ alias, alias ∈ renameAliases rho.symm certificate.leftAliases →
      freshVariable alias ∈ certificate.hidden := by
  intro pulledAlias pulledMember
  obtain ⟨alias, aliasMember, rfl⟩ := List.mem_map.mp pulledMember
  rw [freshVariable_pullback_eq_of_certificate certificate futureFixed
    alias aliasMember]
  exact certificate.leftAliasFresh alias aliasMember

/-- Exact pullback identity used to rewrite the left side of the body
certificate after moving it back to the original namespace. -/
theorem renameGenerated_addAll_pullback
    (rho : VariableRenaming) (aliases : List FreshAliasSequence.Alias)
    (body : Generated) :
    ElaborationRenaming.renameGenerated rho
        (FreshAliasSequence.addAll (renameAliases rho.symm aliases) body) =
      FreshAliasSequence.addAll aliases
        (ElaborationRenaming.renameGenerated rho body) := by
  simp

/-- If the common reference fixes the renaming on the pulled augmented
body, its renamed image is entailed-aligned with the certificate's original
left presentation. -/
theorem pulledAddAll_entailingAlignment
    {reference : List Equation} {rho : VariableRenaming}
    {aliases : List FreshAliasSequence.Alias} {body : Generated}
    (fixed : EntailedRenamingFixedOn reference rho
      (FreshAliasSequence.addAll
        (renameAliases rho.symm aliases) body).unificationVars) :
    EntailedGeneratedAlignment
      (generatedUnderReference reference
        (FreshAliasSequence.addAll (renameAliases rho.symm aliases) body))
      (generatedUnderReference reference
        (FreshAliasSequence.addAll aliases
          (ElaborationRenaming.renameGenerated rho body))) := by
  simpa [renameGenerated_addAll_pullback] using
    fixed.generated
      (FreshAliasSequence.addAll (renameAliases rho.symm aliases) body)

end AliasRenamingTransport

end TypePM.Source
