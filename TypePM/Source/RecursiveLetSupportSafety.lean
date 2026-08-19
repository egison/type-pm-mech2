import TypePM.Source.CrossGeneratedLetNormalization

/-!
# Source-support conditions for recursive let normalization

This module isolates the finite-support facts needed to use
`CrossGeneratedLetNormalization` below an arbitrary source-generated frame.
It contains no new assumption about inference: the final section records the
one strengthened closure-alignment invariant still required from the
structural source proof.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition
open InterfaceAliasDecomposition.AliasFreshness

namespace VariableRenaming

/-- A renaming is supported by `hidden` when every ordinary and capability
name outside `hidden` is fixed. -/
def FixesOutside (rho : VariableRenaming)
    (hidden : List UnificationVar) : Prop :=
  (forall index : TyVar, .ty index ∉ hidden ->
      rho.tyForward index = index) ∧
    (forall index : CapVar, .cap index ∉ hidden ->
      rho.capForward index = index)

theorem FixesOutside.renameTy_eq
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden)
    {target : Ty} (avoids : TypeAvoids hidden target) :
    ElaborationRenaming.renameTy rho target = target := by
  unfold ElaborationRenaming.renameTy
  calc
    target.apply rho.substitution = target.apply Subst.id := by
      apply Ty.apply_eq_of_agree target
      · intro index member
        have outside : .ty index ∉ hidden := by
          intro hiddenMember
          exact avoids (.ty index)
            ((Ty.mem_tyVars_iff_unificationVars index target).mp member)
            hiddenMember
        simp [VariableRenaming.substitution, Subst.id,
          fixed.1 index outside]
      · intro index member
        have outside : .cap index ∉ hidden := by
          intro hiddenMember
          exact avoids (.cap index)
            ((Ty.mem_capVars_iff_unificationVars index target).mp member)
            hiddenMember
        simp [VariableRenaming.substitution, Subst.id,
          fixed.2 index outside]
    _ = target := Ty.apply_id target

theorem FixesOutside.renameCap_eq
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden)
    {capability : Cap}
    (avoids : VariablesAvoid hidden capability.unificationVars) :
    ElaborationRenaming.renameCap rho capability = capability := by
  unfold ElaborationRenaming.renameCap
  calc
    capability.apply rho.substitution.cap =
        capability.apply Subst.id.cap := by
      apply Cap.apply_eq_of_agree capability
      intro index member
      have outside : .cap index ∉ hidden := by
        intro hiddenMember
        exact avoids (.cap index)
          ((Cap.mem_capVars_iff_unificationVars index capability).mp member)
          hiddenMember
      simp [VariableRenaming.substitution, Subst.id,
        fixed.2 index outside]
    _ = capability := Cap.apply_id capability

theorem FixesOutside.renameEquation_eq
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden)
    {equation : Equation}
    (avoids : VariablesAvoid hidden equation.unificationVars) :
    ElaborationRenaming.renameEquation rho equation = equation := by
  cases equation with
  | ty left right =>
      have leftAvoids : TypeAvoids hidden left :=
        fun candidate member hiddenMember => avoids candidate
          (List.mem_append_left _ member) hiddenMember
      have rightAvoids : TypeAvoids hidden right :=
        fun candidate member hiddenMember => avoids candidate
          (List.mem_append_right _ member) hiddenMember
      change Equation.ty
          (ElaborationRenaming.renameTy rho left)
          (ElaborationRenaming.renameTy rho right) = .ty left right
      rw [fixed.renameTy_eq leftAvoids, fixed.renameTy_eq rightAvoids]
  | cap left right =>
      have leftAvoids : VariablesAvoid hidden left.unificationVars :=
        fun candidate member hiddenMember => avoids candidate
          (List.mem_append_left _ member) hiddenMember
      have rightAvoids : VariablesAvoid hidden right.unificationVars :=
        fun candidate member hiddenMember => avoids candidate
          (List.mem_append_right _ member) hiddenMember
      change Equation.cap
          (ElaborationRenaming.renameCap rho left)
          (ElaborationRenaming.renameCap rho right) = .cap left right
      rw [fixed.renameCap_eq leftAvoids, fixed.renameCap_eq rightAvoids]

theorem FixesOutside.renameObligation_eq
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden)
    {obligation : CheckObligation}
    (avoids : VariablesAvoid hidden obligation.unificationVars) :
    ElaborationRenaming.renameObligation rho obligation = obligation := by
  cases obligation with
  | mk source expected =>
      have sourceAvoids : TypeAvoids hidden source :=
        fun candidate member hiddenMember => avoids candidate
          (List.mem_append_left _ member) hiddenMember
      have expectedAvoids : TypeAvoids hidden expected :=
        fun candidate member hiddenMember => avoids candidate
          (List.mem_append_right _ member) hiddenMember
      change CheckObligation.mk
          (ElaborationRenaming.renameTy rho source)
          (ElaborationRenaming.renameTy rho expected) =
        .mk source expected
      rw [fixed.renameTy_eq sourceAvoids,
        fixed.renameTy_eq expectedAvoids]

theorem FixesOutside.renameEquations_eq
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden) :
    forall {equations : List Equation},
      EquationsAvoid hidden equations ->
        equations.map (ElaborationRenaming.renameEquation rho) = equations
  | [], _ => rfl
  | equation :: equations, avoids => by
      change VariablesAvoid hidden
        (equation.unificationVars ++ TypePM.unificationVars equations)
        at avoids
      rw [List.map_cons, fixed.renameEquation_eq
          (fun candidate member hiddenMember => avoids candidate
            (List.mem_append_left _ member) hiddenMember),
        FixesOutside.renameEquations_eq fixed
          (fun candidate member hiddenMember => avoids candidate
            (List.mem_append_right _ member) hiddenMember)]

theorem FixesOutside.renameObligations_eq
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden) :
    forall {pending : List CheckObligation},
      VariablesAvoid hidden (pendingUnificationVars pending) ->
        pending.map (ElaborationRenaming.renameObligation rho) = pending
  | [], _ => rfl
  | obligation :: pending, avoids => by
      change VariablesAvoid hidden
        (obligation.unificationVars ++ pendingUnificationVars pending)
        at avoids
      rw [List.map_cons, fixed.renameObligation_eq
          (fun candidate member hiddenMember => avoids candidate
            (List.mem_append_left _ member) hiddenMember),
        FixesOutside.renameObligations_eq fixed
          (fun candidate member hiddenMember => avoids candidate
            (List.mem_append_right _ member) hiddenMember)]

private theorem types_apply_eq_self
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden) :
    forall {targets : List Ty},
      VariablesAvoid hidden (Ty.unificationVarsList targets) ->
        Ty.applyList rho.substitution targets = targets
  | [], _ => rfl
  | target :: targets, avoids => by
      change VariablesAvoid hidden
        (target.unificationVars ++ Ty.unificationVarsList targets) at avoids
      have targetFixed := fixed.renameTy_eq
        (fun candidate member hiddenMember => avoids candidate
          (List.mem_append_left _ member) hiddenMember)
      change target.apply rho.substitution = target at targetFixed
      rw [Ty.applyList, targetFixed,
        types_apply_eq_self fixed
          (fun candidate member hiddenMember => avoids candidate
            (List.mem_append_right _ member) hiddenMember)]

theorem FixesOutside.renameGenerated_eq
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden)
    {generated : Generated}
    (avoids : GeneratedAvoids hidden generated) :
    ElaborationRenaming.renameGenerated rho generated = generated := by
  have targetAvoids : TypeAvoids hidden generated.target := by
    intro candidate member hiddenMember
    exact avoids candidate (by
      simp [Generated.unificationVars, member]) hiddenMember
  have hardAvoids : EquationsAvoid hidden generated.hard := by
    intro candidate member hiddenMember
    exact avoids candidate (by
      simp [Generated.unificationVars, member]) hiddenMember
  have pendingAvoids :
      VariablesAvoid hidden (pendingUnificationVars generated.pending) := by
    intro candidate member hiddenMember
    exact avoids candidate (by
      simp [Generated.unificationVars, member]) hiddenMember
  cases generated
  simp [ElaborationRenaming.renameGenerated, fixed.renameTy_eq targetAvoids,
    fixed.renameEquations_eq hardAvoids,
    fixed.renameObligations_eq pendingAvoids]

theorem FixesOutside.renameGeneratedItems_eq
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden)
    {generated : GeneratedItems}
    (avoids : GeneratedItemsAvoid hidden generated) :
    ElaborationRenaming.renameGeneratedItems rho generated = generated := by
  have targetsAvoid :
      VariablesAvoid hidden (Ty.unificationVarsList generated.targets) := by
    intro candidate member hiddenMember
    exact avoids candidate (by
      simp [GeneratedItems.unificationVars, member]) hiddenMember
  have hardAvoids : EquationsAvoid hidden generated.hard := by
    intro candidate member hiddenMember
    exact avoids candidate (by
      simp [GeneratedItems.unificationVars, member]) hiddenMember
  have pendingAvoids :
      VariablesAvoid hidden (pendingUnificationVars generated.pending) := by
    intro candidate member hiddenMember
    exact avoids candidate (by
      simp [GeneratedItems.unificationVars, member]) hiddenMember
  cases generated
  simp [ElaborationRenaming.renameGeneratedItems,
    types_apply_eq_self fixed targetsAvoid,
    fixed.renameEquations_eq hardAvoids,
    fixed.renameObligations_eq pendingAvoids]

end VariableRenaming

private theorem renameGenerated_fromLam
    (rho : VariableRenaming) (domain : Ty) (body : Generated) :
    ElaborationRenaming.renameGenerated rho
        (Generated.fromLam domain body) =
      Generated.fromLam (ElaborationRenaming.renameTy rho domain)
        (ElaborationRenaming.renameGenerated rho body) := by
  cases body
  simp [Generated.fromLam, ElaborationRenaming.renameGenerated,
    ElaborationRenaming.renameTy, Ty.apply]

private theorem renameGenerated_fromApp
    (rho : VariableRenaming) (function argument : Generated)
    (domain target : Ty) :
    ElaborationRenaming.renameGenerated rho
        (Generated.fromApp function argument domain target) =
      Generated.fromApp
        (ElaborationRenaming.renameGenerated rho function)
        (ElaborationRenaming.renameGenerated rho argument)
        (ElaborationRenaming.renameTy rho domain)
        (ElaborationRenaming.renameTy rho target) := by
  cases function
  cases argument
  simp [Generated.fromApp, ElaborationRenaming.renameGenerated,
    ElaborationRenaming.renameTy, ElaborationRenaming.renameEquation,
    ElaborationRenaming.renameObligation, Equation.apply,
    CheckObligation.apply, Ty.apply, List.map_append]

private theorem tyApplyList_append
    (substitution : Subst) (left right : List Ty) :
    Ty.applyList substitution (left ++ right) =
      Ty.applyList substitution left ++ Ty.applyList substitution right := by
  induction left with
  | nil => rfl
  | cons target targets induction =>
      simp [Ty.applyList, induction]

private theorem renameGeneratedItems_append
    (rho : VariableRenaming) (left right : GeneratedItems) :
    ElaborationRenaming.renameGeneratedItems rho
        (GeneratedItems.append left right) =
      GeneratedItems.append
        (ElaborationRenaming.renameGeneratedItems rho left)
        (ElaborationRenaming.renameGeneratedItems rho right) := by
  cases left
  cases right
  simp [GeneratedItems.append, ElaborationRenaming.renameGeneratedItems,
    tyApplyList_append, List.map_append]

private theorem renameGeneratedItems_singleton
    (rho : VariableRenaming) (generated : Generated) :
    ElaborationRenaming.renameGeneratedItems rho
        (GeneratedItems.singleton generated) =
      GeneratedItems.singleton
        (ElaborationRenaming.renameGenerated rho generated) := by
  cases generated
  simp [GeneratedItems.singleton, GeneratedItems.cons, GeneratedItems.nil,
    ElaborationRenaming.renameGeneratedItems,
    ElaborationRenaming.renameGenerated, ElaborationRenaming.renameTy,
    Ty.applyList]

private theorem renameGenerated_asTuple
    (rho : VariableRenaming) (items : GeneratedItems) :
    ElaborationRenaming.renameGenerated rho
        (GeneratedItems.asTuple items) =
      GeneratedItems.asTuple
        (ElaborationRenaming.renameGeneratedItems rho items) := by
  cases items
  simp [GeneratedItems.asTuple, ElaborationRenaming.renameGenerated,
    ElaborationRenaming.renameGeneratedItems,
    ElaborationRenaming.renameTy, Ty.apply]

namespace GeneratedFrame

/-- Renaming a hole commutes with plugging it into a fixed source frame when
the frame avoids the complete support of the renaming. -/
theorem renameGenerated_plug_of_fixesOutside
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden)
    {frame : GeneratedFrame} (frameAvoids : frame.Avoids hidden)
    (generated : Generated) :
    ElaborationRenaming.renameGenerated rho (frame.plug generated) =
      frame.plug (ElaborationRenaming.renameGenerated rho generated) := by
  induction frame generalizing generated with
  | hole => rfl
  | lam domain outer induction =>
      rcases frameAvoids with ⟨domainAvoids, outerAvoids⟩
      calc
        ElaborationRenaming.renameGenerated rho
            (outer.plug (Generated.fromLam domain generated)) =
          outer.plug (ElaborationRenaming.renameGenerated rho
            (Generated.fromLam domain generated)) :=
              induction outerAvoids _
        _ = outer.plug (Generated.fromLam domain
            (ElaborationRenaming.renameGenerated rho generated)) := by
              rw [renameGenerated_fromLam,
                fixed.renameTy_eq domainAvoids]
  | appFunction argument domain target outer induction =>
      rcases frameAvoids with
        ⟨argumentAvoids, domainAvoids, targetAvoids, outerAvoids⟩
      have argumentFixed := fixed.renameGenerated_eq argumentAvoids
      have domainFixed := fixed.renameTy_eq domainAvoids
      have targetFixed := fixed.renameTy_eq targetAvoids
      calc
        ElaborationRenaming.renameGenerated rho
            (outer.plug
              (Generated.fromApp generated argument domain target)) =
          outer.plug (ElaborationRenaming.renameGenerated rho
            (Generated.fromApp generated argument domain target)) :=
              induction outerAvoids _
        _ = outer.plug (Generated.fromApp
            (ElaborationRenaming.renameGenerated rho generated)
            argument domain target) := by
              rw [renameGenerated_fromApp, argumentFixed,
                domainFixed, targetFixed]
  | appArgument function domain target outer induction =>
      rcases frameAvoids with
        ⟨functionAvoids, domainAvoids, targetAvoids, outerAvoids⟩
      have functionFixed := fixed.renameGenerated_eq functionAvoids
      have domainFixed := fixed.renameTy_eq domainAvoids
      have targetFixed := fixed.renameTy_eq targetAvoids
      calc
        ElaborationRenaming.renameGenerated rho
            (outer.plug
              (Generated.fromApp function generated domain target)) =
          outer.plug (ElaborationRenaming.renameGenerated rho
            (Generated.fromApp function generated domain target)) :=
              induction outerAvoids _
        _ = outer.plug (Generated.fromApp function
            (ElaborationRenaming.renameGenerated rho generated)
            domain target) := by
              rw [renameGenerated_fromApp, functionFixed,
                domainFixed, targetFixed]
  | tupleItem before after outer induction =>
      rcases frameAvoids with ⟨beforeAvoids, afterAvoids, outerAvoids⟩
      have beforeFixed := fixed.renameGeneratedItems_eq beforeAvoids
      have afterFixed := fixed.renameGeneratedItems_eq afterAvoids
      calc
        ElaborationRenaming.renameGenerated rho
            (outer.plug <| GeneratedItems.asTuple <|
              GeneratedItems.append before <|
                GeneratedItems.append
                  (GeneratedItems.singleton generated) after) =
          outer.plug (ElaborationRenaming.renameGenerated rho <|
            GeneratedItems.asTuple <|
              GeneratedItems.append before <|
                GeneratedItems.append
                  (GeneratedItems.singleton generated) after) :=
              induction outerAvoids _
        _ = outer.plug (GeneratedItems.asTuple <|
              GeneratedItems.append before <|
                GeneratedItems.append
                  (GeneratedItems.singleton
                    (ElaborationRenaming.renameGenerated rho generated))
                  after) := by
              rw [renameGenerated_asTuple,
                renameGeneratedItems_append,
                renameGeneratedItems_append,
                renameGeneratedItems_singleton,
                beforeFixed, afterFixed]
  | letBody effects outer induction =>
      rcases frameAvoids with ⟨effectsAvoids, outerAvoids⟩
      have effectsFixed := fixed.renameEquations_eq effectsAvoids
      calc
        ElaborationRenaming.renameGenerated rho
            (outer.plug (Generated.fromLet effects generated)) =
          outer.plug (ElaborationRenaming.renameGenerated rho
            (Generated.fromLet effects generated)) :=
              induction outerAvoids _
        _ = outer.plug (Generated.fromLet effects
            (ElaborationRenaming.renameGenerated rho generated)) := by
              rw [ElaborationRenaming.renameGenerated_fromLet,
                effectsFixed]

end GeneratedFrame

namespace Generated

/-- A renaming supported entirely by `hidden` is contextually safe: every
admissible fixed frame is unchanged, so whole-block renaming invariance can
be applied after commuting renaming with plugging. -/
theorem scopedContextualEquivalent_rename_of_fixesOutside
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fixed : rho.FixesOutside hidden) (generated : Generated) :
    ScopedContextualEquivalent hidden generated
      (ElaborationRenaming.renameGenerated rho generated) := by
  intro frame frameAvoids
  have commute := GeneratedFrame.renameGenerated_plug_of_fixesOutside
    fixed frameAvoids generated
  have renamed := ElaborationRenaming.blockAccepts_renameVariables_iff
    rho (frame.plug generated)
  rw [commute] at renamed
  exact renamed

end Generated

namespace Elaborates

/-- Source support provenance discharges avoidance of an earlier hidden
interval whenever all variables inherited by the later body lie below the
start of that interval.  At a recursive `let`, this inherited-bound premise
is exactly what is needed to derive body avoidance; constructing the complete
source-safe closure alignment additionally requires the support and alias
ordering certificates recorded below. -/
theorem generatedAvoids_earlierHidden
    {context : Context} {expression : Expr}
    {valueStart bodyStart finish : Supply}
    {generated : Generated}
    (derivation : Elaborates context expression bodyStart generated finish)
    {hidden : List UnificationVar}
    (hiddenFresh : VariablesFreshIn valueStart bodyStart hidden)
    (inheritedBefore : context.initialSupply.Le valueStart) :
    GeneratedAvoids hidden generated :=
  VariablesScopedBy.avoids_earlier hiddenFresh
    derivation.supportProvenance.scopedByInitialSupply
    inheritedBefore (Supply.le_refl bodyStart)

end Elaborates

/-! ## The remaining source invariant -/

/-- The exact source-support package missing from
`FreshClosureAlignment`.  `fixesOutside` is sufficient for isolated child
renaming by the theorem above.  `frameAdmissible` cannot be recovered from a
bare `EquationCommonCore`, because that structure intentionally forgets the
support and ordering certificate of its alias sequences. -/
structure SourceSafeWholeLetAlignment
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context} {boundary start : Supply}
    (alignment : FreshClosureAlignment left right context boundary)
    (body : Generated) where
  hidden : List UnificationVar
  hiddenFresh : VariablesFreshIn start boundary hidden
  fixesOutside : alignment.alignment.rho.FixesOutside hidden
  frameAdmissible :
    (alignment.alignment.renamedFromLetCommonCore body).FrameAdmissible hidden

namespace SourceSafeWholeLetAlignment

/-- The support package discharges both premises of cross-generated
whole-let normalization. -/
theorem scopedContextualEquivalent
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context} {boundary start : Supply}
    {alignment : FreshClosureAlignment left right context boundary}
    {body : Generated}
    (safe : SourceSafeWholeLetAlignment (start := start) alignment body) :
    Generated.ScopedContextualEquivalent safe.hidden
      (Generated.fromLet
        (context.interfaceEquations left.substitution) body)
      (Generated.fromLet
        (context.interfaceEquations right.substitution)
        (ElaborationRenaming.renameGenerated
          alignment.alignment.rho body)) := by
  apply alignment.alignment.fromLet_scopedContextualEquivalent_of_isolatedRenaming
  · exact Generated.scopedContextualEquivalent_rename_of_fixesOutside
      safe.fixesOutside _
  · exact safe.frameAdmissible

/-- The same package gives the interface half of a scoped generated
comparison over the value-elaboration interval. -/
theorem interfaceComparison
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context} {boundary start : Supply}
    {alignment : FreshClosureAlignment left right context boundary}
    {body : Generated}
    (safe : SourceSafeWholeLetAlignment (start := start) alignment body) :
    ScopedGeneratedComparison start boundary boundary
      (Generated.fromLet
        (context.interfaceEquations left.substitution) body)
      (Generated.fromLet
        (context.interfaceEquations right.substitution)
        (ElaborationRenaming.renameGenerated
          alignment.alignment.rho body)) :=
  ⟨rfl, safe.hidden, safe.hiddenFresh,
    safe.scopedContextualEquivalent⟩

end SourceSafeWholeLetAlignment

/-! ## Information-loss counterexample for the pure equation certificate -/

namespace FrameAdmissibilityCounterexample

private def alpha : TyVar := ⟨0⟩
private def beta : TyVar := ⟨1⟩

private def pending : List CheckObligation :=
  [⟨.var alpha, .int⟩]

private def left : Generated :=
  { target := .int
    hard := [.ty (.var alpha) (.var beta)]
    pending := pending }

private def right : Generated :=
  { target := .int
    hard := [.ty (.var beta) (.var beta)]
    pending := pending }

noncomputable def decomposition :
    GeneratedEquationCommonCore left right :=
  { equations :=
      InterfaceAliasDecomposition.EquationLists.EquationCommonCore.tyAlias_refl
        alpha beta []
    target_eq := rfl
    pending_eq := rfl }

/-- `EquationCommonCore` records the correct hard-equation relation but not
that its chosen fresh endpoint occurs in a delayed body obligation.  Hence
frame admissibility is not derivable from that pure certificate alone. -/
theorem not_frameAdmissible :
    ¬ decomposition.FrameAdmissible [] := by
  intro admissible
  have atHole := admissible .hole (by trivial)
  have leftAdmissible := atHole.1
  change FreshAliasSequence.Admissible
      [.ty alpha beta]
      { target := .int, hard := [], pending := pending } at leftAdmissible
  have pendingFixed := leftAdmissible.1.2.2
  simp [FreshAliasSaturation.PendingFixed, pending,
    CheckObligation.apply, Subst.singleTy, Ty.apply,
    alpha, beta] at pendingFixed

end FrameAdmissibilityCounterexample

namespace FutureFixingCounterexample

private def alpha : TyVar := ⟨0⟩
private def beta : TyVar := ⟨1⟩
private def boundary : Supply := ⟨2, 0⟩

private def swap : VariableRenaming :=
  let permutation := FinitePermutation.swap alpha beta
  { tyForward := permutation.forward
    tyBackward := permutation.backward
    capForward := id
    capBackward := id
    ty_backward_forward := permutation.backward_forward
    ty_forward_backward := permutation.forward_backward
    cap_backward_forward := fun _ => rfl
    cap_forward_backward := fun _ => rfl }

theorem fixesAtOrAbove : swap.FixesAtOrAbove boundary := by
  constructor
  · intro index above
    have neither : index ≠ alpha ∧ index ≠ beta := by
      constructor <;> intro equality <;> subst index <;>
        simp [boundary, alpha, beta] at above
    simp [swap, FinitePermutation.swap, FinitePermutation.swapIndex,
      neither.1, neither.2]
  · intro index _above
    rfl

/-- Fixing every future name does not imply support by names fresh in the
current interval: the renaming may still move inherited names below that
interval's start. -/
theorem no_fresh_fixesOutside
    (hidden : List UnificationVar)
    (fresh : VariablesFreshIn boundary boundary hidden) :
    ¬ swap.FixesOutside hidden := by
  intro fixed
  have alphaOutside : .ty alpha ∉ hidden := by
    intro member
    have impossible := fresh (.ty alpha) member
    simp [UnificationVar.FreshIn, boundary, alpha] at impossible
  have alphaFixed := fixed.1 alpha alphaOutside
  simp [swap, FinitePermutation.swap, FinitePermutation.swapIndex,
    alpha, beta] at alphaFixed

end FutureFixingCounterexample

end TypePM.Source
