import TypePM.Source.EntailedRenamingAlignment
import TypePM.Source.ProvenancedFreshClosureAlignment
import TypePM.Source.GeneratedSupportBounds
import TypePM.Source.ContextApplyFreeReflection

/-!
# Body semantics under a closure-interface renaming

The closure renaming need not be semantically fixed on every variable.
For a transported `let` body it is enough to fix the finite support of the
generated body.  Source support provenance reduces that support to the
closed outer context and the future fresh interval; the two interface
equation lists handle the former and `FixesAtOrAbove` handles the latter.
-/

namespace TypePM.Source

/-- The three observable generated components after applying a solution. -/
structure GeneratedAppliedEq (substitution : Subst)
    (left right : Generated) : Prop where
  target : left.target.apply substitution = right.target.apply substitution
  hard : left.hard.map (Equation.apply substitution) =
    right.hard.map (Equation.apply substitution)
  pending : left.pending.map (CheckObligation.apply substitution) =
    right.pending.map (CheckObligation.apply substitution)

private theorem mem_equationList_unificationVars
    {equations : List Equation} {equation : Equation}
    (equationMember : equation ∈ equations) {candidate : UnificationVar}
    (candidateMember : candidate ∈ equation.unificationVars) :
    candidate ∈ TypePM.unificationVars equations := by
  induction equations with
  | nil => simp at equationMember
  | cons head tail induction =>
      simp only [List.mem_cons] at equationMember
      simp only [TypePM.unificationVars, List.mem_append]
      rcases equationMember with rfl | tailMember
      · exact Or.inl candidateMember
      · exact Or.inr (induction tailMember)

private theorem generated_target_member
    (body : Generated) {candidate : UnificationVar}
    (member : candidate ∈ body.target.unificationVars) :
    candidate ∈ body.unificationVars :=
  List.mem_append_left _ (List.mem_append_left _ member)

private theorem generated_hard_member
    (body : Generated) {equation : Equation}
    (equationMember : equation ∈ body.hard) {candidate : UnificationVar}
    (member : candidate ∈ equation.unificationVars) :
    candidate ∈ body.unificationVars :=
  List.mem_append_left _
    (List.mem_append_right _
      (mem_equationList_unificationVars equationMember member))

private theorem generated_pending_member
    (body : Generated) {obligation : CheckObligation}
    (obligationMember : obligation ∈ body.pending)
    {candidate : UnificationVar}
    (member : candidate ∈ obligation.unificationVars) :
    candidate ∈ body.unificationVars :=
  List.mem_append_right _
    (mem_pendingUnificationVars obligationMember member)

namespace EntailedRenamingFixedOn

private theorem ty_agree
    {reference : List Equation} {rho : VariableRenaming}
    {support : List UnificationVar}
    (fixed : EntailedRenamingFixedOn reference rho support)
    {substitution : Subst} (solved : Solves substitution reference)
    {index : TyVar} (member : (.ty index : UnificationVar) ∈ support) :
    substitution.ty index =
      (Subst.compose substitution rho.substitution).ty index :=
  by
    simpa [Subst.compose, VariableRenaming.substitution, Ty.apply] using
      ((fixed substitution solved).1 index member).symm

private theorem cap_agree
    {reference : List Equation} {rho : VariableRenaming}
    {support : List UnificationVar}
    (fixed : EntailedRenamingFixedOn reference rho support)
    {substitution : Subst} (solved : Solves substitution reference)
    {index : CapVar} (member : (.cap index : UnificationVar) ∈ support) :
    substitution.cap index =
      (Subst.compose substitution rho.substitution).cap index :=
  by
    simpa [Subst.compose, VariableRenaming.substitution, Cap.apply] using
      ((fixed substitution solved).2 index member).symm

/-- Local fixedness on `generated.unificationVars` is sufficient for exact
target, hard-equation, and pending-obligation equality after a reference
solution. -/
theorem appliedEq
    {reference : List Equation} {rho : VariableRenaming} {body : Generated}
    (fixed : EntailedRenamingFixedOn reference rho body.unificationVars)
    {substitution : Subst} (solved : Solves substitution reference) :
    GeneratedAppliedEq substitution body
      (ElaborationRenaming.renameGenerated rho body) := by
  have targetEq : body.target.apply substitution =
      body.target.apply (Subst.compose substitution rho.substitution) := by
    apply Ty.apply_eq_of_agree body.target
    · intro index member
      apply fixed.ty_agree solved
      exact generated_target_member body
        ((Ty.mem_tyVars_iff_unificationVars index body.target).mp member)
    · intro index member
      apply fixed.cap_agree solved
      exact generated_target_member body
        ((Ty.mem_capVars_iff_unificationVars index body.target).mp member)
  have equationEq : ∀ equation ∈ body.hard,
      equation.apply substitution =
        equation.apply (Subst.compose substitution rho.substitution) := by
    intro equation equationMember
    cases equation with
    | ty left right =>
        simp only [Equation.apply]
        congr 1
        · apply Ty.apply_eq_of_agree left
          · intro index member
            apply fixed.ty_agree solved
            exact generated_hard_member body equationMember
              (List.mem_append_left _
                ((Ty.mem_tyVars_iff_unificationVars index left).mp member))
          · intro index member
            apply fixed.cap_agree solved
            exact generated_hard_member body equationMember
              (List.mem_append_left _
                ((Ty.mem_capVars_iff_unificationVars index left).mp member))
        · apply Ty.apply_eq_of_agree right
          · intro index member
            apply fixed.ty_agree solved
            exact generated_hard_member body equationMember
              (List.mem_append_right _
                ((Ty.mem_tyVars_iff_unificationVars index right).mp member))
          · intro index member
            apply fixed.cap_agree solved
            exact generated_hard_member body equationMember
              (List.mem_append_right _
                ((Ty.mem_capVars_iff_unificationVars index right).mp member))
    | cap left right =>
        simp only [Equation.apply]
        congr 1
        · apply Cap.apply_eq_of_agree left
          intro index member
          apply fixed.cap_agree solved
          exact generated_hard_member body equationMember
            (List.mem_append_left _
              ((Cap.mem_capVars_iff_unificationVars index left).mp member))
        · apply Cap.apply_eq_of_agree right
          intro index member
          apply fixed.cap_agree solved
          exact generated_hard_member body equationMember
            (List.mem_append_right _
              ((Cap.mem_capVars_iff_unificationVars index right).mp member))
  have pendingEq : ∀ obligation ∈ body.pending,
      obligation.apply substitution =
        obligation.apply (Subst.compose substitution rho.substitution) := by
    rintro ⟨source, expected⟩ obligationMember
    simp only [CheckObligation.apply]
    congr 1
    · apply Ty.apply_eq_of_agree source
      · intro index member
        apply fixed.ty_agree solved
        exact generated_pending_member body obligationMember
          (CheckObligation.mem_unificationVars_source _
            ((Ty.mem_tyVars_iff_unificationVars index source).mp member))
      · intro index member
        apply fixed.cap_agree solved
        exact generated_pending_member body obligationMember
          (CheckObligation.mem_unificationVars_source _
            ((Ty.mem_capVars_iff_unificationVars index source).mp member))
    · apply Ty.apply_eq_of_agree expected
      · intro index member
        apply fixed.ty_agree solved
        exact generated_pending_member body obligationMember
          (CheckObligation.mem_unificationVars_expected _
            ((Ty.mem_tyVars_iff_unificationVars index expected).mp member))
      · intro index member
        apply fixed.cap_agree solved
        exact generated_pending_member body obligationMember
          (CheckObligation.mem_unificationVars_expected _
            ((Ty.mem_capVars_iff_unificationVars index expected).mp member))
  refine ⟨?_, ?_, ?_⟩
  · simpa [ElaborationRenaming.renameGenerated,
      ElaborationRenaming.renameTy, Ty.apply_compose] using targetEq
  · simp only [ElaborationRenaming.renameGenerated, List.map_map,
      Function.comp_def]
    apply List.map_congr_left
    intro equation member
    cases equation <;>
      simpa [ElaborationRenaming.renameEquation, Equation.apply,
        Ty.apply_compose, Cap.apply_compose]
        using equationEq _ member
  · simp only [ElaborationRenaming.renameGenerated, List.map_map,
      Function.comp_def]
    apply List.map_congr_left
    intro obligation member
    simpa [ElaborationRenaming.renameObligation,
      CheckObligation.apply, Ty.apply_compose]
      using pendingEq obligation member

end EntailedRenamingFixedOn

/-- The common semantic reference used at a heterogeneous `let` boundary. -/
def closureInterfaceReference
    {leftGenerated rightGenerated : Generated}
    (context : Context)
    (leftClosure : PrincipalBlockClosure leftGenerated)
    (rightClosure : PrincipalBlockClosure rightGenerated) : List Equation :=
  context.interfaceEquations leftClosure.substitution ++
    context.interfaceEquations rightClosure.substitution

/-- Source support provenance turns the two solved closure interfaces and
future-fixing alignment into local semantic fixedness on the body block.
Generalized value-only names do not appear free in the body context; this is
why the conclusion is support-local rather than global. -/
theorem Elaborates.entailedRenamingFixedOn_of_closureInterfaces
    {signature : Signature} {outerContext : Context} {body : Expr}
    {afterValue bodyFinish : Supply}
    {leftValue rightValue leftBody : Generated}
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (alignment : FreshClosureAlignment leftClosure rightClosure
      outerContext afterValue)
    (bodyElaboration : Elaborates signature
      ((outerContext.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        outerContext.applyFree leftClosure.substitution)
      body afterValue leftBody bodyFinish) :
    EntailedRenamingFixedOn
      (closureInterfaceReference outerContext leftClosure rightClosure)
      alignment.alignment.rho leftBody.unificationVars := by
  intro substitution solved
  have solvedParts := solves_append substitution
    (outerContext.interfaceEquations leftClosure.substitution)
    (outerContext.interfaceEquations rightClosure.substitution) |>.mp solved
  have closedAgree :=
    Context.substitutionsAgree_compose_renaming_of_interfaces
      outerContext leftClosure.substitution rightClosure.substitution
      substitution alignment.alignment.rho solvedParts.1 solvedParts.2
      alignment.alignment.closedContext_exact
  constructor
  · intro index member
    rcases bodyElaboration.supportProvenance (.ty index) member with
      contextMember | fresh
    · have closedMember := Context.generalized_cons_support_subset
          (outerContext.applyFree leftClosure.substitution)
          leftClosure.target (.ty index) contextMember
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
        at closedMember
      rcases closedMember with tyMember | capMember
      · obtain ⟨source, sourceMember, equality⟩ := tyMember
        cases equality
        have agreed := closedAgree.1 index sourceMember
        simpa [Subst.compose, VariableRenaming.substitution, Ty.apply] using
          agreed.symm
      · obtain ⟨source, _, impossible⟩ := capMember
        cases impossible
    · have fixed := alignment.fixesAtOrAbove.1 index fresh.1
      simp [fixed]
  · intro index member
    rcases bodyElaboration.supportProvenance (.cap index) member with
      contextMember | fresh
    · have closedMember := Context.generalized_cons_support_subset
          (outerContext.applyFree leftClosure.substitution)
          leftClosure.target (.cap index) contextMember
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
        at closedMember
      rcases closedMember with tyMember | capMember
      · obtain ⟨source, _, impossible⟩ := tyMember
        cases impossible
      · obtain ⟨source, sourceMember, equality⟩ := capMember
        cases equality
        have agreed := closedAgree.2 index sourceMember
        simpa [Subst.compose, VariableRenaming.substitution, Cap.apply] using
          agreed.symm
    · have fixed := alignment.fixesAtOrAbove.2 index fresh.1
      simp [fixed]

/-- Under every solution of both closure interfaces, the original source
body and its transported image have literally equal applied targets, hard
equations, and delayed obligations. -/
theorem Elaborates.bodyRenamingAppliedEq_of_closureInterfaces
    {signature : Signature} {outerContext : Context} {body : Expr}
    {afterValue bodyFinish : Supply}
    {leftValue rightValue leftBody : Generated}
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (alignment : FreshClosureAlignment leftClosure rightClosure
      outerContext afterValue)
    (bodyElaboration : Elaborates signature
      ((outerContext.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        outerContext.applyFree leftClosure.substitution)
      body afterValue leftBody bodyFinish)
    {substitution : Subst}
    (solved : Solves substitution
      (closureInterfaceReference outerContext leftClosure rightClosure)) :
    GeneratedAppliedEq substitution leftBody
      (ElaborationRenaming.renameGenerated alignment.alignment.rho leftBody) :=
  (bodyElaboration.entailedRenamingFixedOn_of_closureInterfaces
    leftClosure rightClosure alignment).appliedEq solved

/-- Certificate form consumed by whole-`let` assembly: after prepending both
interfaces as a common reference, the original and transported body blocks
are entailed-aligned. -/
theorem Elaborates.bodyRenamingEntailedAlignment_of_closureInterfaces
    {signature : Signature} {outerContext : Context} {body : Expr}
    {afterValue bodyFinish : Supply}
    {leftValue rightValue leftBody : Generated}
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (alignment : FreshClosureAlignment leftClosure rightClosure
      outerContext afterValue)
    (bodyElaboration : Elaborates signature
      ((outerContext.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        outerContext.applyFree leftClosure.substitution)
      body afterValue leftBody bodyFinish) :
    EntailedGeneratedAlignment
      (generatedUnderReference
        (closureInterfaceReference outerContext leftClosure rightClosure)
        leftBody)
      (generatedUnderReference
        (closureInterfaceReference outerContext leftClosure rightClosure)
        (ElaborationRenaming.renameGenerated alignment.alignment.rho
          leftBody)) :=
  EntailedRenamingFixedOn.generated leftBody
    (bodyElaboration.entailedRenamingFixedOn_of_closureInterfaces
      leftClosure rightClosure alignment)

/-- Handler-shaped endpoint retaining both the original and transported
body derivations.  The transported derivation is evidence that the renamed
block is the actual right-context source result; semantic equality itself is
already forced by the original derivation's support provenance. -/
theorem ProvenancedFreshClosureAlignment.bodyAppliedEq_of_elaborations
    {signature : Signature} {outerContext : Context} {body : Expr}
    {afterValue bodyFinish : Supply}
    {leftValue rightValue leftBody : Generated}
    {leftClosure : PrincipalBlockClosure leftValue}
    {rightClosure : PrincipalBlockClosure rightValue}
    (alignment : ProvenancedFreshClosureAlignment leftClosure rightClosure
      outerContext afterValue)
    (leftBodyElaboration : Elaborates signature
      ((outerContext.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        outerContext.applyFree leftClosure.substitution)
      body afterValue leftBody bodyFinish)
    (_transportedBodyElaboration : Elaborates signature
      ((outerContext.applyFree rightClosure.substitution).generalize
          rightClosure.target ::
        outerContext.applyFree rightClosure.substitution)
      body afterValue
      (ElaborationRenaming.renameGenerated
        alignment.alignment.alignment.rho leftBody)
      bodyFinish)
    {substitution : Subst}
    (solved : Solves substitution
      (closureInterfaceReference outerContext leftClosure rightClosure)) :
    GeneratedAppliedEq substitution leftBody
      (ElaborationRenaming.renameGenerated
        alignment.alignment.alignment.rho leftBody) :=
  leftBodyElaboration.bodyRenamingAppliedEq_of_closureInterfaces
    leftClosure rightClosure alignment.toFreshClosureAlignment solved

end TypePM.Source
