import TypePM.Source.EntailedAlignment
import TypePM.Source.ElaborationRenaming

/-!
# Renaming alignment under a semantic reference

A source-specific `let` proof does not need an isolated renaming to be
contextually harmless.  It is enough that every solution of the surrounding
hard reference identifies a substitution with its precomposition by the
closure renaming.  This module packages that exact condition and turns it
into an `EntailedGeneratedAlignment` after prepending the reference.
-/

namespace TypePM.Source

namespace EntailedGeneratedAlignment

/-- Two generated blocks with semantically equivalent hard worklists and
literal target/pending payloads are entailed-aligned.  This is the transport
used to move each alias-reallocated interface presentation to the common
two-interface reference. -/
theorem of_hardEquivalent_sameTargetPending
    {left right : Generated}
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (targetEqual : left.target = right.target)
    (pendingEqual : left.pending = right.pending) :
    EntailedGeneratedAlignment left right := by
  refine ⟨hardEquivalent, ?_, ?_⟩
  · intro substitution _solved
    rw [targetEqual]
  · rw [pendingEqual]
    induction right.pending with
    | nil => exact .nil
    | cons obligation pending induction =>
        exact .cons (EntailedObligationEq.refl left.hard obligation) induction

end EntailedGeneratedAlignment

/-- Every solution of `reference` is invariant under precomposition by
`rho`.  This is the semantic fixed-point condition that interface aliases
must establish in the whole-`let` proof. -/
def EntailedRenamingFixed
    (reference : List Equation) (rho : VariableRenaming) : Prop :=
  ∀ substitution, Solves substitution reference →
    Subst.compose substitution rho.substitution = substitution

/-- Support-local form used by source elaboration.  Closure representatives
may move generalized variables that cannot occur free in the body, so global
substitution equality is unnecessarily strong. -/
def EntailedRenamingFixedOn
    (reference : List Equation) (rho : VariableRenaming)
    (support : List UnificationVar) : Prop :=
  ∀ substitution, Solves substitution reference →
    (∀ index, (.ty index : UnificationVar) ∈ support →
      substitution.ty (rho.tyForward index) = substitution.ty index) ∧
    (∀ index, (.cap index : UnificationVar) ∈ support →
      substitution.cap (rho.capForward index) = substitution.cap index)

/-- Prepend a common hard reference without changing the target or delayed
obligations. -/
def generatedUnderReference
    (reference : List Equation) (generated : Generated) : Generated :=
  { generated with hard := reference ++ generated.hard }

namespace EntailedRenamingFixed

/-- A finite support proof is enough: outside the support the renaming is
literally fixed, while the reference only has to identify the moved names
inside the support. -/
theorem of_support
    {reference : List Equation} {rho : VariableRenaming}
    (support : List UnificationVar)
    (tyOutside : ∀ index, (.ty index : UnificationVar) ∉ support →
      rho.tyForward index = index)
    (capOutside : ∀ index, (.cap index : UnificationVar) ∉ support →
      rho.capForward index = index)
    (tyInside : ∀ substitution, Solves substitution reference →
      ∀ index, (.ty index : UnificationVar) ∈ support →
        substitution.ty (rho.tyForward index) = substitution.ty index)
    (capInside : ∀ substitution, Solves substitution reference →
      ∀ index, (.cap index : UnificationVar) ∈ support →
        substitution.cap (rho.capForward index) = substitution.cap index) :
    EntailedRenamingFixed reference rho := by
  intro substitution solved
  apply Subst.eq_of_components
  · intro index
    by_cases member : (.cap index : UnificationVar) ∈ support
    · simpa [Subst.compose, VariableRenaming.substitution, Cap.apply] using
        capInside substitution solved index member
    · simp [Subst.compose, VariableRenaming.substitution, Cap.apply,
        capOutside index member]
  · intro index
    by_cases member : (.ty index : UnificationVar) ∈ support
    · simpa [Subst.compose, VariableRenaming.substitution, Ty.apply] using
        tyInside substitution solved index member
    · simp [Subst.compose, VariableRenaming.substitution, Ty.apply,
        tyOutside index member]

theorem renameTy_apply_eq
    {reference : List Equation} {rho : VariableRenaming}
    (fixed : EntailedRenamingFixed reference rho)
    {substitution : Subst} (solved : Solves substitution reference)
    (target : Ty) :
    (ElaborationRenaming.renameTy rho target).apply substitution =
      target.apply substitution := by
  simp only [ElaborationRenaming.renameTy, Ty.apply_compose]
  rw [fixed substitution solved]

theorem renameObligation_apply_eq
    {reference : List Equation} {rho : VariableRenaming}
    (fixed : EntailedRenamingFixed reference rho)
    {substitution : Subst} (solved : Solves substitution reference)
    (obligation : CheckObligation) :
    (ElaborationRenaming.renameObligation rho obligation).apply substitution =
      obligation.apply substitution := by
  cases obligation with
  | mk source expected =>
      simp only [ElaborationRenaming.renameObligation,
        CheckObligation.apply, Ty.apply_compose]
      rw [fixed substitution solved]

theorem solves_renamed_iff
    {reference : List Equation} {rho : VariableRenaming}
    (fixed : EntailedRenamingFixed reference rho)
    {substitution : Subst} (referenceSolved : Solves substitution reference)
    (equations : List Equation) :
    Solves substitution
        (equations.map (ElaborationRenaming.renameEquation rho)) ↔
      Solves substitution equations := by
  rw [show ElaborationRenaming.renameEquation rho =
      Equation.apply rho.substitution from rfl,
    solves_map_apply, fixed substitution referenceSolved]

private theorem pendingAligned
    {reference : List Equation} {rho : VariableRenaming}
    (fixed : EntailedRenamingFixed reference rho)
    (hard : List Equation) :
    ∀ pending : List CheckObligation,
      EntailedPendingEq (reference ++ hard) pending
        (pending.map (ElaborationRenaming.renameObligation rho))
  | [] => .nil
  | obligation :: pending => by
      apply EntailedPendingEq.cons
      · intro substitution solved
        have referenceSolved :=
          (solves_append substitution reference hard).mp solved |>.1
        exact (fixed.renameObligation_apply_eq referenceSolved obligation).symm
      · exact pendingAligned fixed hard pending

/-- Once a common hard reference makes the renaming semantically fixed, a
generated block and its renamed image are entailed-aligned under that
reference.  This is deliberately stronger than root-level alpha-invariance
and is stable under all later frame composition performed by
`EntailedGeneratedAlignment`. -/
theorem generated
    {reference : List Equation} {rho : VariableRenaming}
    (fixed : EntailedRenamingFixed reference rho)
    (body : Generated) :
    EntailedGeneratedAlignment
      (generatedUnderReference reference body)
      (generatedUnderReference reference
        (ElaborationRenaming.renameGenerated rho body)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro substitution
    simp only [generatedUnderReference,
      ElaborationRenaming.renameGenerated, solves_append]
    constructor
    · rintro ⟨referenceSolved, bodySolved⟩
      exact ⟨referenceSolved,
        (fixed.solves_renamed_iff referenceSolved body.hard).mpr bodySolved⟩
    · rintro ⟨referenceSolved, renamedSolved⟩
      exact ⟨referenceSolved,
        (fixed.solves_renamed_iff referenceSolved body.hard).mp renamedSolved⟩
  · intro substitution solved
    have referenceSolved :=
      (solves_append substitution reference body.hard).mp solved |>.1
    exact (fixed.renameTy_apply_eq referenceSolved body.target).symm
  · simpa [generatedUnderReference,
      ElaborationRenaming.renameGenerated] using
      pendingAligned fixed body.hard body.pending

end EntailedRenamingFixed

namespace EntailedRenamingFixedOn

theorem of_global
    {reference : List Equation} {rho : VariableRenaming}
    (fixed : EntailedRenamingFixed reference rho)
    (support : List UnificationVar) :
    EntailedRenamingFixedOn reference rho support := by
  intro substitution solved
  have equality := fixed substitution solved
  constructor
  · intro index _member
    have component := congrArg (fun current => current.ty index) equality
    simpa [Subst.compose, VariableRenaming.substitution, Ty.apply] using component
  · intro index _member
    have component := congrArg (fun current => current.cap index) equality
    simpa [Subst.compose, VariableRenaming.substitution, Cap.apply] using component

theorem antitone
    {reference : List Equation} {rho : VariableRenaming}
    {larger smaller : List UnificationVar}
    (fixed : EntailedRenamingFixedOn reference rho larger)
    (subset : ∀ candidate, candidate ∈ smaller → candidate ∈ larger) :
    EntailedRenamingFixedOn reference rho smaller := by
  intro substitution solved
  have facts := fixed substitution solved
  exact
    ⟨fun index member => facts.1 index (subset _ member),
      fun index member => facts.2 index (subset _ member)⟩

theorem renameTy_apply_eq
    {reference : List Equation} {rho : VariableRenaming}
    {support : List UnificationVar}
    (fixed : EntailedRenamingFixedOn reference rho support)
    {substitution : Subst} (solved : Solves substitution reference)
    (target : Ty)
    (supported : ∀ candidate, candidate ∈ target.unificationVars →
      candidate ∈ support) :
    (ElaborationRenaming.renameTy rho target).apply substitution =
      target.apply substitution := by
  simp only [ElaborationRenaming.renameTy, Ty.apply_compose]
  apply Ty.apply_eq_of_agree target
  · intro index member
    exact (fixed substitution solved).1 index
      (supported (.ty index)
        ((Ty.mem_tyVars_iff_unificationVars index target).mp member))
  · intro index member
    exact (fixed substitution solved).2 index
      (supported (.cap index)
        ((Ty.mem_capVars_iff_unificationVars index target).mp member))

theorem renameObligation_apply_eq
    {reference : List Equation} {rho : VariableRenaming}
    {support : List UnificationVar}
    (fixed : EntailedRenamingFixedOn reference rho support)
    {substitution : Subst} (solved : Solves substitution reference)
    (obligation : CheckObligation)
    (supported : ∀ candidate,
      candidate ∈ obligation.unificationVars → candidate ∈ support) :
    (ElaborationRenaming.renameObligation rho obligation).apply substitution =
      obligation.apply substitution := by
  cases obligation with
  | mk source expected =>
      change CheckObligation.mk
          ((ElaborationRenaming.renameTy rho source).apply substitution)
          ((ElaborationRenaming.renameTy rho expected).apply substitution) =
        CheckObligation.mk (source.apply substitution)
          (expected.apply substitution)
      rw [fixed.renameTy_apply_eq solved source (by
        intro candidate member
        exact supported candidate (List.mem_append_left _ member)),
        fixed.renameTy_apply_eq solved expected (by
        intro candidate member
        exact supported candidate (List.mem_append_right _ member))]

theorem renameEquation_holds_iff
    {reference : List Equation} {rho : VariableRenaming}
    {support : List UnificationVar}
    (fixed : EntailedRenamingFixedOn reference rho support)
    {substitution : Subst} (solved : Solves substitution reference)
    (equation : Equation)
    (supported : ∀ candidate,
      candidate ∈ equation.unificationVars → candidate ∈ support) :
    (ElaborationRenaming.renameEquation rho equation).Holds substitution ↔
      equation.Holds substitution := by
  cases equation with
  | ty left right =>
      change
        (ElaborationRenaming.renameTy rho left).apply substitution =
            (ElaborationRenaming.renameTy rho right).apply substitution ↔
          left.apply substitution = right.apply substitution
      rw [fixed.renameTy_apply_eq solved left (by
            intro candidate member
            exact supported candidate (List.mem_append_left _ member)),
        fixed.renameTy_apply_eq solved right (by
            intro candidate member
            exact supported candidate (List.mem_append_right _ member))]
  | cap left right =>
      change
        (ElaborationRenaming.renameCap rho left).apply substitution.cap =
            (ElaborationRenaming.renameCap rho right).apply substitution.cap ↔
          left.apply substitution.cap = right.apply substitution.cap
      simp only [ElaborationRenaming.renameCap, Cap.apply_compose]
      have facts := fixed substitution solved
      have leftEq : left.apply
          (Subst.compose substitution rho.substitution).cap =
          left.apply substitution.cap := by
        apply Cap.apply_eq_of_agree left
        intro index member
        exact facts.2 index (supported (.cap index)
          (List.mem_append_left _
            ((Cap.mem_capVars_iff_unificationVars index left).mp member)))
      have rightEq : right.apply
          (Subst.compose substitution rho.substitution).cap =
          right.apply substitution.cap := by
        apply Cap.apply_eq_of_agree right
        intro index member
        exact facts.2 index (supported (.cap index)
          (List.mem_append_right _
            ((Cap.mem_capVars_iff_unificationVars index right).mp member)))
      rw [leftEq, rightEq]

private theorem hardEquivalent
    {reference : List Equation} {rho : VariableRenaming}
    {support : List UnificationVar}
    (fixed : EntailedRenamingFixedOn reference rho support)
    (hard : List Equation)
    (supported : ∀ equation, equation ∈ hard →
      ∀ candidate, candidate ∈ equation.unificationVars →
        candidate ∈ support) :
    HardEquivalent (reference ++ hard)
      (reference ++ hard.map (ElaborationRenaming.renameEquation rho)) := by
  intro substitution
  simp only [solves_append]
  constructor
  · rintro ⟨referenceSolved, hardSolved⟩
    refine ⟨referenceSolved, ?_⟩
    intro equation member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (fixed.renameEquation_holds_iff referenceSolved original
      (supported original originalMember)).mpr
      (hardSolved original originalMember)
  · rintro ⟨referenceSolved, renamedSolved⟩
    refine ⟨referenceSolved, ?_⟩
    intro equation member
    exact (fixed.renameEquation_holds_iff referenceSolved equation
      (supported equation member)).mp
      (renamedSolved _ (List.mem_map.mpr ⟨equation, member, rfl⟩))

private theorem equationSupport_mem
    {hard : List Equation} {equation : Equation}
    (equationMember : equation ∈ hard)
    {candidate : UnificationVar}
    (candidateMember : candidate ∈ equation.unificationVars) :
    candidate ∈ TypePM.unificationVars hard := by
  induction hard with
  | nil => simp at equationMember
  | cons head tail induction =>
      simp only [List.mem_cons] at equationMember
      simp only [TypePM.unificationVars, List.mem_append]
      rcases equationMember with rfl | tailMember
      · exact Or.inl candidateMember
      · exact Or.inr (induction tailMember)

private theorem pendingAligned
    {reference : List Equation} {rho : VariableRenaming}
    {support : List UnificationVar}
    (fixed : EntailedRenamingFixedOn reference rho support)
    (hard : List Equation) :
    ∀ pending : List CheckObligation,
      (∀ obligation, obligation ∈ pending →
        ∀ candidate, candidate ∈ obligation.unificationVars →
          candidate ∈ support) →
      EntailedPendingEq (reference ++ hard) pending
        (pending.map (ElaborationRenaming.renameObligation rho))
  | [], _supported => .nil
  | obligation :: pending, supported => by
      apply EntailedPendingEq.cons
      · intro substitution solved
        have referenceSolved :=
          (solves_append substitution reference hard).mp solved |>.1
        exact (fixed.renameObligation_apply_eq referenceSolved obligation
          (supported obligation (by simp))).symm
      · apply pendingAligned fixed hard pending
        intro item itemMember
        exact supported item (by simp [itemMember])

/-- Support-local semantic renaming alignment.  Only variables that actually
occur in the generated block must be fixed by the hard reference. -/
theorem generated
    {reference : List Equation} {rho : VariableRenaming}
    (body : Generated)
    (fixed : EntailedRenamingFixedOn reference rho body.unificationVars) :
    EntailedGeneratedAlignment
      (generatedUnderReference reference body)
      (generatedUnderReference reference
        (ElaborationRenaming.renameGenerated rho body)) := by
  refine ⟨hardEquivalent fixed body.hard ?_, ?_, ?_⟩
  · intro equation equationMember candidate candidateMember
    simp only [Generated.unificationVars, List.mem_append]
    exact Or.inl (Or.inr
      (equationSupport_mem equationMember candidateMember))
  · intro substitution solved
    have referenceSolved :=
      (solves_append substitution reference body.hard).mp solved |>.1
    exact (fixed.renameTy_apply_eq referenceSolved body.target
      (fun candidate member => by
        simp [Generated.unificationVars, member])).symm
  · apply pendingAligned fixed body.hard body.pending
    intro obligation obligationMember candidate candidateMember
    simp [Generated.unificationVars,
      mem_pendingUnificationVars obligationMember candidateMember]

end EntailedRenamingFixedOn

end TypePM.Source
