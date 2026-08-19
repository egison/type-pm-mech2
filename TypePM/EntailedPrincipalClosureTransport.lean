import TypePM.AbsorbingBlockClosure
import TypePM.EntailedPendingTransport

/-!
# Principal-closure transport across entailed pending alignment

The acceptance transport in `EntailedPendingTransport` preserves the hard
and residual substitutions selected by a concrete witness.  Here the same
construction is strengthened to preserve a `PrincipalBlockClosure`: the
transported residual worklist is literally equal after applying the shared
hard substitution, so the original residual most-general solution remains
most general.
-/

namespace TypePM

private theorem absorbingPrincipal_of_hardEquivalent
    {left right : List Equation} {principal : Subst}
    (equivalent : HardEquivalent left right)
    (absorbing : AbsorbingPrincipal left principal) :
    AbsorbingPrincipal right principal := by
  constructor
  · exact (HardEquivalent.mostGeneral_iff equivalent principal).mp
      absorbing.mostGeneral
  · intro solution rightSolved
    exact absorbing.absorbs ((equivalent solution).mpr rightSolved)

private theorem residualEquations_eq_of_entailedPendingEq
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right)
    {substitution : Subst} (solved : Solves substitution reference) :
    residualEquations substitution left =
      residualEquations substitution right := by
  induction aligned with
  | nil => rfl
  | @cons leftHead rightHead leftTail rightTail headAligned tailAligned
      induction =>
      have appliedEqual := headAligned substitution solved
      have sourceEqual := congrArg CheckObligation.source appliedEqual
      have expectedEqual := congrArg CheckObligation.expected appliedEqual
      change leftHead.source.apply substitution =
        rightHead.source.apply substitution at sourceEqual
      change leftHead.expected.apply substitution =
        rightHead.expected.apply substitution at expectedEqual
      simp only [residualEquations,
        CheckObligation.residualEquations,
        CheckObligation.resolutionUnder]
      rw [sourceEqual, expectedEqual, induction]

namespace PrincipalBlockClosure

/-- Transport one concrete principal closure across semantic equivalence of
the hard worklists and entailed pointwise alignment of the pending
obligations.  Both selected substitutions are preserved literally. -/
theorem transportEntailed
    {left right : Generated}
    (closure : PrincipalBlockClosure left)
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingAligned : EntailedPendingEq left.hard
      left.pending right.pending) :
    ∃ transported : PrincipalBlockClosure right,
      transported.hardSubstitution = closure.hardSubstitution ∧
      transported.residualSubstitution = closure.residualSubstitution ∧
      transported.substitution = closure.substitution := by
  obtain ⟨transportedHard, transportedPending, transportedSaturation,
      _finalEquivalent, finalAligned⟩ :=
    closure.saturation.transportEntailed hardEquivalent pendingAligned
  have initialSolved : Solves closure.hardSubstitution left.hard := by
    intro equation membership
    exact closure.saturation.principal.1 equation
      (closure.saturation.closure.hard_mem_final equation membership)
  have residualEqual :
      residualEquations closure.hardSubstitution closure.finalPending =
        residualEquations closure.hardSubstitution transportedPending :=
    residualEquations_eq_of_entailedPendingEq finalAligned initialSolved
  let transported : PrincipalBlockClosure right :=
    { finalHard := transportedHard
      finalPending := transportedPending
      hardSubstitution := closure.hardSubstitution
      residualSubstitution := closure.residualSubstitution
      saturation := transportedSaturation
      residualPrincipal := by
        rw [← residualEqual]
        exact closure.residualPrincipal }
  exact ⟨transported, rfl, rfl, rfl⟩

/-- Transport an absorbing principal closure while retaining the same hard,
residual, and composed substitutions.  Semantic equivalence preserves the
absorbing property of the final hard solution; literal equality of the
transported residual worklists preserves it for the residual solution. -/
theorem transportEntailed_absorbing
    {left right : Generated}
    (closure : PrincipalBlockClosure left)
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingAligned : EntailedPendingEq left.hard
      left.pending right.pending)
    (absorbing : closure.Absorbing) :
    ∃ transported : PrincipalBlockClosure right,
      transported.hardSubstitution = closure.hardSubstitution ∧
      transported.residualSubstitution = closure.residualSubstitution ∧
      transported.substitution = closure.substitution ∧
      transported.Absorbing := by
  obtain ⟨transportedHard, transportedPending, transportedSaturation,
      finalEquivalent, finalAligned⟩ :=
    closure.saturation.transportEntailed hardEquivalent pendingAligned
  have initialSolved : Solves closure.hardSubstitution left.hard := by
    intro equation membership
    exact closure.saturation.principal.1 equation
      (closure.saturation.closure.hard_mem_final equation membership)
  have residualEqual :
      residualEquations closure.hardSubstitution closure.finalPending =
        residualEquations closure.hardSubstitution transportedPending :=
    residualEquations_eq_of_entailedPendingEq finalAligned initialSolved
  have transportedHardAbsorbing :
      AbsorbingPrincipal transportedHard closure.hardSubstitution :=
    absorbingPrincipal_of_hardEquivalent finalEquivalent absorbing.1
  have transportedResidualAbsorbing :
      AbsorbingPrincipal
        (residualEquations closure.hardSubstitution transportedPending)
        closure.residualSubstitution := by
    rw [← residualEqual]
    exact absorbing.2
  let transported : PrincipalBlockClosure right :=
    { finalHard := transportedHard
      finalPending := transportedPending
      hardSubstitution := closure.hardSubstitution
      residualSubstitution := closure.residualSubstitution
      saturation := transportedSaturation
      residualPrincipal := transportedResidualAbsorbing.mostGeneral }
  exact ⟨transported, rfl, rfl, rfl,
    transportedHardAbsorbing, transportedResidualAbsorbing⟩

/-- The composed substitution selected by a principal closure solves its
initial hard worklist. -/
theorem substitution_solves_initialHard
    {generated : Generated}
    (closure : PrincipalBlockClosure generated) :
    Solves closure.substitution generated.hard := by
  intro equation membership
  exact closure.finalHard_solved equation
    (closure.saturation.closure.hard_mem_final equation membership)

/-- If the two result types agree under every solution of the left hard
worklist, principal-closure transport preserves the closed result type as
well as both component substitutions. -/
theorem transportEntailed_target
    {left right : Generated}
    (closure : PrincipalBlockClosure left)
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingAligned : EntailedPendingEq left.hard
      left.pending right.pending)
    (targetEntailed : ∀ substitution, Solves substitution left.hard →
      left.target.apply substitution = right.target.apply substitution) :
    ∃ transported : PrincipalBlockClosure right,
      transported.hardSubstitution = closure.hardSubstitution ∧
      transported.residualSubstitution = closure.residualSubstitution ∧
      transported.substitution = closure.substitution ∧
      closure.target = transported.target := by
  obtain ⟨transported, hardEqual, residualEqual, substitutionEqual⟩ :=
    closure.transportEntailed hardEquivalent pendingAligned
  refine ⟨transported, hardEqual, residualEqual, substitutionEqual, ?_⟩
  simp only [PrincipalBlockClosure.target]
  rw [substitutionEqual]
  exact targetEntailed closure.substitution
    closure.substitution_solves_initialHard

/-- Combined endpoint for an absorbing closure and an entailed result type:
the transported closure keeps both selected substitutions, remains
absorbing, and closes the two result types to the same type. -/
theorem transportEntailed_absorbing_target
    {left right : Generated}
    (closure : PrincipalBlockClosure left)
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingAligned : EntailedPendingEq left.hard
      left.pending right.pending)
    (absorbing : closure.Absorbing)
    (targetEntailed : ∀ substitution, Solves substitution left.hard →
      left.target.apply substitution = right.target.apply substitution) :
    ∃ transported : PrincipalBlockClosure right,
      transported.hardSubstitution = closure.hardSubstitution ∧
      transported.residualSubstitution = closure.residualSubstitution ∧
      transported.substitution = closure.substitution ∧
      transported.Absorbing ∧
      closure.target = transported.target := by
  obtain ⟨transported, hardEqual, residualEqual, substitutionEqual,
      transportedAbsorbing⟩ :=
    closure.transportEntailed_absorbing hardEquivalent pendingAligned
      absorbing
  refine ⟨transported, hardEqual, residualEqual, substitutionEqual,
    transportedAbsorbing, ?_⟩
  simp only [PrincipalBlockClosure.target]
  rw [substitutionEqual]
  exact targetEntailed closure.substitution
    closure.substitution_solves_initialHard

end PrincipalBlockClosure

end TypePM
