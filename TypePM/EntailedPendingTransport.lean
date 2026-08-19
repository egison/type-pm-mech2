import TypePM.DeclarativeCoverage
import TypePM.HardWorklistEquivalence

/-!
# Transport across semantically aligned pending obligations

Two delayed checking obligations need not be literally equal in order to
make the same saturation decisions.  It is enough that applying every
solution of a reference hard worklist makes them equal.  This file proves
that such pointwise alignment, together with semantic equivalence of the
initial hard worklists, preserves and reflects generated-block acceptance.
-/

namespace TypePM

/-- Two delayed obligations agree after every solution of `reference` is
applied. -/
def EntailedObligationEq (reference : List Equation)
    (left right : CheckObligation) : Prop :=
  ∀ substitution, Solves substitution reference →
    left.apply substitution = right.apply substitution

namespace EntailedObligationEq

theorem refl (reference : List Equation) (obligation : CheckObligation) :
    EntailedObligationEq reference obligation obligation := by
  intro substitution solved
  rfl

theorem symm {reference : List Equation} {left right : CheckObligation}
    (aligned : EntailedObligationEq reference left right) :
    EntailedObligationEq reference right left := by
  intro substitution solved
  exact (aligned substitution solved).symm

theorem weaken {stronger weaker : List Equation}
    {left right : CheckObligation}
    (aligned : EntailedObligationEq weaker left right)
    (entails : ∀ substitution, Solves substitution stronger →
      Solves substitution weaker) :
    EntailedObligationEq stronger left right := by
  intro substitution solved
  exact aligned substitution (entails substitution solved)

end EntailedObligationEq

/-- Pointwise entailed equality for two pending-obligation lists. -/
inductive EntailedPendingEq (reference : List Equation) :
    List CheckObligation → List CheckObligation → Prop where
  | nil : EntailedPendingEq reference [] []
  | cons {leftHead rightHead leftTail rightTail} :
      EntailedObligationEq reference leftHead rightHead →
      EntailedPendingEq reference leftTail rightTail →
      EntailedPendingEq reference
        (leftHead :: leftTail) (rightHead :: rightTail)

namespace EntailedPendingEq

theorem symm_of_hardEquivalent
    {leftReference rightReference : List Equation}
    {left right : List CheckObligation}
    (aligned : EntailedPendingEq leftReference left right)
    (equivalent : HardEquivalent leftReference rightReference) :
    EntailedPendingEq rightReference right left := by
  induction aligned with
  | nil => exact .nil
  | @cons leftHead rightHead leftTail rightTail headAligned tailAligned
      induction =>
      apply EntailedPendingEq.cons
      · intro substitution rightSolved
        exact (headAligned substitution
          ((equivalent substitution).mpr rightSolved)).symm
      · exact induction

end EntailedPendingEq

private theorem equation_holds_iff_of_apply_eq
    {left right : CheckObligation} {substitution : Subst}
    (equal : left.apply substitution = right.apply substitution) :
    (Equation.ty left.source left.expected).Holds substitution ↔
      (Equation.ty right.source right.expected).Holds substitution := by
  have sourceEqual := congrArg CheckObligation.source equal
  have expectedEqual := congrArg CheckObligation.expected equal
  change left.source.apply substitution =
    right.source.apply substitution at sourceEqual
  change left.expected.apply substitution =
    right.expected.apply substitution at expectedEqual
  simp only [Equation.Holds]
  rw [sourceEqual, expectedEqual]

private theorem residualEquations_eq_of_apply_eq
    {left right : CheckObligation} {substitution : Subst}
    (equal : left.apply substitution = right.apply substitution) :
    left.residualEquations substitution =
      right.residualEquations substitution := by
  have sourceEqual := congrArg CheckObligation.source equal
  have expectedEqual := congrArg CheckObligation.expected equal
  change left.source.apply substitution =
    right.source.apply substitution at sourceEqual
  change left.expected.apply substitution =
    right.expected.apply substitution at expectedEqual
  simp only [CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  rw [sourceEqual, expectedEqual]

/-- One synchronized promotion pass.  Equal normalized obligations make the
same branch decision.  Retained obligations remain aligned, while emitted
ordinary equations have the same solution set under every solution of the
reference hard worklist. -/
private theorem promoteUnder_entailed
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right)
    {classification : Subst} (classificationSolved :
      Solves classification reference) :
    let leftPromotion := promoteUnder classification left
    let rightPromotion := promoteUnder classification right
    EntailedPendingEq reference
      leftPromotion.pending rightPromotion.pending ∧
      (∀ substitution, Solves substitution reference →
        (Solves substitution leftPromotion.equations ↔
          Solves substitution rightPromotion.equations)) ∧
      (leftPromotion.equations = [] ↔
        rightPromotion.equations = []) := by
  induction aligned with
  | nil =>
      exact ⟨EntailedPendingEq.nil, by simp [promoteUnder],
        by simp [promoteUnder]⟩
  | @cons leftHead rightHead leftTail rightTail headAligned tailAligned
      induction =>
      have appliedEqual := headAligned classification classificationSolved
      have possibleEqual :
          (leftHead.source.apply classification).couldSpecial
              (leftHead.expected.apply classification) =
            (rightHead.source.apply classification).couldSpecial
              (rightHead.expected.apply classification) := by
        have sourceEqual := congrArg CheckObligation.source appliedEqual
        have expectedEqual := congrArg CheckObligation.expected appliedEqual
        change leftHead.source.apply classification =
          rightHead.source.apply classification at sourceEqual
        change leftHead.expected.apply classification =
          rightHead.expected.apply classification at expectedEqual
        rw [sourceEqual, expectedEqual]
      rcases induction with ⟨tailPending, tailEquations, tailEmpty⟩
      by_cases possible :
          (leftHead.source.apply classification).couldSpecial
              (leftHead.expected.apply classification) = true
      · have rightPossible :
            (rightHead.source.apply classification).couldSpecial
                (rightHead.expected.apply classification) = true := by
          rw [← possibleEqual]
          exact possible
        simp only [promoteUnder, possible, rightPossible]
        exact ⟨EntailedPendingEq.cons headAligned tailPending,
          tailEquations, tailEmpty⟩
      · have rightPossible :
            (rightHead.source.apply classification).couldSpecial
                (rightHead.expected.apply classification) = false := by
          rw [← possibleEqual]
          cases value :
              (leftHead.source.apply classification).couldSpecial
                (leftHead.expected.apply classification) <;> simp_all
        have leftPossible :
            (leftHead.source.apply classification).couldSpecial
            (leftHead.expected.apply classification) = false := by
          cases value :
              (leftHead.source.apply classification).couldSpecial
                (leftHead.expected.apply classification) <;> simp_all
        simp only [promoteUnder, leftPossible, rightPossible,
          Bool.false_eq_true, ↓reduceIte]
        refine ⟨tailPending, ?_, ?_⟩
        · intro substitution solved
          rw [solves_cons, solves_cons]
          exact and_congr
            (equation_holds_iff_of_apply_eq
              (headAligned substitution solved))
            (tailEquations substitution solved)
        · simp

private theorem residualEquations_eq_of_entailed
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right)
    {substitution : Subst} (solved : Solves substitution reference) :
    residualEquations substitution left =
      residualEquations substitution right := by
  induction aligned with
  | nil => rfl
  | @cons leftHead rightHead leftTail rightTail headAligned tailAligned
      induction =>
      simp only [residualEquations]
      rw [residualEquations_eq_of_apply_eq
        (headAligned substitution solved), induction]

private theorem hard_append_equivalent
    {reference leftHard rightHard leftAdded rightAdded : List Equation}
    (hardEquivalent : HardEquivalent leftHard rightHard)
    (leftEntailsReference : ∀ substitution,
      Solves substitution leftHard → Solves substitution reference)
    (addedEquivalent : ∀ substitution, Solves substitution reference →
      (Solves substitution leftAdded ↔ Solves substitution rightAdded)) :
    HardEquivalent (leftHard ++ leftAdded) (rightHard ++ rightAdded) := by
  intro substitution
  simp only [solves_append]
  constructor
  · rintro ⟨leftSolved, leftAddedSolved⟩
    exact ⟨(hardEquivalent substitution).mp leftSolved,
      (addedEquivalent substitution
        (leftEntailsReference substitution leftSolved)).mp leftAddedSolved⟩
  · rintro ⟨rightSolved, rightAddedSolved⟩
    have leftSolved := (hardEquivalent substitution).mpr rightSolved
    exact ⟨leftSolved,
      (addedEquivalent substitution
        (leftEntailsReference substitution leftSolved)).mpr rightAddedSolved⟩

private theorem appended_entails_reference
    {reference hard added : List Equation}
    (entails : ∀ substitution,
      Solves substitution hard → Solves substitution reference) :
    ∀ substitution, Solves substitution (hard ++ added) →
      Solves substitution reference := by
  intro substitution solved
  exact entails substitution (solves_append substitution hard added |>.mp solved).1

namespace PromotionClosure

/-- Transport a promotion closure while synchronizing semantically aligned
pending obligations.  The theorem keeps the original left hard worklist as
the reference throughout; the explicit entailment invariant records that
promotion only appends hard equations. -/
private theorem transportEntailedAux
    {reference leftHard leftPending finalHard finalPending}
    (closure : PromotionClosure leftHard leftPending finalHard finalPending)
    {rightHard rightPending : List _}
    (hardEquivalent : HardEquivalent leftHard rightHard)
    (pendingAligned : EntailedPendingEq reference
      leftPending rightPending)
    (leftEntailsReference : ∀ substitution,
      Solves substitution leftHard → Solves substitution reference) :
    ∃ transportedHard transportedPending,
      PromotionClosure rightHard rightPending
        transportedHard transportedPending ∧
      HardEquivalent finalHard transportedHard ∧
      EntailedPendingEq reference finalPending transportedPending := by
  induction closure generalizing rightHard rightPending with
  | @refl hard pending =>
      exact ⟨rightHard, rightPending, .refl, hardEquivalent,
        pendingAligned⟩
  | @step hard pending substitution promoted finalHard finalPending
      principal promotion progress tail induction =>
      have rightPrincipal : MostGeneral rightHard substitution :=
        (HardEquivalent.mostGeneral_iff hardEquivalent substitution).mp
          principal
      have referenceSolved : Solves substitution reference :=
        leftEntailsReference substitution principal.1
      have pass := promoteUnder_entailed pendingAligned referenceSolved
      let rightPromoted := promoteUnder substitution rightPending
      have pendingNext : EntailedPendingEq reference
          promoted.pending rightPromoted.pending := by
        rw [← promotion]
        exact pass.1
      have equationsNext : ∀ candidate, Solves candidate reference →
          (Solves candidate promoted.equations ↔
            Solves candidate rightPromoted.equations) := by
        intro candidate solved
        rw [← promotion]
        exact pass.2.1 candidate solved
      have rightProgress : rightPromoted.equations ≠ [] := by
        intro empty
        apply progress
        rw [← promotion]
        exact pass.2.2.mpr empty
      have appendedEquivalent :
          HardEquivalent (hard ++ promoted.equations)
            (rightHard ++ rightPromoted.equations) :=
        hard_append_equivalent hardEquivalent leftEntailsReference
          equationsNext
      obtain ⟨transportedHard, transportedPending, transportedTail,
          finalEquivalent, finalAligned⟩ :=
        induction appendedEquivalent pendingNext
          (appended_entails_reference leftEntailsReference)
      exact ⟨transportedHard, transportedPending,
        .step rightPrincipal rfl rightProgress transportedTail,
        finalEquivalent, finalAligned⟩

/-- A promotion closure transports across semantic hard equivalence and
entailed pointwise alignment of its initial pending worklists. -/
theorem transportEntailed
    {leftHard leftPending finalHard finalPending}
    (closure : PromotionClosure leftHard leftPending finalHard finalPending)
    {rightHard rightPending : List _}
    (hardEquivalent : HardEquivalent leftHard rightHard)
    (pendingAligned : EntailedPendingEq leftHard
      leftPending rightPending) :
    ∃ transportedHard transportedPending,
      PromotionClosure rightHard rightPending
        transportedHard transportedPending ∧
      HardEquivalent finalHard transportedHard ∧
      EntailedPendingEq leftHard finalPending transportedPending := by
  exact closure.transportEntailedAux hardEquivalent pendingAligned
    (fun _ solved => solved)

end PromotionClosure

namespace Saturated

/-- Saturation transports across entailed pending alignment while preserving
the final hard substitution. -/
theorem transportEntailed
    {leftHard leftPending finalHard finalPending substitution}
    (saturated : Saturated leftHard leftPending finalHard finalPending
      substitution)
    {rightHard rightPending : List _}
    (hardEquivalent : HardEquivalent leftHard rightHard)
    (pendingAligned : EntailedPendingEq leftHard
      leftPending rightPending) :
    ∃ transportedHard transportedPending,
      Saturated rightHard rightPending transportedHard transportedPending
        substitution ∧
      HardEquivalent finalHard transportedHard ∧
      EntailedPendingEq leftHard finalPending transportedPending := by
  obtain ⟨transportedHard, transportedPending, transportedClosure,
      finalEquivalent, finalAligned⟩ :=
    saturated.closure.transportEntailed hardEquivalent pendingAligned
  have referenceSolved : Solves substitution leftHard := by
    intro equation membership
    exact saturated.principal.1 equation
      (saturated.closure.hard_mem_final equation membership)
  have finalApplied := promoteUnder_entailed finalAligned referenceSolved
  have transportedStable :
      (promoteUnder substitution transportedPending).equations = [] := by
    exact finalApplied.2.2.mp saturated.stable
  exact ⟨transportedHard, transportedPending,
    { closure := transportedClosure
      principal :=
        (HardEquivalent.mostGeneral_iff finalEquivalent substitution).mp
          saturated.principal
      stable := transportedStable },
    finalEquivalent, finalAligned⟩

end Saturated

namespace BlockAccepts

/-- One-way acceptance transport across semantic hard equivalence and
entailed pointwise alignment of pending obligations. -/
theorem transportEntailed
    {left right : Generated}
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingAligned : EntailedPendingEq left.hard
      left.pending right.pending)
    (accepts : BlockAccepts left) :
    BlockAccepts right := by
  rcases accepts with
    ⟨finalHard, finalPending, hardSubstitution, residualSubstitution,
      saturated, residualSolved⟩
  obtain ⟨transportedHard, transportedPending, transportedSaturated,
      _finalEquivalent, finalAligned⟩ :=
    saturated.transportEntailed hardEquivalent pendingAligned
  have referenceSolved : Solves hardSubstitution left.hard := by
    intro equation membership
    exact saturated.principal.1 equation
      (saturated.closure.hard_mem_final equation membership)
  have residualEqual :
      residualEquations hardSubstitution finalPending =
        residualEquations hardSubstitution transportedPending :=
    residualEquations_eq_of_entailed finalAligned referenceSolved
  exact ⟨transportedHard, transportedPending, hardSubstitution,
    residualSubstitution, transportedSaturated,
    residualEqual ▸ residualSolved⟩

/-- Semantic equivalence of hard worklists and entailed pointwise alignment
of delayed obligations preserve and reflect generated-block acceptance. -/
theorem iff_of_entailedAligned
    {left right : Generated}
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingAligned : EntailedPendingEq left.hard
      left.pending right.pending) :
    BlockAccepts left ↔ BlockAccepts right := by
  constructor
  · exact transportEntailed hardEquivalent pendingAligned
  · exact transportEntailed hardEquivalent.symm
      (pendingAligned.symm_of_hardEquivalent hardEquivalent)

end BlockAccepts

end TypePM
