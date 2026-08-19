import TypePM.InferenceProcedure
import TypePM.ResolutionTransport
import TypePM.Solver

/-!
# Principal closure of a let-free constraint block

Let generalization must close the right-hand side with most-general solutions,
not with an arbitrary solution.  This module packages that declarative fact
without referring to the executable unifier.  The executable connection is a
separate theorem about `inferGeneratedUsing`.
-/

namespace TypePM

/-- A generated let-free block closed by a most-general hard solution and a
most-general residual checking solution. -/
structure PrincipalBlockClosure (generated : Generated) where
  finalHard : List Equation
  finalPending : List CheckObligation
  hardSubstitution : Subst
  residualSubstitution : Subst
  saturation :
    Saturated generated.hard generated.pending
      finalHard finalPending hardSubstitution
  residualPrincipal :
    MostGeneral
      (residualEquations hardSubstitution finalPending)
      residualSubstitution

namespace PrincipalBlockClosure

/-- The simultaneous substitution selected by both closure phases. -/
def substitution {generated : Generated}
    (closure : PrincipalBlockClosure generated) : Subst :=
  Subst.compose closure.residualSubstitution closure.hardSubstitution

/-- The principal result type of the generated block. -/
def target {generated : Generated}
    (closure : PrincipalBlockClosure generated) : Ty :=
  generated.target.apply closure.substitution

/-- The hard equations remain solved after the residual substitution. -/
theorem finalHard_solved {generated : Generated}
    (closure : PrincipalBlockClosure generated) :
    Solves closure.substitution closure.finalHard := by
  exact solves_postcompose closure.saturation.principal.1
    closure.residualSubstitution

/-- Every remaining checking obligation is valid under the composed principal
substitution. -/
theorem remaining_checkConversion {generated : Generated}
    (closure : PrincipalBlockClosure generated) :
    ∀ obligation ∈ closure.finalPending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply closure.substitution)
          (obligation.expected.apply closure.substitution) := by
  intro obligation membership
  obtain ⟨conversionClass, conversion⟩ := residualEquations_sound
    closure.residualPrincipal.1 obligation membership
  exact ⟨conversionClass, by
    simpa only [substitution, Ty.apply_compose] using conversion⟩

private theorem substitution_factors {generated : Generated}
    (general specific : PrincipalBlockClosure generated) :
    FactorsThrough general.substitution specific.substitution := by
  obtain ⟨forward, reverse⟩ :=
    general.saturation.finalSubstitutions_mutualFactors specific.saturation
  obtain ⟨post, hardFactor, transportedSolved⟩ :=
    ResolutionTransport.residualEquations_transport_of_mutualFactors
      forward reverse specific.residualPrincipal.1
  have pendingEquality :=
    (general.saturation.finalState_unique specific.saturation).2
  rw [← pendingEquality] at transportedSolved
  obtain ⟨later, residualFactor⟩ :=
    general.residualPrincipal.2 _ transportedSolved
  refine ⟨later, ?_⟩
  simp only [substitution]
  calc
    Subst.compose specific.residualSubstitution
        specific.hardSubstitution =
        Subst.compose specific.residualSubstitution
          (Subst.compose post general.hardSubstitution) := by
            rw [hardFactor]
    _ = Subst.compose
          (Subst.compose specific.residualSubstitution post)
          general.hardSubstitution :=
        Subst.compose_assoc _ _ _
    _ = Subst.compose
          (Subst.compose later general.residualSubstitution)
          general.hardSubstitution := by
        rw [residualFactor]
    _ = Subst.compose later
          (Subst.compose general.residualSubstitution
            general.hardSubstitution) :=
        (Subst.compose_assoc _ _ _).symm

/-- Principal closures of the same generated block differ only by mutually
factoring representative substitutions. -/
theorem substitutions_mutualFactors {generated : Generated}
    (left right : PrincipalBlockClosure generated) :
    FactorsThrough left.substitution right.substitution ∧
      FactorsThrough right.substitution left.substitution :=
  ⟨substitution_factors left right, substitution_factors right left⟩

/-- Principal result types of the same generated block are mutual
substitution instances. -/
theorem targets_mutualInstances {generated : Generated}
    (left right : PrincipalBlockClosure generated) :
    IsInstance left.target right.target ∧ IsInstance right.target left.target := by
  obtain ⟨leftToRight, rightToLeft⟩ :=
    left.substitutions_mutualFactors right
  constructor
  · obtain ⟨post, factor⟩ := leftToRight
    exact ⟨post, by
      simp only [target, Ty.apply_compose]
      rw [← factor]⟩
  · obtain ⟨post, factor⟩ := rightToLeft
    exact ⟨post, by
      simp only [target, Ty.apply_compose]
      rw [← factor]⟩

end PrincipalBlockClosure

/-- A successful executable block closure yields a declarative principal
closure with exactly the returned substitution and target. -/
theorem inferGeneratedUsing_principalBlockClosure
    {solve : List Equation → Option Subst}
    (solverPrincipal : ∀ equations substitution,
      solve equations = some substitution →
        MostGeneral equations substitution)
    {generated : Generated} {result : InferenceResult}
    (success : inferGeneratedUsing solve generated = some result) :
    ∃ closure : PrincipalBlockClosure generated,
      result.substitution = closure.substitution ∧
        result.target = closure.target := by
  unfold inferGeneratedUsing at success
  cases saturationResult :
      saturateUsing solve generated.hard generated.pending with
  | none => simp [saturationResult] at success
  | some saturated =>
      rw [saturationResult] at success
      change
        (solve (residualEquations saturated.substitution
            saturated.pending)).bind (fun residual =>
          some
            { substitution := Subst.compose residual saturated.substitution
              target := generated.target.apply
                (Subst.compose residual saturated.substitution) }) =
          some result at success
      cases residualResult :
          solve (residualEquations saturated.substitution saturated.pending) with
      | none => simp [residualResult] at success
      | some residual =>
          simp only [residualResult, Option.bind_some,
            Option.some.injEq] at success
          subst result
          let closure : PrincipalBlockClosure generated :=
            { finalHard := saturated.hard
              finalPending := saturated.pending
              hardSubstitution := saturated.substitution
              residualSubstitution := residual
              saturation := saturateUsing_sound solve solverPrincipal
                saturationResult
              residualPrincipal := solverPrincipal _ _ residualResult }
          exact ⟨closure, rfl, rfl⟩

/-- Every declarative principal block closure can be replayed by a complete
most-general-unifier implementation. -/
theorem PrincipalBlockClosure.inferGeneratedUsing_isSome
    {solve : List Equation → Option Subst}
    (solver : CompleteMGUSolver solve)
    {generated : Generated}
    (closure : PrincipalBlockClosure generated) :
    inferGeneratedUsing solve generated ≠ none := by
  obtain ⟨computed, saturationResult⟩ :=
    solver.saturateUsing_complete closure.saturation
  have computedSaturation :
      Saturated generated.hard generated.pending
        computed.hard computed.pending computed.substitution :=
    saturateUsing_sound solve solver.principal saturationResult
  obtain ⟨_, pendingEquality⟩ :=
    closure.saturation.finalState_unique computedSaturation
  obtain ⟨closureToComputed, computedToClosure⟩ :=
    closure.saturation.finalSubstitutions_mutualFactors computedSaturation
  have computedResidualSolvable :
      ∃ substitution,
        Solves substitution
          (residualEquations computed.substitution computed.pending) := by
    rw [← pendingEquality]
    obtain ⟨post, _, transported⟩ :=
      ResolutionTransport.residualEquations_transport_of_mutualFactors
        computedToClosure closureToComputed closure.residualPrincipal.1
    exact ⟨Subst.compose closure.residualSubstitution post, transported⟩
  obtain ⟨residual, residualResult⟩ :=
    solver.complete _ computedResidualSolvable
  simp [inferGeneratedUsing, saturationResult, residualResult]

end TypePM
