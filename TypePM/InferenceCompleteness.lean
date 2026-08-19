import TypePM.Inference
import TypePM.ResolutionTransport

/-!
# Completeness of M1 inference

A declarative typing may use different most-general substitutions from the
executable saturation procedure.  Saturated-state uniqueness aligns the
remaining obligation list, mutual factorization transports its residual
solution, and completeness of the abstract MGU solver finishes the run.
-/

namespace TypePM

/-- Every declarative typing is accepted by inference instantiated with a
complete most-general-unifier solver.  The executable result need not use the
same representative substitutions as the declarative witness. -/
theorem inferUsing_complete
    (solveHard : List Equation → Option Subst)
    (solver : CompleteMGUSolver solveHard)
    {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing context expression target) :
    ∃ result, inferUsing solveHard context expression = some result := by
  rcases typing with ⟨derivation⟩
  have generatedResult :
      generate context expression context.nextVar =
        some (derivation.generated, derivation.next) :=
    generates_to_generate derivation.generation
  obtain ⟨computed, saturationResult⟩ :=
    solver.saturateUsing_complete derivation.saturation
  have computedSaturation :
      Saturated derivation.generated.hard derivation.generated.pending
        computed.hard computed.pending computed.substitution :=
    saturateUsing_sound solveHard solver.principal saturationResult
  obtain ⟨_, pendingEquality⟩ :=
    derivation.saturation.finalState_unique computedSaturation
  obtain ⟨declarativeToComputed, computedToDeclarative⟩ :=
    derivation.saturation.finalSubstitutions_mutualFactors
      computedSaturation
  have computedResidualSolvable :
      ∃ substitution,
        Solves substitution
          (residualEquations computed.substitution computed.pending) := by
    rw [← pendingEquality]
    obtain ⟨post, _, transported⟩ :=
      ResolutionTransport.residualEquations_transport_of_mutualFactors
        computedToDeclarative declarativeToComputed
        derivation.residualSolved
    exact ⟨Subst.compose derivation.residualSubstitution post, transported⟩
  obtain ⟨residual, residualResult⟩ :=
    solver.complete _ computedResidualSolvable
  refine ⟨
    { substitution := Subst.compose residual computed.substitution
      target := derivation.generated.target.apply
        (Subst.compose residual computed.substitution) }, ?_⟩
  simp [inferUsing, generatedResult, inferGeneratedUsing,
    saturationResult, residualResult]

namespace Typing

/-- Public M1 inference accepts every independently typable expression. -/
theorem infer_isSome
    {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing context expression target) :
    infer context expression ≠ none := by
  obtain ⟨result, success⟩ :=
    inferUsing_complete unify unify_completeMGUSolver typing
  simp [infer, success]

end Typing

end TypePM
