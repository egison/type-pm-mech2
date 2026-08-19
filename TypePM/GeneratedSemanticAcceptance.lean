import TypePM.BlockOrderInvariance
import TypePM.DeclarativeCoverage
import TypePM.SolverCertified

/-!
# Semantic solutions of generated blocks

This module records the direct, execution-independent meaning that every
accepted generated block satisfies.  A semantic solution simultaneously
solves the original hard equations and gives a genuine checking conversion
for every original delayed obligation.

The converse is deliberately not claimed.  Residual resolution chooses one
branch for every obligation before solving all residual equations.  A
substitution can expose a special conversion that this earlier classification
did not select; the accompanying regression module gives a minimal
counterexample.
-/

namespace TypePM
namespace Generated

/-- A substitution semantically satisfies a generated block when it solves
the original hard equations and validates every original checking
obligation. -/
def SemanticSolution (generated : Generated) (solution : Subst) : Prop :=
  Solves solution generated.hard ∧
    ∀ obligation ∈ generated.pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)

/-- Declarative block acceptance always yields one semantic solution of the
original generated constraints. -/
theorem exists_semanticSolution_of_blockAccepts
    {generated : Generated} (accepts : BlockAccepts generated) :
    ∃ solution, generated.SemanticSolution solution := by
  rcases accepts with
    ⟨finalHard, finalPending, hardSubstitution, residualSubstitution,
      saturation, residualSolved⟩
  let solution := Subst.compose residualSubstitution hardSubstitution
  have finalHardSolved : Solves solution finalHard :=
    solves_postcompose saturation.principal.1 residualSubstitution
  refine ⟨solution, ?_, ?_⟩
  · intro equation membership
    exact finalHardSolved equation
      (saturation.closure.hard_mem_final equation membership)
  · intro obligation membership
    rcases saturation.closure.pending_covered obligation membership with
      retained | promoted
    · obtain ⟨conversionClass, conversion⟩ :=
        residualEquations_sound residualSolved obligation retained
      exact ⟨conversionClass, by
        simpa only [solution, Ty.apply_compose] using conversion⟩
    · have equality := finalHardSolved
        (.ty obligation.source obligation.expected) promoted
      simp only [Equation.Holds] at equality
      rw [equality]
      exact ⟨.ordinary, .ordinary⟩

/-- With no delayed obligations, semantic solvability is also sufficient for
block acceptance.  The counterexample for the general converse therefore
needs at least one pending check. -/
theorem blockAccepts_iff_exists_semanticSolution_of_pending_eq_nil
    (generated : Generated) (noPending : generated.pending = []) :
    BlockAccepts generated ↔
      ∃ solution, generated.SemanticSolution solution := by
  constructor
  · intro accepts
    exact exists_semanticSolution_of_blockAccepts accepts
  · rintro ⟨solution, hardSolved, _checks⟩
    cases generated with
    | mk target hard pending =>
        simp only at noPending
        subst pending
        obtain ⟨principal, success⟩ := unify_complete ⟨solution, hardSolved⟩
        refine ⟨hard, [], principal, Subst.id, ?_, ?_⟩
        · exact
            { closure := .refl
              principal := unify_mostGeneral success
              stable := by simp [promoteUnder] }
        · simp [residualEquations]

end Generated
end TypePM
