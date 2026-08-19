import TypePM.GeneratedSemanticAcceptance
import TypePM.HardWorklistEquivalence

/-!
# Branch-stable semantic acceptance

Pointwise checking conversions after an arbitrary substitution do not
characterize generated-block acceptance: a later substitution can expose a
special conversion after residual resolution has already selected its
branch.  The definition below records the declarative classification phase
and asks, pointwise, that one residual substitution solve the equations of
the branch selected at that phase.

It does not mention the executable generator, unifier, saturation procedure,
or `inferGeneratedUsing`.
-/

namespace TypePM
namespace Generated

/-- Data selected by a branch-stable solution.  Proofs that these choices are
valid are kept in `StableSemanticSolution`. -/
structure StableSemanticWitness (generated : Generated) where
  finalHard : List Equation
  finalPending : List CheckObligation
  hardSubstitution : Subst
  residualSubstitution : Subst

namespace StableSemanticWitness

/-- The simultaneous substitution obtained after hard classification and
residual branch solving. -/
def solution {generated : Generated}
    (witness : StableSemanticWitness generated) : Subst :=
  Subst.compose witness.residualSubstitution witness.hardSubstitution

end StableSemanticWitness

/-- A branch-stable semantic solution consists of a declarative promotion
closure, a most general hard solution at its final state, stability of every
remaining branch, and pointwise satisfaction of each selected branch's
residual equations. -/
structure StableSemanticSolution (generated : Generated)
    (witness : StableSemanticWitness generated) : Prop where
  closure : PromotionClosure generated.hard generated.pending
    witness.finalHard witness.finalPending
  hardPrincipal : MostGeneral witness.finalHard witness.hardSubstitution
  stable : (promoteUnder witness.hardSubstitution
    witness.finalPending).equations = []
  remainingBranches : ∀ obligation ∈ witness.finalPending,
    Solves witness.residualSubstitution
      (obligation.residualEquations witness.hardSubstitution)

/-- Solving the concatenated residual worklist is equivalent to solving the
selected branch equations of every obligation pointwise with one common
substitution. -/
theorem solves_residualEquations_iff_forall
    (hardSubstitution residualSubstitution : Subst)
    (pending : List CheckObligation) :
    Solves residualSubstitution
        (residualEquations hardSubstitution pending) ↔
      ∀ obligation ∈ pending,
        Solves residualSubstitution
          (obligation.residualEquations hardSubstitution) := by
  induction pending with
  | nil => simp [residualEquations]
  | cons obligation pending induction =>
      simp only [residualEquations, solves_append, List.mem_cons]
      constructor
      · rintro ⟨head, tail⟩ candidate (rfl | membership)
        · exact head
        · exact induction.mp tail candidate membership
      · intro all
        exact ⟨all obligation (by simp), induction.mpr (by
          intro candidate membership
          exact all candidate (by simp [membership]))⟩

namespace StableSemanticSolution

/-- The selected hard substitution and stable flag form an ordinary
declarative `Saturated` witness. -/
theorem saturated {generated : Generated}
    {witness : StableSemanticWitness generated}
    (solution : StableSemanticSolution generated witness) :
    Saturated generated.hard generated.pending witness.finalHard
      witness.finalPending witness.hardSubstitution :=
  { closure := solution.closure
    principal := solution.hardPrincipal
    stable := solution.stable }

/-- Every branch-stable solution gives the weaker pointwise semantic
solution under its composed substitution. -/
theorem semanticSolution {generated : Generated}
    {witness : StableSemanticWitness generated}
    (stableSolution : StableSemanticSolution generated witness) :
    generated.SemanticSolution witness.solution := by
  have finalHardSolved : Solves witness.solution witness.finalHard :=
    solves_postcompose stableSolution.hardPrincipal.1
      witness.residualSubstitution
  constructor
  · intro equation membership
    exact finalHardSolved equation
      (stableSolution.closure.hard_mem_final equation membership)
  · intro obligation membership
    rcases stableSolution.closure.pending_covered obligation membership with
      retained | promoted
    · let resolution := obligation.resolutionUnder witness.hardSubstitution
      refine ⟨resolution.conversionClass, ?_⟩
      have conversion := resolution.sound
        (stableSolution.remainingBranches obligation retained)
      simpa only [StableSemanticWitness.solution, Ty.apply_compose] using
        conversion
    · have equality := finalHardSolved
        (.ty obligation.source obligation.expected) promoted
      simp only [Equation.Holds] at equality
      rw [equality]
      exact ⟨.ordinary, .ordinary⟩

end StableSemanticSolution

/-- Branch-stable semantic solutions characterize declarative block
acceptance. -/
theorem blockAccepts_iff_exists_stableSemanticSolution
    (generated : Generated) :
    BlockAccepts generated ↔
      ∃ witness : StableSemanticWitness generated,
        StableSemanticSolution generated witness := by
  constructor
  · rintro ⟨finalHard, finalPending, hardSubstitution,
      residualSubstitution, saturation, residualSolved⟩
    let witness : StableSemanticWitness generated :=
      { finalHard := finalHard
        finalPending := finalPending
        hardSubstitution := hardSubstitution
        residualSubstitution := residualSubstitution }
    refine ⟨witness, ?_⟩
    exact
      { closure := saturation.closure
        hardPrincipal := saturation.principal
        stable := saturation.stable
        remainingBranches :=
          (solves_residualEquations_iff_forall hardSubstitution
            residualSubstitution finalPending).mp residualSolved }
  · rintro ⟨witness, stableSolution⟩
    exact ⟨witness.finalHard, witness.finalPending,
      witness.hardSubstitution, witness.residualSubstitution,
      stableSolution.saturated,
      (solves_residualEquations_iff_forall witness.hardSubstitution
        witness.residualSubstitution witness.finalPending).mpr
          stableSolution.remainingBranches⟩

/-- Replacing the initial hard worklist by a semantically equivalent one and
keeping the pending obligations fixed transports a concrete branch-stable
solution. -/
theorem StableSemanticSolution.transportHard
    {left right : Generated}
    {witness : StableSemanticWitness left}
    (solution : StableSemanticSolution left witness)
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingEqual : left.pending = right.pending) :
    ∃ transportedWitness : StableSemanticWitness right,
      StableSemanticSolution right transportedWitness := by
  obtain ⟨transportedFinal, transportedClosure, finalEquivalent⟩ :=
    solution.closure.transportHard hardEquivalent
  have transportedPrincipal :
      MostGeneral transportedFinal witness.hardSubstitution :=
    (HardEquivalent.mostGeneral_iff finalEquivalent
      witness.hardSubstitution).mp solution.hardPrincipal
  let transportedWitness : StableSemanticWitness right :=
    { finalHard := transportedFinal
      finalPending := witness.finalPending
      hardSubstitution := witness.hardSubstitution
      residualSubstitution := witness.residualSubstitution }
  refine ⟨transportedWitness, ?_⟩
  exact
    { closure := by
        rw [← pendingEqual]
        exact transportedClosure
      hardPrincipal := transportedPrincipal
      stable := solution.stable
      remainingBranches := solution.remainingBranches }

/-- Hard-equation equivalence and literal equality of the delayed
obligations preserve and reflect existence of branch-stable solutions. -/
theorem exists_stableSemanticSolution_iff_of_hardEquivalent
    {left right : Generated}
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingEqual : left.pending = right.pending) :
    (∃ witness : StableSemanticWitness left,
        StableSemanticSolution left witness) ↔
      ∃ witness : StableSemanticWitness right,
        StableSemanticSolution right witness := by
  constructor
  · rintro ⟨witness, solution⟩
    exact solution.transportHard hardEquivalent pendingEqual
  · rintro ⟨witness, solution⟩
    exact solution.transportHard hardEquivalent.symm pendingEqual.symm

end Generated
end TypePM
