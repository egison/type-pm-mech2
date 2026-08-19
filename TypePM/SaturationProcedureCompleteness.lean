import TypePM.MGUEquivalence
import TypePM.SaturationProcedure

/-!
# Completeness of executable saturation

Whenever the abstract hard solver returns an MGU for each solvable worklist,
the length-bounded simultaneous-promotion procedure succeeds for every
declaratively saturated block.
-/

namespace TypePM

theorem saturateLoop_complete_of_closure
    (solveHard : List Equation → Option Subst)
    (solverPrincipal : ∀ equations substitution,
      solveHard equations = some substitution →
        MostGeneral equations substitution)
    (solverComplete : ∀ equations,
      (∃ substitution, MostGeneral equations substitution) →
        ∃ substitution, solveHard equations = some substitution)
    {hard : List Equation} {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    {finalSubstitution : Subst}
    (closure : PromotionClosure hard pending finalHard finalPending)
    (finalPrincipal : MostGeneral finalHard finalSubstitution)
    (finalStable :
      (promoteUnder finalSubstitution finalPending).equations = [])
    {fuel : Nat} (fuelBound : pending.length < fuel) :
    ∃ output,
      saturateLoop solveHard fuel hard pending = some output := by
  induction closure generalizing fuel with
  | @refl currentHard currentPending =>
      obtain ⟨substitution, solved⟩ :=
        solverComplete currentHard ⟨finalSubstitution, finalPrincipal⟩
      have substitutionPrincipal := solverPrincipal _ _ solved
      have samePromotion := promoteUnder_eq_of_mostGeneral
        substitutionPrincipal finalPrincipal currentPending
      have noPromotion :
          (promoteUnder substitution currentPending).equations = [] := by
        rw [samePromotion]
        exact finalStable
      cases fuel with
      | zero => omega
      | succ fuel =>
          refine ⟨⟨currentHard, currentPending, substitution⟩, ?_⟩
          simp [saturateLoop, solved, noPromotion]
  | @step currentHard currentPending stepSubstitution promoted
      nextHard nextPending stepPrincipal stepPromotion stepProgress
      tailClosure induction =>
      obtain ⟨substitution, solved⟩ :=
        solverComplete currentHard ⟨stepSubstitution, stepPrincipal⟩
      have substitutionPrincipal := solverPrincipal _ _ solved
      have samePromotion := promoteUnder_eq_of_mostGeneral
        substitutionPrincipal stepPrincipal currentPending
      have computedPromotion :
          promoteUnder substitution currentPending = promoted :=
        samePromotion.trans stepPromotion
      have stepProgressAtSource :
          (promoteUnder stepSubstitution currentPending).equations ≠ [] := by
        rw [stepPromotion]
        exact stepProgress
      have shorter := promoteUnder_pending_length_lt
        stepSubstitution currentPending stepProgressAtSource
      rw [stepPromotion] at shorter
      cases fuel with
      | zero => omega
      | succ fuel =>
          have tailFuelBound : promoted.pending.length < fuel := by omega
          obtain ⟨output, recursive⟩ :=
            induction finalPrincipal finalStable tailFuelBound
          refine ⟨output, ?_⟩
          cases equationsCase : promoted.equations with
          | nil => exact (stepProgress equationsCase).elim
          | cons equation equations =>
              have recursive' :
                  saturateLoop solveHard fuel
                    (currentHard ++ equation :: equations) promoted.pending =
                      some output := by
                simpa [equationsCase] using recursive
              simpa [saturateLoop, solved, computedPromotion,
                equationsCase] using recursive'

theorem saturateUsing_complete
    (solveHard : List Equation → Option Subst)
    (solverPrincipal : ∀ equations substitution,
      solveHard equations = some substitution →
        MostGeneral equations substitution)
    (solverComplete : ∀ equations,
      (∃ substitution, MostGeneral equations substitution) →
        ∃ substitution, solveHard equations = some substitution)
    {hard : List Equation} {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    {finalSubstitution : Subst}
    (saturation :
      Saturated hard pending finalHard finalPending finalSubstitution) :
    ∃ output,
      saturateUsing solveHard hard pending = some output := by
  exact saturateLoop_complete_of_closure solveHard
    solverPrincipal solverComplete saturation.closure
    saturation.principal saturation.stable (by omega)

end TypePM
