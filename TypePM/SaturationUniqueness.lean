import TypePM.MGUEquivalence

/-!
# Uniqueness of declarative hard saturation

Every promotion round uses an arbitrary most general solution of the current
hard worklist.  `promoteUnder_eq_of_mostGeneral` shows that this choice cannot
change the simultaneous promotion result.  Consequently, two saturated
derivations from the same initial block reach the same final hard equations
and pending obligations.
-/

namespace TypePM

namespace PromotionClosure

/-- Two promotion closures whose endpoints are stable under most general
solutions have the same endpoint state. -/
theorem stableFinalState_unique
    {hard : List Equation} {pending : List CheckObligation}
    {leftHard rightHard : List Equation}
    {leftPending rightPending : List CheckObligation}
    {leftSubstitution rightSubstitution : Subst}
    (leftClosure :
      PromotionClosure hard pending leftHard leftPending)
    (leftPrincipal : MostGeneral leftHard leftSubstitution)
    (leftStable :
      (promoteUnder leftSubstitution leftPending).equations = [])
    (rightClosure :
      PromotionClosure hard pending rightHard rightPending)
    (rightPrincipal : MostGeneral rightHard rightSubstitution)
    (rightStable :
      (promoteUnder rightSubstitution rightPending).equations = []) :
    leftHard = rightHard ∧ leftPending = rightPending := by
  induction leftClosure generalizing
      rightHard rightPending leftSubstitution rightSubstitution with
  | @refl currentHard currentPending =>
      cases rightClosure with
      | refl => exact ⟨rfl, rfl⟩
      | @step _ _ stepSubstitution promoted finalHard finalPending
          stepPrincipal stepPromotion stepProgress stepClosure =>
          have samePromotion := promoteUnder_eq_of_mostGeneral
            leftPrincipal stepPrincipal currentPending
          have promotedIsStable : promoted.equations = [] := by
            rw [← stepPromotion, ← samePromotion]
            exact leftStable
          exact (stepProgress promotedIsStable).elim
  | @step currentHard currentPending stepSubstitution promoted
      finalHard finalPending
      stepPrincipal stepPromotion stepProgress stepClosure induction =>
      cases rightClosure with
      | refl =>
          have samePromotion := promoteUnder_eq_of_mostGeneral
            stepPrincipal rightPrincipal currentPending
          have promotedIsStable : promoted.equations = [] := by
            rw [← stepPromotion, samePromotion]
            exact rightStable
          exact (stepProgress promotedIsStable).elim
      | @step _ _ rightStepSubstitution rightPromoted
          rightFinalHard rightFinalPending rightStepPrincipal
          rightStepPromotion rightStepProgress rightStepClosure =>
          have samePromotion := promoteUnder_eq_of_mostGeneral
            stepPrincipal rightStepPrincipal currentPending
          have alignedRightClosure :
              PromotionClosure
                (currentHard ++ promoted.equations) promoted.pending
                rightHard rightPending := by
            rw [← stepPromotion, samePromotion, rightStepPromotion]
            exact rightStepClosure
          exact induction leftPrincipal leftStable alignedRightClosure
            rightPrincipal rightStable

end PromotionClosure

namespace Saturated

/-- Saturated state is unique even though each round may choose a different
representative most general substitution. -/
theorem finalState_unique
    {hard : List Equation} {pending : List CheckObligation}
    {leftHard rightHard : List Equation}
    {leftPending rightPending : List CheckObligation}
    {leftSubstitution rightSubstitution : Subst}
    (left : Saturated hard pending leftHard leftPending leftSubstitution)
    (right : Saturated hard pending rightHard rightPending rightSubstitution) :
    leftHard = rightHard ∧ leftPending = rightPending :=
  left.closure.stableFinalState_unique
    left.principal left.stable
    right.closure right.principal right.stable

/-- Final hard substitutions of two saturated derivations mutually factor
through one another. -/
theorem finalSubstitutions_mutualFactors
    {hard : List Equation} {pending : List CheckObligation}
    {leftHard rightHard : List Equation}
    {leftPending rightPending : List CheckObligation}
    {leftSubstitution rightSubstitution : Subst}
    (left : Saturated hard pending leftHard leftPending leftSubstitution)
    (right : Saturated hard pending rightHard rightPending rightSubstitution) :
    FactorsThrough leftSubstitution rightSubstitution ∧
      FactorsThrough rightSubstitution leftSubstitution := by
  obtain ⟨hardEquality, _⟩ := left.finalState_unique right
  subst rightHard
  exact left.principal.mutualFactors right.principal

end Saturated

end TypePM
