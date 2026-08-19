import TypePM.SaturationUniqueness

/-!
# Permutation invariance

Constraint solving is insensitive to worklist order.  A simultaneous
promotion pass likewise preserves a permutation of its input obligations,
separately for the emitted equations and the obligations that remain pending.
These facts let a declarative saturation derivation be transported across a
permutation of its initial hard equations.
-/

namespace TypePM

/-- Solving a list of equations depends only on its multiset of members. -/
theorem solves_iff_of_perm
    {left right : List Equation} (permutation : left.Perm right)
    (substitution : Subst) :
    Solves substitution left ↔ Solves substitution right := by
  constructor
  · intro solved equation membership
    exact solved equation (permutation.mem_iff.mpr membership)
  · intro solved equation membership
    exact solved equation (permutation.mem_iff.mp membership)

/-- Most-generality is insensitive to the order of the equations. -/
theorem mostGeneral_iff_of_perm
    {left right : List Equation} (permutation : left.Perm right)
    (substitution : Subst) :
    MostGeneral left substitution ↔ MostGeneral right substitution := by
  constructor
  · intro principal
    refine ⟨(solves_iff_of_perm permutation substitution).mp principal.1, ?_⟩
    intro specific solved
    exact principal.2 specific
      ((solves_iff_of_perm permutation specific).mpr solved)
  · intro principal
    refine ⟨(solves_iff_of_perm permutation substitution).mpr principal.1, ?_⟩
    intro specific solved
    exact principal.2 specific
      ((solves_iff_of_perm permutation specific).mp solved)

private theorem residualEquations_eq_flatMap
    (substitution : Subst) (obligations : List CheckObligation) :
    residualEquations substitution obligations =
      obligations.flatMap
        (CheckObligation.residualEquations substitution) := by
  induction obligations with
  | nil => simp [residualEquations]
  | cons obligation obligations induction =>
      simp [residualEquations, induction]

/-- Residual equation generation preserves permutations of obligations. -/
theorem residualEquations_perm
    (substitution : Subst) {left right : List CheckObligation}
    (permutation : left.Perm right) :
    (residualEquations substitution left).Perm
      (residualEquations substitution right) := by
  rw [residualEquations_eq_flatMap, residualEquations_eq_flatMap]
  exact permutation.flatMap_right _

private def promotedEquationUnder
    (substitution : Subst) (obligation : CheckObligation) :
    Option Equation :=
  if (obligation.source.apply substitution).couldSpecial
      (obligation.expected.apply substitution) then
    none
  else
    some (.ty obligation.source obligation.expected)

private def pendingObligationUnder
    (substitution : Subst) (obligation : CheckObligation) :
    Option CheckObligation :=
  if (obligation.source.apply substitution).couldSpecial
      (obligation.expected.apply substitution) then
    some obligation
  else
    none

private theorem promoteUnder_equations_eq_filterMap
    (substitution : Subst) (obligations : List CheckObligation) :
    (promoteUnder substitution obligations).equations =
      obligations.filterMap (promotedEquationUnder substitution) := by
  induction obligations with
  | nil => simp [promoteUnder]
  | cons obligation obligations induction =>
      by_cases possible :
          (obligation.source.apply substitution).couldSpecial
            (obligation.expected.apply substitution) = true
      · simp [promoteUnder, promotedEquationUnder, possible, induction]
      · simp [promoteUnder, promotedEquationUnder, possible, induction]

private theorem promoteUnder_pending_eq_filterMap
    (substitution : Subst) (obligations : List CheckObligation) :
    (promoteUnder substitution obligations).pending =
      obligations.filterMap (pendingObligationUnder substitution) := by
  induction obligations with
  | nil => simp [promoteUnder]
  | cons obligation obligations induction =>
      by_cases possible :
          (obligation.source.apply substitution).couldSpecial
            (obligation.expected.apply substitution) = true
      · simp [promoteUnder, pendingObligationUnder, possible, induction]
      · simp [promoteUnder, pendingObligationUnder, possible, induction]

/-- A simultaneous promotion pass preserves an input permutation in both
output components. -/
theorem promoteUnder_perm
    (substitution : Subst) {left right : List CheckObligation}
    (permutation : left.Perm right) :
    (promoteUnder substitution left).equations.Perm
        (promoteUnder substitution right).equations ∧
      (promoteUnder substitution left).pending.Perm
        (promoteUnder substitution right).pending := by
  constructor
  · rw [promoteUnder_equations_eq_filterMap,
      promoteUnder_equations_eq_filterMap]
    exact permutation.filterMap _
  · rw [promoteUnder_pending_eq_filterMap,
      promoteUnder_pending_eq_filterMap]
    exact permutation.filterMap _

namespace PromotionClosure

/-- Reordering the initial hard equations transports a promotion closure.
The final hard equations change only by the corresponding permutation, while
the final pending list can be kept literally identical. -/
theorem permuteInitialHard
    {leftHard rightHard : List Equation}
    {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    (permutation : leftHard.Perm rightHard)
    (closure : PromotionClosure leftHard pending finalHard finalPending) :
    ∃ transportedFinalHard,
      finalHard.Perm transportedFinalHard ∧
        PromotionClosure rightHard pending transportedFinalHard finalPending := by
  induction closure generalizing rightHard with
  | @refl currentHard currentPending =>
      exact ⟨rightHard, permutation, .refl⟩
  | @step currentHard currentPending substitution promoted
      currentFinalHard currentFinalPending principal promotion progress
      remaining induction =>
      have transportedPrincipal : MostGeneral rightHard substitution :=
        (mostGeneral_iff_of_perm permutation substitution).mp principal
      have appendedPermutation :
          (currentHard ++ promoted.equations).Perm
            (rightHard ++ promoted.equations) :=
        permutation.append_right promoted.equations
      obtain ⟨transportedFinalHard, finalPermutation,
          transportedRemaining⟩ := induction appendedPermutation
      exact ⟨transportedFinalHard, finalPermutation,
        .step transportedPrincipal promotion progress transportedRemaining⟩

end PromotionClosure

namespace Saturated

/-- A saturated derivation transports across a permutation of its initial
hard equations, preserving its pending endpoint and hard substitution. -/
theorem permuteInitialHard
    {leftHard rightHard : List Equation}
    {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    {substitution : Subst}
    (permutation : leftHard.Perm rightHard)
    (saturated : Saturated leftHard pending finalHard finalPending substitution) :
    ∃ transportedFinalHard,
      finalHard.Perm transportedFinalHard ∧
        Saturated rightHard pending transportedFinalHard finalPending
          substitution := by
  obtain ⟨transportedFinalHard, finalPermutation,
      transportedClosure⟩ :=
    saturated.closure.permuteInitialHard permutation
  exact ⟨transportedFinalHard, finalPermutation,
    { closure := transportedClosure
      principal :=
        (mostGeneral_iff_of_perm finalPermutation substitution).mp
          saturated.principal
      stable := saturated.stable }⟩

end Saturated

end TypePM
