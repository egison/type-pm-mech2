import TypePM.Saturation

/-!
# Independence from the representative most general unifier

Two most general solutions of the same hard equations factor through one
another.  Potential for a special checking conversion cannot be introduced by
a later substitution, so mutual factorization makes the saturation decision
independent of which most general solution represents the hard solutions.
-/

namespace TypePM

namespace MostGeneral

/-- Any two most general solutions of one worklist factor through one
another. -/
theorem mutualFactors
    {equations : List Equation} {left right : Subst}
    (leftMostGeneral : MostGeneral equations left)
    (rightMostGeneral : MostGeneral equations right) :
    FactorsThrough left right ∧ FactorsThrough right left := by
  exact ⟨leftMostGeneral.2 right rightMostGeneral.1,
    rightMostGeneral.2 left leftMostGeneral.1⟩

end MostGeneral

/-- Special-conversion potential seen after a specific solution was already
present after the more general solution through which it factors. -/
theorem couldSpecial_of_factorsThrough
    {general specific : Subst}
    (factor : FactorsThrough general specific)
    (source expected : Ty)
    (possible :
      (source.apply specific).couldSpecial (expected.apply specific) = true) :
    (source.apply general).couldSpecial (expected.apply general) = true := by
  obtain ⟨later, rfl⟩ := factor
  apply Ty.couldSpecial_of_apply later
    (source.apply general) (expected.apply general)
  simpa only [Ty.apply_compose] using possible

/-- The Boolean special-conversion test is invariant between any two most
general solutions of the same hard equations. -/
theorem couldSpecial_iff_of_mostGeneral
    {equations : List Equation} {left right : Subst}
    (leftMostGeneral : MostGeneral equations left)
    (rightMostGeneral : MostGeneral equations right)
    (source expected : Ty) :
    (source.apply left).couldSpecial (expected.apply left) = true ↔
      (source.apply right).couldSpecial (expected.apply right) = true := by
  obtain ⟨leftToRight, rightToLeft⟩ :=
    leftMostGeneral.mutualFactors rightMostGeneral
  constructor
  · exact couldSpecial_of_factorsThrough rightToLeft source expected
  · exact couldSpecial_of_factorsThrough leftToRight source expected

/-- Equality form used by executable simultaneous promotion. -/
theorem couldSpecial_eq_of_mostGeneral
    {equations : List Equation} {left right : Subst}
    (leftMostGeneral : MostGeneral equations left)
    (rightMostGeneral : MostGeneral equations right)
    (source expected : Ty) :
    (source.apply left).couldSpecial (expected.apply left) =
      (source.apply right).couldSpecial (expected.apply right) := by
  have equivalent := couldSpecial_iff_of_mostGeneral
    leftMostGeneral rightMostGeneral source expected
  cases leftPossible :
      (source.apply left).couldSpecial (expected.apply left) <;>
    cases rightPossible :
      (source.apply right).couldSpecial (expected.apply right) <;>
    simp_all

/-- Being forced to the ordinary equality branch is likewise independent of
the chosen most general hard solution. -/
theorem forcedOrdinary_iff_of_mostGeneral
    {equations : List Equation} {left right : Subst}
    (leftMostGeneral : MostGeneral equations left)
    (rightMostGeneral : MostGeneral equations right)
    (source expected : Ty) :
    ForcedOrdinary (source.apply left) (expected.apply left) ↔
      ForcedOrdinary (source.apply right) (expected.apply right) := by
  change
    (source.apply left).couldSpecial (expected.apply left) = false ↔
      (source.apply right).couldSpecial (expected.apply right) = false
  rw [couldSpecial_eq_of_mostGeneral
    leftMostGeneral rightMostGeneral source expected]

namespace CheckObligation

/-- Pointwise form for obligations stored in a generated block. -/
theorem couldSpecialUnder_iff_of_mostGeneral
    {equations : List Equation} {left right : Subst}
    (leftMostGeneral : MostGeneral equations left)
    (rightMostGeneral : MostGeneral equations right)
    (obligation : CheckObligation) :
    (obligation.source.apply left).couldSpecial
        (obligation.expected.apply left) = true ↔
      (obligation.source.apply right).couldSpecial
        (obligation.expected.apply right) = true :=
  couldSpecial_iff_of_mostGeneral leftMostGeneral rightMostGeneral
    obligation.source obligation.expected

theorem forcedOrdinaryUnder_iff_of_mostGeneral
    {equations : List Equation} {left right : Subst}
    (leftMostGeneral : MostGeneral equations left)
    (rightMostGeneral : MostGeneral equations right)
    (obligation : CheckObligation) :
    obligation.forcedOrdinaryUnder left ↔
      obligation.forcedOrdinaryUnder right :=
  forcedOrdinary_iff_of_mostGeneral leftMostGeneral rightMostGeneral
    obligation.source obligation.expected

end CheckObligation

/-- A whole simultaneous promotion pass selects exactly the same original
obligations and emits exactly the same original equalities for either MGU. -/
theorem promoteUnder_eq_of_mostGeneral
    {equations : List Equation} {left right : Subst}
    (leftMostGeneral : MostGeneral equations left)
    (rightMostGeneral : MostGeneral equations right)
    (pending : List CheckObligation) :
    promoteUnder left pending = promoteUnder right pending := by
  induction pending with
  | nil => rfl
  | cons obligation pending induction =>
      have decision := couldSpecial_eq_of_mostGeneral
        leftMostGeneral rightMostGeneral
        obligation.source obligation.expected
      simp [promoteUnder, decision, induction]

end TypePM
