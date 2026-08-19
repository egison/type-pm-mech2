import TypePM.Declarative

/-!
# Coverage of every generated checking obligation

Hard saturation removes an obligation only by adding its ordinary type
equality to the hard equations.  This file proves that such equations persist
to the final hard worklist.  Consequently, every obligation generated from
source syntax has a checking conversion under the one final composed
substitution, whether it was promoted or remained pending.
-/

namespace TypePM

/-- One promotion pass either retains an obligation or emits exactly its
ordinary type equation. -/
theorem promoteUnder_covers
    (substitution : Subst) (pending : List CheckObligation) :
    ∀ obligation ∈ pending,
      obligation ∈ (promoteUnder substitution pending).pending ∨
        Equation.ty obligation.source obligation.expected ∈
          (promoteUnder substitution pending).equations := by
  induction pending with
  | nil => simp
  | cons head tail induction =>
      intro obligation membership
      simp only [List.mem_cons] at membership
      rcases membership with equality | membership
      · subst obligation
        by_cases possible :
            (head.source.apply substitution).couldSpecial
              (head.expected.apply substitution) = true
        · left
          simp [promoteUnder, possible]
        · right
          simp [promoteUnder, possible]
      · have covered := induction obligation membership
        by_cases possible :
            (head.source.apply substitution).couldSpecial
              (head.expected.apply substitution) = true
        · rcases covered with retained | promoted
          · left
            simp [promoteUnder, possible, retained]
          · right
            simpa [promoteUnder, possible] using promoted
        · rcases covered with retained | promoted
          · left
            simpa [promoteUnder, possible] using retained
          · right
            simp [promoteUnder, possible, promoted]

namespace PromotionClosure

/-- Saturation only appends equations, so every initial hard equation remains
in the final hard worklist. -/
theorem hard_mem_final
    {hard : List Equation} {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    (closure : PromotionClosure hard pending finalHard finalPending) :
    ∀ equation ∈ hard, equation ∈ finalHard := by
  induction closure with
  | refl =>
      intro equation membership
      exact membership
  | step principal promotionEquality progress rest induction =>
      intro equation membership
      exact induction equation (List.mem_append_left _ membership)

/-- Every initial pending obligation either survives to `finalPending` or has
its ordinary equality preserved in `finalHard`. -/
theorem pending_covered
    {hard : List Equation} {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    (closure : PromotionClosure hard pending finalHard finalPending) :
    ∀ obligation ∈ pending,
      obligation ∈ finalPending ∨
        Equation.ty obligation.source obligation.expected ∈ finalHard := by
  induction closure with
  | refl =>
      intro obligation membership
      exact Or.inl membership
  | @step _ _ substitution promoted _ _ principal promotionEquality
      progress rest induction =>
      intro obligation membership
      have covered := promoteUnder_covers substitution _ obligation membership
      rw [promotionEquality] at covered
      rcases covered with retained | promotedEquation
      · exact induction obligation retained
      · exact Or.inr (rest.hard_mem_final _
          (List.mem_append_right _ promotedEquation))

end PromotionClosure

namespace TypingDerivation

/-- Every obligation generated from the source has a checking conversion
under the final composed substitution.  Promoted obligations use `ordinary`;
the final pending obligations use their simultaneously solved resolutions. -/
theorem all_checkConversions
    {context : Context} {expression : Expr} {target : Ty}
    (derivation : TypingDerivation context expression target) :
    ∀ obligation ∈ derivation.generated.pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply
            (Subst.compose derivation.residualSubstitution
              derivation.hardSubstitution))
          (obligation.expected.apply
            (Subst.compose derivation.residualSubstitution
              derivation.hardSubstitution)) := by
  intro obligation membership
  rcases derivation.saturation.closure.pending_covered obligation membership with
    retained | promoted
  · exact derivation.remaining_checkConversion obligation retained
  · have equality := derivation.finalHard_solved
      (.ty obligation.source obligation.expected) promoted
    simp only [Equation.Holds] at equality
    rw [equality]
    exact ⟨.ordinary, .ordinary⟩

end TypingDerivation

namespace Typing

/-- Propositional projection of complete checking coverage from `Typing`. -/
theorem exists_all_checkConversions
    {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing context expression target) :
    ∃ derivation : TypingDerivation context expression target,
      ∀ obligation ∈ derivation.generated.pending,
        ∃ conversionClass,
          CheckConversion conversionClass
            (obligation.source.apply
              (Subst.compose derivation.residualSubstitution
                derivation.hardSubstitution))
            (obligation.expected.apply
              (Subst.compose derivation.residualSubstitution
                derivation.hardSubstitution)) := by
  rcases typing with ⟨derivation⟩
  exact ⟨derivation, derivation.all_checkConversions⟩

end Typing

end TypePM
