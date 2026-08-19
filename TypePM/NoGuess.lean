import TypePM.Saturation

/-!
# No-guess invariant for hard saturation

An obligation is promoted to an ordinary equality only after its normalized
outer shapes prove that no later substitution can expose a special matcher
conversion.  The theorems below retain the source obligation for every
promoted equation and make this permanence property explicit.
-/

namespace TypePM

/-- Every equality emitted by one promotion pass comes from an obligation in
that pass and was already forced to remain ordinary. -/
theorem promoteUnder_equation_origin
    (substitution : Subst) (obligations : List CheckObligation) :
    ∀ equation ∈ (promoteUnder substitution obligations).equations,
      ∃ obligation,
        obligation ∈ obligations ∧
        equation = .ty obligation.source obligation.expected ∧
        obligation.forcedOrdinaryUnder substitution := by
  induction obligations with
  | nil => simp [promoteUnder]
  | cons obligation obligations induction =>
      by_cases possible :
          (obligation.source.apply substitution).couldSpecial
            (obligation.expected.apply substitution) = true
      · simp only [promoteUnder, possible, if_pos]
        intro equation membership
        obtain ⟨origin, originMembership, equality, forced⟩ :=
          induction equation membership
        exact ⟨origin, by simp [originMembership], equality, forced⟩
      · have forced : obligation.forcedOrdinaryUnder substitution := by
          unfold CheckObligation.forcedOrdinaryUnder ForcedOrdinary
          cases candidate :
              (obligation.source.apply substitution).couldSpecial
                (obligation.expected.apply substitution) <;> simp_all
        simp only [promoteUnder, possible]
        intro equation membership
        rcases List.mem_cons.mp membership with equality | tailMembership
        · subst equation
          exact ⟨obligation, by simp, rfl, forced⟩
        · obtain ⟨origin, originMembership, equality, originForced⟩ :=
            induction equation tailMembership
          exact ⟨origin, by simp [originMembership], equality, originForced⟩

/-- A promoted equality cannot become a special matcher conversion after any
later substitution.  Thus only ordinary equalities, never a guessed matcher
or slot shape, feed the next hard-saturation round. -/
theorem promoteUnder_equation_no_special_after
    (substitution later : Subst) (obligations : List CheckObligation)
    {equation : Equation}
    (membership :
      equation ∈ (promoteUnder substitution obligations).equations) :
    ∃ obligation,
      obligation ∈ obligations ∧
      equation = .ty obligation.source obligation.expected ∧
      ∀ resolution : Resolution
          ((obligation.source.apply substitution).apply later)
          ((obligation.expected.apply substitution).apply later),
        ¬ resolution.Special := by
  obtain ⟨obligation, originMembership, equality, forced⟩ :=
    promoteUnder_equation_origin substitution obligations equation membership
  exact ⟨obligation, originMembership, equality,
    fun resolution => forced.no_special_after later⟩

end TypePM
