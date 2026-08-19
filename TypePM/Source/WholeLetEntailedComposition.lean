import TypePM.Source.BodyRenamingSemantics

/-!
# Common-reference helper for whole-let composition

This module isolates the algebraic step which moves an alias-augmented
concrete `let` interface to a common hard-equation reference.  The
pullback-aware whole-`let` composition reuses this helper after transporting
the body aliases to the original coordinate system.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition

namespace EntailedGeneratedAlignment

/-- An alias-augmented concrete `let` presentation is semantically equal to
the same body aliases under a common interface reference.  Hard-equation
order is immaterial because `HardEquivalent` is equality of solution sets. -/
theorem addAll_fromLet_to_commonReference
    (interfaceAliases bodyAliases : List FreshAliasSequence.Alias)
    (interface reference : List Equation) (body : Generated)
    (presentation : HardEquivalent
      (EquationLists.addAliases interfaceAliases interface) reference) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll (interfaceAliases ++ bodyAliases)
        (Generated.fromLet interface body))
      (FreshAliasSequence.addAll bodyAliases
        (Generated.fromLet reference body)) := by
  apply of_hardEquivalent_sameTargetPending
  · have strengthened : HardEquivalent
        (EquationLists.addAliases bodyAliases
          (EquationLists.addAliases interfaceAliases interface))
        (EquationLists.addAliases bodyAliases reference) := by
      intro substitution
      have presented := presentation substitution
      simp only [EquationLists.addAliases_eq_reverse_map_append,
        solves_append] at presented ⊢
      constructor
      · rintro ⟨bodyAliasSolved, interfaceAliasSolved, interfaceSolved⟩
        exact ⟨bodyAliasSolved,
          presented.mp ⟨interfaceAliasSolved, interfaceSolved⟩⟩
      · rintro ⟨bodyAliasSolved, referenceSolved⟩
        have concrete := presented.mpr referenceSolved
        exact ⟨bodyAliasSolved, concrete.1, concrete.2⟩
    simpa [EntailedAlignmentCertificate.addAll_append,
      EquationLists.addAll_hard, Generated.fromLet,
      EquationLists.addAliases_append] using
      strengthened.append (HardEquivalent.refl body.hard)
  · simp [Generated.fromLet]
  · simp [Generated.fromLet]

end EntailedGeneratedAlignment

end TypePM.Source
