import TypePM.Source.BodyRenamingSemantics

/-!
# Generic semantic composition at a whole-let boundary

This module isolates the algebraic part of whole-`let` alignment from the
source elaboration proof which constructs the required aliases and scope
facts.  Each concrete interface presentation is first moved to one common
hard reference.  A semantic body-renaming alignment and an independently
supported body certificate can then be composed under that reference.
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

/-- Compose the semantic ingredients of a heterogeneous whole-`let` proof.

The interface aliases present both concrete interfaces as the common list
`leftInterface ++ rightInterface`.  The body renaming alignment is stated
under exactly that reference.  Freshness and scope of the two final alias
lists remain explicit: they are the source-specific facts supplied by the
outer elaboration proof. -/
def supportedWholeLetEntailedComposition
    {start finish : Supply}
    {leftInterface rightInterface : List Equation}
    {rho : VariableRenaming} {body rightBody : Generated}
    (outerHidden : List UnificationVar)
    (outerHiddenFresh : VariablesFreshIn start finish outerHidden)
    (leftInterfaceAliases rightInterfaceAliases :
      List FreshAliasSequence.Alias)
    (leftPresentation : HardEquivalent
      (EquationLists.addAliases leftInterfaceAliases leftInterface)
      (leftInterface ++ rightInterface))
    (rightPresentation : HardEquivalent
      (EquationLists.addAliases rightInterfaceAliases rightInterface)
      (leftInterface ++ rightInterface))
    (bodyRenaming : EntailedGeneratedAlignment
      (generatedUnderReference (leftInterface ++ rightInterface) body)
      (generatedUnderReference (leftInterface ++ rightInterface)
        (ElaborationRenaming.renameGenerated rho body)))
    (bodyCertificate : SupportedEntailedAlignmentCertificate start finish
      (ElaborationRenaming.renameGenerated rho body) rightBody)
    (leftInterfaceAliasFresh : ∀ alias,
      alias ∈ leftInterfaceAliases →
        AliasFreshness.freshVariable alias ∈ outerHidden)
    (rightInterfaceAliasFresh : ∀ alias,
      alias ∈ rightInterfaceAliases →
        AliasFreshness.freshVariable alias ∈ outerHidden)
    (leftScoped : AliasFreshness.ScopedBy
      (Generated.fromLet leftInterface body).unificationVars
      (leftInterfaceAliases ++ bodyCertificate.leftAliases))
    (rightScoped : AliasFreshness.ScopedBy
      (Generated.fromLet rightInterface rightBody).unificationVars
      (rightInterfaceAliases ++ bodyCertificate.rightAliases)) :
    SupportedEntailedAlignmentCertificate start finish
      (Generated.fromLet leftInterface body)
      (Generated.fromLet rightInterface rightBody) := by
  let reference := leftInterface ++ rightInterface
  let renamedBody := ElaborationRenaming.renameGenerated rho body
  have leftToCommon :=
    EntailedGeneratedAlignment.addAll_fromLet_to_commonReference
      leftInterfaceAliases bodyCertificate.leftAliases
      leftInterface reference body leftPresentation
  have renamedUnderCommon : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll bodyCertificate.leftAliases
        (Generated.fromLet reference body))
      (FreshAliasSequence.addAll bodyCertificate.leftAliases
        (Generated.fromLet reference renamedBody)) :=
    bodyRenaming.addAllBoth bodyCertificate.leftAliases
  have leftReposition : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll bodyCertificate.leftAliases
        (Generated.fromLet reference renamedBody))
      (Generated.fromLet reference
        (FreshAliasSequence.addAll bodyCertificate.leftAliases renamedBody)) :=
    EntailedGeneratedAlignment.addAll_frame_reposition
      bodyCertificate.leftAliases (.letBody reference .hole) renamedBody
  have bodyUnderCommon : EntailedGeneratedAlignment
      (Generated.fromLet reference
        (FreshAliasSequence.addAll bodyCertificate.leftAliases renamedBody))
      (Generated.fromLet reference
        (FreshAliasSequence.addAll bodyCertificate.rightAliases rightBody)) :=
    bodyCertificate.aligned.letBody reference
  have rightReposition : EntailedGeneratedAlignment
      (Generated.fromLet reference
        (FreshAliasSequence.addAll bodyCertificate.rightAliases rightBody))
      (FreshAliasSequence.addAll bodyCertificate.rightAliases
        (Generated.fromLet reference rightBody)) :=
    (EntailedGeneratedAlignment.addAll_frame_reposition
      bodyCertificate.rightAliases (.letBody reference .hole) rightBody).symm
  have rightToCommon :=
    EntailedGeneratedAlignment.addAll_fromLet_to_commonReference
      rightInterfaceAliases bodyCertificate.rightAliases
      rightInterface reference rightBody rightPresentation
  exact
    { hidden := outerHidden ++ bodyCertificate.hidden
      hiddenFresh := outerHiddenFresh.append bodyCertificate.hiddenFresh
      leftAliases := leftInterfaceAliases ++ bodyCertificate.leftAliases
      rightAliases := rightInterfaceAliases ++ bodyCertificate.rightAliases
      leftAliasFresh := by
        intro alias member
        rcases List.mem_append.mp member with interfaceMember | bodyMember
        · exact List.mem_append_left _
            (leftInterfaceAliasFresh alias interfaceMember)
        · exact List.mem_append_right _
            (bodyCertificate.leftAliasFresh alias bodyMember)
      rightAliasFresh := by
        intro alias member
        rcases List.mem_append.mp member with interfaceMember | bodyMember
        · exact List.mem_append_left _
            (rightInterfaceAliasFresh alias interfaceMember)
        · exact List.mem_append_right _
            (bodyCertificate.rightAliasFresh alias bodyMember)
      leftScoped := leftScoped
      rightScoped := rightScoped
      aligned := leftToCommon.trans
        (renamedUnderCommon.trans (leftReposition.trans
          (bodyUnderCommon.trans (rightReposition.trans rightToCommon.symm)))) }

end TypePM.Source
