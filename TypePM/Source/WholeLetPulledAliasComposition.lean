import TypePM.Source.AliasRenamingTransport
import TypePM.Source.WholeLetEntailedComposition

/-!
# Whole-let composition with pulled-back body aliases

The ordinary whole-let composer uses the transported body's left aliases on
both sides of the renaming step.  That is too strong when an alias existing
endpoint belongs only to the renamed support.  This variant pulls those
aliases back through the inverse renaming before attaching them to the
original left block.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition
open AliasRenamingTransport

/-- Generic composer whose original-left body aliases are the inverse image
of the transported body certificate's aliases.  The augmented fixedness
premise has a source-facing constructor in
`AliasRenamingTransport.pulledFixedOn_of_certificate`. -/
def supportedWholeLetEntailedCompositionWithPulledLeftAliases
    {outerStart bodyStart finish : Supply}
    {leftInterface rightInterface : List Equation}
    {rho : VariableRenaming} {body rightBody : Generated}
    (outerHidden : List UnificationVar)
    (outerHiddenFresh : VariablesFreshIn outerStart finish outerHidden)
    (outerStartLeBodyStart : outerStart.Le bodyStart)
    (leftInterfaceAliases rightInterfaceAliases :
      List FreshAliasSequence.Alias)
    (leftPresentation : HardEquivalent
      (EquationLists.addAliases leftInterfaceAliases leftInterface)
      (leftInterface ++ rightInterface))
    (rightPresentation : HardEquivalent
      (EquationLists.addAliases rightInterfaceAliases rightInterface)
      (leftInterface ++ rightInterface))
    (bodyCertificate : SupportedEntailedAlignmentCertificate bodyStart finish
      (ElaborationRenaming.renameGenerated rho body) rightBody)
    (pulledFixed : EntailedRenamingFixedOn
      (leftInterface ++ rightInterface) rho
      (FreshAliasSequence.addAll
        (renameAliases rho.symm bodyCertificate.leftAliases) body).unificationVars)
    (leftInterfaceAliasFresh : ∀ alias,
      alias ∈ leftInterfaceAliases →
        AliasFreshness.freshVariable alias ∈ outerHidden)
    (rightInterfaceAliasFresh : ∀ alias,
      alias ∈ rightInterfaceAliases →
        AliasFreshness.freshVariable alias ∈ outerHidden)
    (pulledLeftAliasFresh : ∀ alias,
      alias ∈ renameAliases rho.symm bodyCertificate.leftAliases →
        AliasFreshness.freshVariable alias ∈ bodyCertificate.hidden)
    (leftScoped : AliasFreshness.ScopedBy
      (Generated.fromLet leftInterface body).unificationVars
      (leftInterfaceAliases ++
        renameAliases rho.symm bodyCertificate.leftAliases))
    (rightScoped : AliasFreshness.ScopedBy
      (Generated.fromLet rightInterface rightBody).unificationVars
      (rightInterfaceAliases ++ bodyCertificate.rightAliases)) :
    SupportedEntailedAlignmentCertificate outerStart finish
      (Generated.fromLet leftInterface body)
      (Generated.fromLet rightInterface rightBody) := by
  let reference := leftInterface ++ rightInterface
  let pulledAliases := renameAliases rho.symm bodyCertificate.leftAliases
  have leftToCommon :=
    EntailedGeneratedAlignment.addAll_fromLet_to_commonReference
      leftInterfaceAliases pulledAliases leftInterface reference body
      leftPresentation
  have leftReposition : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll pulledAliases
        (Generated.fromLet reference body))
      (Generated.fromLet reference
        (FreshAliasSequence.addAll pulledAliases body)) :=
    EntailedGeneratedAlignment.addAll_frame_reposition
      pulledAliases (.letBody reference .hole) body
  have pulledRenaming : EntailedGeneratedAlignment
      (Generated.fromLet reference
        (FreshAliasSequence.addAll pulledAliases body))
      (Generated.fromLet reference
        (FreshAliasSequence.addAll bodyCertificate.leftAliases
          (ElaborationRenaming.renameGenerated rho body))) := by
    exact AliasRenamingTransport.pulledAddAll_entailingAlignment pulledFixed
  have bodyUnderCommon : EntailedGeneratedAlignment
      (Generated.fromLet reference
        (FreshAliasSequence.addAll bodyCertificate.leftAliases
          (ElaborationRenaming.renameGenerated rho body)))
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
      hiddenFresh := outerHiddenFresh.append
        (bodyCertificate.hiddenFresh.widen outerStartLeBodyStart
          (Supply.le_refl finish))
      leftAliases := leftInterfaceAliases ++ pulledAliases
      rightAliases := rightInterfaceAliases ++ bodyCertificate.rightAliases
      leftAliasFresh := by
        intro alias member
        rcases List.mem_append.mp member with interfaceMember | bodyMember
        · exact List.mem_append_left _
            (leftInterfaceAliasFresh alias interfaceMember)
        · exact List.mem_append_right _
            (pulledLeftAliasFresh alias bodyMember)
      rightAliasFresh := by
        intro alias member
        rcases List.mem_append.mp member with interfaceMember | bodyMember
        · exact List.mem_append_left _
            (rightInterfaceAliasFresh alias interfaceMember)
        · exact List.mem_append_right _
            (bodyCertificate.rightAliasFresh alias bodyMember)
      leftScoped := leftScoped
      rightScoped := rightScoped
      aligned := leftToCommon.trans (leftReposition.trans
        (pulledRenaming.trans (bodyUnderCommon.trans
          (rightReposition.trans rightToCommon.symm)))) }

/-- Source-facing form: fixedness only has to be proved on the original body
support.  `FixesAtOrAbove` and the body certificate's fresh interval extend
it automatically across the pulled alias equations. -/
def supportedWholeLetEntailedCompositionWithPulledLeftAliases_of_baseFixed
    {outerStart bodyStart finish : Supply}
    {leftInterface rightInterface : List Equation}
    {rho : VariableRenaming} {body rightBody : Generated}
    (outerHidden : List UnificationVar)
    (outerHiddenFresh : VariablesFreshIn outerStart finish outerHidden)
    (outerStartLeBodyStart : outerStart.Le bodyStart)
    (leftInterfaceAliases rightInterfaceAliases :
      List FreshAliasSequence.Alias)
    (leftPresentation : HardEquivalent
      (EquationLists.addAliases leftInterfaceAliases leftInterface)
      (leftInterface ++ rightInterface))
    (rightPresentation : HardEquivalent
      (EquationLists.addAliases rightInterfaceAliases rightInterface)
      (leftInterface ++ rightInterface))
    (bodyCertificate : SupportedEntailedAlignmentCertificate bodyStart finish
      (ElaborationRenaming.renameGenerated rho body) rightBody)
    (baseFixed : EntailedRenamingFixedOn
      (leftInterface ++ rightInterface) rho body.unificationVars)
    (futureFixed : rho.FixesAtOrAbove bodyStart)
    (leftInterfaceAliasFresh : ∀ alias,
      alias ∈ leftInterfaceAliases →
        AliasFreshness.freshVariable alias ∈ outerHidden)
    (rightInterfaceAliasFresh : ∀ alias,
      alias ∈ rightInterfaceAliases →
        AliasFreshness.freshVariable alias ∈ outerHidden)
    (leftScoped : AliasFreshness.ScopedBy
      (Generated.fromLet leftInterface body).unificationVars
      (leftInterfaceAliases ++
        renameAliases rho.symm bodyCertificate.leftAliases))
    (rightScoped : AliasFreshness.ScopedBy
      (Generated.fromLet rightInterface rightBody).unificationVars
      (rightInterfaceAliases ++ bodyCertificate.rightAliases)) :
    SupportedEntailedAlignmentCertificate outerStart finish
      (Generated.fromLet leftInterface body)
      (Generated.fromLet rightInterface rightBody) := by
  have pulledWithin :=
    pulledFreshWithin_of_certificate bodyCertificate futureFixed
  have pulledFixed := pulledFixedOn_of_certificate bodyCertificate
    baseFixed pulledWithin futureFixed
  exact supportedWholeLetEntailedCompositionWithPulledLeftAliases
    outerHidden outerHiddenFresh outerStartLeBodyStart
    leftInterfaceAliases rightInterfaceAliases
    leftPresentation rightPresentation bodyCertificate pulledFixed
    leftInterfaceAliasFresh rightInterfaceAliasFresh
    (pulledAliasFresh_hidden_of_certificate bodyCertificate futureFixed)
    leftScoped rightScoped

end TypePM.Source
