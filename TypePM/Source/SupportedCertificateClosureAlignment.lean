import TypePM.Source.ProvenancedAliasedEntailedFreshClosureAlignment
import TypePM.Source.FullM2Coherence

/-!
# Closing the generic M2 closure-alignment premise

The support-strengthened semantic certificate contains exactly the alias
scope and fresh-interval facts needed to lift arbitrary absorbing principal
closures and construct a future-fixing alignment.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition.AliasFreshness

/-- Concrete implementation of the generic closure theorem consumed by the
full M2 source induction. -/
theorem supportedCertificateClosureAlignmentComplete :
    SupportedCertificateClosureAlignmentComplete := by
  intro signature context expression start next left right
    wellFormed leftElaboration rightElaboration certificate
    leftClosure rightClosure leftAbsorbing rightAbsorbing
  have leftAdmissible : FreshAliasSequence.Admissible
      certificate.leftAliases left :=
    admissible_of_scopedBy certificate.leftScoped
      (fun _ member => member)
  have rightAdmissible : FreshAliasSequence.Admissible
      certificate.rightAliases right :=
    admissible_of_scopedBy certificate.rightScoped
      (fun _ member => member)
  have leftFresh : ∀ alias, alias ∈ certificate.leftAliases →
      (freshVariable alias).FreshIn start next := by
    intro alias member
    exact certificate.hiddenFresh _
      (certificate.leftAliasFresh alias member)
  have rightFresh : ∀ alias, alias ∈ certificate.rightAliases →
      (freshVariable alias).FreshIn start next := by
    intro alias member
    exact certificate.hiddenFresh _
      (certificate.rightAliasFresh alias member)
  have leftContextFixed : CumulativeAliasContextFixed
      certificate.leftAliases leftClosure context :=
    cumulativeAliasContextFixed_of_scopedBy_sourceFresh
      certificate.leftAliases leftClosure leftAbsorbing context
      start next wellFormed certificate.leftScoped leftFresh
  have rightContextFixed : CumulativeAliasContextFixed
      certificate.rightAliases rightClosure context :=
    cumulativeAliasContextFixed_of_scopedBy_sourceFresh
      certificate.rightAliases rightClosure rightAbsorbing context
      start next wellFormed certificate.rightScoped rightFresh
  have rightAugmentedBelow : ∀ candidate,
      candidate ∈ (FreshAliasSequence.addAll
        certificate.rightAliases right).unificationVars →
        candidate.Below next.ty next.cap := by
    apply FreshAliasSequence.addAll_support_below_of_scopedBy
      certificate.rightAliases right next certificate.rightScoped
      (fun _ member => member)
      (rightElaboration.support_below wellFormed)
    intro alias member
    exact (rightFresh alias member).below
  have contextBelow : context.initialSupply.Le next :=
    Supply.le_trans wellFormed rightElaboration.supply_le_next
  exact ⟨provenancedAliasedEntailedFreshClosureAlignment
    certificate.leftAliases certificate.rightAliases
    leftAdmissible rightAdmissible
    certificate.leftTargetFixed certificate.rightTargetFixed
    certificate.aligned leftClosure rightClosure
    leftAbsorbing rightAbsorbing context next
    leftContextFixed rightContextFixed contextBelow
    rightAugmentedBelow⟩

end TypePM.Source
