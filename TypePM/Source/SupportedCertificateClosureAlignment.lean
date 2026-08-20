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

/-- The closure-alignment construction depends on an elaboration only through
its supply increase and generated-support bound.  Stating that dependency
directly lets later source extensions reuse the completed M2 graph argument
without fabricating an M2 derivation for their new syntax. -/
theorem supportedCertificateClosureAlignment_of_support
    {context : Context} {start next : Supply} {left right : Generated}
    (wellFormed : start.WellFormedFor context)
    (increases : start.Le next)
    (rightSupportBelow : ∀ candidate,
      candidate ∈ right.unificationVars →
        candidate.Below next.ty next.cap)
    (certificate : SupportedEntailedAlignmentCertificate
      start next left right)
    (leftClosure : PrincipalBlockClosure left)
    (rightClosure : PrincipalBlockClosure right)
    (leftAbsorbing : leftClosure.Absorbing)
    (rightAbsorbing : rightClosure.Absorbing) :
    Nonempty (ProvenancedFreshClosureAlignment
      leftClosure rightClosure context next) := by
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
      (fun _ member => member) rightSupportBelow
    intro alias member
    exact (rightFresh alias member).below
  have contextBelow : context.initialSupply.Le next :=
    Supply.le_trans wellFormed increases
  exact ⟨provenancedAliasedEntailedFreshClosureAlignment
    certificate.leftAliases certificate.rightAliases
    leftAdmissible rightAdmissible
    certificate.leftTargetFixed certificate.rightTargetFixed
    certificate.aligned leftClosure rightClosure
    leftAbsorbing rightAbsorbing context next
    leftContextFixed rightContextFixed contextBelow
    rightAugmentedBelow⟩

/-- Concrete implementation of the generic closure theorem consumed by the
full M2 source induction. -/
theorem supportedCertificateClosureAlignmentComplete :
    SupportedCertificateClosureAlignmentComplete := by
  intro signature context expression start next left right
    wellFormed leftElaboration rightElaboration certificate
    leftClosure rightClosure leftAbsorbing rightAbsorbing
  exact supportedCertificateClosureAlignment_of_support wellFormed
    rightElaboration.supply_le_next
    (rightElaboration.support_below wellFormed) certificate
    leftClosure rightClosure leftAbsorbing rightAbsorbing

end TypePM.Source
