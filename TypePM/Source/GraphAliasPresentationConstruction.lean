import TypePM.Source.InterfaceAliasReallocation
import TypePM.Source.SupportedCertificateClosureAlignment

/-!
# Constructing the source-facing representative graph

This module keeps the data-rich path through alias lifting and entailed
closure transport.  In contrast to the final alignment object, this package
retains the same-generated middle pair from which finite support-graph
aliases are constructed.
-/

namespace TypePM.Source

open FreshAliasSequence
open FreshAliasPrincipalClosure
open InterfaceAliasDecomposition

/-- Canonical same-generated closure pair underlying a supported value
comparison. -/
structure CanonicalClosureGraphData
    {start finish : Supply} {leftValue rightValue : Generated}
    (certificate : SupportedEntailedAlignmentCertificate
      start finish leftValue rightValue)
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (context : Context) where
  liftedLeft : PrincipalBlockClosure
    (FreshAliasSequence.addAll certificate.leftAliases leftValue)
  liftedRight : PrincipalBlockClosure
    (FreshAliasSequence.addAll certificate.rightAliases rightValue)
  middle : PrincipalBlockClosure
    (FreshAliasSequence.addAll certificate.rightAliases rightValue)
  liftedLeftAbsorbing : liftedLeft.Absorbing
  liftedRightAbsorbing : liftedRight.Absorbing
  middleAbsorbing : middle.Absorbing
  liftedLeftTarget : liftedLeft.target = leftClosure.target
  liftedRightTarget : liftedRight.target = rightClosure.target
  middleTarget : liftedLeft.target = middle.target
  liftedLeftSubstitution : liftedLeft.substitution =
    Subst.compose leftClosure.substitution
      (sequenceSubstitution certificate.leftAliases)
  liftedRightSubstitution : liftedRight.substitution =
    Subst.compose rightClosure.substitution
      (sequenceSubstitution certificate.rightAliases)
  middleSubstitution : middle.substitution = liftedLeft.substitution
  forward : Subst
  backward : Subst
  transport : PrincipalBlockClosure.RepresentativeTransportUsing
    middle liftedRight forward backward
  support : ClosureSupportBijection middle liftedRight forward backward context

/-- Reconstruct the lifted closures, the entailed middle closure, and the
same-generated finite support bijection used by graph presentation. -/
noncomputable def canonicalClosureGraphData
    {start finish : Supply} {leftValue rightValue : Generated}
    (certificate : SupportedEntailedAlignmentCertificate
      start finish leftValue rightValue)
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (leftAbsorbing : leftClosure.Absorbing)
    (rightAbsorbing : rightClosure.Absorbing)
    (context : Context) :
    CanonicalClosureGraphData certificate
      leftClosure rightClosure context := by
  have leftAdmissible : FreshAliasSequence.Admissible
      certificate.leftAliases leftValue :=
    AliasFreshness.admissible_of_scopedBy certificate.leftScoped
      (fun _ member => member)
  have rightAdmissible : FreshAliasSequence.Admissible
      certificate.rightAliases rightValue :=
    AliasFreshness.admissible_of_scopedBy certificate.rightScoped
      (fun _ member => member)
  let leftLift := exists_liftAll_absorbing_data certificate.leftAliases
    leftValue leftAdmissible certificate.leftTargetFixed
    leftClosure leftAbsorbing
  let liftedLeft := Classical.choose leftLift
  have liftedLeftSpec := Classical.choose_spec leftLift
  let rightLift := exists_liftAll_absorbing_data certificate.rightAliases
    rightValue rightAdmissible certificate.rightTargetFixed
    rightClosure rightAbsorbing
  let liftedRight := Classical.choose rightLift
  have liftedRightSpec := Classical.choose_spec rightLift
  let transported := liftedLeft.transportEntailed_absorbing_target
    certificate.aligned.hardEquivalent certificate.aligned.pendingAligned
    liftedLeftSpec.1 certificate.aligned.targetEntailed
  let middle := Classical.choose transported
  have middleSpec := Classical.choose_spec transported
  let related := middle.representativeTransport liftedRight
  let forward := Classical.choose related
  let remaining := Classical.choose_spec related
  let backward := Classical.choose remaining
  have transport : PrincipalBlockClosure.RepresentativeTransportUsing
      middle liftedRight forward backward := Classical.choose_spec remaining
  exact
    { liftedLeft := liftedLeft
      liftedRight := liftedRight
      middle := middle
      liftedLeftAbsorbing := liftedLeftSpec.1
      liftedRightAbsorbing := liftedRightSpec.1
      middleAbsorbing := middleSpec.2.2.2.1
      liftedLeftTarget := liftedLeftSpec.2.1
      liftedRightTarget := liftedRightSpec.2.1
      middleTarget := middleSpec.2.2.2.2
      liftedLeftSubstitution := liftedLeftSpec.2.2.2.2
      liftedRightSubstitution := liftedRightSpec.2.2.2.2
      middleSubstitution := middleSpec.2.2.1
      forward := forward
      backward := backward
      transport := transport
      support := ClosureSupportConstruction.build transport context }

namespace VisibleSupportGraph

/-- Moved ordinary edges observable in the closed left context and requiring
an explicit alias on the left interface. -/
def leftTySources
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (data : ClosureSupportBijection left right forward backward context)
    (context : Context) : List TyVar :=
  data.support.ty.source.filter fun source => decide
    (source ∈ (context.applyFree left.substitution).freeTyVars ∧
      data.support.ty.forward source ≠ source ∧
      data.support.ty.forward source ∉ context.freeTyVars)

def rightTySources
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (data : ClosureSupportBijection left right forward backward context)
    (context : Context) : List TyVar :=
  data.support.ty.source.filter fun source => decide
    (source ∈ (context.applyFree left.substitution).freeTyVars ∧
      data.support.ty.forward source ≠ source ∧
      source ∉ context.freeTyVars)

def leftCapSources
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (data : ClosureSupportBijection left right forward backward context)
    (context : Context) : List CapVar :=
  data.support.cap.source.filter fun source => decide
    (source ∈ (context.applyFree left.substitution).freeCapVars ∧
      data.support.cap.forward source ≠ source ∧
      data.support.cap.forward source ∉ context.freeCapVars)

def rightCapSources
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (data : ClosureSupportBijection left right forward backward context)
    (context : Context) : List CapVar :=
  data.support.cap.source.filter fun source => decide
    (source ∈ (context.applyFree left.substitution).freeCapVars ∧
      data.support.cap.forward source ≠ source ∧
      source ∉ context.freeCapVars)

def leftAliases
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (data : ClosureSupportBijection left right forward backward context)
    (context : Context) : List FreshAliasSequence.Alias :=
  (leftTySources data context).map (fun source =>
      FreshAliasSequence.Alias.ty (data.support.ty.forward source) source) ++
    (leftCapSources data context).map (fun source =>
      FreshAliasSequence.Alias.cap (data.support.cap.forward source) source)

def rightAliases
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (data : ClosureSupportBijection left right forward backward context)
    (context : Context) : List FreshAliasSequence.Alias :=
  (rightTySources data context).map (fun source =>
      FreshAliasSequence.Alias.ty source (data.support.ty.forward source)) ++
    (rightCapSources data context).map (fun source =>
      FreshAliasSequence.Alias.cap source (data.support.cap.forward source))

def leftHidden
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (data : ClosureSupportBijection left right forward backward context)
    (context : Context) : List UnificationVar :=
  (leftTySources data context).map (fun source =>
      .ty (data.support.ty.forward source)) ++
    (leftCapSources data context).map (fun source =>
      .cap (data.support.cap.forward source))

def rightHidden
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (data : ClosureSupportBijection left right forward backward context)
    (context : Context) : List UnificationVar :=
  (rightTySources data context).map UnificationVar.ty ++
    (rightCapSources data context).map UnificationVar.cap

end VisibleSupportGraph

end TypePM.Source
