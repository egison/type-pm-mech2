import TypePM.Source.M4CanonicalCertificateTransport
import TypePM.Source.M4RawOriginRecursiveProducer
import TypePM.Source.M5PrincipalOriginCertificate

/-!
# Coherence transport for closed raw-origin plans

An exact raw-origin certificate is indexed by a concrete fuel-indexed M4
elaboration.  Coherent principal derivations need not contain definitionally
equal elaboration witnesses, so transporting that dependent object directly
would impose an unnecessarily strong equality requirement.

`RawOriginRequestPlan` already gives the stronger invariant needed here: one
plan constructs an exact certificate for every raw elaboration of the same
source expression.  This module packages that invariant at the principal-
derivation boundary and reconstructs the exact certificate at the target of a
coherence comparison.
-/

namespace TypePM.Source.M4

open TypePM.Runtime
open TypePM.Source.M5CompletionArchitecture

/-- Exact raw-origin evidence attached to one principal M4 derivation.

The structural fuel hidden by `PrincipalTypingDerivation.elaboration` is
exposed existentially, while the generated block and finishing supply remain
those of the principal derivation.  This is the useful principal-indexed unit
for larger runtime-certificate families. -/
def RawOriginRequestPlan.PrincipalExactCertificate
    (_plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    {signature : FrozenSignature} {context : Context} {principal : Ty}
    (derivation : PrincipalTypingDerivation signature context expression
      principal) : Prop :=
  ∃ staticFuel,
    ∃ elaboration : ElaboratesFuel signature staticFuel context expression
        context.initialSupply derivation.generated derivation.next,
      Nonempty (ExactRawOriginRequestCertificate elaboration operationalFuel
        outputDemand inputDemand)

/-- A raw request plan supplies principal-indexed exact evidence for every
principal derivation of its expression. -/
theorem RawOriginRequestPlan.principalExactCertificate
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (derivation : PrincipalTypingDerivation signature context expression
      principal) :
    plan.PrincipalExactCertificate derivation := by
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  exact ⟨staticFuel, elaboration, plan.exactCertificate elaboration⟩

/-- Reconstruct exact raw-origin evidence at the other endpoint of a coherent
closed principal pair.

The source evidence records that the caller retained this plan.  The target
certificate is deliberately regenerated from the same plan rather than cast
through an equality between dependent elaboration witnesses. -/
theorem RawOriginRequestPlan.principalExactCertificate_of_coherence
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (left : PrincipalTypingDerivation signature [] expression leftPrincipal)
    (right : PrincipalTypingDerivation signature [] expression rightPrincipal)
    (_pair : FullM2PairCoherence (Context.initialSupply []) left.next
      right.next left.generated right.generated [])
    (_alignment : ProvenancedFreshClosureAlignment
      left.closure right.closure [] left.next)
    (_source : plan.PrincipalExactCertificate left) :
    plan.PrincipalExactCertificate right :=
  plan.principalExactCertificate right

/-- The principal derivation selected by a successful public inference run
receives exact raw-origin evidence from the same request plan. -/
theorem RawOriginRequestPlan.canonicalPrincipalExactCertificate
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (wellFormed : signature.WellFormed)
    (success : infer signature [] expression = some inferred) :
    plan.PrincipalExactCertificate
      (canonicalPrincipalTypingDerivation wellFormed success) :=
  plan.principalExactCertificate _

/-- A closed runtime-certificate family carrying a raw-origin request plan and
the exact certificate it generates for the retained principal derivation.

The operational fuel and both demands are family parameters.  The plan stays
existential because the source expression is an index of
`RuntimeCertificateFamily`; coherence transport preserves that expression and
therefore preserves the very same plan witness. -/
def ClosedRawOriginPlanCertificateFamily
    (operationalFuel : Nat) (outputDemand : OriginDemand)
    (inputDemand : OriginEnvironmentDemand) : RuntimeCertificateFamily :=
  fun {_signature} {context} {expression} {_principal} derivation
      runtimeContext =>
    context = [] ∧ runtimeContext = [] ∧
      ∃ plan : RawOriginRequestPlan operationalFuel expression outputDemand
          inputDemand,
        plan.PrincipalExactCertificate derivation

/-- Closed raw-origin plan certificates satisfy the generic M4 coherence
transport boundary.  In particular, the target certificate contains the same
request plan and freshly reconstructed exact evidence for the target
elaboration. -/
theorem closedRawOriginPlanCertificate_respectsCoherence
    (operationalFuel : Nat) (outputDemand : OriginDemand)
    (inputDemand : OriginEnvironmentDemand) :
    ClosedRuntimeCertificateRespectsCoherence
      (ClosedRawOriginPlanCertificateFamily operationalFuel outputDemand
        inputDemand) := by
  intro signature expression leftPrincipal rightPrincipal left right pair
    alignment certificate
  rcases certificate with ⟨_leftContext, runtimeContext, plan, source⟩
  exact ⟨rfl, runtimeContext, plan,
    plan.principalExactCertificate_of_coherence left right pair alignment
      source⟩

/-- Specialization of the generic canonical transport theorem to closed
raw-origin plan certificates.  This is the composite-facing API: the target
certificate retains a request plan at the same operational fuel and demands,
but its exact evidence is indexed by the canonical public-inference
derivation. -/
theorem closedRawOriginPlanCertificate_toCanonical
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {expression : Expr} {principal target : Ty}
    (source : PrincipalTypingDerivation signature [] expression principal)
    (instantiation : IsInstance principal target)
    (certificate : ClosedRawOriginPlanCertificateFamily operationalFuel
      outputDemand inputDemand source []) :
    ∃ inferred,
      ∃ success : infer signature [] expression = some inferred,
        ClosedRawOriginPlanCertificateFamily operationalFuel outputDemand
            inputDemand
            (canonicalPrincipalTypingDerivation wellFormed success) [] ∧
          IsInstance inferred target :=
  closedCertificate_toCanonical
    (closedRawOriginPlanCertificate_respectsCoherence operationalFuel
      outputDemand inputDemand)
    wellFormed source instantiation certificate

end TypePM.Source.M4

namespace TypePM.Source.M5PrincipalOriginCertificate

open TypePM.Runtime
open M5CompletionArchitecture

private theorem isInstance_trans
    {first second third : Ty}
    (firstToSecond : IsInstance first second)
    (secondToThird : IsInstance second third) :
    IsInstance first third := by
  obtain ⟨firstSubstitution, firstEquality⟩ := firstToSecond
  obtain ⟨secondSubstitution, secondEquality⟩ := secondToThird
  refine ⟨Subst.compose secondSubstitution firstSubstitution, ?_⟩
  rw [← Ty.apply_compose, firstEquality, secondEquality]

/-- Explicit policy for transporting an additional, non-raw request across
one coherent pair of closed principal derivations.

The raw-plan case needs no premise because the same structural plan can
generate a new exact certificate for the target derivation.  An additional
producer is not a raw-plan derivation, so its target-side preservation theorem
must be supplied here.  The policy receives both instance witnesses and the
applicability proof used for this request; no target producer is inferred from
coherence alone. -/
structure ClosedAdditionalRequestTransportPolicy
    {signature : FrozenSignature} {expression : Expr}
    {leftPrincipal rightPrincipal : Ty}
    (left : M4.PrincipalTypingDerivation signature [] expression
      leftPrincipal)
    (right : M4.PrincipalTypingDerivation signature [] expression
      rightPrincipal) : Type where
  transport : ∀
      (inputDemand : OriginEnvironmentDemand)
      (operationalFuel : Nat) (outputDemand : OriginDemand) (target : Ty),
    IsInstance leftPrincipal target →
      IsInstance rightPrincipal target →
        OriginDemandApplicable outputDemand target →
          (∀ environment,
            OriginEnvironmentSafe inputDemand environment [] →
              OriginResultSafe outputDemand target
                (evalFuel operationalFuel environment expression)) →
            ∀ environment,
              OriginEnvironmentSafe inputDemand environment [] →
                OriginResultSafe outputDemand target
                  (evalFuel operationalFuel environment expression)

/-- Pair-indexed premise required to transport every additional request in a
closed composite certificate.  Keeping the coherence witnesses in this
boundary lets a concrete producer use generated-block or closure-alignment
information when rebuilding its endpoint-specific theorem. -/
abbrev ClosedAdditionalRequestTransport : Type :=
  ∀ {signature : FrozenSignature} {expression : Expr}
      {leftPrincipal rightPrincipal : Ty}
      (left : M4.PrincipalTypingDerivation signature [] expression
        leftPrincipal)
      (right : M4.PrincipalTypingDerivation signature [] expression
        rightPrincipal)
      (_pair : FullM2PairCoherence (Context.initialSupply []) left.next
        right.next left.generated right.generated [])
      (_alignment : ProvenancedFreshClosureAlignment
        left.closure right.closure [] left.next),
    ClosedAdditionalRequestTransportPolicy left right

/-- Canonical transport for an additional request.  Once the left producer
has returned its preservation theorem, that theorem's type contains only the
shared expression, demand, fuel, requested target, and closed runtime
environment.  Neither principal derivation occurs in the proposition, so the
target theorem is definitionally the source theorem. -/
def closedAdditionalRequestTransportPolicy
    {signature : FrozenSignature} {expression : Expr}
    {leftPrincipal rightPrincipal : Ty}
    (left : M4.PrincipalTypingDerivation signature [] expression
      leftPrincipal)
    (right : M4.PrincipalTypingDerivation signature [] expression
      rightPrincipal) :
    ClosedAdditionalRequestTransportPolicy left right where
  transport := by
    intro inputDemand operationalFuel outputDemand target leftInstantiation
      rightInstantiation applicable preserves
    exact preserves

/-- Every additional request in the present composite representation has the
canonical identity transport.  Coherence is still needed to obtain the left
instance witness used to ask the source producer for that theorem; no
derivation-indexed evidence is fabricated. -/
def closedAdditionalRequestTransport : ClosedAdditionalRequestTransport :=
  fun left right _pair _alignment =>
    closedAdditionalRequestTransportPolicy left right

namespace PrincipalOriginRequestProducer

/-- Transport a closed request producer across one coherent principal pair.
Raw requests retain their plan, and elaboration requests retain their
derivation-independent exact-certificate builder; both rebuild the closed
environment premise.  Additional requests are delegated to the explicit
policy. -/
def ofClosedCoherence
    {signature : FrozenSignature} {expression : Expr}
    {leftPrincipal rightPrincipal : Ty}
    {left : M4.PrincipalTypingDerivation signature [] expression
      leftPrincipal}
    {right : M4.PrincipalTypingDerivation signature [] expression
      rightPrincipal}
    (source : PrincipalOriginRequestProducer left [])
    (alignment : ProvenancedFreshClosureAlignment
      left.closure right.closure [] left.next)
    (additional : ClosedAdditionalRequestTransportPolicy left right) :
    PrincipalOriginRequestProducer right [] where
  inputDemand := source.inputDemand
  request := by
    intro operationalFuel outputDemand target rightInstantiation applicable
    have mutualInstances :=
      alignment.principalTargets_mutualInstances left right
    have leftInstantiation : IsInstance leftPrincipal target :=
      isInstance_trans mutualInstances.1 rightInstantiation
    obtain ⟨sourceEvidence⟩ := source.request operationalFuel outputDemand
      leftInstantiation applicable
    refine ⟨?_⟩
    cases sourceEvidence with
    | raw plan _environmentTransport =>
        apply PrincipalOriginRequestEvidence.raw plan
        intro later targetEq environment environmentSafe
        have environmentEq : environment = [] := by
          simpa using environmentSafe.1
        subst environment
        exact SchemeOriginEnvironmentSafe.nil _ _
    | elaboration certificate _environmentTransport =>
        apply PrincipalOriginRequestEvidence.elaboration certificate
        intro later targetEq environment environmentSafe
        have environmentEq : environment = [] := by
          simpa using environmentSafe.1
        subst environment
        exact SchemeOriginEnvironmentSafe.nil _ _
    | additional preserves =>
        exact .additional
          (additional.transport
            (source.inputDemand operationalFuel outputDemand)
            operationalFuel outputDemand target leftInstantiation
            rightInstantiation applicable preserves)

end PrincipalOriginRequestProducer

/-- Under an explicit transport policy for additional producers, the closed
principal-origin composite certificate satisfies the architecture's M4
coherence boundary. -/
theorem closedRuntimeCertificateRespectsCoherence_of_additionalTransport
    (additionalTransport : ClosedAdditionalRequestTransport) :
    ClosedRuntimeCertificateRespectsCoherence Certificate := by
  intro signature expression leftPrincipal rightPrincipal left right pair
    alignment certificate
  rcases certificate with ⟨data⟩
  refine ⟨{
    closureSemantic :=
      TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution right.closure
    contextCompatible :=
      M5CompletionArchitecture.monomorphicRuntimeContext_closed right
    signatureCompatible := data.signatureCompatible
    requests := data.requests.ofClosedCoherence alignment
      (additionalTransport left right pair alignment) }⟩

/-- Canonical transport for the complete principal-origin certificate.  The
additional-request policy is the only premise beyond the generic M4
coherence/replay results; raw request plans are reconstructed internally. -/
theorem certificate_toCanonical_of_additionalTransport
    (additionalTransport : ClosedAdditionalRequestTransport)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {expression : Expr} {principal target : Ty}
    (source : M4.PrincipalTypingDerivation signature [] expression principal)
    (instantiation : IsInstance principal target)
    (certificate : Certificate source []) :
    ∃ inferred,
      ∃ success : M4.infer signature [] expression = some inferred,
        Certificate
            (M4.canonicalPrincipalTypingDerivation wellFormed success) [] ∧
          IsInstance inferred target :=
  M5CompletionArchitecture.closedCertificate_toCanonical
    (closedRuntimeCertificateRespectsCoherence_of_additionalTransport
      additionalTransport)
    wellFormed source instantiation certificate

/-- The composite principal-origin certificate respects closed M4 coherence
without an external policy premise. -/
theorem closedRuntimeCertificateRespectsCoherence :
    ClosedRuntimeCertificateRespectsCoherence Certificate :=
  closedRuntimeCertificateRespectsCoherence_of_additionalTransport
    closedAdditionalRequestTransport

/-- Canonical transport for the composite principal-origin certificate. -/
theorem certificate_toCanonical
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {expression : Expr} {principal target : Ty}
    (source : M4.PrincipalTypingDerivation signature [] expression principal)
    (instantiation : IsInstance principal target)
    (certificate : Certificate source []) :
    ∃ inferred,
      ∃ success : M4.infer signature [] expression = some inferred,
        Certificate
            (M4.canonicalPrincipalTypingDerivation wellFormed success) [] ∧
          IsInstance inferred target :=
  certificate_toCanonical_of_additionalTransport
    closedAdditionalRequestTransport wellFormed source instantiation
      certificate

end TypePM.Source.M5PrincipalOriginCertificate
