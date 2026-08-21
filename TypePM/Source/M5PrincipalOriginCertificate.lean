import TypePM.Source.M5CompletionArchitecture
import TypePM.Source.M4RawOriginRecursiveProducer
import TypePM.Source.M4FuelEmbeddedCertificateBridge

/-!
# Principal-derivation-indexed origin certificates

This module connects structural raw-origin request plans to the M5 completion
architecture without erasing the principal M4 derivation that selected the
solved substitution.  One request policy chooses an environment demand before
runtime values are supplied.  For every evaluator fuel and every applicable
result observation, the policy then supplies either

* a structural `RawOriginRequestPlan`, together with the explicit environment
  transport needed by a later instance substitution, or
* an additional preservation producer.  The latter is the common boundary
  for the matcher, map, recursive-call, and matching-evaluation producers that
  are not constructors of the raw plan judgment.

The open-context transport in the raw branch is intentionally explicit.  A
monomorphic context agreement at the principal substitution alone does not
identify the same runtime context after an arbitrary later substitution.
Closed contexts discharge this condition canonically.
-/

namespace TypePM.Source.M5PrincipalOriginCertificate

open TypePM.Runtime
open M5CompletionArchitecture

private theorem semanticSolution_postcompose
    {generated : Generated} {earlier : Subst}
    (semantic : generated.SemanticSolution earlier) (later : Subst) :
    generated.SemanticSolution (Subst.compose later earlier) := by
  constructor
  · exact solves_postcompose semantic.1 later
  · intro obligation membership
    obtain ⟨conversionClass, conversion⟩ :=
      semantic.2 obligation membership
    exact ⟨conversionClass, by
      simpa only [Ty.apply_compose] using
        TypePM.Runtime.CheckConversion.apply conversion later⟩

/-- One demand-specific source of evaluator preservation.  The raw branch
retains the actual structural request plan.  Its environment premise states
the precise extra transport required when the public result type is a later
instance of the principal representative.  The additional branch accepts the
same conclusion already established by an S8--S10 producer. -/
inductive PrincipalOriginRequestEvidence
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) (operationalFuel : Nat)
    (outputDemand : OriginDemand) (inputDemand : OriginEnvironmentDemand)
    (target : Ty) : Type where
  | raw
      (plan : M4.RawOriginRequestPlan operationalFuel expression outputDemand
        inputDemand)
      (environmentTransport : ∀ later,
        principal.apply later = target →
          ∀ environment,
            OriginEnvironmentSafe inputDemand environment runtimeContext →
              SchemeOriginEnvironmentSafe inputDemand
                (Subst.compose later derivation.closure.substitution)
                environment context) :
      PrincipalOriginRequestEvidence derivation runtimeContext operationalFuel
        outputDemand inputDemand target
  | elaboration
      (certificate : ∀ {staticFuel supply generated next}
        (sourceElaboration : M4.ElaboratesFuel signature staticFuel context
          expression supply generated next),
          Nonempty (M4.ExactRawOriginRequestCertificate sourceElaboration
            operationalFuel outputDemand inputDemand))
      (environmentTransport : ∀ later,
        principal.apply later = target →
          ∀ environment,
            OriginEnvironmentSafe inputDemand environment runtimeContext →
              SchemeOriginEnvironmentSafe inputDemand
                (Subst.compose later derivation.closure.substitution)
                environment context) :
      PrincipalOriginRequestEvidence derivation runtimeContext operationalFuel
        outputDemand inputDemand target
  | additional
      (preserves : ∀ environment,
        OriginEnvironmentSafe inputDemand environment runtimeContext →
          OriginResultSafe outputDemand target
            (evalFuel operationalFuel environment expression)) :
      PrincipalOriginRequestEvidence derivation runtimeContext operationalFuel
        outputDemand inputDemand target

namespace PrincipalOriginRequestEvidence

/-- Both request sources imply the same concrete evaluator preservation
statement.  The raw proof postcomposes the closure solution with the exact
instance substitution instead of replacing the principal representative by
an unrelated solved type. -/
theorem preserves
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    {runtimeContext : List Ty} {operationalFuel : Nat}
    {outputDemand : OriginDemand} {inputDemand : OriginEnvironmentDemand}
    {target : Ty} {environment : ValueEnvironment}
    (evidence : PrincipalOriginRequestEvidence derivation runtimeContext
      operationalFuel outputDemand inputDemand target)
    (compatible : SignatureCompatible signature.base)
    (closureSemantic : derivation.generated.SemanticSolution
      derivation.closure.substitution)
    (instantiation : IsInstance principal target)
    (environmentSafe : OriginEnvironmentSafe inputDemand environment
      runtimeContext) :
    OriginResultSafe outputDemand target
      (evalFuel operationalFuel environment expression) := by
  cases evidence with
  | additional preserves => exact preserves environment environmentSafe
  | raw plan environmentTransport =>
      rcases instantiation with ⟨later, targetEq⟩
      rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
      obtain ⟨exactCertificate⟩ := plan.exactCertificate elaboration
      let solution := Subst.compose later derivation.closure.substitution
      have semantic : derivation.generated.SemanticSolution solution :=
        semanticSolution_postcompose closureSemantic later
      have sourceEnvironmentSafe : SchemeOriginEnvironmentSafe inputDemand
          solution environment context :=
        environmentTransport later targetEq environment environmentSafe
      have safe := exactCertificate.certificate.preserves compatible solution
        semantic environment (by
          simpa [exactCertificate.input_eq] using sourceEnvironmentSafe)
      have generatedTargetEq :
          derivation.generated.target.apply solution = target := by
        calc
          derivation.generated.target.apply solution =
              derivation.closure.target.apply later := by
                simp [solution, PrincipalBlockClosure.target,
                  Ty.apply_compose]
          _ = principal.apply later := by rw [← derivation.target_eq]
          _ = target := targetEq
      simpa [generatedTargetEq] using safe
  | elaboration certificate environmentTransport =>
      rcases instantiation with ⟨later, targetEq⟩
      rcases derivation.elaboration with ⟨staticFuel, sourceElaboration⟩
      obtain ⟨exactCertificate⟩ := certificate sourceElaboration
      let solution := Subst.compose later derivation.closure.substitution
      have semantic : derivation.generated.SemanticSolution solution :=
        semanticSolution_postcompose closureSemantic later
      have sourceEnvironmentSafe : SchemeOriginEnvironmentSafe inputDemand
          solution environment context :=
        environmentTransport later targetEq environment environmentSafe
      have safe := exactCertificate.certificate.preserves compatible solution
        semantic environment (by
          simpa [exactCertificate.input_eq] using sourceEnvironmentSafe)
      have generatedTargetEq :
          derivation.generated.target.apply solution = target := by
        calc
          derivation.generated.target.apply solution =
              derivation.closure.target.apply later := by
                simp [solution, PrincipalBlockClosure.target,
                  Ty.apply_compose]
          _ = principal.apply later := by rw [← derivation.target_eq]
          _ = target := targetEq
      simpa [generatedTargetEq] using safe

end PrincipalOriginRequestEvidence

/-- A total input-demand policy indexed by one exact principal derivation.
The request evidence may inspect the requested instance type and its
applicability proof, but the selected input demand cannot: it is fixed solely
by evaluator fuel and the finite output-demand tree. -/
structure PrincipalOriginRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Type where
  inputDemand : Nat → OriginDemand → OriginEnvironmentDemand
  request : ∀ (operationalFuel : Nat) (outputDemand : OriginDemand)
      {target : Ty},
    IsInstance principal target →
      OriginDemandApplicable outputDemand target →
        Nonempty (PrincipalOriginRequestEvidence derivation runtimeContext
          operationalFuel outputDemand
          (inputDemand operationalFuel outputDemand) target)

/-- Raw-plan-only producer data.  Unlike a bare family of plans, this retains
the open-context transport needed to use the postcomposed semantic solution.
This condition is automatic at a closed root and is deliberately not inferred
from principal context compatibility for an arbitrary open context. -/
structure PrincipalRawOriginPlanProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Type where
  inputDemand : Nat → OriginDemand → OriginEnvironmentDemand
  plan : ∀ operationalFuel outputDemand,
    M4.RawOriginRequestPlan operationalFuel expression outputDemand
      (inputDemand operationalFuel outputDemand)
  environmentTransport : ∀ operationalFuel outputDemand later target,
    principal.apply later = target →
      ∀ environment,
        OriginEnvironmentSafe (inputDemand operationalFuel outputDemand)
            environment runtimeContext →
          SchemeOriginEnvironmentSafe
            (inputDemand operationalFuel outputDemand)
            (Subst.compose later derivation.closure.substitution)
            environment context

namespace PrincipalRawOriginPlanProducer

/-- The realized monomorphic runtime context is unaffected by any later
instance substitution.  This is the concrete open-context condition under
which a principal context realization can be reused at every public instance
type.  Closed and ground runtime contexts satisfy it. -/
def SubstitutionStableRuntimeContext (runtimeContext : List Ty) : Prop :=
  ∀ later, runtimeContext.map (Ty.apply later) = runtimeContext

/-- Closed runtime contexts are substitution-stable. -/
theorem substitutionStable_nil :
    SubstitutionStableRuntimeContext [] := by
  intro later
  rfl

/-- Principal monomorphic context agreement plus substitution stability
constructs the exact raw environment transport retained by this producer. -/
def ofStablePlans
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    {runtimeContext : List Ty}
    (contextCompatible : MonomorphicContextCompatible context runtimeContext
      derivation.closure.substitution)
    (stable : SubstitutionStableRuntimeContext runtimeContext)
    (inputDemand : Nat → OriginDemand → OriginEnvironmentDemand)
    (plan : ∀ operationalFuel outputDemand,
      M4.RawOriginRequestPlan operationalFuel expression outputDemand
        (inputDemand operationalFuel outputDemand)) :
    PrincipalRawOriginPlanProducer derivation runtimeContext where
  inputDemand := inputDemand
  plan := plan
  environmentTransport := by
    intro operationalFuel outputDemand later target targetEq environment safe
    have postcomposed := contextCompatible.postcompose later
    rw [stable later] at postcomposed
    exact safe.toSchemeOrigin postcomposed

/-- Embed a family of structural raw plans into the composite producer. -/
def toRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    {runtimeContext : List Ty}
    (producer : PrincipalRawOriginPlanProducer derivation runtimeContext) :
    PrincipalOriginRequestProducer derivation runtimeContext where
  inputDemand := producer.inputDemand
  request := by
    intro operationalFuel outputDemand target instantiation _applicable
    exact ⟨.raw (producer.plan operationalFuel outputDemand)
      (fun later targetEq =>
        producer.environmentTransport operationalFuel outputDemand later target
          targetEq)⟩

/-- At a closed root, every postcomposed solution has the unique empty
source/runtime environment realization. -/
def closed
    (inputDemand : Nat → OriginDemand → OriginEnvironmentDemand)
    (plan : ∀ operationalFuel outputDemand,
      M4.RawOriginRequestPlan operationalFuel expression outputDemand
        (inputDemand operationalFuel outputDemand))
    (derivation : M4.PrincipalTypingDerivation signature [] expression
      principal) :
    PrincipalRawOriginPlanProducer derivation [] where
  inputDemand := inputDemand
  plan := plan
  environmentTransport := by
    intro operationalFuel outputDemand later target targetEq environment safe
    have environmentEq : environment = [] := by
      simpa using safe.1
    subst environment
    exact SchemeOriginEnvironmentSafe.nil _ _

end PrincipalRawOriginPlanProducer

namespace PrincipalOriginRequestProducer

/-- Package an already established S8--S10 preservation producer.  The
applicability and instance hypotheses remain visible inputs; no evaluator
result equation or completed-search equation is stored. -/
def ofAdditional
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    {runtimeContext : List Ty}
    (inputDemand : Nat → OriginDemand → OriginEnvironmentDemand)
    (preserves : ∀ (operationalFuel : Nat) (outputDemand : OriginDemand)
      {target : Ty},
      IsInstance principal target →
        OriginDemandApplicable outputDemand target →
          ∀ environment,
            OriginEnvironmentSafe (inputDemand operationalFuel outputDemand)
                environment runtimeContext →
              OriginResultSafe outputDemand target
                (evalFuel operationalFuel environment expression)) :
    PrincipalOriginRequestProducer derivation runtimeContext where
  inputDemand := inputDemand
  request := by
    intro operationalFuel outputDemand target instantiation applicable
    exact ⟨.additional
      (preserves operationalFuel outputDemand instantiation applicable)⟩

end PrincipalOriginRequestProducer

/-- Composite M5 runtime data.  It retains the exact closure substitution
through the derivation index, its concrete semantic-solution proof, the
monomorphic runtime-context realization, the evaluator signature agreement,
and the total request producer. -/
structure PrincipalOriginCertificateData
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Type where
  closureSemantic : derivation.generated.SemanticSolution
    derivation.closure.substitution
  contextCompatible : MonomorphicContextCompatible context runtimeContext
    derivation.closure.substitution
  signatureCompatible : SignatureCompatible signature.base
  requests : PrincipalOriginRequestProducer derivation runtimeContext

/-- Architecture-facing propositional certificate family.  The proof object
is retained under `Nonempty`; the demand selector below uses the same chosen
data in both the input-demand family and typed-evaluation theorem. -/
def Certificate : RuntimeCertificateFamily :=
  fun derivation runtimeContext =>
    Nonempty (PrincipalOriginCertificateData derivation runtimeContext)

/-- Explicit derivation-indexed producer predicate used as the current state
erasure scope boundary.  It asks only for the operational request producer;
closure semantics, signature readiness, and context realization are supplied
by the surrounding principal derivation and architecture hypotheses. -/
def DerivationRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Prop :=
  Nonempty (PrincipalOriginRequestProducer derivation runtimeContext)

/-- Construct the composite certificate from the explicit producer predicate.
This is the state-erasure step that is available before a full syntax-recursive
proof that every expression in the intended M5 fragment has such a producer. -/
theorem certificate_of_derivationRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    {runtimeContext : List Ty}
    (signatureReady : RuntimeSignatureReady signature)
    (contextRealization : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (producer : DerivationRequestProducer derivation runtimeContext) :
    Certificate derivation runtimeContext := by
  rcases producer with ⟨requests⟩
  exact ⟨{
    closureSemantic :=
      TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
        derivation.closure
    contextCompatible := contextRealization
    signatureCompatible := signatureReady.2
    requests := requests }⟩

/-- Direct raw-plan entrypoint into the derivation-indexed producer
predicate. -/
theorem derivationRequestProducer_of_raw
    (producer : PrincipalRawOriginPlanProducer derivation runtimeContext) :
    DerivationRequestProducer derivation runtimeContext :=
  ⟨producer.toRequestProducer⟩

/-- A derivation-indexed producer theorem discharges the architecture's
principal-state-erasure field.  The expression-only `scope` is not used to
hide certificates: `produce` must construct one for the exact derivation and
runtime context presented by state erasure. -/
theorem principalStateErasure_of_derivationRequestProducer
    (produce : ∀ {signature context expression principal}
      (derivation : M4.PrincipalTypingDerivation signature context expression
        principal)
      (runtimeContext : List Ty),
      RuntimeSignatureReady signature →
        scope derivation →
          MonomorphicRuntimeContextRelation derivation runtimeContext →
            DerivationRequestProducer derivation runtimeContext) :
    PrincipalStateErasure scope Certificate
      MonomorphicRuntimeContextRelation := by
  intro signature context expression principal derivation runtimeContext
    signatureReady inScope contextRealization
  exact certificate_of_derivationRequestProducer signatureReady
    contextRealization
    (produce derivation runtimeContext signatureReady inScope
      contextRealization)

/-- Raw-plan specialization of the preceding state-erasure theorem.  The
premise remains indexed by the exact derivation and runtime context, so an
expression-only scope proposition cannot manufacture unrelated plans. -/
theorem principalStateErasure_of_rawPlanProducers
    (produce : ∀ {signature context expression principal}
      (derivation : M4.PrincipalTypingDerivation signature context expression
        principal)
      (runtimeContext : List Ty),
      RuntimeSignatureReady signature →
        scope derivation →
          MonomorphicRuntimeContextRelation derivation runtimeContext →
            PrincipalRawOriginPlanProducer derivation runtimeContext) :
    PrincipalStateErasure scope Certificate
      MonomorphicRuntimeContextRelation := by
  apply principalStateErasure_of_derivationRequestProducer
  intro signature context expression principal derivation runtimeContext
    signatureReady inScope contextRealization
  exact derivationRequestProducer_of_raw
    (produce derivation runtimeContext signatureReady inScope
      contextRealization)

/-- Closed-root construction from a total raw request-plan family. -/
theorem closedCertificate_of_rawPlans
    (signatureReady : RuntimeSignatureReady signature)
    (derivation : M4.PrincipalTypingDerivation signature [] expression
      principal)
    (inputDemand : Nat → OriginDemand → OriginEnvironmentDemand)
    (plans : ∀ operationalFuel outputDemand,
      M4.RawOriginRequestPlan operationalFuel expression outputDemand
        (inputDemand operationalFuel outputDemand)) :
    Certificate derivation [] := by
  apply certificate_of_derivationRequestProducer signatureReady
    (derivation := derivation) (runtimeContext := [])
  · exact M5CompletionArchitecture.monomorphicRuntimeContext_closed derivation
  · exact derivationRequestProducer_of_raw
      (PrincipalRawOriginPlanProducer.closed inputDemand plans derivation)

/-- Demand selector induced by the certificate's total request policy. -/
noncomputable def evaluationInputDemand :
    EvaluationInputDemandFamily Certificate originDemandSafetyRelations := by
  intro signature context expression principal derivation runtimeContext
    certificate operationalFuel outputDemand
  exact (Classical.choice certificate).requests.inputDemand operationalFuel
    outputDemand

/-- General typed evaluation for the principal-origin certificate family.
The evaluator fuel passed to the request producer is exactly the fuel passed
to `evalFuel`; no fixed fuel or result equation is part of the statement. -/
theorem typedEvaluation :
    TypedEvaluation Certificate originDemandSafetyRelations
      evaluationInputDemand evalFuel := by
  intro signature context expression principal target derivation runtimeContext
    certificate instantiation operationalFuel outputDemand environment
    applicable environmentSafe
  let data := Classical.choice certificate
  have selectedSafe : OriginEnvironmentSafe
      (data.requests.inputDemand operationalFuel outputDemand)
      environment runtimeContext := by
    change OriginEnvironmentSafe
      ((Classical.choice certificate).requests.inputDemand operationalFuel
        outputDemand) environment runtimeContext at environmentSafe
    simpa [data] using environmentSafe
  obtain ⟨request⟩ := data.requests.request operationalFuel outputDemand
    instantiation applicable
  exact request.preserves data.signatureCompatible data.closureSemantic
    instantiation selectedSafe

end TypePM.Source.M5PrincipalOriginCertificate
