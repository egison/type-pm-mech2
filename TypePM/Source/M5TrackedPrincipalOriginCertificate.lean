import TypePM.Source.M5PrincipalOriginCertificate

/-!
# Search-occurrence-tracked principal Origin certificates

`PrincipalOriginRequestEvidence` deliberately exposes only the evaluator
preservation needed by M5 typed evaluation.  In particular, its elaboration
and additional branches do not retain the child request plans from which a
nested matching search was produced.  This module adds a parallel wrapper;
the existing certificate remains unchanged and is recovered by projection.

`SearchPlanCoverage` is indexed by the exact M4 elaboration judgment.  Its
structural constructors retain coverage for every evaluated child, while the
two matching constructors retain the dedicated raw matching plan.  Therefore
an unrelated syntax tree cannot be inserted as coverage for a principal
derivation.  The dynamic fact that evaluation reached one of these static
occurrences is a separate, later `IssuedAtOccurrence` layer.
-/

namespace TypePM.Source.M5TrackedPrincipalOriginCertificate

open TypePM.Runtime
open M4
open M5CompletionArchitecture
open M5PrincipalOriginCertificate

/- The following helpers assemble exactly the proof indices used by the
structural constructors below. -/

private def appElaboration
    (functionElaboration : ElaboratesFuel signature staticFuel context function
      supply generatedFunction afterFunction)
    (argumentElaboration : ElaboratesFuel signature staticFuel context argument
      afterFunction generatedArgument afterArgument) :
    ElaboratesFuel signature (staticFuel + 1) context (.app function argument)
      supply
      (Generated.fromApp generatedFunction generatedArgument
        (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
      (afterArgument.nextTy 2) := by
  simp only [ElaboratesFuel]
  exact ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
    functionElaboration, argumentElaboration, rfl, rfl⟩

private def tupleElaboration
    (itemsElaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context items supply generated next) :
    ElaboratesFuel signature (staticFuel + 1) context (.tuple items) supply
      ⟨.prod generated.targets, generated.hard, generated.pending⟩ next := by
  simp only [ElaboratesFuel]
  exact ⟨generated, itemsElaboration, rfl⟩

private def letElaboration
    (valueElaboration : ElaboratesFuel signature staticFuel context value supply
      generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (bodyElaboration : ElaboratesFuel signature staticFuel
      ((context.applyFree closure.substitution).generalize closure.target ::
        context.applyFree closure.substitution)
      body
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply)
      generatedBody next) :
    ElaboratesFuel signature (staticFuel + 1) context (.letE value body) supply
      (Generated.fromLet
        (context.interfaceEquations closure.substitution) generatedBody) next := by
  simp only [ElaboratesFuel]
  exact ⟨generatedValue, afterValue, valueElaboration, closure, generatedBody,
    absorbing, bodyElaboration, rfl⟩

private def ctorElaboration
    (lookup : signature.base.lookupDataConstructor constructor = some scheme)
    (arity : arguments.length = scheme.callArity)
    (closed : scheme.Closed)
    (argumentsElaboration : CallElaboratesUsing
      (ElaboratesFuel signature staticFuel) context
      ⟨(scheme.instantiate supply).1, [], []⟩ arguments
      (scheme.instantiate supply).2 generated next) :
    ElaboratesFuel signature (staticFuel + 1) context
      (.ctor constructor arguments) supply generated next := by
  simp only [ElaboratesFuel]
  exact ⟨scheme, lookup, arity, closed, argumentsElaboration⟩

private def primElaboration
    (lookup : signature.base.lookupPrimitive operation = some scheme)
    (arity : arguments.length = scheme.callArity)
    (closed : scheme.Closed)
    (argumentsElaboration : CallElaboratesUsing
      (ElaboratesFuel signature staticFuel) context
      ⟨(scheme.instantiate supply).1, [], []⟩ arguments
      (scheme.instantiate supply).2 generated next) :
    ElaboratesFuel signature (staticFuel + 1) context
      (.prim operation arguments) supply generated next := by
  simp only [ElaboratesFuel]
  exact ⟨scheme, lookup, arity, closed, argumentsElaboration⟩

private def ifElaboration
    (argumentsElaboration : CallElaboratesUsing
      (ElaboratesFuel signature staticFuel) context
      ⟨(conditionalScheme.instantiate supply).1, [], []⟩
      [condition, thenBranch, elseBranch]
      (conditionalScheme.instantiate supply).2 generated next) :
    ElaboratesFuel signature (staticFuel + 1) context
      (.ifE condition thenBranch elseBranch) supply generated next := by
  simpa only [ElaboratesFuel] using argumentsElaboration

mutual

  /-- Static search-plan coverage for one exact elaboration and evaluator
  fuel.  A raw plan is search-free at its matching boundary because
  `RawOriginRequestPlan` has no `matchAll` or `matchFirst` constructor.
  Structural constructors are proof-indexed by the same child elaborations
  used to assemble the parent judgment. -/
  inductive SearchPlanCoverage :
      {signature : FrozenSignature} → {staticFuel : Nat} →
      {context : Context} → {expression : Expr} → {supply : Supply} →
      {generated : Generated} → {next : Supply} →
      ElaboratesFuel signature staticFuel context expression supply generated
        next → Nat → Type where
    | raw
        (elaboration : ElaboratesFuel signature staticFuel context expression
          supply generated next)
        (plan : RawOriginRequestPlan operationalFuel expression outputDemand
          inputDemand) :
        SearchPlanCoverage elaboration operationalFuel
    | app
        {function argument : Expr}
        {generatedFunction generatedArgument : Generated}
        {afterFunction afterArgument : Supply}
        (functionCoverage : SearchPlanCoverage functionElaboration childFuel)
        (argumentCoverage : SearchPlanCoverage argumentElaboration childFuel) :
        SearchPlanCoverage
          (appElaboration functionElaboration argumentElaboration)
          (childFuel + 1)
    | tuple
        (itemsCoverage : SearchItemsCoverage itemsElaboration childFuel) :
        SearchPlanCoverage (tupleElaboration itemsElaboration) (childFuel + 1)
    | letE
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {supply : Supply}
        {value body : Expr} {generatedValue generatedBody : Generated}
        {afterValue next : Supply}
        {closure : PrincipalBlockClosure generatedValue}
        {valueElaboration : ElaboratesFuel signature staticFuel context value
          supply generatedValue afterValue}
        {bodyElaboration : ElaboratesFuel signature staticFuel
          ((context.applyFree closure.substitution).generalize closure.target ::
            context.applyFree closure.substitution)
          body
          (afterValue.join
            (context.applyFree closure.substitution).initialSupply)
          generatedBody next}
        (absorbing : closure.Absorbing)
        (valueCoverage : SearchPlanCoverage valueElaboration childFuel)
        (bodyCoverage : SearchPlanCoverage bodyElaboration childFuel) :
        SearchPlanCoverage
          (letElaboration valueElaboration closure absorbing bodyElaboration)
          (childFuel + 1)
    | ctor
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {supply next : Supply} {generated : Generated}
        {constructor : DataCtor} {arguments : List Expr} {scheme : Scheme}
        {argumentsElaboration : CallElaboratesUsing
          (ElaboratesFuel signature staticFuel) context
          ⟨(scheme.instantiate supply).1, [], []⟩ arguments
          (scheme.instantiate supply).2 generated next}
        (lookup : signature.base.lookupDataConstructor constructor = some scheme)
        (arity : arguments.length = scheme.callArity)
        (closed : scheme.Closed)
        (argumentsCoverage : SearchCallCoverage argumentsElaboration childFuel) :
        SearchPlanCoverage
          (ctorElaboration lookup arity closed argumentsElaboration)
          (childFuel + 1)
    | prim
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {supply next : Supply} {generated : Generated}
        {operation : PrimOp} {arguments : List Expr} {scheme : Scheme}
        {argumentsElaboration : CallElaboratesUsing
          (ElaboratesFuel signature staticFuel) context
          ⟨(scheme.instantiate supply).1, [], []⟩ arguments
          (scheme.instantiate supply).2 generated next}
        (lookup : signature.base.lookupPrimitive operation = some scheme)
        (arity : arguments.length = scheme.callArity)
        (closed : scheme.Closed)
        (argumentsCoverage : SearchCallCoverage argumentsElaboration childFuel) :
        SearchPlanCoverage
          (primElaboration lookup arity closed argumentsElaboration)
          (childFuel + 1)
    | ifE
        (argumentsCoverage : SearchCallCoverage argumentsElaboration childFuel) :
        SearchPlanCoverage (ifElaboration argumentsElaboration) (childFuel + 1)
    | matchAll
        (plan : RawOriginMatchAllPlan elaboration childFuel bindingIndex
          resultIndex sourceTargets targetInput matcherInput bodyInput) :
        SearchPlanCoverage elaboration (childFuel + 1)
    | matchFirst
        (plan : RawOriginMatchFirstPlan elaboration childFuel bindingIndex
          resultIndex sourceTargets targetInput matcherInput fallbackInput) :
        SearchPlanCoverage elaboration (childFuel + 1)

  /-- Coverage aligned with the exact left-to-right tuple elaboration. -/
  inductive SearchItemsCoverage :
      {signature : FrozenSignature} → {staticFuel : Nat} →
      {context : Context} → {expressions : List Expr} → {supply : Supply} →
      {generated : GeneratedItems} → {next : Supply} →
      ItemsElaborateUsing (ElaboratesFuel signature staticFuel) context
        expressions supply generated next → Nat → Type where
    | nil : SearchItemsCoverage ItemsElaborateUsing.nil operationalFuel
    | cons
        (headCoverage : SearchPlanCoverage headElaboration operationalFuel)
        (tailCoverage : SearchItemsCoverage tailElaboration operationalFuel) :
        SearchItemsCoverage
          (ItemsElaborateUsing.cons headElaboration tailElaboration)
          operationalFuel

  /-- Coverage aligned with the exact normalized curried-call spine used by
  constructors, primitives, and `ifE`.  Primitive `map` is covered here as
  the two-child `.prim .map` call rather than by a fixture-specific rule. -/
  inductive SearchCallCoverage :
      {signature : FrozenSignature} → {staticFuel : Nat} →
      {context : Context} → {accumulated : Generated} →
      {arguments : List Expr} → {supply : Supply} →
      {generated : Generated} → {next : Supply} →
      CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
        accumulated arguments supply generated next → Nat → Type where
    | nil : SearchCallCoverage CallElaboratesUsing.nil operationalFuel
    | cons
        (headCoverage : SearchPlanCoverage headElaboration operationalFuel)
        (tailCoverage : SearchCallCoverage tailElaboration operationalFuel) :
        SearchCallCoverage
          (CallElaboratesUsing.cons headElaboration tailElaboration)
          operationalFuel

end

/-- Coverage policy paired with the unchanged principal request producer.
The coverage is required for the same public request and every exact M4
elaboration of the principal expression; no independent syntax tree is an
input. -/
structure TrackedPrincipalOriginRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Type where
  base : PrincipalOriginRequestProducer derivation runtimeContext
  coverage : ∀ (operationalFuel : Nat) (outputDemand : OriginDemand)
      {target : Ty},
    IsInstance principal target →
      OriginDemandApplicable outputDemand target →
        ∀ {staticFuel supply generated next},
          (sourceElaboration : ElaboratesFuel signature staticFuel context
            expression supply generated next) →
          Nonempty (SearchPlanCoverage sourceElaboration operationalFuel)

/-- Tracked runtime certificate data.  Evaluation continues to use `base`;
the second field is retained solely for search-origin completeness. -/
structure TrackedPrincipalOriginCertificateData
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Type where
  base : PrincipalOriginCertificateData derivation runtimeContext
  trackedRequests : TrackedPrincipalOriginRequestProducer derivation
    runtimeContext
  requests_eq : trackedRequests.base = base.requests

def Certificate : RuntimeCertificateFamily :=
  fun derivation runtimeContext =>
    Nonempty (TrackedPrincipalOriginCertificateData derivation runtimeContext)

def DerivationTrackedRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Prop :=
  Nonempty (TrackedPrincipalOriginRequestProducer derivation runtimeContext)

/-- Assemble tracked certificate data for the exact derivation and runtime
context presented by principal state erasure. -/
theorem certificate_of_trackedRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    {runtimeContext : List Ty}
    (signatureReady : RuntimeSignatureReady signature)
    (contextRealization : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (producer : DerivationTrackedRequestProducer derivation runtimeContext) :
    Certificate derivation runtimeContext := by
  rcases producer with ⟨trackedRequests⟩
  exact ⟨{
    base := {
      closureSemantic :=
        TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
          derivation.closure
      contextCompatible := contextRealization
      signatureCompatible := signatureReady.2
      requests := trackedRequests.base }
    trackedRequests := trackedRequests
    requests_eq := rfl }⟩

theorem principalStateErasure_of_trackedRequestProducers
    (produce : ∀ {signature context expression principal}
      (derivation : M4.PrincipalTypingDerivation signature context expression
        principal)
      (runtimeContext : List Ty),
      RuntimeSignatureReady signature →
        scope derivation →
          MonomorphicRuntimeContextRelation derivation runtimeContext →
            DerivationTrackedRequestProducer derivation runtimeContext) :
    PrincipalStateErasure scope Certificate
      MonomorphicRuntimeContextRelation := by
  intro signature context expression principal derivation runtimeContext
    signatureReady inScope contextRealization
  exact certificate_of_trackedRequestProducer signatureReady contextRealization
    (produce derivation runtimeContext signatureReady inScope
      contextRealization)

/-- Forget only search coverage, preserving the exact underlying principal
certificate. -/
def baseCertificate : Certificate derivation runtimeContext →
    M5PrincipalOriginCertificate.Certificate derivation runtimeContext
  | ⟨tracked⟩ => ⟨tracked.base⟩

noncomputable def evaluationInputDemand :
    EvaluationInputDemandFamily Certificate originDemandSafetyRelations := by
  intro signature context expression principal derivation runtimeContext
    certificate operationalFuel outputDemand
  exact M5PrincipalOriginCertificate.evaluationInputDemand
    (baseCertificate certificate) operationalFuel outputDemand

/-- Typed evaluation is inherited from the unchanged base certificate. -/
theorem typedEvaluation :
    TypedEvaluation Certificate originDemandSafetyRelations
      evaluationInputDemand evalFuel := by
  intro signature context expression principal target derivation runtimeContext
    certificate instantiation operationalFuel outputDemand environment
    applicable environmentSafe
  have baseSafe : OriginEnvironmentSafe
      (M5PrincipalOriginCertificate.evaluationInputDemand
        (baseCertificate certificate) operationalFuel outputDemand)
      environment runtimeContext := by
    change OriginEnvironmentSafe
      (M5PrincipalOriginCertificate.evaluationInputDemand
        (baseCertificate certificate) operationalFuel outputDemand)
      environment runtimeContext at environmentSafe
    exact environmentSafe
  exact M5PrincipalOriginCertificate.typedEvaluation
    (baseCertificate certificate) instantiation operationalFuel outputDemand
    environment applicable baseSafe

/-- A raw-plan producer has canonical coverage: its retained plan itself
rules out hidden matching roots. -/
def ofRawPlanProducer
    (producer : PrincipalRawOriginPlanProducer derivation runtimeContext) :
    TrackedPrincipalOriginRequestProducer derivation runtimeContext where
  base := producer.toRequestProducer
  coverage := by
    intro operationalFuel outputDemand target instantiation applicable
      staticFuel supply generated next sourceElaboration
    exact ⟨.raw sourceElaboration
      (producer.plan operationalFuel outputDemand)⟩

end TypePM.Source.M5TrackedPrincipalOriginCertificate
