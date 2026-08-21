import TypePM.Runtime.EvalFuelTraced
import TypePM.Source.M5TwoIndexBoundedDfsSearchBridge

/-!
# Non-vacuous trace origin for M5 bounded DFS

The original `MatchingStateErasure` consumes an origin proof but does not say
that every task issued by evaluation has one.  This module adds that missing
boundary.  Runtime trace membership fixes the concrete task and its two equal
operational fuels.  A source-indexed annotation supplies the binding answer
types and logical result demand, and `EvaluationTraceOriginComplete` requires
such an annotation for every event in every certified safe evaluation.

The annotation remains abstract here.  The final Paper-1 induction must both
cover every trace event and turn its annotation into the two-index search
certificate below.  Choosing an empty annotation relation cannot discharge
the completeness field.
-/

namespace TypePM.Source.M5TracedSearchOrigin

open TypePM.Runtime
open M5CompletionArchitecture

/-- Static information attached to one concrete evaluator trace event. -/
abbrev TraceTaskAnnotationFamily (SearchDemand : Type) :=
  {signature : FrozenSignature} → {context : Context} →
    {expression : Expr} → {principal : Ty} →
      M4.PrincipalTypingDerivation signature context expression principal →
        List Ty → MatchingSearchTraceEvent → List Ty → SearchDemand → Prop

/-- Every task in every certified safe evaluation receives a static answer
type list and logical result demand.  This is the non-vacuity condition absent
from the original conditional completion schema. -/
def EvaluationTraceOriginComplete
    (Certificate : RuntimeCertificateFamily)
    (relations : RuntimeSafetyRelations)
    (inputDemand : EvaluationInputDemandFamily Certificate relations)
    (Annotation : TraceTaskAnnotationFamily relations.SearchDemand) : Prop :=
  ∀ {signature context expression principal target}
      {derivation : M4.PrincipalTypingDerivation signature context expression
        principal}
      {runtimeContext : List Ty}
      (certificate : Certificate derivation runtimeContext)
      (_instantiation : IsInstance principal target)
      (evaluationFuel : Nat) (outputDemand : relations.EvaluationDemand)
      (environment : ValueEnvironment),
    relations.demandApplicable outputDemand target →
      relations.environmentSafe
          (inputDemand certificate evaluationFuel outputDemand)
          environment runtimeContext →
        ∀ event,
          event ∈ evalFuelTrace evaluationFuel environment expression →
            ∃ answerTypes resultDemand,
              Annotation derivation runtimeContext event answerTypes
                resultDemand

/-- Trace membership plus its static annotation is the concrete search-origin
relation.  Both callback and DFS fuel are definitionally the fuel recorded at
the evaluator call site. -/
inductive EvaluationTraceSearchOrigin
    (Annotation : TraceTaskAnnotationFamily SearchDemand) :
    MatchingSearchOriginFamily MatchingSearchTraceEvent SearchDemand where
  | issued
      (outerFuel : Nat) (outerEnvironment : ValueEnvironment)
      (member : event ∈ evalFuelTrace outerFuel outerEnvironment expression)
      (annotation : Annotation derivation runtimeContext event answerTypes
        resultDemand) :
      EvaluationTraceSearchOrigin Annotation derivation runtimeContext event
        answerTypes event.fuel event.fuel resultDemand

/-- Completeness constructs the non-vacuous origin witness for every event in
the evaluator trace. -/
theorem EvaluationTraceOriginComplete.origin
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal target : Ty}
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    {runtimeContext : List Ty}
    {event : MatchingSearchTraceEvent}
    (complete : EvaluationTraceOriginComplete Certificate relations inputDemand
      Annotation)
    (certificate : Certificate derivation runtimeContext)
    (instantiation : IsInstance principal target)
    (evaluationFuel : Nat) (outputDemand : relations.EvaluationDemand)
    (environment : ValueEnvironment)
    (applicable : relations.demandApplicable outputDemand target)
    (environmentSafe : relations.environmentSafe
      (inputDemand certificate evaluationFuel outputDemand)
      environment runtimeContext)
    (member : event ∈ evalFuelTrace evaluationFuel environment expression) :
    ∃ answerTypes resultDemand,
      EvaluationTraceSearchOrigin Annotation derivation runtimeContext event
        answerTypes event.fuel event.fuel resultDemand := by
  obtain ⟨answerTypes, resultDemand, annotation⟩ :=
    complete certificate instantiation evaluationFuel outputDemand environment
      applicable environmentSafe event member
  exact ⟨answerTypes, resultDemand,
    .issued evaluationFuel environment member annotation⟩

/-- Execute a raw trace event.  M-node freedom is retained by the certificate,
not fabricated by runtime tracing. -/
def runTraceEventBoundedDfs
    (callbackFuel searchFuel : Nat) (event : MatchingSearchTraceEvent) :
    FuelResult (List (List Value)) :=
  searchPatternFuel (evalFuel callbackFuel) searchFuel event.environment
    event.pattern event.matcher event.target

/-- Two-index certificate for a raw trace event. -/
structure TraceEventTwoIndexCertificate
    (event : MatchingSearchTraceEvent) (answerTypes : List Ty)
    (callbackFuel searchFuel : Nat)
    (resultDemand : OriginEnvironmentDemand) where
  patternMNodeFree : event.pattern.MNodeFree
  certificate : TwoIndexBoundedDfsSearchCertificate
    ⟨event.environment, event.pattern, patternMNodeFree, event.matcher,
      event.target⟩
    answerTypes callbackFuel searchFuel resultDemand

def traceEventTwoIndexCertificateFamily :
    MatchingSearchCertificateFamily MatchingSearchTraceEvent
      originDemandSafetyRelations.SearchDemand :=
  fun event answerTypes callbackFuel searchFuel resultDemand =>
    Nonempty (TraceEventTwoIndexCertificate event answerTypes callbackFuel
      searchFuel resultDemand)

/-- Existing two-index DFS safety applies after the static M-node-free proof
is paired with the raw runtime event. -/
theorem typedMatchingSearch_of_traceEventTwoIndex :
    TypedMatchingSearch originDemandSafetyRelations
      traceEventTwoIndexCertificateFamily runTraceEventBoundedDfs := by
  intro event answerTypes callbackFuel searchFuel resultDemand wrapped
  rcases wrapped with ⟨wrapped⟩
  have safe := typedMatchingSearch_of_twoIndex callbackFuel searchFuel
    resultDemand ⟨wrapped.certificate⟩
  simpa [runTraceEventBoundedDfs, runBoundedDfsMatchingSearch] using safe

/-- Expression-side obligation left for the integrated Paper-1 induction:
one static annotation and the principal certificate construct the two-index
certificate for that traced event. -/
def TraceEventCertificateProducer
    (Certificate : RuntimeCertificateFamily)
    (Annotation : TraceTaskAnnotationFamily
      originDemandSafetyRelations.SearchDemand) : Prop :=
  ∀ {signature context expression principal}
      {derivation : M4.PrincipalTypingDerivation signature context expression
        principal}
      {runtimeContext event answerTypes resultDemand},
    Certificate derivation runtimeContext →
      Annotation derivation runtimeContext event answerTypes resultDemand →
        traceEventTwoIndexCertificateFamily event answerTypes event.fuel
          event.fuel resultDemand

theorem matchingStateErasure_of_traceEventProducer
    (producer : TraceEventCertificateProducer Certificate Annotation) :
    MatchingStateErasure Certificate (EvaluationTraceSearchOrigin Annotation)
      traceEventTwoIndexCertificateFamily := by
  intro signature context expression principal derivation runtimeContext event
    answerTypes callbackFuel searchFuel resultDemand certificate origin
  cases origin with
  | issued outerFuel outerEnvironment member annotation =>
      exact producer certificate annotation

/-- Existing completion fields plus explicit trace-origin completeness. -/
def TraceCompleteConditionalCompletionSchema
    (scope : RuntimeScope)
    (Certificate : RuntimeCertificateFamily)
    (contextRelation : RuntimeContextRelation)
    (relations : RuntimeSafetyRelations)
    (inputDemand : EvaluationInputDemandFamily Certificate relations)
    (Annotation : TraceTaskAnnotationFamily relations.SearchDemand)
    (SearchCertificate : MatchingSearchCertificateFamily
      MatchingSearchTraceEvent relations.SearchDemand)
    (runSearch : Nat → Nat → MatchingSearchTraceEvent →
      FuelResult (List (List Value))) : Prop :=
  ConditionalCompletionSchema scope Certificate contextRelation relations
      inputDemand evalFuel (EvaluationTraceSearchOrigin Annotation)
      SearchCertificate runSearch ∧
    EvaluationTraceOriginComplete Certificate relations inputDemand Annotation

/-- Packaging theorem for the non-vacuous trace-based schema. -/
theorem traceCompleteConditionalCompletionSchema_of_components
    (completion : ConditionalCompletionSchema scope Certificate contextRelation
      relations inputDemand evalFuel (EvaluationTraceSearchOrigin Annotation)
      SearchCertificate runSearch)
    (complete : EvaluationTraceOriginComplete Certificate relations inputDemand
      Annotation) :
    TraceCompleteConditionalCompletionSchema scope Certificate contextRelation
      relations inputDemand Annotation SearchCertificate runSearch :=
  ⟨completion, complete⟩

/-- M-node-free bounded-DFS specialization with non-vacuous evaluator-trace
coverage built into the public statement. -/
def TraceCompleteMNodeFreeBoundedDfsCompletionSchema
    (Certificate : RuntimeCertificateFamily)
    (inputDemand : EvaluationInputDemandFamily Certificate
      originDemandSafetyRelations)
    (Annotation : TraceTaskAnnotationFamily
      originDemandSafetyRelations.SearchDemand) : Prop :=
  TraceCompleteConditionalCompletionSchema MNodeFreeRuntimeScope Certificate
    MonomorphicRuntimeContextRelation originDemandSafetyRelations inputDemand
    Annotation traceEventTwoIndexCertificateFamily runTraceEventBoundedDfs

/-- Final packaging boundary for the traced M5 lane.  Unlike the earlier
schema package, it requires a proof that every event emitted by every safe
certified evaluation receives an origin annotation. -/
theorem traceCompleteMNodeFreeBoundedDfsCompletionSchema_of_components
    (principalErasure : PrincipalStateErasure MNodeFreeRuntimeScope Certificate
      MonomorphicRuntimeContextRelation)
    (typedEvaluation : TypedEvaluation Certificate
      originDemandSafetyRelations inputDemand evalFuel)
    (producer : TraceEventCertificateProducer Certificate Annotation)
    (complete : EvaluationTraceOriginComplete Certificate
      originDemandSafetyRelations inputDemand Annotation) :
    TraceCompleteMNodeFreeBoundedDfsCompletionSchema Certificate inputDemand
      Annotation := by
  constructor
  · exact conditionalCompletionSchema_of_components
      monomorphicRuntimeContext_closed principalErasure
      (matchingStateErasure_of_traceEventProducer
        (Certificate := Certificate) (Annotation := Annotation) producer)
      typedEvaluation typedMatchingSearch_of_traceEventTwoIndex
  · exact complete

end TypePM.Source.M5TracedSearchOrigin
