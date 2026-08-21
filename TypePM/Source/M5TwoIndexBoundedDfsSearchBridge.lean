import TypePM.Source.M5CompletionArchitecture
import TypePM.Source.M4TwoIndexCanonicalAtomReducerBridge
import TypePM.Source.M4TwoIndexMatchAllInitialProducer

/-!
# Two-index bounded DFS bridge for the M5 completion schema

This module instantiates the search-side interfaces of
`MNodeFreeBoundedDfsCompletionSchema` from the general two-index matching
theorem.  A search certificate retains an initial-state derivation and a
transport from its residual fuel relation to the structural answer demand
selected by the M5 schema.

The origin relation is kept separate from the certificate producer.  Thus a
principal runtime certificate and evidence that evaluation issued one task
must jointly construct the two-index witness; an unrelated search witness
cannot be supplied directly as an origin.
-/

namespace TypePM.Source.M5CompletionArchitecture

open TypePM.Runtime

/-- A numeric residual index covers one structural answer demand when every
fuel-safe answer at that index satisfies the requested position-sensitive
demand. -/
def OriginAnswerDemandCoveredByFuel
    (residual : Nat) (demand : OriginEnvironmentDemand)
    (answerTypes : List Ty) : Prop :=
  ∀ {answer}, FuelEnvironmentSafe residual answer answerTypes →
    OriginEnvironmentSafe demand answer answerTypes

/-- Search certificate consumed by the generic two-index DFS theorem.  The
callback fuel and DFS fuel remain independent; `residual` is existential and
is retained only for the logical relation on completed answers. -/
structure TwoIndexBoundedDfsSearchCertificate
    (task : BoundedDfsMatchingSearchTask) (answerTypes : List Ty)
    (callbackFuel searchFuel : Nat)
    (resultDemand : OriginEnvironmentDemand) where
  residual : Nat
  initialTyped : TwoIndexMatchingStateTyping FuelEnvironmentSafe
    FuelEnvironmentSafe (evaluationAtomReducer (evalFuel callbackFuel))
    searchFuel residual
    ⟨[⟨task.pattern, task.matcher, task.target⟩], task.environment, []⟩
    answerTypes
  demandCovered : OriginAnswerDemandCoveredByFuel residual resultDemand
    answerTypes

/-- `MatchingSearchCertificateFamily` specialization used by the MNode-free
bounded DFS schema. -/
def twoIndexBoundedDfsSearchCertificateFamily :
    MatchingSearchCertificateFamily BoundedDfsMatchingSearchTask
      originDemandSafetyRelations.SearchDemand :=
  fun task answerTypes callbackFuel searchFuel resultDemand =>
    Nonempty (TwoIndexBoundedDfsSearchCertificate task answerTypes callbackFuel
      searchFuel resultDemand)

namespace TwoIndexBoundedDfsSearchCertificate

/-- An evaluated initial-state producer, including the generalized M4
producer, supplies the initial component of the schema search certificate.
No completed-search equation is used. -/
theorem ofEvaluatedInitialState
    {residual : Nat}
    (patternMNodeFree : pattern.MNodeFree)
    (initialTyped : EvaluatedTwoIndexInitialStateTyping FuelEnvironmentSafe
      FuelEnvironmentSafe searchFuel residual environment targetExpression
      matcherExpression pattern answerTypes)
    (targetSuccess :
      evalFuel searchFuel environment targetExpression = .ok targetValue)
    (matcherSuccess :
      evalFuel searchFuel environment matcherExpression = .ok matcherValue)
    (demandCovered : OriginAnswerDemandCoveredByFuel residual resultDemand
      answerTypes) :
    twoIndexBoundedDfsSearchCertificateFamily
      ⟨environment, pattern, patternMNodeFree, matcherValue, targetValue⟩
      answerTypes searchFuel searchFuel resultDemand :=
  ⟨⟨residual,
    initialTyped targetValue matcherValue targetSuccess matcherSuccess,
    demandCovered⟩⟩

end TwoIndexBoundedDfsSearchCertificate

/-- G10: every two-index certificate yields the structural search-result
invariant required by the M5 schema. -/
theorem typedMatchingSearch_of_twoIndex :
    TypedMatchingSearch originDemandSafetyRelations
      twoIndexBoundedDfsSearchCertificateFamily
      runBoundedDfsMatchingSearch := by
  intro task answerTypes callbackFuel searchFuel resultDemand certificate
  rcases certificate with ⟨certificate⟩
  cases certificate with
  | mk residual initialTyped demandCovered =>
      have fuelSafe := searchPatternFuel_twoIndexSafe
        IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
        IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
        initialTyped
      change OriginMatchingSearchResultSafe resultDemand answerTypes
        (searchPatternFuel (evalFuel callbackFuel) searchFuel task.environment
          task.pattern task.matcher task.target)
      rcases fuelSafe with timeout | ⟨answers, success, answersSafe⟩
      · exact .inl timeout
      · exact .inr ⟨answers, success, by
          intro answer answerMember
          exact demandCovered (answersSafe answer answerMember)⟩

/-- Evaluation-specific evidence that one bounded DFS task was actually
issued by the certified source state.  Concrete evaluator producers choose
this relation; the wrapper itself carries no independent search certificate. -/
inductive TwoIndexBoundedDfsSearchOrigin
    (Issued : MatchingSearchOriginFamily BoundedDfsMatchingSearchTask
      originDemandSafetyRelations.SearchDemand) :
    MatchingSearchOriginFamily BoundedDfsMatchingSearchTask
      originDemandSafetyRelations.SearchDemand where
  | issued
      (evidence : Issued derivation runtimeContext task answerTypes
        callbackFuel searchFuel resultDemand) :
      TwoIndexBoundedDfsSearchOrigin Issued derivation runtimeContext task
        answerTypes callbackFuel searchFuel resultDemand

/-- Contract for the expression-side producer at the search boundary.  It
must use both the exact principal runtime certificate and the concrete issued
task evidence to construct the two-index initial state. -/
def TwoIndexBoundedDfsSearchOriginProducer
    (Certificate : RuntimeCertificateFamily)
    (Issued : MatchingSearchOriginFamily BoundedDfsMatchingSearchTask
      originDemandSafetyRelations.SearchDemand) : Prop :=
  ∀ {signature context expression principal}
      {derivation : M4.PrincipalTypingDerivation signature context expression
        principal}
      {runtimeContext task answerTypes callbackFuel searchFuel resultDemand},
    Certificate derivation runtimeContext →
      Issued derivation runtimeContext task answerTypes callbackFuel searchFuel
        resultDemand →
      twoIndexBoundedDfsSearchCertificateFamily task answerTypes callbackFuel
        searchFuel resultDemand

/-- G8--G9: an honest task-origin producer discharges
`MatchingStateErasure`. -/
theorem matchingStateErasure_of_twoIndexOriginProducer
    (producer : TwoIndexBoundedDfsSearchOriginProducer Certificate Issued) :
    MatchingStateErasure Certificate (TwoIndexBoundedDfsSearchOrigin Issued)
      twoIndexBoundedDfsSearchCertificateFamily := by
  intro signature context expression principal derivation runtimeContext task
    answerTypes callbackFuel searchFuel resultDemand certificate origin
  cases origin with
  | issued evidence => exact producer certificate evidence

/-- G8--G10 packaging: once expression-side principal erasure, typed
evaluation, and the issued-task producer are available, the MNode-free
bounded-DFS completion schema follows.  The search proof is the generic
two-index theorem above; no fixture or completed-search equality is a
premise. -/
theorem mNodeFreeBoundedDfsCompletionSchema_of_twoIndexComponents
    (principalErasure : PrincipalStateErasure MNodeFreeRuntimeScope Certificate
      MonomorphicRuntimeContextRelation)
    (typedEvaluation : TypedEvaluation Certificate
      originDemandSafetyRelations inputDemand evalFuel)
    (originProducer :
      TwoIndexBoundedDfsSearchOriginProducer Certificate Issued) :
    MNodeFreeBoundedDfsCompletionSchema Certificate inputDemand
      (TwoIndexBoundedDfsSearchOrigin Issued)
      twoIndexBoundedDfsSearchCertificateFamily := by
  apply conditionalCompletionSchema_of_components
  · exact monomorphicRuntimeContext_closed
  · exact principalErasure
  · exact matchingStateErasure_of_twoIndexOriginProducer
      (Certificate := Certificate) (Issued := Issued) originProducer
  · exact typedEvaluation
  · exact typedMatchingSearch_of_twoIndex

end TypePM.Source.M5CompletionArchitecture
