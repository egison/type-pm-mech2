import TypePM.Source.FullM4Completion
import TypePM.ValueIndexedMatchingSearchSafety
import TypePM.Runtime.PatternFunctionNodeEvaluation

/-!
# M5 completion architecture

This module fixes the proof boundary for results 5.6--5.8 without pretending
that the current certified fragments already cover all of M5.  Existing
theorems for `RuntimeSupported` expressions remain valid, but they use the
traditional structural environment and result typing relations in this
repository.

Two distinctions are essential here.

First, the runtime certificate is indexed by one concrete principal M4
derivation, not just by its result type.  This retains the solved substitution
needed to relate an open source context to runtime values.  Second, the
environment and result invariants are packaged together and left explicit.
Simply replacing `EnvironmentTyping` by `FuelEnvironmentSafe` in the current
common-fuel theorem would still leave its successful result in the
traditional structural `ValueTyping` relation, and a same-index `FuelResultSafe`
conclusion has not yet been proved for arbitrary higher-order evaluation.

The architecture is parameterized by an evaluator because ordinary
`evalFuel` and the checked pattern-function-node evaluator are different
semantic lanes.  `MNodeFreeBoundedDfsCompletionSchema` below fixes the
expression lane to MNode-free expressions and `evalFuel`, and fixes its search
lane to the current bounded depth-first `searchPatternFuel` callback.  This is
the `match-all-dfs` lane, not the fair lazy `match-all` semantics of the APLAS
2018 reduction tree.  A
checked pattern-function completion boundary must additionally retain frozen
definitions and their agreement proof; it is intentionally not claimed here.
-/

namespace TypePM.Source.M5CompletionArchitecture

open TypePM.Runtime

/-- A proof-bearing runtime certificate indexed by the exact principal
derivation whose solved substitution it must preserve. -/
abbrev RuntimeCertificateFamily :=
  {signature : FrozenSignature} →
    {context : Context} →
      {expression : Expr} →
        {principal : Ty} →
          M4.PrincipalTypingDerivation signature context expression principal →
            List Ty → Prop

/-- Relation between one exact principal derivation and the newest-first
runtime context used to evaluate its source expression. -/
abbrev RuntimeContextRelation :=
  {signature : FrozenSignature} →
    {context : Context} →
      {expression : Expr} →
        {principal : Ty} →
          M4.PrincipalTypingDerivation signature context expression principal →
            List Ty → Prop

/-- Current concrete context relation for monomorphic source contexts.  It is
useful for closed expressions, but does not by itself represent a polymorphic
`let` body context. -/
def MonomorphicRuntimeContextRelation
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Prop :=
  MonomorphicContextCompatible context runtimeContext
    derivation.closure.substitution

/-- Static assumptions needed by the ordinary runtime implementation.  The
frozen signature must be well formed, and its ordinary constructor/primitive
base must agree with the meanings implemented by the evaluator. -/
def RuntimeSignatureReady (signature : FrozenSignature) : Prop :=
  signature.WellFormed ∧ SignatureCompatible signature.base

/-- Environment and successful-result invariants used by one preservation
proof.  Keeping them in one package prevents the environment side from being
generalized while silently retaining an incompatible result relation.

Evaluator fuel, search fuel, and the logical result index are deliberately
separate.  The two index functions compute how much input safety is required
to obtain a requested logical result index.  This prevents evaluator fuel
from being silently identified with the strictly decreasing index used by
higher-order application. -/
structure RuntimeSafetyRelations where
  environmentSafe : Nat → ValueEnvironment → List Ty → Prop
  resultSafe : Nat → Ty → FuelResult Value → Prop
  searchResultSafe : Nat → List Ty →
    FuelResult (List (List Value)) → Prop
  evaluationInputIndex : Nat → Nat → Nat
  searchInputIndex : Nat → Nat → Nat → Nat
  emptyEnvironment : ∀ index, environmentSafe index [] []
  resultNotStuck : ∀ {index target result},
    resultSafe index target result → result.NotStuck
  searchResultNotStuck : ∀ {index targets result},
    searchResultSafe index targets result → result.NotStuck

/-- Pointwise fuel-indexed safety of every binding environment returned by a
completed matching search. -/
abbrev FuelMatchingAnswersSafe (index : Nat) (answers : List (List Value))
    (answerTypes : List Ty) : Prop :=
  MatchingAnswersSafeWith (FuelEnvironmentSafe index) answers answerTypes

/-- Timeout or a completed list of pointwise fuel-indexed matching answers. -/
abbrev FuelMatchingSearchResultSafe (index : Nat) (answerTypes : List Ty)
    (result : FuelResult (List (List Value))) : Prop :=
  MatchingSearchResultSafeWith (FuelEnvironmentSafe index) answerTypes result

theorem FuelMatchingSearchResultSafe.notStuck
    (safe : FuelMatchingSearchResultSafe index answerTypes result) :
    result.NotStuck :=
  MatchingSearchResultSafeWith.notStuck safe

/-- Existing fuel-indexed value/environment relations form one coherent
safety package.  This declaration does not claim the full M4 preservation
property for that package. -/
def fuelIndexedSafetyRelations : RuntimeSafetyRelations where
  environmentSafe := FuelEnvironmentSafe
  resultSafe := FuelResultSafe
  searchResultSafe := FuelMatchingSearchResultSafe
  evaluationInputIndex := fun evaluationFuel resultIndex =>
    evaluationFuel + resultIndex
  searchInputIndex := fun callbackFuel searchFuel resultIndex =>
    callbackFuel + searchFuel + resultIndex
  emptyEnvironment := FuelEnvironmentSafe.nil
  resultNotStuck := FuelResultSafe.notStuck
  searchResultNotStuck := FuelMatchingSearchResultSafe.notStuck

/-- **Target statement 5.6 (state erasure).**  An exact principal M4
derivation in the selected source fragment and an explicit context
realization construct the chosen proof-bearing runtime certificate. -/
def PrincipalStateErasure
    (scope : Expr → Prop)
    (Certificate : RuntimeCertificateFamily)
    (contextRelation : RuntimeContextRelation) : Prop :=
  ∀ {signature context expression principal}
      (derivation : M4.PrincipalTypingDerivation signature context expression
        principal)
      (runtimeContext : List Ty),
    RuntimeSignatureReady signature →
      scope expression →
        contextRelation derivation runtimeContext →
          Certificate derivation runtimeContext

/-- **Target statement 5.7 (typed evaluation).**  A runtime
certificate transports the environment side of one safety package to its
matching result side.  `evaluate` may be `evalFuel` or another checked
evaluator; the statement does not hard-code the structural `TypedResult`. -/
def TypedEvaluation
    (Certificate : RuntimeCertificateFamily)
    (relations : RuntimeSafetyRelations)
    (evaluate : Nat → ValueEnvironment → Expr → FuelResult Value) : Prop :=
  ∀ {signature context expression principal target}
      {derivation : M4.PrincipalTypingDerivation signature context expression
        principal}
      {runtimeContext : List Ty}
      (_certificate : Certificate derivation runtimeContext)
      (_instantiation : IsInstance principal target)
      (evaluationFuel resultIndex : Nat) (environment : ValueEnvironment),
    relations.environmentSafe
        (relations.evaluationInputIndex evaluationFuel resultIndex)
        environment runtimeContext →
      relations.resultSafe resultIndex target
        (evaluate evaluationFuel environment expression)

/-- A proof-bearing certificate for one concrete matching-search task and its
answer binding types.  The task type may retain patterns, matcher values,
runtime environments, and callback-specific evidence. -/
abbrev MatchingSearchCertificateFamily (SearchTask : Type) :=
  SearchTask → List Ty → Nat → Prop

/-- An actual matching-search obligation originating in one principal source
derivation and its realized runtime context.  A concrete instantiation must
relate precisely the tasks issued by its evaluator; this relation is not a
free-standing source of unrelated search fixtures. -/
abbrev MatchingSearchOriginFamily (SearchTask : Type) :=
  {signature : FrozenSignature} →
    {context : Context} →
      {expression : Expr} →
        {principal : Ty} →
          M4.PrincipalTypingDerivation signature context expression principal →
            List Ty → SearchTask → List Ty → Nat → Prop

/-- **Target statement 5.6 (matching-state erasure).**  A proof-bearing
runtime certificate and evidence that a concrete search task originates in
that certified state generate the certificate consumed by bounded search.
This is the missing link between principal state erasure and the search
preservation theorem: `SearchCertificate` is not admitted as an independent
premise for an unrelated task. -/
def MatchingStateErasure
    (Certificate : RuntimeCertificateFamily)
    {SearchTask : Type}
    (SearchOrigin : MatchingSearchOriginFamily SearchTask)
    (SearchCertificate : MatchingSearchCertificateFamily SearchTask) : Prop :=
  ∀ {signature context expression principal}
      {derivation : M4.PrincipalTypingDerivation signature context expression
        principal}
      {runtimeContext : List Ty} {task : SearchTask} {answerTypes : List Ty}
      {inputIndex : Nat},
    Certificate derivation runtimeContext →
      SearchOrigin derivation runtimeContext task answerTypes inputIndex →
        SearchCertificate task answerTypes inputIndex

/-- **Target statement 5.7 (matching and finite search).**  A certified search
task returns either timeout or answers satisfying the search component of the
same safety package used by expression evaluation. -/
def TypedMatchingSearch
    {SearchTask : Type}
    (SearchCertificate : MatchingSearchCertificateFamily SearchTask)
    (relations : RuntimeSafetyRelations)
    (runSearch : Nat → Nat → SearchTask →
      FuelResult (List (List Value))) : Prop :=
  ∀ {task answerTypes},
    ∀ callbackFuel searchFuel resultIndex,
      SearchCertificate task answerTypes
          (relations.searchInputIndex callbackFuel searchFuel resultIndex) →
        relations.searchResultSafe resultIndex answerTypes
          (runSearch callbackFuel searchFuel task)

/-- The three search-side boundaries compose: principal erasure constructs
the runtime certificate, matching-state erasure turns an originating search
obligation into a bounded search certificate, and typed search establishes
the result invariant. -/
theorem matchingSearchSafe_of_erasure
    {scope : Expr → Prop}
    {Certificate : RuntimeCertificateFamily}
    {contextRelation : RuntimeContextRelation}
    {relations : RuntimeSafetyRelations}
    {SearchTask : Type}
    {SearchOrigin : MatchingSearchOriginFamily SearchTask}
    {SearchCertificate : MatchingSearchCertificateFamily SearchTask}
    {runSearch : Nat → Nat → SearchTask →
      FuelResult (List (List Value))}
    (principalErasure :
      PrincipalStateErasure scope Certificate contextRelation)
    (matchingErasure :
      MatchingStateErasure Certificate SearchOrigin SearchCertificate)
    (typedSearch :
      TypedMatchingSearch SearchCertificate relations runSearch)
    {signature context expression principal}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty)
    (signatureReady : RuntimeSignatureReady signature)
    (inScope : scope expression)
    (contextRealization : contextRelation derivation runtimeContext)
    {task : SearchTask} {answerTypes : List Ty}
    (callbackFuel searchFuel resultIndex : Nat)
    (origin : SearchOrigin derivation runtimeContext task answerTypes
      (relations.searchInputIndex callbackFuel searchFuel resultIndex)) :
    relations.searchResultSafe resultIndex answerTypes
      (runSearch callbackFuel searchFuel task) := by
  have runtimeCertificate : Certificate derivation runtimeContext :=
    principalErasure derivation runtimeContext signatureReady inScope
      contextRealization
  have searchCertificate : SearchCertificate task answerTypes
      (relations.searchInputIndex callbackFuel searchFuel resultIndex) :=
    matchingErasure runtimeCertificate origin
  exact typedSearch callbackFuel searchFuel resultIndex searchCertificate

/-- The context relation has a canonical realization for every closed
principal derivation.  This is the only context fact needed to derive 5.8. -/
def ClosedContextRealizable (contextRelation : RuntimeContextRelation) : Prop :=
  ∀ {signature expression principal}
      (derivation : M4.PrincipalTypingDerivation signature [] expression
        principal),
    contextRelation derivation []

theorem monomorphicRuntimeContext_closed :
    ClosedContextRealizable MonomorphicRuntimeContextRelation := by
  intro signature expression principal derivation
  change MonomorphicContextCompatible [] [] derivation.closure.substitution
  exact .nil

/-- **Target statement 5.8 (closed no-stuck).**  Every closed expression in
the selected source fragment that has an M4 typing avoids `stuck` for every
fuel amount.  Timeout remains an ordinary bounded-evaluation result. -/
def ClosedNoStuck
    (scope : Expr → Prop)
    (evaluate : Nat → ValueEnvironment → Expr → FuelResult Value) : Prop :=
  ∀ {signature expression target},
    RuntimeSignatureReady signature →
      scope expression →
        M4.Typing signature [] expression target →
          ∀ fuel, (evaluate fuel [] expression).NotStuck

/-- State erasure and typed evaluation imply the closed no-stuck statement.
An arbitrary M4 typing contains a principal witness and an instance proof for
the requested result type.  Typed evaluation retains that proof and certifies
the result at the requested type, rather than silently replacing it by the
principal representative.
-/
theorem closedNoStuck_of_principalStateErasure_and_typedEvaluation
    {scope : Expr → Prop}
    {Certificate : RuntimeCertificateFamily}
    {contextRelation : RuntimeContextRelation}
    {relations : RuntimeSafetyRelations}
    {evaluate : Nat → ValueEnvironment → Expr → FuelResult Value}
    (closedContext : ClosedContextRealizable contextRelation)
    (stateErasure : PrincipalStateErasure scope Certificate contextRelation)
    (typedEvaluation : TypedEvaluation Certificate relations evaluate) :
    ClosedNoStuck scope evaluate := by
  unfold ClosedNoStuck
  intro signature expression target signatureReady inScope sourceTyping fuel
  rcases sourceTyping with ⟨principal, principalTyping, instantiation⟩
  let selectedDerivation := Classical.choice principalTyping
  have contextRealization : contextRelation selectedDerivation [] :=
    closedContext selectedDerivation
  have certificate : Certificate selectedDerivation [] :=
    stateErasure selectedDerivation [] signatureReady inScope
      contextRealization
  exact relations.resultNotStuck
    (typedEvaluation certificate instantiation fuel 0 []
      (relations.emptyEnvironment
        (relations.evaluationInputIndex fuel 0)))

/-- Machine-checked architecture boundary for one evaluator lane.  The final
no-stuck conjunct is retained explicitly because it is the user-facing result,
although it follows from the preceding fields and closed-context realization.
-/
def ConditionalCompletionSchema
    (scope : Expr → Prop)
    (Certificate : RuntimeCertificateFamily)
    (contextRelation : RuntimeContextRelation)
    (relations : RuntimeSafetyRelations)
    (evaluate : Nat → ValueEnvironment → Expr → FuelResult Value)
    {SearchTask : Type}
    (SearchOrigin : MatchingSearchOriginFamily SearchTask)
    (SearchCertificate : MatchingSearchCertificateFamily SearchTask)
    (runSearch : Nat → Nat → SearchTask →
      FuelResult (List (List Value))) : Prop :=
  ClosedContextRealizable contextRelation ∧
    PrincipalStateErasure scope Certificate contextRelation ∧
      MatchingStateErasure Certificate SearchOrigin SearchCertificate ∧
        TypedEvaluation Certificate relations evaluate ∧
          TypedMatchingSearch SearchCertificate relations runSearch ∧
            ClosedNoStuck scope evaluate

/-- Packaging theorem for a future concrete certificate family. -/
theorem conditionalCompletionSchema_of_components
    {scope : Expr → Prop}
    {Certificate : RuntimeCertificateFamily}
    {contextRelation : RuntimeContextRelation}
    {relations : RuntimeSafetyRelations}
    {evaluate : Nat → ValueEnvironment → Expr → FuelResult Value}
    {SearchTask : Type}
    {SearchOrigin : MatchingSearchOriginFamily SearchTask}
    {SearchCertificate : MatchingSearchCertificateFamily SearchTask}
    {runSearch : Nat → Nat → SearchTask → FuelResult (List (List Value))}
    (closedContext : ClosedContextRealizable contextRelation)
    (stateErasure : PrincipalStateErasure scope Certificate contextRelation)
    (matchingErasure :
      MatchingStateErasure Certificate SearchOrigin SearchCertificate)
    (typedEvaluation : TypedEvaluation Certificate relations evaluate)
    (typedSearch : TypedMatchingSearch SearchCertificate relations runSearch) :
    ConditionalCompletionSchema scope Certificate contextRelation relations
      evaluate SearchOrigin SearchCertificate runSearch :=
  ⟨closedContext, stateErasure, matchingErasure, typedEvaluation, typedSearch,
    closedNoStuck_of_principalStateErasure_and_typedEvaluation closedContext
      stateErasure typedEvaluation⟩

/-- Runtime input of one current bounded depth-first `searchPatternFuel`
call. -/
structure BoundedDfsMatchingSearchTask where
  environment : ValueEnvironment
  pattern : Pattern
  patternMNodeFree : pattern.MNodeFree
  matcher : Value
  target : Value

/-- The bounded DFS lane uses `evalFuel` at the independently selected
callback fuel and the generic depth-first search bound. -/
def runBoundedDfsMatchingSearch
    (callbackFuel searchFuel : Nat) (task : BoundedDfsMatchingSearchTask) :
    FuelResult (List (List Value)) :=
  searchPatternFuel (evalFuel callbackFuel) searchFuel task.environment
    task.pattern task.matcher task.target

/-- MNode-free bounded-DFS specialization of the architecture.  Its
expression scope is exactly the recursively MNode-free fragment evaluated by
`evalFuel`.  Its search lane is the current `searchPatternFuel` callback above;
`SearchOrigin` must identify the concrete DFS tasks issued by that evaluation.
This schema proves finite bounded-search safety only.  A fair `matchAll` needs
the separate binary-reduction-tree prefix semantics and cannot be obtained by
relabeling this finite-list result.  MNode-bearing patterns instead require the checked
pattern-function evaluator together with frozen definitions and agreement
evidence, and are not hidden in this schema.  The certificate families remain
parameters until their full M4 instances are proved. -/
def MNodeFreeBoundedDfsCompletionSchema
    (Certificate : RuntimeCertificateFamily)
    (SearchOrigin : MatchingSearchOriginFamily BoundedDfsMatchingSearchTask)
    (SearchCertificate :
      MatchingSearchCertificateFamily BoundedDfsMatchingSearchTask) : Prop :=
  ConditionalCompletionSchema Expr.MNodeFree Certificate
    MonomorphicRuntimeContextRelation fuelIndexedSafetyRelations evalFuel
      SearchOrigin SearchCertificate runBoundedDfsMatchingSearch

end TypePM.Source.M5CompletionArchitecture
