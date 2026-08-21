import TypePM.Source.M5Paper1ProvenRuntimeScope
import TypePM.Source.M5TracedSearchOrigin

/-!
# Trace completion for the proved search-free Paper-1 scope

This module is the first end-to-end instance of the trace-based completion
schema.  The current `ProvenRuntimeScope` contains only canonical structural
expressions and an arity-zero let of two such expressions.  Their evaluator
trace is empty at every fuel and runtime environment, so no search task can be
hidden behind an empty origin relation.

The result is deliberately scoped to `ProvenRuntimeScope`.  Later matching
constructors must enlarge that same scope and replace the empty annotation
with concrete two-index certificates for their emitted events.
-/

namespace TypePM.Source.M5Paper1ProvenTraceCompletion

open TypePM.Runtime
open M5CompletionArchitecture
open M5PrincipalOriginCertificate
open M5Paper1RuntimeProducer
open M5Paper1SearchFreeStructuralProducer
open M5Paper1ProvenRuntimeScope
open M5TracedSearchOrigin

private theorem traceTraverse_eq_nil_of_mem
    (evaluate : α → FuelResult β)
    (trace : α → List MatchingSearchTraceEvent)
    (items : List α)
    (empty : ∀ item, item ∈ items → trace item = []) :
    traceTraverse evaluate trace items = [] := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [traceTraverse, empty head (by simp)]
      cases evaluate head with
      | timeout | stuck => rfl
      | ok value =>
          simpa using ih (fun item member => empty item (by simp [member]))

private theorem evalFuelTrace_prim_eq_nil
    (notMap : operation ≠ .map)
    (empty : ∀ item, item ∈ arguments →
      evalFuelTrace childFuel environment item = []) :
    evalFuelTrace (childFuel + 1) environment (.prim operation arguments) =
      [] := by
  rw [evalFuelTrace]
  rw [traceTraverse_eq_nil_of_mem _ _ _ empty]
  cases FuelResult.traverse (evalFuel childFuel environment) arguments <;>
    simp [evalPrimitiveTrace, notMap]

private theorem evalFuelTrace_if_eq_nil
    (conditionEmpty : ∀ fuel environment,
      evalFuelTrace fuel environment condition = [])
    (thenEmpty : ∀ fuel environment,
      evalFuelTrace fuel environment thenBranch = [])
    (elseEmpty : ∀ fuel environment,
      evalFuelTrace fuel environment elseBranch = []) :
    ∀ fuel environment,
      evalFuelTrace fuel environment
        (.ifE condition thenBranch elseBranch) = [] := by
  intro fuel environment
  cases fuel with
  | zero => rfl
  | succ childFuel =>
      rw [evalFuelTrace, conditionEmpty childFuel environment]
      cases result : evalFuel childFuel environment condition with
      | timeout | stuck => rfl
      | ok value =>
          cases value with
          | data constructor arguments =>
              cases arguments with
              | nil => simp [thenEmpty, elseEmpty]
              | cons head tail => rfl
          | int | tuple | closure | matcherV | something => rfl

private theorem evalFuelTrace_let_eq_nil
    (valueEmpty : ∀ fuel environment,
      evalFuelTrace fuel environment valueExpression = [])
    (bodyEmpty : ∀ fuel environment,
      evalFuelTrace fuel environment bodyExpression = []) :
    ∀ fuel environment,
      evalFuelTrace fuel environment (.letE valueExpression bodyExpression) =
        [] := by
  intro fuel environment
  cases fuel with
  | zero => rfl
  | succ childFuel =>
      rw [evalFuelTrace, valueEmpty childFuel environment]
      cases evalFuel childFuel environment valueExpression with
      | timeout | stuck => rfl
      | ok value => exact bodyEmpty childFuel (value :: environment)

private theorem pairTree_evalFuelTrace_eq_nil
    (tree : PairTree expression target) :
    ∀ fuel environment,
      evalFuelTrace fuel environment expression = [] := by
  induction tree with
  | lit =>
      intro fuel environment
      cases fuel <;> rfl
  | pair left right leftIH rightIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply traceTraverse_eq_nil_of_mem
          intro item member
          simp at member
          rcases member with rfl | rfl
          · exact leftIH childFuel environment
          · exact rightIH childFuel environment

/-- Canonical structural plans emit no matching-search event. -/
theorem planScope_evalFuelTrace_eq_nil
    (tree : PlanScope expression target) :
    ∀ fuel environment,
      evalFuelTrace fuel environment expression = [] := by
  induction tree with
  | var =>
      intro fuel environment
      cases fuel <;> rfl
  | something =>
      intro fuel environment
      cases fuel <;> rfl
  | pairTree pair => exact pairTree_evalFuelTrace_eq_nil pair
  | tuple left right leftIH rightIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply traceTraverse_eq_nil_of_mem
          intro item member
          simp at member
          rcases member with rfl | rfl
          · exact leftIH childFuel environment
          · exact rightIH childFuel environment
  | boolTrue =>
      intro fuel environment
      cases fuel <;> rfl
  | boolFalse =>
      intro fuel environment
      cases fuel <;> rfl
  | listNil =>
      intro fuel environment
      cases fuel <;> rfl
  | listCons head tail headIH tailIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply traceTraverse_eq_nil_of_mem
          intro item member
          simp at member
          rcases member with rfl | rfl
          · exact headIH childFuel environment
          · exact tailIH childFuel environment
  | add left right leftIH rightIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply evalFuelTrace_prim_eq_nil (by simp)
          intro item member
          simp at member
          rcases member with rfl | rfl
          · exact leftIH childFuel environment
          · exact rightIH childFuel environment
  | append left right leftIH rightIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply evalFuelTrace_prim_eq_nil (by simp)
          intro item member
          simp at member
          rcases member with rfl | rfl
          · exact leftIH childFuel environment
          · exact rightIH childFuel environment
  | member item items itemIH itemsIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply evalFuelTrace_prim_eq_nil (by simp)
          intro expression member
          simp at member
          rcases member with rfl | rfl
          · exact itemIH childFuel environment
          · exact itemsIH childFuel environment
  | deleteFirst item items itemIH itemsIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply evalFuelTrace_prim_eq_nil (by simp)
          intro expression member
          simp at member
          rcases member with rfl | rfl
          · exact itemIH childFuel environment
          · exact itemsIH childFuel environment
  | pairFirst pair pairIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply evalFuelTrace_prim_eq_nil (by simp)
          intro item member
          simp at member
          subst item
          exact pairIH childFuel environment
  | pairSecond pair pairIH =>
      intro fuel environment
      cases fuel with
      | zero => rfl
      | succ childFuel =>
          apply evalFuelTrace_prim_eq_nil (by simp)
          intro item member
          simp at member
          subst item
          exact pairIH childFuel environment
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      exact evalFuelTrace_if_eq_nil conditionIH thenIH elseIH

/-- Every expression admitted by the currently proved scope has an empty
direct evaluator search trace. -/
theorem provenRuntimeScope_evalFuelTrace_eq_nil
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    (scope : ProvenRuntimeScope derivation) :
    ∀ fuel environment,
      evalFuelTrace fuel environment expression = [] := by
  cases scope with
  | canonical derivation tree fixedTarget =>
      exact planScope_evalFuelTrace_eq_nil tree
  | letCanonical derivation valueTree bodyTree bindingApplicable fixedTarget
      contextArityZero =>
      exact evalFuelTrace_let_eq_nil
        (planScope_evalFuelTrace_eq_nil valueTree)
        (planScope_evalFuelTrace_eq_nil bodyTree)

/-- The search-free scope has no event annotation constructor.  Completeness
below is nevertheless non-vacuous because it separately proves that its trace
contains no events. -/
def NoSearchTraceAnnotation : TraceTaskAnnotationFamily
    originDemandSafetyRelations.SearchDemand :=
  fun _derivation _runtimeContext _event _answerTypes _resultDemand => False

theorem noSearchTraceEventCertificateProducer :
    TraceEventCertificateProducer Certificate NoSearchTraceAnnotation := by
  intro signature context expression principal derivation runtimeContext event
    answerTypes resultDemand certificate annotation
  exact False.elim annotation

theorem evaluationTraceOriginComplete :
    EvaluationTraceOriginComplete ProvenRuntimeScope Certificate
      originDemandSafetyRelations evaluationInputDemand
      NoSearchTraceAnnotation := by
  intro signature context expression principal target derivation runtimeContext
    inScope certificate instantiation evaluationFuel outputDemand environment
    applicable environmentSafe event member
  rw [provenRuntimeScope_evalFuelTrace_eq_nil inScope evaluationFuel
    environment] at member
  exact False.elim (by simp at member)

/-- End-to-end 5.6--5.8 schema for the current proved search-free fragment,
including explicit trace-origin completeness. -/
theorem traceCompleteConditionalCompletionSchema :
    TraceCompleteConditionalCompletionSchema ProvenRuntimeScope Certificate
      StableMonomorphicRuntimeContextRelation originDemandSafetyRelations
      evaluationInputDemand NoSearchTraceAnnotation
      traceEventTwoIndexCertificateFamily runTraceEventBoundedDfs := by
  apply traceCompleteConditionalCompletionSchema_of_components
  · exact conditionalCompletionSchema_of_components
      stableMonomorphicRuntimeContext_closed principalStateErasure
      (matchingStateErasure_of_traceEventProducer
        noSearchTraceEventCertificateProducer)
      typedEvaluation typedMatchingSearch_of_traceEventTwoIndex
  · exact evaluationTraceOriginComplete

end TypePM.Source.M5Paper1ProvenTraceCompletion
