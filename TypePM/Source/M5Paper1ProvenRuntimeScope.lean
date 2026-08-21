import TypePM.Source.M5Paper1ArityZeroLetProducer

/-!
# Proven derivation-indexed Paper-1 runtime scope

This scope contains only the two producer fragments already proved below M5:
canonical search-free expressions and arity-zero lets whose two children are
canonical plan families.  It maps to the intended Paper-1 runtime scope and
to recursive M-node freedom, and it supplies principal state erasure.
-/

namespace TypePM.Source.M5Paper1ProvenRuntimeScope

open TypePM.Runtime
open M5CompletionArchitecture
open M5PrincipalOriginCertificate
open M5Paper1RuntimeProducer
open M5Paper1SearchFreeStructuralProducer
open M5Paper1ArityZeroLetProducer

private theorem pairTreeScope
    (tree : PairTree expression target) : Scope expression := by
  induction tree with
  | lit => exact .lit
  | pair left right leftIH rightIH =>
      exact .tuple (.cons leftIH (.cons rightIH .nil))

private theorem canonicalScope
    (tree : PlanScope expression target) : Scope expression := by
  induction tree with
  | var => exact .var
  | pairTree pair => exact pairTreeScope pair
  | tuple left right leftIH rightIH =>
      exact .tuple (.cons leftIH (.cons rightIH .nil))
  | boolTrue => exact .ctor .nil
  | boolFalse => exact .ctor .nil
  | listNil => exact .ctor .nil
  | listCons head tail headIH tailIH =>
      exact .ctor (.cons headIH (.cons tailIH .nil))
  | add left right leftIH rightIH =>
      exact .prim (.cons leftIH (.cons rightIH .nil))
  | append left right leftIH rightIH =>
      exact .prim (.cons leftIH (.cons rightIH .nil))
  | member item items itemIH itemsIH =>
      exact .prim (.cons itemIH (.cons itemsIH .nil))
  | deleteFirst item items itemIH itemsIH =>
      exact .prim (.cons itemIH (.cons itemsIH .nil))
  | pairFirst pair pairIH => exact .prim (.cons pairIH .nil)
  | pairSecond pair pairIH => exact .prim (.cons pairIH .nil)
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      exact .ifE conditionIH thenIH elseIH

private theorem pairTreeMNodeFree
    (tree : PairTree expression target) : expression.MNodeFree := by
  induction tree <;>
    simp_all [Expr.MNodeFree, PatternFunctionExpansion.expandExpr,
      PatternFunctionExpansion.expandExprList]

/-- Canonical structural expressions contain no pattern-function application
or embedded pattern parameter. -/
theorem canonicalMNodeFree
    (tree : PlanScope expression target) : expression.MNodeFree := by
  induction tree with
  | pairTree pair => exact pairTreeMNodeFree pair
  | var | tuple | boolTrue | boolFalse | listNil |
    listCons | add | append | member | deleteFirst | pairFirst | pairSecond |
    ifE =>
      simp_all [Expr.MNodeFree, PatternFunctionExpansion.expandExpr,
        PatternFunctionExpansion.expandExprList]

/-- The proved scope: a canonical search-free derivation, or one arity-zero
let whose children are canonical and whose body demand at position zero is
applicable to the value result.  No child producer is stored independently;
both plan families are computed from the two syntax proofs. -/
inductive ProvenRuntimeScope : M5CompletionArchitecture.RuntimeScope where
  | canonical
      (derivation : M4.PrincipalTypingDerivation signature context expression
        principal)
      (tree : PlanScope expression target)
      (fixedTarget : PrincipalFixedTarget derivation target) :
      ProvenRuntimeScope derivation
  | letCanonical
      (derivation : M4.PrincipalTypingDerivation signature context
        (.letE valueExpression bodyExpression) principal)
      (valueTree : PlanScope valueExpression valueTarget)
      (bodyTree : PlanScope bodyExpression bodyTarget)
      (bindingApplicable : BindingDemandApplicable
        (RawApplicablePlanFamily.ofPlanScope valueTree)
        (RawApplicablePlanFamily.ofPlanScope bodyTree))
      (fixedTarget : PrincipalFixedTarget derivation bodyTarget)
      (contextArityZero : M4.ContextSchemeArityZero context) :
      ProvenRuntimeScope derivation

/-- Every proved constructor belongs to the intended derivation-indexed
Paper-1 runtime scope. -/
theorem ProvenRuntimeScope.toPaper1RuntimeScope
    (scope : ProvenRuntimeScope derivation) :
    M5Paper1RuntimeProducer.RuntimeScope derivation := by
  cases scope with
  | canonical derivation tree fixedTarget =>
      exact .closed (canonicalScope tree) (canonicalMNodeFree tree)
  | letCanonical derivation valueTree bodyTree bindingApplicable fixedTarget
      contextArityZero =>
      exact .letArityZero contextArityZero (canonicalScope valueTree)
        (canonicalScope bodyTree) (by
          have valueFree := canonicalMNodeFree valueTree
          have bodyFree := canonicalMNodeFree bodyTree
          unfold Expr.MNodeFree at valueFree bodyFree ⊢
          simp [PatternFunctionExpansion.expandExpr, valueFree, bodyFree])

/-- Scope projection used by scope-parameterized bounded-DFS completion. -/
theorem ProvenRuntimeScope.mnodeFree
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    (scope : ProvenRuntimeScope derivation) : expression.MNodeFree := by
  cases scope with
  | canonical derivation tree fixedTarget => exact canonicalMNodeFree tree
  | letCanonical derivation valueTree bodyTree bindingApplicable fixedTarget
      contextArityZero =>
      have valueFree := canonicalMNodeFree valueTree
      have bodyFree := canonicalMNodeFree bodyTree
      unfold Expr.MNodeFree at valueFree bodyFree ⊢
      simp [PatternFunctionExpansion.expandExpr, valueFree, bodyFree]

/-- Principal state erasure for the currently proved Paper-1 fragment. -/
theorem principalStateErasure :
    PrincipalStateErasure ProvenRuntimeScope Certificate
      StableMonomorphicRuntimeContextRelation := by
  intro signature context expression principal derivation runtimeContext
    signatureReady scope contextRealization
  rcases contextRealization with ⟨contextCompatible, stable⟩
  apply certificate_of_derivationRequestProducer signatureReady
    contextCompatible
  cases scope with
  | canonical derivation tree fixedTarget =>
      exact M5Paper1SearchFreeStructuralProducer.derivationRequestProducer
        ⟨_, tree, fixedTarget, canonicalMNodeFree tree⟩ runtimeContext
          contextCompatible stable
  | letCanonical derivation valueTree bodyTree bindingApplicable fixedTarget
      contextArityZero =>
      exact M5Paper1ArityZeroLetProducer.derivationRequestProducer derivation
        (RawApplicablePlanFamily.ofPlanScope valueTree)
        (RawApplicablePlanFamily.ofPlanScope bodyTree) bindingApplicable
        fixedTarget runtimeContext contextCompatible stable contextArityZero

end TypePM.Source.M5Paper1ProvenRuntimeScope
