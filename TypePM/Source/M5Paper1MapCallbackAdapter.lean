import TypePM.Source.M5Paper1MapDemandProducer
import TypePM.Source.M5Paper1BodyFamilyProducer

/-!
# Paper-1 map callback adapter

This module connects an arity-zero `letE` lambda body to the exact primitive
`map` certificate.  The map children, the lambda observation, and runtime
callback invocation all carry the same predecessor fuel index.
-/

namespace TypePM.Source.M5Paper1MapCallbackAdapter

open TypePM.Runtime
open M5CompletionArchitecture
open M5Paper1SearchFreeStructuralProducer
open M5Paper1ArityZeroLetProducer
open M5Paper1MapDemandProducer
open M5Paper1BodyFamilyProducer
open M5Paper1ClosureRequestProducer

/-- A one-entry monomorphic lambda context satisfies the arity-zero boundary
of the specialized let rule. -/
theorem monoSingleton_contextSchemeArityZero (domain : Ty) :
    M4.ContextSchemeArityZero [Scheme.mono domain] := by
  intro position scheme lookup
  cases position with
  | zero =>
      simp only [List.getElem?_cons_zero] at lookup
      have schemeEq : scheme = Scheme.mono domain :=
        Option.some.inj lookup.symm
      subst scheme
      simp [Scheme.mono]
  | succ position =>
      simp at lookup

/-- Exact input selected by an arity-zero let body at one callback-body fuel.
At positive fuel this is precisely the conjunction produced by
`RawOriginLetArityZeroPlan`. -/
def lambdaLetBodyInput
    (value : RawApplicablePlanFamily valueExpression valueTarget)
    (body : RawApplicablePlanFamily bodyExpression resultType)
    (bodyFuel : Nat) (resultDemand : OriginDemand) :
    OriginEnvironmentDemand :=
  M5Paper1ArityZeroLetProducer.inputDemand value body bodyFuel resultDemand

structure LambdaLetBodyConditions
    (value : RawApplicablePlanFamily valueExpression valueTarget)
    (body : RawApplicablePlanFamily bodyExpression resultType)
    (argumentType : Ty) : Prop where
  bindingApplicable : BindingDemandApplicable value body
  argumentCovers : ∀ bodyFuel argumentDemand resultDemand domain,
    OriginDemandApplicable argumentDemand domain →
      OriginDemand.Le
        (lambdaLetBodyInput value body bodyFuel resultDemand 0)
        argumentDemand

/-- Build the callback body family for `fun argument => let value; body`.
The exact let rule consumes one callback-body fuel and uses its predecessor
for both let children. -/
def lambdaCallBodyFamilyOfArityZeroLet
    (value : RawApplicablePlanFamily valueExpression valueTarget)
    (body : RawApplicablePlanFamily bodyExpression resultType)
    (conditions : LambdaLetBodyConditions
      value body argumentType) :
    LambdaCallBodyFamily signature
      (.letE valueExpression bodyExpression) argumentType resultType where
  bodyInput := fun bodyFuel _argumentDemand resultDemand =>
    lambdaLetBodyInput value body bodyFuel resultDemand
  certificate := by
    intro bodyFuel argumentDemand resultDemand staticFuel supply generated next
      argumentApplicable resultApplicable bodyElaboration
    cases bodyFuel with
    | zero =>
        exact ⟨by
          simpa [lambdaLetBodyInput,
            M5Paper1ArityZeroLetProducer.inputDemand] using
            (M4.ExactRawOriginRequestCertificate.timeout bodyElaboration
              resultDemand)⟩
    | succ letChildFuel =>
        cases staticFuel with
        | zero => exact False.elim bodyElaboration
        | succ letStaticFuel =>
            let bodyInput := body.inputDemand letChildFuel resultDemand
            let valueInput := value.inputDemand letChildFuel (bodyInput 0)
            have bindingApplicable : OriginDemandApplicable (bodyInput 0)
                valueTarget :=
              conditions.bindingApplicable letChildFuel resultDemand
                resultApplicable
            let letPlan : M4.RawOriginLetArityZeroPlan
                [Scheme.mono (Ty.var ⟨supply.ty⟩)] letChildFuel valueExpression
                bodyExpression resultDemand valueInput bodyInput :=
              { contextArityZero :=
                  monoSingleton_contextSchemeArityZero
                    (Ty.var ⟨supply.ty⟩)
                valuePlan := value.plan letChildFuel (bodyInput 0)
                  bindingApplicable
                bodyPlan := body.plan letChildFuel resultDemand
                  resultApplicable }
            simpa [lambdaLetBodyInput,
              M5Paper1ArityZeroLetProducer.inputDemand, bodyInput,
              valueInput] using
              letPlan.exactCertificate bodyElaboration
  argumentCovers := conditions.argumentCovers

/-- Exact positive-fuel `map` certificate whose callback is the lambda family
above.  `childFuel` appears simultaneously in callback construction,
`plainCall`, input evaluation, and `primMap`'s runtime invocation. -/
theorem primMapExactCertificate_of_lambdaCallback
    (callback : LambdaCallBodyFamily signature callbackBody argumentType
      resultType)
    (input : RawListObservationPlanFamily inputExpression argumentType)
    (argumentApplicable : OriginDemandApplicable argumentDemand argumentType)
    (resultApplicable : OriginDemandApplicable resultDemand resultType)
    (elaboration : M4.ElaboratesFuel signature (staticFuel + 1) []
      (.prim .map [.lam callbackBody, inputExpression]) supply generated next) :
    Nonempty (M4.ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.listOf resultDemand)
      (OriginEnvironmentDemand.both
        (lambdaAtomicInput callback
          (.plainCall childFuel argumentDemand resultDemand))
        (input.inputDemand childFuel argumentDemand))) := by
  apply M4.ExactRawOriginRequestCertificate.primMap elaboration childFuel
    argumentDemand resultDemand
    (lambdaAtomicInput callback
      (.plainCall childFuel argumentDemand resultDemand))
    (input.inputDemand childFuel argumentDemand)
  · intro childSupply generatedFunction afterFunction functionElaboration
    exact (lambdaFunctionCertificates callback).call childFuel childFuel
      argumentDemand resultDemand argumentApplicable resultApplicable
      functionElaboration
  · intro childSupply generatedInput afterInput inputElaboration
    exact (input.plan childFuel argumentDemand
      argumentApplicable).exactCertificate inputElaboration

/-- Direct specialization for an arity-zero let callback body. -/
theorem primMapExactCertificate_of_arityZeroLetCallback
    (value : RawApplicablePlanFamily valueExpression valueTarget)
    (body : RawApplicablePlanFamily bodyExpression resultType)
    (conditions : LambdaLetBodyConditions
      value body argumentType)
    (input : RawListObservationPlanFamily inputExpression argumentType)
    (argumentApplicable : OriginDemandApplicable argumentDemand argumentType)
    (resultApplicable : OriginDemandApplicable resultDemand resultType)
    (elaboration : M4.ElaboratesFuel signature (staticFuel + 1) []
      (.prim .map
        [.lam (.letE valueExpression bodyExpression), inputExpression])
      supply generated next) :
    Nonempty (M4.ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.listOf resultDemand)
      (OriginEnvironmentDemand.both
        (lambdaAtomicInput
          (lambdaCallBodyFamilyOfArityZeroLet (signature := signature)
            value body conditions)
          (.plainCall childFuel argumentDemand resultDemand))
        (input.inputDemand childFuel argumentDemand))) :=
  primMapExactCertificate_of_lambdaCallback
    (lambdaCallBodyFamilyOfArityZeroLet (signature := signature)
      value body conditions) input
    argumentApplicable resultApplicable elaboration

end TypePM.Source.M5Paper1MapCallbackAdapter
