import TypePM.Source.M4RawOriginRequestCertificate
import TypePM.FuelUserMatcherGeneralSafety

/-!
# Raw M4 certificates as embedded evaluator certificates

This module hides one solved raw M4 elaboration, its structural origin-request
certificate, and its monomorphic source/runtime context alignment behind the
`FuelEmbeddedExpressionCertificateFamily` interface consumed by matcher
capture and arm evaluation.  Binding and outer-environment types are combined
in their exact runtime order.
-/

namespace TypePM.Runtime

namespace MonomorphicContextCompatible

/-- Source and runtime contexts aligned pointwise also have equal lengths. -/
theorem source_runtime_length
    (compatible : MonomorphicContextCompatible sourceContext runtimeContext
      solution) :
    sourceContext.length = runtimeContext.length := by
  induction compatible with
  | nil => rfl
  | cons tail induction => simp [induction]

end MonomorphicContextCompatible

/-- General transport from a monomorphic runtime context observation to the
scheme-indexed observation expected by a raw M4 request certificate. -/
theorem OriginEnvironmentSafe.toSchemeOrigin
    (compatible : MonomorphicContextCompatible sourceContext runtimeContext
      solution)
    (safe : OriginEnvironmentSafe demand values runtimeContext) :
    SchemeOriginEnvironmentSafe demand solution values sourceContext := by
  refine ⟨?_, ?_⟩
  · calc
      values.length = runtimeContext.length := safe.1
      _ = sourceContext.length := compatible.source_runtime_length.symm
  · intro position scheme value schemeFound valueFound
    obtain ⟨sourceTarget, schemeEq, runtimeFound⟩ :=
      compatible.lookup schemeFound
    subst scheme
    have valueSafe := safe.2 position (sourceTarget.apply solution) value
      runtimeFound valueFound
    intro occurrenceSupply
    simpa [Source.Scheme.instantiate_mono] using valueSafe

end TypePM.Runtime

namespace TypePM.Source.M4

open TypePM.Runtime

/-- Certificate-family instance obtained by existentially hiding all raw M4
indices.  The visible target and input demand are tied by exact equalities to
the solved generated block and selected raw request certificate. -/
def M4FuelEmbeddedCertificate
    (signature : FrozenSignature) : FuelEmbeddedExpressionCertificateFamily :=
  fun operationalFuel bindingTypes environmentTypes expression target
      outputDemand inputDemand =>
    ∃ staticFuel sourceContext supply generated next solution,
      ∃ elaboration : ElaboratesFuel signature staticFuel sourceContext
        expression supply generated next,
        generated.SemanticSolution solution ∧
          MonomorphicContextCompatible sourceContext
            (bindingTypes ++ environmentTypes) solution ∧
          generated.target.apply solution = target ∧
          ∃ raw : RawOriginRequestCertificate elaboration operationalFuel
            outputDemand,
            raw.inputDemand = inputDemand

/-- Package one concrete solved raw certificate into the embedded family. -/
theorem M4FuelEmbeddedCertificate.ofRaw
    (elaboration : ElaboratesFuel signature staticFuel sourceContext
      expression supply generated next)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible sourceContext
      (bindingTypes ++ environmentTypes) solution)
    (raw : RawOriginRequestCertificate elaboration operationalFuel
      outputDemand) :
    M4FuelEmbeddedCertificate signature operationalFuel bindingTypes
      environmentTypes expression (generated.target.apply solution)
      outputDemand raw.inputDemand := by
  exact ⟨staticFuel, sourceContext, supply, generated, next, solution,
    elaboration, semantic, contextCompatible, rfl, raw, rfl⟩

/-- The existential family faithfully supplies the demand-parametric
embedded-evaluator contract for the actual `evalFuel`. -/
theorem m4FuelEmbeddedEvaluatorSafe
    (compatible : SignatureCompatible signature.base) :
    FuelEmbeddedEvaluatorSafe (M4FuelEmbeddedCertificate signature)
      evalFuel := by
  intro operationalFuel bindingTypes environmentTypes expression target
    outputDemand inputDemand bindings environment certificate environmentSafe
  rcases certificate with
    ⟨staticFuel, sourceContext, supply, generated, next, solution,
      elaboration, semantic, contextCompatible, targetEq, raw, inputEq⟩
  subst target
  subst inputDemand
  exact raw.preserves compatible solution semantic (bindings ++ environment)
    (environmentSafe.toSchemeOrigin contextCompatible)

end TypePM.Source.M4
