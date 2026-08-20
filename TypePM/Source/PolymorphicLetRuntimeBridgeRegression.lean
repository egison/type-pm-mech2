import TypePM.Source.PolymorphicLetRuntimeBridge
import TypePM.Source.M2Regression

/-!
# Regression: one source-polymorphic identity used at two runtime types

This regression reuses the public M2 source program and exact inference
theorem.  Its single generalized identity closure is used first at `Int` and
then at a matcher type.  The runtime context is still `[Ty]`; the separate
`[true]` proof mask is the only fact authorizing both instantiations.
-/

namespace TypePM.Source.PolymorphicLetRuntimeBridgeRegression

open TypePM.Runtime

def resultType : Ty :=
  .prod [.int, .matcher .any (.var ⟨5⟩)]

def identityType : Ty :=
  .fn (.var ⟨0⟩) (.var ⟨0⟩)

private theorem identityAtInt :
    IsInstance identityType (.fn .int .int) := by
  refine ⟨Subst.singleTy ⟨0⟩ .int, ?_⟩
  simp [identityType, Subst.singleTy, Ty.apply]

private theorem identityAtMatcher :
    IsInstance identityType
      (.fn (.matcher .any (.var ⟨5⟩))
        (.matcher .any (.var ⟨5⟩))) := by
  refine ⟨Subst.singleTy ⟨0⟩ (.matcher .any (.var ⟨5⟩)), ?_⟩
  simp [identityType, Subst.singleTy, Ty.apply]

/-- Public inference exposes the actual value/body elaboration boundary of
the source `letE`.  At that boundary the generalized identity type is
automatically separated from the support generated later by the body; no
disjointness or substitution-fixedness premise is supplied by this
regression. -/
theorem polymorphicIdentity_actualLetBoundarySeparated :
    ClosedLetBoundVariableSupportSeparated Paper1Signature.signature
      (.lam (.var 0))
      (.tuple [
        .app (.var 0) (.lit 1),
        .app (.var 0) .something]) := by
  apply inferSuccessClosedLetBoundVariableSupportSeparated
    Paper1Signature.wellFormed
  simpa [M2Regression.polymorphicIdentity] using
    M2Regression.infer_polymorphicIdentity_exact

/-- The proof-only runtime derivation uses one generic context entry at two
different types.  Neither use is available through `RuntimeTyping.var`; both
must cite the `true` provenance entry introduced by `letPoly`. -/
theorem polymorphicIdentity_protectedRuntimeTyping :
    ProtectedRuntimeTyping [] M2Regression.polymorphicIdentity resultType := by
  apply ProtectedRuntimeTyping.letPoly
    (general := identityType)
  · exact .runtime (.lam (.var rfl))
  · apply ProtectedRuntimeTyping.tuple
    apply ProtectedRuntimeTypings.cons
    · apply ProtectedRuntimeTyping.app
      · exact .instantiatedVar rfl rfl identityAtInt
      · exact .runtime (.lit 1)
    · apply ProtectedRuntimeTypings.cons
      · apply ProtectedRuntimeTyping.app
        · exact .instantiatedVar rfl rfl identityAtMatcher
        · exact .runtime (.something (.var ⟨5⟩))
      · exact .nil

/-- The runtime certificate is anchored in the actual relational principal
typing recovered from successful public source inference. -/
theorem polymorphicIdentity_provenancedRuntimeTyping :
    ProvenancedRuntimeTyping Paper1Signature.signature
      M2Regression.polymorphicIdentity resultType := by
  exact Inference.infer_success_provenancedRuntimeTyping
    Paper1Signature.wellFormed M2Regression.infer_polymorphicIdentity_exact
      polymorphicIdentity_protectedRuntimeTyping

/-- Erasure of the bridge certificate is the existing public
`Source.Typing`, not a parallel source judgment. -/
theorem polymorphicIdentity_sourceTyping :
    Typing Paper1Signature.signature [] M2Regression.polymorphicIdentity
      resultType :=
  polymorphicIdentity_provenancedRuntimeTyping.toSourceTyping

/-- Source-polymorphic `let` has preservation and ready progress at every
fuel amount. -/
theorem polymorphicIdentity_typedResult (fuel : Nat) :
    TypedResult resultType
      (evalFuel fuel [] M2Regression.polymorphicIdentity) :=
  polymorphicIdentity_provenancedRuntimeTyping.coreSafety fuel

/-- Source-polymorphic `let` cannot reach the evaluator's `stuck` result. -/
theorem polymorphicIdentity_neverStuck (fuel : Nat) :
    (evalFuel fuel [] M2Regression.polymorphicIdentity).NotStuck :=
  polymorphicIdentity_provenancedRuntimeTyping.neverStuck fuel

/-- Both independent instantiations execute through the same closure. -/
theorem polymorphicIdentity_exactEvaluation :
    evalFuel 5 [] M2Regression.polymorphicIdentity =
      .ok (.tuple [.int 1, .something]) := by
  with_unfolding_all rfl

end TypePM.Source.PolymorphicLetRuntimeBridgeRegression
