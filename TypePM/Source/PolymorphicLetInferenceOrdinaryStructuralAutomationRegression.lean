import TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralAutomation

/-!
# Regression for source-structural ordinary-check automation

This new fixture uses one generalized identity from the source context at
both integer and matcher types below a conditional.  The root certificate is
obtained by one source-structural Boolean check rather than by replaying the
generated pending list in the proof.  The general checker theorem, rather
than this one fixture, also covers `let` (with its right-hand side hidden),
non-nullary constructors, and primitives.
-/

namespace TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralAutomationRegression

open Runtime
open PolymorphicLetProtectedSyntaxRegression
open PolymorphicLetInferenceOrdinary

set_option linter.unusedSimpArgs false

def slotConsumerScheme : Scheme :=
  .mono (.fn (.slot .any .int) .int)

def actualMatcherToSlotApplication : Expr :=
  .app (.var 0) .something

set_option maxRecDepth 100000 in
/-- The rejection theorem is exercised on an actual source elaboration, not
merely on a hand-written obligation.  Hard saturation exposes the function's
slot domain, after which the local application check selects the special
matcher-to-slot conversion and rejects it. -/
theorem actualMatcherToSlotApplication_rejected :
    inferenceRootStructuralOrdinaryCheckUsing (unifyWithFuel 100)
      Paper1Signature.signature [slotConsumerScheme]
        actualMatcherToSlotApplication = false := by
  with_unfolding_all rfl

def automaticFragmentBody : Expr :=
  .ifE (.ctor DataCtor.true [])
    (.tuple [
      .app (.var 0) (.lit 7),
      .app (.var 0) .something])
    (.tuple [
      .lit 0,
      .something])

theorem automaticFragmentBody_supported :
    ProtectedClosureBodySupported automaticFragmentBody := by
  exact .firstOrder (.ifE .boolTrue
    (.tuple (.cons
      (.app .var .lit)
      (.cons (.app .var .something) .nil)))
    (.tuple (.cons
      .lit
      (.cons .something .nil))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem automaticFragmentBody_structuralFuelCheck :
    inferenceRootStructuralOrdinaryCheckUsing (unifyWithFuel 1000)
      Paper1Signature.signature [identityScheme] automaticFragmentBody = true := by
  with_unfolding_all rfl

/-- One source-structural computation discharges the public root checker. -/
theorem automaticFragmentBody_structuralCheck :
    inferenceRootStructuralOrdinaryCheck Paper1Signature.signature
      [identityScheme] automaticFragmentBody = true :=
  inferenceRootStructuralOrdinaryCheck_unify_of_fuel
    automaticFragmentBody_structuralFuelCheck

/-- The public `true` result constructs the node-indexed certificate. -/
theorem automaticFragmentBody_structuralOrdinary :
    InferenceRootResolutionsOrdinaryStructural Paper1Signature.signature
      [identityScheme] automaticFragmentBody :=
  InferenceRootResolutionsOrdinaryStructural.of_sourceStructuralCheck
    Paper1Signature.wellFormed automaticFragmentBody_structuralCheck

theorem automaticFragmentBody_residualsOrdinary :
    InferenceResidualsOrdinary Paper1Signature.signature [identityScheme]
      automaticFragmentBody :=
  automaticFragmentBody_structuralOrdinary.rootPending.inferenceResidualsOrdinary

private theorem identityContextCompatible (solution : Subst) :
    ProtectedContextCompatible [identityScheme]
      [(identityScheme.instantiate ⟨0, 0⟩).1] [true] solution := by
  apply ProtectedContextCompatible.pushCanonical
      (canonicalSupply := (⟨0, 0⟩ : Supply))
  · intro index membership
    simp [identityScheme, Scheme.freeTyVars, PolyTy.freeTyVars,
      dedupFirst, dedup] at membership
  · intro index membership
    simp [identityScheme, Scheme.freeCapVars, PolyTy.freeCapVars,
      dedupFirst, dedup] at membership
  · exact ProtectedContextCompatible.nil

theorem automaticFragmentBody_runtimeTypingFromCheckedInfer
    (success : infer Paper1Signature.signature [identityScheme]
      automaticFragmentBody = some target) :
    ProtectedClosureRuntimeTyping [true] automaticFragmentBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success
      automaticFragmentBody_residualsOrdinary
  have typing := automaticFragmentBody_supported.elaboration_typing
    paper1SignatureCompatible certified.derivation.elaboration
      (strictSemanticSolution_of_closure certified.derivation.closure
        certified.ordinary)
      (identityContextCompatible certified.derivation.closure.substitution)
  rw [certified.derivation.target_eq]
  exact typing

theorem automaticFragmentBody_neverStuckFromCheckedInfer
    (success : infer Paper1Signature.signature [identityScheme]
      automaticFragmentBody = some target)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      automaticFragmentBody).NotStuck := by
  apply (automaticFragmentBody_runtimeTypingFromCheckedInfer success).neverStuck
  exact EnvironmentTyping.cons
    (.plainClosure .nil (.var rfl)) EnvironmentTyping.nil

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem automaticFragmentBody_inferFuelSome :
    (match elaborate Paper1Signature.signature [identityScheme]
        automaticFragmentBody (Context.initialSupply [identityScheme]) with
      | none => false
      | some (generated, _) =>
          (inferGeneratedUsing (unifyWithFuel 1000) generated).isSome) = true := by
  with_unfolding_all rfl

/-- The fixture has a genuine successful public inference result.  This is a
fixture-specific computation, not an arbitrary-success claim for the source
fragment. -/
theorem infer_automaticFragmentBody_isSome :
    ∃ target, infer Paper1Signature.signature [identityScheme]
      automaticFragmentBody = some target := by
  have fuelSome := automaticFragmentBody_inferFuelSome
  cases elaborated : elaborate Paper1Signature.signature [identityScheme]
      automaticFragmentBody (Context.initialSupply [identityScheme]) with
  | none => simp [elaborated] at fuelSome
  | some output =>
      rcases output with ⟨generated, next⟩
      simp only [elaborated] at fuelSome
      cases fuelResult : inferGeneratedUsing (unifyWithFuel 1000) generated with
      | none => simp [fuelResult] at fuelSome
      | some result =>
          have publicResult := inferGeneratedUsing_unify_of_fuel_success fuelResult
          refine ⟨result.target, ?_⟩
          unfold infer elaborateRoot
          simp [elaborated, publicResult]

theorem automaticFragmentBody_checkedPublicInfer_runtimeTyping :
    ∃ target, ProtectedClosureRuntimeTyping [true] automaticFragmentBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  obtain ⟨target, success⟩ := infer_automaticFragmentBody_isSome
  exact ⟨target, automaticFragmentBody_runtimeTypingFromCheckedInfer success⟩

theorem automaticFragmentBody_checkedPublicInfer_neverStuck (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      automaticFragmentBody).NotStuck := by
  obtain ⟨target, success⟩ := infer_automaticFragmentBody_isSome
  exact automaticFragmentBody_neverStuckFromCheckedInfer success fuel

end TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralAutomationRegression
