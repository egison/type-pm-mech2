import TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralChecker

/-!
# Regression for the executable structural checker

The nested tuple-value fixture closes a product-valued inner `let`, then uses
an outer generalized identity at both `Int` and matcher types.  This gives a
second, nontrivial public-inference path beyond the conditional fixture in
the structural-certificate module.
-/

namespace TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralCheckerRegression

open Runtime
open PolymorphicLetProtectedSyntaxRegression
open PolymorphicLetInferenceOrdinary

set_option linter.unusedSimpArgs false

set_option maxRecDepth 100000 in
private theorem nestedTupleValueBody_rootFuelCheck :
    inferenceRootPendingResolutionsOrdinaryCheckUsing (unifyWithFuel 100)
      Paper1Signature.signature [identityScheme] nestedTupleValueBody = true := by
  unfold inferenceRootPendingResolutionsOrdinaryCheckUsing
  rw [elaborate_nestedTupleValueBody_exact]
  with_unfolding_all rfl

/-- The public root checker accepts the actual nested source elaboration. -/
theorem nestedTupleValueBody_rootCheck :
    inferenceRootPendingResolutionsOrdinaryCheck Paper1Signature.signature
      [identityScheme] nestedTupleValueBody = true :=
  inferenceRootPendingResolutionsOrdinaryCheck_unify_of_fuel
    nestedTupleValueBody_rootFuelCheck

/-- Checker success constructs the node-indexed structural certificate for
the actual relational elaboration. -/
theorem nestedTupleValueBody_structuralOrdinary :
    InferenceRootResolutionsOrdinaryStructural Paper1Signature.signature
      [identityScheme] nestedTupleValueBody :=
  InferenceRootResolutionsOrdinaryStructural.of_check
    Paper1Signature.wellFormed nestedTupleValueBody_rootCheck

/-- Forgetting node origins supplies exactly the residual premise needed by
the public inference-to-runtime bridge. -/
theorem nestedTupleValueBody_residualsFromStructuralCheck :
    InferenceResidualsOrdinary Paper1Signature.signature [identityScheme]
      nestedTupleValueBody :=
  nestedTupleValueBody_structuralOrdinary.rootPending.inferenceResidualsOrdinary

theorem nestedTupleValueBody_runtimeTypingFromCheckedInfer
    (success : infer Paper1Signature.signature [identityScheme]
      nestedTupleValueBody = some target) :
    ProtectedClosureRuntimeTyping [true] nestedTupleValueBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success
      nestedTupleValueBody_residualsFromStructuralCheck
  exact nestedTupleValueBody_runtimeTypingFromSource certified.derivation
    certified.ordinary

theorem nestedTupleValueBody_neverStuckFromCheckedInfer
    (success : infer Paper1Signature.signature [identityScheme]
      nestedTupleValueBody = some target)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      nestedTupleValueBody).NotStuck :=
  (nestedTupleValueBody_runtimeTypingFromCheckedInfer success).neverStuck fuel
    [Value.plainClosure [] (.var 0)] (EnvironmentTyping.cons
      (.plainClosure .nil (.var rfl)) EnvironmentTyping.nil)

set_option maxRecDepth 100000 in
private theorem nestedTupleValueBody_inferFuelSome :
    (match elaborate Paper1Signature.signature [identityScheme]
        nestedTupleValueBody (Context.initialSupply [identityScheme]) with
      | none => false
      | some (generated, _) =>
          (inferGeneratedUsing (unifyWithFuel 1000) generated).isSome) = true := by
  rw [elaborate_nestedTupleValueBody_exact]
  with_unfolding_all rfl

/-- The regression uses a genuine successful public inference result, not a
hand-written target type. -/
theorem infer_nestedTupleValueBody_isSome :
    ∃ target, infer Paper1Signature.signature [identityScheme]
      nestedTupleValueBody = some target := by
  have fuelSome := nestedTupleValueBody_inferFuelSome
  cases elaborated : elaborate Paper1Signature.signature [identityScheme]
      nestedTupleValueBody (Context.initialSupply [identityScheme]) with
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

theorem nestedTupleValueBody_runtimeTypingFromCheckedPublicInfer :
    ∃ target, ProtectedClosureRuntimeTyping [true] nestedTupleValueBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  obtain ⟨target, success⟩ := infer_nestedTupleValueBody_isSome
  exact ⟨target, nestedTupleValueBody_runtimeTypingFromCheckedInfer success⟩

theorem nestedTupleValueBody_checkedPublicInfer_neverStuck (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      nestedTupleValueBody).NotStuck := by
  obtain ⟨target, success⟩ := infer_nestedTupleValueBody_isSome
  exact nestedTupleValueBody_neverStuckFromCheckedInfer success fuel

end TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralCheckerRegression
