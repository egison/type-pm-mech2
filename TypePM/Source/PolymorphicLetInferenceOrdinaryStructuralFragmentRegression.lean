import TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralFragment

/-!
# Regression for the structurally ordinary source fragment

The fixture has no generated-block literal.  Its fragment proof follows the
source tree, and the general theorem turns one genuine public inference
success into acceptance by the source-structural checker.

The main inferred fixture contains an ordinary lambda application and a
two-argument primitive call.  A second fixture wraps the same body in a
`letE` whose right-hand side contains a matcher-to-slot application.  That
application is not itself in the fragment, but closing the right-hand side
keeps its pending obligation out of the root block.
-/

namespace TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralFragmentRegression

open Runtime

def slotConsumerScheme : Scheme :=
  .mono (.fn (.slot .any .int) .int)

def hiddenMatcherToSlot : Expr :=
  .app (.var 0) .something

def ordinaryFragmentFixture : Expr :=
  .app
    (.lam (.tuple [
      .var 0,
      .prim .add [.lit 20, .lit 22]]))
    (.lit 7)

def ordinaryFragmentWithHiddenRhs : Expr :=
  .letE hiddenMatcherToSlot ordinaryFragmentFixture

/-- The special matcher argument prevents the internally closed right-hand
side from satisfying the explicit root fragment on its own. -/
theorem hiddenMatcherToSlot_not_fragment :
    ¬ RootOrdinarySourceFragment hiddenMatcherToSlot := by
  intro fragment
  cases fragment with
  | app functionFragment argumentFragment argumentResult =>
      cases argumentResult

set_option maxRecDepth 100000 in
/-- The excluded expression genuinely selects a special matcher-to-slot
conversion when checked at the root. -/
theorem hiddenMatcherToSlot_rootCheck_rejected :
    inferenceRootStructuralOrdinaryCheckUsing (unifyWithFuel 100)
      Paper1Signature.signature [slotConsumerScheme] hiddenMatcherToSlot = false := by
  with_unfolding_all rfl

/-- The root fragment deliberately starts at the `letE` body.  Its two actual
call sites use only syntax-fixed integer arguments. -/
theorem ordinaryFragmentFixture_fragment :
    RootOrdinarySourceFragment ordinaryFragmentFixture := by
  exact .app
    (.lam (.tuple
      (.cons (.var 0)
        (.cons
          (.prim .add
            (.cons (.lit 20) (.lit 20)
              (.cons (.lit 22) (.lit 22) .nil)))
          .nil))))
    (.lit 7)
    (.lit 7)

/-- The same fixture lies in the existing one-closure runtime fragment: the
lambda body is first-order and contains the tuple and primitive call. -/
theorem ordinaryFragmentFixture_bodySupported :
    ProtectedClosureBodySupported ordinaryFragmentFixture := by
  exact .app
    (.lam (.tuple
      (.cons .var
        (.cons (.add .lit .lit) .nil))))
    .lit

/-- `letE` admits the same body certificate without requiring its internally
closed right-hand side to belong to the root fragment. -/
theorem ordinaryFragmentWithHiddenRhs_fragment :
    RootOrdinarySourceFragment ordinaryFragmentWithHiddenRhs :=
  .letE hiddenMatcherToSlot ordinaryFragmentFixture_fragment

/-- The root certificate remains available around the internal special
conversion because `Generated.fromLet` exposes only the body's pending list. -/
theorem ordinaryFragmentWithHiddenRhs_rootStructural :
    InferenceRootResolutionsOrdinaryStructural Paper1Signature.signature
      [slotConsumerScheme] ordinaryFragmentWithHiddenRhs :=
  ordinaryFragmentWithHiddenRhs_fragment.rootStructural
    Paper1Signature.wellFormed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ordinaryFragmentFixture_inferFuelSome :
    (match elaborate Paper1Signature.signature []
        ordinaryFragmentFixture (Context.initialSupply []) with
      | none => false
      | some (generated, _) =>
          (inferGeneratedUsing (unifyWithFuel 1000) generated).isSome) = true := by
  with_unfolding_all rfl

/-- This is an actual public inference result, not an assumption equivalent
to checker acceptance. -/
theorem infer_ordinaryFragmentFixture_isSome :
    ∃ target, infer Paper1Signature.signature []
      ordinaryFragmentFixture = some target := by
  have fuelSome := ordinaryFragmentFixture_inferFuelSome
  cases elaborated : elaborate Paper1Signature.signature []
      ordinaryFragmentFixture (Context.initialSupply []) with
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

/-- Public inference plus the syntactic fragment theorem automatically
establishes the executable source-structural root check. -/
theorem ordinaryFragmentFixture_structuralCheck :
    inferenceRootStructuralOrdinaryCheck Paper1Signature.signature
      [] ordinaryFragmentFixture = true := by
  obtain ⟨target, success⟩ := infer_ordinaryFragmentFixture_isSome
  exact ordinaryFragmentFixture_fragment.inferenceRootStructuralCheck
    Paper1Signature.wellFormed success

/-- The same syntax evidence constructs the reusable node-indexed root
certificate without mentioning generated obligations. -/
theorem ordinaryFragmentFixture_rootStructural :
    InferenceRootResolutionsOrdinaryStructural Paper1Signature.signature
      [] ordinaryFragmentFixture :=
  ordinaryFragmentFixture_fragment.rootStructural Paper1Signature.wellFormed

/-- The structural root certificate supplies the exact ordinary-residual
premise used by the protected inference-to-runtime bridge. -/
theorem ordinaryFragmentFixture_residualsOrdinary :
    InferenceResidualsOrdinary Paper1Signature.signature []
      ordinaryFragmentFixture :=
  ordinaryFragmentFixture_rootStructural.rootPending.inferenceResidualsOrdinary

/-- A successful public inference run now constructs runtime typing without
a fixture-specific generated block or handwritten runtime derivation. -/
theorem ordinaryFragmentFixture_runtimeTypingFromInfer
    (success : infer Paper1Signature.signature [] ordinaryFragmentFixture =
      some target) :
    ProtectedClosureRuntimeTyping [] ordinaryFragmentFixture target [] := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success
      ordinaryFragmentFixture_residualsOrdinary
  have typing := ordinaryFragmentFixture_bodySupported.elaboration_typing
    paper1SignatureCompatible certified.derivation.elaboration
      (strictSemanticSolution_of_closure certified.derivation.closure
        certified.ordinary)
      ProtectedContextCompatible.nil
  rw [certified.derivation.target_eq]
  exact typing

/-- Runtime typing from the checked public inference rules out `stuck` for
every evaluator fuel. -/
theorem ordinaryFragmentFixture_neverStuckFromInfer
    (success : infer Paper1Signature.signature [] ordinaryFragmentFixture =
      some target)
    (fuel : Nat) :
    (evalFuel fuel [] ordinaryFragmentFixture).NotStuck :=
  (ordinaryFragmentFixture_runtimeTypingFromInfer success).neverStuck
    fuel [] EnvironmentTyping.nil

/-- The regression's actual public inference run reaches the runtime typing
endpoint. -/
theorem ordinaryFragmentFixture_checkedPublicInfer_runtimeTyping :
    ∃ target, ProtectedClosureRuntimeTyping [] ordinaryFragmentFixture target [] := by
  obtain ⟨target, success⟩ := infer_ordinaryFragmentFixture_isSome
  exact ⟨target, ordinaryFragmentFixture_runtimeTypingFromInfer success⟩

/-- Closed arbitrary-fuel no-stuck endpoint for the actual inferred fixture. -/
theorem ordinaryFragmentFixture_checkedPublicInfer_neverStuck (fuel : Nat) :
    (evalFuel fuel [] ordinaryFragmentFixture).NotStuck := by
  obtain ⟨target, success⟩ := infer_ordinaryFragmentFixture_isSome
  exact ordinaryFragmentFixture_neverStuckFromInfer success fuel

end TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralFragmentRegression
