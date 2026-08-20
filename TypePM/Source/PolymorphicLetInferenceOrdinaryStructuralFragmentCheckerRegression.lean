import TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralFragmentChecker
import TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralFragmentRegression

/-!
# Regression for the executable ordinary-fragment checker

These examples reuse the fragment fixtures rather than reconstructing their
certificates by hand.  The positive example computes to `true`; the exposed
matcher-to-slot application computes to `false`.  Wrapping that application
as a `letE` right-hand side remains accepted because the root fragment, and
therefore the checker, deliberately inspect only the body.
-/

namespace TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralFragmentCheckerRegression

open Runtime
open PolymorphicLetInferenceOrdinaryStructuralFragmentRegression

/-- The ordinary lambda application and primitive call are accepted by direct
syntax computation. -/
theorem ordinaryFragmentFixture_fragmentCheck :
    rootOrdinarySourceFragmentCheck ordinaryFragmentFixture = true := by
  with_unfolding_all rfl

/-- Exposing the matcher-to-slot application at the root is outside the
explicit fragment. -/
theorem hiddenMatcherToSlot_fragmentCheck_rejected :
    rootOrdinarySourceFragmentCheck hiddenMatcherToSlot = false := by
  with_unfolding_all rfl

/-- The checker has the same intentional `letE` boundary as the proposition:
the internally closed right-hand side is not part of the root pending block. -/
theorem ordinaryFragmentWithHiddenRhs_fragmentCheck :
    rootOrdinarySourceFragmentCheck ordinaryFragmentWithHiddenRhs = true := by
  with_unfolding_all rfl

/-- The positive computation reconstructs the reusable node-indexed root
certificate. -/
theorem ordinaryFragmentFixture_rootStructuralFromCheck :
    InferenceRootResolutionsOrdinaryStructural Paper1Signature.signature []
      ordinaryFragmentFixture :=
  rootOrdinarySourceFragmentCheck_rootStructural
    ordinaryFragmentFixture_fragmentCheck Paper1Signature.wellFormed

/-- The checked certificate supplies the ordinary-residual premise used by
the public inference-to-runtime bridge. -/
theorem ordinaryFragmentFixture_residualsFromFragmentCheck :
    InferenceResidualsOrdinary Paper1Signature.signature []
      ordinaryFragmentFixture :=
  InferenceRootPendingResolutionsOrdinary.inferenceResidualsOrdinary
    ordinaryFragmentFixture_rootStructuralFromCheck.rootPending

/-- Fragment-check acceptance and an independent genuine public inference
result make the executable root structural checker accept. -/
theorem ordinaryFragmentFixture_checkedPublicInfer_structuralCheck :
    inferenceRootStructuralOrdinaryCheck Paper1Signature.signature []
      ordinaryFragmentFixture = true := by
  obtain ⟨target, success⟩ := infer_ordinaryFragmentFixture_isSome
  exact rootOrdinarySourceFragmentCheck_inferenceRootStructuralCheck
    ordinaryFragmentFixture_fragmentCheck Paper1Signature.wellFormed success

/-- The checked source certificate, rather than a handwritten generated
block, reaches runtime typing after public inference succeeds. -/
theorem ordinaryFragmentFixture_runtimeTypingFromCheckedFragment
    (success : infer Paper1Signature.signature [] ordinaryFragmentFixture =
      some target) :
    ProtectedClosureRuntimeTyping [] ordinaryFragmentFixture target [] := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success
      ordinaryFragmentFixture_residualsFromFragmentCheck
  have typing := ordinaryFragmentFixture_bodySupported.elaboration_typing
    paper1SignatureCompatible certified.derivation.elaboration
      (strictSemanticSolution_of_closure certified.derivation.closure
        certified.ordinary)
      ProtectedContextCompatible.nil
  rw [certified.derivation.target_eq]
  exact typing

/-- The actual checked public-inference run cannot evaluate to `stuck` at any
fuel. -/
theorem ordinaryFragmentFixture_checkedFragment_neverStuck (fuel : Nat) :
    (evalFuel fuel [] ordinaryFragmentFixture).NotStuck := by
  obtain ⟨target, success⟩ := infer_ordinaryFragmentFixture_isSome
  exact (ordinaryFragmentFixture_runtimeTypingFromCheckedFragment success)
    |>.neverStuck fuel [] EnvironmentTyping.nil

end TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralFragmentCheckerRegression
