import TypePM.InferenceExactness
import TypePM.Principality
import TypePM.RenamingUniqueness
import TypePM.NoGuess
import TypePM.SourcePermutation
import TypePM.GenerationRenaming
import TypePM.SaturationRenaming
import TypePM.BlockOrderInvariance
import TypePM.UnificationRegression
import TypePM.Regression
import TypePM.M1BoundaryRegression

/-!
# Axiom audit for public milestones

These commands make the trusted assumptions of selected public results visible in
every full build.
-/

#print axioms TypePM.Cap.apply_compose
#print axioms TypePM.Ty.apply_compose
#print axioms TypePM.Regression.pair_principal
#print axioms TypePM.Regression.pair_checks_as_slot
#print axioms TypePM.Regression.structured_matcher_checks_at_any_slot
#print axioms TypePM.unify_none_iff_unsatisfiable
#print axioms TypePM.unify_completeMGUSolver
#print axioms TypePM.promoteUnder_equation_no_special_after
#print axioms TypePM.Resolution.special_expected_head
#print axioms TypePM.Resolution.resolve_apply_canonical_of_retract
#print axioms TypePM.ResolutionTransport.residualEquations_transport_of_mutualFactors
#print axioms TypePM.Inference.infer_success_typing
#print axioms TypePM.Typing.infer_isSome
#print axioms TypePM.Inference.typable_iff_infer_isSome
#print axioms TypePM.Inference.typableDecidable
#print axioms TypePM.Inference.infer_principal
#print axioms TypePM.Inference.infer_success_principalTyping
#print axioms TypePM.PrincipalTyping.finiteRenaming_unique
#print axioms TypePM.GeneratedItems.siblingAlphaEq_collect_of_perm
#print axioms TypePM.solves_rename_perm
#print axioms TypePM.GeneratesItems.swapAdjacentPair
#print axioms TypePM.Saturated.permuteInitial
#print axioms TypePM.TypingDerivation.transportAlphaEq
#print axioms TypePM.Generated.AlphaEq.blockAccepts_iff
#print axioms TypePM.M1BoundaryRegression.infer_useFirst_exact
#print axioms TypePM.M1BoundaryRegression.infer_applicationFirst_exact
#print axioms TypePM.M1BoundaryRegression.infer_singletonFirst_none
#print axioms TypePM.M1BoundaryRegression.infer_pairFirst_none
#print axioms TypePM.M1BoundaryRegression.infer_pair_exact_raw_product
#print axioms TypePM.M1BoundaryRegression.singletonFirst_not_typable
#print axioms TypePM.M1BoundaryRegression.pairFirst_not_typable
