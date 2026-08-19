import TypePM.InferenceCompleteness
import TypePM.M1Examples

/-!
# Executable M1 boundary regressions

These guards fix the four source-order examples at the public `infer`
boundary.  The positive computations are connected to the independent
declarative typing relation through inference soundness; the negative
computations use inference completeness to rule out any declarative result.
-/

namespace TypePM
namespace M1BoundaryRegression

set_option linter.unusedSimpArgs false

open M1Examples

private def tv (index : Nat) : Ty := .var ⟨index⟩

private def useFirstProblem : Generated :=
  { target := .fn (tv 0) (.prod [tv 2, tv 5])
    hard := [
      .ty useType (.fn (tv 1) (tv 2)),
      .ty (tv 0) (.fn (tv 4) (tv 5))]
    pending := [
      ⟨tv 0, tv 1⟩,
      ⟨.matcher .any (tv 3), tv 4⟩] }

private def applicationFirstProblem : Generated :=
  { target := .fn (tv 0) (.prod [tv 3, tv 5])
    hard := [
      .ty (tv 0) (.fn (tv 2) (tv 3)),
      .ty useType (.fn (tv 4) (tv 5))]
    pending := [
      ⟨.matcher .any (tv 1), tv 2⟩,
      ⟨tv 0, tv 4⟩] }

private def singletonFirstProblem : Generated :=
  { target := .fn (tv 0) (.prod [tv 3, tv 7])
    hard := [
      .ty (tv 0) (.fn (tv 2) (tv 3)),
      .ty (tv 0) (.fn (tv 6) (tv 7))]
    pending := [
      ⟨.matcher .any (tv 1), tv 2⟩,
      ⟨.prod [.matcher .any (tv 4), .matcher .any (tv 5)], tv 6⟩] }

private def pairFirstProblem : Generated :=
  { target := .fn (tv 0) (.prod [tv 4, tv 7])
    hard := [
      .ty (tv 0) (.fn (tv 3) (tv 4)),
      .ty (tv 0) (.fn (tv 6) (tv 7))]
    pending := [
      ⟨.prod [.matcher .any (tv 1), .matcher .any (tv 2)], tv 3⟩,
      ⟨.matcher .any (tv 5), tv 6⟩] }

private theorem unify_nil_exact :
    unify [] = some Subst.id := by
  unfold unify
  rw [unifyLoop.eq_def]

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, eliminatedVariable?, unificationVars,
        Equation.unificationVars, Ty.unificationVars,
        Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, Ty.nodeCount, Ty.nodeCountList,
        Cap.nodeCount, Cap.nodeCountList,
        Ty.occursTy, Ty.occursTyList, Cap.occurs, Cap.occursList,
        Equation.apply, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
        Subst.singleTy, Subst.singleCap, Subst.compose, Subst.id])

/-- Delaying the application demand until after `use f` accepts the intended
function type. -/
theorem infer_useFirst_exact :
    infer useContext useFirst = some acceptedType := by
  unfold infer inferUsing
  rw [show generate useContext useFirst useContext.nextVar =
    some (useFirstProblem, 6) by rfl]
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only
  simp only [useFirstProblem, tv, useType, consumerFunction, slotInt]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  simp only [saturateLoop]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨3⟩)) (.slot .any .int) =
        .matcherToSlot .any .any (.var ⟨3⟩) .int .rootedAny := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification
  simp [acceptedType, useType, consumerFunction, slotInt, Ty.apply,
    Ty.applyList, Cap.apply, Cap.applyList, Subst.compose, Subst.id]

/-- Encountering `f something` before `use f` produces the same result. -/
theorem infer_applicationFirst_exact :
    infer useContext applicationFirst = some acceptedType := by
  unfold infer inferUsing
  rw [show generate useContext applicationFirst useContext.nextVar =
    some (applicationFirstProblem, 6) by rfl]
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only
  simp only [applicationFirstProblem, tv, useType, consumerFunction, slotInt]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  simp only [saturateLoop]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨1⟩)) (.slot .any .int) =
        .matcherToSlot .any .any (.var ⟨1⟩) .int .rootedAny := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification
  simp [acceptedType, useType, consumerFunction, slotInt, Ty.apply,
    Ty.applyList, Cap.apply, Cap.applyList, Subst.compose, Subst.id]

/-- Two incompatible uses of the same function are rejected without guessing
a product capability. -/
theorem infer_singletonFirst_none :
    infer useContext singletonFirst = none := by
  unfold infer inferUsing
  rw [show generate useContext singletonFirst useContext.nextVar =
    some (singletonFirstProblem, 8) by rfl]
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only
  simp only [singletonFirstProblem, tv, useType, consumerFunction, slotInt]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  have matcherResolution :
      resolve (.matcher .any (.var ⟨1⟩)) (.var ⟨6⟩) =
        .ordinary (.matcher .any (.var ⟨1⟩)) (.var ⟨6⟩) := by
    rfl
  have productResolution :
      resolve (.prod [.matcher .any (.var ⟨4⟩),
          .matcher .any (.var ⟨5⟩)]) (.var ⟨6⟩) =
        .ordinary (.prod [.matcher .any (.var ⟨4⟩),
          .matcher .any (.var ⟨5⟩)]) (.var ⟨6⟩) := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [matcherResolution, productResolution]
  simp [Resolution.equations]
  compute_unification

/-- Reversing the two incompatible uses remains rejected. -/
theorem infer_pairFirst_none :
    infer useContext pairFirst = none := by
  unfold infer inferUsing
  rw [show generate useContext pairFirst useContext.nextVar =
    some (pairFirstProblem, 8) by rfl]
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only
  simp only [pairFirstProblem, tv, useType, consumerFunction, slotInt]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  have productResolution :
      resolve (.prod [.matcher .any (.var ⟨1⟩),
          .matcher .any (.var ⟨2⟩)]) (.var ⟨6⟩) =
        .ordinary (.prod [.matcher .any (.var ⟨1⟩),
          .matcher .any (.var ⟨2⟩)]) (.var ⟨6⟩) := by
    rfl
  have matcherResolution :
      resolve (.matcher .any (.var ⟨5⟩)) (.var ⟨6⟩) =
        .ordinary (.matcher .any (.var ⟨5⟩)) (.var ⟨6⟩) := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [productResolution, matcherResolution]
  simp [Resolution.equations]
  compute_unification

/-- Raw inference of the pair remains product-headed.  Matcher and slot
interpretations belong to checking, not synthesis. -/
theorem infer_pair_exact_raw_product :
    infer [] Regression.pair = some pairGenerated.target := by
  unfold infer inferUsing
  rw [show generate [] Regression.pair (Context.nextVar []) =
    some (pairGenerated, 2) by rfl]
  simp [inferGeneratedUsing, pairGenerated, saturateUsing, saturateLoop,
    unify_nil_exact, promoteUnder, residualEquations]

/-- Both accepted source orders compute literally the same public target. -/
theorem accepted_orders_same_target :
    infer useContext useFirst = infer useContext applicationFirst := by
  rw [infer_useFirst_exact, infer_applicationFirst_exact]

theorem useFirst_typing :
    Typing useContext useFirst acceptedType :=
  Inference.infer_success_typing infer_useFirst_exact

theorem applicationFirst_typing :
    Typing useContext applicationFirst acceptedType :=
  Inference.infer_success_typing infer_applicationFirst_exact

theorem pair_raw_product_typing :
    Typing [] Regression.pair pairGenerated.target :=
  Inference.infer_success_typing infer_pair_exact_raw_product

/-- Completeness turns executable rejection into the absence of any
declarative type. -/
theorem singletonFirst_not_typable
    (target : Ty) :
    ¬ Typing useContext singletonFirst target := by
  intro typing
  exact typing.infer_isSome infer_singletonFirst_none

theorem pairFirst_not_typable
    (target : Ty) :
    ¬ Typing useContext pairFirst target := by
  intro typing
  exact typing.infer_isSome infer_pairFirst_none

end M1BoundaryRegression
end TypePM
