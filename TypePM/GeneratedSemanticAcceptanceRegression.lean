import TypePM.GeneratedSemanticAcceptance
import TypePM.Source.ElaborationCompleteness

/-!
# Semantic-solution completeness counterexample

One type variable occurs as the sole item of a product.  Assigning it the
matcher type `Matcher Any Int` exposes a valid product-matcher conversion.
Residual resolution, however, parses the product before solving and therefore
falls back to an impossible ordinary equality between a product and a matcher.
-/

namespace TypePM
namespace GeneratedSemanticAcceptanceCounterexample

set_option linter.unusedSimpArgs false

private def tyVariable : TyVar := ⟨0⟩

private def delayedProductMatcher : CheckObligation :=
  ⟨.prod [.var tyVariable], .matcher (.prod [.any]) (.prod [.int])⟩

/-- A minimal counterexample by obligation count: no hard equations, one
ordinary type variable, and one delayed obligation. -/
def block : Generated :=
  { target := .int
    hard := []
    pending := [delayedProductMatcher] }

private def semanticSubstitution : Subst :=
  Subst.singleTy tyVariable (.matcher .any .int)

theorem has_semanticSolution : block.SemanticSolution semanticSubstitution := by
  constructor
  · simp [block, Solves]
  · intro obligation membership
    simp only [block, List.mem_cons, List.not_mem_nil, or_false] at membership
    subst obligation
    refine ⟨.productMatcher, ?_⟩
    simpa [delayedProductMatcher, semanticSubstitution, tyVariable,
      Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.singleTy,
      Dual.matcherType, Dual.capabilities, Dual.targets] using
      (CheckConversion.productMatcher
        (duals := [⟨Cap.any, Ty.int⟩]) (by simp))

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, eliminatedVariable?, unificationVars,
        Equation.unificationVars, Ty.unificationVars,
        Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, Ty.nodeCount, Ty.nodeCountList,
        Cap.nodeCount, Cap.nodeCountList, Ty.occursTy, Ty.occursTyList,
        Cap.occurs, Cap.occursList, Equation.apply, Ty.apply,
        Ty.applyList, Cap.apply, Cap.applyList, Subst.singleTy,
        Subst.singleCap, Subst.compose, Subst.id])

/-- The executable certified closure rejects the block because its ordinary
residual equality has incompatible outer constructors. -/
theorem inferGeneratedUsing_unify_eq_none :
    inferGeneratedUsing unify block = none := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only
  simp only [block, delayedProductMatcher, tyVariable]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  have resolutionTrace :
      resolve (.prod [.var (⟨0⟩ : TyVar)])
          (.matcher (.prod [.any]) (.prod [.int])) =
        .ordinary (.prod [.var (⟨0⟩ : TyVar)])
          (.matcher (.prod [.any]) (.prod [.int])) := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations]
  compute_unification

/-- Existence of pointwise checking conversions does not imply generated
block acceptance. -/
theorem not_blockAccepts : ¬ BlockAccepts block := by
  intro accepts
  have accepted := BlockAccepts.inferGeneratedUsing_isSome
    unify_completeMGUSolver accepts
  exact accepted inferGeneratedUsing_unify_eq_none

theorem semanticSolution_not_iff_blockAccepts :
    (∃ solution, block.SemanticSolution solution) ∧ ¬ BlockAccepts block :=
  ⟨⟨semanticSubstitution, has_semanticSolution⟩, not_blockAccepts⟩

end GeneratedSemanticAcceptanceCounterexample
end TypePM
