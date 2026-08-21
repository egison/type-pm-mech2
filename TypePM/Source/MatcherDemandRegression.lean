import TypePM.Source.M4RecursiveElaboration
import TypePM.Source.Paper1Programs

/-!
# Paper 1 higher-order matcher demand

This module fixes the exact source program displayed as `unconsWith` in
Paper 1.  The matcher parameter is not treated as a producer: inference
records the constructor-pattern requirement with `Ty.slot`, while the target
parameter fixes the list element type.
-/

namespace TypePM.Source.MatcherDemand

open TypePM.Source

set_option linter.unusedSimpArgs false

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, tyEquations, capEquations, eliminatedVariable?,
        unificationVars, Equation.unificationVars, Ty.unificationVars,
        Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, Ty.nodeCount, Ty.nodeCountList,
        Cap.nodeCount, Cap.nodeCountList,
        Ty.occursTy, Ty.occursTyList, Cap.occurs, Cap.occursList,
        Equation.apply, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
        Subst.singleTy, Subst.singleCap, Subst.compose, Subst.id])

/-- `def unconsWith m target :=
    matchAll target as m with $x :: $xs -> (x, xs)`.

The two lambdas bind `m` and then `target`.  Pattern bindings are prepended in
source order, so the result tuple reads `x` at index zero and `xs` at index
one. -/
def unconsWith : Expr :=
  .lam (.lam
    (.matchAll (.var 0) (.var 1)
      (.ctor PatternCtor.cons [.var, .var])
      (.tuple [.var 0, .var 1])))

/-- The exact residual-variable representative returned by public M4
inference.  The residual capability and element variables stand for the two
universally quantified variables in the paper notation. -/
def unconsWithType : Ty :=
  .fn
    (.slot (.con PatternFormer.list [.var ⟨0⟩])
      (DataTypes.list (.var ⟨2⟩)))
    (.fn (DataTypes.list (.var ⟨2⟩))
      (DataTypes.list
        (.prod [.var ⟨2⟩, DataTypes.list (.var ⟨2⟩)])))

/-- Exact raw constraint block generated before saturation. -/
def unconsWithGenerated : Generated :=
  { target := .fn (.var ⟨0⟩)
      (.fn (.var ⟨1⟩)
        (DataTypes.list (.prod [.var ⟨3⟩, .var ⟨4⟩])))
    hard :=
      [ .ty (DataTypes.list (.var ⟨2⟩)) (.var ⟨1⟩),
        .ty (.var ⟨3⟩) (.var ⟨2⟩),
        .cap (.var ⟨1⟩) (.var ⟨0⟩),
        .ty (.var ⟨4⟩) (DataTypes.list (.var ⟨2⟩)),
        .cap (.var ⟨2⟩) (.con PatternFormer.list [.var ⟨0⟩]) ]
    pending :=
      [⟨.var ⟨0⟩,
        .slot (.con PatternFormer.list [.var ⟨0⟩]) (.var ⟨1⟩)⟩] }

/-- The full recursive elaborator produces exactly the displayed raw block. -/
theorem unconsWith_elaborate_exact :
    M4.elaborate Paper1FrozenSignature.signature [] unconsWith ⟨0, 0⟩ =
      some (unconsWithGenerated, ⟨5, 3⟩) := by
  unfold M4.elaborate unconsWith
  simp only [Expr.complexity, Expr.listComplexity, Pattern.complexity,
    Pattern.listComplexity]
  with_unfolding_all rfl

/-- Saturation turns the ordinary matcher parameter into the demanded slot,
without inventing a matcher producer. -/
theorem unconsWith_close_exact :
    (inferGeneratedUsing unify unconsWithGenerated).bind
      (fun closed => some closed.target) = some unconsWithType := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [unconsWithGenerated, unconsWithType, DataTypes.list]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have resolutionTrace :
      resolve (.var ⟨0⟩)
          (.slot (.con PatternFormer.list [.var ⟨0⟩])
            (.data DataFormer.list [.var ⟨2⟩])) =
        .ordinary (.var ⟨0⟩)
          (.slot (.con PatternFormer.list [.var ⟨0⟩])
            (.data DataFormer.list [.var ⟨2⟩])) := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations]
  compute_unification

/-- Public inference returns the higher-order matcher-slot demand exactly. -/
theorem unconsWith_infer_principal :
    M4.infer Paper1FrozenSignature.signature [] unconsWith =
      some unconsWithType := by
  unfold M4.infer
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    unconsWith_elaborate_exact]
  exact unconsWith_close_exact

/-- The exact inferred representative has an independently elaborated,
absorbing principal block-closure witness. -/
theorem unconsWith_principalTyping :
    M4.PrincipalTyping Paper1FrozenSignature.signature [] unconsWith
      unconsWithType :=
  M4.infer_success_principalTyping Paper1FrozenSignature.wellFormed
    unconsWith_infer_principal

/-- In particular, the exact inferred representative is accepted by the
independent M4 typing relation. -/
theorem unconsWith_typing :
    M4.Typing Paper1FrozenSignature.signature [] unconsWith
      unconsWithType :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    unconsWith_infer_principal

end TypePM.Source.MatcherDemand
