import TypePM.Source.M4MatchFirstTyping
import TypePM.Source.M4FrozenSignatureRegression

/-!
# M4 single-result match regressions

The positive fixture is the exact static core of Paper 1's
`\(left,right) -> (left,right)` pattern lambda.  The negative fixtures check
the nonempty-arm requirement, common direct result type, and matcher-slot
checking.
-/

namespace TypePM.Source.M4MatchFirstTypingRegression

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

def tupleType : Ty := .prod [.int, .int]

def tupleContext : Context := [.mono tupleType]

def tupleMatcher : Expr := .tuple [.something, .something]

def tuplePattern : Pattern := .tuple [.var, .var]

def tupleBody : Expr := .tuple [.var 0, .var 1]

def tupleArm : MatchFirstArm := .mk tuplePattern tupleBody

def tupleMatch : Expr :=
  .matchFirst (.var 0) tupleMatcher [tupleArm]

def tupleLambda : Expr := Expr.tuplePatternLambda tupleBody

/-- The builder is exactly the Paper 1 pattern-lambda desugaring, not a
`matchAll` encoding that would add a list layer. -/
theorem tuple_pattern_lambda_desugaring_exact :
    tupleLambda = .lam tupleMatch := by
  rfl

def tupleGenerated : Generated :=
  { target := .prod [.var ⟨2⟩, .var ⟨3⟩]
    hard := [
      .ty (.prod [.var ⟨2⟩, .var ⟨3⟩]) tupleType]
    pending := [
      ⟨.prod [.matcher .any (.var ⟨0⟩), .matcher .any (.var ⟨1⟩)],
        .slot (.prod [.var ⟨0⟩, .var ⟨1⟩]) tupleType⟩] }

theorem elaborate_tuple_destructuring_exact :
    MatchFirstTyping.elaborate Paper1FrozenSignature.signature tupleContext
      (.var 0) tupleMatcher [tupleArm] ⟨0, 0⟩ =
        some (tupleGenerated, ⟨4, 2⟩) := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.armsExhaustive,
    MatchFirstTyping.structurallyIrrefutable,
    MatchFirstTyping.allStructurallyIrrefutable,
    MatchFirstTyping.elaborateArmsUsing,
    MatchFirstTyping.elaborateTailUsing,
    MatchFirstTyping.GeneratedArms.fromFirst,
    MatchFirstTyping.Generated.fromMatchFirst,
    tupleContext, tupleMatcher, tupleArm, tuplePattern, tupleBody,
    tupleGenerated, tupleType, elaboratePattern, elaboratePatterns,
    Pattern.extendContext, TypePM.Source.elaborate, elaborateItems,
    Scheme.mono, Scheme.instantiate, Supply.nextTy, Dual.targets,
    Dual.capabilities]

/-- Tuple destructuring has the direct tuple result, with no surrounding
list type. -/
theorem close_tuple_destructuring_exact :
    (inferGeneratedUsing unify tupleGenerated).bind
      (fun closed => some closed.target) = some tupleType := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [tupleGenerated, tupleType]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have resolutionTrace :
      resolve
          (.prod [.matcher .any (.var ⟨0⟩),
            .matcher .any (.var ⟨1⟩)])
          (.slot (.prod [.var ⟨0⟩, .var ⟨1⟩])
            (.prod [.int, .int])) =
        .productMatcherToSlot
          [.matcher .any (.var ⟨0⟩), .matcher .any (.var ⟨1⟩)]
          [⟨.any, .var ⟨0⟩⟩, ⟨.any, .var ⟨1⟩⟩]
          (by rfl) (by simp)
          (.prod [.var ⟨0⟩, .var ⟨1⟩]) (.prod [.int, .int])
          .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp only [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
    Subst.compose, Subst.id]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
    Subst.singleTy, Subst.singleCap, Subst.compose, Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations,
    Dual.capabilities, Dual.targets]
  compute_unification

theorem infer_tuple_destructuring_exact :
    MatchFirstTyping.infer Paper1FrozenSignature.signature tupleContext
      (.var 0) tupleMatcher [tupleArm] = some tupleType := by
  unfold MatchFirstTyping.infer
  rw [show Context.initialSupply tupleContext = ⟨0, 0⟩ by rfl,
    elaborate_tuple_destructuring_exact]
  exact close_tuple_destructuring_exact

theorem tuple_destructuring_relational :
    MatchFirstTyping.Elaborates Paper1FrozenSignature.signature tupleContext
      tupleMatch ⟨0, 0⟩ tupleGenerated ⟨4, 2⟩ := by
  exact MatchFirstTyping.elaborate_sound Paper1FrozenSignature.wellFormed
    elaborate_tuple_destructuring_exact

def firstArm : MatchFirstArm := .mk .wild (.lit 11)
def secondArm : MatchFirstArm := .mk .var (.lit 22)
def orderedArms : List MatchFirstArm := [firstArm, secondArm]

/-- Arm metadata is stored in source order, so a future evaluator can select
the first successful arm without reconstructing or sorting the list. -/
theorem source_order_first_arm_metadata_exact :
    orderedArms.head? = some firstArm ∧
      orderedArms.map MatchFirstArm.pattern = [.wild, .var] := by
  constructor <;> rfl

theorem absent_arms_rejected :
    MatchFirstTyping.elaborate Paper1FrozenSignature.signature tupleContext
      (.var 0) tupleMatcher [] ⟨0, 0⟩ = none := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.armsExhaustive,
    MatchFirstTyping.elaborateArmsUsing, tupleContext, tupleMatcher,
    TypePM.Source.elaborate, elaborateItems, Scheme.mono,
    Scheme.instantiate]

def inconsistentArms : List MatchFirstArm :=
  [tupleArm, .mk .wild (.tuple [.lit 1])]

def inconsistentGenerated : Generated :=
  { target := .prod [.var ⟨2⟩, .var ⟨3⟩]
    hard := [
      .ty (.prod [.var ⟨2⟩, .var ⟨3⟩]) tupleType,
      .ty (.var ⟨4⟩) tupleType,
      .ty (.prod [.int]) (.prod [.var ⟨2⟩, .var ⟨3⟩])]
    pending := [
      ⟨.prod [.matcher .any (.var ⟨0⟩), .matcher .any (.var ⟨1⟩)],
        .slot (.prod [.var ⟨0⟩, .var ⟨1⟩]) tupleType⟩,
      ⟨.prod [.matcher .any (.var ⟨0⟩), .matcher .any (.var ⟨1⟩)],
        .slot (.var ⟨2⟩) tupleType⟩] }

theorem elaborate_inconsistent_exact :
    MatchFirstTyping.elaborate Paper1FrozenSignature.signature tupleContext
      (.var 0) tupleMatcher inconsistentArms ⟨0, 0⟩ =
        some (inconsistentGenerated, ⟨5, 3⟩) := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.armsExhaustive,
    MatchFirstTyping.structurallyIrrefutable,
    MatchFirstTyping.elaborateArmsUsing,
    MatchFirstTyping.elaborateTailUsing,
    MatchFirstTyping.GeneratedTail.fromArm,
    MatchFirstTyping.GeneratedArms.fromFirst,
    MatchFirstTyping.Generated.fromMatchFirst,
    inconsistentGenerated, inconsistentArms, tupleContext, tupleMatcher,
    tupleArm, tuplePattern, tupleBody, tupleType, elaboratePattern,
    elaboratePatterns, Pattern.extendContext, TypePM.Source.elaborate,
    elaborateItems, Scheme.mono, Scheme.instantiate, Supply.nextTy,
    Dual.targets, Dual.capabilities]

theorem close_inconsistent_none :
    inferGeneratedUsing unify inconsistentGenerated = none := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [inconsistentGenerated, tupleType]
  compute_unification

/-- All arm bodies must agree with the first body's direct result type. -/
theorem inconsistent_result_types_rejected :
    MatchFirstTyping.infer Paper1FrozenSignature.signature tupleContext
      (.var 0) tupleMatcher inconsistentArms = none := by
  unfold MatchFirstTyping.infer
  rw [show Context.initialSupply tupleContext = ⟨0, 0⟩ by rfl,
    elaborate_inconsistent_exact]
  simp [close_inconsistent_none]

def badMatcherGenerated : Generated :=
  { target := .prod [.var ⟨0⟩, .var ⟨1⟩]
    hard := [
      .ty (.prod [.var ⟨0⟩, .var ⟨1⟩]) tupleType]
    pending := [
      ⟨.int,
        .slot (.prod [.var ⟨0⟩, .var ⟨1⟩]) tupleType⟩] }

theorem elaborate_bad_matcher_exact :
    MatchFirstTyping.elaborate Paper1FrozenSignature.signature tupleContext
      (.var 0) (.lit 0) [tupleArm] ⟨0, 0⟩ =
        some (badMatcherGenerated, ⟨2, 2⟩) := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.armsExhaustive,
    MatchFirstTyping.structurallyIrrefutable,
    MatchFirstTyping.allStructurallyIrrefutable,
    MatchFirstTyping.elaborateArmsUsing,
    MatchFirstTyping.elaborateTailUsing,
    MatchFirstTyping.GeneratedArms.fromFirst,
    MatchFirstTyping.Generated.fromMatchFirst,
    badMatcherGenerated, tupleContext, tupleArm, tuplePattern, tupleBody,
    tupleType, elaboratePattern, elaboratePatterns, Pattern.extendContext,
    TypePM.Source.elaborate, elaborateItems, Scheme.mono,
    Scheme.instantiate, Supply.nextTy, Dual.targets, Dual.capabilities]

theorem close_bad_matcher_none :
    inferGeneratedUsing unify badMatcherGenerated = none := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [badMatcherGenerated, tupleType]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  rw [saturateLoop.eq_def]
  simp only
  compute_unification

/-- An integer is not a matcher and cannot satisfy the directional matcher
slot obligation created for the arm. -/
theorem bad_matcher_rejected :
    MatchFirstTyping.infer Paper1FrozenSignature.signature tupleContext
      (.var 0) (.lit 0) [tupleArm] = none := by
  unfold MatchFirstTyping.infer
  rw [show Context.initialSupply tupleContext = ⟨0, 0⟩ by rfl,
    elaborate_bad_matcher_exact]
  simp [close_bad_matcher_none]

def uncoveredArm : MatchFirstArm :=
  .mk (.ctor .cons [.var, .wild]) (.lit 0)

/-- A final constructor pattern can fail, so it is rejected before target or
matcher elaboration. -/
theorem uncovered_final_arm_rejected :
    MatchFirstTyping.elaborate Paper1FrozenSignature.signature tupleContext
      (.var 0) tupleMatcher [uncoveredArm] ⟨0, 0⟩ = none := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.armsExhaustive,
    MatchFirstTyping.structurallyIrrefutable, uncoveredArm]

end TypePM.Source.M4MatchFirstTypingRegression
