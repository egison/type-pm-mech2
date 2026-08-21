import TypePM.Source.M5ClosedPairProjectionCertificate
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility

/-!
# Regression for the first concrete M5 certificate

The fixture is closed and genuinely nested: its outer first projection selects
the result of an inner second projection.  Static acceptance is anchored at
the public M4 `infer` and `Typing` interfaces, while arbitrary-fuel no-stuck is
obtained from the concrete M5 certificate package.
-/

namespace TypePM.Source.M5ClosedPairProjectionCertificateRegression

open TypePM.Runtime
open TypePM.Source.M5CompletionArchitecture
open TypePM.Source.M5ClosedPairProjectionCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
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

def nestedProjection : Expr :=
  .prim PrimOp.pairFirst [
    .tuple [
      .prim PrimOp.pairSecond [.tuple [.lit 1, .lit 2]],
      .lit 3]]

theorem nestedProjection_fragment : Fragment nestedProjection .int := by
  exact .pairFirst (.pairSecond (.lit 1) (.lit 2)) (.lit 3)

theorem nestedProjection_supported : Supported nestedProjection :=
  ⟨.int, nestedProjection_fragment⟩

theorem nestedProjection_mnodeFree : nestedProjection.MNodeFree :=
  nestedProjection_fragment.mnodeFree

private def nestedProjectionGenerated : Generated :=
  { target := .var ⟨7⟩
    hard := [
      .ty
        (.fn (.prod [.var ⟨2⟩, .var ⟨3⟩]) (.var ⟨3⟩))
        (.fn (.var ⟨4⟩) (.var ⟨5⟩)),
      .ty
        (.fn (.prod [.var ⟨0⟩, .var ⟨1⟩]) (.var ⟨0⟩))
        (.fn (.var ⟨6⟩) (.var ⟨7⟩))]
    pending := [
      ⟨.prod [.int, .int], .var ⟨4⟩⟩,
      ⟨.prod [.var ⟨5⟩, .int], .var ⟨6⟩⟩] }

private theorem nestedProjection_elaborate :
    M4.elaborate Paper1FrozenSignature.signature [] nestedProjection
        (Context.initialSupply []) =
      some (nestedProjectionGenerated, ⟨8, 0⟩) := by
  rfl'

private theorem nestedProjection_close :
    (inferGeneratedUsing unify nestedProjectionGenerated).bind
      (fun closed => some closed.target) = some .int := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [nestedProjectionGenerated]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  rw [saturateLoop.eq_def]
  simp [promoteUnder, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
    Subst.compose, Subst.id, Subst.singleTy, Subst.singleCap]
  compute_unification
  simp [residualEquations, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
    Subst.compose, Subst.id, Subst.singleTy, Subst.singleCap]
  compute_unification

/-- The fixture is accepted by the executable public M4 entry point. -/
theorem nestedProjection_infer :
    M4.infer Paper1FrozenSignature.signature [] nestedProjection = some .int := by
  unfold M4.infer
  rw [nestedProjection_elaborate]
  exact nestedProjection_close

/-- The declarative public typing follows from public-inference soundness. -/
theorem nestedProjection_typing :
    M4.Typing Paper1FrozenSignature.signature [] nestedProjection .int :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    nestedProjection_infer

private theorem signatureReady :
    RuntimeSignatureReady Paper1FrozenSignature.signature :=
  ⟨Paper1FrozenSignature.wellFormed,
    Paper1FrozenSignature.runtimeCompatible.toSignatureCompatible⟩

/-- Every fuel amount yields timeout or a value; `stuck` is impossible. -/
theorem nestedProjection_neverStuck (fuel : Nat) :
    (evalFuel fuel [] nestedProjection).NotStuck :=
  closedNoStuck signatureReady nestedProjection_supported
    nestedProjection_typing fuel

/-- The regression keeps both public static endpoints and the arbitrary-fuel
runtime endpoint visible in one statement. -/
theorem publicInferTypingAndNoStuck :
    M4.infer Paper1FrozenSignature.signature [] nestedProjection = some .int ∧
      M4.Typing Paper1FrozenSignature.signature [] nestedProjection .int ∧
        ∀ fuel, (evalFuel fuel [] nestedProjection).NotStuck :=
  ⟨nestedProjection_infer, nestedProjection_typing,
    nestedProjection_neverStuck⟩

end TypePM.Source.M5ClosedPairProjectionCertificateRegression
