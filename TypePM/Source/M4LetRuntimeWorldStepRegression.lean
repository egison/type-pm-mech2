import TypePM.Source.M4LetRuntimeWorldStep
import TypePM.Source.M4CanonicalCertificateTransport
import TypePM.Source.M2Regression
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility

/-!
# Regression for the M4 `letE` source/runtime-world step

The closed fixture binds the identity function once and uses that generalized
binding independently at `Int` and at a matcher type.  Public M4 inference
selects the exact principal derivation passed to `letE_runtimeWorld`.

The regression observes only the static predecessor elaboration and the
canonical one-entry body context.  It contains no evaluator/search fuel and no
completed evaluation or search equation.
-/

namespace TypePM.Source.M4LetRuntimeWorldStepRegression

open TypePM.Runtime
open TypePM.Source.M4

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

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

def body : Expr :=
  .tuple [
    .app (.var 0) (.lit 1),
    .app (.var 0) .something]

def expression : Expr :=
  .letE (.lam (.var 0)) body

def resultType : Ty :=
  .prod [.int, .matcher .any (.var ⟨5⟩)]

private def identityValueGenerated : Generated :=
  { target := .fn (.var ⟨0⟩) (.var ⟨0⟩)
    hard := []
    pending := [] }

private def expressionGenerated : Generated :=
  { target := .prod [.var ⟨3⟩, .var ⟨7⟩]
    hard := [
      .ty (.fn (.var ⟨1⟩) (.var ⟨1⟩))
        (.fn (.var ⟨2⟩) (.var ⟨3⟩)),
      .ty (.fn (.var ⟨4⟩) (.var ⟨4⟩))
        (.fn (.var ⟨6⟩) (.var ⟨7⟩))]
    pending := [
      ⟨.int, .var ⟨2⟩⟩,
      ⟨.matcher .any (.var ⟨5⟩), .var ⟨6⟩⟩] }

private theorem unify_nil_exact : unify [] = some Subst.id := by
  unfold unify
  rw [unifyLoop.eq_def]

private theorem closeIdentityValue :
    inferGeneratedUsing unify identityValueGenerated = some
      { substitution := Subst.id
        target := .fn (.var ⟨0⟩) (.var ⟨0⟩) } := by
  simp [inferGeneratedUsing, identityValueGenerated, saturateUsing,
    saturateLoop, unify_nil_exact, promoteUnder, residualEquations]

private theorem expression_elaborate :
    M4.elaborate Paper1FrozenSignature.signature [] expression
      (Context.initialSupply []) =
        some (expressionGenerated, ⟨8, 0⟩) := by
  simp [M4.elaborate, M4.elaborateFuel, M4.elaborateFuelUsing,
    M4.elaborateItemsUsing, expression, body, identityValueGenerated,
    expressionGenerated, Generated.fromLam, closeIdentityValue,
    Context.initialSupply, Context.applyFree, Context.generalize,
    Context.generalizedTyVars, Context.generalizedCapVars,
    Context.freeTyVars, Context.freeCapVars, Context.interfaceEquations,
    Scheme.instantiate, Scheme.boundTyInstance, Scheme.boundCapInstance,
    Scheme.mono, Scheme.applyFree, Scheme.freeTyVars,
    Scheme.freeCapVars, PolyTy.ofTy, PolyTy.ofTyList, PolyTy.close,
    PolyTy.closeList, PolyTy.openBound, PolyTy.openBoundList,
    PolyTy.freeTyVars, PolyTy.freeTyVarsList, PolyTy.freeCapVars,
    PolyTy.freeCapVarsList, PolyCap.ofCap, PolyCap.ofCapList,
    PolyCap.close, PolyCap.closeList, PolyCap.openBound,
    PolyCap.openBoundList, PolyCap.freeCapVars, PolyCap.freeCapVarsList,
    Supply.nextTy, Supply.join, Generated.fromLet,
    TyVar.next, CapVar.next, dedup, dedupFirst, List.idxOf, List.findIdx,
    List.findIdx.go, Ty.tyVars, Ty.capVars, Cap.capVars, Cap.capVarsList,
    Ty.apply, Ty.applyList, Subst.id]
  have closeValue :
      inferGeneratedUsing unify
        { target := .fn (.var ⟨0⟩) (.var ⟨0⟩)
          hard := []
          pending := [] } =
        some
          { substitution := Subst.id
            target := .fn (.var ⟨0⟩) (.var ⟨0⟩) } := by
    simpa [identityValueGenerated] using closeIdentityValue
  rw [closeValue]
  rfl

private theorem closeExpressionTarget :
    (inferGeneratedUsing unify expressionGenerated).bind
      (fun closed => some closed.target) = some resultType := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [expressionGenerated]
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
  have matcherResolution :
      resolve (.matcher .any (.var ⟨5⟩)) (.var ⟨7⟩) =
        .ordinary (.matcher .any (.var ⟨5⟩)) (.var ⟨7⟩) := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [matcherResolution]
  simp [Resolution.equations]
  compute_unification
  rfl

theorem expression_shape :
    expression = .letE (.lam (.var 0)) body := by
  rfl

theorem expression_reuses_polymorphicIdentity :
    expression = M2Regression.polymorphicIdentity := by
  rfl

/-- The full M4 public entry point accepts the existing polymorphic fixture. -/
theorem expression_infer :
    M4.infer Paper1FrozenSignature.signature [] expression =
      some resultType := by
  unfold M4.infer
  rw [expression_elaborate]
  exact closeExpressionTarget

/-- The exact canonical derivation selected from public M4 inference. -/
noncomputable def derivation :
    M4.PrincipalTypingDerivation Paper1FrozenSignature.signature [] expression
      resultType :=
  M4.canonicalPrincipalTypingDerivation Paper1FrozenSignature.wellFormed
    expression_infer

/-- The principal `letE` exposes a nonempty body world from the empty source
and runtime contexts. -/
theorem runtimeWorld :
    ∃ fuel,
      Nonempty
        (M4.LetRuntimeWorld
          (signature := Paper1FrozenSignature.signature)
          (context := []) (value := .lam (.var 0)) (body := body)
          (supply := Context.initialSupply [])
          (generated := derivation.generated) (next := derivation.next)
          fuel derivation.closure.substitution [] []) := by
  exact derivation.letE_runtimeWorld ProtectedContextCompatible.nil rfl rfl

/-- Opening the world makes the source and runtime body extensions explicit:
the body source context begins with the generalized right-hand-side scheme,
the runtime context contains its canonical monotype, and the provenance mask
contains exactly one protected entry. -/
theorem bodyContext_isCanonicalSingleton :
    ∃ fuel,
      ∃ world : M4.LetRuntimeWorld
        (signature := Paper1FrozenSignature.signature)
        (context := []) (value := .lam (.var 0)) (body := body)
        (supply := Context.initialSupply [])
        (generated := derivation.generated) (next := derivation.next)
        fuel derivation.closure.substitution [] [],
      ProtectedContextCompatible
        (((Context.applyFree world.valueClosure.substitution []).generalize
            world.valueClosure.target) ::
          Context.applyFree world.valueClosure.substitution [])
        [(((Context.applyFree world.valueClosure.substitution []).generalize
            world.valueClosure.target).instantiate
              (Context.applyFree world.valueClosure.substitution
                []).initialSupply).1]
        [true] derivation.closure.substitution := by
  obtain ⟨fuel, ⟨world⟩⟩ := runtimeWorld
  exact ⟨fuel, world, world.bodyContextCompatible⟩

/-- The same canonical singleton world preserves both source/runtime and
runtime/provenance lengths after the `letE` body extension. -/
theorem bodyContext_lengthAlignment :
    ∃ fuel,
      ∃ world : M4.LetRuntimeWorld
        (signature := Paper1FrozenSignature.signature)
        (context := []) (value := .lam (.var 0)) (body := body)
        (supply := Context.initialSupply [])
        (generated := derivation.generated) (next := derivation.next)
        fuel derivation.closure.substitution [] [],
      ((((Context.applyFree world.valueClosure.substitution []).generalize
            world.valueClosure.target) ::
          Context.applyFree world.valueClosure.substitution []).length =
        [(((Context.applyFree world.valueClosure.substitution []).generalize
            world.valueClosure.target).instantiate
              (Context.applyFree world.valueClosure.substitution
                []).initialSupply).1].length) ∧
      ([(((Context.applyFree world.valueClosure.substitution []).generalize
            world.valueClosure.target).instantiate
              (Context.applyFree world.valueClosure.substitution
                []).initialSupply).1].length = [true].length) := by
  obtain ⟨fuel, ⟨world⟩⟩ := runtimeWorld
  exact ⟨fuel, world, world.bodySourceRuntimeLength,
    world.bodyRuntimeProvenanceLength⟩

/-- The enclosing `fromLet` solution has already been projected to the body
block, so a later body induction does not need to rewrite the parent block. -/
theorem bodySemantic_isAvailable :
    ∃ fuel,
      ∃ world : M4.LetRuntimeWorld
        (signature := Paper1FrozenSignature.signature)
        (context := []) (value := .lam (.var 0)) (body := body)
        (supply := Context.initialSupply [])
        (generated := derivation.generated) (next := derivation.next)
        fuel derivation.closure.substitution [] [],
      world.bodyGenerated.SemanticSolution
        derivation.closure.substitution := by
  obtain ⟨fuel, ⟨world⟩⟩ := runtimeWorld
  exact ⟨fuel, world, world.bodySemantic⟩

/-- The same world exposes the strict static-fuel predecessor: the value and
body derivations both use `fuel`, while rebuilding their enclosing `letE`
derivation uses exactly `fuel + 1`. -/
theorem bodyElaboration_atStrictStaticPredecessor :
    ∃ fuel,
      ∃ world : M4.LetRuntimeWorld
        (signature := Paper1FrozenSignature.signature)
        (context := []) (value := .lam (.var 0)) (body := body)
        (supply := Context.initialSupply [])
        (generated := derivation.generated) (next := derivation.next)
        fuel derivation.closure.substitution [] [],
      M4.ElaboratesFuel Paper1FrozenSignature.signature fuel
          ((Context.applyFree world.valueClosure.substitution []).generalize
              world.valueClosure.target ::
            Context.applyFree world.valueClosure.substitution [])
          body
          (world.afterValue.join
            (Context.applyFree world.valueClosure.substitution
              []).initialSupply)
          world.bodyGenerated derivation.next ∧
        M4.ElaboratesFuel Paper1FrozenSignature.signature (fuel + 1) []
          (.letE (.lam (.var 0)) body) (Context.initialSupply [])
          derivation.generated derivation.next := by
  obtain ⟨fuel, ⟨world⟩⟩ := runtimeWorld
  refine ⟨fuel, world, world.bodyElaboration, ?_⟩
  simp only [M4.ElaboratesFuel]
  exact ⟨world.valueGenerated, world.afterValue, world.valueElaboration,
    world.valueClosure, world.bodyGenerated, world.valueAbsorbing,
    world.bodyElaboration, world.generated_eq⟩

end TypePM.Source.M4LetRuntimeWorldStepRegression
