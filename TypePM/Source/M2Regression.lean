import TypePM.Source.Elaboration
import TypePM.Source.FullM2Completion

/-!
# M2 source regressions

These kernel-checked examples exercise polymorphic `letE`, the explicit-let
example from the paper, and rejection at the closed right-hand-side boundary.
-/

namespace TypePM.Source.M2Regression

set_option linter.unusedSimpArgs false

def slotInt : Ty := .slot .any .int
def consumerFunction : Ty := .fn slotInt .int
def requireSlotType : Ty := .fn consumerFunction .int
def requireSlotContext : Context := [.mono requireSlotType]

def polymorphicIdentity : Expr :=
  .letE (.lam (.var 0))
    (.tuple [
      .app (.var 0) (.lit 1),
      .app (.var 0) .something])

def explicitLet : Expr :=
  .lam
    (.letE
      (.app (.var 1) (.var 0))
      (.tuple [
        .app (.var 1) .something,
        .var 0]))

def cutRejectsBackflow : Expr :=
  .lam
    (.letE
      (.app (.var 1) (.var 0))
      (.app (.var 1) (.lam (.var 0))))

private def explicitValueGenerated : Generated :=
  { target := .var ⟨2⟩
    hard := [
      .ty requireSlotType
        (.fn (.var ⟨1⟩) (.var ⟨2⟩))]
    pending := [⟨.var ⟨0⟩, .var ⟨1⟩⟩] }

private def explicitValueSubstitution : Subst :=
  Subst.compose (Subst.singleTy ⟨0⟩ consumerFunction)
    (Subst.compose (Subst.singleTy ⟨2⟩ .int)
      (Subst.singleTy ⟨1⟩ consumerFunction))

private theorem unify_nil_exact : unify [] = some Subst.id := by
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

private theorem closeExplicitValue :
    inferGeneratedUsing unify explicitValueGenerated = some
      { substitution := explicitValueSubstitution
        target := .int } := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [explicitValueGenerated, requireSlotType, consumerFunction,
    slotInt]
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
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  rw [unifyLoop.eq_def]
  simp [explicitValueSubstitution, Ty.apply, Ty.applyList, Cap.apply,
    Cap.applyList, Subst.compose, Subst.id, funext_iff]
  constructor
  · intro index
    rfl
  · intro index
    by_cases atZero : index = ⟨0⟩
    · subst index
      simp [Subst.singleTy, Ty.apply, Cap.apply, consumerFunction, slotInt]
    · by_cases atOne : index = ⟨1⟩
      · subst index
        simp [Subst.singleTy, Ty.apply, Cap.apply, consumerFunction, slotInt]
      · by_cases atTwo : index = ⟨2⟩
        · subst index
          simp [Subst.singleTy, Ty.apply, Cap.apply, consumerFunction, slotInt]
        · simp [Subst.singleTy, Ty.apply, Cap.apply, atZero, atOne, atTwo]

private def identityValueGenerated : Generated :=
  { target := .fn (.var ⟨0⟩) (.var ⟨0⟩)
    hard := []
    pending := [] }

private theorem closeIdentityValue :
    inferGeneratedUsing unify identityValueGenerated = some
      { substitution := Subst.id
        target := .fn (.var ⟨0⟩) (.var ⟨0⟩) } := by
  simp [inferGeneratedUsing, identityValueGenerated, saturateUsing,
    saturateLoop, unify_nil_exact, promoteUnder, residualEquations]

private theorem closeIdentityAt (index : Nat) :
    inferGeneratedUsing unify
      { target := .fn (.var ⟨index⟩) (.var ⟨index⟩)
        hard := []
        pending := [] } = some
      { substitution := Subst.id
        target := .fn (.var ⟨index⟩) (.var ⟨index⟩) } := by
  simp [inferGeneratedUsing, saturateUsing, saturateLoop,
    unify_nil_exact, promoteUnder, residualEquations]

private def polymorphicIdentityGenerated : Generated :=
  { target := .prod [.var ⟨3⟩, .var ⟨7⟩]
    hard := [
      .ty (.fn (.var ⟨1⟩) (.var ⟨1⟩))
        (.fn (.var ⟨2⟩) (.var ⟨3⟩)),
      .ty (.fn (.var ⟨4⟩) (.var ⟨4⟩))
        (.fn (.var ⟨6⟩) (.var ⟨7⟩))]
    pending := [
      ⟨.int, .var ⟨2⟩⟩,
      ⟨.matcher .any (.var ⟨5⟩), .var ⟨6⟩⟩] }

private def explicitLetGenerated : Generated :=
  { target := .fn (.var ⟨0⟩) (.prod [.var ⟨5⟩, .int])
    hard := [
      .ty (.var ⟨0⟩) consumerFunction,
      .ty consumerFunction (.fn (.var ⟨4⟩) (.var ⟨5⟩))]
    pending := [
      ⟨.matcher .any (.var ⟨3⟩), .var ⟨4⟩⟩] }

private def cutGenerated : Generated :=
  { target := .fn (.var ⟨0⟩) (.var ⟨5⟩)
    hard := [
      .ty (.var ⟨0⟩) consumerFunction,
      .ty consumerFunction (.fn (.var ⟨4⟩) (.var ⟨5⟩))]
    pending := [
      ⟨.fn (.var ⟨3⟩) (.var ⟨3⟩), .var ⟨4⟩⟩] }

private theorem elaborateExplicitValue :
    elaborate Paper1Signature.signature
      (.mono (.var ⟨0⟩) :: requireSlotContext)
      (.app (.var 1) (.var 0)) ⟨1, 0⟩ =
        some (explicitValueGenerated, ⟨3, 0⟩) := by
  simp [elaborate, explicitValueGenerated, requireSlotContext,
    requireSlotType, consumerFunction, Scheme.mono, Scheme.instantiate,
    Scheme.boundTyInstance, Scheme.boundCapInstance, PolyTy.ofTy,
    PolyTy.ofTyList, PolyTy.openBound, PolyTy.openBoundList,
    PolyCap.ofCap, PolyCap.ofCapList, PolyCap.openBound,
    PolyCap.openBoundList, Supply.nextTy]

private theorem elaboratePolymorphicIdentity :
    elaborateRoot Paper1Signature.signature [] polymorphicIdentity =
      some polymorphicIdentityGenerated := by
  simp [elaborateRoot, polymorphicIdentity, elaborate, elaborateItems,
    closeIdentityAt, closeIdentityValue, identityValueGenerated,
    polymorphicIdentityGenerated,
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
    List.findIdx.go,
    Ty.tyVars, Ty.capVars, Cap.capVars, Cap.capVarsList,
    Ty.apply, Ty.applyList, Subst.id]

private theorem elaborateExplicitLetPair :
    elaborate Paper1Signature.signature requireSlotContext explicitLet ⟨0, 0⟩ =
      some (explicitLetGenerated, ⟨6, 0⟩) := by
  rw [show explicitLet = .lam
    (.letE (.app (.var 1) (.var 0))
      (.tuple [.app (.var 1) .something, .var 0])) by rfl]
  rw [elaborate]
  simp only [Supply.nextTy]
  rw [elaborate]
  rw [elaborateExplicitValue]
  simp [closeExplicitValue, elaborate, elaborateItems,
    explicitValueSubstitution,
    explicitLetGenerated, requireSlotContext, requireSlotType,
    consumerFunction, slotInt,
    Context.initialSupply, Context.applyFree, Context.generalize,
    Context.generalizedTyVars, Context.generalizedCapVars,
    Context.freeTyVars, Context.freeCapVars, Context.interfaceEquations,
    Scheme.instantiate, Scheme.boundTyInstance, Scheme.boundCapInstance,
    Scheme.mono, Scheme.applyFree, Scheme.freeTyVars,
    Scheme.freeCapVars, PolyTy.ofTy, PolyTy.ofTyList, PolyTy.close,
    PolyTy.closeList, PolyTy.openBound, PolyTy.openBoundList,
    PolyTy.applyFree, PolyTy.applyFreeList, PolyTy.freeTyVars,
    PolyTy.freeTyVarsList, PolyTy.freeCapVars, PolyTy.freeCapVarsList,
    PolyCap.ofCap, PolyCap.ofCapList, PolyCap.close, PolyCap.closeList,
    PolyCap.openBound, PolyCap.openBoundList, PolyCap.applyFree,
    PolyCap.applyFreeList, PolyCap.freeCapVars, PolyCap.freeCapVarsList,
    Supply.nextTy, Supply.join, Generated.fromLet,
    TyVar.next, CapVar.next, dedup, dedupFirst, List.idxOf, List.findIdx,
    List.findIdx.go,
    Ty.tyVars, Ty.capVars, Cap.capVars, Cap.capVarsList,
    Ty.apply, Ty.applyList, Subst.singleTy, Subst.compose, Subst.id]
private theorem elaborateExplicitLet :
    elaborateRoot Paper1Signature.signature requireSlotContext explicitLet =
      some explicitLetGenerated := by
  unfold elaborateRoot
  rw [show Context.initialSupply requireSlotContext = ⟨0, 0⟩ by rfl]
  rw [elaborateExplicitLetPair]
  rfl

private theorem elaborateCutPair :
    elaborate Paper1Signature.signature requireSlotContext cutRejectsBackflow ⟨0, 0⟩ =
      some (cutGenerated, ⟨6, 0⟩) := by
  rw [show cutRejectsBackflow = .lam
    (.letE (.app (.var 1) (.var 0))
      (.app (.var 1) (.lam (.var 0)))) by rfl]
  rw [elaborate]
  simp only [Supply.nextTy]
  rw [elaborate]
  rw [elaborateExplicitValue]
  simp [closeExplicitValue, elaborate, explicitValueSubstitution, cutGenerated,
    requireSlotContext, requireSlotType, consumerFunction, slotInt,
    Context.initialSupply, Context.applyFree, Context.generalize,
    Context.generalizedTyVars, Context.generalizedCapVars,
    Context.freeTyVars, Context.freeCapVars, Context.interfaceEquations,
    Scheme.instantiate, Scheme.boundTyInstance, Scheme.boundCapInstance,
    Scheme.mono, Scheme.applyFree, Scheme.freeTyVars,
    Scheme.freeCapVars, PolyTy.ofTy, PolyTy.ofTyList, PolyTy.close,
    PolyTy.closeList, PolyTy.openBound, PolyTy.openBoundList,
    PolyTy.applyFree, PolyTy.applyFreeList, PolyTy.freeTyVars,
    PolyTy.freeTyVarsList, PolyTy.freeCapVars, PolyTy.freeCapVarsList,
    PolyCap.ofCap, PolyCap.ofCapList, PolyCap.close, PolyCap.closeList,
    PolyCap.openBound, PolyCap.openBoundList, PolyCap.applyFree,
    PolyCap.applyFreeList, PolyCap.freeCapVars, PolyCap.freeCapVarsList,
    Supply.nextTy, Supply.join, Generated.fromLet,
    TyVar.next, CapVar.next, dedup, dedupFirst, List.idxOf, List.findIdx,
    List.findIdx.go,
    Ty.tyVars, Ty.capVars, Cap.capVars, Cap.capVarsList,
    Ty.apply, Ty.applyList, Subst.singleTy, Subst.compose, Subst.id]

private theorem elaborateCut :
    elaborateRoot Paper1Signature.signature requireSlotContext cutRejectsBackflow =
      some cutGenerated := by
  unfold elaborateRoot
  rw [show Context.initialSupply requireSlotContext = ⟨0, 0⟩ by rfl]
  rw [elaborateCutPair]
  rfl

private theorem closePolymorphicIdentityTarget :
    (inferGeneratedUsing unify polymorphicIdentityGenerated).bind
      (fun closed => some closed.target) =
      some (.prod [.int, .matcher .any (.var ⟨5⟩)]) := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only
  simp only [polymorphicIdentityGenerated]
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

def explicitLetType : Ty :=
  .fn consumerFunction (.prod [.int, .int])

private theorem closeExplicitLetTarget :
    (inferGeneratedUsing unify explicitLetGenerated).bind
      (fun closed => some closed.target) = some explicitLetType := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only
  simp only [explicitLetGenerated, consumerFunction, slotInt]
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
  rfl

private theorem closeCutNone :
    inferGeneratedUsing unify cutGenerated = none := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [cutGenerated, requireSlotType, consumerFunction, slotInt]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  simp only [saturateLoop]
  compute_unification

/-- The generalized identity is instantiated independently at `Int` and at a
matcher type. -/
theorem infer_polymorphicIdentity_exact : infer Paper1Signature.signature [] polymorphicIdentity =
    some (.prod [.int, .matcher .any (.var ⟨5⟩)]) := by
  unfold infer
  rw [elaboratePolymorphicIdentity]
  exact closePolymorphicIdentityTarget

/-- The explicit-let example from the paper has the intended function type. -/
theorem infer_explicitLet_exact :
    infer Paper1Signature.signature requireSlotContext explicitLet = some explicitLetType := by
  unfold infer
  rw [elaborateExplicitLet]
  exact closeExplicitLetTarget

theorem polymorphicIdentityTyping :
    Typing Paper1Signature.signature [] polymorphicIdentity
      (.prod [.int, .matcher .any (.var ⟨5⟩)]) :=
  Inference.infer_success_typing Paper1Signature.wellFormed
    infer_polymorphicIdentity_exact

theorem explicitLetTyping :
    Typing Paper1Signature.signature requireSlotContext explicitLet explicitLetType :=
  Inference.infer_success_typing Paper1Signature.wellFormed
    infer_explicitLet_exact

/-- Closing the right-hand side fixes `f` before the body tries to apply it to
an incompatible function argument.  The body demand is not allowed to flow
back into the already closed right-hand-side block. -/
theorem infer_cutRejectsBackflow_none :
    infer Paper1Signature.signature requireSlotContext cutRejectsBackflow = none := by
  unfold infer
  rw [elaborateCut]
  simp [closeCutNone]

/-- Full M2 completeness turns the executable full-cut rejection into a
declarative non-typability result. -/
theorem cutRejectsBackflow_not_typable :
    ¬ Typable Paper1Signature.signature requireSlotContext cutRejectsBackflow := by
  intro typable
  have accepted := (Inference.typable_iff_infer_isSome
    Paper1Signature.signature Paper1Signature.wellFormed
    requireSlotContext cutRejectsBackflow).mp typable
  exact accepted infer_cutRejectsBackflow_none


end TypePM.Source.M2Regression
