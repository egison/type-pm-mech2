import TypePM.Source.PolymorphicLetRuntimeBridge
import TypePM.Source.M2Regression

/-!
# Regression: a lambda captures one generalized identity

The generalized identity is outside the inner lambda.  Consequently its two
uses occur below a monomorphic lambda parameter in the runtime environment:
the mask there is `[false, true]`.  One use instantiates the identity at
`Int`; the other instantiates it at a matcher type.
-/

namespace TypePM.Source.PolymorphicLetProtectedClosureRegression

open TypePM.Runtime

set_option linter.unusedSimpArgs false

def capturedPolymorphicIdentity : Expr :=
  .letE
    (.lam (.var 0))
    (.app
      (.lam (.tuple [
        .app (.var 1) (.lit 1),
        .app (.var 1) .something
      ]))
      (.lit 0))

def resultType : Ty :=
  .prod [.int, .matcher .any (.var ⟨6⟩)]

def capturedGenerated : Generated :=
  { target := .var ⟨10⟩
    hard := [
      .ty (.fn (.var ⟨2⟩) (.var ⟨2⟩))
        (.fn (.var ⟨3⟩) (.var ⟨4⟩)),
      .ty (.fn (.var ⟨5⟩) (.var ⟨5⟩))
        (.fn (.var ⟨7⟩) (.var ⟨8⟩)),
      .ty (.fn (.var ⟨1⟩) (.prod [.var ⟨4⟩, .var ⟨8⟩]))
        (.fn (.var ⟨9⟩) (.var ⟨10⟩))]
    pending := [
      ⟨.int, .var ⟨3⟩⟩,
      ⟨.matcher .any (.var ⟨6⟩), .var ⟨7⟩⟩,
      ⟨.int, .var ⟨9⟩⟩] }

private theorem unify_nil_exact : unify [] = some Subst.id := by
  unfold unify
  rw [unifyLoop.eq_def]

private theorem closeIdentityAt (index : Nat) :
    inferGeneratedUsing unify
      { target := .fn (.var ⟨index⟩) (.var ⟨index⟩)
        hard := []
        pending := [] } = some
      { substitution := Subst.id
        target := .fn (.var ⟨index⟩) (.var ⟨index⟩) } := by
  simp [inferGeneratedUsing, saturateUsing, saturateLoop,
    unify_nil_exact, promoteUnder, residualEquations]

theorem elaborateCaptured :
    elaborateRoot Paper1Signature.signature [] capturedPolymorphicIdentity =
      some capturedGenerated := by
  simp [elaborateRoot, capturedPolymorphicIdentity, elaborate, elaborateItems,
    closeIdentityAt, capturedGenerated,
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
        Cap.occurs, Cap.occursList, Equation.apply, Ty.apply, Ty.applyList,
        Cap.apply, Cap.applyList, Subst.singleTy, Subst.singleCap,
        Subst.compose, Subst.id])

private theorem closeCaptured :
    (inferGeneratedUsing unify capturedGenerated).bind
      (fun closed => some closed.target) = some resultType := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [capturedGenerated]
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
      resolve (.matcher .any (.var ⟨6⟩)) (.var ⟨8⟩) =
        .ordinary (.matcher .any (.var ⟨6⟩)) (.var ⟨8⟩) := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [matcherResolution]
  simp [Resolution.equations]
  compute_unification
  rfl

private theorem checkConversion_fromInt_eq
    (conversion : CheckConversion conversionClass .int target) :
    Ty.int = target :=
  match conversion with
  | .ordinary => rfl

private theorem mem_of_mem_promoteUnder_pending
    (substitution : Subst) (obligation : CheckObligation) :
    ∀ pending,
      obligation ∈ (promoteUnder substitution pending).pending →
        obligation ∈ pending := by
  intro pending
  induction pending with
  | nil => simp [promoteUnder]
  | cons head tail induction =>
      simp only [promoteUnder]
      split
      · intro membership
        simp only [List.mem_cons] at membership ⊢
        exact membership.elim Or.inl (fun tailMembership =>
          Or.inr (induction tailMembership))
      · intro membership
        exact List.mem_cons_of_mem head (induction membership)

private theorem finalPending_mem_of_promotion
    (promotion : PromotionClosure hard pending finalHard finalPending)
    (membership : obligation ∈ finalPending) :
    obligation ∈ pending := by
  induction promotion with
  | refl => exact membership
  | @step hard pending substitution promoted finalHard finalPending
      _ promotedEq _ _ induction =>
      have promotedMembership : obligation ∈ promoted.pending :=
        induction membership
      rw [← promotedEq] at promotedMembership
      exact mem_of_mem_promoteUnder_pending substitution obligation pending
        promotedMembership

private theorem capturedPending_eq
    (closure : PrincipalBlockClosure capturedGenerated)
    (absorbing : closure.Absorbing)
    (targetEq : closure.target = resultType)
    (membership : obligation ∈ capturedGenerated.pending) :
    obligation.source.apply closure.substitution =
      obligation.expected.apply closure.substitution := by
  obtain ⟨conversionClass, conversion⟩ :=
    (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution closure).2
      obligation membership
  simp only [capturedGenerated, List.mem_cons, List.not_mem_nil, or_false]
    at membership
  rcases membership with rfl | rfl | rfl
  · exact checkConversion_fromInt_eq conversion
  · have hardSecond := closure.finalHard_solved
      (.ty (.fn (.var ⟨5⟩) (.var ⟨5⟩))
        (.fn (.var ⟨7⟩) (.var ⟨8⟩)))
      (closure.saturation.closure.hard_mem_final _ (by
        simp [capturedGenerated]))
    have hardThird := closure.finalHard_solved
      (.ty (.fn (.var ⟨1⟩) (.prod [.var ⟨4⟩, .var ⟨8⟩]))
        (.fn (.var ⟨9⟩) (.var ⟨10⟩)))
      (closure.saturation.closure.hard_mem_final _ (by
        simp [capturedGenerated]))
    have closureTargetEq := targetEq
    simp [Equation.Holds, PrincipalBlockClosure.target, capturedGenerated,
      resultType, Ty.apply] at hardSecond hardThird targetEq
    have productItems := Ty.prod.inj (hardThird.2.trans targetEq)
    simp [Ty.applyList, Ty.apply] at productItems
    have targetFixed : closure.target.apply closure.substitution =
        closure.target := by
      unfold PrincipalBlockClosure.target
      rw [Ty.apply_compose, closure.substitution_idempotent absorbing]
    rw [closureTargetEq] at targetFixed
    simp [resultType, Ty.apply, Ty.applyList] at targetFixed
    change Ty.matcher Cap.any (closure.substitution.ty ⟨6⟩) =
      closure.substitution.ty ⟨7⟩
    rw [targetFixed.2]
    exact productItems.2.symm.trans
      (hardSecond.2.symm.trans hardSecond.1)
  · exact checkConversion_fromInt_eq conversion

private theorem capturedClosure_remainingChecksOrdinary
    (closure : PrincipalBlockClosure capturedGenerated)
    (absorbing : closure.Absorbing)
    (targetEq : closure.target = resultType) :
    ClosureRemainingChecksOrdinary closure := by
  intro obligation membership
  have originalMembership : obligation ∈ capturedGenerated.pending :=
    finalPending_mem_of_promotion closure.saturation.closure membership
  have equality := capturedPending_eq closure absorbing targetEq
    originalMembership
  rw [equality]
  exact .ordinary

private theorem capturedClosure_strict
    (closure : PrincipalBlockClosure capturedGenerated)
    (absorbing : closure.Absorbing)
    (targetEq : closure.target = resultType) :
    StrictGeneratedSemanticSolution capturedGenerated closure.substitution :=
  strictSemanticSolution_of_closure closure
    (capturedClosure_remainingChecksOrdinary closure absorbing targetEq)

private theorem capturedPrincipalClosure :
    ∃ closure : PrincipalBlockClosure capturedGenerated,
      closure.Absorbing ∧ closure.target = resultType := by
  have closedTarget := closeCaptured
  cases closedEq : inferGeneratedUsing unify capturedGenerated with
  | none =>
      simp [closedEq] at closedTarget
  | some closed =>
      have closedTargetEq : closed.target = resultType := by
        simpa [closedEq] using closedTarget
      obtain ⟨closure, _, targetEq, absorbing⟩ :=
        inferGeneratedUsing_absorbingPrincipalBlockClosure
          unify_absorbingMGUSolver closedEq
      exact ⟨closure, absorbing, targetEq.symm.trans closedTargetEq⟩

private theorem capturedRelationalElaboration :
    ∃ next,
      Elaborates Paper1Signature.signature [] capturedPolymorphicIdentity
        (Context.initialSupply []) capturedGenerated next := by
  have rootEq := elaborateCaptured
  unfold elaborateRoot at rootEq
  cases elaborated :
      elaborate Paper1Signature.signature [] capturedPolymorphicIdentity
        (Context.initialSupply []) with
  | none => simp [elaborated] at rootEq
  | some output =>
      rcases output with ⟨generated, next⟩
      simp only [elaborated, Option.map_some, Option.some.injEq] at rootEq
      subst generated
      exact ⟨next, elaborate_sound Paper1Signature.wellFormed elaborated⟩

/-- Public M2 inference computes the same type used by the protected closure
runtime derivation below. -/
theorem infer_capturedPolymorphicIdentity_exact :
    infer Paper1Signature.signature [] capturedPolymorphicIdentity =
      some resultType := by
  unfold infer
  rw [elaborateCaptured]
  exact closeCaptured

/-- The captured example is connected to the independent relational source
typing judgment through public inference soundness. -/
theorem capturedPolymorphicIdentity_sourceTyping :
    Typing Paper1Signature.signature [] capturedPolymorphicIdentity
      resultType :=
  Inference.infer_success_typing Paper1Signature.wellFormed
    infer_capturedPolymorphicIdentity_exact

/-- The actual inferred `letE` boundary supplies the support-separation fact
for the generalized identity before the closure body is translated. -/
theorem capturedPolymorphicIdentity_actualLetBoundarySeparated :
    ClosedLetBoundVariableSupportSeparated Paper1Signature.signature
      (.lam (.var 0))
      (.app
        (.lam (.tuple [
          .app (.var 1) (.lit 1),
          .app (.var 1) .something]))
        (.lit 0)) := by
  apply inferSuccessClosedLetBoundVariableSupportSeparated
    Paper1Signature.wellFormed
  simpa [capturedPolymorphicIdentity] using
    infer_capturedPolymorphicIdentity_exact

/-- The complete expression surrounding the generalized variable uses lies
in the syntax-directed single-closure bridge fragment.  The outer `letE`
boundary is handled separately by
`inferSuccessClosedLetBoundVariableSupportSeparated`. -/
theorem capturedBody_bridgeSupported :
    ProtectedClosureBodySupported
      (.app
        (.lam (.tuple [
          .app (.var 1) (.lit 1),
          .app (.var 1) .something]))
        (.lit 0)) :=
  .app
    (.lam (.tuple (.cons (.app .var .lit)
      (.cons (.app .var .something) .nil))))
    .lit


private theorem capturedPolymorphicIdentity_runtimeTypingFromElaboration :
    ProtectedClosureRuntimeTyping [] capturedPolymorphicIdentity resultType [] := by
  obtain ⟨rootClosure, rootAbsorbing, rootTargetEq⟩ := capturedPrincipalClosure
  obtain ⟨next, outerElaboration⟩ := capturedRelationalElaboration
  generalize generatedEq : capturedGenerated = generated at outerElaboration
  cases outerElaboration with
  | @letE _ _ _ _ generatedValue afterValue generatedBody _
      valueElaboration valueClosure valueAbsorbing bodyElaboration =>
      have valueTargetShape : ∃ domain,
          valueClosure.target = .fn domain domain := by
        cases valueElaboration with
        | lam bodyElaboration =>
            cases bodyElaboration with
            | var lookup =>
                simp at lookup
                subst_vars
                refine ⟨valueClosure.substitution.ty ⟨0⟩, ?_⟩
                rfl
      obtain ⟨valueDomain, valueTargetEq⟩ := valueTargetShape
      let scheme := (Context.applyFree valueClosure.substitution []).generalize
        valueClosure.target
      let canonicalSupply : Supply := ⟨0, 0⟩
      let general := (scheme.instantiate canonicalSupply).1
      have generalShape : ∃ domain, general = .fn domain domain := by
        dsimp [general, scheme]
        rw [valueTargetEq]
        simp [canonicalSupply, Context.applyFree,
          Context.generalize, Context.generalizedTyVars,
          Context.generalizedCapVars, Context.freeTyVars,
          Context.freeCapVars, Scheme.instantiate, Scheme.boundTyInstance,
          Scheme.boundCapInstance, PolyTy.close, PolyTy.openBound,
          PolyTy.freeTyVars, PolyTy.freeCapVars, Ty.tyVars, Ty.capVars,
          Cap.capVars, dedupFirst, dedup]
      obtain ⟨generalDomain, generalEq⟩ := generalShape
      apply ProtectedClosureRuntimeTyping.letPoly (general := general)
      · rw [generalEq]
        exact .runtime (.lam (.var rfl))
      · simp [Context.interfaceEquations, Context.freeTyVars,
          Context.freeCapVars, Generated.fromLet, dedupFirst, dedup] at generatedEq
        have generatedBodyEq : capturedGenerated = generatedBody := generatedEq
        subst generatedBody
        have bodySemantic := capturedClosure_strict rootClosure
          rootAbsorbing rootTargetEq
        have contextCompatible :
            ProtectedContextCompatible
              ((Context.applyFree valueClosure.substitution []).generalize
                  valueClosure.target ::
                Context.applyFree valueClosure.substitution [])
              [general] [true] rootClosure.substitution := by
          apply ProtectedContextCompatible.pushCanonical
              (canonicalSupply := canonicalSupply)
          · intro index membership
            have impossible :=
              (Context.mem_generalize_freeTyVars.mp membership).2
            simp [Context.applyFree, Context.freeTyVars, dedupFirst, dedup]
              at impossible
          · intro index membership
            have impossible :=
              (Context.mem_generalize_freeCapVars.mp membership).2
            simp [Context.applyFree, Context.freeCapVars, dedupFirst, dedup]
              at impossible
          · exact ProtectedContextCompatible.nil
        rw [← rootTargetEq]
        exact
          capturedBody_bridgeSupported.elaboration_typing
            paper1SignatureCompatible bodyElaboration bodySemantic
              contextCompatible

/-- The outer lambda captures the generalized identity.  The principal source
closure, canonical generalized representative, and the relational body
elaboration now construct the runtime derivation; no occurrence-specific
runtime derivation is supplied by hand. -/
theorem capturedPolymorphicIdentity_protectedClosureRuntimeTyping :
    ProtectedClosureRuntimeTyping [] capturedPolymorphicIdentity resultType :=
  capturedPolymorphicIdentity_runtimeTypingFromElaboration

/-- The protected closure certificate is anchored in the principal
relational derivation recovered from the public inference result. -/
theorem capturedPolymorphicIdentity_protectedClosureProvenanced :
    ProtectedClosureProvenancedRuntimeTyping Paper1Signature.signature
      capturedPolymorphicIdentity resultType :=
  Inference.infer_success_protectedClosureRuntimeTyping
    Paper1Signature.wellFormed infer_capturedPolymorphicIdentity_exact
    capturedPolymorphicIdentity_protectedClosureRuntimeTyping

/-- Evaluation either times out or returns a value at the protected runtime
type, including the protected closure-application path. -/
theorem capturedPolymorphicIdentity_typedResult (fuel : Nat) :
    ProtectedClosureTypedResult resultType
      (evalFuel fuel [] capturedPolymorphicIdentity) :=
  capturedPolymorphicIdentity_protectedClosureProvenanced.coreSafety fuel

/-- Capturing a generalized identity below a lambda cannot lead to `stuck`. -/
theorem capturedPolymorphicIdentity_neverStuck (fuel : Nat) :
    (evalFuel fuel [] capturedPolymorphicIdentity).NotStuck :=
  capturedPolymorphicIdentity_protectedClosureProvenanced.neverStuck fuel

/-- Both differently typed uses execute through the identity closure captured
by the outer lambda. -/
theorem capturedPolymorphicIdentity_exactEvaluation :
    evalFuel 7 [] capturedPolymorphicIdentity =
      .ok (.tuple [.int 1, .something]) := by
  with_unfolding_all rfl

end TypePM.Source.PolymorphicLetProtectedClosureRegression
