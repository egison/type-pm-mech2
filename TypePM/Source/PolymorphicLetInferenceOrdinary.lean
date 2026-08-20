import TypePM.Source.PolymorphicLetProtectedSyntaxRegression
import TypePM.Source.PolymorphicLetProtectedClosureRegression

/-!
# Executable ordinary-residual certificates for the protected let bridge

The protected runtime bridge needs ordinary equality for the checks left by
hard-constraint saturation.  That fact is not true for arbitrary M4 checks.
This module therefore records a narrow, executable certificate: for the
actual generated block, every residual resolution selected by the concrete
saturation result is the ordinary branch.
-/

namespace TypePM

/-- The concrete hard-saturation result for `generated` leaves only ordinary
resolutions.  Unlike an unrestricted `ClosureRemainingChecksOrdinary`
assumption, this proposition is tied to the executable generated block and
can be reduced for a fixed source fixture. -/
def ExecutableResidualsOrdinary (generated : Generated) : Prop :=
  ∀ output,
    saturateUsing unify generated.hard generated.pending = some output →
      ∀ obligation ∈ output.pending,
        (obligation.resolutionUnder output.substitution).conversionClass =
          .ordinary

/-- Executable form of `ExecutableResidualsOrdinary`.  Failure of hard
saturation is rejected; successful saturation checks exactly the residual
list and substitution returned by the public procedure. -/
def executableResidualsOrdinaryCheckUsing
    (solve : List Equation → Option Subst) (generated : Generated) : Bool :=
  match saturateUsing solve generated.hard generated.pending with
  | none => false
  | some output => output.pending.all fun obligation =>
      (obligation.resolutionUnder output.substitution).conversionClass ==
        .ordinary

def executableResidualsOrdinaryCheck (generated : Generated) : Bool :=
  executableResidualsOrdinaryCheckUsing unify generated

theorem executableResidualsOrdinaryCheck_unify_of_fuel
    {solverFuel : Nat} {generated : Generated}
    (checked : executableResidualsOrdinaryCheckUsing
      (unifyWithFuel solverFuel) generated = true) :
    executableResidualsOrdinaryCheck generated = true := by
  unfold executableResidualsOrdinaryCheck
  unfold executableResidualsOrdinaryCheckUsing at checked ⊢
  cases fuelSaturation : saturateUsing (unifyWithFuel solverFuel)
      generated.hard generated.pending with
  | none => simp [fuelSaturation] at checked
  | some output =>
      have publicSaturation := saturateUsing_success_transport
        unify_eq_of_unifyWithFuel_success fuelSaturation
      rw [fuelSaturation] at checked
      rw [publicSaturation]
      exact checked

theorem ExecutableResidualsOrdinary.of_check
    {generated : Generated}
    (checked : executableResidualsOrdinaryCheck generated = true) :
    ExecutableResidualsOrdinary generated := by
  intro output success obligation membership
  simp only [executableResidualsOrdinaryCheck,
    executableResidualsOrdinaryCheckUsing, success, List.all_eq_true,
    beq_iff_eq] at checked
  exact checked obligation membership

private theorem residualEquations_ordinary_sound
    {hardSubstitution residualSubstitution : Subst}
    {obligations : List CheckObligation}
    (solved : Solves residualSubstitution
      (residualEquations hardSubstitution obligations))
    (ordinary : ∀ obligation ∈ obligations,
      (obligation.resolutionUnder hardSubstitution).conversionClass =
        .ordinary) :
    ∀ obligation ∈ obligations,
      CheckConversion .ordinary
        ((obligation.source.apply hardSubstitution).apply residualSubstitution)
        ((obligation.expected.apply hardSubstitution).apply
          residualSubstitution) := by
  induction obligations with
  | nil => simp
  | cons head tail induction =>
      simp only [residualEquations] at solved
      obtain ⟨headSolved, tailSolved⟩ :=
        (solves_append residualSubstitution _ _).mp solved
      intro obligation membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · let resolution :=
          CheckObligation.resolutionUnder hardSubstitution obligation
        have sound := resolution.sound headSolved
        have ordinaryBranch := ordinary obligation (by simp)
        rw [ordinaryBranch] at sound
        exact sound
      · exact induction tailSolved
          (fun candidate candidateMembership =>
            ordinary candidate (by simp [candidateMembership]))
          obligation membership

/-- Successful executable closure plus the residual-branch certificate
constructs the same principal closure data as public inference, now carrying
the ordinary-check proof required by the protected runtime bridge. -/
theorem inferGeneratedUsing_ordinaryPrincipalBlockClosure
    {generated : Generated} {result : InferenceResult}
    (success : inferGeneratedUsing unify generated = some result)
    (ordinary : ExecutableResidualsOrdinary generated) :
    ∃ closure : PrincipalBlockClosure generated,
      result.substitution = closure.substitution ∧
      result.target = closure.target ∧ closure.Absorbing ∧
      Runtime.ClosureRemainingChecksOrdinary closure := by
  unfold inferGeneratedUsing at success
  cases saturationResult :
      saturateUsing unify generated.hard generated.pending with
  | none => simp [saturationResult] at success
  | some saturated =>
      rw [saturationResult] at success
      change
        (unify (residualEquations saturated.substitution saturated.pending)).bind
          (fun residual => some
            { substitution := Subst.compose residual saturated.substitution
              target := generated.target.apply
                (Subst.compose residual saturated.substitution) }) =
          some result at success
      cases residualResult :
          unify (residualEquations saturated.substitution saturated.pending) with
      | none => simp [residualResult] at success
      | some residual =>
          simp only [residualResult, Option.bind_some,
            Option.some.injEq] at success
          subst result
          have hardAbsorbing :=
            saturateUsing_absorbingPrincipal unify_absorbingMGUSolver
              saturationResult
          have residualAbsorbing :=
            unify_absorbingMGUSolver _ _ residualResult
          let closure : PrincipalBlockClosure generated :=
            { finalHard := saturated.hard
              finalPending := saturated.pending
              hardSubstitution := saturated.substitution
              residualSubstitution := residual
              saturation := saturateUsing_sound unify
                (fun equations substitution solved =>
                  (unify_absorbingMGUSolver equations substitution solved).mostGeneral)
                saturationResult
              residualPrincipal := residualAbsorbing.mostGeneral }
          refine ⟨closure, rfl, rfl, ⟨hardAbsorbing, residualAbsorbing⟩, ?_⟩
          intro obligation membership
          have ordinaryResolution := ordinary saturated saturationResult
          have conversion := residualEquations_ordinary_sound
            residualAbsorbing.mostGeneral.1 ordinaryResolution
            obligation membership
          simpa only [PrincipalBlockClosure.substitution, Ty.apply_compose]
            using conversion

namespace Source

/-- The generated block selected by executable elaboration has only ordinary
residual resolutions.  The equation argument prevents a certificate for an
unrelated hand-written block from being used at the inference boundary. -/
def InferenceResidualsOrdinary
    (signature : Signature) (context : Context) (expression : Expr) : Prop :=
  ∀ generated next,
    elaborate signature context expression context.initialSupply =
      some (generated, next) →
    ExecutableResidualsOrdinary generated

/-- Fully executable root check: elaborate the actual source program, then
inspect only the residual branches selected for that generated block. -/
def inferenceResidualsOrdinaryCheck
    (signature : Signature) (context : Context) (expression : Expr) : Bool :=
  match elaborate signature context expression context.initialSupply with
  | none => false
  | some (generated, _) => executableResidualsOrdinaryCheck generated

theorem InferenceResidualsOrdinary.of_check
    {signature : Signature} {context : Context} {expression : Expr}
    (checked : inferenceResidualsOrdinaryCheck signature context expression =
      true) :
    InferenceResidualsOrdinary signature context expression := by
  intro generated next success
  simp only [inferenceResidualsOrdinaryCheck, success] at checked
  exact ExecutableResidualsOrdinary.of_check checked

mutual

  /-- Sound structural subfragment whose root elaboration creates no delayed
  checking obligations.  A nested `letE` may have any value expression:
  that value block is closed internally, so only the supported body can
  contribute to the root pending list.  Applications and non-nullary calls
  are intentionally absent. -/
  inductive RootPendingFree : Expr → Prop where
    | var : RootPendingFree (.var index)
    | lit : RootPendingFree (.lit value)
    | something : RootPendingFree .something
    | boolTrue : RootPendingFree (.ctor DataCtor.true [])
    | boolFalse : RootPendingFree (.ctor DataCtor.false [])
    | listNil : RootPendingFree (.ctor DataCtor.nil [])
    | tuple (items : RootPendingFrees expressions) :
        RootPendingFree (.tuple expressions)
    | letE (body : RootPendingFree bodyExpression) :
        RootPendingFree (.letE valueExpression bodyExpression)

  inductive RootPendingFrees : List Expr → Prop where
    | nil : RootPendingFrees []
    | cons
        (head : RootPendingFree expression)
        (tail : RootPendingFrees expressions) :
        RootPendingFrees (expression :: expressions)

end

mutual

  theorem RootPendingFree.elaboration_pending_nil
      (supported : RootPendingFree expression)
      (elaboration : Elaborates signature context expression supply generated next) :
      generated.pending = [] := by
    cases supported with
    | var => cases elaboration; rfl
    | lit => cases elaboration; rfl
    | something => cases elaboration; rfl
    | boolTrue =>
        cases elaboration with
        | ctor lookup arity closed call => cases call; rfl
    | boolFalse =>
        cases elaboration with
        | ctor lookup arity closed call => cases call; rfl
    | listNil =>
        cases elaboration with
        | ctor lookup arity closed call => cases call; rfl
    | tuple items =>
        cases elaboration with
        | tuple itemsElaboration =>
            exact items.elaboration_pending_nil itemsElaboration
    | letE body =>
        cases elaboration with
        | letE valueElaboration closure absorbing bodyElaboration =>
            simpa [Generated.fromLet] using
              body.elaboration_pending_nil bodyElaboration

  theorem RootPendingFrees.elaboration_pending_nil
      (supported : RootPendingFrees expressions)
      (elaboration : ElaboratesItems signature context expressions supply
        generated next) :
      generated.pending = [] := by
    cases supported with
    | nil => cases elaboration; rfl
    | cons head tail =>
        cases elaboration with
        | cons headElaboration tailElaboration =>
            simp [head.elaboration_pending_nil headElaboration,
              tail.elaboration_pending_nil tailElaboration]

end

/-- A pending-free generated block passes the residual certificate for every
successful concrete saturation run. -/
theorem ExecutableResidualsOrdinary.of_pending_nil
    {generated : Generated} (pending : generated.pending = []) :
    ExecutableResidualsOrdinary generated := by
  intro output success obligation membership
  have saturated := saturateUsing_sound unify
    (fun equations substitution solved =>
      (unify_absorbingMGUSolver equations substitution solved).mostGeneral)
    success
  have outputPending : output.pending = [] :=
    Runtime.PromotionClosure.finalPending_eq_nil_of_initial_nil
      saturated.closure pending
  rw [outputPending] at membership
  contradiction

/-- Structural construction of the inference residual certificate.  This is
the premise-free path for the pending-free subfragment; broader supported
applications still require a local ordinary-conversion certificate. -/
theorem RootPendingFree.inferenceResidualsOrdinary
    (supported : RootPendingFree expression) (wellFormed : signature.WellFormed) :
    InferenceResidualsOrdinary signature context expression := by
  intro generated next success
  have elaboration := elaborate_sound wellFormed success
  exact ExecutableResidualsOrdinary.of_pending_nil
    (supported.elaboration_pending_nil elaboration)

/-- Principal source evidence returned from inference together with the
ordinary residual proof for its exact root closure. -/
structure OrdinaryPrincipalTypingDerivation
    (signature : Signature) (context : Context) (expression : Expr)
    (target : Ty) where
  derivation : PrincipalTypingDerivation signature context expression target
  ordinary : Runtime.ClosureRemainingChecksOrdinary derivation.closure

namespace Inference

/-- Public inference constructs an ordinary-root principal derivation when
the concrete elaboration result carries the executable residual certificate.
No claim is made for expressions whose residual resolver selects matcher or
product conversion. -/
theorem infer_success_ordinaryPrincipalTyping
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer signature context expression = some target)
    (ordinary : InferenceResidualsOrdinary signature context expression) :
    Nonempty
      (OrdinaryPrincipalTypingDerivation signature context expression target) := by
  unfold infer at success
  cases elaborated :
      elaborate signature context expression context.initialSupply with
  | none => simp [elaborateRoot, elaborated] at success
  | some output =>
      rcases output with ⟨generated, next⟩
      simp only [elaborateRoot, elaborated, Option.map_some] at success
      change
        (inferGeneratedUsing unify generated).bind
          (fun closed => some closed.target) = some target at success
      cases closedResult : inferGeneratedUsing unify generated with
      | none => simp [closedResult] at success
      | some result =>
          simp only [closedResult, Option.bind_some,
            Option.some.injEq] at success
          subst target
          obtain ⟨closure, _, targetEquality, absorbing,
            closureOrdinary⟩ :=
            inferGeneratedUsing_ordinaryPrincipalBlockClosure closedResult
              (ordinary generated next elaborated)
          exact ⟨
            { derivation :=
                { generated := generated
                  next := next
                  elaboration := elaborate_sound wellFormed elaborated
                  closure := closure
                  absorbing := absorbing
                  target_eq := targetEquality }
              ordinary := closureOrdinary }⟩

end Inference
end Source

end TypePM

namespace TypePM.Source.PolymorphicLetInferenceOrdinary

open Runtime
open PolymorphicLetProtectedSyntaxRegression
open PolymorphicLetProtectedClosureRegression

set_option linter.unusedSimpArgs false

def nestedTupleGenerated : Generated :=
  { target := .prod [.prod [.int, .int], .var ⟨2⟩, .var ⟨6⟩]
    hard := [
      .ty (.fn (.var ⟨0⟩) (.var ⟨0⟩))
        (.fn (.var ⟨1⟩) (.var ⟨2⟩)),
      .ty (.fn (.var ⟨3⟩) (.var ⟨3⟩))
        (.fn (.var ⟨5⟩) (.var ⟨6⟩))]
    pending := [
      ⟨.int, .var ⟨1⟩⟩,
      ⟨.matcher .any (.var ⟨4⟩), .var ⟨5⟩⟩] }

theorem elaborate_nestedTupleValueBody_exact :
    elaborate Paper1Signature.signature [identityScheme] nestedTupleValueBody
      (Context.initialSupply [identityScheme]) =
      some (nestedTupleGenerated, ⟨7, 0⟩) := by
  simp [nestedTupleValueBody, nestedTupleValue, nestedTupleGenerated,
    identityScheme, identityType,
    elaborate, elaborateItems, closeNestedTupleValue,
    Context.initialSupply, Context.applyFree, Context.generalize,
    Context.generalizedTyVars, Context.generalizedCapVars,
    Context.freeTyVars, Context.freeCapVars, Context.interfaceEquations,
    Scheme.instantiate, Scheme.boundTyInstance, Scheme.boundCapInstance,
    Scheme.mono, Scheme.applyFree, Scheme.freeTyVars, Scheme.freeCapVars,
    PolyTy.ofTy, PolyTy.ofTyList, PolyTy.close, PolyTy.closeList,
    PolyTy.openBound, PolyTy.openBoundList, PolyTy.applyFree,
    PolyTy.applyFreeList, PolyTy.freeTyVars, PolyTy.freeTyVarsList,
    PolyTy.freeCapVars, PolyTy.freeCapVarsList, PolyCap.ofCap,
    PolyCap.ofCapList, PolyCap.close, PolyCap.closeList, PolyCap.openBound,
    PolyCap.openBoundList, PolyCap.applyFree, PolyCap.applyFreeList,
    PolyCap.freeCapVars, PolyCap.freeCapVarsList, Supply.nextTy, Supply.join,
    Generated.fromLet,
    TyVar.next, CapVar.next, dedup, dedupFirst, List.idxOf, List.findIdx,
    List.findIdx.go, Ty.tyVars, Ty.tyVarsList, Ty.capVars, Ty.capVarsList,
    Cap.capVars, Cap.capVarsList, Ty.apply, Ty.applyList, Subst.id]

set_option maxRecDepth 100000 in
private theorem nestedTupleGenerated_fuelCheck :
    executableResidualsOrdinaryCheckUsing (unifyWithFuel 100)
      nestedTupleGenerated = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem nestedGenerated_fuelCheck :
    executableResidualsOrdinaryCheckUsing (unifyWithFuel 100)
      nestedGenerated = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem capturedGenerated_fuelCheck :
    executableResidualsOrdinaryCheckUsing (unifyWithFuel 100)
      capturedGenerated = true := by
  with_unfolding_all rfl

theorem nestedTupleValueBody_residualsOrdinary :
    InferenceResidualsOrdinary Paper1Signature.signature [identityScheme]
      nestedTupleValueBody := by
  intro generated next success
  rw [elaborate_nestedTupleValueBody_exact] at success
  simp only [Option.some.injEq, Prod.mk.injEq] at success
  rcases success with ⟨rfl, rfl⟩
  exact ExecutableResidualsOrdinary.of_check
    (executableResidualsOrdinaryCheck_unify_of_fuel
      nestedTupleGenerated_fuelCheck)

theorem nestedProtectedBody_residualsOrdinary :
    InferenceResidualsOrdinary Paper1Signature.signature [identityScheme]
      nestedProtectedBody := by
  intro generated next success
  rw [elaborate_nestedProtectedBody_exact] at success
  simp only [Option.some.injEq, Prod.mk.injEq] at success
  rcases success with ⟨rfl, rfl⟩
  exact ExecutableResidualsOrdinary.of_check
    (executableResidualsOrdinaryCheck_unify_of_fuel nestedGenerated_fuelCheck)

theorem capturedPolymorphicIdentity_residualsOrdinary :
    InferenceResidualsOrdinary Paper1Signature.signature []
      capturedPolymorphicIdentity := by
  intro generated next success
  have rootSuccess := congrArg (Option.map Prod.fst) success
  change elaborateRoot Paper1Signature.signature []
    capturedPolymorphicIdentity = some generated at rootSuccess
  rw [elaborateCaptured] at rootSuccess
  simp only [Option.some.injEq] at rootSuccess
  subst generated
  exact ExecutableResidualsOrdinary.of_check
    (executableResidualsOrdinaryCheck_unify_of_fuel capturedGenerated_fuelCheck)

theorem nestedTupleValueBody_runtimeTypingFromInfer
    (success : infer Paper1Signature.signature [identityScheme]
      nestedTupleValueBody = some target) :
    ProtectedClosureRuntimeTyping [true] nestedTupleValueBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success
      nestedTupleValueBody_residualsOrdinary
  exact nestedTupleValueBody_runtimeTypingFromSource certified.derivation
    certified.ordinary

theorem nestedTupleValueBody_neverStuckFromInfer
    (success : infer Paper1Signature.signature [identityScheme]
      nestedTupleValueBody = some target)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      nestedTupleValueBody).NotStuck := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success
      nestedTupleValueBody_residualsOrdinary
  exact nestedTupleValueBody_neverStuckFromSource certified.derivation
    certified.ordinary fuel

theorem nestedProtectedBody_runtimeTypingFromInfer
    (success : infer Paper1Signature.signature [identityScheme]
      nestedProtectedBody = some target) :
    ProtectedClosureRuntimeTyping [true] nestedProtectedBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success nestedProtectedBody_residualsOrdinary
  exact nestedProtectedBody_runtimeTypingFromSource certified.derivation
    certified.ordinary

theorem nestedProtectedBody_neverStuckFromInfer
    (success : infer Paper1Signature.signature [identityScheme]
      nestedProtectedBody = some target)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      nestedProtectedBody).NotStuck := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success nestedProtectedBody_residualsOrdinary
  exact nestedProtectedBody_neverStuckFromSource certified.derivation
    certified.ordinary fuel

theorem capturedPolymorphicIdentity_ordinaryPrincipalFromInfer
    (success : infer Paper1Signature.signature [] capturedPolymorphicIdentity =
      some target) :
    Nonempty (OrdinaryPrincipalTypingDerivation Paper1Signature.signature []
      capturedPolymorphicIdentity target) :=
  Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success
      capturedPolymorphicIdentity_residualsOrdinary

theorem capturedPolymorphicIdentity_runtimeTypingFromInfer
    (success : infer Paper1Signature.signature [] capturedPolymorphicIdentity =
      some target) :
    ProtectedClosureRuntimeTyping [] capturedPolymorphicIdentity target [] := by
  rw [infer_capturedPolymorphicIdentity_exact] at success
  injection success with targetEquality
  rw [← targetEquality]
  exact capturedPolymorphicIdentity_protectedClosureRuntimeTyping

theorem capturedPolymorphicIdentity_neverStuckFromInfer
    (success : infer Paper1Signature.signature [] capturedPolymorphicIdentity =
      some target)
    (fuel : Nat) :
    (evalFuel fuel [] capturedPolymorphicIdentity).NotStuck := by
  have _ordinary := capturedPolymorphicIdentity_ordinaryPrincipalFromInfer success
  exact capturedPolymorphicIdentity_neverStuck fuel

/-! ## Structural pending-free regression: nested Boolean value -/

def nestedBoolValueBody : Expr :=
  .letE (.ctor DataCtor.true []) (.var 0)

theorem nestedBoolValueBody_pendingFree :
    RootPendingFree nestedBoolValueBody := by
  exact .letE .var

theorem nestedBoolValueBody_residualsOrdinary :
    InferenceResidualsOrdinary Paper1Signature.signature []
      nestedBoolValueBody :=
  nestedBoolValueBody_pendingFree.inferenceResidualsOrdinary
    Paper1Signature.wellFormed

theorem infer_nestedBoolValueBody_exact :
    infer Paper1Signature.signature [] nestedBoolValueBody =
      some DataTypes.bool := by
  have emptyUnify : unify [] = some Subst.id := by
    unfold unify
    rw [unifyLoop.eq_def]
  have closeBool : inferGeneratedUsing unify
      { target := DataTypes.bool, hard := [], pending := [] } =
      some { substitution := Subst.id, target := DataTypes.bool } := by
    simp [inferGeneratedUsing, saturateUsing, saturateLoop, emptyUnify,
      promoteUnder, residualEquations, DataTypes.bool, Ty.apply, Ty.applyList,
      Cap.apply, Subst.compose, Subst.id]
  have closeBoolRaw : inferGeneratedUsing unify
      { target := Ty.data DataFormer.bool [], hard := [], pending := [] } =
      some { substitution := Subst.id, target := Ty.data DataFormer.bool [] } := by
    simpa [DataTypes.bool] using closeBool
  have elaborateExact :
      elaborateRoot Paper1Signature.signature [] nestedBoolValueBody =
        some { target := DataTypes.bool, hard := [], pending := [] } := by
    simp [elaborateRoot, nestedBoolValueBody, elaborate, elaborateCall,
    Scheme.callArity, Scheme.callArity.go, closeBoolRaw, Context.initialSupply,
    Context.applyFree, Context.generalize, Context.generalizedTyVars,
    Context.generalizedCapVars, Context.freeTyVars, Context.freeCapVars,
    Context.interfaceEquations, ConstructorSchemes.boolTrue,
    PolyDataTypes.bool, DataTypes.bool, Scheme.instantiate,
    Scheme.applyFree, Scheme.freeTyVars, Scheme.freeCapVars, PolyTy.close,
    PolyTy.closeList, PolyTy.openBound, PolyTy.openBoundList,
    PolyTy.applyFree, PolyTy.applyFreeList, PolyTy.freeTyVars,
    PolyTy.freeTyVarsList, PolyTy.freeCapVars, PolyTy.freeCapVarsList,
    PolyCap.applyFree, PolyCap.applyFreeList, PolyCap.freeCapVars,
    PolyCap.freeCapVarsList, Generated.fromLet, Ty.tyVars, Ty.tyVarsList, Ty.capVars,
    Ty.capVarsList, Ty.apply, Ty.applyList, Cap.apply, Cap.capVars, Cap.capVarsList,
    Supply.join, TyVar.next, CapVar.next, dedupFirst, dedup, Subst.id]
  simp [infer, elaborateExact, closeBool]

private theorem nestedBoolValue_sameClosureCertificate
    {supply afterValue : Supply} {generatedValue : Generated}
    (valueElaboration : Elaborates Paper1Signature.signature []
      (.ctor DataCtor.true []) supply generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (_absorbing : closure.Absorbing) :
    ProtectedNestedLetValueAtClosure valueElaboration closure [] [] := by
  cases valueElaboration with
  | ctor lookup arity closed call =>
      simp only [Paper1Signature.lookup_true, Option.some.injEq] at lookup
      cases lookup
      cases call with
      | nil =>
          constructor
          · intro obligation membership
            have finalPending :=
              Runtime.PromotionClosure.finalPending_eq_nil_of_initial_nil
                closure.saturation.closure rfl
            rw [finalPending] at membership
            contradiction
          · simpa [PrincipalBlockClosure.target, Context.applyFree,
              Context.generalize, Context.generalizedTyVars,
              Context.generalizedCapVars, Context.freeTyVars,
              Context.freeCapVars, ConstructorSchemes.boolTrue,
              PolyDataTypes.bool, DataTypes.bool, Scheme.instantiate, PolyTy.close,
              PolyTy.closeList, PolyTy.openBound, PolyTy.openBoundList,
              PolyTy.freeTyVars, PolyTy.freeCapVars, Ty.tyVars,
              Ty.tyVarsList, Ty.capVars, Ty.capVarsList, Ty.apply,
              Ty.applyList, Cap.capVars, Cap.capVarsList, dedupFirst,
              dedup] using
              (ProtectedRuntimeTyping.runtime RuntimeTyping.boolTrue)

theorem nestedBoolValueBody_runtimeTypingFromInfer
    (success : infer Paper1Signature.signature [] nestedBoolValueBody =
      some target) :
    ProtectedClosureRuntimeTyping [] nestedBoolValueBody target [] := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success nestedBoolValueBody_residualsOrdinary
  have semantic := Runtime.strictSemanticSolution_of_closure
    certified.derivation.closure certified.ordinary
  have runtimeTyping :=
    (ProtectedClosureBodySupported.firstOrder
      (ProtectedBodySupported.var (index := 0))).elaboration_typing_letValue
        Runtime.paper1SignatureCompatible certified.derivation.elaboration
          semantic Runtime.ProtectedContextCompatible.nil
          nestedBoolValue_sameClosureCertificate
  rw [certified.derivation.target_eq]
  exact runtimeTyping

theorem nestedBoolValueBody_neverStuckFromInfer
    (success : infer Paper1Signature.signature [] nestedBoolValueBody =
      some target)
    (fuel : Nat) :
    (evalFuel fuel [] nestedBoolValueBody).NotStuck :=
  (nestedBoolValueBody_runtimeTypingFromInfer success).neverStuck fuel []
    EnvironmentTyping.nil

theorem nestedBoolValueBody_runtimeTyping :
    ProtectedClosureRuntimeTyping [] nestedBoolValueBody DataTypes.bool [] :=
  nestedBoolValueBody_runtimeTypingFromInfer infer_nestedBoolValueBody_exact

theorem nestedBoolValueBody_neverStuck (fuel : Nat) :
    (evalFuel fuel [] nestedBoolValueBody).NotStuck :=
  nestedBoolValueBody_neverStuckFromInfer infer_nestedBoolValueBody_exact fuel

end TypePM.Source.PolymorphicLetInferenceOrdinary
