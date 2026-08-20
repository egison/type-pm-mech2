import TypePM.Source.PolymorphicLetRuntimeBridge
import TypePM.InferenceFuelTransport

/-!
# Regression: generalized identity below data, primitive, and conditional syntax

This body is checked under one generalized identity entry.  Three occurrences
instantiate that one entry at the element type of a List constructor, at
`Int` inside addition, and at a matcher type.  The protected runtime
derivation below is built only from the relational source elaboration and its
strict semantic solution; it is not assembled occurrence by occurrence.
-/

namespace TypePM.Source.PolymorphicLetProtectedSyntaxRegression

open TypePM.Runtime

set_option linter.unusedSimpArgs false

def identityType : Ty :=
  .fn (.var ⟨0⟩) (.var ⟨0⟩)

def identityScheme : Scheme :=
  ⟨1, 0, .fn (.bound 0) (.bound 0), by
    simp [PolyTy.WellScoped]⟩

def thenBranch : Expr :=
  .tuple [
    .ctor DataCtor.cons [
      .app (.var 0) (.lit 1),
      .ctor DataCtor.nil []],
    .prim PrimOp.add [
      .app (.var 0) (.lit 2),
      .lit 3],
    .app (.var 0) .something]

def elseBranch : Expr :=
  .tuple [
    .ctor DataCtor.nil [],
    .prim PrimOp.add [.lit 0, .lit 0],
    .something]

def protectedSyntaxBody : Expr :=
  .ifE (.ctor DataCtor.true []) thenBranch elseBranch

def nestedProtectedBody : Expr :=
  .letE (.lam (.var 0))
    (.tuple [
      .app (.var 0) (.lit 4),
      .app (.var 0) .something,
      .app (.var 1) (.lit 5),
      .app (.var 1) .something])

/-- A second nested-let fixture whose value is a closed product rather than
the identity function.  The surrounding generalized identity is still used
at both `Int` and matcher types below the new binding. -/
def nestedTupleValue : Expr :=
  .tuple [.lit 1, .lit 2]

def nestedTupleValueBody : Expr :=
  .letE nestedTupleValue
    (.tuple [
      .var 0,
      .app (.var 1) (.lit 3),
      .app (.var 1) .something])

private theorem nestedTupleValue_sameClosureCertificate
    {supply afterValue : Supply} {generatedValue : Generated}
    (valueElaboration : Elaborates Paper1Signature.signature [identityScheme]
      nestedTupleValue supply generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (_absorbing : closure.Absorbing) :
    ProtectedNestedLetValueAtClosure valueElaboration closure [true]
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  unfold nestedTupleValue at valueElaboration
  cases valueElaboration with
  | tuple itemsElaboration =>
      cases itemsElaboration with
      | cons firstElaboration restElaboration =>
          cases firstElaboration
          cases restElaboration with
          | cons secondElaboration nilElaboration =>
              cases secondElaboration
              cases nilElaboration
              constructor
              · intro obligation membership
                have finalPending :=
                  TypePM.Runtime.PromotionClosure.finalPending_eq_nil_of_initial_nil
                    closure.saturation.closure rfl
                rw [finalPending] at membership
                contradiction
              · simpa [nestedTupleValue, PrincipalBlockClosure.target, Context.generalize,
                  Context.generalizedTyVars, Context.generalizedCapVars,
                  Context.freeTyVars, Context.freeCapVars, Scheme.freeTyVars,
                  Scheme.freeCapVars, PolyTy.freeTyVars, PolyTy.freeCapVars,
                  PolyTy.close, PolyTy.closeList, PolyTy.openBound,
                  PolyTy.openBoundList, Scheme.instantiate, Ty.tyVars,
                  Ty.tyVarsList, Ty.capVars, Ty.capVarsList, Cap.capVars,
                  Cap.capVarsList, Ty.apply, Ty.applyList, dedupFirst, dedup] using
                  (ProtectedRuntimeTyping.runtime
                    (RuntimeTyping.tuple
                      (RuntimeTypings.cons (.lit 1)
                        (RuntimeTypings.cons (.lit 2) .nil))))

theorem nestedTupleValueBody_bodySupported :
    ProtectedClosureBodySupported
      (.tuple [
        .var 0,
        .app (.var 1) (.lit 3),
        .app (.var 1) .something]) := by
  exact .firstOrder (.tuple
    (.cons .var
      (.cons (.app .var .lit)
        (.cons (.app .var .something) .nil))))

private theorem closeNestedTupleValue :
    inferGeneratedUsing unify
      { target := .prod [.int, .int]
        hard := []
        pending := [] } =
      some
        { substitution := Subst.id
          target := .prod [.int, .int] } := by
  have emptyUnify : unify [] = some Subst.id := by
    unfold unify
    rw [unifyLoop.eq_def]
  simp [inferGeneratedUsing, saturateUsing, saturateLoop, emptyUnify,
    promoteUnder, residualEquations]

/-- The executable elaborator supplies a genuine relational derivation for
the non-identity nested value fixture. -/
theorem nestedTupleValueBody_elaboration_exists :
    ∃ generated next,
      Elaborates Paper1Signature.signature [identityScheme]
        nestedTupleValueBody (Context.initialSupply [identityScheme])
        generated next := by
  have succeeds :
      (elaborate Paper1Signature.signature [identityScheme]
        nestedTupleValueBody
        (Context.initialSupply [identityScheme])).isSome = true := by
    simp [nestedTupleValueBody, nestedTupleValue, elaborate, elaborateItems,
      closeNestedTupleValue]
  cases equation : elaborate Paper1Signature.signature [identityScheme]
      nestedTupleValueBody (Context.initialSupply [identityScheme]) with
  | none => simp [equation] at succeeds
  | some output =>
      rcases output with ⟨generated, next⟩
      exact ⟨generated, next,
        elaborate_sound Paper1Signature.wellFormed equation⟩

/-- Relational source elaboration reconstructs the nested runtime derivation.
The tuple value is typed through the exact inner closure certificate above;
the regression does not provide a hand-written typing tree for the whole
program. -/
theorem nestedTupleValueBody_runtimeTyping
    (elaboration : Elaborates Paper1Signature.signature [identityScheme]
      nestedTupleValueBody supply generated next)
    (semantic : StrictGeneratedSemanticSolution generated solution) :
    ProtectedClosureRuntimeTyping [true] nestedTupleValueBody
      (generated.target.apply solution)
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  unfold nestedTupleValueBody at elaboration ⊢
  have contextCompatible : ProtectedContextCompatible [identityScheme]
      [(identityScheme.instantiate ⟨0, 0⟩).1] [true] solution := by
    apply ProtectedContextCompatible.pushCanonical
        (canonicalSupply := (⟨0, 0⟩ : Supply))
    · intro index membership
      simp [identityScheme, Scheme.freeTyVars, PolyTy.freeTyVars,
        dedupFirst, dedup] at membership
    · intro index membership
      simp [identityScheme, Scheme.freeCapVars, PolyTy.freeCapVars,
        dedupFirst, dedup] at membership
    · exact ProtectedContextCompatible.nil
  exact nestedTupleValueBody_bodySupported.elaboration_typing_letValue
    paper1SignatureCompatible elaboration semantic
      contextCompatible
      nestedTupleValue_sameClosureCertificate

/-- Every evaluator fuel is non-stuck for the automatically reconstructed
nested tuple-value program. -/
theorem nestedTupleValueBody_neverStuck
    (elaboration : Elaborates Paper1Signature.signature [identityScheme]
      nestedTupleValueBody supply generated next)
    (semantic : StrictGeneratedSemanticSolution generated solution)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      nestedTupleValueBody).NotStuck := by
  apply (nestedTupleValueBody_runtimeTyping elaboration semantic).neverStuck
  apply EnvironmentTyping.cons
  · change ValueTyping (Value.plainClosure [] (.var 0)) identityType
    exact .plainClosure .nil (.var rfl)
  · exact .nil

/-- The principal source derivation supplies the root semantic solution;
only its already-public ordinary residual-check boundary remains explicit. -/
theorem nestedTupleValueBody_runtimeTypingFromSource
    (derivation : PrincipalTypingDerivation Paper1Signature.signature
      [identityScheme] nestedTupleValueBody target)
    (ordinary : ClosureRemainingChecksOrdinary derivation.closure) :
    ProtectedClosureRuntimeTyping [true] nestedTupleValueBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  have typing := nestedTupleValueBody_runtimeTyping derivation.elaboration
    (strictSemanticSolution_of_closure derivation.closure ordinary)
  rw [derivation.target_eq]
  exact typing

/-- Source principal typing therefore rules out evaluator `stuck` for the
non-identity nested value, without a separately supplied runtime derivation. -/
theorem nestedTupleValueBody_neverStuckFromSource
    (derivation : PrincipalTypingDerivation Paper1Signature.signature
      [identityScheme] nestedTupleValueBody target)
    (ordinary : ClosureRemainingChecksOrdinary derivation.closure)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      nestedTupleValueBody).NotStuck := by
  apply (nestedTupleValueBody_runtimeTypingFromSource
    derivation ordinary).neverStuck
  apply EnvironmentTyping.cons
  · change ValueTyping (Value.plainClosure [] (.var 0)) identityType
    exact .plainClosure .nil (.var rfl)
  · exact .nil

private def nestedGenerated : Generated :=
  { target := .prod [.var ⟨3⟩, .var ⟨7⟩, .var ⟨10⟩, .var ⟨14⟩]
    hard := [
      .ty (.fn (.var ⟨1⟩) (.var ⟨1⟩))
        (.fn (.var ⟨2⟩) (.var ⟨3⟩)),
      .ty (.fn (.var ⟨4⟩) (.var ⟨4⟩))
        (.fn (.var ⟨6⟩) (.var ⟨7⟩)),
      .ty (.fn (.var ⟨8⟩) (.var ⟨8⟩))
        (.fn (.var ⟨9⟩) (.var ⟨10⟩)),
      .ty (.fn (.var ⟨11⟩) (.var ⟨11⟩))
        (.fn (.var ⟨13⟩) (.var ⟨14⟩))]
    pending := [
      ⟨.int, .var ⟨2⟩⟩,
      ⟨.matcher .any (.var ⟨5⟩), .var ⟨6⟩⟩,
      ⟨.int, .var ⟨9⟩⟩,
      ⟨.matcher .any (.var ⟨12⟩), .var ⟨13⟩⟩] }

private theorem unify_nil_exact : unify [] = some Subst.id := by
  unfold unify
  rw [unifyLoop.eq_def]

private theorem closeIdentityAt (index : Nat) :
    inferGeneratedUsing unify
      { target := .fn (.var ⟨index⟩) (.var ⟨index⟩)
        hard := []
        pending := [] } =
      some
        { substitution := Subst.id
          target := .fn (.var ⟨index⟩) (.var ⟨index⟩) } := by
  simp [inferGeneratedUsing, saturateUsing, saturateLoop,
    unify_nil_exact, promoteUnder, residualEquations]

private theorem elaborate_nestedProtectedBody_exact :
    elaborate Paper1Signature.signature [identityScheme] nestedProtectedBody
      (Context.initialSupply [identityScheme]) =
      some (nestedGenerated, ⟨15, 0⟩) := by
  simp [nestedProtectedBody, nestedGenerated, identityScheme, identityType,
    elaborate, elaborateItems, closeIdentityAt,
    Context.initialSupply, Context.applyFree, Context.generalize,
    Context.generalizedTyVars, Context.generalizedCapVars,
    Context.freeTyVars, Context.freeCapVars, Context.interfaceEquations,
    Scheme.instantiate, Scheme.boundTyInstance, Scheme.boundCapInstance,
    Scheme.mono, Scheme.applyFree, Scheme.freeTyVars, Scheme.freeCapVars,
    PolyTy.ofTy, PolyTy.ofTyList, PolyTy.close, PolyTy.closeList,
    PolyTy.openBound, PolyTy.openBoundList, PolyTy.applyFree,
    PolyTy.applyFreeList, PolyTy.freeTyVars,
    PolyTy.freeTyVarsList, PolyTy.freeCapVars, PolyTy.freeCapVarsList,
    PolyCap.ofCap, PolyCap.ofCapList, PolyCap.close, PolyCap.closeList,
    PolyCap.openBound, PolyCap.openBoundList, PolyCap.applyFree,
    PolyCap.applyFreeList, PolyCap.freeCapVars,
    PolyCap.freeCapVarsList, Supply.nextTy, Supply.join, Generated.fromLet,
    TyVar.next, CapVar.next, dedup, dedupFirst, List.idxOf, List.findIdx,
    List.findIdx.go, Ty.tyVars, Ty.capVars, Cap.capVars, Cap.capVarsList,
    Ty.apply, Ty.applyList, Subst.id]

theorem nestedProtectedBody_supported :
    ProtectedClosureBodySupported nestedProtectedBody := by
  exact .letIdentity (.firstOrder (.tuple
    (.cons (.app .var .lit)
      (.cons (.app .var .something)
        (.cons (.app .var .lit)
          (.cons (.app .var .something) .nil))))))

theorem infer_nestedProtectedBody_isSome :
    (infer Paper1Signature.signature [identityScheme]
      nestedProtectedBody).isSome = true := by
  have fuelSuccess :
      (inferGeneratedUsing (unifyWithFuel 100) nestedGenerated).isSome =
        true := by
    with_unfolding_all rfl
  cases fuelEquation : inferGeneratedUsing (unifyWithFuel 100)
      nestedGenerated with
  | none => simp [fuelEquation] at fuelSuccess
  | some result =>
      have publicEquation : inferGeneratedUsing unify nestedGenerated =
          some result :=
        inferGeneratedUsing_unify_of_fuel_success fuelEquation
      unfold infer elaborateRoot
      rw [elaborate_nestedProtectedBody_exact]
      simp [publicEquation]

/-- The focused nested-let fixture has an actual independently checked source
principal derivation; it is not represented by a hand-built runtime tree. -/
theorem nestedProtectedBody_sourcePrincipal_exists :
    ∃ target,
      PrincipalTyping Paper1Signature.signature [identityScheme]
        nestedProtectedBody target := by
  cases equation : infer Paper1Signature.signature [identityScheme]
      nestedProtectedBody with
  | none =>
      have succeeds := infer_nestedProtectedBody_isSome
      simp [equation] at succeeds
  | some target =>
      exact ⟨target, Inference.infer_success_principalTyping
        Paper1Signature.wellFormed equation⟩

theorem protectedSyntaxBody_supported :
    ProtectedBodySupported protectedSyntaxBody := by
  exact .ifE .boolTrue
    (.tuple (.cons
      (.listCons (.app .var .lit) .listNil)
      (.cons
        (.add (.app .var .lit) .lit)
        (.cons (.app .var .something) .nil))))
    (.tuple (.cons .listNil
      (.cons (.add .lit .lit)
        (.cons .something .nil))))

private def canonicalSupply : Supply :=
  ⟨0, 0⟩

private theorem canonicalIdentityType_eq :
    (identityScheme.instantiate canonicalSupply).1 = identityType := by
  rfl

private theorem identityContextCompatible (solution : Subst) :
    ProtectedContextCompatible [identityScheme]
      [(identityScheme.instantiate canonicalSupply).1] [true] solution := by
  apply ProtectedContextCompatible.pushCanonical
      (canonicalSupply := canonicalSupply)
  · intro index membership
    simp [identityScheme, Scheme.freeTyVars, PolyTy.freeTyVars,
      dedupFirst, dedup] at membership
  · intro index membership
    simp [identityScheme, Scheme.freeCapVars, PolyTy.freeCapVars,
      dedupFirst, dedup] at membership
  · exact ProtectedContextCompatible.nil

/-- The source elaborator really accepts the focused body in the generalized
identity context.  This witness is kernel-reduced and then transported to the
independent relational elaboration judgment. -/
theorem protectedSyntaxBody_elaboration_exists :
    ∃ generated next,
      Elaborates Paper1Signature.signature [identityScheme]
        protectedSyntaxBody (Context.initialSupply [identityScheme])
          generated next := by
  have succeeds :
      (elaborate Paper1Signature.signature [identityScheme]
        protectedSyntaxBody (Context.initialSupply [identityScheme])).isSome =
          true := by
    with_unfolding_all rfl
  cases equation : elaborate Paper1Signature.signature [identityScheme]
      protectedSyntaxBody (Context.initialSupply [identityScheme]) with
  | none => simp [equation] at succeeds
  | some output =>
      rcases output with ⟨generated, next⟩
      exact ⟨generated, next,
        elaborate_sound Paper1Signature.wellFormed equation⟩

/-- Constructor, primitive, and conditional typing are reconstructed from an
actual relational elaboration and a strict semantic solution.  In particular,
the conclusion contains all three protected instantiations without a
hand-written runtime derivation. -/
theorem protectedSyntaxBody_runtimeTyping
    (elaboration : Elaborates Paper1Signature.signature [identityScheme]
      protectedSyntaxBody supply generated next)
    (semantic : StrictGeneratedSemanticSolution generated solution) :
    ProtectedRuntimeTyping [true] protectedSyntaxBody
      (generated.target.apply solution)
      [(identityScheme.instantiate canonicalSupply).1] :=
  protectedSyntaxBody_supported.elaboration_typing
    paper1SignatureCompatible elaboration semantic
      (identityContextCompatible solution)

/-- Evaluating the automatically reconstructed body under the canonical
identity closure cannot get stuck.  The only remaining premise is the strict
semantic solution of the actual source constraint block. -/
theorem protectedSyntaxBody_neverStuck
    (elaboration : Elaborates Paper1Signature.signature [identityScheme]
      protectedSyntaxBody supply generated next)
    (semantic : StrictGeneratedSemanticSolution generated solution)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)] protectedSyntaxBody).NotStuck := by
  apply (protectedSyntaxBody_runtimeTyping elaboration semantic).neverStuck
  apply EnvironmentTyping.cons
  · rw [canonicalIdentityType_eq]
    exact .plainClosure .nil (.var rfl)
  · exact .nil

/-! ## Nested principal-let checkpoint

The nested source derivation contains two closure representatives: the inner
identity closure stored by `Elaborates.letE`, and the root closure supplying
the final semantic solution.  The general bridge now connects the inner
representative automatically.  The only remaining certificate below says
that the root closure's residual checks use ordinary equality, which is the
pre-existing strict-body boundary and is unrelated to representative choice.
-/

/-- An exact source principal derivation and its ordinary residual-check
certificate automatically produce the nested protected runtime derivation.
Both the inner identity and the captured outer identity are used at `Int` and
at independently fresh matcher types in `nestedProtectedBody`. -/
theorem nestedProtectedBody_runtimeTypingFromSource
    (derivation : PrincipalTypingDerivation Paper1Signature.signature
      [identityScheme] nestedProtectedBody target)
    (ordinary : ClosureRemainingChecksOrdinary derivation.closure) :
    ProtectedClosureRuntimeTyping [true] nestedProtectedBody target
      [(identityScheme.instantiate canonicalSupply).1] := by
  have semantic := strictSemanticSolution_of_closure derivation.closure ordinary
  have runtimeTyping := nestedProtectedBody_supported.elaboration_typing
    paper1SignatureCompatible derivation.elaboration semantic
      (identityContextCompatible derivation.closure.substitution)
  rw [derivation.target_eq]
  exact runtimeTyping

/-- Evaluator no-stuck follows from the exact source derivation through the
syntax-directed nested-let bridge; no runtime derivation is supplied by the
regression. -/
theorem nestedProtectedBody_neverStuckFromSource
    (derivation : PrincipalTypingDerivation Paper1Signature.signature
      [identityScheme] nestedProtectedBody target)
    (ordinary : ClosureRemainingChecksOrdinary derivation.closure)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)] nestedProtectedBody).NotStuck := by
  apply (nestedProtectedBody_runtimeTypingFromSource derivation ordinary).neverStuck
  apply EnvironmentTyping.cons
  · rw [canonicalIdentityType_eq]
    exact .plainClosure .nil (.var rfl)
  · exact .nil

end TypePM.Source.PolymorphicLetProtectedSyntaxRegression
