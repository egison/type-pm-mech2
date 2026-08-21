import TypePM.Source.M4MatchFirstTotalCoreBridge
import TypePM.Source.M4ElaborationFuelTransport
import TypePM.Source.M4RecursiveMatcherRuntimeInputBridge
import TypePM.Source.M4RecursiveMatcherTotalBridgeRegression
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility
import TypePM.Runtime.EvaluationAdequacy

/-!
# Public M4 `matchFirst` with an actual user matcher

This regression crosses the first explicit-fallback `matchFirst` boundary
whose matcher expression evaluates to a user matcher closure rather than to
the primitive `something` value.  The single wildcard arm has no bindings.
The matcher deliberately returns zero decompositions, so evaluation reaches
the mandatory fallback in the original environment.

The atom certificate is indexed by the real dispatch result.  No premise
claims that arbitrary delegated branches preserve the wildcard's empty
binding list.
-/

namespace TypePM.Source.M4UserMatcherMatchFirstRegression

open TypePM.Runtime
open TypePM.Source.MatcherTyping

abbrev emptyClause : MatcherClause :=
  MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause

def expression : Expr :=
  .matchFirst (.lit 0) (.matcher [emptyClause])
    [.mk .wild (.lit 42)] (.lit 7)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

private def inferenceGenerated : Generated :=
  { target := .int
    hard := [
      .cap (.var ⟨0⟩) .any,
      .ty (.var ⟨3⟩) .int,
      .ty .int .int]
    pending := [
      ⟨.matcher .any (.var ⟨1⟩), .slot (.var ⟨1⟩) (.var ⟨0⟩)⟩,
      ⟨DataTypes.list (.var ⟨2⟩), DataTypes.list (.var ⟨0⟩)⟩,
      ⟨.matcher (.var ⟨0⟩) (.var ⟨0⟩),
        .slot (.var ⟨2⟩) .int⟩] }

private theorem elaborate_next_matcher_exact :
    M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 8 []
        .something ⟨1, 2⟩ =
      some (⟨.matcher .any (.var ⟨1⟩), [], []⟩, ⟨2, 2⟩) := by
  rfl

private theorem elaborate_empty_list_exact :
    M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 8
        [.mono (.var ⟨0⟩)] (.ctor DataCtor.nil []) ⟨2, 2⟩ =
      some (⟨DataTypes.list (.var ⟨2⟩), [], []⟩, ⟨3, 2⟩) := by
  rfl'

private theorem elaborate_matcher_exact :
    M4.elaborateFuel Paper1FrozenSignature.signature 9 []
        (.matcher [emptyClause]) ⟨0, 0⟩ =
      some
        (MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcherGenerated,
          ⟨3, 2⟩) := by
  have checked : MatcherTyping.staticChecks Paper1FrozenSignature.signature
      [emptyClause] = true := by
    simpa [emptyClause] using
      (MatcherTyping.staticChecksHold_iff Paper1FrozenSignature.signature
        [MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause]).1
        MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause_staticChecks
  unfold M4.elaborateFuel M4.elaborateFuelUsing
  change MatcherTyping.elaborateMatcherLiteralUsing
      (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 8)
      Paper1FrozenSignature.signature [] [emptyClause] ⟨0, 0⟩ =
    some
      (MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcherGenerated,
        ⟨3, 2⟩)
  unfold MatcherTyping.elaborateMatcherLiteralUsing
  rw [show MatcherTyping.staticChecks Paper1FrozenSignature.signature
      [emptyClause] = true from checked]
  simp only [if_true,
    MatcherTyping.elaborateMatcherClausesUsing,
    MatcherTyping.elaborateMatcherClauseUsing]
  have shape : emptyClause.toShape.check Paper1FrozenSignature.signature =
      true := by
    have shapes := (MatcherClause.shapesWellFormed_iff
      Paper1FrozenSignature.signature [emptyClause]).1
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause_staticChecks.shapes
    simpa [MatcherClause.checkShapes, MatcherClauseShapes.check,
      MatcherClauseShapes.catchAllLast, MatcherClauseShapes.isCatchAll,
      emptyClause,
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause] using shapes
  rw [shape]
  simp only [if_true, emptyClause,
    MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause,
    MatcherClause.header, MatcherClause.nextMatchers, MatcherClause.arms,
    MatcherTyping.elaboratePPat,
    MatcherTyping.elaboratePPatFuel, Option.bind_some,
    MatcherTyping.elaborateNextMatchersUsing,
    MatcherTyping.elaborateCheckedExpressionUsing]
  simp [Pattern.extendContext]
  rw [elaborate_next_matcher_exact]
  simp only [Option.bind_some, MatcherTyping.elaborateMatcherArmsUsing,
    MatcherTyping.elaborateMatcherArmUsing, MatcherTyping.elaborateDPat,
    MatcherTyping.elaborateDPatFuel, Pattern.extendContext,
    MatcherTyping.elaborateCheckedExpressionUsing]
  simp [Pattern.extendContext, MatcherTyping.holeProductTarget]
  rw [elaborate_empty_list_exact]
  simp [MatcherTyping.GeneratedChecks.checked,
    MatcherTyping.GeneratedChecks.append,
    MatcherTyping.GeneratedChecks.empty,
    MatcherTyping.evidenceEquations,
    MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcherGenerated,
    emptyClause,
    MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause,
    MatcherTyping.holeProductTarget]

private theorem elaborate_matcher_public_callback_exact :
    M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 14 []
        (.matcher [emptyClause]) ⟨0, 0⟩ =
      some
        (MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcherGenerated,
          ⟨3, 2⟩) := by
  exact M4.elaborateFuelUsing_success_mono
    (solveHard := unify) (signature := Paper1FrozenSignature.signature)
    (smaller := 9) (larger := 14) (by omega)
    (by simpa [M4.elaborateFuel] using elaborate_matcher_exact)

private def inferenceArms : MatchFirstTyping.GeneratedArms :=
  { target := .int
    hard := [.ty (.var ⟨3⟩) .int, .ty .int .int]
    pending := [
      ⟨.matcher (.var ⟨0⟩) (.var ⟨0⟩),
        .slot (.var ⟨2⟩) .int⟩] }

private theorem elaborate_arms_exact :
    MatchFirstTyping.elaborateArmsUsing
        (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 14)
        Paper1FrozenSignature.signature [] .int
        (.matcher (.var ⟨0⟩) (.var ⟨0⟩)) (.lit 7)
        [.mk .wild (.lit 42)] ⟨3, 2⟩ =
      some (inferenceArms, ⟨4, 3⟩) := by
  rfl'

private theorem elaborate_expression_exact :
    M4.elaborate Paper1FrozenSignature.signature [] expression ⟨0, 0⟩ =
      some (inferenceGenerated, ⟨4, 3⟩) := by
  unfold M4.elaborate
  change M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 15 []
      expression ⟨0, 0⟩ = some (inferenceGenerated, ⟨4, 3⟩)
  unfold M4.elaborateFuelUsing
  change MatchFirstTyping.elaborateUsing
      (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 14)
      Paper1FrozenSignature.signature [] (.lit 0) (.matcher [emptyClause])
      [.mk .wild (.lit 42)] (.lit 7) ⟨0, 0⟩ =
        some (inferenceGenerated, ⟨4, 3⟩)
  unfold MatchFirstTyping.elaborateUsing
  rw [show M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 14 []
      (.lit 0) ⟨0, 0⟩ = some (⟨.int, [], []⟩, ⟨0, 0⟩) by rfl]
  change (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 14 []
      (.matcher [emptyClause]) ⟨0, 0⟩).bind (fun matcherOutput =>
        (MatchFirstTyping.elaborateArmsUsing
          (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 14)
          Paper1FrozenSignature.signature [] .int matcherOutput.1.target
          (.lit 7) [.mk .wild (.lit 42)] matcherOutput.2).bind
            (fun armsOutput => some
              (MatchFirstTyping.Generated.fromMatchFirst ⟨.int, [], []⟩
                matcherOutput.1 armsOutput.1, armsOutput.2))) =
      some (inferenceGenerated, ⟨4, 3⟩)
  rw [elaborate_matcher_public_callback_exact]
  change (MatchFirstTyping.elaborateArmsUsing
      (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 14)
      Paper1FrozenSignature.signature [] .int
      (.matcher (.var ⟨0⟩) (.var ⟨0⟩)) (.lit 7)
      [.mk .wild (.lit 42)] ⟨3, 2⟩).bind (fun armsOutput =>
        some (MatchFirstTyping.Generated.fromMatchFirst ⟨.int, [], []⟩
          MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcherGenerated
          armsOutput.1, armsOutput.2)) =
    some (inferenceGenerated, ⟨4, 3⟩)
  rw [elaborate_arms_exact]
  simp [inferenceArms,
    MatchFirstTyping.Generated.fromMatchFirst,
    MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcherGenerated,
    inferenceGenerated]

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

private theorem close_inference_exact :
    (inferGeneratedUsing unify inferenceGenerated).bind
      (fun closed => some closed.target) = some .int := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [inferenceGenerated, DataTypes.list]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  unfold saturateLoop
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have nextResolution :
      resolve (.matcher .any (.var ⟨1⟩))
          (.slot (.var ⟨1⟩) (.var ⟨0⟩)) =
        .matcherToSlot .any (.var ⟨1⟩) (.var ⟨1⟩) (.var ⟨0⟩)
          .equal := by
    rfl
  have useResolution :
      resolve (.matcher .any (.var ⟨0⟩)) (.slot (.var ⟨2⟩) .int) =
        .matcherToSlot .any (.var ⟨2⟩) (.var ⟨0⟩) .int .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [nextResolution, useResolution]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

private theorem wildcardInput_of_singleHoleClause
    (plain : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      PPatElaborates DPatElaborates Paper1FrozenSignature.signature context
      [.mk .hole nextMatchers arms] supply generated next) :
    MatcherLiteralTotalInputElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      Paper1FrozenSignature.signature
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      solution atomEnvironmentTypes .wild context
      [.mk .hole nextMatchers arms] supply generated next := by
  cases plain
  rename_i generatedClauses checked clauses
  cases clauses with
  | cons head tail =>
      cases head
      rename_i generatedHeader afterHeader generatedNext afterNext generatedArms
        nextMatchersElaboration shape headerElaboration armsElaboration
      cases headerElaboration
      cases tail
      exact .mk checked (.cons
        (.mk shape.check_eq_true .hole nextMatchersElaboration
          armsElaboration (by
          intro dispatch inspected
          simp [inspectPatternPattern] at inspected
          subst dispatch
          exact .nil))
        .nil)

private theorem matcherInput :
    MatcherLiteralTotalInputElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature 9)
      Paper1FrozenSignature.signature
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.solved [] .wild []
      [emptyClause] ⟨0, 0⟩
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcherGenerated
      ⟨3, 2⟩ := by
  simpa [emptyClause,
    MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause] using
    (wildcardInput_of_singleHoleClause
      (solution :=
        MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.solved)
      (atomEnvironmentTypes := [])
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcher_m4FuelElaborates)

private theorem clausesInput :
    RuntimeMatcherClausesInputTyping [] [] .int .wild [emptyClause] := by
  simpa [MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.solved,
    Ty.apply] using matcherInput.toRuntimeInputTyping_of_m4Fuel
      Paper1FrozenSignature.runtimeCompatible
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause_runtimeSupported
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcher_semantic
      MonomorphicContextCompatible.nil

private theorem finalCatchAll : MatcherTyping.FinalCatchAll [emptyClause] :=
  (MatcherTyping.finalCatchAll_iff [emptyClause]).2 (by rfl)

/-- The actual wildcard dispatch of this matcher can only return the empty
branch list.  In particular, no conclusion-equivalent assumption about a
fabricated branch is used. -/
theorem dispatch_returns_no_branches
    (fuel : Nat) (atomEnvironment : ValueEnvironment) (target : Value)
    {branches : MatchingBranches}
    (success : dispatchMatcherClauses (evalFuel fuel) atomEnvironment []
      [emptyClause] .wild target = .ok (.hit branches)) :
    branches = [] := by
  cases fuel with
  | zero =>
    simp [dispatchMatcherClauses, firstHit, tryMatcherClause, tryMatcherArm,
      emptyClause,
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause,
      inspectPatternPattern, FuelResult.traverse, evalFuel,
      matchValueDataPattern, decodeDecompositions, decodeProduct,
      buildMatchingBranches, DataCtor.nil] at success
  | succ fuel =>
    simp [dispatchMatcherClauses, firstHit, tryMatcherClause, tryMatcherArm,
      emptyClause,
      MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.clause,
      inspectPatternPattern, FuelResult.traverse, evalFuel,
      matchValueDataPattern, decodeDecompositions, decodeProduct,
      buildMatchingBranches, closeMatcherArmsResult, Value.viewList,
      DataCtor.nil] at success
    exact success

private theorem initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (environmentTyped : EnvironmentTyping environment [])
    (_targetSuccess : evalFuel fuel environment (.lit 0) = .ok targetValue)
    (matcherSuccess : evalFuel fuel environment (.matcher [emptyClause]) =
      .ok matcherValue)
    (targetTyped : ValueTyping targetValue .int)
    (_matcherTyped : ValueTyping matcherValue (.matcher .any .int)) :
    TotalMatchingAtomTyping [] [] ⟨.wild, matcherValue, targetValue⟩ [] := by
  cases environmentTyped
  cases fuel with
  | zero => simp [evalFuel] at matcherSuccess
  | succ fuel =>
      simp [evalFuel] at matcherSuccess
      subst matcherValue
      apply TotalMatchingAtomTyping.user (by
        intro eval atomEnvironment
        rfl) EnvironmentTyping.nil targetTyped clausesInput finalCatchAll
      intro dispatchFuel atomEnvironment holes recursiveBranches dispatched
        delegated branch member
      have empty := dispatch_returns_no_branches dispatchFuel atomEnvironment
        targetValue dispatched
      subst recursiveBranches
      simp at member

/-- Exact public M4 inference for this closed fixture. -/
theorem expression_infer_exact :
    M4.infer Paper1FrozenSignature.signature [] expression = some .int := by
  unfold M4.infer
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    elaborate_expression_exact]
  exact close_inference_exact

/-- Fixture-specific total-runtime certificate for the actual user matcher.
It is assembled from the exact recursive-M4 matcher derivation and its
dispatch-indexed input certificate, without using the top-level
`expression_infer_exact` proof or the fixed-fuel `expression_eval_exact`. -/
theorem expression_total_core_typing : TotalCoreTyping expression .int [] := by
  exact .matchFirst (.core (.lit 0))
    MatcherTyping.M4RecursiveMatcherTotalBridgeRegression.matcher_totalCoreTyping
    (.cons initialAtom (.core (.lit 42)) .nil) (.core (.lit 7))

/-- The exact inference computation supplies the static component, while the
fixture-specific certificate above supplies the independent runtime
component. -/
theorem publicTypingAndTotalCoreTyping :
    M4.Typing Paper1FrozenSignature.signature [] expression .int ∧
      TotalCoreTyping expression .int [] :=
  ⟨M4.infer_success_typing Paper1FrozenSignature.wellFormed
      expression_infer_exact,
    expression_total_core_typing⟩

/-- Mandatory-else semantics is observable: the matcher yields no branch,
so the fallback value is selected. -/
theorem expression_eval_exact : evalFuel 30 [] expression = .ok (.int 7) := by
  with_unfolding_all rfl

/-- Relational evaluation follows from the exact fuel-indexed execution. -/
theorem expression_eval_relational : Eval [] expression (.int 7) :=
  evalFuel_sound expression_eval_exact

/-- Common-fuel safety follows for every fuel from the fixture-specific total
runtime certificate. -/
theorem expression_never_stuck (fuel : Nat) :
    (evalFuel fuel [] expression).NotStuck :=
  expression_total_core_typing.neverStuck fuel [] .nil

/-- Public boundary: an erased callback over arbitrary type-compatible
branches cannot justify the zero-binding wildcard conclusion.  An exact
dispatch index is therefore necessary for this erased-callback interface. -/
theorem no_erased_wildcard_zero_binding_bridge
    (targetTyped : ValueTyping target targetType)
    (branches : ∀ {holes recursiveBranches},
      DelegatedMatchingBranchesTyping holes recursiveBranches →
      ∀ branch ∈ recursiveBranches,
        TotalMatchingAtomsTyping environmentTypes bindingTypes branch []) :
    False :=
  erasedBranches_cannot_preserve_wildcard_zeroBindings targetTyped branches

end TypePM.Source.M4UserMatcherMatchFirstRegression
