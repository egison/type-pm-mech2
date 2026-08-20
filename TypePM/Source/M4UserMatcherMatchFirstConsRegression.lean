import TypePM.Source.M4MatchFirstTotalCoreBridge
import TypePM.UserMatcherGeneralSafetyRegression
import TypePM.Runtime.EvaluationAdequacy

/-!
# Constructor-binding `matchFirst` with a user matcher

This fixture is the first explicit-else `matchFirst` regression in which an
actual user matcher returns a nonempty branch. Its constructor arm delegates
the source pattern `cons [var, wild]` to two `something` matchers. The first
delegated atom binds the integer target and the ordinary arm reads that
binding; the distinct integer fallback makes arm selection observable.

The runtime matcher deliberately has only the selected constructor clause and
the mandatory final catch-all. This is the smallest useful dispatch fixture,
but M4's frozen-signature coverage check requires general clauses for every
constructor of the mentioned `List` pattern former. Consequently the public
inference boundary is the exact rejection theorem below. Completing those
clauses with the intended list decompositions requires the recursive list
matcher, which is beyond the current nonrecursive `TotalCoreTyping.matcher`
constructor; shallow coverage alone could also be satisfied by nonrecursive
stub clauses. All results below the boundary are premise-free and indexed by
the actual dispatch result.
-/

namespace TypePM.Source.M4UserMatcherMatchFirstConsRegression

open TypePM.Runtime
open TypePM.Source.MatcherTyping

abbrev constructorClause : MatcherClause :=
  TypePM.UserMatcherGeneralSafetyRegression.twoHoleClause

abbrev constructorPattern : Pattern :=
  TypePM.UserMatcherGeneralSafetyRegression.twoHolePattern

def fallbackBody : Expr := .ctor DataCtor.nil []

def fallbackClause : MatcherClause :=
  .mk .hole .something [.mk .var fallbackBody]

def clauses : List MatcherClause := [constructorClause, fallbackClause]

def userMatcher : Expr := .matcher clauses

def ordinaryArm : MatchFirstArm := .mk constructorPattern (.var 0)

def expression : Expr :=
  .matchFirst (.lit 99) userMatcher [ordinaryArm] (.lit 7)

def expectedBranches : MatchingBranches :=
  [[⟨.var, .something, .int 99⟩, ⟨.wild, .something, .int 99⟩]]

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-! ## Exact M4 pattern boundary -/

def patternGenerated : GeneratedPattern :=
  { dual :=
      ⟨.con PatternFormer.list [.var ⟨0⟩],
        DataTypes.list (.var ⟨0⟩)⟩
    bindings := [.var ⟨1⟩]
    hard := [
      .ty (.var ⟨1⟩) (.var ⟨0⟩),
      .cap (.var ⟨1⟩) (.var ⟨0⟩),
      .ty (.var ⟨2⟩) (DataTypes.list (.var ⟨0⟩)),
      .cap (.var ⟨2⟩) (.con PatternFormer.list [.var ⟨0⟩])]
    pending := [] }

/-- Executable M4 pattern synthesis records the constructor capability and
the single left-to-right binding exactly. -/
theorem elaborate_constructor_pattern_exact :
    elaboratePatternUsing
        (M4.elaborateFuel Paper1FrozenSignature.signature 8)
        Paper1FrozenSignature.signature [] [] constructorPattern [] ⟨0, 0⟩ =
      some (patternGenerated, ⟨3, 3⟩) := by
  rfl

/-- Independent source/M4 derivation of the same constructor pattern. The
callback is genuinely M4-indexed, although this pattern has no embedded
expression and therefore does not invoke it. -/
theorem constructor_pattern_m4_derivation :
    PatternElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature 8)
      Paper1FrozenSignature.signature [] [] constructorPattern [] ⟨0, 0⟩
      patternGenerated ⟨3, 3⟩ := by
  refine elaboratePatternUsing_sound
    (elaborateExpression :=
      M4.elaborateFuel Paper1FrozenSignature.signature 8)
    (ExpressionElaborates :=
      M4.ElaboratesFuel Paper1FrozenSignature.signature 8) ?_
    Paper1FrozenSignature.wellFormed elaborate_constructor_pattern_exact
  intro context expression supply generated next success
  exact M4.elaborateFuel_sound Paper1FrozenSignature.wellFormed success

/-- The two-clause runtime fixture is rejected at exactly the root-coverage
gate: mentioning the `List` former requires general `nil`, `cons`, and `join`
clauses, not only the selected `cons` clause and final catch-all. -/
theorem root_coverage_rejected_exact :
    rootCoverageOK Paper1FrozenSignature.signature clauses = false := by
  rfl

/-- Shape checking, arm coverage, and the final catch-all all succeed.  This
separates the root-coverage failure from the other three static checks. -/
theorem noncoverage_static_checks_accept_exact :
    (MatcherClause.checkShapes Paper1FrozenSignature.signature clauses &&
      clauses.all (fun clause =>
        armCoverageOK Paper1FrozenSignature.signature clause.arms ||
          structurallyRefinedArmCoverage clause) &&
      finalCatchAllVariableArm clauses) = true := by
  have shapes :
      MatcherClause.checkShapes Paper1FrozenSignature.signature clauses =
        true := by
    simp [clauses, constructorClause, fallbackClause,
      TypePM.UserMatcherGeneralSafetyRegression.twoHoleClause,
      MatcherClause.checkShapes, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShapes.check, MatcherClauseShapes.catchAllLast,
      MatcherClauseShapes.isCatchAll, MatcherClauseShape.check,
      MatcherArmHeader.check, MatcherArmHeader.canonical,
      HoleConvention.ofCount, PPat.shapeOK, PPat.shapesOK,
      PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
      PPat.occurrences, PPat.holeCount, DPat.shapeOK,
      Paper1FrozenSignature.lookup_pattern_cons, ListPatternSchemes.cons]
  have arms : clauses.all (fun clause =>
      armCoverageOK Paper1FrozenSignature.signature clause.arms ||
        structurallyRefinedArmCoverage clause) = true := by
    rfl
  have final : finalCatchAllVariableArm clauses = true := by
    rfl
  simp [shapes, arms, final]

theorem static_checks_rejected_exact :
    staticChecks Paper1FrozenSignature.signature clauses = false := by
  unfold staticChecks
  rw [root_coverage_rejected_exact]
  simp

/-- No result type admits an independent public M4 typing derivation for the
fixture: every such derivation would contain a matcher-literal derivation,
whose proof-level static-check certificate contradicts the exact root-
coverage rejection above. -/
theorem expression_not_typable (target : Ty) :
    ¬ M4.Typing Paper1FrozenSignature.signature [] expression target := by
  rintro ⟨_, ⟨derivation⟩, _⟩
  rcases derivation with
    ⟨generated, next, ⟨fuel, elaboration⟩, _, _, _⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at elaboration
  | succ fuel =>
      change MatchFirstTyping.ElaboratesUsing
        (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
        Paper1FrozenSignature.signature [] expression
        (Context.initialSupply []) generated next at elaboration
      cases elaboration with
      | matchFirst _ matcherElaboration _ =>
          cases fuel with
          | zero => simp [M4.ElaboratesFuel] at matcherElaboration
          | succ innerFuel =>
              change MatcherLiteralElaboratesUsing
                (M4.ElaboratesFuel Paper1FrozenSignature.signature innerFuel)
                PPatElaborates DPatElaborates
                Paper1FrozenSignature.signature [] clauses _ _ _
                at matcherElaboration
              cases matcherElaboration with
              | mk checked _ =>
                  have accepted :
                      staticChecks Paper1FrozenSignature.signature clauses =
                        true :=
                    (staticChecksHold_iff
                      Paper1FrozenSignature.signature clauses).1 checked
                  rw [static_checks_rejected_exact] at accepted
                  contradiction

/-- Strongest honest public-inference statement for this nonrecursive
fixture.  The three preceding equations isolate root coverage as the failing
matcher-literal gate, after target elaboration and before the outer arm can be
accepted. -/
theorem expression_infer_none :
    M4.infer Paper1FrozenSignature.signature [] expression = none := by
  cases result : M4.infer Paper1FrozenSignature.signature [] expression with
  | none => rfl
  | some target =>
      exact False.elim (expression_not_typable target
        (M4.infer_success_typing Paper1FrozenSignature.wellFormed result))

/-! ## Input-indexed runtime dispatch -/

private theorem fallbackClause_inputTyping :
    RuntimeMatcherClauseInputTyping [] [] .int constructorPattern
      fallbackClause := by
  apply RuntimeMatcherClauseInputTyping.mk
    (holes := [⟨.any, .int⟩]) (captureTypes := [])
  · exact .hole .any
  · exact .one (.checked (.something .int) (.matcherToSlot .equal))
  · exact .cons (.mk .var (.listNil .int)) .nil
  · intro dispatch inspected
    simp [inspectPatternPattern] at inspected
    subst dispatch
    exact .nil

private theorem clausesInputTyping :
    RuntimeMatcherClausesInputTyping [] [] .int constructorPattern clauses := by
  exact .cons
    TypePM.UserMatcherGeneralSafetyRegression.twoHoleClause_input_typed
    (.cons fallbackClause_inputTyping .nil)

private theorem finalCatchAll : FinalCatchAll clauses := by
  exact .skip .last

private theorem decompositionBody_exact (fuel : Nat) :
    evalFuel (fuel + 1 + 1 + 1) [.int 99]
        TypePM.UserMatcherGeneralSafetyRegression.pairProductListBody =
      .ok (Value.buildList [.tuple [.int 99, .int 99]]) := by
  rfl

private theorem decompositionBody_unfolded_exact (fuel : Nat) :
    evalFuel (fuel + 1 + 1 + 1) [.int 99]
        (.ctor DataCtor.cons
          [.tuple [.var 0, .var 0], .ctor DataCtor.nil []]) =
      .ok (Value.buildList [.tuple [.int 99, .int 99]]) := by
  rfl

private theorem nextMatchers_exact (fuel : Nat) :
    evalFuel (fuel + 1 + 1 + 1) [] (.tuple [.something, .something]) =
      .ok (.tuple [.something, .something]) := by
  rfl

/-- The certificate is indexed by the dispatch's real input pattern and
result. At insufficient callback fuel dispatch times out; every successful
dispatch returns exactly the one nonempty branch below. -/
theorem dispatch_success_exact
    (success : dispatchMatcherClauses (evalFuel fuel) atomEnvironment []
      clauses constructorPattern (.int 99) = .ok (.hit branches)) :
    branches = expectedBranches := by
  cases fuel with
  | zero =>
      simp [clauses, constructorClause, constructorPattern,
        TypePM.UserMatcherGeneralSafetyRegression.twoHoleClause,
        TypePM.UserMatcherGeneralSafetyRegression.twoHolePattern,
        TypePM.UserMatcherGeneralSafetyRegression.pairProductListBody,
        dispatchMatcherClauses, firstHit, tryMatcherClause, tryMatcherArm,
        inspectPatternPattern, inspectPatternPatterns, matchValueDataPattern,
        PatternDispatch.empty, PatternDispatch.append,
        FuelResult.traverse, evalFuel] at success
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [clauses, constructorClause, constructorPattern,
            TypePM.UserMatcherGeneralSafetyRegression.twoHoleClause,
            TypePM.UserMatcherGeneralSafetyRegression.twoHolePattern,
            TypePM.UserMatcherGeneralSafetyRegression.pairProductListBody,
            dispatchMatcherClauses, firstHit, tryMatcherClause, tryMatcherArm,
            inspectPatternPattern, inspectPatternPatterns,
            matchValueDataPattern, PatternDispatch.empty, PatternDispatch.append,
            FuelResult.traverse, evalFuel] at success
      | succ fuel =>
          cases fuel with
          | zero =>
              simp [clauses, constructorClause, constructorPattern,
                TypePM.UserMatcherGeneralSafetyRegression.twoHoleClause,
                TypePM.UserMatcherGeneralSafetyRegression.twoHolePattern,
                TypePM.UserMatcherGeneralSafetyRegression.pairProductListBody,
                dispatchMatcherClauses, firstHit, tryMatcherClause,
                tryMatcherArm, inspectPatternPattern, inspectPatternPatterns,
                matchValueDataPattern, PatternDispatch.empty,
                PatternDispatch.append,
                FuelResult.traverse, evalFuel] at success
          | succ fuel =>
              have branchEquality : expectedBranches = branches := by
                simpa [clauses, constructorClause, constructorPattern,
                expectedBranches,
                TypePM.UserMatcherGeneralSafetyRegression.twoHoleClause,
                TypePM.UserMatcherGeneralSafetyRegression.twoHolePattern,
                TypePM.UserMatcherGeneralSafetyRegression.pairProductListBody,
                dispatchMatcherClauses, firstHit, tryMatcherClause,
                tryMatcherArm, inspectPatternPattern, inspectPatternPatterns,
                matchValueDataPattern, PatternDispatch.empty,
                PatternDispatch.append,
                decompositionBody_exact, decompositionBody_unfolded_exact,
                nextMatchers_exact,
                FuelResult.traverse,
                decodeDecompositions, decodeProduct, buildMatchingBranches,
                zipMatchingAtoms, closeMatcherArmsResult,
                FuelResult.bind, FuelResult.map,
                Value.viewList, Value.buildList,
                Value.nilValue, Value.consValue] using success
              exact branchEquality.symm

/-- Concrete successful dispatch, including the constructor arm's preserved
`var, wild` source order. -/
theorem dispatch_at_three_exact :
    dispatchMatcherClauses (evalFuel 3) [] [] clauses constructorPattern
      (.int 99) = .ok (.hit expectedBranches) := by
  with_unfolding_all rfl

private theorem initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (environmentTyped : EnvironmentTyping environment [])
    (targetSuccess : evalFuel fuel environment (.lit 99) = .ok targetValue)
    (matcherSuccess : evalFuel fuel environment userMatcher = .ok matcherValue)
    (targetTyped : ValueTyping targetValue .int)
    (_matcherTyped : ValueTyping matcherValue (.matcher .any .int)) :
    TotalMatchingAtomTyping [] []
      ⟨constructorPattern, matcherValue, targetValue⟩ [.int] := by
  cases environmentTyped
  cases fuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ fuel =>
      simp [evalFuel, userMatcher] at targetSuccess matcherSuccess
      subst targetValue
      subst matcherValue
      apply TotalMatchingAtomTyping.user
      · intro evaluate atomEnvironment
        rfl
      · exact .nil
      · exact .int 99
      · exact clausesInputTyping
      · exact finalCatchAll
      · intro dispatchFuel atomEnvironment holes recursiveBranches
          dispatched delegated branch member
        have exactBranches := dispatch_success_exact dispatched
        subst recursiveBranches
        simp [expectedBranches] at member
        subst branch
        exact .cons (.builtin (.somethingVar (.int 99)))
          (.cons (.builtin (.somethingWild (.int 99))) .nil)

/-! ## Total core and exact evaluation -/

/-- Complete total-core certificate. The arm body is typed under
`[int] ++ []`, while the fallback remains under the original empty context. -/
theorem expression_total_core_typing : TotalCoreTyping expression .int [] := by
  exact .matchFirst (.core (.lit 99))
    (.matcher clausesInputTyping.runtimeTyping)
    (.cons initialAtom (.core (.var rfl)) .nil)
    (.core (.lit 7))

/-- The ordinary arm reads its binding and suppresses the distinct fallback. -/
theorem expression_eval_exact : evalFuel 12 [] expression = .ok (.int 99) := by
  with_unfolding_all rfl

/-- Relational evaluation follows from the exact fuel-indexed execution. -/
theorem expression_eval_relational : Eval [] expression (.int 99) :=
  evalFuel_sound expression_eval_exact

/-- Target evaluation still precedes matcher evaluation and fallback choice. -/
theorem target_stuck_precedes_matcher_and_fallback :
    evalFuel 12 []
      (.matchFirst (.var 0) userMatcher [ordinaryArm] (.lit 7)) = .stuck := by
  with_unfolding_all rfl

/-- Common-fuel safety is independent of the one successful run above. -/
theorem expression_never_stuck (fuel : Nat) :
    (evalFuel fuel [] expression).NotStuck :=
  expression_total_core_typing.neverStuck fuel [] .nil

end TypePM.Source.M4UserMatcherMatchFirstConsRegression
