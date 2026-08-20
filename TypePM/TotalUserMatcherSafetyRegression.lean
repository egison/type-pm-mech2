import TypePM.CommonFuelSafety
import TypePM.RecursiveTotalMatchingSafety
import TypePM.Source.M4RecursiveMatcherTotalBridge

/-!
# Recursive matcher-body regression

This focused matcher has the same dynamic recursion boundary as the Paper-1
`multiset` clauses: its selected arm evaluates a `matchAll` expression before
the next matcher is evaluated.  The callback-parametric clause certificate is
instantiated with `TotalCoreTyping`, and ordinary `evalFuel` safety is then
discharged by the common-fuel theorem.
-/

namespace TypePM.TotalUserMatcherSafetyRegression

open TypePM.Runtime
open TypePM.Source

abbrev TotalExpressionTyping : EmbeddedExpressionTyping :=
  fun context expression target => TotalCoreTyping expression target context

def recursiveBody : Source.Expr :=
  .matchAll (.lit 7) .something .var (.var 0)

def recursiveClause : MatcherClause :=
  .mk .hole .something
    [.mk .var recursiveBody]

def recursiveMatcher : Source.Expr := Source.Expr.matcher [recursiveClause]

def recursiveGenerated : Generated :=
  { target := .matcher (.var ⟨0⟩) (.var ⟨0⟩)
    hard := [.cap (.var ⟨0⟩) .any, .ty (.var ⟨2⟩) .int]
    pending := [
      ⟨.matcher .any (.var ⟨1⟩), .slot (.var ⟨1⟩) (.var ⟨0⟩)⟩,
      ⟨.matcher .any (.var ⟨3⟩), .slot (.var ⟨2⟩) .int⟩,
      ⟨DataTypes.list (.var ⟨2⟩), DataTypes.list (.var ⟨0⟩)⟩] }

def recursiveSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

def recursiveBodyGenerated : Generated :=
  { target := DataTypes.list (.var ⟨2⟩)
    hard := [.ty (.var ⟨2⟩) .int]
    pending := [
      ⟨.matcher .any (.var ⟨3⟩), .slot (.var ⟨2⟩) .int⟩] }

theorem recursiveBody_elaborateFuel_exact :
    M4.elaborateFuel Paper1FrozenSignature.signature 29
      [.mono (.var ⟨0⟩)] recursiveBody ⟨2, 2⟩ =
        some (recursiveBodyGenerated, ⟨4, 3⟩) := by
  with_unfolding_all rfl

private def recursiveCallback : MatcherTyping.ExpressionElaborator :=
  M4.elaborateFuel Paper1FrozenSignature.signature 29

private def recursiveHeader : MatcherTyping.GeneratedPPat :=
  ⟨[⟨Cap.var ⟨1⟩, Ty.var ⟨0⟩⟩], [], none, []⟩

private def recursiveNext : MatcherTyping.GeneratedChecks :=
  ⟨[], [⟨.matcher .any (.var ⟨1⟩),
    .slot (.var ⟨1⟩) (.var ⟨0⟩)⟩]⟩

private def recursiveArm : MatcherTyping.GeneratedChecks :=
  { hard := recursiveBodyGenerated.hard
    pending := recursiveBodyGenerated.pending ++
      [⟨recursiveBodyGenerated.target, DataTypes.list (.var ⟨0⟩)⟩] }

private def recursiveArms : MatcherTyping.GeneratedArms :=
  ⟨recursiveArm.append MatcherTyping.GeneratedChecks.empty⟩

private def recursiveClauseGenerated : MatcherTyping.GeneratedMatcherClause :=
  { holes := recursiveHeader.holes
    evidence := none
    checks :=
      { hard := recursiveNext.hard ++ recursiveArms.checks.hard
        pending := recursiveNext.pending ++ recursiveArms.checks.pending } }

private def recursiveClausesGenerated : MatcherTyping.GeneratedMatcherClauses :=
  ⟨[], recursiveClauseGenerated.checks.append
    MatcherTyping.GeneratedChecks.empty⟩

private theorem recursive_header_exact :
    MatcherTyping.elaboratePPat Paper1FrozenSignature.signature .hole
      (.var ⟨0⟩) none ⟨1, 1⟩ = some (recursiveHeader, ⟨1, 2⟩) := by
  rfl

private theorem recursive_next_exact :
    MatcherTyping.elaborateNextMatchersUsing recursiveCallback [] .something
      recursiveHeader.holes ⟨1, 2⟩ = some (recursiveNext, ⟨2, 2⟩) := by
  rfl

private theorem recursive_arm_exact :
    MatcherTyping.elaborateMatcherArmUsing recursiveCallback
      Paper1FrozenSignature.signature [] [] (.var ⟨0⟩)
      recursiveHeader.holes (.mk .var recursiveBody) ⟨2, 2⟩ =
        some (recursiveArm, ⟨4, 3⟩) := by
  simp only [MatcherTyping.elaborateMatcherArmUsing,
    MatcherTyping.elaborateDPat, MatcherTyping.elaborateDPatFuel,
    Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map, List.cons_append, List.nil_append,
    MatcherTyping.elaborateCheckedExpressionUsing, recursiveCallback]
  rw [recursiveBody_elaborateFuel_exact]
  rfl

private theorem recursive_arms_exact :
    MatcherTyping.elaborateMatcherArmsUsing recursiveCallback
      Paper1FrozenSignature.signature [] [] (.var ⟨0⟩)
      recursiveHeader.holes [MatcherArm.mk .var recursiveBody] ⟨2, 2⟩ =
        some (recursiveArms, ⟨4, 3⟩) := by
  simp only [MatcherTyping.elaborateMatcherArmsUsing]
  rw [recursive_arm_exact]
  rfl

private theorem recursive_clause_exact :
    MatcherTyping.elaborateMatcherClauseUsing recursiveCallback
      Paper1FrozenSignature.signature [] (.var ⟨0⟩) recursiveClause
      ⟨1, 1⟩ = some (recursiveClauseGenerated, ⟨4, 3⟩) := by
  unfold recursiveClause
  have shape :
      (MatcherClause.mk .hole .something
        [MatcherArm.mk .var recursiveBody]).toShape.check
          Paper1FrozenSignature.signature = true := by
    simp [MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount, PPat.shapeOK,
      PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
      PPat.occurrences, PPat.holeCount, DPat.shapeOK]
  simp only [MatcherTyping.elaborateMatcherClauseUsing, shape, if_true]
  simp only [MatcherClause.header, MatcherClause.nextMatchers,
    MatcherClause.arms]
  rw [recursive_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, recursiveHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  have nextExact :
      MatcherTyping.elaborateNextMatchersUsing recursiveCallback [] .something
        [⟨Cap.var ⟨1⟩, Ty.var ⟨0⟩⟩] ⟨1, 2⟩ =
          some (recursiveNext, ⟨2, 2⟩) := by
    simpa [recursiveHeader] using recursive_next_exact
  rw [nextExact]
  simp only [Option.bind_some]
  have armsExact :
      MatcherTyping.elaborateMatcherArmsUsing recursiveCallback
        Paper1FrozenSignature.signature [] [] (.var ⟨0⟩)
        [⟨Cap.var ⟨1⟩, Ty.var ⟨0⟩⟩]
        [MatcherArm.mk .var recursiveBody] ⟨2, 2⟩ =
          some (recursiveArms, ⟨4, 3⟩) := by
    simpa [recursiveHeader] using recursive_arms_exact
  rw [armsExact]
  rfl

private theorem recursive_clauses_exact :
    MatcherTyping.elaborateMatcherClausesUsing recursiveCallback
      Paper1FrozenSignature.signature [] (.var ⟨0⟩) [recursiveClause]
      ⟨1, 1⟩ = some (recursiveClausesGenerated, ⟨4, 3⟩) := by
  simp only [MatcherTyping.elaborateMatcherClausesUsing]
  rw [recursive_clause_exact]
  rfl

theorem recursiveMatcher_elaborateFuel_exact :
    M4.elaborateFuel Paper1FrozenSignature.signature 30 [] recursiveMatcher
      ⟨0, 0⟩ = some (recursiveGenerated, ⟨4, 3⟩) := by
  change MatcherTyping.elaborateMatcherLiteralUsing recursiveCallback
    Paper1FrozenSignature.signature [] [recursiveClause] ⟨0, 0⟩ = _
  have checked : MatcherTyping.staticChecks Paper1FrozenSignature.signature
      [recursiveClause] = true := by
    simp [MatcherTyping.staticChecks, recursiveClause,
      MatcherClause.checkShapes, MatcherClause.toShape,
      MatcherClauseShapes.check, MatcherClauseShapes.catchAllLast,
      MatcherClauseShapes.isCatchAll, MatcherClauseShape.check, MatcherClause.header,
      MatcherClause.arms, MatcherArm.toHeader,
      MatcherArmHeader.check, MatcherArmHeader.canonical,
      MatcherTyping.armCoverageOK, MatcherTyping.armsCatchAllLast,
      MatcherTyping.finalCatchAllVariableArm, MatcherTyping.rootCoverageOK,
      MatcherTyping.DPat.isIrrefutable, MatcherArm.header,
      MatcherTyping.PPat.rootFormer?, PPat.shapeOK,
      PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
      PPat.occurrences, PPat.holeCount,
      HoleConvention.ofCount, DPat.shapeOK,
      Paper1FrozenSignature.signature, Paper1Signature.signature,
      Paper1Signature.patternConstructors, ListPatternSchemes.nil,
      ListPatternSchemes.cons, ListPatternSchemes.join]
  simp only [MatcherTyping.elaborateMatcherLiteralUsing, checked, if_true]
  rw [recursive_clauses_exact]
  rfl

/-- The recursive-body fixture is accepted by the actual fuel-indexed M4
elaborator, not only by the runtime certificate layer. -/
theorem recursiveMatcher_m4FuelElaborates :
    MatcherTyping.MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature 29)
      MatcherTyping.PPatElaborates MatcherTyping.DPatElaborates
      Paper1FrozenSignature.signature [] [recursiveClause]
      ⟨0, 0⟩ recursiveGenerated ⟨4, 3⟩ := by
  have elaborated := M4.elaborateFuel_sound
    Paper1FrozenSignature.wellFormed recursiveMatcher_elaborateFuel_exact
  change MatcherTyping.MatcherLiteralElaboratesUsing
    (M4.ElaboratesFuel Paper1FrozenSignature.signature 29)
    MatcherTyping.PPatElaborates MatcherTyping.DPatElaborates
    Paper1FrozenSignature.signature [] [recursiveClause]
    ⟨0, 0⟩ recursiveGenerated ⟨4, 3⟩ at elaborated
  exact elaborated

theorem recursiveMatcher_semantic :
    recursiveGenerated.SemanticSolution recursiveSolution := by
  constructor
  · simp [recursiveGenerated, recursiveSolution, Solves, Equation.Holds,
      Cap.apply, Ty.apply]
  · intro obligation member
    simp [recursiveGenerated] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨.matcherToSlot, by
        simpa [recursiveSolution, Ty.apply, Cap.apply] using
          (CheckConversion.matcherToSlot CapabilityDemand.equal :
            CheckConversion .matcherToSlot (.matcher .any .int)
              (.slot .any .int))⟩
    · exact ⟨.matcherToSlot, by
        simpa [recursiveSolution, Ty.apply, Cap.apply] using
          (CheckConversion.matcherToSlot CapabilityDemand.equal :
            CheckConversion .matcherToSlot (.matcher .any .int)
              (.slot .any .int))⟩
    · exact ⟨.ordinary, by
        simpa [recursiveSolution, Ty.apply, Ty.applyList, DataTypes.list] using
          (CheckConversion.ordinary :
            CheckConversion .ordinary (DataTypes.list .int)
              (DataTypes.list .int))⟩

private theorem recursiveBody_initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (_environmentTyped : EnvironmentTyping environment [.int])
    (targetSuccess : evalFuel fuel environment (.lit 7) = .ok targetValue)
    (matcherSuccess : evalFuel fuel environment .something = .ok matcherValue)
    (targetTyped : ValueTyping targetValue .int)
    (matcherTyped : ValueTyping matcherValue (.matcher .any .int)) :
    TotalMatchingAtomTyping [.int] []
      ⟨.var, matcherValue, targetValue⟩ [.int] := by
  cases fuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ fuel =>
      simp [evalFuel] at targetSuccess matcherSuccess
      subst targetValue
      subst matcherValue
      exact .builtin (.somethingVar (.int 7))

theorem recursiveBody_totalCoreTyping :
    TotalCoreTyping recursiveBody (DataTypes.list .int) [.int] := by
  unfold recursiveBody
  exact .matchAll (.core (.lit 7)) (.core (.something .int))
    recursiveBody_initialAtom (.core (.var rfl))

theorem recursiveClause_totalTyping :
    TotalRuntimeMatcherClauseTyping TotalExpressionTyping [] .int
      recursiveClause := by
  unfold recursiveClause TotalExpressionTyping
  apply TotalRuntimeMatcherClauseTyping.mk
  · exact RuntimePPatTyping.hole .any
  · exact ⟨.core (.checked (.something .int) (.matcherToSlot .equal))⟩
  · exact .cons
      (.mk RuntimeDPatTyping.var recursiveBody_totalCoreTyping)
      .nil

theorem recursiveClauses_totalTyping :
    TotalRuntimeMatcherClausesTyping TotalExpressionTyping [] .int
      [recursiveClause] :=
  .cons recursiveClause_totalTyping .nil

/-- The literal evaluates to a closure carrying the recursive clause
certificate, rather than an erased ordinary runtime-clause certificate. -/
theorem recursiveMatcher_typedResult (fuel : Nat) :
    evalFuel fuel [] recursiveMatcher = .timeout ∨
      ∃ value,
        evalFuel fuel [] recursiveMatcher = .ok value ∧
        TotalMatcherClosureTyping TotalExpressionTyping value .int := by
  simpa [recursiveMatcher] using
    recursiveClauses_totalTyping.evalMatcherLiteral_typed
      (EnvironmentTyping.nil) fuel

theorem recursiveMatcher_neverStuck (fuel : Nat) :
    (evalFuel fuel [] recursiveMatcher).NotStuck := by
  exact recursiveClauses_totalTyping.matcherLiteral_neverStuck .nil fuel

theorem recursiveClause_inputTyping :
    TotalRuntimeMatcherClauseInputTyping TotalExpressionTyping [] [] .int
      .wild recursiveClause := by
  unfold recursiveClause TotalExpressionTyping
  apply TotalRuntimeMatcherClauseInputTyping.mk
  · exact RuntimePPatTyping.hole .any
  · exact ⟨.core (.checked (.something .int) (.matcherToSlot .equal))⟩
  · exact .cons
      (.mk RuntimeDPatTyping.var recursiveBody_totalCoreTyping)
      .nil
  · intro dispatch inspected
    simp [inspectPatternPattern] at inspected
    subst dispatch
    exact .nil

/-- Normal `evalFuel` endpoint: dispatching the recursive-body clause either
uses up the common fuel or returns a typed matcher-clause observation. -/
theorem recursiveClause_dispatch_totalCoreSafe (fuel : Nat) :
    dispatchMatcherClauses (evalFuel fuel) [] [] [recursiveClause] .wild
        (.int 7) = .timeout ∨
      ∃ result,
        dispatchMatcherClauses (evalFuel fuel) [] [] [recursiveClause] .wild
            (.int 7) = .ok result ∧
        MatcherClauseResultTyping result := by
  exact dispatchMatcherClauses_totalCoreTypedSafe fuel .nil .nil (.int 7)
    (.cons recursiveClause_inputTyping .nil)

theorem recursiveMatcher_inputTyping :
    TotalMatcherClosureInputTyping TotalExpressionTyping []
      (.matcherV [] [recursiveClause] [recursiveClause]) .int .wild :=
  .matcherClosure .nil (.cons recursiveClause_inputTyping .nil)
    ⟨[], by simp⟩

theorem recursiveMatcher_finalCatchAll :
    MatcherTyping.FinalCatchAll [recursiveClause] := by
  exact .last

private theorem wildcardSomethingBranches_shape
    {decompositions : List (List Value)} {branches : MatchingBranches}
    (built : buildMatchingBranches [.wild] [.something] decompositions =
      some branches) :
    ∀ branch ∈ branches,
      ∃ target, branch =
        [{ pattern := .wild, matcher := .something, target := target }] := by
  induction decompositions generalizing branches with
  | nil =>
      simp [buildMatchingBranches] at built
      subst branches
      simp
  | cons decomposition decompositions induction =>
      cases decomposition with
      | nil =>
          simp [buildMatchingBranches, List.mapM_cons,
            zipMatchingAtoms] at built
      | cons target targets =>
          cases targets with
          | nil =>
              cases tailBuilt :
                  List.mapM (zipMatchingAtoms [.wild] [.something])
                    decompositions with
              | none =>
                  simp [buildMatchingBranches, List.mapM_cons,
                    zipMatchingAtoms, tailBuilt] at built
              | some tailBranches =>
                  simp [buildMatchingBranches, List.mapM_cons,
                    zipMatchingAtoms, tailBuilt] at built
                  subst branches
                  intro branch member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | tailMember
                  · exact ⟨target, rfl⟩
                  · exact induction (by
                      simpa [buildMatchingBranches] using tailBuilt)
                      branch tailMember
          | cons second rest =>
              simp [buildMatchingBranches, List.mapM_cons,
                zipMatchingAtoms] at built

private theorem delegatedBranch_member
    (typing : DelegatedMatchingBranchesTyping holes branches) :
    ∀ branch ∈ branches, DelegatedMatchingAtomsTyping branch holes := by
  induction typing with
  | nil => simp
  | cons head tail induction =>
      intro branch member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact head
      · exact induction branch member

private theorem recursiveDispatch_branchesTyped
    (fuel : Nat) (atomEnvironment : ValueEnvironment)
    {holes branches}
    (dispatched : dispatchMatcherClauses (evalFuel fuel) atomEnvironment []
      [recursiveClause] .wild (.int 7) = .ok (.hit branches))
    (_delegated : DelegatedMatchingBranchesTyping holes branches) :
    ∀ branch ∈ branches,
      RecursiveTotalMatchingAtomsTyping TotalExpressionTyping (evalFuel fuel)
        [] [] branch [] := by
  have clauseSuccess :
      tryMatcherClause (evalFuel fuel) atomEnvironment [] .wild (.int 7)
        recursiveClause = .ok (.hit branches) := by
    have ordered := firstHit_sound dispatched
    cases ordered with
    | hit selected => exact selected
    | skip missed tail => cases tail
  have armsMapped :
      FuelResult.map closeMatcherArmsResult
        (firstHit
          (tryMatcherArm (evalFuel fuel) [] [] [.wild] .something (.int 7))
          [.mk .var recursiveBody]) = .ok (.hit branches) := by
    simpa [tryMatcherClause, recursiveClause, inspectPatternPattern,
      FuelResult.traverse, FuelResult.bind] using clauseSuccess
  rw [FuelResult.map_eq_ok_iff] at armsMapped
  obtain ⟨armsResult, armsSuccess, closed⟩ := armsMapped
  cases armsResult with
  | miss =>
      simp [closeMatcherArmsResult] at closed
      subst branches
      simp
  | hit recursiveBranches =>
      simp [closeMatcherArmsResult] at closed
      subst branches
      have armSuccess :
          tryMatcherArm (evalFuel fuel) [] [] [.wild] .something (.int 7)
              (.mk .var recursiveBody) = .ok (.hit recursiveBranches) := by
        have ordered := firstHit_sound armsSuccess
        cases ordered with
        | hit selected => exact selected
        | skip missed tail => cases tail
      have armDispatch :=
        (tryMatcherArm_eq_ok_iff (evalFuel fuel) [] [] [.wild] .something
          (.int 7) (.mk .var recursiveBody) (.hit recursiveBranches)).mp
          armSuccess
      cases armDispatch with
      | hit dataMatch bodyEval decompositionShape matcherEval matcherShape
          branchesBuilt =>
          cases fuel with
          | zero => simp [evalFuel] at matcherEval
          | succ fuel =>
              simp [evalFuel, decodeProduct] at matcherEval matcherShape
              subst_vars
              intro branch member
              obtain ⟨target, rfl⟩ :=
                wildcardSomethingBranches_shape branchesBuilt branch member
              have branchDelegated :=
                delegatedBranch_member _delegated _ member
              cases branchDelegated with
              | cons matcherTyped targetTyped delegatedAtomsTail =>
                  exact .cons (.builtin (.somethingWild targetTyped)) .nil

/-- The closure produced by the M4-checked matcher literal is accepted as an
actual user-matcher atom.  Recursive branches are tied to this exact fuel
callback, rather than postulated for arbitrary evaluators. -/
theorem recursiveMatcher_userAtom (fuel : Nat) :
    RecursiveTotalMatchingAtomTyping TotalExpressionTyping (evalFuel fuel)
      [] []
      ⟨.wild, .matcherV [] [recursiveClause] [recursiveClause], .int 7⟩ [] := by
  exact .user
    (fun atomEnvironment => by simp [reduceBuiltinAtom])
    .nil (.int 7) (.cons recursiveClause_inputTyping .nil)
    recursiveMatcher_finalCatchAll (recursiveDispatch_branchesTyped fuel)

/-- End-to-end finite-search safety for a recursive-body user matcher.  The
same fuel-indexed evaluator runs the clause body, next matcher, recursively
created atom, and depth-first search. -/
theorem recursiveMatcher_search_totalSafe (fuel : Nat) :
    TypedMatchingSearchResult []
      (searchPatternFuel (evalFuel fuel) fuel [] .wild
        (.matcherV [] [recursiveClause] [recursiveClause]) (.int 7)) := by
  exact searchPatternFuel_recursiveTotalTypedSafe
    (expressionTyping := TotalExpressionTyping) (eval := evalFuel fuel)
    (evalFuel_totalCore_embeddedSafe fuel) .nil
    (recursiveMatcher_userAtom fuel) fuel

theorem recursiveMatcher_search_neverStuck (fuel : Nat) :
    (searchPatternFuel (evalFuel fuel) fuel [] .wild
      (.matcherV [] [recursiveClause] [recursiveClause]) (.int 7)).NotStuck := by
  rcases recursiveMatcher_search_totalSafe fuel with timeout |
    ⟨answers, success, answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TypePM.TotalUserMatcherSafetyRegression
