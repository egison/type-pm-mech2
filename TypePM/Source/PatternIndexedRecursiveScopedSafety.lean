import TypePM.PatternFunctionSafety
import TypePM.RecursiveTotalMatchingSafety
import TypePM.Source.M4MatchingAtomRuntimeBridge
import TypePM.Source.M4RecursiveMatcherInputBridge

/-!
# Pattern-indexed user dispatch into checked pattern-function work

Runtime matcher dispatch normally exposes only value typing for delegated
branches.  The relations in this file keep the exact source patterns emitted
by `inspectPatternPattern` through the successful `buildMatchingBranches`
call.  A second, parallel certificate classifies those exact atoms as checked
outer work; in particular, a pattern-function application is handled by the
checked MNode invariant rather than being treated as an ordinary atom.
-/

namespace TypePM.Runtime

open TypePM.Source
open TypePM.Source.MatcherTyping

/-- Successful matcher-arm typing retaining the exact delegated source
patterns. -/
inductive PatternIndexedMatcherArmResultTyping
    (patterns : List Pattern) (holes : List Dual) :
    DispatchResult MatchingBranches → Prop where
  | miss : PatternIndexedMatcherArmResultTyping patterns holes
      (DispatchResult.miss : DispatchResult MatchingBranches)
  | hit
      (branches : PatternIndexedDelegatedMatchingBranchesTyping
        patterns holes recursiveBranches) :
      PatternIndexedMatcherArmResultTyping patterns holes
        (DispatchResult.hit recursiveBranches)

/-- Clause-result typing retaining the source-pattern list selected by the
successful header. -/
inductive PatternIndexedMatcherClauseResultTyping :
    DispatchResult MatchingBranches → Prop where
  | miss : PatternIndexedMatcherClauseResultTyping
      (DispatchResult.miss : DispatchResult MatchingBranches)
  | hit
      (branches : PatternIndexedDelegatedMatchingBranchesTyping
        patterns holes recursiveBranches) :
      PatternIndexedMatcherClauseResultTyping
        (DispatchResult.hit recursiveBranches)

theorem tryMatcherArm_patternIndexedTotalTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (captureValuesTyped : ValueTypings captureValues captureTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (nextMatchersTyped : TotalRuntimeNextMatchersTyping expressionTyping
      (captureTypes ++ definitionTypes) nextMatchers holes)
    (armTyped : TotalRuntimeMatcherArmTyping expressionTyping definitionTypes
      captureTypes matcherTarget holes arm)
    (patternsLength : patterns.length = holes.length) :
    tryMatcherArm eval matcherEnvironment captureValues patterns nextMatchers
        target arm = .timeout ∨
      ∃ result,
        tryMatcherArm eval matcherEnvironment captureValues patterns nextMatchers
          target arm = .ok result ∧
        PatternIndexedMatcherArmResultTyping patterns holes result := by
  cases armTyped with
  | @mk dataPattern bindingTypes bodyExpression header body =>
      rcases header.match_typed targetTyped with dataMismatch |
        ⟨dataValues, dataMatch, dataValuesTyped⟩
      · exact .inr ⟨.miss, by simp [tryMatcherArm, dataMismatch], .miss⟩
      · have bodyEnvironmentTyped := dataValuesTyped.dataCapturesDefinition
          captureValuesTyped matcherEnvironmentTyped
        rcases evalSafe bodyEnvironmentTyped body with bodyTimeout |
          ⟨decompositionValue, bodySuccess, decompositionTyped⟩
        · have bodyTimeout' :
              eval (dataValues ++ (captureValues ++ matcherEnvironment))
                  bodyExpression = .timeout := by
            simpa [List.append_assoc] using bodyTimeout
          exact .inl (by simp [tryMatcherArm, dataMatch, bodyTimeout'])
        · obtain ⟨decompositions, decompositionsDecoded,
              decompositionsTyped⟩ := decompositionTyped.decodeDecompositions_typed
          have bodySuccess' :
              eval (dataValues ++ (captureValues ++ matcherEnvironment))
                  bodyExpression = .ok decompositionValue := by
            simpa [List.append_assoc] using bodySuccess
          have decompositionsDecoded' :
              decodeDecompositions patterns.length decompositionValue =
                some decompositions := by
            simpa [patternsLength] using decompositionsDecoded
          have nextEnvironmentTyped :=
            captureValuesTyped.appendEnvironment matcherEnvironmentTyped
          rcases evalSafe nextEnvironmentTyped nextMatchersTyped.typed with
            nextTimeout | ⟨matcherProduct, nextSuccess, matcherProductTyped⟩
          · exact .inl (by
              simp [tryMatcherArm, dataMatch, bodySuccess',
                decompositionsDecoded', nextTimeout])
          · obtain ⟨matcherValues, matchersDecoded, matcherValuesTyped⟩ :=
              matcherProductTyped.decodeRuntimeProduct
            have matchersDecoded' :
                decodeProduct patterns.length matcherProduct =
                  some matcherValues := by
              simpa [patternsLength] using matchersDecoded
            obtain ⟨branches, branchesBuilt, branchesTyped⟩ :=
              buildMatchingBranches_patternIndexedTyped patternsLength
                matcherValuesTyped decompositionsTyped
            exact .inr ⟨.hit branches, by
              simp [tryMatcherArm, dataMatch, bodySuccess',
                decompositionsDecoded', nextSuccess, matchersDecoded',
                branchesBuilt], .hit branchesTyped⟩

theorem firstHitMatcherArms_patternIndexedTotalTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (captureValuesTyped : ValueTypings captureValues captureTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (nextMatchersTyped : TotalRuntimeNextMatchersTyping expressionTyping
      (captureTypes ++ definitionTypes) nextMatchers holes)
    (armsTyped : TotalRuntimeMatcherArmsTyping expressionTyping definitionTypes
      captureTypes matcherTarget holes arms)
    (patternsLength : patterns.length = holes.length) :
    firstHit
        (tryMatcherArm eval matcherEnvironment captureValues patterns
          nextMatchers target) arms = .timeout ∨
      ∃ result,
        firstHit
          (tryMatcherArm eval matcherEnvironment captureValues patterns
            nextMatchers target) arms = .ok result ∧
        PatternIndexedMatcherArmResultTyping patterns holes result := by
  induction armsTyped with
  | nil => exact .inr ⟨.miss, rfl, .miss⟩
  | cons head tail induction =>
      rcases tryMatcherArm_patternIndexedTotalTypedSafe
          (expressionTyping := expressionTyping) (eval := eval)
          evalSafe matcherEnvironmentTyped captureValuesTyped targetTyped
          nextMatchersTyped head patternsLength with
        headTimeout | ⟨headResult, headSuccess, headTyped⟩
      · exact .inl (by simp [firstHit, headTimeout])
      · cases headTyped with
        | hit branchesTyped =>
            exact .inr ⟨_, by simp [firstHit, headSuccess], .hit branchesTyped⟩
        | miss =>
            rcases induction with tailTimeout |
              ⟨tailResult, tailSuccess, tailTyped⟩
            · exact .inl (by simp [firstHit, headSuccess, tailTimeout])
            · exact .inr ⟨tailResult, by
                simp [firstHit, headSuccess, tailSuccess], tailTyped⟩

private theorem closeMatcherArmsResult_patternIndexedTyped
    (typing : PatternIndexedMatcherArmResultTyping patterns holes result) :
    PatternIndexedMatcherClauseResultTyping
      (closeMatcherArmsResult result) := by
  cases typing with
  | miss => exact .hit (patterns := patterns) (holes := holes) .nil
  | hit branches => exact .hit branches

theorem tryMatcherClause_patternIndexedTotalTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (clauseTyped : TotalRuntimeMatcherClauseInputTyping expressionTyping
      atomEnvironmentTypes definitionTypes matcherTarget pattern clause) :
    tryMatcherClause eval atomEnvironment matcherEnvironment pattern target
        clause = .timeout ∨
      ∃ result,
        tryMatcherClause eval atomEnvironment matcherEnvironment pattern target
          clause = .ok result ∧
        PatternIndexedMatcherClauseResultTyping result := by
  cases clauseTyped with
  | @mk patternPattern holes captureTypes nextMatcherExpression matcherArms
      header nextMatchers arms captures =>
      cases inspected : inspectPatternPattern patternPattern pattern with
      | none =>
          exact .inr ⟨.miss, by simp [tryMatcherClause, inspected], .miss⟩
      | some dispatch =>
          have runtimeCounts := (inspectPatternPattern_sound inspected).counts
          have staticCounts := header.counts
          have patternsLength : dispatch.holes.length = holes.length := by omega
          have capturesTyping := captures inspected
          rcases RuntimeCaptureExpressionsTyping.traverse_typed
              (eval := eval) evalSafe atomEnvironmentTyped capturesTyping with
            captureTimeout |
              ⟨captureValues, captureSuccess, captureValuesTyped⟩
          · exact .inl (by simp [tryMatcherClause, inspected, captureTimeout])
          · rcases firstHitMatcherArms_patternIndexedTotalTypedSafe
                (expressionTyping := expressionTyping) (eval := eval) evalSafe
                matcherEnvironmentTyped captureValuesTyped targetTyped
                nextMatchers arms patternsLength with
              armsTimeout | ⟨armsResult, armsSuccess, armsTyped⟩
            · exact .inl (by
                simp [tryMatcherClause, inspected, captureSuccess, armsTimeout])
            · exact .inr ⟨closeMatcherArmsResult armsResult, by
                simp [tryMatcherClause, inspected, captureSuccess, armsSuccess],
                closeMatcherArmsResult_patternIndexedTyped armsTyped⟩

theorem dispatchMatcherClauses_patternIndexedTotalTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (clausesTyped : TotalRuntimeMatcherClausesInputTyping expressionTyping
      atomEnvironmentTypes definitionTypes matcherTarget pattern clauses) :
    dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
        pattern target = .timeout ∨
      ∃ result,
        dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
          pattern target = .ok result ∧
        PatternIndexedMatcherClauseResultTyping result := by
  induction clausesTyped with
  | nil => exact .inr ⟨.miss, rfl, .miss⟩
  | cons head tail induction =>
      rcases tryMatcherClause_patternIndexedTotalTypedSafe
          (expressionTyping := expressionTyping) (eval := eval) evalSafe
          atomEnvironmentTyped matcherEnvironmentTyped targetTyped head with
        headTimeout | ⟨headResult, headSuccess, headTyped⟩
      · exact .inl (by simp [dispatchMatcherClauses, firstHit, headTimeout])
      · cases headTyped with
        | hit branchesTyped =>
            exact .inr ⟨_, by
              simp [dispatchMatcherClauses, firstHit, headSuccess],
              .hit branchesTyped⟩
        | miss =>
            rcases induction with tailTimeout |
              ⟨tailResult, tailSuccess, tailTyped⟩
            · exact .inl (by
                simp [dispatchMatcherClauses, firstHit, headSuccess]
                simpa [dispatchMatcherClauses] using tailTimeout)
            · exact .inr ⟨tailResult, by
                simp [dispatchMatcherClauses, firstHit, headSuccess]
                simpa [dispatchMatcherClauses] using tailSuccess,
                tailTyped⟩

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- The M4 input bridge feeds the pattern-indexed dispatcher without passing
through `DelegatedMatchingBranchesTyping`.  Thus a successful result retains
the concrete patterns extracted from the source input. -/
theorem MatcherLiteralTotalInputElaboratesUsing.dispatchPatternIndexedSafe_of_m4Fuel
    (input : MatcherLiteralTotalInputElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature elaborationFuel)
      expressionTyping solution atomEnvironmentTypes pattern context clauses
      supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution)
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target
      ((Ty.var ⟨supply.ty⟩).apply solution)) :
    dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
        pattern target = .timeout ∨
      ∃ result,
        dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
          pattern target = .ok result ∧
        PatternIndexedMatcherClauseResultTyping result := by
  exact dispatchMatcherClauses_patternIndexedTotalTypedSafe evalSafe
    atomEnvironmentTyped matcherEnvironmentTyped targetTyped
    (input.toTotalInputTyping_of_m4Fuel bridge semantic contextCompatible)

end TypePM.Source.MatcherTyping

namespace TypePM.Runtime

open TypePM.Source
open TypePM.Source.MatcherTyping

/-- The ordinary recursive leg remains exactly the existing callback-indexed
theorem.  This endpoint is paired with the source-indexed MNode leg below;
applications are never inserted into `RecursiveTotalMatchingAtomTyping`. -/
theorem evaluationAtomReducer_recursiveBuiltinTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (environmentTyped : EnvironmentTyping environment environmentTypes)
    (bindingsTyped : ValueTypings bindings bindingTypes)
    (atomTyped : MatchingAtomTyping expressionTyping environmentTypes
      bindingTypes atom newBindings) :
    evaluationAtomReducer eval (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        evaluationAtomReducer eval (bindings ++ environment) atom =
            .ok (.hit reduction) ∧
        RecursiveTotalAtomReductionTyping expressionTyping eval
          environmentTypes bindingTypes newBindings reduction :=
  evaluationAtomReducer_recursiveTotalTypedSafe
    (expressionTyping := expressionTyping) (eval := eval) evalSafe
    environmentTyped bindingsTyped (.builtin atomTyped)

/-! ## Exact branches as checked scoped work -/

/-- A delegated branch whose exact source-pattern index has been classified
as checked outer work.  The delegated value certificate and the executable
scoped-work certificate are kept together, so neither can be reassociated
with a different erased pattern list. -/
structure PatternIndexedCheckedScopedAtomsTyping
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes bindingTypes : List Ty)
    (atoms : List MatchingAtom) (patterns : List Pattern) (holes : List Dual)
    (answerTypes : List Ty) : Prop where
  indexed : PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes
  work : CheckedScopedWorkTyping signature definitions environmentTypes
    bindingTypes (MatchingTree.ofAtoms atoms) answerTypes

namespace PatternIndexedCheckedScopedAtomsTyping

/-- Empty dispatch branches are checked empty work. -/
theorem nil : PatternIndexedCheckedScopedAtomsTyping signature definitions
    environmentTypes bindingTypes [] [] [] bindingTypes :=
  ⟨.nil, .nil⟩

/-- The ordinary subcase is converted with the existing checked-ordinary
certificate.  Application and parameter patterns deliberately do not enter
this constructor; their source-specific constructors must provide scoped
MNode work directly. -/
theorem ofOrdinary
    (indexed : PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes)
    (ordinary : CheckedOrdinaryAtomsTyping environmentTypes bindingTypes atoms
      newBindings) :
    PatternIndexedCheckedScopedAtomsTyping signature definitions
      environmentTypes bindingTypes atoms patterns holes
      (bindingTypes ++ newBindings) := by
  refine ⟨indexed, ?_⟩
  have combined := CheckedScopedWorkTyping.prependTotalAtoms ordinary (by
    simpa using (CheckedScopedWorkTyping.nil :
      CheckedScopedWorkTyping signature definitions environmentTypes
        (bindingTypes ++ newBindings) [] (bindingTypes ++ newBindings)))
  rw [List.append_nil] at combined
  exact combined

/-- A checked application branch is retained as application work, rather than
being coerced to `CheckedOrdinaryAtomsTyping`. -/
theorem application
    (indexed : PatternIndexedDelegatedMatchingAtomsTyping
      [⟨.app name arguments, matcher, target⟩] [.app name arguments] [hole])
    (work : CheckedScopedWorkTyping signature definitions environmentTypes
      bindingTypes [.atom ⟨.app name arguments, matcher, target⟩] answerTypes) :
    PatternIndexedCheckedScopedAtomsTyping signature definitions
      environmentTypes bindingTypes
      [⟨.app name arguments, matcher, target⟩] [.app name arguments] [hole]
      answerTypes :=
  ⟨indexed, by simpa [MatchingTree.ofAtoms] using work⟩

end PatternIndexedCheckedScopedAtomsTyping

/-- Actual successful user dispatch, with every returned branch classified
using the pattern-indexed certificate produced by that same dispatch. -/
structure CheckedScopedSuccessfulUserDispatch
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes bindingTypes answerTypes : List Ty)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (clauses : List MatcherClause) (pattern : Pattern) (target : Value) where
  branches : MatchingBranches
  success : dispatchMatcherClauses eval atomEnvironment matcherEnvironment
    clauses pattern target = .ok (.hit branches)
  patterns : List Pattern
  holes : List Dual
  indexed : PatternIndexedDelegatedMatchingBranchesTyping patterns holes branches
  checked : ∀ branch ∈ branches,
    PatternIndexedDelegatedMatchingAtomsTyping branch patterns holes →
    PatternIndexedCheckedScopedAtomsTyping signature definitions
      environmentTypes bindingTypes branch patterns holes answerTypes

namespace CheckedScopedSuccessfulUserDispatch

private theorem indexed_member
    {patterns : List Pattern} {holes : List Dual}
    {branches : MatchingBranches}
    (typing : PatternIndexedDelegatedMatchingBranchesTyping patterns holes branches) :
    ∀ branch ∈ branches,
      PatternIndexedDelegatedMatchingAtomsTyping branch patterns holes := by
  induction typing with
  | nil => simp
  | cons head tail induction =>
      intro branch member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact head
      · exact induction branch member

/-- The concrete successful matcher dispatch is exactly a successful
`evaluationAtomReducer` reduction, and its branches are checked scoped work.
This theorem is intentionally success-indexed: it does not claim a global
upgrade for unrelated user matchers or erased branches. -/
theorem evaluationAtomReducer_exact
    (builtinMiss : reduceBuiltinAtom eval atomEnvironment
      ⟨pattern, .matcherV matcherEnvironment original clauses, target⟩ =
        .ok .miss)
    (dispatch : CheckedScopedSuccessfulUserDispatch signature definitions
      environmentTypes bindingTypes answerTypes eval atomEnvironment
      matcherEnvironment clauses pattern target) :
    evaluationAtomReducer eval atomEnvironment
        ⟨pattern, .matcherV matcherEnvironment original clauses, target⟩ =
      .ok (.hit ⟨dispatch.branches, []⟩) ∧
    ∀ branch ∈ dispatch.branches,
      PatternIndexedCheckedScopedAtomsTyping signature definitions
        environmentTypes bindingTypes branch dispatch.patterns dispatch.holes
        answerTypes := by
  constructor
  · unfold evaluationAtomReducer combineAtomReducers
    rw [builtinMiss]
    simp only [FuelResult.bind]
    simpa [reduceMatcherAtom, clauseResultToAtomReduction] using
      congrArg (FuelResult.map clauseResultToAtomReduction) dispatch.success
  · intro branch member
    exact dispatch.checked branch member
      (indexed_member dispatch.indexed branch member)

end CheckedScopedSuccessfulUserDispatch

end TypePM.Runtime
