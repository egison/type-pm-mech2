import TypePM.UserMatcherGeneralSafety

/-!
# Callback-parametric safety for recursively typed matcher clauses

The original runtime matcher certificates store `RuntimeTyping` for every
next-matcher expression and arm body.  This parallel family stores an
arbitrary embedded expression judgment instead.  Its safety theorem is
therefore reusable with the ordinary evaluator, the common-fuel total core,
and a checked pattern-function-node evaluator; only the corresponding
`EmbeddedEvaluatorSafe` proof changes.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- A next-matcher expression has the single product type consumed by the
runtime decoder.  The zero/one/many source convention is already enforced by
source elaboration; dispatch safety needs exactly this semantic type. -/
structure TotalRuntimeNextMatchersTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (context : List Ty) (expression : Source.Expr) (holes : List Dual) : Prop where
  typed : expressionTyping context expression (runtimeMatcherProductTarget holes)

/-- One matcher arm whose body may itself use recursive matching. -/
inductive TotalRuntimeMatcherArmTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (definitionTypes captureTypes : List Ty) (matcherTarget : Ty)
    (holes : List Dual) : Source.MatcherArm → Prop where
  | mk
      (header : RuntimeDPatTyping dataPattern matcherTarget bindingTypes)
      (body : expressionTyping
        (bindingTypes ++ captureTypes ++ definitionTypes) bodyExpression
        (TypePM.DataTypes.list (runtimeHoleProductTarget holes))) :
      TotalRuntimeMatcherArmTyping expressionTyping definitionTypes captureTypes
        matcherTarget holes (.mk dataPattern bodyExpression)

inductive TotalRuntimeMatcherArmsTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (definitionTypes captureTypes : List Ty) (matcherTarget : Ty)
    (holes : List Dual) : List Source.MatcherArm → Prop where
  | nil : TotalRuntimeMatcherArmsTyping expressionTyping definitionTypes
      captureTypes matcherTarget holes []
  | cons
      (head : TotalRuntimeMatcherArmTyping expressionTyping definitionTypes
        captureTypes matcherTarget holes arm)
      (tail : TotalRuntimeMatcherArmsTyping expressionTyping definitionTypes
        captureTypes matcherTarget holes arms) :
      TotalRuntimeMatcherArmsTyping expressionTyping definitionTypes
        captureTypes matcherTarget holes (arm :: arms)

inductive TotalRuntimeMatcherClauseTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (definitionTypes : List Ty) (matcherTarget : Ty) :
    Source.MatcherClause → Prop where
  | mk
      (header : RuntimePPatTyping patternPattern matcherTarget holes captureTypes)
      (nextMatchers : TotalRuntimeNextMatchersTyping expressionTyping
        (captureTypes ++ definitionTypes) nextMatcherExpression holes)
      (arms : TotalRuntimeMatcherArmsTyping expressionTyping definitionTypes
        captureTypes matcherTarget holes matcherArms) :
      TotalRuntimeMatcherClauseTyping expressionTyping definitionTypes
        matcherTarget (.mk patternPattern nextMatcherExpression matcherArms)

inductive TotalRuntimeMatcherClausesTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (definitionTypes : List Ty) (matcherTarget : Ty) :
    List Source.MatcherClause → Prop where
  | nil : TotalRuntimeMatcherClausesTyping expressionTyping definitionTypes
      matcherTarget []
  | cons
      (head : TotalRuntimeMatcherClauseTyping expressionTyping definitionTypes
        matcherTarget clause)
      (tail : TotalRuntimeMatcherClausesTyping expressionTyping definitionTypes
        matcherTarget clauses) :
      TotalRuntimeMatcherClausesTyping expressionTyping definitionTypes
        matcherTarget (clause :: clauses)

/-- Value typing for a matcher closure whose stored clause expressions use
the callback-parametric total judgment. -/
inductive TotalMatcherClosureTyping
    (expressionTyping : EmbeddedExpressionTyping) : Value → Ty → Prop where
  | matcherClosure
      (environment : EnvironmentTyping matcherEnvironment definitionTypes)
      (clauses : TotalRuntimeMatcherClausesTyping expressionTyping
        definitionTypes matcherTarget original)
      (cursor : ∃ tried, original = tried ++ remaining) :
      TotalMatcherClosureTyping expressionTyping
        (.matcherV matcherEnvironment original remaining) matcherTarget

/-- Evaluating a certified matcher literal either consumes zero fuel or
constructs the exact certified closure. -/
theorem TotalRuntimeMatcherClausesTyping.evalMatcherLiteral_typed
    (typing : TotalRuntimeMatcherClausesTyping expressionTyping context
      matcherTarget clauses)
    (environmentTyped : EnvironmentTyping environment context)
    (fuel : Nat) :
    evalFuel fuel environment (.matcher clauses) = .timeout ∨
      ∃ value,
        evalFuel fuel environment (.matcher clauses) = .ok value ∧
        TotalMatcherClosureTyping expressionTyping value matcherTarget := by
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨Value.matcherClosure environment clauses, rfl,
        .matcherClosure environmentTyped typing ⟨[], by simp⟩⟩

theorem TotalRuntimeMatcherClausesTyping.matcherLiteral_neverStuck
    (_typing : TotalRuntimeMatcherClausesTyping expressionTyping context
      matcherTarget clauses)
    (_environmentTyped : EnvironmentTyping environment context)
    (fuel : Nat) :
    (evalFuel fuel environment (.matcher clauses)).NotStuck := by
  cases fuel <;> simp [evalFuel, FuelResult.NotStuck]

/-- Input-indexed clause certificate.  The capture proof is tied to the
actual source pattern inspected by dispatch. -/
inductive TotalRuntimeMatcherClauseInputTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (atomEnvironmentTypes definitionTypes : List Ty)
    (matcherTarget : Ty) (pattern : Source.Pattern) :
    Source.MatcherClause → Prop where
  | mk
      (header : RuntimePPatTyping patternPattern matcherTarget holes captureTypes)
      (nextMatchers : TotalRuntimeNextMatchersTyping expressionTyping
        (captureTypes ++ definitionTypes) nextMatcherExpression holes)
      (arms : TotalRuntimeMatcherArmsTyping expressionTyping definitionTypes
        captureTypes matcherTarget holes matcherArms)
      (captures : ∀ {dispatch},
        inspectPatternPattern patternPattern pattern = some dispatch →
        RuntimeCaptureExpressionsTyping expressionTyping atomEnvironmentTypes
          dispatch.captures captureTypes) :
      TotalRuntimeMatcherClauseInputTyping expressionTyping atomEnvironmentTypes
        definitionTypes matcherTarget pattern
        (.mk patternPattern nextMatcherExpression matcherArms)

inductive TotalRuntimeMatcherClausesInputTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (atomEnvironmentTypes definitionTypes : List Ty)
    (matcherTarget : Ty) (pattern : Source.Pattern) :
    List Source.MatcherClause → Prop where
  | nil : TotalRuntimeMatcherClausesInputTyping expressionTyping
      atomEnvironmentTypes definitionTypes matcherTarget pattern []
  | cons
      (head : TotalRuntimeMatcherClauseInputTyping expressionTyping
        atomEnvironmentTypes definitionTypes matcherTarget pattern clause)
      (tail : TotalRuntimeMatcherClausesInputTyping expressionTyping
        atomEnvironmentTypes definitionTypes matcherTarget pattern clauses) :
      TotalRuntimeMatcherClausesInputTyping expressionTyping atomEnvironmentTypes
        definitionTypes matcherTarget pattern (clause :: clauses)

/-- A value-level certificate for the exact matcher cursor consumed by user
dispatch.  It preserves both the original clause list and the current suffix. -/
inductive TotalMatcherClosureInputTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (atomEnvironmentTypes : List Ty) :
    Value → Ty → Source.Pattern → Prop where
  | matcherClosure
      (environment : EnvironmentTyping matcherEnvironment definitionTypes)
      (clauses : TotalRuntimeMatcherClausesInputTyping expressionTyping
        atomEnvironmentTypes definitionTypes matcherTarget pattern remaining)
      (cursor : ∃ tried, original = tried ++ remaining) :
      TotalMatcherClosureInputTyping expressionTyping atomEnvironmentTypes
        (.matcherV matcherEnvironment original remaining) matcherTarget pattern

theorem tryMatcherArm_totalTypedSafe
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
        MatcherArmResultTyping holes result := by
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
              buildMatchingBranches_typed patternsLength matcherValuesTyped
                decompositionsTyped
            exact .inr ⟨.hit branches, by
              simp [tryMatcherArm, dataMatch, bodySuccess',
                decompositionsDecoded', nextSuccess, matchersDecoded',
                branchesBuilt], .hit branchesTyped⟩

theorem firstHitMatcherArms_totalTypedSafe
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
        MatcherArmResultTyping holes result := by
  induction armsTyped with
  | nil => exact .inr ⟨.miss, rfl, .miss⟩
  | cons head tail induction =>
      rcases tryMatcherArm_totalTypedSafe
          (expressionTyping := expressionTyping) (eval := eval)
          evalSafe matcherEnvironmentTyped
          captureValuesTyped targetTyped nextMatchersTyped head patternsLength with
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

private theorem closeMatcherArmsResult_totalTyped
    (typing : MatcherArmResultTyping holes result) :
    MatcherClauseResultTyping (closeMatcherArmsResult result) := by
  cases typing with
  | miss => exact .hit (holes := holes) .nil
  | hit branches => exact .hit branches

theorem tryMatcherClause_totalTypedSafe
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
        MatcherClauseResultTyping result := by
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
          · rcases firstHitMatcherArms_totalTypedSafe
                (expressionTyping := expressionTyping) (eval := eval) evalSafe
                matcherEnvironmentTyped captureValuesTyped targetTyped
                nextMatchers arms patternsLength with
              armsTimeout | ⟨armsResult, armsSuccess, armsTyped⟩
            · exact .inl (by
                simp [tryMatcherClause, inspected, captureSuccess, armsTimeout,
                  FuelResult.map])
            · exact .inr ⟨closeMatcherArmsResult armsResult, by
                simp [tryMatcherClause, inspected, captureSuccess, armsSuccess,
                  FuelResult.map], closeMatcherArmsResult_totalTyped armsTyped⟩

/-- Callback-parametric dispatch safety.  This is the public reusable endpoint
for ordinary `evalFuel` and checked MNode evaluation. -/
theorem dispatchMatcherClauses_totalTypedSafe
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
        MatcherClauseResultTyping result := by
  induction clausesTyped with
  | nil => exact .inr ⟨.miss, rfl, .miss⟩
  | cons head tail induction =>
      rcases tryMatcherClause_totalTypedSafe
          (expressionTyping := expressionTyping) (eval := eval)
          evalSafe atomEnvironmentTyped
          matcherEnvironmentTyped targetTyped head with
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

theorem TotalMatcherClosureInputTyping.dispatch_typedSafe
    (typing : TotalMatcherClosureInputTyping expressionTyping
      atomEnvironmentTypes matcherValue matcherTarget pattern)
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (targetTyped : ValueTyping target matcherTarget) :
    dispatchMatcherValue eval atomEnvironment matcherValue pattern target =
        .timeout ∨
      ∃ result,
        dispatchMatcherValue eval atomEnvironment matcherValue pattern target =
            .ok result ∧
        MatcherClauseResultTyping result := by
  cases typing with
  | matcherClosure environment clauses cursor =>
      simpa [dispatchMatcherValue] using
        dispatchMatcherClauses_totalTypedSafe
          (expressionTyping := expressionTyping) (eval := eval)
          evalSafe atomEnvironmentTyped
          environment targetTyped clauses

end TypePM.Runtime
