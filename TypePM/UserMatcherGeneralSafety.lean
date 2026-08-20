import TypePM.UserMatcherSafety

/-!
# General runtime safety for typed user-matcher dispatch

This module lifts the first concrete user-matcher example to the complete
evaluator-facing `RuntimePPatTyping` / `RuntimeDPatTyping` fragment.  It proves
typed progress for one arm, ordered arms, one clause, and ordered clauses.

The result certificate records exactly what clause dispatch establishes:
delegated matcher values have the solved slot types and decomposition targets
have the solved hole types.  Source-pattern typing and static clause
exhaustiveness remain explicit boundaries; neither is inferred here.
-/

namespace TypePM.Runtime

open TypePM.Source

def runtimeProductTarget : List Ty → Ty
  | [] => .prod []
  | [target] => target
  | targets => .prod targets

def runtimeMatcherProductTarget (holes : List Dual) : Ty :=
  runtimeProductTarget
    (holes.map (fun hole => .slot hole.capability hole.target))

theorem RuntimeNextMatchersTyping.runtimeTyping
    (typing : RuntimeNextMatchersTyping context expression holes) :
    RuntimeTyping expression (runtimeMatcherProductTarget holes) context := by
  cases typing with
  | zero => exact .tuple .nil
  | one typed => exact typed
  | many typed => exact .tuple typed

theorem ValueTyping.decodeRuntimeProduct
    (typing : ValueTyping value (runtimeProductTarget targets)) :
    ∃ values,
      decodeProduct targets.length value = some values ∧
      ValueTypings values targets := by
  cases targets with
  | nil =>
      obtain ⟨values, rfl, valuesTyped⟩ := typing.product_canonical
      cases valuesTyped
      exact ⟨[], rfl, .nil⟩
  | cons first rest =>
      cases rest with
      | nil => exact ⟨[value], rfl, .cons typing .nil⟩
      | cons second rest =>
          obtain ⟨values, rfl, valuesTyped⟩ := typing.product_canonical
          refine ⟨values, ?_, valuesTyped⟩
          exact decodeProduct_many_exact (by simp) values valuesTyped.length_eq

/-- Pointwise typing for captured expressions.  Every capture is evaluated in
the same atom environment; captures are not incrementally added to it. -/
inductive RuntimeCaptureExpressionsTyping
    (expressionTyping : EmbeddedExpressionTyping) (context : List Ty) :
    List Source.Expr → List Ty → Prop where
  | nil : RuntimeCaptureExpressionsTyping expressionTyping context [] []
  | cons
      (head : expressionTyping context expression target)
      (tail : RuntimeCaptureExpressionsTyping expressionTyping context
        expressions targets) :
      RuntimeCaptureExpressionsTyping expressionTyping context
        (expression :: expressions) (target :: targets)

theorem RuntimeCaptureExpressionsTyping.traverse_typed
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (environmentTyped : EnvironmentTyping environment context)
    (typing : RuntimeCaptureExpressionsTyping expressionTyping context
      expressions targets) :
    FuelResult.traverse (eval environment) expressions = .timeout ∨
      ∃ values,
        FuelResult.traverse (eval environment) expressions = .ok values ∧
        ValueTypings values targets := by
  induction typing with
  | nil => exact .inr ⟨[], rfl, .nil⟩
  | @cons expression target expressions targets head tail ih =>
      rcases evalSafe environmentTyped head with headTimeout |
        ⟨headValue, headSuccess, headTyped⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · rcases ih with tailTimeout | ⟨tailValues, tailSuccess, tailTyped⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            .cons headTyped tailTyped⟩

/-- Value typing retained by one branch created by a user matcher.  Patterns
are preserved syntactically by dispatch; their static typing is intentionally
not claimed at this boundary. -/
inductive DelegatedMatchingAtomsTyping :
    List MatchingAtom → List Dual → Prop where
  | nil : DelegatedMatchingAtomsTyping [] []
  | cons
      (matcher : ValueTyping matcherValue
        (.slot hole.capability hole.target))
      (target : ValueTyping targetValue hole.target)
      (tail : DelegatedMatchingAtomsTyping atoms holes) :
      DelegatedMatchingAtomsTyping
        (⟨pattern, matcherValue, targetValue⟩ :: atoms) (hole :: holes)

/-- Every source-ordered candidate branch has the same solved hole types. -/
inductive DelegatedMatchingBranchesTyping (holes : List Dual) :
    MatchingBranches → Prop where
  | nil : DelegatedMatchingBranchesTyping holes []
  | cons
      (head : DelegatedMatchingAtomsTyping branch holes)
      (tail : DelegatedMatchingBranchesTyping holes branches) :
      DelegatedMatchingBranchesTyping holes (branch :: branches)

/-- Typed observation of arm dispatch. -/
inductive MatcherArmResultTyping (holes : List Dual) :
    DispatchResult MatchingBranches → Prop where
  | miss : MatcherArmResultTyping holes .miss
  | hit
      (branches : DelegatedMatchingBranchesTyping holes result) :
      MatcherArmResultTyping holes (.hit result)

/-- Clause lists can select clauses with different hole products, so the
selected hole types are existential in their common result certificate. -/
inductive MatcherClauseResultTyping :
    DispatchResult MatchingBranches → Prop where
  | miss : MatcherClauseResultTyping .miss
  | hit
      (branches : DelegatedMatchingBranchesTyping holes result) :
      MatcherClauseResultTyping (.hit result)

theorem zipMatchingAtoms_typed
    (length : patterns.length = holes.length)
    (matchersTyped : ValueTypings matcherValues
      (holes.map (fun hole => .slot hole.capability hole.target)))
    (targetsTyped : ValueTypings targetValues (Dual.targets holes)) :
    ∃ atoms,
      zipMatchingAtoms patterns matcherValues targetValues = some atoms ∧
      DelegatedMatchingAtomsTyping atoms holes := by
  induction holes generalizing patterns matcherValues targetValues with
  | nil =>
      cases matchersTyped
      cases targetsTyped
      simp at length
      subst patterns
      exact ⟨[], rfl, .nil⟩
  | cons hole holes ih =>
      cases matchersTyped with
      | cons matcherTyped matchersTyped =>
          cases targetsTyped with
          | cons targetTyped targetsTyped =>
              cases patterns with
              | nil => simp at length
              | cons pattern patterns =>
                  simp at length
                  obtain ⟨atoms, zipped, atomsTyped⟩ :=
                    ih length matchersTyped targetsTyped
                  exact ⟨⟨pattern, _, _⟩ :: atoms, by
                    simp [zipMatchingAtoms, zipped],
                    .cons matcherTyped targetTyped atomsTyped⟩

theorem buildMatchingBranches_typed
    (length : patterns.length = holes.length)
    (matchersTyped : ValueTypings matcherValues
      (holes.map (fun hole => .slot hole.capability hole.target)))
    (decompositionsTyped : HoleDecompositionsTyping holes decompositions) :
    ∃ branches,
      buildMatchingBranches patterns matcherValues decompositions = some branches ∧
      DelegatedMatchingBranchesTyping holes branches := by
  induction decompositionsTyped with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons targetValues decompositions targetsTyped tailTyped ih =>
      obtain ⟨branch, zipped, branchTyped⟩ :=
        zipMatchingAtoms_typed length matchersTyped targetsTyped
      obtain ⟨branches, built, branchesTyped⟩ := ih
      change List.mapM (zipMatchingAtoms patterns matcherValues) decompositions =
        some branches at built
      exact ⟨branch :: branches, by
        simp [buildMatchingBranches, List.mapM_cons, zipped, built],
        .cons branchTyped branchesTyped⟩

theorem RuntimeDataConstructorTyping.value_shape
    (constructorTyped : RuntimeDataConstructorTyping constructor fieldTypes target)
    (targetTyped : ValueTyping value target) :
    ∃ actual arguments,
      value = .data actual arguments ∧
      (actual = constructor → ValueTypings arguments fieldTypes) := by
  cases constructorTyped with
  | boolTrue =>
      rcases targetTyped.bool_canonical with isTrue | isFalse
      · exact ⟨DataCtor.true, [], isTrue, fun _ => .nil⟩
      · refine ⟨DataCtor.false, [], isFalse, ?_⟩
        intro impossible
        simp [DataCtor.true, DataCtor.false] at impossible
  | boolFalse =>
      rcases targetTyped.bool_canonical with isTrue | isFalse
      · refine ⟨DataCtor.true, [], isTrue, ?_⟩
        intro impossible
        simp [DataCtor.true, DataCtor.false] at impossible
      · exact ⟨DataCtor.false, [], isFalse, fun _ => .nil⟩
  | listNil element =>
      obtain ⟨values, valueEq, valuesTyped⟩ := targetTyped.list_canonical
      cases values with
      | nil => exact ⟨DataCtor.nil, [], valueEq, fun _ => .nil⟩
      | cons head tail =>
          refine ⟨DataCtor.cons, [head, Value.buildList tail], valueEq, ?_⟩
          intro impossible
          simp [DataCtor.nil, DataCtor.cons] at impossible
  | listCons element =>
      obtain ⟨values, valueEq, valuesTyped⟩ := targetTyped.list_canonical
      cases values with
      | nil =>
          refine ⟨DataCtor.nil, [], valueEq, ?_⟩
          intro impossible
          simp [DataCtor.nil, DataCtor.cons] at impossible
      | cons head tail =>
          cases valuesTyped with
          | cons headTyped tailTyped =>
              exact ⟨DataCtor.cons, [head, Value.buildList tail], valueEq,
                fun _ => .cons headTyped (.cons (.list tailTyped) .nil)⟩

mutual

  theorem RuntimeDPatTyping.match_typed
      (typing : RuntimeDPatTyping pattern target bindingTypes)
      (targetTyped : ValueTyping value target) :
      matchValueDataPattern pattern value = none ∨
        ∃ bindings,
          matchValueDataPattern pattern value = some bindings ∧
          ValueTypings bindings bindingTypes := by
    cases typing with
    | var => exact .inr ⟨[value], rfl, .cons targetTyped .nil⟩
    | wild => exact .inr ⟨[], rfl, .nil⟩
    | ctor constructorTyped fields =>
        rename_i dataConstructor fieldTypes patterns
        obtain ⟨actual, arguments, rfl, argumentsTyped⟩ :=
          constructorTyped.value_shape targetTyped
        by_cases same : actual = dataConstructor
        · subst actual
          rcases fields.match_typed (argumentsTyped rfl) with mismatch |
            ⟨bindings, matched, bindingsTyped⟩
          · exact .inl (by simp [matchValueDataPattern, mismatch])
          · exact .inr ⟨bindings, by
              simp [matchValueDataPattern, matched], bindingsTyped⟩
        · have different : dataConstructor ≠ actual := fun equal => same equal.symm
          exact .inl (by
            simp [matchValueDataPattern, different])
    | tuple items =>
        obtain ⟨values, rfl, valuesTyped⟩ := targetTyped.product_canonical
        rcases items.match_typed valuesTyped with mismatch |
          ⟨bindings, matched, bindingsTyped⟩
        · exact .inl mismatch
        · exact .inr ⟨bindings, matched, bindingsTyped⟩

  theorem RuntimeDPatsTyping.match_typed
      (typing : RuntimeDPatsTyping patterns targets bindingTypes)
      (valuesTyped : ValueTypings values targets) :
      matchValueDataPatterns patterns values = none ∨
        ∃ bindings,
          matchValueDataPatterns patterns values = some bindings ∧
          ValueTypings bindings bindingTypes := by
    cases typing with
    | nil =>
        cases valuesTyped
        exact .inr ⟨[], rfl, .nil⟩
    | cons head tail =>
        cases valuesTyped with
        | cons headTyped tailTyped =>
            rcases head.match_typed headTyped with headMismatch |
              ⟨headBindings, headMatched, headBindingsTyped⟩
            · exact .inl (by
                simp [matchValueDataPatterns, headMismatch])
            · rcases tail.match_typed tailTyped with tailMismatch |
                ⟨tailBindings, tailMatched, tailBindingsTyped⟩
              · exact .inl (by
                  simp [matchValueDataPatterns, headMatched, tailMismatch])
              · exact .inr ⟨headBindings ++ tailBindings, by
                  simp [matchValueDataPatterns, headMatched, tailMatched],
                  headBindingsTyped.append tailBindingsTyped⟩

end

mutual

  theorem RuntimeDPatTyping.bindings_length
      (typing : RuntimeDPatTyping pattern target bindingTypes) :
      bindingTypes.length = pattern.bindingCount := by
    cases typing with
    | var => simp [DPat.bindingCount]
    | wild => simp [DPat.bindingCount]
    | ctor _ fields | tuple fields =>
        simpa [DPat.bindingCount] using fields.bindings_length

  theorem RuntimeDPatsTyping.bindings_length
      (typing : RuntimeDPatsTyping patterns targets bindingTypes) :
      bindingTypes.length = (patterns.map DPat.bindingCount).sum := by
    cases typing with
    | nil => rfl
    | cons head tail =>
        simp [head.bindings_length, tail.bindings_length]

end

mutual

  theorem RuntimePPatTyping.counts
      (typing : RuntimePPatTyping header target holes captureTypes) :
      holes.length = header.holeCount ∧
        captureTypes.length = header.captureCount := by
    cases typing with
    | hole => simp [PPat.holeCount, PPat.captureCount]
    | wild => simp [PPat.holeCount, PPat.captureCount]
    | capture => simp [PPat.holeCount, PPat.captureCount]
    | ctor fields =>
        simpa [PPat.holeCount, PPat.captureCount] using fields.counts

  theorem RuntimePPatsTyping.counts
      (typing : RuntimePPatsTyping headers targets holes captureTypes) :
      holes.length = (headers.map PPat.holeCount).sum ∧
        captureTypes.length = (headers.map PPat.captureCount).sum := by
    cases typing with
    | nil => simp
    | cons head tail =>
        have headCounts := head.counts
        have tailCounts := tail.counts
        constructor <;> simp [headCounts, tailCounts]

end

/-- Typed progress and preservation for one matcher arm, uniformly over the
zero/singleton/product hole decoding convention. -/
theorem tryMatcherArm_typedSafe
    (evalSafe : EmbeddedEvaluatorSafe
      (fun context expression target => RuntimeTyping expression target context)
      eval)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (captureValuesTyped : ValueTypings captureValues captureTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (nextMatchersTyped : RuntimeNextMatchersTyping
      (captureTypes ++ definitionTypes) nextMatchers holes)
    (armTyped : RuntimeMatcherArmTyping definitionTypes captureTypes
      matcherTarget holes arm)
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
      · exact .inr ⟨.miss, by
          simp [tryMatcherArm, dataMismatch], .miss⟩
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
          rcases evalSafe nextEnvironmentTyped nextMatchersTyped.runtimeTyping with
            nextTimeout | ⟨matcherProduct, nextSuccess, matcherProductTyped⟩
          · exact .inl (by
              simp [tryMatcherArm, dataMatch, bodySuccess',
                decompositionsDecoded', nextTimeout])
          · obtain ⟨matcherValues, matchersDecoded, matcherValuesTyped⟩ :=
              matcherProductTyped.decodeRuntimeProduct
            have matchersDecoded' :
                decodeProduct patterns.length matcherProduct = some matcherValues := by
              simpa [patternsLength] using matchersDecoded
            obtain ⟨branches, branchesBuilt, branchesTyped⟩ :=
              buildMatchingBranches_typed patternsLength matcherValuesTyped
                decompositionsTyped
            exact .inr ⟨.hit branches, by
              simp [tryMatcherArm, dataMatch, bodySuccess',
                decompositionsDecoded', nextSuccess, matchersDecoded', branchesBuilt],
              .hit branchesTyped⟩

/-- Ordered arm dispatch is safe for every finite typed arm list.  The empty
list returns a normal miss. -/
theorem firstHitMatcherArms_typedSafe
    (evalSafe : EmbeddedEvaluatorSafe
      (fun context expression target => RuntimeTyping expression target context)
      eval)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (captureValuesTyped : ValueTypings captureValues captureTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (nextMatchersTyped : RuntimeNextMatchersTyping
      (captureTypes ++ definitionTypes) nextMatchers holes)
    (armsTyped : RuntimeMatcherArmsTyping definitionTypes captureTypes
      matcherTarget holes arms)
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
  | cons head tail ih =>
      rcases tryMatcherArm_typedSafe evalSafe matcherEnvironmentTyped
          captureValuesTyped targetTyped nextMatchersTyped head patternsLength with
        headTimeout | ⟨headResult, headSuccess, headTyped⟩
      · exact .inl (by simp [firstHit, headTimeout])
      · cases headTyped with
        | hit branchesTyped =>
            exact .inr ⟨_, by simp [firstHit, headSuccess], .hit branchesTyped⟩
        | miss =>
            rcases ih with tailTimeout | ⟨tailResult, tailSuccess, tailTyped⟩
            · exact .inl (by simp [firstHit, headSuccess, tailTimeout])
            · exact .inr ⟨tailResult, by
                simp [firstHit, headSuccess, tailSuccess], tailTyped⟩

private theorem closeMatcherArmsResult_typed
    (typing : MatcherArmResultTyping holes result) :
    MatcherClauseResultTyping (closeMatcherArmsResult result) := by
  cases typing with
  | miss => exact .hit (holes := holes) .nil
  | hit branches => exact .hit branches

/-- A clause certificate at one concrete input pattern.  In addition to the
solved runtime types, it records the only source-pattern fact needed by
dispatch: successful header inspection extracts expressions with the solved
capture types, in source order. -/
inductive RuntimeMatcherClauseInputTyping
    (atomEnvironmentTypes definitionTypes : List Ty)
    (matcherTarget : Ty) (pattern : Source.Pattern) :
    Source.MatcherClause → Prop where
  | mk
      (header : RuntimePPatTyping patternPattern matcherTarget holes captureTypes)
      (nextMatchers : RuntimeNextMatchersTyping
        (captureTypes ++ definitionTypes) nextMatcherExpression holes)
      (arms : RuntimeMatcherArmsTyping definitionTypes captureTypes matcherTarget
        holes matcherArms)
      (captures : ∀ {dispatch},
        inspectPatternPattern patternPattern pattern = some dispatch →
        RuntimeCaptureExpressionsTyping
          (fun context expression target => RuntimeTyping expression target context)
          atomEnvironmentTypes dispatch.captures captureTypes) :
      RuntimeMatcherClauseInputTyping atomEnvironmentTypes definitionTypes
        matcherTarget pattern
        (.mk patternPattern nextMatcherExpression matcherArms)

/-- Pointwise input certificates for a source-ordered clause suffix. -/
inductive RuntimeMatcherClausesInputTyping
    (atomEnvironmentTypes definitionTypes : List Ty)
    (matcherTarget : Ty) (pattern : Source.Pattern) :
    List Source.MatcherClause → Prop where
  | nil : RuntimeMatcherClausesInputTyping atomEnvironmentTypes definitionTypes
      matcherTarget pattern []
  | cons
      (head : RuntimeMatcherClauseInputTyping atomEnvironmentTypes
        definitionTypes matcherTarget pattern clause)
      (tail : RuntimeMatcherClausesInputTyping atomEnvironmentTypes
        definitionTypes matcherTarget pattern clauses) :
      RuntimeMatcherClausesInputTyping atomEnvironmentTypes definitionTypes
        matcherTarget pattern (clause :: clauses)

theorem RuntimeMatcherClauseInputTyping.runtimeTyping
    (typing : RuntimeMatcherClauseInputTyping atomEnvironmentTypes
      definitionTypes matcherTarget pattern clause) :
    RuntimeMatcherClauseTyping definitionTypes matcherTarget clause := by
  cases typing with
  | mk header nextMatchers arms _ => exact .mk header nextMatchers arms

theorem RuntimeMatcherClausesInputTyping.runtimeTyping
    (typing : RuntimeMatcherClausesInputTyping atomEnvironmentTypes
      definitionTypes matcherTarget pattern clauses) :
    RuntimeMatcherClausesTyping definitionTypes matcherTarget clauses := by
  induction typing with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.runtimeTyping ih

/-- Typed progress for one clause.  A header mismatch is a normal `.miss`;
once a header matches, arm exhaustion is closed to a typed empty hit. -/
theorem tryMatcherClause_typedSafe
    (evalSafe : EmbeddedEvaluatorSafe
      (fun context expression target => RuntimeTyping expression target context)
      eval)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (clauseTyped : RuntimeMatcherClauseInputTyping atomEnvironmentTypes
      definitionTypes matcherTarget pattern clause) :
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
          have patternsLength : dispatch.holes.length = holes.length := by
            omega
          have capturesTyping := captures inspected
          rcases RuntimeCaptureExpressionsTyping.traverse_typed
              (eval := eval) evalSafe atomEnvironmentTyped capturesTyping with
            captureTimeout |
              ⟨captureValues, captureSuccess, captureValuesTyped⟩
          · exact .inl (by
              simp [tryMatcherClause, inspected, captureTimeout])
          · rcases firstHitMatcherArms_typedSafe evalSafe
                matcherEnvironmentTyped captureValuesTyped targetTyped
                nextMatchers arms patternsLength with
              armsTimeout | ⟨armsResult, armsSuccess, armsTyped⟩
            · exact .inl (by
                simp [tryMatcherClause, inspected, captureSuccess, armsTimeout,
                  FuelResult.map])
            · exact .inr ⟨closeMatcherArmsResult armsResult, by
                simp [tryMatcherClause, inspected, captureSuccess, armsSuccess,
                  FuelResult.map],
                closeMatcherArmsResult_typed armsTyped⟩

/-- Typed progress and preservation for a source-ordered clause suffix.  This
does not assert that some header must match. -/
theorem dispatchMatcherClauses_typedSafe
    (evalSafe : EmbeddedEvaluatorSafe
      (fun context expression target => RuntimeTyping expression target context)
      eval)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (clausesTyped : RuntimeMatcherClausesInputTyping atomEnvironmentTypes
      definitionTypes matcherTarget pattern clauses) :
    dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
        pattern target = .timeout ∨
      ∃ result,
        dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
          pattern target = .ok result ∧
        MatcherClauseResultTyping result := by
  induction clausesTyped with
  | nil => exact .inr ⟨.miss, rfl, .miss⟩
  | cons head tail ih =>
      rcases tryMatcherClause_typedSafe evalSafe atomEnvironmentTyped
          matcherEnvironmentTyped targetTyped head with
        headTimeout | ⟨headResult, headSuccess, headTyped⟩
      · exact .inl (by simp [dispatchMatcherClauses, firstHit, headTimeout])
      · cases headTyped with
        | hit branchesTyped =>
            exact .inr ⟨_, by
              simp [dispatchMatcherClauses, firstHit, headSuccess],
              .hit branchesTyped⟩
        | miss =>
            rcases ih with tailTimeout | ⟨tailResult, tailSuccess, tailTyped⟩
            · exact .inl (by
                simp [dispatchMatcherClauses, firstHit, headSuccess]
                simpa [dispatchMatcherClauses] using tailTimeout)
            · exact .inr ⟨tailResult, by
                simp [dispatchMatcherClauses, firstHit, headSuccess]
                simpa [dispatchMatcherClauses] using tailSuccess,
                tailTyped⟩

end TypePM.Runtime
