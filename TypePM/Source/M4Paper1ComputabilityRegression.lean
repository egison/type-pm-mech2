import TypePM.Source.M4MatcherTypingRegression
import TypePM.Source.M4RecursiveElaboration

/-!
# Kernel-computable Paper 1 source facts

The virtual-machine evaluator can run the complete Paper 1 matcher fixtures
directly, but reducing one complete inference run inside the kernel is much
larger.  This module proves the finite syntax budgets and the two Boolean
gates separately.  Later exact inference regressions can rewrite these facts
before computing the remaining fuel-indexed elaboration.
-/

namespace TypePM.Source.M4Paper1ComputabilityRegression

open Paper1Programs

set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem list_static_checks :
    MatcherTyping.staticChecks Paper1FrozenSignature.signature
      listMatcherClauses = true := by
  have shapes := list_matcher_clause_shapes_checked
  have arms : listMatcherClauses.all (fun clause =>
      MatcherTyping.armCoverageOK Paper1FrozenSignature.signature
          clause.arms ||
        MatcherTyping.structurallyRefinedArmCoverage clause) = true := by
    simp [listMatcherClauses, listMatcherNilClause, listMatcherConsClause,
      listMatcherJoinClause, listMatcherCatchAllClause, nilClause,
      catchAllClause, MatcherTyping.armCoverageOK,
      MatcherTyping.armsCatchAllLast,
      MatcherTyping.structurallyRefinedArmCoverage, MatcherClause.arms,
      MatcherArm.header, MatcherTyping.DPat.rootDataFormer?,
      MatcherTyping.DPat.isGeneralConstructor,
      MatcherTyping.DPat.isIrrefutable,
      Paper1FrozenSignature.lookup_data_nil,
      Paper1FrozenSignature.lookup_data_cons,
      Paper1FrozenSignature.lookup_true,
      Paper1FrozenSignature.lookup_false,
      Signature.constructorResult?, ConstructorSchemes.listNil,
      ConstructorSchemes.listCons, ConstructorSchemes.boolTrue,
      ConstructorSchemes.boolFalse, PolyDataTypes.list, PolyDataTypes.bool,
      Paper1FrozenSignature.signature, Paper1Signature.signature,
      Paper1Signature.dataConstructors, FrozenSignature.lookupDataConstructor,
      Signature.lookupDataConstructor, Scheme.callArity,
      DataCtor.true, DataCtor.false, DataCtor.nil, DataCtor.cons,
      DataFormer.bool, DataFormer.list] <;> decide
  have final : MatcherTyping.finalCatchAllVariableArm
      listMatcherClauses = true := by rfl
  have coverage : MatcherTyping.rootCoverageOK
      Paper1FrozenSignature.signature listMatcherClauses = true := by
    simp [MatcherTyping.rootCoverageOK, listMatcherClauses,
      listMatcherNilClause, listMatcherConsClause,
      listMatcherJoinClause, listMatcherCatchAllClause, nilClause,
      catchAllClause, MatcherTyping.PPat.rootFormer?,
      MatcherTyping.PPat.isGeneralConstructor, MatcherClause.header,
      Paper1FrozenSignature.lookup_pattern_nil,
      Paper1FrozenSignature.lookup_pattern_cons,
      Paper1FrozenSignature.lookup_pattern_join,
      Paper1FrozenSignature.signature, Paper1Signature.signature,
      Paper1Signature.patternConstructors, ListPatternSchemes.nil,
      ListPatternSchemes.cons, ListPatternSchemes.join,
      FrozenSignature.lookupPatternConstructor,
      Signature.lookupPatternConstructor, PatternCtor.nil, PatternCtor.cons,
      PatternCtor.join, PatternFormer.list]
  simp only [MatcherTyping.staticChecks, shapes, final, coverage,
    arms, Bool.true_and]

theorem multiset_static_checks :
    MatcherTyping.staticChecks Paper1FrozenSignature.signature
      multisetClauses = true := by
  simpa [M4MatcherTypingRegression.multisetClauses] using
    M4MatcherTypingRegression.all_seven_static_checks

theorem listSplitTailResults_public :
    listSplitTailResults =
      .matchAll (.var 1) (.app (.var 3) (.var 2))
        (.ctor PatternCtor.join [.var, .var])
        (.tuple [.var 0, .var 1]) := by
  rfl

theorem splitTailResults_public :
    splitTailResults =
      .matchAll (.var 1) (.app (.var 3) (.var 2))
        (.ctor PatternCtor.join [.var, .var])
        (.tuple [.var 0, .var 1]) := by
  rfl

theorem generalConsBody_public :
    generalConsBody =
      .matchAll (.var 0) (.app (.var 3) (.var 1))
        (.ctor PatternCtor.join
          [.var, .ctor PatternCtor.cons [.var, .var]])
        (.tuple [.var 1, .prim .append [.var 0, .var 2]]) := by
  rfl

theorem wholeValueBody_public :
    wholeValueBody =
      .matchFirst wholeValueTarget wholeValueMatcher
        [.mk (.tuple
            [.ctor PatternCtor.nil [], .ctor PatternCtor.nil []])
            wholeValueSuccess,
          .mk (.tuple
            [.ctor PatternCtor.cons [.var, .var],
              .ctor PatternCtor.cons
                [.value (.var 0), .value (.var 1)]])
            wholeValueSuccess]
        (sourceList []) := by
  rfl

theorem listSplitTailResults_complexity :
    listSplitTailResults.complexity = 15 := by
  rw [listSplitTailResults_public]
  simp

theorem splitTailResults_complexity : splitTailResults.complexity = 15 := by
  rw [splitTailResults_public]
  simp

theorem putCurrentAtPrefixEnd_complexity :
    putCurrentAtPrefixEnd.complexity = 18 := by
  simp [putCurrentAtPrefixEnd, Expr.pairDestructuringLambda]

theorem putCurrentRight_complexity : putCurrentRight.complexity = 18 := by
  simp [putCurrentRight, Expr.pairDestructuringLambda]

theorem putCurrentLeft_complexity : putCurrentLeft.complexity = 18 := by
  simp [putCurrentLeft, Expr.pairDestructuringLambda]

theorem listJoinConsBody_complexity : listJoinConsBody.complexity = 54 := by
  simp [listJoinConsBody, listSplitTailResults_complexity,
    putCurrentAtPrefixEnd_complexity, sourceList]

theorem joinConsBody_complexity : joinConsBody.complexity = 63 := by
  simp [joinConsBody, splitTailResults_complexity,
    putCurrentRight_complexity, putCurrentLeft_complexity]

theorem generalConsBody_complexity : generalConsBody.complexity = 23 := by
  rw [generalConsBody_public]
  simp

theorem wholeValueBody_complexity : wholeValueBody.complexity = 50 := by
  rw [wholeValueBody_public]
  simp [wholeValueTarget, wholeValueMatcher, wholeValueSuccess, sourceList,
    unit]

theorem listMatcherNilClause_complexity : listMatcherNilClause.complexity = 12 := by
  simp [listMatcherNilClause, nilClause, sourceList, unit]

theorem listMatcherConsClause_complexity :
    listMatcherConsClause.complexity = 19 := by
  simp [listMatcherConsClause, sourceList]

theorem listMatcherJoinClause_complexity :
    listMatcherJoinClause.complexity = 77 := by
  simp [listMatcherJoinClause, listJoinConsBody_complexity, sourceList]

theorem listMatcherCatchAllClause_complexity :
    listMatcherCatchAllClause.complexity = 9 := by
  simp [listMatcherCatchAllClause, catchAllClause, sourceList]

theorem listMatcherDefinition_complexity :
    listMatcherDefinition.complexity = 123 := by
  simp [listMatcherDefinition, listMatcherClauses,
    listMatcherNilClause_complexity, listMatcherConsClause_complexity,
    listMatcherJoinClause_complexity,
    listMatcherCatchAllClause_complexity]

theorem nilClause_complexity : nilClause.complexity = 12 := by
  simp [nilClause, sourceList, unit]

theorem headOnlyClause_complexity : headOnlyClause.complexity = 5 := by
  simp [headOnlyClause]

theorem valueConsClause_complexity : valueConsClause.complexity = 25 := by
  simp [valueConsClause, sourceList]

theorem generalConsClause_complexity : generalConsClause.complexity = 33 := by
  simp [generalConsClause, generalConsBody_complexity]

theorem joinClause_complexity : joinClause.complexity = 86 := by
  simp [joinClause, joinConsBody_complexity, sourceList]

theorem wholeValueClause_complexity : wholeValueClause.complexity = 54 := by
  simp [wholeValueClause, wholeValueBody_complexity]

theorem catchAllClause_complexity : catchAllClause.complexity = 9 := by
  simp [catchAllClause, sourceList]

theorem multisetDefinition_complexity : multisetDefinition.complexity = 233 := by
  simp [multisetDefinition, multisetClauses, nilClause_complexity,
    headOnlyClause_complexity, valueConsClause_complexity,
    generalConsClause_complexity, joinClause_complexity,
    wholeValueClause_complexity, catchAllClause_complexity]

theorem closedMultisetDefinition_complexity :
    closedMultisetDefinition.complexity = 358 := by
  simp [closedMultisetDefinition, multisetWithListArgument,
    multisetDefinition_complexity, listMatcherDefinition_complexity]

theorem multisetSomething_complexity : multisetSomething.complexity = 360 := by
  simp [multisetSomething, closedMultisetDefinition_complexity]

private theorem directSelf_compute
    (clauses : List MatcherClause) (budget : Nat)
    (complexity : (.matcher clauses : Expr).complexity = budget)
    (result : DirectSelf.checkFuel (budget * 3 + 1) 1
      (.matcher clauses) = true) :
    DirectSelf.check 1 (.matcher clauses) = true := by
  unfold DirectSelf.check
  rw [complexity]
  exact result

theorem list_direct_self_check :
    DirectSelf.check 1 (.matcher listMatcherClauses) = true := by
  apply directSelf_compute listMatcherClauses 122
  · simpa [listMatcherDefinition] using listMatcherDefinition_complexity
  · simp [DirectSelf.checkFuel, DirectSelf.checkHeadFuel,
      DirectSelf.checkListFuel, DirectSelf.checkPatternFuel,
      DirectSelf.checkPatternsFuel, DirectSelf.checkClauseFuel,
      DirectSelf.checkClausesFuel, DirectSelf.checkArmFuel,
      DirectSelf.checkArmsFuel, DirectSelf.checkMatchFirstArmFuel,
      DirectSelf.checkMatchFirstArmsFuel, DirectSelf.mentions,
      DirectSelf.mentionsList, DirectSelf.mentionsPattern,
      DirectSelf.mentionsPatterns, DirectSelf.mentionsClause,
      DirectSelf.mentionsClauses, DirectSelf.mentionsArm,
      DirectSelf.mentionsArms, DirectSelf.mentionsMatchFirstArm,
      DirectSelf.mentionsMatchFirstArms, DirectSelf.patternBindingCount,
      DirectSelf.patternBindingCountList, listMatcherClauses,
      listMatcherNilClause, listMatcherConsClause, listMatcherJoinClause,
      listMatcherCatchAllClause, nilClause, catchAllClause, listJoinConsBody,
      listSplitTailResults_public, putCurrentAtPrefixEnd, sourceList,
      Expr.pairDestructuringLambda, PPat.captureCount,
      DPat.bindingCount, unit]

theorem multiset_direct_self_check :
    DirectSelf.check 1 (.matcher multisetClauses) = true := by
  apply directSelf_compute multisetClauses 232
  · simpa [multisetDefinition] using multisetDefinition_complexity
  · simp [DirectSelf.checkFuel, DirectSelf.checkHeadFuel,
      DirectSelf.checkListFuel, DirectSelf.checkPatternFuel,
      DirectSelf.checkPatternsFuel, DirectSelf.checkClauseFuel,
      DirectSelf.checkClausesFuel, DirectSelf.checkArmFuel,
      DirectSelf.checkArmsFuel, DirectSelf.checkMatchFirstArmFuel,
      DirectSelf.checkMatchFirstArmsFuel, DirectSelf.mentions,
      DirectSelf.mentionsList, DirectSelf.mentionsPattern,
      DirectSelf.mentionsPatterns, DirectSelf.mentionsClause,
      DirectSelf.mentionsClauses, DirectSelf.mentionsArm,
      DirectSelf.mentionsArms, DirectSelf.mentionsMatchFirstArm,
      DirectSelf.mentionsMatchFirstArms, DirectSelf.patternBindingCount,
      DirectSelf.patternBindingCountList, multisetClauses, nilClause,
      headOnlyClause, valueConsClause, generalConsClause,
      generalConsBody_public, joinClause, joinConsBody,
      splitTailResults_public, putCurrentRight,
      putCurrentLeft, wholeValueClause, wholeValueBody_public,
      wholeValueTarget, wholeValueMatcher, wholeValueSuccess,
      catchAllClause, sourceList, Expr.pairDestructuringLambda,
      PPat.captureCount, DPat.bindingCount, unit]

end TypePM.Source.M4Paper1ComputabilityRegression
