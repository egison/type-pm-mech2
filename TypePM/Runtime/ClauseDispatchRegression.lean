import TypePM.Runtime.ClauseDispatch
import TypePM.Runtime.CombinedAtomReducer
import TypePM.Source.M4MatcherPatternRegression

/-!
# Concrete matcher-clause dispatch regressions

Each of the seven multiset matcher headers is exercised through a complete
`MatcherClause`: pattern-pattern inspection, ordered data-pattern arms, body
decoding, next-matcher decoding, and branch construction all run here.
-/

namespace TypePM.Runtime.ClauseDispatchRegression

open TypePM.Source
open TypePM.Source.M4MatcherPatternRegression

def elementMatcher : Value := Value.matcherClosure [] []
def multisetMatcher : Value := Value.matcherClosure [] []

def nilValue : Value := Value.nilValue
def list12 : Value :=
  Value.buildList [.int 1, .int 2]

def bodyZero : Expr := .lit 10
def nextZero : Expr := .lit 11
def bodyOne : Expr := .lit 20
def nextOne : Expr := .lit 21
def bodyValueCons : Expr := .lit 22
def nextMultiset : Expr := .lit 23
def bodyJoinEmpty : Expr := .lit 24
def bodyWholeSuccess : Expr := .lit 25
def bodyCatchAll : Expr := .lit 26
def bodyTwo : Expr := .lit 30
def nextTwo : Expr := .lit 31
def nextJoin : Expr := .lit 32
def nextSomething : Expr := .lit 33
def bodyEmpty : Expr := .lit 40
def captureExpression : Expr := .lit 100

/-- A small evaluator oracle for the clause boundary.  The expression tags
make the expected body and next-matcher shapes explicit. -/
def shapeEval (_ : ValueEnvironment) : Expr → FuelResult Value
  | .lit 10 => .ok (Value.buildList [.tuple []])
  | .lit 11 => .ok (.tuple [])
  | .lit 20 => .ok (Value.buildList [.int 1, .int 2])
  | .lit 21 => .ok elementMatcher
  | .lit 22 => .ok (Value.buildList [Value.buildList [.int 2]])
  | .lit 23 => .ok multisetMatcher
  | .lit 24 =>
      .ok (Value.buildList [.tuple [Value.nilValue, Value.nilValue]])
  | .lit 25 => .ok (Value.buildList [.tuple []])
  | .lit 26 => .ok (Value.buildList [list12])
  | .lit 30 =>
      .ok (Value.buildList
        [.tuple [.int 1, list12], .tuple [.int 2, Value.nilValue]])
  | .lit 31 => .ok (.tuple [elementMatcher, multisetMatcher])
  | .lit 32 => .ok (.tuple [multisetMatcher, multisetMatcher])
  | .lit 33 => .ok .something
  | .lit 40 => .ok Value.nilValue
  | .lit 100 => .ok (.int 1)
  | _ => .stuck

def fallbackArmZero : MatcherArm := .mk .wild bodyEmpty
def nilClause : MatcherClause :=
  .mk nilHeader nextZero
    [.mk (.ctor DataCtor.nil []) bodyZero, fallbackArmZero]

def headOnlyClause : MatcherClause :=
  .mk headOnlyHeader nextOne [.mk .var bodyOne]

def valueConsClause : MatcherClause :=
  .mk valueConsHeader nextMultiset [.mk .var bodyValueCons]

def generalConsClause : MatcherClause :=
  .mk generalConsHeader nextTwo [.mk .var bodyTwo]

def joinClause : MatcherClause :=
  .mk joinHeader nextJoin
    [.mk (.ctor DataCtor.nil []) bodyJoinEmpty,
      .mk (.ctor DataCtor.cons [.var, .var]) bodyTwo]

def wholeValueClause : MatcherClause :=
  .mk wholeValueHeader nextZero [.mk .var bodyWholeSuccess]

def catchAllClause : MatcherClause :=
  .mk catchAllHeader nextSomething [.mk .var bodyCatchAll]

def nilPattern : Pattern := .ctor PatternCtor.nil []
def consPattern : Pattern := .ctor PatternCtor.cons [.var, .wild]
def valueConsPattern : Pattern :=
  .ctor PatternCtor.cons [.value captureExpression, .wild]
def joinPattern : Pattern := .ctor PatternCtor.join [.var, .wild]

macro "reduce_multiset_dispatch" : tactic =>
  `(tactic|
    simp [tryMatcherClause, closeMatcherArmsResult,
      dispatchMatcherClauses, firstHit,
      tryMatcherArm, inspectPatternPattern, inspectPatternPatterns,
      matchValueDataPattern, matchValueDataPatterns,
      PatternDispatch.empty, PatternDispatch.append,
      FuelResult.traverse, FuelResult.bind, FuelResult.map,
      Value.nilValue, Value.consValue, Value.buildList, Value.viewList,
      decodeDecompositions, decodeProduct,
      buildMatchingBranches, zipMatchingAtoms,
      elementMatcher, multisetMatcher, list12,
      bodyZero, nextZero, bodyOne, nextOne, bodyValueCons, nextMultiset,
      bodyJoinEmpty, bodyWholeSuccess, bodyCatchAll, bodyTwo, nextTwo,
      nextJoin, nextSomething, bodyEmpty,
      captureExpression, shapeEval, fallbackArmZero,
      nilClause, headOnlyClause, valueConsClause, generalConsClause,
      joinClause, wholeValueClause, catchAllClause,
      nilPattern, consPattern, valueConsPattern, joinPattern,
      nilHeader, headOnlyHeader, valueConsHeader, generalConsHeader,
      joinHeader, wholeValueHeader, catchAllHeader])

theorem nil_clause_complete_dispatch_exact :
    tryMatcherClause shapeEval [] [] nilPattern Value.nilValue nilClause =
      .ok (.hit [[]]) := by
  reduce_multiset_dispatch

theorem head_only_clause_complete_dispatch_exact :
    tryMatcherClause shapeEval [] [] consPattern list12 headOnlyClause =
      .ok (.hit
        [[⟨.var, elementMatcher, .int 1⟩],
          [⟨.var, elementMatcher, .int 2⟩]]) := by
  reduce_multiset_dispatch

theorem value_cons_clause_complete_dispatch_exact :
    tryMatcherClause shapeEval [] [] valueConsPattern list12 valueConsClause =
      .ok (.hit
        [[⟨.wild, multisetMatcher, Value.buildList [.int 2]⟩]]) := by
  reduce_multiset_dispatch

theorem general_cons_clause_complete_dispatch_exact :
    tryMatcherClause shapeEval [] [] consPattern list12 generalConsClause =
      .ok (.hit
        [[⟨.var, elementMatcher, .int 1⟩,
            ⟨.wild, multisetMatcher, list12⟩],
          [⟨.var, elementMatcher, .int 2⟩,
            ⟨.wild, multisetMatcher, Value.nilValue⟩]]) := by
  reduce_multiset_dispatch

theorem join_clause_second_arm_dispatch_exact :
    tryMatcherClause shapeEval [] [] joinPattern list12 joinClause =
      .ok (.hit
        [[⟨.var, multisetMatcher, .int 1⟩,
            ⟨.wild, multisetMatcher, list12⟩],
          [⟨.var, multisetMatcher, .int 2⟩,
            ⟨.wild, multisetMatcher, Value.nilValue⟩]]) := by
  reduce_multiset_dispatch

theorem join_clause_first_arm_dispatch_exact :
    tryMatcherClause shapeEval [] [] joinPattern Value.nilValue joinClause =
      .ok (.hit
        [[⟨.var, multisetMatcher, Value.nilValue⟩,
            ⟨.wild, multisetMatcher, Value.nilValue⟩]]) := by
  reduce_multiset_dispatch

theorem whole_value_clause_complete_dispatch_exact :
    tryMatcherClause shapeEval [] [] (.value captureExpression) (.int 1)
        wholeValueClause = .ok (.hit [[]]) := by
  reduce_multiset_dispatch

theorem catch_all_clause_complete_dispatch_exact :
    tryMatcherClause shapeEval [] [] (.tuple []) list12 catchAllClause =
      .ok (.hit
        [[⟨.tuple [], .something, list12⟩]]) := by
  reduce_multiset_dispatch

theorem all_seven_concrete_clause_shapes_checked :
    MatcherClause.checkShapes Paper1FrozenSignature.signature
      [nilClause, headOnlyClause, valueConsClause, generalConsClause,
        joinClause, wholeValueClause, catchAllClause] = true := by
  simp [MatcherClause.checkShapes, MatcherClause.toShape, MatcherArm.toHeader,
    MatcherClauseShapes.check, MatcherClauseShapes.catchAllLast,
    MatcherClauseShapes.isCatchAll, MatcherClauseShape.check,
    MatcherArmHeader.check, MatcherArmHeader.canonical,
    HoleConvention.ofCount, PPat.shapeOK, PPat.shapesOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
    DPat.constructorArity?, nilClause, headOnlyClause, valueConsClause,
    generalConsClause, joinClause, wholeValueClause, catchAllClause,
    fallbackArmZero, nilHeader, headOnlyHeader,
    valueConsHeader, generalConsHeader, joinHeader, wholeValueHeader,
    catchAllHeader, ConstructorSchemes.listNil, ConstructorSchemes.listCons,
    ListPatternSchemes.nil, ListPatternSchemes.cons, ListPatternSchemes.join,
    PolyDataTypes.list]

/-! ## Ordered failure boundaries -/

def alwaysMissClause : MatcherClause :=
  .mk nilHeader nextZero [.mk (.ctor DataCtor.nil []) bodyZero]

def laterCatchClause : MatcherClause :=
  .mk catchAllHeader nextOne [.mk .var bodyOne]

theorem pattern_mismatch_alone_advances_to_next_clause :
    dispatchMatcherClauses shapeEval [] []
        [alwaysMissClause, laterCatchClause] (.tuple []) list12 =
      .ok (.hit
        [[⟨.tuple [], elementMatcher, .int 1⟩],
          [⟨.tuple [], elementMatcher, .int 2⟩]]) := by
  simp only [alwaysMissClause, laterCatchClause]
  reduce_multiset_dispatch

def firstArmMissClause : MatcherClause :=
  .mk catchAllHeader nextOne
    [.mk (.ctor DataCtor.nil []) bodyEmpty, .mk .var bodyOne]

theorem data_mismatch_alone_advances_to_next_arm :
    tryMatcherClause shapeEval [] [] (.tuple []) list12 firstArmMissClause =
      .ok (.hit
        [[⟨.tuple [], elementMatcher, .int 1⟩],
          [⟨.tuple [], elementMatcher, .int 2⟩]]) := by
  simp only [firstArmMissClause]
  reduce_multiset_dispatch

def allDataArmsMissClause : MatcherClause :=
  .mk catchAllHeader nextOne [.mk (.ctor DataCtor.nil []) bodyEmpty]

theorem all_data_arm_mismatch_is_normal_empty_result :
    tryMatcherClause shapeEval [] [] (.tuple []) list12
        allDataArmsMissClause = .ok (.hit []) := by
  simp only [allDataArmsMissClause]
  reduce_multiset_dispatch

theorem selected_pattern_clause_does_not_fall_through_after_data_mismatch :
    dispatchMatcherClauses shapeEval [] []
        [allDataArmsMissClause, laterCatchClause] (.tuple []) list12 =
      .ok (.hit []) := by
  simp only [allDataArmsMissClause, laterCatchClause]
  reduce_multiset_dispatch

def emptyHitClause : MatcherClause :=
  .mk catchAllHeader nextOne [.mk .var bodyEmpty, .mk .var bodyOne]

theorem empty_candidate_list_is_hit_and_stops_later_arm :
    tryMatcherClause shapeEval [] [] (.tuple []) list12 emptyHitClause =
      .ok (.hit []) := by
  simp only [emptyHitClause]
  reduce_multiset_dispatch

theorem empty_candidate_list_stops_later_clause :
    dispatchMatcherClauses shapeEval [] [] [emptyHitClause, laterCatchClause]
        (.tuple []) list12 = .ok (.hit []) := by
  simp only [emptyHitClause, laterCatchClause]
  reduce_multiset_dispatch

/-! ## Environment order and evaluation environment boundaries -/

def environmentAuditEval : ValueEnvironment → Expr → FuelResult Value
  | [.int 80], .lit 100 => .ok (.int 70)
  | [.int 1, .int 70, .int 90], .lit 101 =>
      .ok (Value.buildList [.tuple []])
  | [.int 90], .lit 102 => .ok (.tuple [])
  | _, _ => .stuck

def environmentAuditClause : MatcherClause :=
  .mk wholeValueHeader (.lit 102) [.mk .var (.lit 101)]

theorem capture_data_and_matcher_environments_are_exact :
    tryMatcherClause environmentAuditEval [.int 80] [.int 90]
        (.value (.lit 100)) (.int 1) environmentAuditClause =
      .ok (.hit [[]]) := by
  simp only [environmentAuditClause]
  reduce_multiset_dispatch
  simp [environmentAuditEval, Value.buildList, Value.nilValue,
    Value.consValue, Value.viewList, decodeProduct, zipMatchingAtoms]

def wrongAtomEnvironmentEval : ValueEnvironment → Expr → FuelResult Value
  | [.int 90], .lit 100 => .ok (.int 70)
  | _, _ => .stuck

theorem captures_do_not_use_matcher_definition_environment :
    tryMatcherClause wrongAtomEnvironmentEval [.int 80] [.int 90]
        (.value (.lit 100)) (.int 1) environmentAuditClause = .stuck := by
  simp only [environmentAuditClause]
  reduce_multiset_dispatch
  simp [wrongAtomEnvironmentEval]

/-! ## Malformed shapes and control-result propagation -/

def malformedBodyEval (_ : ValueEnvironment) : Expr → FuelResult Value
  | .lit 50 => .ok (.data DataCtor.cons [.int 1, .int 2])
  | _ => .stuck

def malformedBodyClause : MatcherClause :=
  .mk catchAllHeader nextOne [.mk .var (.lit 50)]

theorem improper_decomposition_list_is_stuck :
    tryMatcherClause malformedBodyEval [] [] (.tuple []) (.int 1)
        malformedBodyClause = .stuck := by
  simp only [malformedBodyClause]
  reduce_multiset_dispatch
  simp [malformedBodyEval, Value.viewList]

def wrongTupleBodyEval (_ : ValueEnvironment) : Expr → FuelResult Value
  | .lit 51 => .ok (Value.buildList [.tuple [.int 1]])
  | _ => .stuck

def wrongTupleBodyClause : MatcherClause :=
  .mk generalConsHeader nextTwo
    [.mk (.ctor DataCtor.cons [.var, .var]) (.lit 51)]

theorem wrong_decomposition_product_arity_is_stuck :
    tryMatcherClause wrongTupleBodyEval [] [] consPattern list12
        wrongTupleBodyClause = .stuck := by
  simp only [wrongTupleBodyClause]
  reduce_multiset_dispatch
  simp [wrongTupleBodyEval, Value.buildList, Value.nilValue,
    Value.consValue, Value.viewList, decodeProduct]

def wrongMatcherProductEval (_ : ValueEnvironment) : Expr → FuelResult Value
  | .lit 30 => .ok (Value.buildList [.tuple [.int 1, Value.nilValue]])
  | .lit 52 => .ok (.tuple [])
  | _ => .stuck

def wrongMatcherProductClause : MatcherClause :=
  .mk generalConsHeader (.lit 52)
    [.mk (.ctor DataCtor.cons [.var, .var]) bodyTwo]

theorem wrong_next_matcher_product_arity_is_stuck :
    tryMatcherClause wrongMatcherProductEval [] [] consPattern list12
        wrongMatcherProductClause = .stuck := by
  simp only [wrongMatcherProductClause]
  reduce_multiset_dispatch
  simp [wrongMatcherProductEval, Value.buildList, Value.nilValue,
    Value.consValue, Value.viewList, decodeProduct]

def timeoutBodyEval (_ : ValueEnvironment) : Expr → FuelResult Value
  | .lit 60 => .timeout
  | _ => .stuck

def timeoutBodyClause : MatcherClause :=
  .mk catchAllHeader nextOne [.mk .var (.lit 60)]

theorem arm_body_timeout_propagates_before_later_arm :
    tryMatcherClause timeoutBodyEval [] [] (.tuple []) (.int 1)
        (.mk catchAllHeader nextOne
          [.mk .var (.lit 60), .mk .var bodyOne]) = .timeout := by
  reduce_multiset_dispatch
  simp [timeoutBodyEval]

def timeoutNextEval (_ : ValueEnvironment) : Expr → FuelResult Value
  | .lit 20 => .ok (Value.buildList [.int 1])
  | .lit 61 => .timeout
  | _ => .stuck

theorem next_matcher_timeout_propagates_before_later_clause :
    dispatchMatcherClauses timeoutNextEval [] []
        [(.mk catchAllHeader (.lit 61) [.mk .var bodyOne]), laterCatchClause]
        (.tuple []) (.int 1) = .timeout := by
  simp only [laterCatchClause]
  reduce_multiset_dispatch
  simp [timeoutNextEval, Value.buildList, Value.nilValue,
    Value.consValue, Value.viewList, decodeProduct]

def stuckCaptureEval (_ : ValueEnvironment) (_ : Expr) : FuelResult Value :=
  .stuck

theorem capture_stuck_propagates_before_arms :
    tryMatcherClause stuckCaptureEval [] [] (.value captureExpression) (.int 1)
        wholeValueClause = .stuck := by
  reduce_multiset_dispatch
  simp [stuckCaptureEval]

/-! ## Cursor suffix and relational adequacy -/

def cursorMatcher : Value :=
  .matcherV [] [alwaysMissClause, laterCatchClause] [laterCatchClause]

theorem cursor_suffix_is_valid : cursorMatcher.MatcherCursorValid := by
  exact ⟨[alwaysMissClause], rfl⟩

theorem matcher_dispatch_uses_remaining_suffix :
    dispatchMatcherValue shapeEval [] cursorMatcher (.tuple []) list12 =
      .ok (.hit
        [[⟨.tuple [], elementMatcher, .int 1⟩],
          [⟨.tuple [], elementMatcher, .int 2⟩]]) := by
  simp only [dispatchMatcherValue, cursorMatcher, laterCatchClause]
  reduce_multiset_dispatch

theorem non_matcher_dispatch_is_stuck :
    dispatchMatcherValue shapeEval [] (.int 1) (.tuple []) list12 = .stuck := by
  rfl

theorem matcher_atom_handler_builds_shared_reduction :
    reduceMatcherAtom shapeEval []
        ⟨.tuple [], cursorMatcher, list12⟩ =
      .ok (.hit
        ⟨[[⟨.tuple [], elementMatcher, .int 1⟩],
            [⟨.tuple [], elementMatcher, .int 2⟩]], []⟩) := by
  simp [reduceMatcherAtom, cursorMatcher, laterCatchClause]
  reduce_multiset_dispatch
  simp [clauseResultToAtomReduction]

theorem matcher_atom_handler_misses_non_matcher :
    reduceMatcherAtom shapeEval []
        ⟨.tuple [], .something, list12⟩ = .ok .miss := by
  rfl

theorem builtin_miss_falls_through_to_concrete_matcher_handler :
    combineAtomReducers (reduceBuiltinAtom shapeEval)
        (reduceMatcherAtom shapeEval) []
        ⟨.tuple [], cursorMatcher, list12⟩ =
      .ok (.hit
        ⟨[[⟨.tuple [], elementMatcher, .int 1⟩],
            [⟨.tuple [], elementMatcher, .int 2⟩]], []⟩) := by
  have builtinMiss :
      reduceBuiltinAtom shapeEval []
        ⟨.tuple [], cursorMatcher, list12⟩ = .ok .miss := by
    simp [reduceBuiltinAtom, cursorMatcher]
  rw [combineAtomReducers_primary_miss _ _ builtinMiss]
  exact matcher_atom_handler_builds_shared_reduction

theorem matcher_atom_handler_timeout_propagates :
    reduceMatcherAtom timeoutNextEval []
        ⟨.tuple [],
          .matcherV []
            [(.mk catchAllHeader (.lit 61) [.mk .var bodyOne])]
            [(.mk catchAllHeader (.lit 61) [.mk .var bodyOne])],
          .int 1⟩ = .timeout := by
  simp [reduceMatcherAtom]
  reduce_multiset_dispatch
  simp [timeoutNextEval, Value.buildList, Value.nilValue,
    Value.consValue, Value.viewList, decodeProduct]

theorem successful_dispatch_has_independent_derivation :
    MatcherClausesDispatch shapeEval [] [] (.tuple []) list12
      [alwaysMissClause, laterCatchClause]
      (.hit
        [[⟨.tuple [], elementMatcher, .int 1⟩],
          [⟨.tuple [], elementMatcher, .int 2⟩]]) := by
  exact (dispatchMatcherClauses_eq_ok_iff _ _ _ _ _ _ _).mp
    pattern_mismatch_alone_advances_to_next_clause

theorem matcher_atom_hit_has_independent_derivation :
    MatcherAtomReduces shapeEval []
      ⟨.tuple [], cursorMatcher, list12⟩
      ⟨[[⟨.tuple [], elementMatcher, .int 1⟩],
          [⟨.tuple [], elementMatcher, .int 2⟩]], []⟩ := by
  exact (reduceMatcherAtom_hit_iff _ _ _ _).mp
    matcher_atom_handler_builds_shared_reduction

theorem explicit_zip_rejects_all_three_length_mismatches :
    zipMatchingAtoms [.var] [] [.int 1] = none ∧
      zipMatchingAtoms [] [elementMatcher] [] = none ∧
      zipMatchingAtoms [] [] [.int 1] = none := by
  exact ⟨rfl, rfl, rfl⟩

end TypePM.Runtime.ClauseDispatchRegression
