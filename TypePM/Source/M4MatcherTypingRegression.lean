import TypePM.Source.M4MatcherTyping
import TypePM.Source.M4MatcherClauseShapeRegression
import TypePM.Source.Paper1Programs

/-!
# M4 matcher-literal typing regressions

The seven clauses below use the corrected outer data-pattern structure and
the exact bodies from Paper 1.  The final source AST represents nested
`matchAll`, tuple-pattern lambdas, and single-result `matchFirst`; typing those
bodies together still requires the recursive M4 dispatcher documented below.
-/

namespace TypePM.Source.M4MatcherTypingRegression

open M4MatcherPatternRegression
open MatcherTyping

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

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

def element : Ty := .var ⟨0⟩
def elementCapability : Cap := .var ⟨0⟩
def listElement : Ty := DataTypes.list element
def listCapability : Cap := .con PatternFormer.list [elementCapability]

/-- Index 0 is the element matcher and index 1 is the recursive multiset
matcher.  The latter is an explicit checkpoint assumption until `fixE` is
composed with `elaborateMatcherLiteralUsing`. -/
def matcherContext : Context :=
  [ Scheme.mono (.matcher elementCapability element),
    Scheme.mono (.matcher listCapability listElement) ]

theorem matcher_context_initial_supply :
    matcherContext.initialSupply = ⟨1, 1⟩ := by
  rfl

def emptyList : Expr := .ctor DataCtor.nil []
def singleton (item : Expr) : Expr :=
  .ctor DataCtor.cons [item, emptyList]
def unit : Expr := Paper1Programs.unit
def singletonUnit : Expr := singleton unit

def nilClause : MatcherClause := Paper1Programs.nilClause
def headOnlyClause : MatcherClause := Paper1Programs.headOnlyClause
def valueConsClause : MatcherClause := Paper1Programs.valueConsClause
def generalConsClause : MatcherClause := Paper1Programs.generalConsClause
def joinClause : MatcherClause := Paper1Programs.joinClause
def wholeValueClause : MatcherClause := Paper1Programs.wholeValueClause
def catchAllClause : MatcherClause := Paper1Programs.catchAllClause
def multisetClauses : List MatcherClause := Paper1Programs.multisetClauses

theorem all_seven_final_shapes_exact :
    multisetClauses.map MatcherClause.toShape =
      M4MatcherClauseShapeRegression.multisetClauses := by
  simp [multisetClauses, nilClause, headOnlyClause, valueConsClause,
    generalConsClause, joinClause, wholeValueClause, catchAllClause,
    Paper1Programs.multisetClauses, Paper1Programs.nilClause,
    Paper1Programs.headOnlyClause, Paper1Programs.valueConsClause,
    Paper1Programs.generalConsClause, Paper1Programs.joinClause,
    Paper1Programs.wholeValueClause, Paper1Programs.catchAllClause,
    MatcherClause.toShape, MatcherArm.toHeader,
    MatcherClause.header, MatcherClause.nextMatchers, MatcherClause.arms,
    MatcherArm.header, MatcherArm.body,
    M4MatcherClauseShapeRegression.multisetClauses,
    M4MatcherClauseShapeRegression.nilClause,
    M4MatcherClauseShapeRegression.headOnlyClause,
    M4MatcherClauseShapeRegression.valueConsClause,
    M4MatcherClauseShapeRegression.generalConsClause,
    M4MatcherClauseShapeRegression.joinClause,
    M4MatcherClauseShapeRegression.wholeValueClause,
    M4MatcherClauseShapeRegression.catchAllClause,
    M4MatcherClauseShapeRegression.nilArm,
    M4MatcherClauseShapeRegression.consArm,
    M4MatcherClauseShapeRegression.variableArm,
    M4MatcherClauseShapeRegression.wildcardArm,
    MatcherArmHeader.canonical, HoleConvention.ofCount,
    PPat.holeCount, nilHeader, headOnlyHeader, valueConsHeader,
    generalConsHeader, joinHeader, wholeValueHeader, catchAllHeader]

theorem all_seven_static_checks :
    staticChecks Paper1FrozenSignature.signature multisetClauses = true := by
  have shapes : MatcherClause.checkShapes Paper1FrozenSignature.signature
      multisetClauses = true := by
    rw [MatcherClause.checkShapes, all_seven_final_shapes_exact]
    exact M4MatcherClauseShapeRegression.all_seven_clause_shapes_checked
  have arms : multisetClauses.all (fun clause =>
      armCoverageOK Paper1FrozenSignature.signature clause.arms) = true := by
    simp [multisetClauses, nilClause, headOnlyClause, valueConsClause,
      generalConsClause, joinClause, wholeValueClause, catchAllClause,
      Paper1Programs.multisetClauses, Paper1Programs.nilClause,
      Paper1Programs.headOnlyClause, Paper1Programs.valueConsClause,
      Paper1Programs.generalConsClause, Paper1Programs.joinClause,
      Paper1Programs.wholeValueClause, Paper1Programs.catchAllClause,
      armCoverageOK, armsCatchAllLast,
      MatcherClause.arms, MatcherArm.header,
      MatcherTyping.DPat.rootDataFormer?, MatcherTyping.DPat.isGeneralConstructor,
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
  have final : finalCatchAllVariableArm multisetClauses = true := by rfl
  have coverage : rootCoverageOK Paper1FrozenSignature.signature
      multisetClauses = true := by
    simp [rootCoverageOK, multisetClauses, nilClause, headOnlyClause,
      valueConsClause, generalConsClause, joinClause, wholeValueClause,
      catchAllClause, MatcherTyping.PPat.rootFormer?,
      Paper1Programs.multisetClauses, Paper1Programs.nilClause,
      Paper1Programs.headOnlyClause, Paper1Programs.valueConsClause,
      Paper1Programs.generalConsClause, Paper1Programs.joinClause,
      Paper1Programs.wholeValueClause, Paper1Programs.catchAllClause,
      MatcherTyping.PPat.isGeneralConstructor,
      MatcherClause.header,
      nilHeader, headOnlyHeader, valueConsHeader, generalConsHeader,
      joinHeader, wholeValueHeader, catchAllHeader,
      Paper1FrozenSignature.lookup_pattern_nil,
      Paper1FrozenSignature.lookup_pattern_cons,
      Paper1FrozenSignature.lookup_pattern_join,
      Paper1FrozenSignature.signature, Paper1Signature.signature,
      Paper1Signature.patternConstructors, ListPatternSchemes.nil,
      ListPatternSchemes.cons, ListPatternSchemes.join,
      FrozenSignature.lookupPatternConstructor,
      Signature.lookupPatternConstructor, PatternCtor.nil, PatternCtor.cons,
      PatternCtor.join, PatternFormer.list]
  simp only [staticChecks, shapes, final, coverage, Bool.true_and]
  simp only [Bool.and_true]
  rw [List.all_eq_true] at arms ⊢
  intro clause member
  simp [arms clause member]

theorem hole_product_zero_one_k_exact :
    holeProductTarget [] = .prod [] ∧
      holeProductTarget [⟨elementCapability, element⟩] = element ∧
      holeProductTarget
        [⟨elementCapability, element⟩, ⟨listCapability, listElement⟩] =
          .prod [element, listElement] := by
  exact ⟨rfl, rfl, rfl⟩

def identityClause : MatcherClause :=
  .mk .hole .something [.mk .var emptyList]

def identityLiteral : List MatcherClause := [identityClause]

theorem identity_literal_static_checks :
    staticChecks Paper1FrozenSignature.signature identityLiteral = true := by
  simp [staticChecks, identityLiteral, identityClause,
    MatcherClause.checkShapes, MatcherClause.toShape,
    MatcherClauseShapes.check, MatcherClauseShapes.catchAllLast,
    MatcherClauseShapes.isCatchAll, MatcherClauseShape.check,
    MatcherClause.header, MatcherClause.arms,
    MatcherArm.toHeader, MatcherArmHeader.check, MatcherArmHeader.canonical,
    armCoverageOK, armsCatchAllLast, finalCatchAllVariableArm, rootCoverageOK,
    MatcherTyping.DPat.isIrrefutable, MatcherArm.header,
    MatcherTyping.PPat.rootFormer?, PPat.shapeOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, HoleConvention.ofCount, DPat.shapeOK,
    Paper1FrozenSignature.signature, Paper1Signature.signature,
    Paper1Signature.patternConstructors, ListPatternSchemes.nil,
    ListPatternSchemes.cons, ListPatternSchemes.join]

theorem infer_identity_literal_exact :
    inferMatcherLiteral Paper1FrozenSignature.signature matcherContext
      identityLiteral = some (.matcher .any (.var ⟨1⟩)) := by
  unfold inferMatcherLiteral
  rw [matcher_context_initial_supply]
  simp only [elaborateMatcherLiteral, identity_literal_static_checks, if_true]
  simp [identityLiteral, identityClause, emptyList,
    elaborateMatcherClauses, elaborateMatcherClause,
    elaboratePPat, elaboratePPatFuel,
    elaboratePPatFields, elaboratePPatFieldsFuel,
    elaborateNextMatchers, elaborateCheckedExpression,
    elaborateMatcherArms, elaborateMatcherArm,
    elaborateDPat, elaborateDPatFuel,
    elaborateDPatFields, elaborateDPatFieldsFuel,
    GeneratedChecks.checked, GeneratedChecks.append, GeneratedChecks.empty,
    evidenceEquations, MatcherClause.toShape, MatcherClause.header,
    MatcherClause.nextMatchers, MatcherClause.arms, MatcherArm.toHeader,
    MatcherClauseShape.check, MatcherArmHeader.check,
    MatcherArmHeader.canonical, HoleConvention.ofCount, PPat.shapeOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, DPat.shapeOK,
    matcherContext, Pattern.extendContext, elaborate, elaborateItems,
    elaborateCall, Scheme.mono, Scheme.instantiate, Scheme.callArity,
    Scheme.callArity.go,
    Paper1FrozenSignature.lookup_data_nil, ConstructorSchemes.listNil,
    Paper1FrozenSignature.signature, Paper1Signature.signature,
    Paper1Signature.dataConstructors, FrozenSignature.lookupDataConstructor,
    Signature.lookupDataConstructor, ConstructorSchemes.boolTrue,
    ConstructorSchemes.boolFalse, ConstructorSchemes.listCons,
    DataCtor.true, DataCtor.false, DataCtor.nil, DataCtor.cons,
    PolyTy.openBound, PolyTy.openBoundList, PolyCap.openBound,
    PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list,
    holeProductTarget, Dual.targets, Supply.nextTy]
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  simp only [saturateLoop]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨2⟩))
          (.slot (.var ⟨2⟩) (.var ⟨1⟩)) =
        .matcherToSlot .any (.var ⟨2⟩) (.var ⟨2⟩) (.var ⟨1⟩) .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

theorem zero_hole_requires_unit :
    elaborateNextMatchers Paper1FrozenSignature.signature matcherContext
      (.lit 0) [] ⟨1, 1⟩ = none := by
  rfl

theorem two_holes_require_exact_tuple :
    elaborateNextMatchers Paper1FrozenSignature.signature matcherContext
      (.var 0)
      [⟨elementCapability, element⟩, ⟨listCapability, listElement⟩]
      ⟨1, 1⟩ = none := by
  rfl

theorem next_matcher_direction_equations_exact :
    (resolve (.matcher .any element) (.slot elementCapability element)).equations =
      [.cap .any elementCapability, .ty element element] := by
  rfl

theorem next_matcher_direction_rejected_after_header_solving :
    unify [.cap .any listCapability, .ty element element] = none := by
  unfold unify
  simp only [element, listCapability]
  compute_unification

theorem capture_before_hole_order_exact :
    valueConsHeader.captureSlots = [.capture 0] ∧
      valueConsHeader.holeCount = 1 := by
  simp [valueConsHeader, PPat.captureSlots, PPat.captureBindings,
    PPat.captureCount, PPat.holeCount]

def catchAllFirst : List MatcherClause :=
  catchAllClause :: multisetClauses

theorem catch_all_order_rejected :
    elaborateMatcherLiteral Paper1FrozenSignature.signature matcherContext
      catchAllFirst matcherContext.initialSupply = none := by
  rfl

def missingJoinCoverage : List MatcherClause :=
  [nilClause, headOnlyClause, valueConsClause, generalConsClause,
    wholeValueClause, catchAllClause]

theorem missing_general_constructor_coverage_rejected :
    rootCoverageOK Paper1FrozenSignature.signature missingJoinCoverage = false := by
  simp [rootCoverageOK, missingJoinCoverage, nilClause, headOnlyClause,
    valueConsClause, generalConsClause, wholeValueClause, catchAllClause,
    Paper1Programs.nilClause, Paper1Programs.headOnlyClause,
    Paper1Programs.valueConsClause, Paper1Programs.generalConsClause,
    Paper1Programs.wholeValueClause, Paper1Programs.catchAllClause,
    MatcherTyping.PPat.rootFormer?, MatcherTyping.PPat.isGeneralConstructor,
    MatcherClause.header, nilHeader, headOnlyHeader, valueConsHeader,
    generalConsHeader, wholeValueHeader, catchAllHeader,
    Paper1FrozenSignature.signature, Paper1Signature.signature,
    Paper1Signature.patternConstructors, FrozenSignature.lookupPatternConstructor,
    Signature.lookupPatternConstructor, ListPatternSchemes.nil,
    ListPatternSchemes.cons, ListPatternSchemes.join,
    PatternCtor.nil, PatternCtor.cons, PatternCtor.join, PatternFormer.list]

def nonExhaustiveJoin : MatcherClause :=
  .mk joinHeader (.tuple [.var 1, .var 1])
    [.mk (.ctor DataCtor.nil []) emptyList]

def nonExhaustiveArms : List MatcherClause :=
  [nilClause, headOnlyClause, valueConsClause, generalConsClause,
    nonExhaustiveJoin, wholeValueClause, catchAllClause]

theorem nonexhaustive_data_arms_rejected :
    armCoverageOK Paper1FrozenSignature.signature nonExhaustiveJoin.arms =
      false := by
  simp [nonExhaustiveJoin, armCoverageOK, armsCatchAllLast,
    MatcherClause.arms, MatcherArm.header,
    MatcherTyping.DPat.rootDataFormer?,
    MatcherTyping.DPat.isGeneralConstructor, MatcherTyping.DPat.isIrrefutable,
    Paper1FrozenSignature.signature, Paper1Signature.signature,
    Paper1Signature.dataConstructors, FrozenSignature.lookupDataConstructor,
    Signature.lookupDataConstructor, Signature.constructorResult?,
    ConstructorSchemes.listNil, ConstructorSchemes.listCons,
    ConstructorSchemes.boolTrue, ConstructorSchemes.boolFalse,
    PolyDataTypes.list, PolyDataTypes.bool, DataCtor.true, DataCtor.false,
    DataCtor.nil, DataCtor.cons, DataFormer.bool, DataFormer.list] <;> decide

theorem arm_body_must_return_decomposition_products :
    unify [.ty .int (DataTypes.list (.prod [element, listElement]))] = none := by
  unfold unify
  simp only [element, listElement, DataTypes.list]
  compute_unification

end TypePM.Source.M4MatcherTypingRegression
