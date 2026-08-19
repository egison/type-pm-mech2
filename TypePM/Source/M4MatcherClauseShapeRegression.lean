import TypePM.Source.MatcherClauseShape
import TypePM.Source.M4MatcherPatternRegression

/-!
# M4 matcher-clause structure regressions

The structures below attach ordered data-pattern arm headers to the seven
multiset pattern-pattern headers.  They do not attach source expressions or
claim that the operational matcher clauses have been implemented.
-/

namespace TypePM.Source.M4MatcherClauseShapeRegression

open M4MatcherPatternRegression

def nilArm : MatcherArmHeader :=
  MatcherArmHeader.canonical (.ctor DataCtor.nil [])

def consArm : MatcherArmHeader :=
  MatcherArmHeader.canonical (.ctor DataCtor.cons [.var, .var])

def tupleListArm : MatcherArmHeader :=
  MatcherArmHeader.canonical
    (.tuple [.var, .ctor DataCtor.cons [.var, .var]])

def variableArm : MatcherArmHeader :=
  MatcherArmHeader.canonical .var

def wildcardArm : MatcherArmHeader :=
  MatcherArmHeader.canonical .wild

def nilClause : MatcherClauseShape :=
  { header := nilHeader
    holeConvention := .zero
    arms := [nilArm, wildcardArm] }

def headOnlyClause : MatcherClauseShape :=
  { header := headOnlyHeader
    holeConvention := .one
    arms := [consArm, wildcardArm] }

def valueConsClause : MatcherClauseShape :=
  { header := valueConsHeader
    holeConvention := .one
    arms := [tupleListArm, wildcardArm] }

def generalConsClause : MatcherClauseShape :=
  { header := generalConsHeader
    holeConvention := .multiple 2
    arms := [consArm, wildcardArm] }

def joinClause : MatcherClauseShape :=
  { header := joinHeader
    holeConvention := .multiple 2
    arms := [nilArm, consArm, wildcardArm] }

def wholeValueClause : MatcherClauseShape :=
  { header := wholeValueHeader
    holeConvention := .zero
    arms := [variableArm] }

def catchAllClause : MatcherClauseShape :=
  { header := catchAllHeader
    holeConvention := .one
    arms := [variableArm] }

def multisetClauses : List MatcherClauseShape :=
  [ nilClause, headOnlyClause, valueConsClause, generalConsClause,
    joinClause, wholeValueClause, catchAllClause ]

theorem hole_conventions_zero_one_k_exact :
    nilClause.holeConvention = .zero ∧
      headOnlyClause.holeConvention = .one ∧
      generalConsClause.holeConvention = .multiple 2 := by
  exact ⟨rfl, rfl, rfl⟩

theorem all_seven_clause_shapes_checked :
    MatcherClauseShapes.check Paper1FrozenSignature.signature
      multisetClauses = true := by
  simp [MatcherClauseShapes.check, MatcherClauseShapes.catchAllLast,
    MatcherClauseShapes.isCatchAll, MatcherClauseShape.check,
    multisetClauses, nilClause, headOnlyClause, valueConsClause,
    generalConsClause, joinClause, wholeValueClause, catchAllClause,
    nilArm, consArm, tupleListArm, variableArm, wildcardArm,
    HoleConvention.ofCount, nilHeader, headOnlyHeader, valueConsHeader,
    generalConsHeader, joinHeader, wholeValueHeader, catchAllHeader,
    PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
    PPat.captureBeforeFirstHoleFrom, PPat.occurrences, PPat.holeCount,
    DPat.shapeOK, DPat.shapesOK, DPat.constructorArity?,
    ListPatternSchemes.nil, ListPatternSchemes.cons,
    ListPatternSchemes.join, ConstructorSchemes.listNil,
    ConstructorSchemes.listCons, PolyDataTypes.list]

theorem all_seven_headers_exact :
    multisetClauses.map MatcherClauseShape.header =
      [ nilHeader, headOnlyHeader, valueConsHeader, generalConsHeader,
        joinHeader, wholeValueHeader, catchAllHeader ] := by
  rfl

theorem all_seven_arm_counts_exact :
    multisetClauses.map (fun clause => clause.arms.length) =
      [2, 2, 2, 2, 3, 1, 1] := by
  rfl

theorem value_cons_arm_order_exact :
    valueConsClause.arms = [tupleListArm, wildcardArm] := by
  rfl

theorem join_arm_order_exact :
    joinClause.arms = [nilArm, consArm, wildcardArm] := by
  rfl

theorem all_checked_arm_slots_linear_and_disjoint :
    ∀ clause ∈ multisetClauses, ∀ arm ∈ clause.arms,
      arm.bindingSlots.Nodup ∧
        (∀ slot ∈ clause.header.captureSlots,
          slot ∉ arm.bindingSlots) := by
  intro clause clauseMember arm armMember
  have clausesChecked :
      multisetClauses.all
        (MatcherClauseShape.check Paper1FrozenSignature.signature) = true := by
    have checked := all_seven_clause_shapes_checked
    simp only [MatcherClauseShapes.check, Bool.and_eq_true] at checked
    exact checked.2
  have clauseChecked :
      clause.check Paper1FrozenSignature.signature = true :=
    (List.all_eq_true.mp clausesChecked) clause clauseMember
  exact
    ⟨clause.arm_bindingSlots_nodup clauseChecked armMember,
      clause.capture_arm_bindingSlots_disjoint arm⟩

def catchAllNotLast : List MatcherClauseShape :=
  [catchAllClause, nilClause]

theorem catch_all_not_last_rejected :
    MatcherClauseShapes.check Paper1FrozenSignature.signature
      catchAllNotLast = false := by
  rfl

def badPatternArityClause : MatcherClauseShape :=
  { header := badPatternConstructorArity
    holeConvention := .one
    arms := [variableArm] }

def badDataArityArm : MatcherArmHeader :=
  MatcherArmHeader.canonical badDataConstructorArity

def badDataArityClause : MatcherClauseShape :=
  { header := catchAllHeader
    holeConvention := .one
    arms := [badDataArityArm] }

theorem bad_arities_rejected :
    badPatternArityClause.check Paper1FrozenSignature.signature = false ∧
      badDataArityClause.check Paper1FrozenSignature.signature = false := by
  simp [MatcherClauseShape.check, badPatternArityClause,
    badDataArityClause, badDataArityArm, variableArm,
    MatcherArmHeader.check, MatcherArmHeader.canonical,
    badPatternConstructorArity, badDataConstructorArity,
    catchAllHeader, PPat.shapeOK, PPat.shapesOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, HoleConvention.ofCount,
    DPat.shapeOK, DPat.shapesOK, DPat.constructorArity?,
    ListPatternSchemes.cons, ConstructorSchemes.listCons,
    PolyDataTypes.list]

def duplicateBindingArm : MatcherArmHeader :=
  { pattern := .ctor DataCtor.cons [.var, .var]
    bindingOrder := [0, 0] }

def duplicateBindingClause : MatcherClauseShape :=
  { header := catchAllHeader
    holeConvention := .one
    arms := [duplicateBindingArm] }

theorem duplicate_binding_slots_rejected :
    duplicateBindingClause.check Paper1FrozenSignature.signature = false := by
  have rangeTwo : List.range 2 = [0, 1] := by decide
  simp [MatcherClauseShape.check, duplicateBindingClause,
    duplicateBindingArm, catchAllHeader, PPat.shapeOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, MatcherArmHeader.check,
    DPat.shapeOK, DPat.shapesOK, DPat.constructorArity?,
    DPat.bindingsInSourceOrder, DPat.bindingCount, rangeTwo,
    ConstructorSchemes.listCons, PolyDataTypes.list]

def wrongHoleConventionClause : MatcherClauseShape :=
  { header := generalConsHeader
    holeConvention := .one
    arms := [consArm] }

theorem wrong_hole_convention_rejected :
    wrongHoleConventionClause.check Paper1FrozenSignature.signature = false := by
  simp [MatcherClauseShape.check, wrongHoleConventionClause,
    generalConsHeader, PPat.shapeOK, PPat.shapesOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, HoleConvention.ofCount]

end TypePM.Source.M4MatcherClauseShapeRegression
