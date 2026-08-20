import TypePM.Source.M4RecursiveMatcherTotalBridge

/-!
# Regression for the fuel-indexed M4 matcher-literal bridge

The final catch-all clause delegates its one hole to `something` and returns
an empty decomposition list.  Both stored expressions are elaborated through
the recursive `M4.ElaboratesFuel` callback, not the older M3 matcher relation.
-/

namespace TypePM.Source.MatcherTyping.M4RecursiveMatcherTotalBridgeRegression

open TypePM.Runtime

def clause : MatcherClause :=
  .mk .hole .something [.mk .var (.ctor DataCtor.nil [])]

def matcherGenerated : Generated :=
  { target := .matcher (.var ⟨0⟩) (.var ⟨0⟩)
    hard := [.cap (.var ⟨0⟩) .any]
    pending := [
      ⟨.matcher .any (.var ⟨1⟩), .slot (.var ⟨1⟩) (.var ⟨0⟩)⟩,
      ⟨DataTypes.list (.var ⟨2⟩), DataTypes.list (.var ⟨0⟩)⟩] }

def solved : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

theorem clause_staticChecks :
    StaticChecksHold Paper1FrozenSignature.signature [clause] := by
  apply (staticChecksHold_iff Paper1FrozenSignature.signature [clause]).2
  simp [staticChecks, clause,
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

theorem matcher_m4FuelElaborates :
    MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature 9)
      PPatElaborates DPatElaborates Paper1FrozenSignature.signature [] [clause]
      ⟨0, 0⟩ matcherGenerated ⟨3, 2⟩ := by
  unfold clause matcherGenerated
  let nextObligation : CheckObligation :=
    ⟨.matcher .any (.var ⟨1⟩), .slot (.var ⟨1⟩) (.var ⟨0⟩)⟩
  let bodyObligation : CheckObligation :=
    ⟨DataTypes.list (.var ⟨2⟩), DataTypes.list (.var ⟨0⟩)⟩
  refine MatcherLiteralElaboratesUsing.mk
    (generatedClauses := ⟨[], ⟨[], [nextObligation, bodyObligation]⟩⟩)
    (by simpa [clause] using clause_staticChecks) ?_
  refine MatcherClausesElaborateUsing.cons
    (generatedClause :=
      ⟨[⟨Cap.var ⟨1⟩, Ty.var ⟨0⟩⟩], none,
        ⟨[], [nextObligation, bodyObligation]⟩⟩)
    (generatedClauses := ⟨[], GeneratedChecks.empty⟩) ?_ .nil
  refine MatcherClauseElaboratesUsing.mk
    (generatedHeader := ⟨[⟨Cap.var ⟨1⟩, Ty.var ⟨0⟩⟩], [], none, []⟩)
    (generatedNext := ⟨[], [nextObligation]⟩)
    (afterNext := ⟨2, 2⟩)
    (generatedArms := ⟨⟨[], [bodyObligation]⟩⟩)
    (MatcherClauseShape.wellFormed_of_check (by
      simp [MatcherClause.toShape, MatcherClauseShape.check,
        MatcherArm.toHeader, MatcherArmHeader.check, MatcherArmHeader.canonical,
        PPat.shapeOK, PPat.captureBeforeFirstHole,
        PPat.captureBeforeFirstHoleFrom, PPat.occurrences, PPat.holeCount,
        HoleConvention.ofCount, DPat.shapeOK])) PPatElaborates.hole
    (.one (CheckedExpressionElaboratesUsing.mk
      (generated := ⟨.matcher .any (.var ⟨1⟩), [], []⟩)
      (next := ⟨2, 2⟩) ?_)) ?_
  · simp [M4.ElaboratesFuel, Supply.nextTy]
  · refine MatcherArmsElaborateUsing.cons
      (generatedArm := ⟨[], [bodyObligation]⟩)
      (generatedArms := ⟨GeneratedChecks.empty⟩) ?_ .nil
    refine MatcherArmElaboratesUsing.mk
      (generatedHeader := ⟨[Ty.var ⟨0⟩], []⟩)
      (generatedBody := ⟨[], [bodyObligation]⟩)
      DPatElaborates.var
      (CheckedExpressionElaboratesUsing.mk
        (generated := ⟨DataTypes.list (.var ⟨2⟩), [], []⟩)
        (next := ⟨3, 2⟩) ?_)
    change ∃ scheme,
      Paper1FrozenSignature.signature.lookupDataConstructor DataCtor.nil =
          some scheme ∧
        [].length = scheme.callArity ∧ scheme.Closed ∧
        M4.CallElaboratesUsing
          (M4.ElaboratesFuel Paper1FrozenSignature.signature 8)
          [Scheme.mono (Ty.var ⟨0⟩)]
          ⟨(scheme.instantiate ⟨2, 2⟩).1, [], []⟩ []
          (scheme.instantiate ⟨2, 2⟩).2
          ⟨DataTypes.list (Ty.var ⟨2⟩), [], []⟩ ⟨3, 2⟩
    refine ⟨ConstructorSchemes.listNil,
      Paper1FrozenSignature.lookup_data_nil, rfl,
      Paper1FrozenSignature.wellFormed.baseWellFormed
        |>.dataConstructorClosed_of_lookup
          Paper1FrozenSignature.lookup_data_nil, ?_⟩
    simpa only [ConstructorSchemes.instantiate_listNil] using
      (M4.CallElaboratesUsing.nil :
        M4.CallElaboratesUsing
          (M4.ElaboratesFuel Paper1FrozenSignature.signature 8)
          [Scheme.mono (Ty.var ⟨0⟩)]
          ⟨DataTypes.list (Ty.var ⟨2⟩), [], []⟩ [] ⟨3, 2⟩
          ⟨DataTypes.list (Ty.var ⟨2⟩), [], []⟩ ⟨3, 2⟩)

theorem matcher_semantic :
    matcherGenerated.SemanticSolution solved := by
  constructor
  · simp [matcherGenerated, solved, Solves, Equation.Holds, Cap.apply]
  · intro obligation member
    simp [matcherGenerated] at member
    rcases member with rfl | rfl
    · exact ⟨.matcherToSlot, by
        simpa [solved, Ty.apply, Cap.apply] using
          (CheckConversion.matcherToSlot CapabilityDemand.equal :
            CheckConversion .matcherToSlot (.matcher .any .int)
              (.slot .any .int))⟩
    · exact ⟨.ordinary, by
        simpa [solved, Ty.apply, Ty.applyList, DataTypes.list] using
          (CheckConversion.ordinary :
            CheckConversion .ordinary (DataTypes.list .int)
              (DataTypes.list .int))⟩

theorem clause_runtimeSupported :
    MatcherClausesRuntimeExpressionsSupported [clause] := by
  exact .cons (.mk .something (.cons .listNil .nil)) .nil

theorem matcher_totalCoreTyping :
    TotalCoreTyping (.matcher [clause]) (.matcher .any .int) [] := by
  simpa [solved, Ty.apply] using
    matcher_m4FuelElaborates.toTotalCoreTyping_of_m4Fuel
      clause_runtimeSupported matcher_semantic
      MonomorphicContextCompatible.nil

theorem matcher_neverStuck (fuel : Nat) :
    (evalFuel fuel [] (.matcher [clause])).NotStuck :=
  matcher_totalCoreTyping.neverStuck fuel [] .nil

end TypePM.Source.MatcherTyping.M4RecursiveMatcherTotalBridgeRegression
