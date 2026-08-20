import TypePM.Source.M4Paper1ComputabilityRegression
import TypePM.Source.M4ElaborationFuelTransport

/-!
# Exact kernel regression for the Paper 1 `list` matcher

The complete matcher-clause traversal is deliberately assembled from small
executable equations.  This keeps kernel reduction local to one header,
next-matcher expression, or arm body at a time.
-/

namespace TypePM.Source.M4Paper1ListExactRegression

open Paper1Programs
open MatcherTyping

set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private def callback : ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 200)
    Paper1FrozenSignature.signature 128

private def fixContext : Context :=
  [.mono (.slot (.var ⟨0⟩) (.var ⟨0⟩)),
    .mono (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
      (.matcher (.var ⟨1⟩) (.var ⟨1⟩)))]

private def nilHeader : GeneratedPPat :=
  { holes := []
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨3⟩])
    hard := [.ty (DataTypes.list (.var ⟨3⟩)) (.var ⟨2⟩)] }

private theorem nil_header_exact :
    elaboratePPat Paper1FrozenSignature.signature
      listMatcherNilClause.header (.var ⟨2⟩) none ⟨3, 3⟩ =
      some (nilHeader, ⟨4, 4⟩) := by
  simp [nilHeader, listMatcherNilClause, Paper1Programs.nilClause,
    elaboratePPat, elaboratePPatFuel, elaboratePPatFieldsFuel,
    PPat.typingSize, PPat.listTypingSize,
    Paper1FrozenSignature.lookup_pattern_nil, ListPatternSchemes.nil,
    DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
    PolyCap.openBoundList, PolyTy.openBound, PolyTy.openBoundList,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    PolyDataTypes.list, DataTypes.list]

private def nilNext : GeneratedChecks :=
  { hard := []
    pending := [⟨.prod [], .prod []⟩] }

private theorem callback_empty_tuple_exact :
    callback fixContext (.tuple []) ⟨4, 4⟩ =
      some (⟨.prod [], [], []⟩, ⟨4, 4⟩) := by
  unfold callback
  rw [M4.elaborateFuelUsing.eq_def]
  rfl

private theorem nil_next_exact :
    elaborateNextMatchersUsing callback fixContext
      listMatcherNilClause.nextMatchers [] ⟨4, 4⟩ =
      some (nilNext, ⟨4, 4⟩) := by
  simp only [listMatcherNilClause, Paper1Programs.nilClause,
    MatcherClause.nextMatchers, elaborateNextMatchersUsing,
    elaborateCheckedExpressionUsing]
  rw [callback_empty_tuple_exact]
  rfl

private def nilFirstDPat : GeneratedDPat :=
  { bindings := []
    hard := [.ty (DataTypes.list (.var ⟨4⟩)) (.var ⟨2⟩)] }

private theorem nil_first_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature (.ctor DataCtor.nil [])
      (.var ⟨2⟩) ⟨4, 4⟩ = some (nilFirstDPat, ⟨5, 4⟩) := by
  simp [nilFirstDPat, elaborateDPat, elaborateDPatFuel,
    elaborateDPatFieldsFuel, DPat.typingSize, DPat.listTypingSize,
    peelFunctionExact, Paper1FrozenSignature.lookup_data_nil,
    ConstructorSchemes.listNil, Scheme.instantiate, Scheme.callArity,
    Scheme.callArity.go, PolyTy.openBound, PolyTy.openBoundList,
    PolyCap.openBound, PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list]

private def nilFirstBody : Generated :=
  { target := .var ⟨10⟩
    hard :=
      [.ty
        (.fn (.var ⟨5⟩)
          (.fn (DataTypes.list (.var ⟨5⟩))
            (DataTypes.list (.var ⟨5⟩))))
        (.fn (.var ⟨6⟩) (.var ⟨7⟩)),
       .ty (.var ⟨7⟩) (.fn (.var ⟨9⟩) (.var ⟨10⟩))]
    pending :=
      [⟨.prod [], .var ⟨6⟩⟩,
       ⟨DataTypes.list (.var ⟨8⟩), .var ⟨9⟩⟩] }

private theorem nil_first_body_exact :
    callback fixContext (sourceList [Paper1Programs.unit]) ⟨5, 4⟩ =
      some (nilFirstBody, ⟨11, 4⟩) := by
  unfold callback
  rw [M4.elaborateFuelUsing.eq_def]
  simp [nilFirstBody, fixContext, Paper1Programs.sourceList,
    Paper1Programs.unit, M4.elaborateFuelUsing, M4.elaborateCallUsing,
    M4.elaborateItemsUsing, Paper1FrozenSignature.lookup_data_nil,
    Paper1FrozenSignature.lookup_data_cons,
    ConstructorSchemes.listNil, ConstructorSchemes.listCons,
    Paper1FrozenSignature.signature, Paper1Signature.signature,
    Paper1Signature.dataConstructors, FrozenSignature.lookupDataConstructor,
    Signature.lookupDataConstructor, ConstructorSchemes.boolTrue,
    ConstructorSchemes.boolFalse, DataCtor.true, DataCtor.false,
    DataCtor.nil, DataCtor.cons, DataFormer.bool, DataFormer.list,
    Scheme.instantiate, Scheme.callArity, Scheme.callArity.go,
    PolyTy.openBound, PolyTy.openBoundList, PolyCap.openBound,
    PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list,
    Generated.fromApp, Supply.nextTy]

private def nilFirstArm : GeneratedChecks :=
  { hard :=
      [.ty (DataTypes.list (.var ⟨4⟩)) (.var ⟨2⟩),
       .ty
         (.fn (.var ⟨5⟩)
           (.fn (DataTypes.list (.var ⟨5⟩))
             (DataTypes.list (.var ⟨5⟩))))
         (.fn (.var ⟨6⟩) (.var ⟨7⟩)),
       .ty (.var ⟨7⟩) (.fn (.var ⟨9⟩) (.var ⟨10⟩))]
    pending :=
      [⟨.prod [], .var ⟨6⟩⟩,
       ⟨DataTypes.list (.var ⟨8⟩), .var ⟨9⟩⟩,
       ⟨.var ⟨10⟩, DataTypes.list (.prod [])⟩] }

private theorem nil_first_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) []
      (.mk (.ctor DataCtor.nil []) (sourceList [Paper1Programs.unit]))
      ⟨4, 4⟩ = some (nilFirstArm, ⟨11, 4⟩) := by
  simp only [elaborateMatcherArmUsing, nil_first_dpat_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, nilFirstDPat,
    Pattern.extendContext,
    List.map_nil, List.nil_append, elaborateCheckedExpressionUsing]
  rw [nil_first_body_exact]
  rfl

private theorem nil_second_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature .wild (.var ⟨2⟩)
      ⟨11, 4⟩ = some (⟨[], []⟩, ⟨11, 4⟩) := by
  rfl

private def nilSecondBody : Generated :=
  { target := DataTypes.list (.var ⟨11⟩)
    hard := []
    pending := [] }

private theorem nil_second_body_exact :
    callback fixContext (sourceList []) ⟨11, 4⟩ =
      some (nilSecondBody, ⟨12, 4⟩) := by
  unfold callback
  rw [M4.elaborateFuelUsing.eq_def]
  simp [nilSecondBody, fixContext, Paper1Programs.sourceList,
    M4.elaborateFuelUsing, M4.elaborateCallUsing,
    Paper1FrozenSignature.lookup_data_nil, ConstructorSchemes.listNil,
    Paper1FrozenSignature.signature, Paper1Signature.signature,
    Paper1Signature.dataConstructors, FrozenSignature.lookupDataConstructor,
    Signature.lookupDataConstructor, ConstructorSchemes.boolTrue,
    ConstructorSchemes.boolFalse, DataCtor.true, DataCtor.false,
    DataCtor.nil, DataCtor.cons, DataFormer.bool, DataFormer.list,
    Scheme.instantiate, Scheme.callArity, Scheme.callArity.go,
    PolyTy.openBound, PolyTy.openBoundList, PolyCap.openBound,
    PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list,
    Supply.nextTy]

private def nilSecondArm : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨DataTypes.list (.var ⟨11⟩), DataTypes.list (.prod [])⟩] }

private theorem nil_second_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) []
      (.mk .wild (sourceList [])) ⟨11, 4⟩ =
      some (nilSecondArm, ⟨12, 4⟩) := by
  simp only [elaborateMatcherArmUsing, nil_second_dpat_exact]
  simp only [Option.bind_eq_bind, Option.bind_some,
    Pattern.extendContext, List.map_nil,
    List.nil_append, elaborateCheckedExpressionUsing]
  rw [nil_second_body_exact]
  rfl

private def nilArms : GeneratedArms :=
  ⟨nilFirstArm.append nilSecondArm⟩

private theorem nil_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) [] listMatcherNilClause.arms ⟨4, 4⟩ =
      some (nilArms, ⟨12, 4⟩) := by
  simp only [listMatcherNilClause, Paper1Programs.nilClause,
    MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [nil_first_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [nil_second_arm_exact]
  rfl

private def nilClause : GeneratedMatcherClause :=
  { holes := []
    evidence := nilHeader.evidence
    checks :=
      { hard := nilHeader.hard ++ nilNext.hard ++ nilArms.checks.hard
        pending := nilNext.pending ++ nilArms.checks.pending } }

theorem nil_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨2⟩) listMatcherNilClause ⟨3, 3⟩ =
      some (nilClause, ⟨12, 4⟩) := by
  have shape : listMatcherNilClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [listMatcherNilClause, Paper1Programs.nilClause,
      MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      ConstructorSchemes.listNil, ListPatternSchemes.nil,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [nil_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, nilHeader,
    Pattern.extendContext,
    List.map_nil, List.nil_append]
  rw [nil_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [nil_arms_exact]
  rfl

/-! ## The `cons` clause -/

private def consHoles : List Dual :=
  [⟨.var ⟨5⟩, .var ⟨12⟩⟩,
   ⟨.var ⟨6⟩, DataTypes.list (.var ⟨12⟩)⟩]

private def consHeader : GeneratedPPat :=
  { holes := consHoles
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨4⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨12⟩)) (.var ⟨2⟩),
       .cap (.var ⟨5⟩) (.var ⟨4⟩),
       .cap (.var ⟨6⟩) (.con PatternFormer.list [.var ⟨4⟩])] }

private theorem cons_header_exact :
    elaboratePPat Paper1FrozenSignature.signature
      listMatcherConsClause.header (.var ⟨2⟩) none ⟨12, 4⟩ =
      some (consHeader, ⟨13, 7⟩) := by
  simp [consHeader, consHoles, listMatcherConsClause, elaboratePPat,
    elaboratePPatFuel, elaboratePPatFieldsFuel,
    PPat.typingSize, PPat.listTypingSize,
    Paper1FrozenSignature.lookup_pattern_cons, ListPatternSchemes.cons,
    DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
    PolyCap.openBoundList, PolyTy.openBound, PolyTy.openBoundList,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    PolyDataTypes.list, DataTypes.list]

private def consNext : GeneratedChecks :=
  { hard :=
      [.ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨1⟩)))
        (.fn (.var ⟨13⟩) (.var ⟨14⟩))]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨0⟩),
        .slot (.var ⟨5⟩) (.var ⟨12⟩)⟩,
       ⟨.slot (.var ⟨0⟩) (.var ⟨0⟩), .var ⟨13⟩⟩,
       ⟨.var ⟨14⟩,
        .slot (.var ⟨6⟩) (DataTypes.list (.var ⟨12⟩))⟩] }

private def consNextFirst : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨0⟩),
        .slot (.var ⟨5⟩) (.var ⟨12⟩)⟩] }

private theorem cons_next_first_exact :
    elaborateCheckedExpressionUsing callback fixContext (.var 0)
      (.slot (.var ⟨5⟩) (.var ⟨12⟩)) ⟨13, 7⟩ =
      some (consNextFirst, ⟨13, 7⟩) := by
  unfold elaborateCheckedExpressionUsing callback
  rw [M4.elaborateFuelUsing.eq_def]
  simp [consNextFirst, fixContext, GeneratedChecks.checked,
    Scheme.mono, Scheme.instantiate]

private def consNextSecond : GeneratedChecks :=
  { hard := consNext.hard
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨0⟩), .var ⟨13⟩⟩,
       ⟨.var ⟨14⟩,
        .slot (.var ⟨6⟩) (DataTypes.list (.var ⟨12⟩))⟩] }

private theorem cons_next_second_exact :
    elaborateCheckedExpressionUsing callback fixContext
      (.app (.var 1) (.var 0))
      (.slot (.var ⟨6⟩) (DataTypes.list (.var ⟨12⟩)))
      ⟨13, 7⟩ = some (consNextSecond, ⟨15, 7⟩) := by
  unfold elaborateCheckedExpressionUsing callback
  rw [M4.elaborateFuelUsing.eq_def]
  simp [consNextSecond, consNext, fixContext, GeneratedChecks.checked,
    M4.elaborateFuelUsing, Generated.fromApp, Scheme.mono,
    Scheme.instantiate, DataTypes.list, Supply.nextTy]

private theorem cons_next_exact :
    elaborateNextMatchersUsing callback fixContext
      listMatcherConsClause.nextMatchers consHoles ⟨13, 7⟩ =
      some (consNext, ⟨15, 7⟩) := by
  simp only [listMatcherConsClause, MatcherClause.nextMatchers,
    elaborateNextMatchersUsing, consHoles,
    elaborateNextMatcherItemsUsing]
  rw [cons_next_first_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [cons_next_second_exact]
  rfl

private def consDPat : GeneratedDPat :=
  { bindings := [.var ⟨15⟩, DataTypes.list (.var ⟨15⟩)]
    hard := [.ty (DataTypes.list (.var ⟨15⟩)) (.var ⟨2⟩)] }

private theorem cons_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature
      (.ctor DataCtor.cons [.var, .var]) (.var ⟨2⟩) ⟨15, 7⟩ =
      some (consDPat, ⟨16, 7⟩) := by
  simp [consDPat, elaborateDPat, elaborateDPatFuel,
    elaborateDPatFieldsFuel, DPat.typingSize, DPat.listTypingSize,
    peelFunctionExact, Paper1FrozenSignature.lookup_data_cons,
    ConstructorSchemes.listCons, Scheme.instantiate, Scheme.callArity,
    Scheme.callArity.go, PolyTy.openBound, PolyTy.openBoundList,
    PolyCap.openBound, PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list]

private def consBody : Generated :=
  { target := .var ⟨21⟩
    hard :=
      [.ty
        (.fn (.var ⟨16⟩)
          (.fn (DataTypes.list (.var ⟨16⟩))
            (DataTypes.list (.var ⟨16⟩))))
        (.fn (.var ⟨17⟩) (.var ⟨18⟩)),
       .ty (.var ⟨18⟩) (.fn (.var ⟨20⟩) (.var ⟨21⟩))]
    pending :=
      [⟨.prod [.var ⟨15⟩, DataTypes.list (.var ⟨15⟩)],
        .var ⟨17⟩⟩,
       ⟨DataTypes.list (.var ⟨19⟩), .var ⟨20⟩⟩] }

private theorem cons_body_exact :
    callback
      (.mono (.var ⟨15⟩) ::
        .mono (DataTypes.list (.var ⟨15⟩)) :: fixContext)
      (sourceList [.tuple [.var 0, .var 1]])
      ⟨16, 7⟩ = some (consBody, ⟨22, 7⟩) := by
  unfold callback
  rw [M4.elaborateFuelUsing.eq_def]
  simp [consBody, fixContext, Paper1Programs.sourceList,
    M4.elaborateFuelUsing, M4.elaborateCallUsing,
    M4.elaborateItemsUsing, Generated.fromApp,
    Paper1FrozenSignature.lookup_data_nil,
    Paper1FrozenSignature.lookup_data_cons,
    ConstructorSchemes.listNil, ConstructorSchemes.listCons,
    Paper1FrozenSignature.signature, Paper1Signature.signature,
    Paper1Signature.dataConstructors, FrozenSignature.lookupDataConstructor,
    Signature.lookupDataConstructor, ConstructorSchemes.boolTrue,
    ConstructorSchemes.boolFalse, DataCtor.true, DataCtor.false,
    DataCtor.nil, DataCtor.cons, DataFormer.bool, DataFormer.list,
    Scheme.mono, Scheme.instantiate, Scheme.callArity, Scheme.callArity.go,
    PolyTy.openBound, PolyTy.openBoundList, PolyCap.openBound,
    PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list,
    Supply.nextTy]

private def consArm : GeneratedChecks :=
  { hard := consDPat.hard ++ consBody.hard
    pending := consBody.pending ++
      [⟨consBody.target,
        DataTypes.list (.prod [.var ⟨12⟩,
          DataTypes.list (.var ⟨12⟩)])⟩] }

private theorem cons_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) consHoles
      (.mk (.ctor DataCtor.cons [.var, .var])
        (sourceList [.tuple [.var 0, .var 1]])) ⟨15, 7⟩ =
      some (consArm, ⟨22, 7⟩) := by
  simp only [elaborateMatcherArmUsing, cons_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, consDPat,
    Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, elaborateCheckedExpressionUsing]
  rw [cons_body_exact]
  rfl

private def consArms : GeneratedArms :=
  ⟨consArm.append GeneratedChecks.empty⟩

private theorem cons_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) consHoles
      listMatcherConsClause.arms ⟨15, 7⟩ =
      some (consArms, ⟨22, 7⟩) := by
  simp only [listMatcherConsClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [cons_arm_exact]
  rfl

private def consClause : GeneratedMatcherClause :=
  { holes := consHoles
    evidence := consHeader.evidence
    checks :=
      { hard := consHeader.hard ++ consNext.hard ++ consArms.checks.hard
        pending := consNext.pending ++ consArms.checks.pending } }

theorem cons_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨2⟩) listMatcherConsClause ⟨12, 4⟩ =
      some (consClause, ⟨22, 7⟩) := by
  have shape : listMatcherConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [listMatcherConsClause, MatcherClause.toShape,
      MatcherArm.toHeader, MatcherClauseShape.check,
      MatcherArmHeader.check, MatcherArmHeader.canonical,
      HoleConvention.ofCount, PPat.shapeOK, PPat.shapesOK,
      PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
      PPat.occurrences, PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_cons,
      ConstructorSchemes.listCons, ListPatternSchemes.cons,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [cons_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, consHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [cons_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [cons_arms_exact]
  rfl

/-! ## The `join` clause -/

private def joinHoles : List Dual :=
  [⟨.var ⟨8⟩, DataTypes.list (.var ⟨22⟩)⟩,
   ⟨.var ⟨9⟩, DataTypes.list (.var ⟨22⟩)⟩]

private def joinHeader : GeneratedPPat :=
  { holes := joinHoles
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨7⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨22⟩)) (.var ⟨2⟩),
       .cap (.var ⟨8⟩) (.con PatternFormer.list [.var ⟨7⟩]),
       .cap (.var ⟨9⟩) (.con PatternFormer.list [.var ⟨7⟩])] }

private theorem join_header_exact :
    elaboratePPat Paper1FrozenSignature.signature
      listMatcherJoinClause.header (.var ⟨2⟩) none ⟨22, 7⟩ =
      some (joinHeader, ⟨23, 10⟩) := by
  simp [joinHeader, joinHoles, listMatcherJoinClause, elaboratePPat,
    elaboratePPatFuel, elaboratePPatFieldsFuel,
    PPat.typingSize, PPat.listTypingSize,
    Paper1FrozenSignature.lookup_pattern_join, ListPatternSchemes.join,
    DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
    PolyCap.openBoundList, PolyTy.openBound, PolyTy.openBoundList,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    PolyDataTypes.list, DataTypes.list]

private def joinNextFirst : GeneratedChecks :=
  { hard :=
      [.ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨1⟩)))
        (.fn (.var ⟨23⟩) (.var ⟨24⟩))]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨0⟩), .var ⟨23⟩⟩,
       ⟨.var ⟨24⟩,
        .slot (.var ⟨8⟩) (DataTypes.list (.var ⟨22⟩))⟩] }

private theorem join_next_first_exact :
    elaborateCheckedExpressionUsing callback fixContext
      (.app (.var 1) (.var 0))
      (.slot (.var ⟨8⟩) (DataTypes.list (.var ⟨22⟩)))
      ⟨23, 10⟩ = some (joinNextFirst, ⟨25, 10⟩) := by
  unfold elaborateCheckedExpressionUsing callback
  rw [M4.elaborateFuelUsing.eq_def]
  simp [joinNextFirst, fixContext, GeneratedChecks.checked,
    M4.elaborateFuelUsing, Generated.fromApp, Scheme.mono,
    Scheme.instantiate, DataTypes.list, Supply.nextTy]

private def joinNextSecond : GeneratedChecks :=
  { hard :=
      [.ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨1⟩)))
        (.fn (.var ⟨25⟩) (.var ⟨26⟩))]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨0⟩), .var ⟨25⟩⟩,
       ⟨.var ⟨26⟩,
        .slot (.var ⟨9⟩) (DataTypes.list (.var ⟨22⟩))⟩] }

private theorem join_next_second_exact :
    elaborateCheckedExpressionUsing callback fixContext
      (.app (.var 1) (.var 0))
      (.slot (.var ⟨9⟩) (DataTypes.list (.var ⟨22⟩)))
      ⟨25, 10⟩ = some (joinNextSecond, ⟨27, 10⟩) := by
  unfold elaborateCheckedExpressionUsing callback
  rw [M4.elaborateFuelUsing.eq_def]
  simp [joinNextSecond, fixContext, GeneratedChecks.checked,
    M4.elaborateFuelUsing, Generated.fromApp, Scheme.mono,
    Scheme.instantiate, DataTypes.list, Supply.nextTy]

private def joinNext : GeneratedChecks :=
  joinNextFirst.append joinNextSecond

private theorem join_next_exact :
    elaborateNextMatchersUsing callback fixContext
      listMatcherJoinClause.nextMatchers joinHoles ⟨23, 10⟩ =
      some (joinNext, ⟨27, 10⟩) := by
  simp only [listMatcherJoinClause, MatcherClause.nextMatchers,
    elaborateNextMatchersUsing, joinHoles,
    elaborateNextMatcherItemsUsing]
  rw [join_next_first_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [join_next_second_exact]
  rfl

private def joinNilDPat : GeneratedDPat :=
  { bindings := []
    hard := [.ty (DataTypes.list (.var ⟨27⟩)) (.var ⟨2⟩)] }

private theorem join_nil_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature (.ctor DataCtor.nil [])
      (.var ⟨2⟩) ⟨27, 10⟩ = some (joinNilDPat, ⟨28, 10⟩) := by
  simp [joinNilDPat, elaborateDPat, elaborateDPatFuel,
    elaborateDPatFieldsFuel, DPat.typingSize, DPat.listTypingSize,
    peelFunctionExact, Paper1FrozenSignature.lookup_data_nil,
    ConstructorSchemes.listNil, Scheme.instantiate, Scheme.callArity,
    Scheme.callArity.go, PolyTy.openBound, PolyTy.openBoundList,
    PolyCap.openBound, PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list]

private def joinNilBody : Generated :=
  { target := .var ⟨35⟩
    hard :=
      [.ty
        (.fn (.var ⟨28⟩)
          (.fn (DataTypes.list (.var ⟨28⟩))
            (DataTypes.list (.var ⟨28⟩))))
        (.fn (.var ⟨31⟩) (.var ⟨32⟩)),
       .ty (.var ⟨32⟩) (.fn (.var ⟨34⟩) (.var ⟨35⟩))]
    pending :=
      [⟨.prod [DataTypes.list (.var ⟨29⟩),
          DataTypes.list (.var ⟨30⟩)], .var ⟨31⟩⟩,
       ⟨DataTypes.list (.var ⟨33⟩), .var ⟨34⟩⟩] }

private theorem join_nil_body_exact :
    callback fixContext
      (sourceList [.tuple [sourceList [], sourceList []]]) ⟨28, 10⟩ =
      some (joinNilBody, ⟨36, 10⟩) := by
  unfold callback
  rw [M4.elaborateFuelUsing.eq_def]
  simp [joinNilBody, fixContext, Paper1Programs.sourceList,
    M4.elaborateFuelUsing, M4.elaborateCallUsing,
    M4.elaborateItemsUsing, Generated.fromApp,
    Paper1FrozenSignature.lookup_data_nil,
    Paper1FrozenSignature.lookup_data_cons,
    ConstructorSchemes.listNil, ConstructorSchemes.listCons,
    Paper1FrozenSignature.signature, Paper1Signature.signature,
    Paper1Signature.dataConstructors, FrozenSignature.lookupDataConstructor,
    Signature.lookupDataConstructor, ConstructorSchemes.boolTrue,
    ConstructorSchemes.boolFalse, DataCtor.true, DataCtor.false,
    DataCtor.nil, DataCtor.cons, DataFormer.bool, DataFormer.list,
    Scheme.mono, Scheme.instantiate, Scheme.callArity,
    Scheme.callArity.go, PolyTy.openBound, PolyTy.openBoundList,
    PolyCap.openBound, PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list,
    Supply.nextTy]

private def joinNilArm : GeneratedChecks :=
  { hard := joinNilDPat.hard ++ joinNilBody.hard
    pending := joinNilBody.pending ++
      [⟨joinNilBody.target,
        DataTypes.list
          (.prod [DataTypes.list (.var ⟨22⟩),
            DataTypes.list (.var ⟨22⟩)])⟩] }

private theorem join_nil_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) joinHoles
      (.mk (.ctor DataCtor.nil [])
        (sourceList [.tuple [sourceList [], sourceList []]])) ⟨27, 10⟩ =
      some (joinNilArm, ⟨36, 10⟩) := by
  simp only [elaborateMatcherArmUsing, join_nil_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, joinNilDPat,
    Pattern.extendContext, List.map_nil, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [join_nil_body_exact]
  rfl

private def joinConsDPat : GeneratedDPat :=
  { bindings := [.var ⟨36⟩, DataTypes.list (.var ⟨36⟩)]
    hard := [.ty (DataTypes.list (.var ⟨36⟩)) (.var ⟨2⟩)] }

private theorem join_cons_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature
      (.ctor DataCtor.cons [.var, .var]) (.var ⟨2⟩) ⟨36, 10⟩ =
      some (joinConsDPat, ⟨37, 10⟩) := by
  simp [joinConsDPat, elaborateDPat, elaborateDPatFuel,
    elaborateDPatFieldsFuel, DPat.typingSize, DPat.listTypingSize,
    peelFunctionExact, Paper1FrozenSignature.lookup_data_cons,
    ConstructorSchemes.listCons, Scheme.instantiate, Scheme.callArity,
    Scheme.callArity.go, PolyTy.openBound, PolyTy.openBoundList,
    PolyCap.openBound, PolyCap.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list]

private def joinConsBody : Generated :=
  { target := .var ⟨74⟩
    hard :=
      [.ty (.var ⟨36⟩) (.var ⟨36⟩),
       .ty (.var ⟨0⟩) (.var ⟨0⟩),
       .ty (.var ⟨1⟩) (DataTypes.list (.var ⟨36⟩)),
       .cap (.var ⟨0⟩) (.var ⟨0⟩),
       .cap (.var ⟨1⟩) (.con PatternFormer.list [.var ⟨10⟩]),
       .ty
         (.fn (.var ⟨45⟩)
           (.fn (DataTypes.list (.var ⟨45⟩))
             (DataTypes.list (.var ⟨45⟩))))
         (.fn (.var ⟨46⟩) (.var ⟨47⟩)),
       .ty (.var ⟨47⟩) (.fn (.var ⟨48⟩) (.var ⟨49⟩)),
       .ty
         (.fn (.var ⟨43⟩)
           (.fn (DataTypes.list (.var ⟨43⟩))
             (DataTypes.list (.var ⟨43⟩))))
         (.fn (.var ⟨50⟩) (.var ⟨51⟩)),
       .ty (.var ⟨51⟩) (.fn (.var ⟨53⟩) (.var ⟨54⟩)),
       .ty
         (.fn (DataTypes.list (.var ⟨42⟩))
           (.fn (DataTypes.list (.var ⟨42⟩))
             (DataTypes.list (.var ⟨42⟩))))
         (.fn (.var ⟨55⟩) (.var ⟨56⟩)),
       .ty (.prod [.var ⟨62⟩, .var ⟨63⟩]) (.var ⟨59⟩),
       .ty
         (.fn (.var ⟨64⟩)
           (.fn (DataTypes.list (.var ⟨64⟩))
             (DataTypes.list (.var ⟨64⟩))))
         (.fn (.var ⟨65⟩) (.var ⟨66⟩)),
       .ty (.var ⟨66⟩) (.fn (.var ⟨67⟩) (.var ⟨68⟩)),
       .ty
         (.fn (.fn (.var ⟨57⟩) (.var ⟨58⟩))
           (.fn (DataTypes.list (.var ⟨57⟩))
             (DataTypes.list (.var ⟨58⟩))))
         (.fn (.var ⟨69⟩) (.var ⟨70⟩)),
       .ty (.var ⟨70⟩) (.fn (.var ⟨71⟩) (.var ⟨72⟩)),
       .ty (.var ⟨56⟩) (.fn (.var ⟨73⟩) (.var ⟨74⟩))]
    pending :=
      [⟨.var ⟨36⟩, .var ⟨46⟩⟩,
       ⟨DataTypes.list (.var ⟨36⟩), .var ⟨48⟩⟩,
       ⟨.prod [DataTypes.list (.var ⟨44⟩), .var ⟨49⟩],
        .var ⟨50⟩⟩,
       ⟨DataTypes.list (.var ⟨52⟩), .var ⟨53⟩⟩,
       ⟨.var ⟨54⟩, .var ⟨55⟩⟩,
       ⟨.prod [.matcher .any (.var ⟨60⟩),
          .matcher .any (.var ⟨61⟩)],
        .slot (.prod [.var ⟨13⟩, .var ⟨14⟩]) (.var ⟨59⟩)⟩,
       ⟨.var ⟨36⟩, .var ⟨65⟩⟩,
       ⟨.var ⟨62⟩, .var ⟨67⟩⟩,
       ⟨.fn (.var ⟨59⟩) (.prod [.var ⟨68⟩, .var ⟨63⟩]),
        .var ⟨69⟩⟩,
       ⟨DataTypes.list
          (.prod [DataTypes.list (.var ⟨36⟩),
            DataTypes.list (.var ⟨36⟩)]), .var ⟨71⟩⟩,
       ⟨.var ⟨72⟩, .var ⟨73⟩⟩] }

private theorem join_cons_body_exact :
    callback
      (.mono (.var ⟨36⟩) ::
        .mono (DataTypes.list (.var ⟨36⟩)) :: fixContext)
      Paper1Programs.listJoinConsBody ⟨37, 10⟩ =
      some (joinConsBody, ⟨75, 15⟩) := by
  rfl'

private def joinConsArm : GeneratedChecks :=
  { hard := joinConsDPat.hard ++ joinConsBody.hard
    pending := joinConsBody.pending ++
      [⟨joinConsBody.target,
        DataTypes.list
          (.prod [DataTypes.list (.var ⟨22⟩),
            DataTypes.list (.var ⟨22⟩)])⟩] }

private theorem join_cons_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) joinHoles
      (.mk (.ctor DataCtor.cons [.var, .var])
        Paper1Programs.listJoinConsBody) ⟨36, 10⟩ =
      some (joinConsArm, ⟨75, 15⟩) := by
  simp only [elaborateMatcherArmUsing, join_cons_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, joinConsDPat,
    Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, elaborateCheckedExpressionUsing]
  rw [join_cons_body_exact]
  rfl

private def joinArms : GeneratedArms :=
  ⟨joinNilArm.append (joinConsArm.append GeneratedChecks.empty)⟩

private theorem join_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) joinHoles listMatcherJoinClause.arms
      ⟨27, 10⟩ = some (joinArms, ⟨75, 15⟩) := by
  simp only [listMatcherJoinClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [join_nil_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [join_cons_arm_exact]
  rfl

private def joinClause : GeneratedMatcherClause :=
  { holes := joinHoles
    evidence := joinHeader.evidence
    checks :=
      { hard := joinHeader.hard ++ joinNext.hard ++ joinArms.checks.hard
        pending := joinNext.pending ++ joinArms.checks.pending } }

theorem join_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨2⟩) listMatcherJoinClause ⟨22, 7⟩ =
      some (joinClause, ⟨75, 15⟩) := by
  have shape : listMatcherJoinClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [listMatcherJoinClause, MatcherClause.toShape,
      MatcherArm.toHeader, MatcherClauseShape.check,
      MatcherArmHeader.check, MatcherArmHeader.canonical,
      HoleConvention.ofCount, PPat.shapeOK, PPat.shapesOK,
      PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
      PPat.occurrences, PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      Paper1FrozenSignature.lookup_data_cons, ConstructorSchemes.listNil,
      ConstructorSchemes.listCons, ListPatternSchemes.join,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [join_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, joinHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [join_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [join_arms_exact]
  rfl

/-! ## The final catch-all clause -/

private def catchHoles : List Dual :=
  [⟨.var ⟨15⟩, .var ⟨2⟩⟩]

private def catchHeader : GeneratedPPat :=
  { holes := catchHoles
    captures := []
    evidence := none
    hard := [] }

private theorem catch_header_exact :
    elaboratePPat Paper1FrozenSignature.signature
      listMatcherCatchAllClause.header (.var ⟨2⟩) none ⟨75, 15⟩ =
      some (catchHeader, ⟨75, 16⟩) := by
  rfl'

private def catchNext : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨.matcher .any (.var ⟨75⟩),
        .slot (.var ⟨15⟩) (.var ⟨2⟩)⟩] }

private theorem catch_next_exact :
    elaborateNextMatchersUsing callback fixContext
      listMatcherCatchAllClause.nextMatchers catchHoles ⟨75, 16⟩ =
      some (catchNext, ⟨76, 16⟩) := by
  rfl'

private def catchBody : Generated :=
  { target := .var ⟨81⟩
    hard :=
      [.ty
        (.fn (.var ⟨76⟩)
          (.fn (DataTypes.list (.var ⟨76⟩))
            (DataTypes.list (.var ⟨76⟩))))
        (.fn (.var ⟨77⟩) (.var ⟨78⟩)),
       .ty (.var ⟨78⟩) (.fn (.var ⟨80⟩) (.var ⟨81⟩))]
    pending :=
      [⟨.var ⟨2⟩, .var ⟨77⟩⟩,
       ⟨DataTypes.list (.var ⟨79⟩), .var ⟨80⟩⟩] }

private theorem catch_body_exact :
    callback (.mono (.var ⟨2⟩) :: fixContext)
      (sourceList [.var 0]) ⟨76, 16⟩ = some (catchBody, ⟨82, 16⟩) := by
  rfl'

private def catchArm : GeneratedChecks :=
  { hard := catchBody.hard
    pending := catchBody.pending ++
      [⟨catchBody.target, DataTypes.list (.var ⟨2⟩)⟩] }

private theorem catch_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) catchHoles
      (.mk .var (sourceList [.var 0])) ⟨76, 16⟩ =
      some (catchArm, ⟨82, 16⟩) := by
  rfl'

private def catchArms : GeneratedArms :=
  ⟨catchArm.append GeneratedChecks.empty⟩

private theorem catch_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨2⟩) catchHoles
      listMatcherCatchAllClause.arms ⟨76, 16⟩ =
      some (catchArms, ⟨82, 16⟩) := by
  rfl'

private def catchClause : GeneratedMatcherClause :=
  { holes := catchHoles
    evidence := none
    checks :=
      { hard := catchNext.hard ++ catchArms.checks.hard
        pending := catchNext.pending ++ catchArms.checks.pending } }

theorem catch_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨2⟩) listMatcherCatchAllClause ⟨75, 15⟩ =
      some (catchClause, ⟨82, 16⟩) := by
  have shape : listMatcherCatchAllClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [listMatcherCatchAllClause, Paper1Programs.catchAllClause,
      MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [catch_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, catchHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [catch_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [catch_arms_exact]
  rfl

/-! ## Source-ordered clause traversal and public inference -/

private def generatedClauses : GeneratedMatcherClauses :=
  { evidences :=
      [.con PatternFormer.list [.var ⟨3⟩],
       .con PatternFormer.list [.var ⟨4⟩],
       .con PatternFormer.list [.var ⟨7⟩]]
    checks := nilClause.checks.append
      (consClause.checks.append
        (joinClause.checks.append
          (catchClause.checks.append GeneratedChecks.empty))) }

theorem clauses_exact :
    elaborateMatcherClausesUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨2⟩) listMatcherClauses ⟨3, 3⟩ =
      some (generatedClauses, ⟨82, 16⟩) := by
  simp only [listMatcherClauses, elaborateMatcherClausesUsing]
  rw [nil_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [cons_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [join_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [catch_clause_exact]
  rfl'

private def matcherLiteralGenerated : Generated :=
  { target := .matcher (.var ⟨2⟩) (.var ⟨2⟩)
    hard := evidenceEquations (.var ⟨2⟩) generatedClauses.evidences ++
      generatedClauses.checks.hard
    pending := generatedClauses.checks.pending }

theorem matcher_literal_exact :
    elaborateMatcherLiteralUsing callback Paper1FrozenSignature.signature
      fixContext listMatcherClauses ⟨2, 2⟩ =
      some (matcherLiteralGenerated, ⟨82, 16⟩) := by
  simp only [elaborateMatcherLiteralUsing,
    M4Paper1ComputabilityRegression.list_static_checks, if_true]
  rw [clauses_exact]
  rfl

private def listGenerated : Generated :=
  Generated.fromFix
    (.slot (.var ⟨0⟩) (.var ⟨0⟩))
    (.matcher (.var ⟨1⟩) (.var ⟨1⟩))
    matcherLiteralGenerated

theorem structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 200)
      Paper1FrozenSignature.signature 130 [] listMatcherDefinition ⟨0, 0⟩ =
      some (listGenerated, ⟨82, 16⟩) := by
  simp only [listMatcherDefinition, M4.elaborateFuelUsing.eq_def,
    elaborateFixUsing,
    M4Paper1ComputabilityRegression.list_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing callback Paper1FrozenSignature.signature
      fixContext listMatcherClauses ⟨2, 2⟩).bind _ = _
  rw [matcher_literal_exact]
  rfl

/-- Translate both fresh-variable sorts from the standalone origin to an
arbitrary starting supply. -/
def supplyShiftSubstitution (start : Supply) : Subst :=
  { ty := fun index => .var ⟨start.ty + index.index⟩
    cap := fun index => .var ⟨start.cap + index.index⟩ }

private def listShiftSubstitution : Subst :=
  supplyShiftSubstitution ⟨145, 37⟩

def translateGenerated (start : Supply) (generated : Generated) : Generated :=
  let substitution := supplyShiftSubstitution start
  { target := generated.target.apply substitution
    hard := generated.hard.map (Equation.apply substitution)
    pending := generated.pending.map
      (CheckObligation.apply substitution) }

private def shiftGenerated (generated : Generated) : Generated :=
  translateGenerated ⟨145, 37⟩ generated

/-- The standalone `list` constraints translated to an arbitrary origin. -/
def listGeneratedAt (start : Supply) : Generated :=
  translateGenerated start listGenerated

/-- The translated `list` constraints used by closed Paper 1 elaboration. -/
def shiftedListGenerated : Generated := listGeneratedAt ⟨145, 37⟩

private def shiftedCallback : ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 381

private def shiftedFixContext : Context :=
  fixContext.applyFree listShiftSubstitution

private def shiftChecks (checks : GeneratedChecks) : GeneratedChecks :=
  { hard := checks.hard.map (Equation.apply listShiftSubstitution)
    pending := checks.pending.map
      (CheckObligation.apply listShiftSubstitution) }

private def shiftDual (dual : Dual) : Dual :=
  ⟨dual.capability.apply listShiftSubstitution.cap,
    dual.target.apply listShiftSubstitution⟩

private def shiftMatcherClause
    (clause : GeneratedMatcherClause) : GeneratedMatcherClause :=
  { holes := clause.holes.map shiftDual
    evidence := clause.evidence.map
      (Cap.apply listShiftSubstitution.cap)
    checks := shiftChecks clause.checks }

private theorem shifted_nil_clause_exact :
    elaborateMatcherClauseUsing shiftedCallback
      Paper1FrozenSignature.signature shiftedFixContext (.var ⟨147⟩)
      listMatcherNilClause ⟨148, 40⟩ =
      some (shiftMatcherClause nilClause, ⟨157, 41⟩) := by
  have shape : listMatcherNilClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simpa using (show listMatcherNilClause.toShape.check
      Paper1FrozenSignature.signature = true from by
        simp [listMatcherNilClause, Paper1Programs.nilClause,
          MatcherClause.toShape, MatcherArm.toHeader,
          MatcherClauseShape.check, MatcherArmHeader.check,
          MatcherArmHeader.canonical, HoleConvention.ofCount,
          PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
          PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
          PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
          DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
          ConstructorSchemes.listNil, ListPatternSchemes.nil,
          PolyDataTypes.list])
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rfl'

private theorem shifted_cons_clause_exact :
    elaborateMatcherClauseUsing shiftedCallback
      Paper1FrozenSignature.signature shiftedFixContext (.var ⟨147⟩)
      listMatcherConsClause ⟨157, 41⟩ =
      some (shiftMatcherClause consClause, ⟨167, 44⟩) := by
  have shape : listMatcherConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [listMatcherConsClause, MatcherClause.toShape,
      MatcherArm.toHeader, MatcherClauseShape.check,
      MatcherArmHeader.check, MatcherArmHeader.canonical,
      HoleConvention.ofCount, PPat.shapeOK, PPat.shapesOK,
      PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
      PPat.occurrences, PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_cons,
      ConstructorSchemes.listCons, ListPatternSchemes.cons,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rfl'

private theorem shifted_join_clause_exact :
    elaborateMatcherClauseUsing shiftedCallback
      Paper1FrozenSignature.signature shiftedFixContext (.var ⟨147⟩)
      listMatcherJoinClause ⟨167, 44⟩ =
      some (shiftMatcherClause joinClause, ⟨220, 52⟩) := by
  have shape : listMatcherJoinClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [listMatcherJoinClause, MatcherClause.toShape,
      MatcherArm.toHeader, MatcherClauseShape.check,
      MatcherArmHeader.check, MatcherArmHeader.canonical,
      HoleConvention.ofCount, PPat.shapeOK, PPat.shapesOK,
      PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
      PPat.occurrences, PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      Paper1FrozenSignature.lookup_data_cons, ConstructorSchemes.listNil,
      ConstructorSchemes.listCons, ListPatternSchemes.join,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rfl'

private theorem shifted_catch_clause_exact :
    elaborateMatcherClauseUsing shiftedCallback
      Paper1FrozenSignature.signature shiftedFixContext (.var ⟨147⟩)
      listMatcherCatchAllClause ⟨220, 52⟩ =
      some (shiftMatcherClause catchClause, ⟨227, 53⟩) := by
  have shape : listMatcherCatchAllClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [listMatcherCatchAllClause, Paper1Programs.catchAllClause,
      MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rfl'

private def shiftMatcherClauses
    (clauses : GeneratedMatcherClauses) : GeneratedMatcherClauses :=
  { evidences := clauses.evidences.map
      (Cap.apply listShiftSubstitution.cap)
    checks := shiftChecks clauses.checks }

private theorem shifted_clauses_exact :
    elaborateMatcherClausesUsing shiftedCallback
      Paper1FrozenSignature.signature shiftedFixContext (.var ⟨147⟩)
      listMatcherClauses ⟨148, 40⟩ =
      some (shiftMatcherClauses generatedClauses, ⟨227, 53⟩) := by
  simp only [listMatcherClauses, elaborateMatcherClausesUsing]
  rw [shifted_nil_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [shifted_cons_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [shifted_join_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [shifted_catch_clause_exact]
  rfl'

private theorem shifted_matcher_literal_exact :
    elaborateMatcherLiteralUsing shiftedCallback
      Paper1FrozenSignature.signature shiftedFixContext listMatcherClauses
      ⟨147, 39⟩ =
      some (shiftGenerated matcherLiteralGenerated, ⟨227, 53⟩) := by
  simp only [elaborateMatcherLiteralUsing,
    M4Paper1ComputabilityRegression.list_static_checks, if_true]
  rw [shifted_clauses_exact]
  rfl'

/-- Exact nested execution used by the closed-multiset Paper 1 regression. -/
theorem shifted_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 383 [] listMatcherDefinition ⟨145, 37⟩ =
      some (shiftedListGenerated, ⟨227, 53⟩) := by
  simp only [listMatcherDefinition, M4.elaborateFuelUsing.eq_def,
    elaborateFixUsing,
    M4Paper1ComputabilityRegression.list_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing shiftedCallback
      Paper1FrozenSignature.signature shiftedFixContext listMatcherClauses
      ⟨147, 39⟩).bind _ = _
  rw [shifted_matcher_literal_exact]
  rfl'

/-- Exact principal type computed for the source-defined unary `list`
matcher constructor. -/
def listMatcherType : Ty :=
  .fn (.slot (.var ⟨10⟩) (.var ⟨44⟩))
    (.matcher (.con PatternFormer.list [.var ⟨10⟩])
      (DataTypes.list (.var ⟨44⟩)))

private theorem close_fuel_exact :
    (inferGeneratedUsing (unifyWithFuel 200) listGenerated).bind
      (fun closed => some closed.target) = some listMatcherType := by
  simp only [listGenerated, matcherLiteralGenerated, generatedClauses,
    nilClause, nilHeader, nilNext, nilArms, nilFirstArm, nilSecondArm,
    consClause, consHeader, consNext, consArms, consArm, consDPat,
    consBody, joinClause, joinHeader, joinNext, joinNextFirst,
    joinNextSecond, joinArms, joinNilArm, joinNilDPat, joinNilBody,
    joinConsArm, joinConsDPat, joinConsBody,
    catchClause, catchHeader, catchNext, catchArms, catchArm, catchBody,
    Generated.fromFix, GeneratedChecks.append, GeneratedChecks.empty,
    evidenceEquations, List.append_assoc]
  rfl'

theorem infer_exact :
    M4.infer Paper1FrozenSignature.signature [] listMatcherDefinition =
      some listMatcherType := by
  have elaborated :=
    M4.elaborateFuel_success_of_solverFuel_success structural_fuel_exact
  cases closureEquality :
      inferGeneratedUsing (unifyWithFuel 200) listGenerated with
  | none =>
      have impossible := close_fuel_exact
      simp [closureEquality] at impossible
  | some closed =>
      have closedTarget : closed.target = listMatcherType := by
        have exactTarget := close_fuel_exact
        simpa [closureEquality] using exactTarget
      have publicClosure :=
        inferGeneratedUsing_unify_of_fuel_success closureEquality
      unfold M4.infer M4.elaborate
      rw [M4Paper1ComputabilityRegression.listMatcherDefinition_complexity]
      rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl]
      rw [elaborated]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [publicClosure]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [closedTarget]
      rfl

theorem typing :
    M4.Typing Paper1FrozenSignature.signature [] listMatcherDefinition
      listMatcherType :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed infer_exact

end TypePM.Source.M4Paper1ListExactRegression
