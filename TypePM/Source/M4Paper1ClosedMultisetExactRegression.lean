import TypePM.Source.M4Paper1ComputabilityRegression
import TypePM.Source.M4ElaborationFuelTransport
import TypePM.Source.M4Paper1ListExactRegression

/-!
# Exact kernel regression stages for the closed Paper 1 `multiset` matcher

The seven matcher clauses are recorded as separate executable equations.
Nested source expressions are reduced at their own named boundaries so no
single simplifier call traverses the complete program.
-/

namespace TypePM.Source.M4Paper1ClosedMultisetExactRegression

open Paper1Programs
open MatcherTyping

set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private def callback : ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 355

private def fixContext : Context :=
  [.mono (.slot (.var ⟨0⟩) (.var ⟨1⟩)),
   .mono (.fn (.slot (.var ⟨0⟩) (.var ⟨1⟩))
     (.matcher (.var ⟨1⟩) (.var ⟨2⟩))),
   .mono (.var ⟨0⟩)]

/-! ## Clauses 1 and 2 -/

private def nilClauseGenerated : GeneratedMatcherClause :=
  { holes := []
    evidence := some (.con PatternFormer.list [.var ⟨3⟩])
    checks :=
      { hard :=
          [.ty (DataTypes.list (.var ⟨4⟩)) (.var ⟨3⟩),
           .ty (DataTypes.list (.var ⟨5⟩)) (.var ⟨3⟩),
           .ty
             (.fn (.var ⟨6⟩)
               (.fn (DataTypes.list (.var ⟨6⟩))
                 (DataTypes.list (.var ⟨6⟩))))
             (.fn (.var ⟨7⟩) (.var ⟨8⟩)),
           .ty (.var ⟨8⟩) (.fn (.var ⟨10⟩) (.var ⟨11⟩))]
        pending :=
          [⟨.prod [], .prod []⟩,
           ⟨.prod [], .var ⟨7⟩⟩,
           ⟨DataTypes.list (.var ⟨9⟩), .var ⟨10⟩⟩,
           ⟨.var ⟨11⟩, DataTypes.list (.prod [])⟩,
           ⟨DataTypes.list (.var ⟨12⟩), DataTypes.list (.prod [])⟩] } }

private def nilHeader : GeneratedPPat :=
  { holes := []
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨3⟩])
    hard := [.ty (DataTypes.list (.var ⟨4⟩)) (.var ⟨3⟩)] }

private theorem nil_header_exact :
    elaboratePPat Paper1FrozenSignature.signature nilClause.header
      (.var ⟨3⟩) none ⟨4, 3⟩ = some (nilHeader, ⟨5, 4⟩) := by
  rfl'

private def nilNext : GeneratedChecks :=
  { hard := []
    pending := [⟨.prod [], .prod []⟩] }

private theorem nil_next_exact :
    elaborateNextMatchersUsing callback fixContext nilClause.nextMatchers []
      ⟨5, 4⟩ = some (nilNext, ⟨5, 4⟩) := by
  rfl'

private def nilFirstDPat : GeneratedDPat :=
  { bindings := []
    hard := [.ty (DataTypes.list (.var ⟨5⟩)) (.var ⟨3⟩)] }

private theorem nil_first_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature (.ctor DataCtor.nil [])
      (.var ⟨3⟩) ⟨5, 4⟩ = some (nilFirstDPat, ⟨6, 4⟩) := by
  rfl'

private def nilFirstBody : Generated :=
  { target := .var ⟨11⟩
    hard :=
      [.ty
        (.fn (.var ⟨6⟩)
          (.fn (DataTypes.list (.var ⟨6⟩))
            (DataTypes.list (.var ⟨6⟩))))
        (.fn (.var ⟨7⟩) (.var ⟨8⟩)),
       .ty (.var ⟨8⟩) (.fn (.var ⟨10⟩) (.var ⟨11⟩))]
    pending :=
      [⟨.prod [], .var ⟨7⟩⟩,
       ⟨DataTypes.list (.var ⟨9⟩), .var ⟨10⟩⟩] }

private theorem nil_first_body_exact :
    callback fixContext (sourceList [Paper1Programs.unit]) ⟨6, 4⟩ =
      some (nilFirstBody, ⟨12, 4⟩) := by
  rfl'

private def nilFirstArm : GeneratedChecks :=
  { hard := nilFirstDPat.hard ++ nilFirstBody.hard
    pending := nilFirstBody.pending ++
      [⟨nilFirstBody.target, DataTypes.list (.prod [])⟩] }

private theorem nil_first_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) []
      (.mk (.ctor DataCtor.nil []) (sourceList [Paper1Programs.unit]))
      ⟨5, 4⟩ = some (nilFirstArm, ⟨12, 4⟩) := by
  simp only [elaborateMatcherArmUsing, nil_first_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, nilFirstDPat,
    Pattern.extendContext, List.map_nil, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [nil_first_body_exact]
  rfl

private def nilSecondBody : Generated :=
  { target := DataTypes.list (.var ⟨12⟩)
    hard := []
    pending := [] }

private theorem nil_second_body_exact :
    callback fixContext (sourceList []) ⟨12, 4⟩ =
      some (nilSecondBody, ⟨13, 4⟩) := by
  rfl'

private def nilSecondArm : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨DataTypes.list (.var ⟨12⟩), DataTypes.list (.prod [])⟩] }

private theorem nil_second_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) [] (.mk .wild (sourceList []))
      ⟨12, 4⟩ = some (nilSecondArm, ⟨13, 4⟩) := by
  rfl'

private def nilArms : GeneratedArms :=
  ⟨nilFirstArm.append (nilSecondArm.append GeneratedChecks.empty)⟩

private theorem nil_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) [] nilClause.arms ⟨5, 4⟩ =
      some (nilArms, ⟨13, 4⟩) := by
  simp only [nilClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [nil_first_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [nil_second_arm_exact]
  rfl

theorem nil_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨3⟩) Paper1Programs.nilClause ⟨4, 3⟩ =
      some (nilClauseGenerated, ⟨13, 4⟩) := by
  have shape : nilClause.toShape.check Paper1FrozenSignature.signature = true := by
    simp [nilClause, MatcherClause.toShape, MatcherArm.toHeader,
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
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [nil_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [nil_arms_exact]
  rfl

private def headOnlyHoles : List Dual :=
  [⟨.var ⟨5⟩, .var ⟨13⟩⟩]

private def headOnlyClauseGenerated : GeneratedMatcherClause :=
  { holes := headOnlyHoles
    evidence := some (.con PatternFormer.list [.var ⟨4⟩])
    checks :=
      { hard :=
          [.ty (DataTypes.list (.var ⟨13⟩)) (.var ⟨3⟩),
           .cap (.var ⟨5⟩) (.var ⟨4⟩)]
        pending :=
          [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩),
            .slot (.var ⟨5⟩) (.var ⟨13⟩)⟩,
           ⟨.var ⟨3⟩, DataTypes.list (.var ⟨13⟩)⟩] } }

theorem head_only_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨3⟩) headOnlyClause ⟨13, 4⟩ =
      some (headOnlyClauseGenerated, ⟨14, 6⟩) := by
  let header : GeneratedPPat :=
    { holes := headOnlyHoles
      captures := []
      evidence := some (.con PatternFormer.list [.var ⟨4⟩])
      hard :=
        [.ty (DataTypes.list (.var ⟨13⟩)) (.var ⟨3⟩),
         .cap (.var ⟨5⟩) (.var ⟨4⟩)] }
  have headerExact : elaboratePPat Paper1FrozenSignature.signature
      headOnlyClause.header (.var ⟨3⟩) none ⟨13, 4⟩ =
      some (header, ⟨14, 6⟩) := by
    rfl'
  let next : GeneratedChecks :=
    { hard := []
      pending :=
        [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩),
          .slot (.var ⟨5⟩) (.var ⟨13⟩)⟩] }
  have nextExact : elaborateNextMatchersUsing callback fixContext
      headOnlyClause.nextMatchers headOnlyHoles ⟨14, 6⟩ =
      some (next, ⟨14, 6⟩) := by
    rfl'
  let arm : GeneratedChecks :=
    { hard := []
      pending := [⟨.var ⟨3⟩, DataTypes.list (.var ⟨13⟩)⟩] }
  have armExact : elaborateMatcherArmUsing callback
      Paper1FrozenSignature.signature fixContext [] (.var ⟨3⟩)
      headOnlyHoles (.mk .var (.var 0)) ⟨14, 6⟩ =
      some (arm, ⟨14, 6⟩) := by
    rfl'
  let arms : GeneratedArms := ⟨arm.append GeneratedChecks.empty⟩
  have armsExact : elaborateMatcherArmsUsing callback
      Paper1FrozenSignature.signature fixContext [] (.var ⟨3⟩)
      headOnlyHoles headOnlyClause.arms ⟨14, 6⟩ =
      some (arms, ⟨14, 6⟩) := by
    simp only [headOnlyClause, MatcherClause.arms,
      elaborateMatcherArmsUsing]
    rw [armExact]
    rfl
  have shape : headOnlyClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [headOnlyClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [headerExact]
  simp only [Option.bind_eq_bind, Option.bind_some, header,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [nextExact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [armsExact]
  rfl

/-! ## Clause 3: value-cons -/

private def valueConsHoles : List Dual :=
  [⟨.var ⟨7⟩, DataTypes.list (.var ⟨14⟩)⟩]

private def valueConsHeader : GeneratedPPat :=
  { holes := valueConsHoles
    captures := [.var ⟨14⟩]
    evidence := some (.con PatternFormer.list [.var ⟨6⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨14⟩)) (.var ⟨3⟩),
       .cap (.var ⟨7⟩) (.con PatternFormer.list [.var ⟨6⟩])] }

private theorem value_cons_header_exact :
    elaboratePPat Paper1FrozenSignature.signature valueConsClause.header
      (.var ⟨3⟩) none ⟨14, 6⟩ =
      some (valueConsHeader, ⟨15, 8⟩) := by
  rfl'

private def valueConsNext : GeneratedChecks :=
  { hard :=
      [.ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨1⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨2⟩)))
        (.fn (.var ⟨15⟩) (.var ⟨16⟩))]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩), .var ⟨15⟩⟩,
       ⟨.var ⟨16⟩,
        .slot (.var ⟨7⟩) (DataTypes.list (.var ⟨14⟩))⟩] }

private theorem value_cons_next_exact :
    elaborateNextMatchersUsing callback
      (.mono (.var ⟨14⟩) :: fixContext)
      valueConsClause.nextMatchers valueConsHoles ⟨15, 8⟩ =
      some (valueConsNext, ⟨17, 8⟩) := by
  rfl'

private def valueConsBody : Generated :=
  { target := .var ⟨40⟩
    hard :=
      [.ty
        (.fn (.var ⟨18⟩)
          (.fn (DataTypes.list (.var ⟨18⟩))
            (.data DataFormer.bool [])))
        (.fn (.var ⟨19⟩) (.var ⟨20⟩)),
       .ty (.var ⟨20⟩) (.fn (.var ⟨21⟩) (.var ⟨22⟩)),
       .ty
        (.fn (.data DataFormer.bool [])
          (.fn (.var ⟨17⟩) (.fn (.var ⟨17⟩) (.var ⟨17⟩))))
        (.fn (.var ⟨23⟩) (.var ⟨24⟩)),
       .ty
        (.fn (.var ⟨26⟩)
          (.fn (DataTypes.list (.var ⟨26⟩))
            (DataTypes.list (.var ⟨26⟩))))
        (.fn (.var ⟨27⟩) (.var ⟨28⟩)),
       .ty (.var ⟨28⟩) (.fn (.var ⟨29⟩) (.var ⟨30⟩)),
       .ty
        (.fn (.var ⟨25⟩)
          (.fn (DataTypes.list (.var ⟨25⟩))
            (DataTypes.list (.var ⟨25⟩))))
        (.fn (.var ⟨31⟩) (.var ⟨32⟩)),
       .ty (.var ⟨32⟩) (.fn (.var ⟨34⟩) (.var ⟨35⟩)),
       .ty (.var ⟨24⟩) (.fn (.var ⟨36⟩) (.var ⟨37⟩)),
       .ty (.var ⟨37⟩) (.fn (.var ⟨39⟩) (.var ⟨40⟩))]
    pending :=
      [⟨.var ⟨14⟩, .var ⟨19⟩⟩,
       ⟨.var ⟨3⟩, .var ⟨21⟩⟩,
       ⟨.var ⟨22⟩, .var ⟨23⟩⟩,
       ⟨.var ⟨14⟩, .var ⟨27⟩⟩,
       ⟨.var ⟨3⟩, .var ⟨29⟩⟩,
       ⟨.var ⟨30⟩, .var ⟨31⟩⟩,
       ⟨DataTypes.list (.var ⟨33⟩), .var ⟨34⟩⟩,
       ⟨.var ⟨35⟩, .var ⟨36⟩⟩,
       ⟨DataTypes.list (.var ⟨38⟩), .var ⟨39⟩⟩] }

private def valueConsArmSource : MatcherArm :=
  .mk .var
    (.ifE (.prim .member [.var 1, .var 0])
      (sourceList [.prim .deleteFirst [.var 1, .var 0]])
      (sourceList []))

private theorem value_cons_body_exact :
    callback
      (.mono (.var ⟨3⟩) ::
        .mono (.var ⟨14⟩) :: fixContext)
      valueConsArmSource.body ⟨17, 8⟩ =
      some (valueConsBody, ⟨41, 8⟩) := by
  rfl'

private def valueConsArm : GeneratedChecks :=
  { hard := valueConsBody.hard
    pending := valueConsBody.pending ++
      [⟨valueConsBody.target,
        DataTypes.list (DataTypes.list (.var ⟨14⟩))⟩] }

private theorem value_cons_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext valueConsHeader.captures (.var ⟨3⟩) valueConsHoles
      valueConsArmSource ⟨17, 8⟩ =
      some (valueConsArm, ⟨41, 8⟩) := by
  rfl'

private def valueConsArms : GeneratedArms :=
  ⟨valueConsArm.append GeneratedChecks.empty⟩

private theorem value_cons_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [.var ⟨14⟩] (.var ⟨3⟩) valueConsHoles
      valueConsClause.arms ⟨17, 8⟩ =
      some (valueConsArms, ⟨41, 8⟩) := by
  change elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
    fixContext valueConsHeader.captures (.var ⟨3⟩) valueConsHoles
    [valueConsArmSource] ⟨17, 8⟩ = _
  simp only [elaborateMatcherArmsUsing]
  rw [value_cons_arm_exact]
  rfl

private def valueConsClauseGenerated : GeneratedMatcherClause :=
  { holes := valueConsHoles
    evidence := valueConsHeader.evidence
    checks :=
      { hard := valueConsHeader.hard ++ valueConsNext.hard ++ valueConsArm.hard
        pending := valueConsNext.pending ++ valueConsArm.pending } }

theorem value_cons_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨3⟩) valueConsClause ⟨14, 6⟩ =
      some (valueConsClauseGenerated, ⟨41, 8⟩) := by
  have shape : valueConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [valueConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [value_cons_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, valueConsHeader,
    Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [value_cons_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [value_cons_arms_exact]
  rfl

/-! ## Clause 4: general cons -/

private def generalConsHoles : List Dual :=
  [⟨.var ⟨9⟩, .var ⟨41⟩⟩,
   ⟨.var ⟨10⟩, DataTypes.list (.var ⟨41⟩)⟩]

private def generalConsHeader : GeneratedPPat :=
  { holes := generalConsHoles
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨8⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨41⟩)) (.var ⟨3⟩),
       .cap (.var ⟨9⟩) (.var ⟨8⟩),
       .cap (.var ⟨10⟩) (.con PatternFormer.list [.var ⟨8⟩])] }

private theorem general_cons_header_exact :
    elaboratePPat Paper1FrozenSignature.signature generalConsClause.header
      (.var ⟨3⟩) none ⟨41, 8⟩ =
      some (generalConsHeader, ⟨42, 11⟩) := by
  rfl'

private def generalConsNext : GeneratedChecks :=
  { hard :=
      [.ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨1⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨2⟩)))
        (.fn (.var ⟨42⟩) (.var ⟨43⟩))]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩),
        .slot (.var ⟨9⟩) (.var ⟨41⟩)⟩,
       ⟨.slot (.var ⟨0⟩) (.var ⟨1⟩), .var ⟨42⟩⟩,
       ⟨.var ⟨43⟩,
        .slot (.var ⟨10⟩) (DataTypes.list (.var ⟨41⟩))⟩] }

private theorem general_cons_next_exact :
    elaborateNextMatchersUsing callback fixContext generalConsClause.nextMatchers
      generalConsHoles ⟨42, 11⟩ = some (generalConsNext, ⟨44, 11⟩) := by
  rfl'

private def generalConsBodyGenerated : Generated :=
  { target := DataTypes.list (.prod [.var ⟨47⟩, .var ⟨55⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨44⟩)) (.var ⟨3⟩),
       .ty (.var ⟨47⟩) (.var ⟨46⟩),
       .cap (.var ⟨14⟩) (.var ⟨13⟩),
       .ty (.var ⟨48⟩) (DataTypes.list (.var ⟨46⟩)),
       .cap (.var ⟨15⟩) (.con PatternFormer.list [.var ⟨13⟩]),
       .ty (.var ⟨45⟩) (DataTypes.list (.var ⟨44⟩)),
       .cap (.var ⟨12⟩) (.con PatternFormer.list [.var ⟨11⟩]),
       .ty (DataTypes.list (.var ⟨46⟩)) (DataTypes.list (.var ⟨44⟩)),
       .cap (.con PatternFormer.list [.var ⟨13⟩])
         (.con PatternFormer.list [.var ⟨11⟩]),
       .ty (.var ⟨0⟩) (.fn (.var ⟨49⟩) (.var ⟨50⟩)),
       .ty
         (.fn (DataTypes.list (.var ⟨51⟩))
           (.fn (DataTypes.list (.var ⟨51⟩))
             (DataTypes.list (.var ⟨51⟩))))
         (.fn (.var ⟨52⟩) (.var ⟨53⟩)),
       .ty (.var ⟨53⟩) (.fn (.var ⟨54⟩) (.var ⟨55⟩))]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩), .var ⟨49⟩⟩,
       ⟨.var ⟨50⟩,
        .slot (.con PatternFormer.list [.var ⟨11⟩]) (.var ⟨3⟩)⟩,
       ⟨.var ⟨45⟩, .var ⟨52⟩⟩,
       ⟨.var ⟨48⟩, .var ⟨54⟩⟩] }

private theorem general_cons_body_exact :
    callback (.mono (.var ⟨3⟩) :: fixContext) generalConsBody ⟨44, 11⟩ =
      some (generalConsBodyGenerated, ⟨56, 16⟩) := by
  rfl'

private def generalConsArm : GeneratedChecks :=
  { hard := generalConsBodyGenerated.hard
    pending := generalConsBodyGenerated.pending ++
      [⟨generalConsBodyGenerated.target,
        DataTypes.list (.prod [.var ⟨41⟩,
          DataTypes.list (.var ⟨41⟩)])⟩] }

private theorem general_cons_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) generalConsHoles (.mk .var generalConsBody)
      ⟨44, 11⟩ = some (generalConsArm, ⟨56, 16⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨3⟩)
      ⟨44, 11⟩ = some (⟨[.var ⟨3⟩], []⟩, ⟨44, 11⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [general_cons_body_exact]
  rfl

private def generalConsArms : GeneratedArms :=
  ⟨generalConsArm.append GeneratedChecks.empty⟩

private theorem general_cons_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) generalConsHoles generalConsClause.arms
      ⟨44, 11⟩ = some (generalConsArms, ⟨56, 16⟩) := by
  simp only [generalConsClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [general_cons_arm_exact]
  rfl

private def generalConsClauseGenerated : GeneratedMatcherClause :=
  { holes := generalConsHoles
    evidence := generalConsHeader.evidence
    checks :=
      { hard := generalConsHeader.hard ++ generalConsNext.hard ++ generalConsArm.hard
        pending := generalConsNext.pending ++ generalConsArm.pending } }

theorem general_cons_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨3⟩) generalConsClause ⟨41, 8⟩ =
      some (generalConsClauseGenerated, ⟨56, 16⟩) := by
  have shape : generalConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [generalConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [general_cons_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, generalConsHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [general_cons_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [general_cons_arms_exact]
  rfl

/-! ## Clause 5: join -/

private def joinHoles : List Dual :=
  [⟨.var ⟨17⟩, DataTypes.list (.var ⟨56⟩)⟩,
   ⟨.var ⟨18⟩, DataTypes.list (.var ⟨56⟩)⟩]

private def joinHeader : GeneratedPPat :=
  { holes := joinHoles
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨16⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨56⟩)) (.var ⟨3⟩),
       .cap (.var ⟨17⟩) (.con PatternFormer.list [.var ⟨16⟩]),
       .cap (.var ⟨18⟩) (.con PatternFormer.list [.var ⟨16⟩])] }

private theorem join_header_exact :
    elaboratePPat Paper1FrozenSignature.signature joinClause.header
      (.var ⟨3⟩) none ⟨56, 16⟩ = some (joinHeader, ⟨57, 19⟩) := by
  rfl'

private def joinNext : GeneratedChecks :=
  { hard :=
      [.ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨1⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨2⟩)))
        (.fn (.var ⟨57⟩) (.var ⟨58⟩)),
       .ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨1⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨2⟩)))
        (.fn (.var ⟨59⟩) (.var ⟨60⟩))]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩), .var ⟨57⟩⟩,
       ⟨.var ⟨58⟩,
        .slot (.var ⟨17⟩) (DataTypes.list (.var ⟨56⟩))⟩,
       ⟨.slot (.var ⟨0⟩) (.var ⟨1⟩), .var ⟨59⟩⟩,
       ⟨.var ⟨60⟩,
        .slot (.var ⟨18⟩) (DataTypes.list (.var ⟨56⟩))⟩] }

private theorem join_next_exact :
    elaborateNextMatchersUsing callback fixContext joinClause.nextMatchers
      joinHoles ⟨57, 19⟩ = some (joinNext, ⟨61, 19⟩) := by
  rfl'

private def joinNilDPat : GeneratedDPat :=
  { bindings := []
    hard := [.ty (DataTypes.list (.var ⟨61⟩)) (.var ⟨3⟩)] }

private def joinNilBody : Generated :=
  { target := .var ⟨69⟩
    hard :=
      [.ty
        (.fn (.var ⟨62⟩)
          (.fn (DataTypes.list (.var ⟨62⟩))
            (DataTypes.list (.var ⟨62⟩))))
        (.fn (.var ⟨65⟩) (.var ⟨66⟩)),
       .ty (.var ⟨66⟩) (.fn (.var ⟨68⟩) (.var ⟨69⟩))]
    pending :=
      [⟨.prod [DataTypes.list (.var ⟨63⟩),
          DataTypes.list (.var ⟨64⟩)], .var ⟨65⟩⟩,
       ⟨DataTypes.list (.var ⟨67⟩), .var ⟨68⟩⟩] }

private def joinNilArm : GeneratedChecks :=
  { hard := joinNilDPat.hard ++ joinNilBody.hard
    pending := joinNilBody.pending ++
      [⟨joinNilBody.target,
        DataTypes.list (.prod [DataTypes.list (.var ⟨56⟩),
          DataTypes.list (.var ⟨56⟩)])⟩] }

private theorem join_nil_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) joinHoles
      (.mk (.ctor DataCtor.nil [])
        (sourceList [.tuple [sourceList [], sourceList []]]))
      ⟨61, 19⟩ = some (joinNilArm, ⟨70, 19⟩) := by
  rfl'

private def joinConsDPat : GeneratedDPat :=
  { bindings := [.var ⟨70⟩, DataTypes.list (.var ⟨70⟩)]
    hard := [.ty (DataTypes.list (.var ⟨70⟩)) (.var ⟨3⟩)] }

private theorem join_cons_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature
      (.ctor DataCtor.cons [.var, .var]) (.var ⟨3⟩) ⟨70, 19⟩ =
      some (joinConsDPat, ⟨71, 19⟩) := by
  rfl'

private def joinConsBodyGenerated : Generated :=
  { target := TypePM.Ty.var { index := 120 },
     hard := [TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 1 }) (TypePM.Ty.var { index := 1 }),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 2 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap
                (TypePM.Cap.var { index := 1 })
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 19 }]),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 79 })
                (TypePM.Ty.prod [TypePM.Ty.var { index := 80 }, TypePM.Ty.var { index := 83 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 1 }) (TypePM.Ty.var { index := 1 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 19 }) (TypePM.Cap.var { index := 19 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 83 }) (TypePM.Ty.var { index := 85 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 80 }) (TypePM.Ty.var { index := 87 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 1 }) (TypePM.Ty.var { index := 1 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 19 }) (TypePM.Cap.var { index := 19 }),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.var { index := 88 })
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 88 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 88 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 89 }) (TypePM.Ty.var { index := 90 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 90 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 91 }) (TypePM.Ty.var { index := 92 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.fn (TypePM.Ty.var { index := 77 }) (TypePM.Ty.var { index := 78 }))
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 77 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 78 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 93 }) (TypePM.Ty.var { index := 94 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 94 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 95 }) (TypePM.Ty.var { index := 96 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 76 }])
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 76 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 76 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 97 }) (TypePM.Ty.var { index := 98 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 101 })
                (TypePM.Ty.prod [TypePM.Ty.var { index := 102 }, TypePM.Ty.var { index := 105 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 1 }) (TypePM.Ty.var { index := 1 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 19 }) (TypePM.Cap.var { index := 19 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 105 }) (TypePM.Ty.var { index := 107 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 102 }) (TypePM.Ty.var { index := 109 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 1 }) (TypePM.Ty.var { index := 1 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 19 }) (TypePM.Cap.var { index := 19 }),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.var { index := 110 })
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 110 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 110 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 111 }) (TypePM.Ty.var { index := 112 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 112 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 113 }) (TypePM.Ty.var { index := 114 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.fn (TypePM.Ty.var { index := 99 }) (TypePM.Ty.var { index := 100 }))
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 99 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 100 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 115 }) (TypePM.Ty.var { index := 116 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 116 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 117 }) (TypePM.Ty.var { index := 118 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 98 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 119 }) (TypePM.Ty.var { index := 120 }))],
     pending := [{ source := TypePM.Ty.var { index := 70 }, expected := TypePM.Ty.var { index := 89 } },
                 { source := TypePM.Ty.var { index := 85 }, expected := TypePM.Ty.var { index := 91 } },
                 { source := TypePM.Ty.fn
                               (TypePM.Ty.var { index := 79 })
                               (TypePM.Ty.prod [TypePM.Ty.var { index := 87 }, TypePM.Ty.var { index := 92 }]),
                   expected := TypePM.Ty.var { index := 93 } },
                 { source := TypePM.Ty.data
                               { name := "List" }
                               [TypePM.Ty.prod
                                  [TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }],
                                   TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }]]],
                   expected := TypePM.Ty.var { index := 95 } },
                 { source := TypePM.Ty.var { index := 96 }, expected := TypePM.Ty.var { index := 97 } },
                 { source := TypePM.Ty.var { index := 70 }, expected := TypePM.Ty.var { index := 111 } },
                 { source := TypePM.Ty.var { index := 109 }, expected := TypePM.Ty.var { index := 113 } },
                 { source := TypePM.Ty.fn
                               (TypePM.Ty.var { index := 101 })
                               (TypePM.Ty.prod [TypePM.Ty.var { index := 114 }, TypePM.Ty.var { index := 107 }]),
                   expected := TypePM.Ty.var { index := 115 } },
                 { source := TypePM.Ty.data
                               { name := "List" }
                               [TypePM.Ty.prod
                                  [TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }],
                                   TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }]]],
                   expected := TypePM.Ty.var { index := 117 } },
                 { source := TypePM.Ty.var { index := 118 }, expected := TypePM.Ty.var { index := 119 } }] }
private theorem join_cons_body_exact :
    callback
      (.mono (.var ⟨70⟩) ::
        .mono (DataTypes.list (.var ⟨70⟩)) :: fixContext)
      joinConsBody ⟨71, 19⟩ =
      some (joinConsBodyGenerated, ⟨121, 22⟩) := by
  rfl'

private def joinConsArm : GeneratedChecks :=
  { hard := joinConsDPat.hard ++ joinConsBodyGenerated.hard
    pending := joinConsBodyGenerated.pending ++
      [⟨joinConsBodyGenerated.target,
        DataTypes.list
          (.prod [DataTypes.list (.var ⟨56⟩),
            DataTypes.list (.var ⟨56⟩)])⟩] }

private theorem join_cons_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) joinHoles
      (.mk (.ctor DataCtor.cons [.var, .var]) joinConsBody)
      ⟨70, 19⟩ = some (joinConsArm, ⟨121, 22⟩) := by
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
      fixContext [] (.var ⟨3⟩) joinHoles joinClause.arms ⟨61, 19⟩ =
      some (joinArms, ⟨121, 22⟩) := by
  simp only [joinClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [join_nil_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [join_cons_arm_exact]
  rfl

private def joinClauseGenerated : GeneratedMatcherClause :=
  { holes := joinHoles
    evidence := joinHeader.evidence
    checks :=
      { hard := joinHeader.hard ++ joinNext.hard ++ joinArms.checks.hard
        pending := joinNext.pending ++ joinArms.checks.pending } }

theorem join_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨3⟩) joinClause ⟨56, 16⟩ =
      some (joinClauseGenerated, ⟨121, 22⟩) := by
  have shape : joinClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [joinClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
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

/-! ## Clause 6: whole-value capture -/

private def wholeValueHeader : GeneratedPPat :=
  { holes := []
    captures := [.var ⟨3⟩]
    evidence := none
    hard := [] }

private theorem whole_value_header_exact :
    elaboratePPat Paper1FrozenSignature.signature wholeValueClause.header
      (.var ⟨3⟩) none ⟨121, 22⟩ =
      some (wholeValueHeader, ⟨121, 22⟩) := by
  rfl'

private def wholeValueNext : GeneratedChecks :=
  { hard := []
    pending := [⟨.prod [], .prod []⟩] }

private theorem whole_value_next_exact :
    elaborateNextMatchersUsing callback
      (.mono (.var ⟨3⟩) :: fixContext)
      wholeValueClause.nextMatchers [] ⟨121, 22⟩ =
      some (wholeValueNext, ⟨121, 22⟩) := by
  rfl'

private def wholeValueBodyGenerated : Generated :=
  { target := TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 125 }],
     hard := [TypePM.Equation.ty
                (TypePM.Ty.var { index := 0 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 121 }) (TypePM.Ty.var { index := 122 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.slot (TypePM.Cap.var { index := 0 }) (TypePM.Ty.var { index := 1 }))
                  (TypePM.Ty.matcher (TypePM.Cap.var { index := 1 }) (TypePM.Ty.var { index := 2 })))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 123 }) (TypePM.Ty.var { index := 124 })),
              TypePM.Equation.ty
                (TypePM.Ty.prod
                  [TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 126 }],
                   TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 127 }]])
                (TypePM.Ty.prod [TypePM.Ty.var { index := 3 }, TypePM.Ty.var { index := 3 }]),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.var { index := 128 })
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 128 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 128 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 129 }) (TypePM.Ty.var { index := 130 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 130 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 132 }) (TypePM.Ty.var { index := 133 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 133 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 125 }]),
              TypePM.Equation.ty
                (TypePM.Ty.prod
                  [TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 134 }],
                   TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 137 }]])
                (TypePM.Ty.prod [TypePM.Ty.var { index := 3 }, TypePM.Ty.var { index := 3 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 135 }) (TypePM.Ty.var { index := 134 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 25 }) (TypePM.Cap.var { index := 24 }),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 136 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 134 }]),
              TypePM.Equation.cap
                (TypePM.Cap.var { index := 26 })
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 24 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 135 }) (TypePM.Ty.var { index := 137 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 28 }) (TypePM.Cap.var { index := 27 }),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 136 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 137 }]),
              TypePM.Equation.cap
                (TypePM.Cap.var { index := 29 })
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 27 }]),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.var { index := 138 })
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 138 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 138 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 139 }) (TypePM.Ty.var { index := 140 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 140 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 142 }) (TypePM.Ty.var { index := 143 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 143 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 125 }])],
     pending := [{ source := TypePM.Ty.slot (TypePM.Cap.var { index := 0 }) (TypePM.Ty.var { index := 1 }),
                   expected := TypePM.Ty.var { index := 121 } },
                 { source := TypePM.Ty.slot (TypePM.Cap.var { index := 0 }) (TypePM.Ty.var { index := 1 }),
                   expected := TypePM.Ty.var { index := 123 } },
                 { source := TypePM.Ty.prod [TypePM.Ty.var { index := 122 }, TypePM.Ty.var { index := 124 }],
                   expected := TypePM.Ty.slot
                                 (TypePM.Cap.prod
                                   [TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 22 }],
                                    TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 23 }]])
                                 (TypePM.Ty.prod [TypePM.Ty.var { index := 3 }, TypePM.Ty.var { index := 3 }]) },
                 { source := TypePM.Ty.prod [], expected := TypePM.Ty.var { index := 129 } },
                 { source := TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 131 }],
                   expected := TypePM.Ty.var { index := 132 } },
                 { source := TypePM.Ty.prod [TypePM.Ty.var { index := 122 }, TypePM.Ty.var { index := 124 }],
                   expected := TypePM.Ty.slot
                                 (TypePM.Cap.prod
                                   [TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 24 }],
                                    TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 27 }]])
                                 (TypePM.Ty.prod [TypePM.Ty.var { index := 3 }, TypePM.Ty.var { index := 3 }]) },
                 { source := TypePM.Ty.prod [], expected := TypePM.Ty.var { index := 139 } },
                 { source := TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 141 }],
                   expected := TypePM.Ty.var { index := 142 } }] }

private theorem whole_value_body_exact :
    callback
      (.mono (.var ⟨3⟩) :: .mono (.var ⟨3⟩) :: fixContext)
      wholeValueBody ⟨121, 22⟩ =
      some (wholeValueBodyGenerated, ⟨144, 30⟩) := by
  rfl'

private def wholeValueArm : GeneratedChecks :=
  { hard := wholeValueBodyGenerated.hard
    pending := wholeValueBodyGenerated.pending ++
      [⟨wholeValueBodyGenerated.target, DataTypes.list (.prod [])⟩] }

private theorem whole_value_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [.var ⟨3⟩] (.var ⟨3⟩) []
      (.mk .var wholeValueBody) ⟨121, 22⟩ =
      some (wholeValueArm, ⟨144, 30⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨3⟩)
      ⟨121, 22⟩ = some (⟨[.var ⟨3⟩], []⟩, ⟨121, 22⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [whole_value_body_exact]
  rfl

private def wholeValueArms : GeneratedArms :=
  ⟨wholeValueArm.append GeneratedChecks.empty⟩

private theorem whole_value_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [.var ⟨3⟩] (.var ⟨3⟩) [] wholeValueClause.arms
      ⟨121, 22⟩ = some (wholeValueArms, ⟨144, 30⟩) := by
  simp only [wholeValueClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [whole_value_arm_exact]
  rfl

private def wholeValueClauseGenerated : GeneratedMatcherClause :=
  { holes := []
    evidence := none
    checks :=
      { hard := wholeValueNext.hard ++ wholeValueArm.hard
        pending := wholeValueNext.pending ++ wholeValueArm.pending } }

theorem whole_value_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨3⟩) wholeValueClause ⟨121, 22⟩ =
      some (wholeValueClauseGenerated, ⟨144, 30⟩) := by
  have shape : wholeValueClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [wholeValueClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [whole_value_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, wholeValueHeader,
    Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [whole_value_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [whole_value_arms_exact]
  rfl

/-! ## Clause 7: final catch-all -/

private def catchHoles : List Dual :=
  [⟨.var ⟨30⟩, .var ⟨3⟩⟩]

private def catchHeader : GeneratedPPat :=
  { holes := catchHoles
    captures := []
    evidence := none
    hard := [] }

private theorem catch_header_exact :
    elaboratePPat Paper1FrozenSignature.signature catchAllClause.header
      (.var ⟨3⟩) none ⟨144, 30⟩ =
      some (catchHeader, ⟨144, 31⟩) := by
  rfl'

private def catchNext : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨.matcher .any (.var ⟨144⟩),
        .slot (.var ⟨30⟩) (.var ⟨3⟩)⟩] }

private theorem catch_next_exact :
    elaborateNextMatchersUsing callback fixContext
      catchAllClause.nextMatchers catchHoles ⟨144, 31⟩ =
      some (catchNext, ⟨145, 31⟩) := by
  rfl'

private def catchBody : Generated :=
  { target := .var ⟨150⟩
    hard :=
      [.ty
        (.fn (.var ⟨145⟩)
          (.fn (DataTypes.list (.var ⟨145⟩))
            (DataTypes.list (.var ⟨145⟩))))
        (.fn (.var ⟨146⟩) (.var ⟨147⟩)),
       .ty (.var ⟨147⟩) (.fn (.var ⟨149⟩) (.var ⟨150⟩))]
    pending :=
      [⟨.var ⟨3⟩, .var ⟨146⟩⟩,
       ⟨DataTypes.list (.var ⟨148⟩), .var ⟨149⟩⟩] }

private theorem catch_body_exact :
    callback (.mono (.var ⟨3⟩) :: fixContext)
      (sourceList [.var 0]) ⟨145, 31⟩ =
      some (catchBody, ⟨151, 31⟩) := by
  rfl'

private def catchArm : GeneratedChecks :=
  { hard := catchBody.hard
    pending := catchBody.pending ++
      [⟨catchBody.target, DataTypes.list (.var ⟨3⟩)⟩] }

private theorem catch_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) catchHoles
      (.mk .var (sourceList [.var 0])) ⟨145, 31⟩ =
      some (catchArm, ⟨151, 31⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨3⟩)
      ⟨145, 31⟩ = some (⟨[.var ⟨3⟩], []⟩, ⟨145, 31⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [catch_body_exact]
  rfl

private def catchArms : GeneratedArms :=
  ⟨catchArm.append GeneratedChecks.empty⟩

private theorem catch_arms_exact :
    elaborateMatcherArmsUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) catchHoles catchAllClause.arms
      ⟨145, 31⟩ = some (catchArms, ⟨151, 31⟩) := by
  simp only [catchAllClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [catch_arm_exact]
  rfl

private def catchClauseGenerated : GeneratedMatcherClause :=
  { holes := catchHoles
    evidence := none
    checks :=
      { hard := catchNext.hard ++ catchArm.hard
        pending := catchNext.pending ++ catchArm.pending } }

theorem catch_clause_exact :
    elaborateMatcherClauseUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨3⟩) catchAllClause ⟨144, 30⟩ =
      some (catchClauseGenerated, ⟨151, 31⟩) := by
  have shape : catchAllClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [catchAllClause, MatcherClause.toShape, MatcherArm.toHeader,
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

/-! ## Source-ordered traversal and the closed application -/

private def generatedClauses : GeneratedMatcherClauses :=
  { evidences :=
      [.con PatternFormer.list [.var ⟨3⟩],
       .con PatternFormer.list [.var ⟨4⟩],
       .con PatternFormer.list [.var ⟨6⟩],
       .con PatternFormer.list [.var ⟨8⟩],
       .con PatternFormer.list [.var ⟨16⟩]]
    checks := nilClauseGenerated.checks.append
      (headOnlyClauseGenerated.checks.append
        (valueConsClauseGenerated.checks.append
          (generalConsClauseGenerated.checks.append
            (joinClauseGenerated.checks.append
              (wholeValueClauseGenerated.checks.append
                (catchClauseGenerated.checks.append GeneratedChecks.empty)))))) }

theorem clauses_exact :
    elaborateMatcherClausesUsing callback Paper1FrozenSignature.signature
      fixContext (.var ⟨3⟩) multisetClauses ⟨4, 3⟩ =
      some (generatedClauses, ⟨151, 31⟩) := by
  simp only [multisetClauses, elaborateMatcherClausesUsing]
  rw [nil_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [head_only_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [value_cons_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [general_cons_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [join_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [whole_value_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [catch_clause_exact]
  rfl'

private def matcherLiteralGenerated : Generated :=
  { target := .matcher (.var ⟨2⟩) (.var ⟨3⟩)
    hard := evidenceEquations (.var ⟨2⟩) generatedClauses.evidences ++
      generatedClauses.checks.hard
    pending := generatedClauses.checks.pending }

theorem matcher_literal_exact :
    elaborateMatcherLiteralUsing callback Paper1FrozenSignature.signature
      fixContext multisetClauses ⟨3, 2⟩ =
      some (matcherLiteralGenerated, ⟨151, 31⟩) := by
  simp only [elaborateMatcherLiteralUsing,
    M4Paper1ComputabilityRegression.multiset_static_checks, if_true]
  rw [clauses_exact]
  rfl

private def multisetFixGenerated : Generated :=
  Generated.fromFix
    (.slot (.var ⟨0⟩) (.var ⟨1⟩))
    (.matcher (.var ⟨1⟩) (.var ⟨2⟩))
    matcherLiteralGenerated

private theorem multiset_fix_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 357 [.mono (.var ⟨0⟩)]
      multisetDefinition ⟨1, 0⟩ =
      some (multisetFixGenerated, ⟨151, 31⟩) := by
  simp only [multisetDefinition, M4.elaborateFuelUsing.eq_def,
    elaborateFixUsing,
    M4Paper1ComputabilityRegression.multiset_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing callback
      Paper1FrozenSignature.signature fixContext multisetClauses ⟨3, 2⟩).bind _ = _
  rw [matcher_literal_exact]
  rfl

def multisetFunctionGenerated : Generated :=
  Generated.fromLam (.var ⟨0⟩) multisetFixGenerated

private theorem multiset_function_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 358 [] multisetWithListArgument ⟨0, 0⟩ =
      some (multisetFunctionGenerated, ⟨151, 31⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 357 [.mono (.var ⟨0⟩)]
    multisetDefinition ⟨1, 0⟩).bind
      (fun output => some (Generated.fromLam (.var ⟨0⟩) output.1,
        output.2)) = _
  rw [multiset_fix_structural_fuel_exact]
  rfl

private def closedGenerated : Generated :=
  Generated.fromApp multisetFunctionGenerated
    M4Paper1ListExactRegression.shiftedListGenerated
    (.var ⟨237⟩) (.var ⟨238⟩)

theorem structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 359 [] closedMultisetDefinition ⟨0, 0⟩ =
      some (closedGenerated, ⟨239, 45⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 358 [] multisetWithListArgument ⟨0, 0⟩).bind
      (fun functionOutput =>
        (M4.elaborateFuelUsing (unifyWithFuel 500)
          Paper1FrozenSignature.signature 358 [] listMatcherDefinition
          functionOutput.2).bind
          (fun argumentOutput =>
            some (Generated.fromApp functionOutput.1 argumentOutput.1
              (.var ⟨argumentOutput.2.ty⟩)
              (.var ⟨argumentOutput.2.ty + 1⟩),
              argumentOutput.2.nextTy 2))) = _
  rw [multiset_function_structural_fuel_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [M4Paper1ListExactRegression.shifted_structural_fuel_exact]
  rfl

/-- Exact principal type of the closed Paper 1 `multiset` constructor. -/
def closedMultisetType : Ty :=
  .fn (.slot (.var ⟨27⟩) (.var ⟨111⟩))
    (.matcher (.con PatternFormer.list [.var ⟨27⟩])
      (DataTypes.list (.var ⟨111⟩)))

private theorem close_fuel_exact :
    (inferGeneratedUsing (unifyWithFuel 1000) closedGenerated).bind
      (fun closed => some closed.target) = some closedMultisetType := by
  simp only [closedGenerated, multisetFunctionGenerated, multisetFixGenerated,
    matcherLiteralGenerated, generatedClauses,
    nilClauseGenerated, headOnlyClauseGenerated,
    valueConsClauseGenerated, valueConsHeader, valueConsNext,
    valueConsArm, valueConsBody,
    generalConsClauseGenerated, generalConsHeader, generalConsNext,
    generalConsArm, generalConsBodyGenerated,
    joinClauseGenerated, joinHeader, joinNext, joinArms, joinNilArm,
    joinNilDPat, joinNilBody, joinConsArm, joinConsDPat,
    joinConsBodyGenerated,
    wholeValueClauseGenerated, wholeValueNext, wholeValueArm,
    wholeValueBodyGenerated,
    catchClauseGenerated, catchNext, catchArm, catchBody,
    M4Paper1ListExactRegression.shiftedListGenerated,
    Generated.fromLam, Generated.fromFix, Generated.fromApp,
    GeneratedChecks.append, GeneratedChecks.empty,
    evidenceEquations, List.append_assoc]
  rfl'

theorem infer_exact :
    M4.infer Paper1FrozenSignature.signature [] closedMultisetDefinition =
      some closedMultisetType := by
  have elaborated :=
    M4.elaborateFuel_success_of_solverFuel_success structural_fuel_exact
  cases closureEquality :
      inferGeneratedUsing (unifyWithFuel 1000) closedGenerated with
  | none =>
      have impossible := close_fuel_exact
      simp [closureEquality] at impossible
  | some closed =>
      have closedTarget : closed.target = closedMultisetType := by
        have exactTarget := close_fuel_exact
        simpa [closureEquality] using exactTarget
      have publicClosure :=
        inferGeneratedUsing_unify_of_fuel_success closureEquality
      unfold M4.infer M4.elaborate
      rw [M4Paper1ComputabilityRegression.closedMultisetDefinition_complexity]
      rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl]
      rw [elaborated]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [publicClosure]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [closedTarget]
      rfl

theorem typing :
    M4.Typing Paper1FrozenSignature.signature [] closedMultisetDefinition
      closedMultisetType :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed infer_exact

/-! ## The intentionally open definition -/

private def openCallback : ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 232

private def openFixContext : Context :=
  [.mono (.slot (.var ⟨0⟩) (.var ⟨0⟩)),
   .mono (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
     (.matcher (.var ⟨1⟩) (.var ⟨1⟩)))]

private def openShift : Subst :=
  { ty := fun index => .var ⟨index.index - 1⟩
    cap := fun index => .var index }

private def shiftPPat (generated : GeneratedPPat) : GeneratedPPat :=
  { holes := generated.holes.map (fun hole =>
      ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩)
    captures := generated.captures.map (Ty.apply openShift)
    evidence := generated.evidence.map (Cap.apply openShift.cap)
    hard := generated.hard.map (Equation.apply openShift) }

private def shiftChecks (checks : GeneratedChecks) : GeneratedChecks :=
  { hard := checks.hard.map (Equation.apply openShift)
    pending := checks.pending.map (CheckObligation.apply openShift) }

private def shiftGenerated (generated : Generated) : Generated :=
  { target := generated.target.apply openShift
    hard := generated.hard.map (Equation.apply openShift)
    pending := generated.pending.map (CheckObligation.apply openShift) }

private def shiftDPat (generated : GeneratedDPat) : GeneratedDPat :=
  { bindings := generated.bindings.map (Ty.apply openShift)
    hard := generated.hard.map (Equation.apply openShift) }

private def shiftArms (generated : GeneratedArms) : GeneratedArms :=
  ⟨shiftChecks generated.checks⟩

private def shiftClause (clause : GeneratedMatcherClause) :
    GeneratedMatcherClause :=
  { holes := clause.holes.map (fun hole =>
      ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩)
    evidence := clause.evidence.map (Cap.apply openShift.cap)
    checks := shiftChecks clause.checks }

private theorem open_shift_ty14 :
    (.var ⟨14⟩ : Ty).apply openShift = .var ⟨13⟩ := by
  rfl'

private theorem open_nil_header_exact :
    elaboratePPat Paper1FrozenSignature.signature nilClause.header
      (.var ⟨2⟩) none ⟨3, 3⟩ =
      some (shiftPPat nilHeader, ⟨4, 4⟩) := by
  rfl'

private theorem open_nil_next_exact :
    elaborateNextMatchersUsing openCallback openFixContext nilClause.nextMatchers
      [] ⟨4, 4⟩ = some (shiftChecks nilNext, ⟨4, 4⟩) := by
  rfl'

private theorem open_nil_first_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature (.ctor DataCtor.nil [])
      (.var ⟨2⟩) ⟨4, 4⟩ =
      some (shiftDPat nilFirstDPat, ⟨5, 4⟩) := by
  rfl'

private theorem open_nil_first_body_exact :
    openCallback openFixContext (sourceList [Paper1Programs.unit]) ⟨5, 4⟩ =
      some (shiftGenerated nilFirstBody, ⟨11, 4⟩) := by
  rfl'

private theorem open_nil_first_arm_exact :
    elaborateMatcherArmUsing openCallback Paper1FrozenSignature.signature
      openFixContext [] (.var ⟨2⟩) []
      (.mk (.ctor DataCtor.nil []) (sourceList [Paper1Programs.unit]))
      ⟨4, 4⟩ = some (shiftChecks nilFirstArm, ⟨11, 4⟩) := by
  simp only [elaborateMatcherArmUsing, open_nil_first_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, shiftDPat, nilFirstDPat,
    Pattern.extendContext, List.map_nil, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [open_nil_first_body_exact]
  rfl'

private theorem open_nil_second_arm_exact :
    elaborateMatcherArmUsing openCallback Paper1FrozenSignature.signature
      openFixContext [] (.var ⟨2⟩) [] (.mk .wild (sourceList []))
      ⟨11, 4⟩ = some (shiftChecks nilSecondArm, ⟨12, 4⟩) := by
  rfl'

private theorem open_nil_arms_exact :
    elaborateMatcherArmsUsing openCallback Paper1FrozenSignature.signature
      openFixContext [] (.var ⟨2⟩) [] nilClause.arms ⟨4, 4⟩ =
      some (shiftArms nilArms, ⟨12, 4⟩) := by
  simp only [nilClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [open_nil_first_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [open_nil_second_arm_exact]
  rfl'

private theorem open_nil_clause_exact :
    elaborateMatcherClauseUsing openCallback Paper1FrozenSignature.signature
      openFixContext (.var ⟨2⟩) nilClause ⟨3, 3⟩ =
      some (shiftClause nilClauseGenerated, ⟨12, 4⟩) := by
  have shape : nilClause.toShape.check Paper1FrozenSignature.signature = true := by
    simp [nilClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      ConstructorSchemes.listNil, ListPatternSchemes.nil,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [open_nil_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, shiftPPat, nilHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [open_nil_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [open_nil_arms_exact]
  rfl'

private def openHeadHoles : List Dual :=
  [⟨.var ⟨5⟩, .var ⟨12⟩⟩]

private def openHeadHeader : GeneratedPPat :=
  { holes := openHeadHoles
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨4⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨12⟩)) (.var ⟨2⟩),
       .cap (.var ⟨5⟩) (.var ⟨4⟩)] }

private theorem open_head_header_exact :
    elaboratePPat Paper1FrozenSignature.signature headOnlyClause.header
      (.var ⟨2⟩) none ⟨12, 4⟩ =
      some (openHeadHeader, ⟨13, 6⟩) := by
  rfl'

private def openHeadNext : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨0⟩),
        .slot (.var ⟨5⟩) (.var ⟨12⟩)⟩] }

private theorem open_head_next_exact :
    elaborateNextMatchersUsing openCallback openFixContext
      headOnlyClause.nextMatchers openHeadHoles ⟨13, 6⟩ =
      some (openHeadNext, ⟨13, 6⟩) := by
  rfl'

private def openHeadArm : GeneratedChecks :=
  { hard := []
    pending := [⟨.var ⟨2⟩, DataTypes.list (.var ⟨12⟩)⟩] }

private theorem open_head_arm_exact :
    elaborateMatcherArmUsing openCallback Paper1FrozenSignature.signature
      openFixContext [] (.var ⟨2⟩) openHeadHoles (.mk .var (.var 0))
      ⟨13, 6⟩ = some (openHeadArm, ⟨13, 6⟩) := by
  rfl'

private def openHeadArms : GeneratedArms :=
  ⟨openHeadArm.append GeneratedChecks.empty⟩

private theorem open_head_arms_exact :
    elaborateMatcherArmsUsing openCallback Paper1FrozenSignature.signature
      openFixContext [] (.var ⟨2⟩) openHeadHoles headOnlyClause.arms
      ⟨13, 6⟩ = some (openHeadArms, ⟨13, 6⟩) := by
  simp only [headOnlyClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [open_head_arm_exact]
  rfl

private def openHeadClause : GeneratedMatcherClause :=
  { holes := openHeadHoles
    evidence := openHeadHeader.evidence
    checks :=
      { hard := openHeadHeader.hard ++ openHeadNext.hard ++ openHeadArm.hard
        pending := openHeadNext.pending ++ openHeadArm.pending } }

private theorem open_head_clause_exact :
    elaborateMatcherClauseUsing openCallback Paper1FrozenSignature.signature
      openFixContext (.var ⟨2⟩) headOnlyClause ⟨12, 4⟩ =
      some (openHeadClause, ⟨13, 6⟩) := by
  have shape : headOnlyClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [headOnlyClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [open_head_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, openHeadHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [open_head_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [open_head_arms_exact]
  rfl

private theorem open_value_header_exact :
    elaboratePPat Paper1FrozenSignature.signature valueConsClause.header
      (.var ⟨2⟩) none ⟨13, 6⟩ =
      some (shiftPPat valueConsHeader, ⟨14, 8⟩) := by
  rfl'

private theorem open_value_next_exact :
    elaborateNextMatchersUsing openCallback
      (.mono (.var ⟨13⟩) :: openFixContext)
      valueConsClause.nextMatchers
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      ⟨14, 8⟩ = some (shiftChecks valueConsNext, ⟨16, 8⟩) := by
  rfl'

private theorem open_value_body_exact :
    openCallback
      (.mono (.var ⟨2⟩) :: .mono (.var ⟨13⟩) :: openFixContext)
      valueConsArmSource.body ⟨16, 8⟩ =
      some (shiftGenerated valueConsBody, ⟨40, 8⟩) := by
  rfl'

private theorem open_value_arm_exact :
    elaborateMatcherArmUsing openCallback Paper1FrozenSignature.signature
      openFixContext [.var ⟨13⟩] (.var ⟨2⟩)
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      valueConsArmSource ⟨16, 8⟩ =
      some (shiftChecks valueConsArm, ⟨40, 8⟩) := by
  rfl'

private theorem open_value_arms_exact :
    elaborateMatcherArmsUsing openCallback Paper1FrozenSignature.signature
      openFixContext [.var ⟨13⟩] (.var ⟨2⟩)
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      valueConsClause.arms ⟨16, 8⟩ =
      some (⟨shiftChecks valueConsArm |>.append GeneratedChecks.empty⟩,
        ⟨40, 8⟩) := by
  change elaborateMatcherArmsUsing openCallback
    Paper1FrozenSignature.signature openFixContext [.var ⟨13⟩]
    (.var ⟨2⟩)
    (valueConsHoles.map (fun hole =>
      ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
    [valueConsArmSource] ⟨16, 8⟩ = _
  simp only [elaborateMatcherArmsUsing]
  rw [open_value_arm_exact]
  rfl

private theorem open_value_clause_exact :
    elaborateMatcherClauseUsing openCallback Paper1FrozenSignature.signature
      openFixContext (.var ⟨2⟩) valueConsClause ⟨13, 6⟩ =
      some (shiftClause valueConsClauseGenerated, ⟨40, 8⟩) := by
  have shape : valueConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [valueConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [open_value_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, shiftPPat,
    valueConsHeader, Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [open_shift_ty14]
  rw [open_value_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [open_value_arms_exact]
  rfl'

private theorem open_general_header_exact :
    elaboratePPat Paper1FrozenSignature.signature generalConsClause.header
      (.var ⟨2⟩) none ⟨40, 8⟩ =
      some (shiftPPat generalConsHeader, ⟨41, 11⟩) := by
  rfl'

private theorem open_general_next_exact :
    elaborateNextMatchersUsing openCallback openFixContext
      generalConsClause.nextMatchers
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      ⟨41, 11⟩ = some (shiftChecks generalConsNext, ⟨43, 11⟩) := by
  rfl'

/-- The open definition first fails in the fourth matcher's arm body: its
recursive matcher variable is out of range without the outer list argument. -/
private theorem open_general_body_none :
    openCallback (.mono (.var ⟨2⟩) :: openFixContext)
      generalConsBody ⟨43, 11⟩ = none := by
  rfl'

private theorem open_general_arm_none :
    elaborateMatcherArmUsing openCallback Paper1FrozenSignature.signature
      openFixContext [] (.var ⟨2⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      (.mk .var generalConsBody) ⟨43, 11⟩ = none := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨2⟩)
      ⟨43, 11⟩ = some (⟨[.var ⟨2⟩], []⟩, ⟨43, 11⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [open_general_body_none]
  rfl

private theorem open_general_arms_none :
    elaborateMatcherArmsUsing openCallback Paper1FrozenSignature.signature
      openFixContext [] (.var ⟨2⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      generalConsClause.arms ⟨43, 11⟩ = none := by
  simp only [generalConsClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [open_general_arm_none]
  rfl

private theorem open_general_clause_none :
    elaborateMatcherClauseUsing openCallback Paper1FrozenSignature.signature
      openFixContext (.var ⟨2⟩) generalConsClause ⟨40, 8⟩ = none := by
  have shape : generalConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [generalConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [open_general_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, shiftPPat,
    generalConsHeader, Pattern.extendContext, List.map_nil,
    List.nil_append]
  rw [open_general_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [open_general_arms_none]
  rfl

private theorem open_clauses_none :
    elaborateMatcherClausesUsing openCallback
      Paper1FrozenSignature.signature openFixContext (.var ⟨2⟩)
      multisetClauses ⟨3, 3⟩ = none := by
  simp only [multisetClauses, elaborateMatcherClausesUsing]
  rw [open_nil_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [open_head_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [open_value_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [open_general_clause_none]
  rfl

private theorem open_matcher_literal_none :
    elaborateMatcherLiteralUsing openCallback
      Paper1FrozenSignature.signature openFixContext multisetClauses
      ⟨2, 2⟩ = none := by
  simp only [elaborateMatcherLiteralUsing,
    M4Paper1ComputabilityRegression.multiset_static_checks, if_true]
  rw [open_clauses_none]
  rfl

theorem open_structural_fuel_none :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 234 [] multisetDefinition ⟨0, 0⟩ =
      none := by
  simp only [multisetDefinition, M4.elaborateFuelUsing.eq_def,
    elaborateFixUsing,
    M4Paper1ComputabilityRegression.multiset_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing openCallback
    Paper1FrozenSignature.signature openFixContext multisetClauses
    ⟨2, 2⟩).bind _ = none
  rw [open_matcher_literal_none]
  rfl

private def openPublicCallback : ExpressionElaborator :=
  M4.elaborateFuel Paper1FrozenSignature.signature 232

private theorem open_callback_transport :
    M4.ElaboratorSuccessTransport openCallback openPublicCallback := by
  intro context expression supply generated next success
  exact M4.elaborateFuel_success_of_solverFuel_success success

private theorem public_open_nil_clause_exact :
    elaborateMatcherClauseUsing openPublicCallback
      Paper1FrozenSignature.signature openFixContext (.var ⟨2⟩) nilClause
      ⟨3, 3⟩ = some (shiftClause nilClauseGenerated, ⟨12, 4⟩) :=
  MatcherTyping.elaborateMatcherClauseUsing_success_transport
    open_callback_transport open_nil_clause_exact

private theorem public_open_head_clause_exact :
    elaborateMatcherClauseUsing openPublicCallback
      Paper1FrozenSignature.signature openFixContext (.var ⟨2⟩)
      headOnlyClause ⟨12, 4⟩ = some (openHeadClause, ⟨13, 6⟩) :=
  MatcherTyping.elaborateMatcherClauseUsing_success_transport
    open_callback_transport open_head_clause_exact

private theorem public_open_value_clause_exact :
    elaborateMatcherClauseUsing openPublicCallback
      Paper1FrozenSignature.signature openFixContext (.var ⟨2⟩)
      valueConsClause ⟨13, 6⟩ =
      some (shiftClause valueConsClauseGenerated, ⟨40, 8⟩) :=
  MatcherTyping.elaborateMatcherClauseUsing_success_transport
    open_callback_transport open_value_clause_exact

private theorem public_open_general_next_exact :
    elaborateNextMatchersUsing openPublicCallback openFixContext
      generalConsClause.nextMatchers
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      ⟨41, 11⟩ = some (shiftChecks generalConsNext, ⟨43, 11⟩) :=
  MatcherTyping.elaborateNextMatchersUsing_success_transport
    open_callback_transport open_general_next_exact

private theorem public_open_general_body_none :
    openPublicCallback (.mono (.var ⟨2⟩) :: openFixContext)
      generalConsBody ⟨43, 11⟩ = none := by
  rfl'

private theorem public_open_general_arm_none :
    elaborateMatcherArmUsing openPublicCallback
      Paper1FrozenSignature.signature openFixContext [] (.var ⟨2⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      (.mk .var generalConsBody) ⟨43, 11⟩ = none := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨2⟩)
      ⟨43, 11⟩ = some (⟨[.var ⟨2⟩], []⟩, ⟨43, 11⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [public_open_general_body_none]
  rfl

private theorem public_open_general_arms_none :
    elaborateMatcherArmsUsing openPublicCallback
      Paper1FrozenSignature.signature openFixContext [] (.var ⟨2⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      generalConsClause.arms ⟨43, 11⟩ = none := by
  simp only [generalConsClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [public_open_general_arm_none]
  rfl

private theorem public_open_general_clause_none :
    elaborateMatcherClauseUsing openPublicCallback
      Paper1FrozenSignature.signature openFixContext (.var ⟨2⟩)
      generalConsClause ⟨40, 8⟩ = none := by
  have shape : generalConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [generalConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [open_general_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, shiftPPat,
    generalConsHeader, Pattern.extendContext, List.map_nil,
    List.nil_append]
  rw [public_open_general_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [public_open_general_arms_none]
  rfl

private theorem public_open_clauses_none :
    elaborateMatcherClausesUsing openPublicCallback
      Paper1FrozenSignature.signature openFixContext (.var ⟨2⟩)
      multisetClauses ⟨3, 3⟩ = none := by
  simp only [multisetClauses, elaborateMatcherClausesUsing]
  rw [public_open_nil_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [public_open_head_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [public_open_value_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [public_open_general_clause_none]
  rfl

private theorem public_open_matcher_literal_none :
    elaborateMatcherLiteralUsing openPublicCallback
      Paper1FrozenSignature.signature openFixContext multisetClauses
      ⟨2, 2⟩ = none := by
  simp only [elaborateMatcherLiteralUsing,
    M4Paper1ComputabilityRegression.multiset_static_checks, if_true]
  rw [public_open_clauses_none]
  rfl

private theorem public_open_structural_fuel_none :
    M4.elaborateFuel Paper1FrozenSignature.signature 234 []
      multisetDefinition ⟨0, 0⟩ = none := by
  simp only [M4.elaborateFuel, multisetDefinition,
    M4.elaborateFuelUsing.eq_def, elaborateFixUsing,
    M4Paper1ComputabilityRegression.multiset_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing openPublicCallback
    Paper1FrozenSignature.signature openFixContext multisetClauses
    ⟨2, 2⟩).bind _ = none
  rw [public_open_matcher_literal_none]
  rfl

/-- The intentionally open Paper 1 `multiset` definition does not infer in
the empty context. -/
theorem open_infer_none :
    M4.infer Paper1FrozenSignature.signature [] multisetDefinition = none := by
  unfold M4.infer M4.elaborate
  rw [M4Paper1ComputabilityRegression.multisetDefinition_complexity]
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl]
  rw [public_open_structural_fuel_none]
  rfl

/-! ## Closed definition at the P1-L05 fresh-variable origin -/

private def origin19Substitution : Subst :=
  M4Paper1ListExactRegression.supplyShiftSubstitution ⟨19, 3⟩

private def origin19Callback : ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 355

private def origin19FixContext : Context :=
  fixContext.applyFree origin19Substitution

private def translatePPat19 (generated : GeneratedPPat) : GeneratedPPat :=
  { holes := generated.holes.map (fun hole =>
      ⟨hole.capability.apply origin19Substitution.cap,
        hole.target.apply origin19Substitution⟩)
    captures := generated.captures.map (Ty.apply origin19Substitution)
    evidence := generated.evidence.map (Cap.apply origin19Substitution.cap)
    hard := generated.hard.map (Equation.apply origin19Substitution) }

private def translateChecks19 (checks : GeneratedChecks) : GeneratedChecks :=
  { hard := checks.hard.map (Equation.apply origin19Substitution)
    pending := checks.pending.map
      (CheckObligation.apply origin19Substitution) }

private def translateDPat19 (generated : GeneratedDPat) : GeneratedDPat :=
  { bindings := generated.bindings.map (Ty.apply origin19Substitution)
    hard := generated.hard.map (Equation.apply origin19Substitution) }

private def translateGenerated19 (generated : Generated) : Generated :=
  M4Paper1ListExactRegression.translateGenerated ⟨19, 3⟩ generated

private def translateArms19 (arms : GeneratedArms) : GeneratedArms :=
  ⟨translateChecks19 arms.checks⟩

private def translateClause19
    (clause : GeneratedMatcherClause) : GeneratedMatcherClause :=
  { holes := clause.holes.map (fun hole =>
      ⟨hole.capability.apply origin19Substitution.cap,
        hole.target.apply origin19Substitution⟩)
    evidence := clause.evidence.map (Cap.apply origin19Substitution.cap)
    checks := translateChecks19 clause.checks }

private theorem origin19_nil_header_exact :
    elaboratePPat Paper1FrozenSignature.signature nilClause.header
      (.var ⟨22⟩) none ⟨23, 6⟩ =
      some (translatePPat19 nilHeader, ⟨24, 7⟩) := by
  rfl'

private theorem origin19_nil_next_exact :
    elaborateNextMatchersUsing origin19Callback origin19FixContext
      nilClause.nextMatchers [] ⟨24, 7⟩ =
      some (translateChecks19 nilNext, ⟨24, 7⟩) := by
  rfl'

private theorem origin19_nil_first_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature (.ctor DataCtor.nil [])
      (.var ⟨22⟩) ⟨24, 7⟩ =
      some (translateDPat19 nilFirstDPat, ⟨25, 7⟩) := by
  rfl'

private theorem origin19_nil_first_body_exact :
    origin19Callback origin19FixContext
      (sourceList [Paper1Programs.unit]) ⟨25, 7⟩ =
      some (translateGenerated19 nilFirstBody, ⟨31, 7⟩) := by
  rfl'

private theorem origin19_nil_first_arm_exact :
    elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩) []
      (.mk (.ctor DataCtor.nil []) (sourceList [Paper1Programs.unit]))
      ⟨24, 7⟩ = some (translateChecks19 nilFirstArm, ⟨31, 7⟩) := by
  simp only [elaborateMatcherArmUsing, origin19_nil_first_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, translateDPat19, nilFirstDPat,
    Pattern.extendContext, List.map_nil, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [origin19_nil_first_body_exact]
  rfl'

private theorem origin19_nil_second_arm_exact :
    elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩) []
      (.mk .wild (sourceList [])) ⟨31, 7⟩ =
      some (translateChecks19 nilSecondArm, ⟨32, 7⟩) := by
  rfl'

private theorem origin19_nil_arms_exact :
    elaborateMatcherArmsUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩) []
      nilClause.arms ⟨24, 7⟩ =
      some (translateArms19 nilArms, ⟨32, 7⟩) := by
  simp only [nilClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [origin19_nil_first_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_nil_second_arm_exact]
  rfl'

private theorem origin19_nil_clause_exact :
    elaborateMatcherClauseUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext (.var ⟨22⟩)
      nilClause ⟨23, 6⟩ =
      some (translateClause19 nilClauseGenerated, ⟨32, 7⟩) := by
  have shape : nilClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [nilClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      ConstructorSchemes.listNil, ListPatternSchemes.nil,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin19_nil_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat19,
    nilHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [origin19_nil_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_nil_arms_exact]
  rfl'

private theorem origin19_head_clause_exact :
    elaborateMatcherClauseUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext (.var ⟨22⟩)
      headOnlyClause ⟨32, 7⟩ =
      some (translateClause19 headOnlyClauseGenerated, ⟨33, 9⟩) := by
  let header : GeneratedPPat := translatePPat19
    { holes := headOnlyHoles
      captures := []
      evidence := some (.con PatternFormer.list [.var ⟨4⟩])
      hard :=
        [.ty (DataTypes.list (.var ⟨13⟩)) (.var ⟨3⟩),
         .cap (.var ⟨5⟩) (.var ⟨4⟩)] }
  have headerExact : elaboratePPat Paper1FrozenSignature.signature
      headOnlyClause.header (.var ⟨22⟩) none ⟨32, 7⟩ =
      some (header, ⟨33, 9⟩) := by
    rfl'
  let holes : List Dual := headOnlyHoles.map (fun hole =>
    ⟨hole.capability.apply origin19Substitution.cap,
      hole.target.apply origin19Substitution⟩)
  let next : GeneratedChecks := translateChecks19
    { hard := []
      pending :=
        [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩),
          .slot (.var ⟨5⟩) (.var ⟨13⟩)⟩] }
  have nextExact : elaborateNextMatchersUsing origin19Callback
      origin19FixContext headOnlyClause.nextMatchers holes ⟨33, 9⟩ =
      some (next, ⟨33, 9⟩) := by
    rfl'
  let arm : GeneratedChecks := translateChecks19
    { hard := []
      pending := [⟨.var ⟨3⟩, DataTypes.list (.var ⟨13⟩)⟩] }
  have armExact : elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      holes (.mk .var (.var 0)) ⟨33, 9⟩ = some (arm, ⟨33, 9⟩) := by
    rfl'
  let arms : GeneratedArms := ⟨arm.append GeneratedChecks.empty⟩
  have armsExact : elaborateMatcherArmsUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      holes headOnlyClause.arms ⟨33, 9⟩ = some (arms, ⟨33, 9⟩) := by
    simp only [headOnlyClause, MatcherClause.arms,
      elaborateMatcherArmsUsing]
    rw [armExact]
    rfl
  have shape : headOnlyClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [headOnlyClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [headerExact]
  simp only [Option.bind_eq_bind, Option.bind_some, header, translatePPat19,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [nextExact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [armsExact]
  rfl'

private theorem origin19_value_header_exact :
    elaboratePPat Paper1FrozenSignature.signature valueConsClause.header
      (.var ⟨22⟩) none ⟨33, 9⟩ =
      some (translatePPat19 valueConsHeader, ⟨34, 11⟩) := by
  rfl'

private theorem origin19_value_next_exact :
    elaborateNextMatchersUsing origin19Callback
      (.mono ((Ty.var ⟨14⟩).apply origin19Substitution) :: origin19FixContext)
      valueConsClause.nextMatchers
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      ⟨34, 11⟩ = some (translateChecks19 valueConsNext, ⟨36, 11⟩) := by
  rfl'

private theorem origin19_value_arm_exact :
    elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext
      (valueConsHeader.captures.map (Ty.apply origin19Substitution))
      (.var ⟨22⟩)
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      valueConsArmSource ⟨36, 11⟩ =
      some (translateChecks19 valueConsArm, ⟨60, 11⟩) := by
  rfl'

private theorem origin19_value_arms_exact :
    elaborateMatcherArmsUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext
      [(Ty.var ⟨14⟩).apply origin19Substitution]
      (.var ⟨22⟩)
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      valueConsClause.arms ⟨36, 11⟩ =
      some (translateArms19 valueConsArms, ⟨60, 11⟩) := by
  change elaborateMatcherArmsUsing origin19Callback
    Paper1FrozenSignature.signature origin19FixContext
    (valueConsHeader.captures.map (Ty.apply origin19Substitution))
    (.var ⟨22⟩)
    (valueConsHoles.map (fun hole =>
      ⟨hole.capability.apply origin19Substitution.cap,
        hole.target.apply origin19Substitution⟩))
    [valueConsArmSource] ⟨36, 11⟩ = _
  simp only [elaborateMatcherArmsUsing]
  rw [origin19_value_arm_exact]
  rfl'

private theorem origin19_value_clause_exact :
    elaborateMatcherClauseUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext (.var ⟨22⟩)
      valueConsClause ⟨33, 9⟩ =
      some (translateClause19 valueConsClauseGenerated, ⟨60, 11⟩) := by
  have shape : valueConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [valueConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin19_value_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat19,
    valueConsHeader, Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [origin19_value_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_value_arms_exact]
  rfl'

private theorem origin19_general_header_exact :
    elaboratePPat Paper1FrozenSignature.signature generalConsClause.header
      (.var ⟨22⟩) none ⟨60, 11⟩ =
      some (translatePPat19 generalConsHeader, ⟨61, 14⟩) := by
  rfl'

private theorem origin19_general_next_exact :
    elaborateNextMatchersUsing origin19Callback origin19FixContext
      generalConsClause.nextMatchers
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      ⟨61, 14⟩ = some (translateChecks19 generalConsNext, ⟨63, 14⟩) := by
  rfl'

private theorem origin19_general_body_exact :
    origin19Callback (.mono (.var ⟨22⟩) :: origin19FixContext)
      generalConsBody ⟨63, 14⟩ =
      some (translateGenerated19 generalConsBodyGenerated, ⟨75, 19⟩) := by
  rfl'

private theorem origin19_general_arm_exact :
    elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      (.mk .var generalConsBody) ⟨63, 14⟩ =
      some (translateChecks19 generalConsArm, ⟨75, 19⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨22⟩)
      ⟨63, 14⟩ = some (⟨[.var ⟨22⟩], []⟩, ⟨63, 14⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [origin19_general_body_exact]
  rfl'

private theorem origin19_general_arms_exact :
    elaborateMatcherArmsUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      generalConsClause.arms ⟨63, 14⟩ =
      some (translateArms19 generalConsArms, ⟨75, 19⟩) := by
  simp only [generalConsClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [origin19_general_arm_exact]
  rfl'

private theorem origin19_general_clause_exact :
    elaborateMatcherClauseUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext (.var ⟨22⟩)
      generalConsClause ⟨60, 11⟩ =
      some (translateClause19 generalConsClauseGenerated, ⟨75, 19⟩) := by
  have shape : generalConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [generalConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin19_general_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat19,
    generalConsHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [origin19_general_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_general_arms_exact]
  rfl'

private theorem origin19_join_header_exact :
    elaboratePPat Paper1FrozenSignature.signature joinClause.header
      (.var ⟨22⟩) none ⟨75, 19⟩ =
      some (translatePPat19 joinHeader, ⟨76, 22⟩) := by
  rfl'

private theorem origin19_join_next_exact :
    elaborateNextMatchersUsing origin19Callback origin19FixContext
      joinClause.nextMatchers
      (joinHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      ⟨76, 22⟩ = some (translateChecks19 joinNext, ⟨80, 22⟩) := by
  rfl'

private theorem origin19_join_nil_arm_exact :
    elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      (joinHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      (.mk (.ctor DataCtor.nil [])
        (sourceList [.tuple [sourceList [], sourceList []]]))
      ⟨80, 22⟩ = some (translateChecks19 joinNilArm, ⟨89, 22⟩) := by
  rfl'

private theorem origin19_join_cons_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature
      (.ctor DataCtor.cons [.var, .var]) (.var ⟨22⟩) ⟨89, 22⟩ =
      some (translateDPat19 joinConsDPat, ⟨90, 22⟩) := by
  rfl'

private theorem origin19_join_cons_body_exact :
    origin19Callback
      (.mono ((Ty.var ⟨70⟩).apply origin19Substitution) ::
        .mono ((DataTypes.list (.var ⟨70⟩)).apply origin19Substitution) ::
        origin19FixContext)
      joinConsBody ⟨90, 22⟩ =
      some (translateGenerated19 joinConsBodyGenerated, ⟨140, 25⟩) := by
  rfl'

private theorem origin19_join_cons_arm_exact :
    elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      (joinHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      (.mk (.ctor DataCtor.cons [.var, .var]) joinConsBody)
      ⟨89, 22⟩ = some (translateChecks19 joinConsArm, ⟨140, 25⟩) := by
  simp only [elaborateMatcherArmUsing, origin19_join_cons_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, translateDPat19, joinConsDPat,
    Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, elaborateCheckedExpressionUsing]
  rw [origin19_join_cons_body_exact]
  rfl'

private theorem origin19_join_arms_exact :
    elaborateMatcherArmsUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      (joinHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      joinClause.arms ⟨80, 22⟩ =
      some (translateArms19 joinArms, ⟨140, 25⟩) := by
  simp only [joinClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [origin19_join_nil_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_join_cons_arm_exact]
  rfl'

private theorem origin19_join_clause_exact :
    elaborateMatcherClauseUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext (.var ⟨22⟩)
      joinClause ⟨75, 19⟩ =
      some (translateClause19 joinClauseGenerated, ⟨140, 25⟩) := by
  have shape : joinClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [joinClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      Paper1FrozenSignature.lookup_data_cons, ConstructorSchemes.listNil,
      ConstructorSchemes.listCons, ListPatternSchemes.join,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin19_join_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat19,
    joinHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [origin19_join_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_join_arms_exact]
  rfl'

private theorem origin19_whole_header_exact :
    elaboratePPat Paper1FrozenSignature.signature wholeValueClause.header
      (.var ⟨22⟩) none ⟨140, 25⟩ =
      some (translatePPat19 wholeValueHeader, ⟨140, 25⟩) := by
  rfl'

private theorem origin19_whole_next_exact :
    elaborateNextMatchersUsing origin19Callback
      (.mono ((Ty.var ⟨3⟩).apply origin19Substitution) :: origin19FixContext)
      wholeValueClause.nextMatchers [] ⟨140, 25⟩ =
      some (translateChecks19 wholeValueNext, ⟨140, 25⟩) := by
  rfl'

private theorem origin19_whole_body_exact :
    origin19Callback
      (.mono (.var ⟨22⟩) ::
        .mono ((Ty.var ⟨3⟩).apply origin19Substitution) ::
        origin19FixContext)
      wholeValueBody ⟨140, 25⟩ =
      some (translateGenerated19 wholeValueBodyGenerated, ⟨163, 33⟩) := by
  rfl'

private theorem origin19_whole_arm_exact :
    elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext
      [(Ty.var ⟨3⟩).apply origin19Substitution]
      (.var ⟨22⟩) [] (.mk .var wholeValueBody) ⟨140, 25⟩ =
      some (translateChecks19 wholeValueArm, ⟨163, 33⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨22⟩)
      ⟨140, 25⟩ = some (⟨[.var ⟨22⟩], []⟩, ⟨140, 25⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [origin19_whole_body_exact]
  rfl'

private theorem origin19_whole_arms_exact :
    elaborateMatcherArmsUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext
      [(Ty.var ⟨3⟩).apply origin19Substitution]
      (.var ⟨22⟩) [] wholeValueClause.arms ⟨140, 25⟩ =
      some (translateArms19 wholeValueArms, ⟨163, 33⟩) := by
  simp only [wholeValueClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [origin19_whole_arm_exact]
  rfl'

private theorem origin19_whole_clause_exact :
    elaborateMatcherClauseUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext (.var ⟨22⟩)
      wholeValueClause ⟨140, 25⟩ =
      some (translateClause19 wholeValueClauseGenerated, ⟨163, 33⟩) := by
  have shape : wholeValueClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [wholeValueClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin19_whole_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat19,
    wholeValueHeader, Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [origin19_whole_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_whole_arms_exact]
  rfl'

private theorem origin19_catch_header_exact :
    elaboratePPat Paper1FrozenSignature.signature catchAllClause.header
      (.var ⟨22⟩) none ⟨163, 33⟩ =
      some (translatePPat19 catchHeader, ⟨163, 34⟩) := by
  rfl'

private theorem origin19_catch_next_exact :
    elaborateNextMatchersUsing origin19Callback origin19FixContext
      catchAllClause.nextMatchers
      (catchHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      ⟨163, 34⟩ = some (translateChecks19 catchNext, ⟨164, 34⟩) := by
  rfl'

private theorem origin19_catch_body_exact :
    origin19Callback (.mono (.var ⟨22⟩) :: origin19FixContext)
      (sourceList [.var 0]) ⟨164, 34⟩ =
      some (translateGenerated19 catchBody, ⟨170, 34⟩) := by
  rfl'

private theorem origin19_catch_arm_exact :
    elaborateMatcherArmUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      (catchHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      (.mk .var (sourceList [.var 0])) ⟨164, 34⟩ =
      some (translateChecks19 catchArm, ⟨170, 34⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨22⟩)
      ⟨164, 34⟩ = some (⟨[.var ⟨22⟩], []⟩, ⟨164, 34⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [origin19_catch_body_exact]
  rfl'

private theorem origin19_catch_arms_exact :
    elaborateMatcherArmsUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext [] (.var ⟨22⟩)
      (catchHoles.map (fun hole =>
        ⟨hole.capability.apply origin19Substitution.cap,
          hole.target.apply origin19Substitution⟩))
      catchAllClause.arms ⟨164, 34⟩ =
      some (translateArms19 catchArms, ⟨170, 34⟩) := by
  simp only [catchAllClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [origin19_catch_arm_exact]
  rfl'

private theorem origin19_catch_clause_exact :
    elaborateMatcherClauseUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext (.var ⟨22⟩)
      catchAllClause ⟨163, 33⟩ =
      some (translateClause19 catchClauseGenerated, ⟨170, 34⟩) := by
  have shape : catchAllClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [catchAllClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin19_catch_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat19,
    catchHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [origin19_catch_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_catch_arms_exact]
  rfl'

private def translateClauses19
    (clauses : GeneratedMatcherClauses) : GeneratedMatcherClauses :=
  { evidences := clauses.evidences.map
      (Cap.apply origin19Substitution.cap)
    checks := translateChecks19 clauses.checks }

private theorem origin19_clauses_exact :
    elaborateMatcherClausesUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext (.var ⟨22⟩)
      multisetClauses ⟨23, 6⟩ =
      some (translateClauses19 generatedClauses, ⟨170, 34⟩) := by
  simp only [multisetClauses, elaborateMatcherClausesUsing]
  rw [origin19_nil_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_head_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_value_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_general_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_join_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_whole_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin19_catch_clause_exact]
  rfl'

private theorem origin19_matcher_literal_exact :
    elaborateMatcherLiteralUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext multisetClauses
      ⟨22, 5⟩ =
      some (translateGenerated19 matcherLiteralGenerated, ⟨170, 34⟩) := by
  simp only [elaborateMatcherLiteralUsing,
    M4Paper1ComputabilityRegression.multiset_static_checks, if_true]
  rw [origin19_clauses_exact]
  rfl'

private theorem origin19_fix_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 357 [.mono (.var ⟨19⟩)]
      multisetDefinition ⟨20, 3⟩ =
      some (translateGenerated19 multisetFixGenerated, ⟨170, 34⟩) := by
  simp only [multisetDefinition, M4.elaborateFuelUsing.eq_def,
    elaborateFixUsing,
    M4Paper1ComputabilityRegression.multiset_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing origin19Callback
      Paper1FrozenSignature.signature origin19FixContext multisetClauses
      ⟨22, 5⟩).bind _ = _
  rw [origin19_matcher_literal_exact]
  rfl'

/-- The generated block for the closed multiset function, translated to a
concrete fresh-variable origin without duplicating its seven clause blocks. -/
def multisetFunctionGeneratedAt (start : Supply) : Generated :=
  M4Paper1ListExactRegression.translateGenerated start
    multisetFunctionGenerated

/-- Exact executable multiset-function elaboration at the P1-L05 matcher's
fresh-variable origin. -/
theorem multiset_function_origin19_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 358 [] multisetWithListArgument ⟨19, 3⟩ =
      some (multisetFunctionGeneratedAt ⟨19, 3⟩, ⟨170, 34⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 357 [.mono (.var ⟨19⟩)]
    multisetDefinition ⟨20, 3⟩).bind
      (fun output => some (Generated.fromLam (.var ⟨19⟩) output.1,
        output.2)) = _
  rw [origin19_fix_structural_fuel_exact]
  rfl'

def closedGeneratedAt19 : Generated :=
  Generated.fromApp (multisetFunctionGeneratedAt ⟨19, 3⟩)
    (M4Paper1ListExactRegression.listGeneratedAt ⟨170, 34⟩)
    (.var ⟨256⟩) (.var ⟨257⟩)

/-- Exact closed multiset-constructor elaboration at the P1-L05 origin. -/
theorem closed_origin19_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 359 [] closedMultisetDefinition ⟨19, 3⟩ =
      some (closedGeneratedAt19, ⟨258, 48⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 358 [] multisetWithListArgument
    ⟨19, 3⟩).bind
      (fun functionOutput =>
        (M4.elaborateFuelUsing (unifyWithFuel 500)
          Paper1FrozenSignature.signature 358 [] listMatcherDefinition
          functionOutput.2).bind
          (fun argumentOutput =>
            some (Generated.fromApp functionOutput.1 argumentOutput.1
              (.var ⟨argumentOutput.2.ty⟩)
              (.var ⟨argumentOutput.2.ty + 1⟩),
              argumentOutput.2.nextTy 2))) = _
  rw [multiset_function_origin19_structural_fuel_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have listAt358 := M4.elaborateFuelUsing_success_mono
    (solveHard := unifyWithFuel 500)
    (signature := Paper1FrozenSignature.signature)
    (smaller := 124) (larger := 358) (by omega)
    M4Paper1ListExactRegression.closed170_structural_fuel_exact
  rw [listAt358]
  rfl



/-! ## Closed definition at the P1-L02 fresh-variable origin -/

private def origin29Substitution : Subst :=
  M4Paper1ListExactRegression.supplyShiftSubstitution ⟨29, 5⟩

private def origin29Callback : ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 355

private def origin29FixContext : Context :=
  fixContext.applyFree origin29Substitution

private def translatePPat29 (generated : GeneratedPPat) : GeneratedPPat :=
  { holes := generated.holes.map (fun hole =>
      ⟨hole.capability.apply origin29Substitution.cap,
        hole.target.apply origin29Substitution⟩)
    captures := generated.captures.map (Ty.apply origin29Substitution)
    evidence := generated.evidence.map (Cap.apply origin29Substitution.cap)
    hard := generated.hard.map (Equation.apply origin29Substitution) }

private def translateChecks29 (checks : GeneratedChecks) : GeneratedChecks :=
  { hard := checks.hard.map (Equation.apply origin29Substitution)
    pending := checks.pending.map
      (CheckObligation.apply origin29Substitution) }

private def translateDPat29 (generated : GeneratedDPat) : GeneratedDPat :=
  { bindings := generated.bindings.map (Ty.apply origin29Substitution)
    hard := generated.hard.map (Equation.apply origin29Substitution) }

private def translateGenerated29 (generated : Generated) : Generated :=
  M4Paper1ListExactRegression.translateGenerated ⟨29, 5⟩ generated

private def translateArms29 (arms : GeneratedArms) : GeneratedArms :=
  ⟨translateChecks29 arms.checks⟩

private def translateClause29
    (clause : GeneratedMatcherClause) : GeneratedMatcherClause :=
  { holes := clause.holes.map (fun hole =>
      ⟨hole.capability.apply origin29Substitution.cap,
        hole.target.apply origin29Substitution⟩)
    evidence := clause.evidence.map (Cap.apply origin29Substitution.cap)
    checks := translateChecks29 clause.checks }

private theorem origin29_nil_header_exact :
    elaboratePPat Paper1FrozenSignature.signature nilClause.header
      (.var ⟨32⟩) none ⟨33, 8⟩ =
      some (translatePPat29 nilHeader, ⟨34, 9⟩) := by
  rfl'

private theorem origin29_nil_next_exact :
    elaborateNextMatchersUsing origin29Callback origin29FixContext
      nilClause.nextMatchers [] ⟨34, 9⟩ =
      some (translateChecks29 nilNext, ⟨34, 9⟩) := by
  rfl'

private theorem origin29_nil_first_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature (.ctor DataCtor.nil [])
      (.var ⟨32⟩) ⟨34, 9⟩ =
      some (translateDPat29 nilFirstDPat, ⟨35, 9⟩) := by
  rfl'

private theorem origin29_nil_first_body_exact :
    origin29Callback origin29FixContext
      (sourceList [Paper1Programs.unit]) ⟨35, 9⟩ =
      some (translateGenerated29 nilFirstBody, ⟨41, 9⟩) := by
  rfl'

private theorem origin29_nil_first_arm_exact :
    elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩) []
      (.mk (.ctor DataCtor.nil []) (sourceList [Paper1Programs.unit]))
      ⟨34, 9⟩ = some (translateChecks29 nilFirstArm, ⟨41, 9⟩) := by
  simp only [elaborateMatcherArmUsing, origin29_nil_first_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, translateDPat29, nilFirstDPat,
    Pattern.extendContext, List.map_nil, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [origin29_nil_first_body_exact]
  rfl'

private theorem origin29_nil_second_arm_exact :
    elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩) []
      (.mk .wild (sourceList [])) ⟨41, 9⟩ =
      some (translateChecks29 nilSecondArm, ⟨42, 9⟩) := by
  rfl'

private theorem origin29_nil_arms_exact :
    elaborateMatcherArmsUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩) []
      nilClause.arms ⟨34, 9⟩ =
      some (translateArms29 nilArms, ⟨42, 9⟩) := by
  simp only [nilClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [origin29_nil_first_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_nil_second_arm_exact]
  rfl'

private theorem origin29_nil_clause_exact :
    elaborateMatcherClauseUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext (.var ⟨32⟩)
      nilClause ⟨33, 8⟩ =
      some (translateClause29 nilClauseGenerated, ⟨42, 9⟩) := by
  have shape : nilClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [nilClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      ConstructorSchemes.listNil, ListPatternSchemes.nil,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin29_nil_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat29,
    nilHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [origin29_nil_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_nil_arms_exact]
  rfl'

private theorem origin29_head_clause_exact :
    elaborateMatcherClauseUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext (.var ⟨32⟩)
      headOnlyClause ⟨42, 9⟩ =
      some (translateClause29 headOnlyClauseGenerated, ⟨43, 11⟩) := by
  let header : GeneratedPPat := translatePPat29
    { holes := headOnlyHoles
      captures := []
      evidence := some (.con PatternFormer.list [.var ⟨4⟩])
      hard :=
        [.ty (DataTypes.list (.var ⟨13⟩)) (.var ⟨3⟩),
         .cap (.var ⟨5⟩) (.var ⟨4⟩)] }
  have headerExact : elaboratePPat Paper1FrozenSignature.signature
      headOnlyClause.header (.var ⟨32⟩) none ⟨42, 9⟩ =
      some (header, ⟨43, 11⟩) := by
    rfl'
  let holes : List Dual := headOnlyHoles.map (fun hole =>
    ⟨hole.capability.apply origin29Substitution.cap,
      hole.target.apply origin29Substitution⟩)
  let next : GeneratedChecks := translateChecks29
    { hard := []
      pending :=
        [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩),
          .slot (.var ⟨5⟩) (.var ⟨13⟩)⟩] }
  have nextExact : elaborateNextMatchersUsing origin29Callback
      origin29FixContext headOnlyClause.nextMatchers holes ⟨43, 11⟩ =
      some (next, ⟨43, 11⟩) := by
    rfl'
  let arm : GeneratedChecks := translateChecks29
    { hard := []
      pending := [⟨.var ⟨3⟩, DataTypes.list (.var ⟨13⟩)⟩] }
  have armExact : elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      holes (.mk .var (.var 0)) ⟨43, 11⟩ = some (arm, ⟨43, 11⟩) := by
    rfl'
  let arms : GeneratedArms := ⟨arm.append GeneratedChecks.empty⟩
  have armsExact : elaborateMatcherArmsUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      holes headOnlyClause.arms ⟨43, 11⟩ = some (arms, ⟨43, 11⟩) := by
    simp only [headOnlyClause, MatcherClause.arms,
      elaborateMatcherArmsUsing]
    rw [armExact]
    rfl
  have shape : headOnlyClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [headOnlyClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [headerExact]
  simp only [Option.bind_eq_bind, Option.bind_some, header, translatePPat29,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [nextExact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [armsExact]
  rfl'

private theorem origin29_value_header_exact :
    elaboratePPat Paper1FrozenSignature.signature valueConsClause.header
      (.var ⟨32⟩) none ⟨43, 11⟩ =
      some (translatePPat29 valueConsHeader, ⟨44, 13⟩) := by
  rfl'

private theorem origin29_value_next_exact :
    elaborateNextMatchersUsing origin29Callback
      (.mono ((Ty.var ⟨14⟩).apply origin29Substitution) :: origin29FixContext)
      valueConsClause.nextMatchers
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      ⟨44, 13⟩ = some (translateChecks29 valueConsNext, ⟨46, 13⟩) := by
  rfl'

private theorem origin29_value_arm_exact :
    elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext
      (valueConsHeader.captures.map (Ty.apply origin29Substitution))
      (.var ⟨32⟩)
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      valueConsArmSource ⟨46, 13⟩ =
      some (translateChecks29 valueConsArm, ⟨70, 13⟩) := by
  rfl'

private theorem origin29_value_arms_exact :
    elaborateMatcherArmsUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext
      [(Ty.var ⟨14⟩).apply origin29Substitution]
      (.var ⟨32⟩)
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      valueConsClause.arms ⟨46, 13⟩ =
      some (translateArms29 valueConsArms, ⟨70, 13⟩) := by
  change elaborateMatcherArmsUsing origin29Callback
    Paper1FrozenSignature.signature origin29FixContext
    (valueConsHeader.captures.map (Ty.apply origin29Substitution))
    (.var ⟨32⟩)
    (valueConsHoles.map (fun hole =>
      ⟨hole.capability.apply origin29Substitution.cap,
        hole.target.apply origin29Substitution⟩))
    [valueConsArmSource] ⟨46, 13⟩ = _
  simp only [elaborateMatcherArmsUsing]
  rw [origin29_value_arm_exact]
  rfl'

private theorem origin29_value_clause_exact :
    elaborateMatcherClauseUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext (.var ⟨32⟩)
      valueConsClause ⟨43, 11⟩ =
      some (translateClause29 valueConsClauseGenerated, ⟨70, 13⟩) := by
  have shape : valueConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [valueConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin29_value_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat29,
    valueConsHeader, Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [origin29_value_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_value_arms_exact]
  rfl'

private theorem origin29_general_header_exact :
    elaboratePPat Paper1FrozenSignature.signature generalConsClause.header
      (.var ⟨32⟩) none ⟨70, 13⟩ =
      some (translatePPat29 generalConsHeader, ⟨71, 16⟩) := by
  rfl'

private theorem origin29_general_next_exact :
    elaborateNextMatchersUsing origin29Callback origin29FixContext
      generalConsClause.nextMatchers
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      ⟨71, 16⟩ = some (translateChecks29 generalConsNext, ⟨73, 16⟩) := by
  rfl'

private theorem origin29_general_body_exact :
    origin29Callback (.mono (.var ⟨32⟩) :: origin29FixContext)
      generalConsBody ⟨73, 16⟩ =
      some (translateGenerated29 generalConsBodyGenerated, ⟨85, 21⟩) := by
  rfl'

private theorem origin29_general_arm_exact :
    elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      (.mk .var generalConsBody) ⟨73, 16⟩ =
      some (translateChecks29 generalConsArm, ⟨85, 21⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨32⟩)
      ⟨73, 16⟩ = some (⟨[.var ⟨32⟩], []⟩, ⟨73, 16⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [origin29_general_body_exact]
  rfl'

private theorem origin29_general_arms_exact :
    elaborateMatcherArmsUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      generalConsClause.arms ⟨73, 16⟩ =
      some (translateArms29 generalConsArms, ⟨85, 21⟩) := by
  simp only [generalConsClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [origin29_general_arm_exact]
  rfl'

private theorem origin29_general_clause_exact :
    elaborateMatcherClauseUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext (.var ⟨32⟩)
      generalConsClause ⟨70, 13⟩ =
      some (translateClause29 generalConsClauseGenerated, ⟨85, 21⟩) := by
  have shape : generalConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [generalConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin29_general_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat29,
    generalConsHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [origin29_general_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_general_arms_exact]
  rfl'

private theorem origin29_join_header_exact :
    elaboratePPat Paper1FrozenSignature.signature joinClause.header
      (.var ⟨32⟩) none ⟨85, 21⟩ =
      some (translatePPat29 joinHeader, ⟨86, 24⟩) := by
  rfl'

private theorem origin29_join_next_exact :
    elaborateNextMatchersUsing origin29Callback origin29FixContext
      joinClause.nextMatchers
      (joinHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      ⟨86, 24⟩ = some (translateChecks29 joinNext, ⟨90, 24⟩) := by
  rfl'

private theorem origin29_join_nil_arm_exact :
    elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      (joinHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      (.mk (.ctor DataCtor.nil [])
        (sourceList [.tuple [sourceList [], sourceList []]]))
      ⟨90, 24⟩ = some (translateChecks29 joinNilArm, ⟨99, 24⟩) := by
  rfl'

private theorem origin29_join_cons_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature
      (.ctor DataCtor.cons [.var, .var]) (.var ⟨32⟩) ⟨99, 24⟩ =
      some (translateDPat29 joinConsDPat, ⟨100, 24⟩) := by
  rfl'

private theorem origin29_join_cons_body_exact :
    origin29Callback
      (.mono ((Ty.var ⟨70⟩).apply origin29Substitution) ::
        .mono ((DataTypes.list (.var ⟨70⟩)).apply origin29Substitution) ::
        origin29FixContext)
      joinConsBody ⟨100, 24⟩ =
      some (translateGenerated29 joinConsBodyGenerated, ⟨150, 27⟩) := by
  rfl'

private theorem origin29_join_cons_arm_exact :
    elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      (joinHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      (.mk (.ctor DataCtor.cons [.var, .var]) joinConsBody)
      ⟨99, 24⟩ = some (translateChecks29 joinConsArm, ⟨150, 27⟩) := by
  simp only [elaborateMatcherArmUsing, origin29_join_cons_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, translateDPat29, joinConsDPat,
    Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, elaborateCheckedExpressionUsing]
  rw [origin29_join_cons_body_exact]
  rfl'

private theorem origin29_join_arms_exact :
    elaborateMatcherArmsUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      (joinHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      joinClause.arms ⟨90, 24⟩ =
      some (translateArms29 joinArms, ⟨150, 27⟩) := by
  simp only [joinClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [origin29_join_nil_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_join_cons_arm_exact]
  rfl'

private theorem origin29_join_clause_exact :
    elaborateMatcherClauseUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext (.var ⟨32⟩)
      joinClause ⟨85, 21⟩ =
      some (translateClause29 joinClauseGenerated, ⟨150, 27⟩) := by
  have shape : joinClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [joinClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      Paper1FrozenSignature.lookup_data_cons, ConstructorSchemes.listNil,
      ConstructorSchemes.listCons, ListPatternSchemes.join,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin29_join_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat29,
    joinHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [origin29_join_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_join_arms_exact]
  rfl'

private theorem origin29_whole_header_exact :
    elaboratePPat Paper1FrozenSignature.signature wholeValueClause.header
      (.var ⟨32⟩) none ⟨150, 27⟩ =
      some (translatePPat29 wholeValueHeader, ⟨150, 27⟩) := by
  rfl'

private theorem origin29_whole_next_exact :
    elaborateNextMatchersUsing origin29Callback
      (.mono ((Ty.var ⟨3⟩).apply origin29Substitution) :: origin29FixContext)
      wholeValueClause.nextMatchers [] ⟨150, 27⟩ =
      some (translateChecks29 wholeValueNext, ⟨150, 27⟩) := by
  rfl'

private theorem origin29_whole_body_exact :
    origin29Callback
      (.mono (.var ⟨32⟩) ::
        .mono ((Ty.var ⟨3⟩).apply origin29Substitution) ::
        origin29FixContext)
      wholeValueBody ⟨150, 27⟩ =
      some (translateGenerated29 wholeValueBodyGenerated, ⟨173, 35⟩) := by
  rfl'

private theorem origin29_whole_arm_exact :
    elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext
      [(Ty.var ⟨3⟩).apply origin29Substitution]
      (.var ⟨32⟩) [] (.mk .var wholeValueBody) ⟨150, 27⟩ =
      some (translateChecks29 wholeValueArm, ⟨173, 35⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨32⟩)
      ⟨150, 27⟩ = some (⟨[.var ⟨32⟩], []⟩, ⟨150, 27⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [origin29_whole_body_exact]
  rfl'

private theorem origin29_whole_arms_exact :
    elaborateMatcherArmsUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext
      [(Ty.var ⟨3⟩).apply origin29Substitution]
      (.var ⟨32⟩) [] wholeValueClause.arms ⟨150, 27⟩ =
      some (translateArms29 wholeValueArms, ⟨173, 35⟩) := by
  simp only [wholeValueClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [origin29_whole_arm_exact]
  rfl'

private theorem origin29_whole_clause_exact :
    elaborateMatcherClauseUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext (.var ⟨32⟩)
      wholeValueClause ⟨150, 27⟩ =
      some (translateClause29 wholeValueClauseGenerated, ⟨173, 35⟩) := by
  have shape : wholeValueClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [wholeValueClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin29_whole_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat29,
    wholeValueHeader, Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [origin29_whole_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_whole_arms_exact]
  rfl'

private theorem origin29_catch_header_exact :
    elaboratePPat Paper1FrozenSignature.signature catchAllClause.header
      (.var ⟨32⟩) none ⟨173, 35⟩ =
      some (translatePPat29 catchHeader, ⟨173, 36⟩) := by
  rfl'

private theorem origin29_catch_next_exact :
    elaborateNextMatchersUsing origin29Callback origin29FixContext
      catchAllClause.nextMatchers
      (catchHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      ⟨173, 36⟩ = some (translateChecks29 catchNext, ⟨174, 36⟩) := by
  rfl'

private theorem origin29_catch_body_exact :
    origin29Callback (.mono (.var ⟨32⟩) :: origin29FixContext)
      (sourceList [.var 0]) ⟨174, 36⟩ =
      some (translateGenerated29 catchBody, ⟨180, 36⟩) := by
  rfl'

private theorem origin29_catch_arm_exact :
    elaborateMatcherArmUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      (catchHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      (.mk .var (sourceList [.var 0])) ⟨174, 36⟩ =
      some (translateChecks29 catchArm, ⟨180, 36⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨32⟩)
      ⟨174, 36⟩ = some (⟨[.var ⟨32⟩], []⟩, ⟨174, 36⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [origin29_catch_body_exact]
  rfl'

private theorem origin29_catch_arms_exact :
    elaborateMatcherArmsUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext [] (.var ⟨32⟩)
      (catchHoles.map (fun hole =>
        ⟨hole.capability.apply origin29Substitution.cap,
          hole.target.apply origin29Substitution⟩))
      catchAllClause.arms ⟨174, 36⟩ =
      some (translateArms29 catchArms, ⟨180, 36⟩) := by
  simp only [catchAllClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [origin29_catch_arm_exact]
  rfl'

private theorem origin29_catch_clause_exact :
    elaborateMatcherClauseUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext (.var ⟨32⟩)
      catchAllClause ⟨173, 35⟩ =
      some (translateClause29 catchClauseGenerated, ⟨180, 36⟩) := by
  have shape : catchAllClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [catchAllClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [origin29_catch_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, translatePPat29,
    catchHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [origin29_catch_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_catch_arms_exact]
  rfl'

private def translateClauses29
    (clauses : GeneratedMatcherClauses) : GeneratedMatcherClauses :=
  { evidences := clauses.evidences.map
      (Cap.apply origin29Substitution.cap)
    checks := translateChecks29 clauses.checks }

private theorem origin29_clauses_exact :
    elaborateMatcherClausesUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext (.var ⟨32⟩)
      multisetClauses ⟨33, 8⟩ =
      some (translateClauses29 generatedClauses, ⟨180, 36⟩) := by
  simp only [multisetClauses, elaborateMatcherClausesUsing]
  rw [origin29_nil_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_head_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_value_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_general_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_join_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_whole_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [origin29_catch_clause_exact]
  rfl'

private theorem origin29_matcher_literal_exact :
    elaborateMatcherLiteralUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext multisetClauses
      ⟨32, 7⟩ =
      some (translateGenerated29 matcherLiteralGenerated, ⟨180, 36⟩) := by
  simp only [elaborateMatcherLiteralUsing,
    M4Paper1ComputabilityRegression.multiset_static_checks, if_true]
  rw [origin29_clauses_exact]
  rfl'

private theorem origin29_fix_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 357 [.mono (.var ⟨29⟩)]
      multisetDefinition ⟨30, 5⟩ =
      some (translateGenerated29 multisetFixGenerated, ⟨180, 36⟩) := by
  simp only [multisetDefinition, M4.elaborateFuelUsing.eq_def,
    elaborateFixUsing,
    M4Paper1ComputabilityRegression.multiset_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing origin29Callback
      Paper1FrozenSignature.signature origin29FixContext multisetClauses
      ⟨32, 7⟩).bind _ = _
  rw [origin29_matcher_literal_exact]
  rfl'

/-- Exact executable multiset-function elaboration at the P1-L02 matcher's
fresh-variable origin. -/
theorem multiset_function_origin29_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 358 [] multisetWithListArgument ⟨29, 5⟩ =
      some (multisetFunctionGeneratedAt ⟨29, 5⟩, ⟨180, 36⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 357 [.mono (.var ⟨29⟩)]
    multisetDefinition ⟨30, 5⟩).bind
      (fun output => some (Generated.fromLam (.var ⟨29⟩) output.1,
        output.2)) = _
  rw [origin29_fix_structural_fuel_exact]
  rfl'

def closedGeneratedAt29 : Generated :=
  Generated.fromApp (multisetFunctionGeneratedAt ⟨29, 5⟩)
    (M4Paper1ListExactRegression.listGeneratedAt ⟨180, 36⟩)
    (.var ⟨266⟩) (.var ⟨267⟩)

/-- Exact closed multiset-constructor elaboration at the P1-L02 origin. -/
theorem closed_origin29_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 359 [] closedMultisetDefinition ⟨29, 5⟩ =
      some (closedGeneratedAt29, ⟨268, 50⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 358 [] multisetWithListArgument
    ⟨29, 5⟩).bind
      (fun functionOutput =>
        (M4.elaborateFuelUsing (unifyWithFuel 500)
          Paper1FrozenSignature.signature 358 [] listMatcherDefinition
          functionOutput.2).bind
          (fun argumentOutput =>
            some (Generated.fromApp functionOutput.1 argumentOutput.1
              (.var ⟨argumentOutput.2.ty⟩)
              (.var ⟨argumentOutput.2.ty + 1⟩),
              argumentOutput.2.nextTy 2))) = _
  rw [multiset_function_origin29_structural_fuel_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have listAt358 := M4.elaborateFuelUsing_success_mono
    (solveHard := unifyWithFuel 500)
    (signature := Paper1FrozenSignature.signature)
    (smaller := 124) (larger := 358) (by omega)
    M4Paper1ListExactRegression.closed180_structural_fuel_exact
  rw [listAt358]
  rfl

/-! ## The direct multiset definition under a generalized list binding -/

/-- The Paper 1 library context in which the open multiset definition is
checked directly.  Each source lookup receives a fresh instance of the
already inferred list-matcher scheme. -/
def listLibraryContext : Context :=
  [Context.generalize [] M4Paper1ListExactRegression.listMatcherType]

private def libraryCallback : ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 232

private def libraryFixContext : Context :=
  [.mono (.slot (.var ⟨0⟩) (.var ⟨0⟩)),
   .mono (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
     (.matcher (.var ⟨1⟩) (.var ⟨1⟩)))] ++ listLibraryContext

private theorem library_nil_header_exact :
    elaboratePPat Paper1FrozenSignature.signature nilClause.header
      (.var ⟨2⟩) none ⟨3, 3⟩ =
      some (shiftPPat nilHeader, ⟨4, 4⟩) := by
  rfl'

private theorem library_nil_next_exact :
    elaborateNextMatchersUsing libraryCallback libraryFixContext nilClause.nextMatchers
      [] ⟨4, 4⟩ = some (shiftChecks nilNext, ⟨4, 4⟩) := by
  rfl'

private theorem library_nil_first_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature (.ctor DataCtor.nil [])
      (.var ⟨2⟩) ⟨4, 4⟩ =
      some (shiftDPat nilFirstDPat, ⟨5, 4⟩) := by
  rfl'

private theorem library_nil_first_body_exact :
    libraryCallback libraryFixContext (sourceList [Paper1Programs.unit]) ⟨5, 4⟩ =
      some (shiftGenerated nilFirstBody, ⟨11, 4⟩) := by
  rfl'

private theorem library_nil_first_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) []
      (.mk (.ctor DataCtor.nil []) (sourceList [Paper1Programs.unit]))
      ⟨4, 4⟩ = some (shiftChecks nilFirstArm, ⟨11, 4⟩) := by
  simp only [elaborateMatcherArmUsing, library_nil_first_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, shiftDPat, nilFirstDPat,
    Pattern.extendContext, List.map_nil, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [library_nil_first_body_exact]
  rfl'

private theorem library_nil_second_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) [] (.mk .wild (sourceList []))
      ⟨11, 4⟩ = some (shiftChecks nilSecondArm, ⟨12, 4⟩) := by
  rfl'

private theorem library_nil_arms_exact :
    elaborateMatcherArmsUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) [] nilClause.arms ⟨4, 4⟩ =
      some (shiftArms nilArms, ⟨12, 4⟩) := by
  simp only [nilClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [library_nil_first_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_nil_second_arm_exact]
  rfl'

private theorem library_nil_clause_exact :
    elaborateMatcherClauseUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext (.var ⟨2⟩) nilClause ⟨3, 3⟩ =
      some (shiftClause nilClauseGenerated, ⟨12, 4⟩) := by
  have shape : nilClause.toShape.check Paper1FrozenSignature.signature = true := by
    simp [nilClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      ConstructorSchemes.listNil, ListPatternSchemes.nil,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [library_nil_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, shiftPPat, nilHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [library_nil_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_nil_arms_exact]
  rfl'

private def libraryHeadHoles : List Dual :=
  [⟨.var ⟨5⟩, .var ⟨12⟩⟩]

private def libraryHeadHeader : GeneratedPPat :=
  { holes := libraryHeadHoles
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨4⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨12⟩)) (.var ⟨2⟩),
       .cap (.var ⟨5⟩) (.var ⟨4⟩)] }

private theorem library_head_header_exact :
    elaboratePPat Paper1FrozenSignature.signature headOnlyClause.header
      (.var ⟨2⟩) none ⟨12, 4⟩ =
      some (libraryHeadHeader, ⟨13, 6⟩) := by
  rfl'

private def libraryHeadNext : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨0⟩),
        .slot (.var ⟨5⟩) (.var ⟨12⟩)⟩] }

private theorem library_head_next_exact :
    elaborateNextMatchersUsing libraryCallback libraryFixContext
      headOnlyClause.nextMatchers libraryHeadHoles ⟨13, 6⟩ =
      some (libraryHeadNext, ⟨13, 6⟩) := by
  unfold libraryFixContext listLibraryContext
  rfl'

private def libraryHeadArm : GeneratedChecks :=
  { hard := []
    pending := [⟨.var ⟨2⟩, DataTypes.list (.var ⟨12⟩)⟩] }

private theorem library_head_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) libraryHeadHoles (.mk .var (.var 0))
      ⟨13, 6⟩ = some (libraryHeadArm, ⟨13, 6⟩) := by
  rfl'

private def libraryHeadArms : GeneratedArms :=
  ⟨libraryHeadArm.append GeneratedChecks.empty⟩

private theorem library_head_arms_exact :
    elaborateMatcherArmsUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) libraryHeadHoles headOnlyClause.arms
      ⟨13, 6⟩ = some (libraryHeadArms, ⟨13, 6⟩) := by
  simp only [headOnlyClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [library_head_arm_exact]
  rfl

private def libraryHeadClause : GeneratedMatcherClause :=
  { holes := libraryHeadHoles
    evidence := libraryHeadHeader.evidence
    checks :=
      { hard := libraryHeadHeader.hard ++ libraryHeadNext.hard ++ libraryHeadArm.hard
        pending := libraryHeadNext.pending ++ libraryHeadArm.pending } }

private theorem library_head_clause_exact :
    elaborateMatcherClauseUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext (.var ⟨2⟩) headOnlyClause ⟨12, 4⟩ =
      some (libraryHeadClause, ⟨13, 6⟩) := by
  have shape : headOnlyClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [headOnlyClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [library_head_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, libraryHeadHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [library_head_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_head_arms_exact]
  rfl

private theorem library_value_header_exact :
    elaboratePPat Paper1FrozenSignature.signature valueConsClause.header
      (.var ⟨2⟩) none ⟨13, 6⟩ =
      some (shiftPPat valueConsHeader, ⟨14, 8⟩) := by
  rfl'

private theorem library_value_next_exact :
    elaborateNextMatchersUsing libraryCallback
      (.mono (.var ⟨13⟩) :: libraryFixContext)
      valueConsClause.nextMatchers
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      ⟨14, 8⟩ = some (shiftChecks valueConsNext, ⟨16, 8⟩) := by
  unfold libraryFixContext listLibraryContext
  rfl'

private theorem library_value_body_exact :
    libraryCallback
      (.mono (.var ⟨2⟩) :: .mono (.var ⟨13⟩) :: libraryFixContext)
      valueConsArmSource.body ⟨16, 8⟩ =
      some (shiftGenerated valueConsBody, ⟨40, 8⟩) := by
  rfl'

private theorem library_value_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [.var ⟨13⟩] (.var ⟨2⟩)
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      valueConsArmSource ⟨16, 8⟩ =
      some (shiftChecks valueConsArm, ⟨40, 8⟩) := by
  rfl'

private theorem library_value_arms_exact :
    elaborateMatcherArmsUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [.var ⟨13⟩] (.var ⟨2⟩)
      (valueConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      valueConsClause.arms ⟨16, 8⟩ =
      some (⟨shiftChecks valueConsArm |>.append GeneratedChecks.empty⟩,
        ⟨40, 8⟩) := by
  change elaborateMatcherArmsUsing libraryCallback
    Paper1FrozenSignature.signature libraryFixContext [.var ⟨13⟩]
    (.var ⟨2⟩)
    (valueConsHoles.map (fun hole =>
      ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
    [valueConsArmSource] ⟨16, 8⟩ = _
  simp only [elaborateMatcherArmsUsing]
  rw [library_value_arm_exact]
  rfl

private theorem library_value_clause_exact :
    elaborateMatcherClauseUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext (.var ⟨2⟩) valueConsClause ⟨13, 6⟩ =
      some (shiftClause valueConsClauseGenerated, ⟨40, 8⟩) := by
  have shape : valueConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [valueConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [library_value_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, shiftPPat,
    valueConsHeader, Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [open_shift_ty14]
  rw [library_value_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_value_arms_exact]
  rfl'

private def libraryGeneralBodyGenerated : Generated :=
  { target := TypePM.Ty.data
                 { name := "List" }
                 [TypePM.Ty.prod [TypePM.Ty.var { index := 46 }, TypePM.Ty.var { index := 55 }]],
     hard := [TypePM.Equation.ty
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 43 }])
                (TypePM.Ty.var { index := 2 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 46 }) (TypePM.Ty.var { index := 45 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 14 }) (TypePM.Cap.var { index := 13 }),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 47 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 45 }]),
              TypePM.Equation.cap
                (TypePM.Cap.var { index := 15 })
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 13 }]),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 44 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 43 }]),
              TypePM.Equation.cap
                (TypePM.Cap.var { index := 12 })
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 11 }]),
              TypePM.Equation.ty
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 45 }])
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 43 }]),
              TypePM.Equation.cap
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 13 }])
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 11 }]),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.slot (TypePM.Cap.var { index := 16 }) (TypePM.Ty.var { index := 48 }))
                  (TypePM.Ty.matcher
                    (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 16 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 48 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 49 }) (TypePM.Ty.var { index := 50 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 51 }])
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 51 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 51 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 52 }) (TypePM.Ty.var { index := 53 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 53 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 54 }) (TypePM.Ty.var { index := 55 }))],
     pending := [{ source := TypePM.Ty.slot (TypePM.Cap.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
                   expected := TypePM.Ty.var { index := 49 } },
                 { source := TypePM.Ty.var { index := 50 },
                   expected := TypePM.Ty.slot
                                 (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 11 }])
                                 (TypePM.Ty.var { index := 2 }) },
                 { source := TypePM.Ty.var { index := 44 }, expected := TypePM.Ty.var { index := 52 } },
                 { source := TypePM.Ty.var { index := 47 }, expected := TypePM.Ty.var { index := 54 } }] }

private def libraryJoinBodyGenerated : Generated :=
  { target := TypePM.Ty.var { index := 120 },
     hard := [TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 1 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }]),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap
                (TypePM.Cap.var { index := 1 })
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 20 }]),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 79 })
                (TypePM.Ty.prod [TypePM.Ty.var { index := 80 }, TypePM.Ty.var { index := 83 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 20 }) (TypePM.Cap.var { index := 20 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 83 }) (TypePM.Ty.var { index := 85 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 80 }) (TypePM.Ty.var { index := 87 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 20 }) (TypePM.Cap.var { index := 20 }),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.var { index := 88 })
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 88 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 88 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 89 }) (TypePM.Ty.var { index := 90 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 90 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 91 }) (TypePM.Ty.var { index := 92 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.fn (TypePM.Ty.var { index := 77 }) (TypePM.Ty.var { index := 78 }))
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 77 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 78 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 93 }) (TypePM.Ty.var { index := 94 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 94 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 95 }) (TypePM.Ty.var { index := 96 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 76 }])
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 76 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 76 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 97 }) (TypePM.Ty.var { index := 98 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 101 })
                (TypePM.Ty.prod [TypePM.Ty.var { index := 102 }, TypePM.Ty.var { index := 105 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 20 }) (TypePM.Cap.var { index := 20 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 105 }) (TypePM.Ty.var { index := 107 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 102 }) (TypePM.Ty.var { index := 109 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 70 }) (TypePM.Ty.var { index := 70 }),
              TypePM.Equation.ty (TypePM.Ty.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 0 }) (TypePM.Cap.var { index := 0 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 20 }) (TypePM.Cap.var { index := 20 }),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.var { index := 110 })
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 110 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 110 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 111 }) (TypePM.Ty.var { index := 112 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 112 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 113 }) (TypePM.Ty.var { index := 114 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.fn (TypePM.Ty.var { index := 99 }) (TypePM.Ty.var { index := 100 }))
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 99 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 100 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 115 }) (TypePM.Ty.var { index := 116 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 116 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 117 }) (TypePM.Ty.var { index := 118 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 98 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 119 }) (TypePM.Ty.var { index := 120 }))],
     pending := [{ source := TypePM.Ty.var { index := 70 }, expected := TypePM.Ty.var { index := 89 } },
                 { source := TypePM.Ty.var { index := 85 }, expected := TypePM.Ty.var { index := 91 } },
                 { source := TypePM.Ty.fn
                               (TypePM.Ty.var { index := 79 })
                               (TypePM.Ty.prod [TypePM.Ty.var { index := 87 }, TypePM.Ty.var { index := 92 }]),
                   expected := TypePM.Ty.var { index := 93 } },
                 { source := TypePM.Ty.data
                               { name := "List" }
                               [TypePM.Ty.prod
                                  [TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }],
                                   TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }]]],
                   expected := TypePM.Ty.var { index := 95 } },
                 { source := TypePM.Ty.var { index := 96 }, expected := TypePM.Ty.var { index := 97 } },
                 { source := TypePM.Ty.var { index := 70 }, expected := TypePM.Ty.var { index := 111 } },
                 { source := TypePM.Ty.var { index := 109 }, expected := TypePM.Ty.var { index := 113 } },
                 { source := TypePM.Ty.fn
                               (TypePM.Ty.var { index := 101 })
                               (TypePM.Ty.prod [TypePM.Ty.var { index := 114 }, TypePM.Ty.var { index := 107 }]),
                   expected := TypePM.Ty.var { index := 115 } },
                 { source := TypePM.Ty.data
                               { name := "List" }
                               [TypePM.Ty.prod
                                  [TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }],
                                   TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 70 }]]],
                   expected := TypePM.Ty.var { index := 117 } },
                 { source := TypePM.Ty.var { index := 118 }, expected := TypePM.Ty.var { index := 119 } }] }

private def libraryWholeBodyGenerated : Generated :=
  { target := TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 126 }],
     hard := [TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.slot (TypePM.Cap.var { index := 23 }) (TypePM.Ty.var { index := 121 }))
                  (TypePM.Ty.matcher
                    (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 23 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 121 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 122 }) (TypePM.Ty.var { index := 123 })),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.slot (TypePM.Cap.var { index := 0 }) (TypePM.Ty.var { index := 0 }))
                  (TypePM.Ty.matcher (TypePM.Cap.var { index := 1 }) (TypePM.Ty.var { index := 1 })))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 124 }) (TypePM.Ty.var { index := 125 })),
              TypePM.Equation.ty
                (TypePM.Ty.prod
                  [TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 127 }],
                   TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 128 }]])
                (TypePM.Ty.prod [TypePM.Ty.var { index := 2 }, TypePM.Ty.var { index := 2 }]),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.var { index := 129 })
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 129 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 129 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 130 }) (TypePM.Ty.var { index := 131 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 131 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 133 }) (TypePM.Ty.var { index := 134 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 134 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 126 }]),
              TypePM.Equation.ty
                (TypePM.Ty.prod
                  [TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 135 }],
                   TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 138 }]])
                (TypePM.Ty.prod [TypePM.Ty.var { index := 2 }, TypePM.Ty.var { index := 2 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 136 }) (TypePM.Ty.var { index := 135 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 27 }) (TypePM.Cap.var { index := 26 }),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 137 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 135 }]),
              TypePM.Equation.cap
                (TypePM.Cap.var { index := 28 })
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 26 }]),
              TypePM.Equation.ty (TypePM.Ty.var { index := 136 }) (TypePM.Ty.var { index := 138 }),
              TypePM.Equation.cap (TypePM.Cap.var { index := 30 }) (TypePM.Cap.var { index := 29 }),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 137 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 138 }]),
              TypePM.Equation.cap
                (TypePM.Cap.var { index := 31 })
                (TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 29 }]),
              TypePM.Equation.ty
                (TypePM.Ty.fn
                  (TypePM.Ty.var { index := 139 })
                  (TypePM.Ty.fn
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 139 }])
                    (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 139 }])))
                (TypePM.Ty.fn (TypePM.Ty.var { index := 140 }) (TypePM.Ty.var { index := 141 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 141 })
                (TypePM.Ty.fn (TypePM.Ty.var { index := 143 }) (TypePM.Ty.var { index := 144 })),
              TypePM.Equation.ty
                (TypePM.Ty.var { index := 144 })
                (TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 126 }])],
     pending := [{ source := TypePM.Ty.slot (TypePM.Cap.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
                   expected := TypePM.Ty.var { index := 122 } },
                 { source := TypePM.Ty.slot (TypePM.Cap.var { index := 0 }) (TypePM.Ty.var { index := 0 }),
                   expected := TypePM.Ty.var { index := 124 } },
                 { source := TypePM.Ty.prod [TypePM.Ty.var { index := 123 }, TypePM.Ty.var { index := 125 }],
                   expected := TypePM.Ty.slot
                                 (TypePM.Cap.prod
                                   [TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 24 }],
                                    TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 25 }]])
                                 (TypePM.Ty.prod [TypePM.Ty.var { index := 2 }, TypePM.Ty.var { index := 2 }]) },
                 { source := TypePM.Ty.prod [], expected := TypePM.Ty.var { index := 130 } },
                 { source := TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 132 }],
                   expected := TypePM.Ty.var { index := 133 } },
                 { source := TypePM.Ty.prod [TypePM.Ty.var { index := 123 }, TypePM.Ty.var { index := 125 }],
                   expected := TypePM.Ty.slot
                                 (TypePM.Cap.prod
                                   [TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 26 }],
                                    TypePM.Cap.con { name := "List" } [TypePM.Cap.var { index := 29 }]])
                                 (TypePM.Ty.prod [TypePM.Ty.var { index := 2 }, TypePM.Ty.var { index := 2 }]) },
                 { source := TypePM.Ty.prod [], expected := TypePM.Ty.var { index := 140 } },
                 { source := TypePM.Ty.data { name := "List" } [TypePM.Ty.var { index := 142 }],
                   expected := TypePM.Ty.var { index := 143 } }] }

private theorem library_general_header_exact :
    elaboratePPat Paper1FrozenSignature.signature generalConsClause.header
      (.var ⟨2⟩) none ⟨40, 8⟩ =
      some (shiftPPat generalConsHeader, ⟨41, 11⟩) := by
  rfl'

private theorem library_general_next_exact :
    elaborateNextMatchersUsing libraryCallback libraryFixContext
      generalConsClause.nextMatchers
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      ⟨41, 11⟩ = some (shiftChecks generalConsNext, ⟨43, 11⟩) := by
  unfold libraryFixContext listLibraryContext
  rfl'

private theorem library_general_body_exact :
    libraryCallback (.mono (.var ⟨2⟩) :: libraryFixContext)
      generalConsBody ⟨43, 11⟩ =
      some (libraryGeneralBodyGenerated, ⟨56, 17⟩) := by
  unfold libraryCallback libraryFixContext listLibraryContext
  rfl'

private def libraryGeneralArm : GeneratedChecks :=
  { hard := libraryGeneralBodyGenerated.hard
    pending := libraryGeneralBodyGenerated.pending ++
      [⟨libraryGeneralBodyGenerated.target,
        DataTypes.list (.prod [.var ⟨40⟩,
          DataTypes.list (.var ⟨40⟩)])⟩] }

private theorem library_general_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      (.mk .var generalConsBody) ⟨43, 11⟩ =
      some (libraryGeneralArm, ⟨56, 17⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨2⟩)
      ⟨43, 11⟩ = some (⟨[.var ⟨2⟩], []⟩, ⟨43, 11⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [library_general_body_exact]
  rfl

private def libraryGeneralArms : GeneratedArms :=
  ⟨libraryGeneralArm.append GeneratedChecks.empty⟩

private theorem library_general_arms_exact :
    elaborateMatcherArmsUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩)
      (generalConsHoles.map (fun hole =>
        ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩))
      generalConsClause.arms ⟨43, 11⟩ =
      some (libraryGeneralArms, ⟨56, 17⟩) := by
  simp only [generalConsClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [library_general_arm_exact]
  rfl

private def libraryGeneralClause : GeneratedMatcherClause :=
  { holes := generalConsHoles.map (fun hole =>
      ⟨hole.capability.apply openShift.cap, hole.target.apply openShift⟩)
    evidence := (shiftPPat generalConsHeader).evidence
    checks :=
      { hard := (shiftPPat generalConsHeader).hard ++
          (shiftChecks generalConsNext).hard ++ libraryGeneralArm.hard
        pending := (shiftChecks generalConsNext).pending ++
          libraryGeneralArm.pending } }

private theorem library_general_clause_exact :
    elaborateMatcherClauseUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext (.var ⟨2⟩) generalConsClause ⟨40, 8⟩ =
      some (libraryGeneralClause, ⟨56, 17⟩) := by
  have shape : generalConsClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [generalConsClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, ListPatternSchemes.cons]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [library_general_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, shiftPPat,
    generalConsHeader, Pattern.extendContext, List.map_nil, List.nil_append]
  rw [library_general_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_general_arms_exact]
  rfl'

private def libraryJoinHoles : List Dual :=
  [⟨.var ⟨18⟩, DataTypes.list (.var ⟨56⟩)⟩,
   ⟨.var ⟨19⟩, DataTypes.list (.var ⟨56⟩)⟩]

private def libraryJoinHeader : GeneratedPPat :=
  { holes := libraryJoinHoles
    captures := []
    evidence := some (.con PatternFormer.list [.var ⟨17⟩])
    hard :=
      [.ty (DataTypes.list (.var ⟨56⟩)) (.var ⟨2⟩),
       .cap (.var ⟨18⟩) (.con PatternFormer.list [.var ⟨17⟩]),
       .cap (.var ⟨19⟩) (.con PatternFormer.list [.var ⟨17⟩])] }

private theorem library_join_header_exact :
    elaboratePPat Paper1FrozenSignature.signature joinClause.header
      (.var ⟨2⟩) none ⟨56, 17⟩ =
      some (libraryJoinHeader, ⟨57, 20⟩) := by
  rfl'

private def libraryJoinNext : GeneratedChecks :=
  { hard :=
      [.ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨1⟩)))
        (.fn (.var ⟨57⟩) (.var ⟨58⟩)),
       .ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
          (.matcher (.var ⟨1⟩) (.var ⟨1⟩)))
        (.fn (.var ⟨59⟩) (.var ⟨60⟩))]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨0⟩), .var ⟨57⟩⟩,
       ⟨.var ⟨58⟩,
        .slot (.var ⟨18⟩) (DataTypes.list (.var ⟨56⟩))⟩,
       ⟨.slot (.var ⟨0⟩) (.var ⟨0⟩), .var ⟨59⟩⟩,
       ⟨.var ⟨60⟩,
        .slot (.var ⟨19⟩) (DataTypes.list (.var ⟨56⟩))⟩] }

private theorem library_join_next_exact :
    elaborateNextMatchersUsing libraryCallback libraryFixContext
      joinClause.nextMatchers libraryJoinHoles ⟨57, 20⟩ =
      some (libraryJoinNext, ⟨61, 20⟩) := by
  unfold libraryFixContext listLibraryContext
  rfl'

private def libraryJoinNilArm : GeneratedChecks :=
  { hard :=
      [.ty (DataTypes.list (.var ⟨61⟩)) (.var ⟨2⟩),
       .ty
        (.fn (.var ⟨62⟩)
          (.fn (DataTypes.list (.var ⟨62⟩))
            (DataTypes.list (.var ⟨62⟩))))
        (.fn (.var ⟨65⟩) (.var ⟨66⟩)),
       .ty (.var ⟨66⟩) (.fn (.var ⟨68⟩) (.var ⟨69⟩))]
    pending :=
      [⟨.prod [DataTypes.list (.var ⟨63⟩),
          DataTypes.list (.var ⟨64⟩)], .var ⟨65⟩⟩,
       ⟨DataTypes.list (.var ⟨67⟩), .var ⟨68⟩⟩,
       ⟨.var ⟨69⟩,
        DataTypes.list (.prod [DataTypes.list (.var ⟨56⟩),
          DataTypes.list (.var ⟨56⟩)])⟩] }

private theorem library_join_nil_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) libraryJoinHoles
      (.mk (.ctor DataCtor.nil [])
        (sourceList [.tuple [sourceList [], sourceList []]]))
      ⟨61, 20⟩ = some (libraryJoinNilArm, ⟨70, 20⟩) := by
  unfold libraryFixContext listLibraryContext
  rfl'

private def libraryJoinConsDPat : GeneratedDPat :=
  { bindings := [.var ⟨70⟩, DataTypes.list (.var ⟨70⟩)]
    hard := [.ty (DataTypes.list (.var ⟨70⟩)) (.var ⟨2⟩)] }

private theorem library_join_cons_dpat_exact :
    elaborateDPat Paper1FrozenSignature.signature
      (.ctor DataCtor.cons [.var, .var]) (.var ⟨2⟩) ⟨70, 20⟩ =
      some (libraryJoinConsDPat, ⟨71, 20⟩) := by
  rfl'

private theorem library_join_cons_body_exact :
    libraryCallback
      (.mono (.var ⟨70⟩) ::
        .mono (DataTypes.list (.var ⟨70⟩)) :: libraryFixContext)
      joinConsBody ⟨71, 20⟩ =
      some (libraryJoinBodyGenerated, ⟨121, 23⟩) := by
  unfold libraryCallback libraryFixContext listLibraryContext
  rfl'

private def libraryJoinConsArm : GeneratedChecks :=
  { hard := libraryJoinConsDPat.hard ++ libraryJoinBodyGenerated.hard
    pending := libraryJoinBodyGenerated.pending ++
      [⟨libraryJoinBodyGenerated.target,
        DataTypes.list
          (.prod [DataTypes.list (.var ⟨56⟩),
            DataTypes.list (.var ⟨56⟩)])⟩] }

private theorem library_join_cons_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) libraryJoinHoles
      (.mk (.ctor DataCtor.cons [.var, .var]) joinConsBody)
      ⟨70, 20⟩ = some (libraryJoinConsArm, ⟨121, 23⟩) := by
  simp only [elaborateMatcherArmUsing, library_join_cons_dpat_exact,
    Option.bind_eq_bind, Option.bind_some, libraryJoinConsDPat,
    Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, elaborateCheckedExpressionUsing]
  rw [library_join_cons_body_exact]
  rfl

private def libraryJoinArms : GeneratedArms :=
  ⟨libraryJoinNilArm.append
    (libraryJoinConsArm.append GeneratedChecks.empty)⟩

private theorem library_join_arms_exact :
    elaborateMatcherArmsUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) libraryJoinHoles joinClause.arms
      ⟨61, 20⟩ = some (libraryJoinArms, ⟨121, 23⟩) := by
  simp only [joinClause, MatcherClause.arms, elaborateMatcherArmsUsing]
  rw [library_join_nil_arm_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_join_cons_arm_exact]
  rfl

private def libraryJoinClause : GeneratedMatcherClause :=
  { holes := libraryJoinHoles
    evidence := libraryJoinHeader.evidence
    checks :=
      { hard := libraryJoinHeader.hard ++ libraryJoinNext.hard ++
          libraryJoinArms.checks.hard
        pending := libraryJoinNext.pending ++ libraryJoinArms.checks.pending } }

private theorem library_join_clause_exact :
    elaborateMatcherClauseUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext (.var ⟨2⟩) joinClause ⟨56, 17⟩ =
      some (libraryJoinClause, ⟨121, 23⟩) := by
  have shape : joinClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [joinClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.shapesOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
      DPat.constructorArity?, Paper1FrozenSignature.lookup_data_nil,
      Paper1FrozenSignature.lookup_data_cons, ConstructorSchemes.listNil,
      ConstructorSchemes.listCons, ListPatternSchemes.join,
      PolyDataTypes.list]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [library_join_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, libraryJoinHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [library_join_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_join_arms_exact]
  rfl

private def libraryWholeHeader : GeneratedPPat :=
  { holes := []
    captures := [.var ⟨2⟩]
    evidence := none
    hard := [] }

private theorem library_whole_header_exact :
    elaboratePPat Paper1FrozenSignature.signature wholeValueClause.header
      (.var ⟨2⟩) none ⟨121, 23⟩ =
      some (libraryWholeHeader, ⟨121, 23⟩) := by
  rfl'

private def libraryWholeNext : GeneratedChecks :=
  { hard := []
    pending := [⟨.prod [], .prod []⟩] }

private theorem library_whole_next_exact :
    elaborateNextMatchersUsing libraryCallback
      (.mono (.var ⟨2⟩) :: libraryFixContext)
      wholeValueClause.nextMatchers [] ⟨121, 23⟩ =
      some (libraryWholeNext, ⟨121, 23⟩) := by
  rfl'

private theorem library_whole_body_exact :
    libraryCallback
      (.mono (.var ⟨2⟩) :: .mono (.var ⟨2⟩) :: libraryFixContext)
      wholeValueBody ⟨121, 23⟩ =
      some (libraryWholeBodyGenerated, ⟨145, 32⟩) := by
  unfold libraryCallback libraryFixContext listLibraryContext
  rfl'

private def libraryWholeArm : GeneratedChecks :=
  { hard := libraryWholeBodyGenerated.hard
    pending := libraryWholeBodyGenerated.pending ++
      [⟨libraryWholeBodyGenerated.target, DataTypes.list (.prod [])⟩] }

private theorem library_whole_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [.var ⟨2⟩] (.var ⟨2⟩) []
      (.mk .var wholeValueBody) ⟨121, 23⟩ =
      some (libraryWholeArm, ⟨145, 32⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨2⟩)
      ⟨121, 23⟩ = some (⟨[.var ⟨2⟩], []⟩, ⟨121, 23⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [library_whole_body_exact]
  rfl

private def libraryWholeArms : GeneratedArms :=
  ⟨libraryWholeArm.append GeneratedChecks.empty⟩

private theorem library_whole_arms_exact :
    elaborateMatcherArmsUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [.var ⟨2⟩] (.var ⟨2⟩) []
      wholeValueClause.arms ⟨121, 23⟩ =
      some (libraryWholeArms, ⟨145, 32⟩) := by
  simp only [wholeValueClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [library_whole_arm_exact]
  rfl

private def libraryWholeClause : GeneratedMatcherClause :=
  { holes := []
    evidence := none
    checks :=
      { hard := libraryWholeNext.hard ++ libraryWholeArm.hard
        pending := libraryWholeNext.pending ++ libraryWholeArm.pending } }

private theorem library_whole_clause_exact :
    elaborateMatcherClauseUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext (.var ⟨2⟩) wholeValueClause ⟨121, 23⟩ =
      some (libraryWholeClause, ⟨145, 32⟩) := by
  have shape : wholeValueClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [wholeValueClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [library_whole_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, libraryWholeHeader,
    Pattern.extendContext, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [library_whole_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_whole_arms_exact]
  rfl

private def libraryCatchHoles : List Dual :=
  [⟨.var ⟨32⟩, .var ⟨2⟩⟩]

private def libraryCatchHeader : GeneratedPPat :=
  { holes := libraryCatchHoles
    captures := []
    evidence := none
    hard := [] }

private theorem library_catch_header_exact :
    elaboratePPat Paper1FrozenSignature.signature catchAllClause.header
      (.var ⟨2⟩) none ⟨145, 32⟩ =
      some (libraryCatchHeader, ⟨145, 33⟩) := by
  rfl'

private def libraryCatchNext : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨.matcher .any (.var ⟨145⟩),
        .slot (.var ⟨32⟩) (.var ⟨2⟩)⟩] }

private theorem library_catch_next_exact :
    elaborateNextMatchersUsing libraryCallback libraryFixContext
      catchAllClause.nextMatchers libraryCatchHoles ⟨145, 33⟩ =
      some (libraryCatchNext, ⟨146, 33⟩) := by
  rfl'

private def libraryCatchBody : Generated :=
  { target := .var ⟨151⟩
    hard :=
      [.ty
        (.fn (.var ⟨146⟩)
          (.fn (DataTypes.list (.var ⟨146⟩))
            (DataTypes.list (.var ⟨146⟩))))
        (.fn (.var ⟨147⟩) (.var ⟨148⟩)),
       .ty (.var ⟨148⟩) (.fn (.var ⟨150⟩) (.var ⟨151⟩))]
    pending :=
      [⟨.var ⟨2⟩, .var ⟨147⟩⟩,
       ⟨DataTypes.list (.var ⟨149⟩), .var ⟨150⟩⟩] }

private theorem library_catch_body_exact :
    libraryCallback (.mono (.var ⟨2⟩) :: libraryFixContext)
      (sourceList [.var 0]) ⟨146, 33⟩ =
      some (libraryCatchBody, ⟨152, 33⟩) := by
  rfl'

private def libraryCatchArm : GeneratedChecks :=
  { hard := libraryCatchBody.hard
    pending := libraryCatchBody.pending ++
      [⟨libraryCatchBody.target, DataTypes.list (.var ⟨2⟩)⟩] }

private theorem library_catch_arm_exact :
    elaborateMatcherArmUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) libraryCatchHoles
      (.mk .var (sourceList [.var 0])) ⟨146, 33⟩ =
      some (libraryCatchArm, ⟨152, 33⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨2⟩)
      ⟨146, 33⟩ = some (⟨[.var ⟨2⟩], []⟩, ⟨146, 33⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [library_catch_body_exact]
  rfl

private def libraryCatchArms : GeneratedArms :=
  ⟨libraryCatchArm.append GeneratedChecks.empty⟩

private theorem library_catch_arms_exact :
    elaborateMatcherArmsUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext [] (.var ⟨2⟩) libraryCatchHoles catchAllClause.arms
      ⟨146, 33⟩ = some (libraryCatchArms, ⟨152, 33⟩) := by
  simp only [catchAllClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [library_catch_arm_exact]
  rfl

private def libraryCatchClause : GeneratedMatcherClause :=
  { holes := libraryCatchHoles
    evidence := none
    checks :=
      { hard := libraryCatchNext.hard ++ libraryCatchArm.hard
        pending := libraryCatchNext.pending ++ libraryCatchArm.pending } }

private theorem library_catch_clause_exact :
    elaborateMatcherClauseUsing libraryCallback Paper1FrozenSignature.signature
      libraryFixContext (.var ⟨2⟩) catchAllClause ⟨145, 32⟩ =
      some (libraryCatchClause, ⟨152, 33⟩) := by
  have shape : catchAllClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [catchAllClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [library_catch_header_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, libraryCatchHeader,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [library_catch_next_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_catch_arms_exact]
  rfl

private def libraryGeneratedClauses : GeneratedMatcherClauses :=
  { evidences :=
      [(shiftClause nilClauseGenerated).evidence.getD .any,
       libraryHeadClause.evidence.getD .any,
       (shiftClause valueConsClauseGenerated).evidence.getD .any,
       libraryGeneralClause.evidence.getD .any,
       libraryJoinClause.evidence.getD .any]
    checks := (shiftClause nilClauseGenerated).checks.append
      (libraryHeadClause.checks.append
        ((shiftClause valueConsClauseGenerated).checks.append
          (libraryGeneralClause.checks.append
            (libraryJoinClause.checks.append
              (libraryWholeClause.checks.append
                (libraryCatchClause.checks.append GeneratedChecks.empty)))))) }

private theorem library_clauses_exact :
    elaborateMatcherClausesUsing libraryCallback
      Paper1FrozenSignature.signature libraryFixContext (.var ⟨2⟩)
      multisetClauses ⟨3, 3⟩ =
      some (libraryGeneratedClauses, ⟨152, 33⟩) := by
  simp only [multisetClauses, elaborateMatcherClausesUsing]
  rw [library_nil_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_head_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_value_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_general_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_join_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_whole_clause_exact]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [library_catch_clause_exact]
  rfl'

private def libraryMatcherLiteralGenerated : Generated :=
  { target := .matcher (.var ⟨2⟩) (.var ⟨2⟩)
    hard := evidenceEquations (.var ⟨2⟩)
      libraryGeneratedClauses.evidences ++ libraryGeneratedClauses.checks.hard
    pending := libraryGeneratedClauses.checks.pending }

private theorem library_matcher_literal_exact :
    elaborateMatcherLiteralUsing libraryCallback
      Paper1FrozenSignature.signature libraryFixContext multisetClauses
      ⟨2, 2⟩ =
      some (libraryMatcherLiteralGenerated, ⟨152, 33⟩) := by
  simp only [elaborateMatcherLiteralUsing,
    M4Paper1ComputabilityRegression.multiset_static_checks, if_true]
  rw [library_clauses_exact]
  rfl

private def libraryMultisetGenerated : Generated :=
  Generated.fromFix
    (.slot (.var ⟨0⟩) (.var ⟨0⟩))
    (.matcher (.var ⟨1⟩) (.var ⟨1⟩))
    libraryMatcherLiteralGenerated

theorem library_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 234 listLibraryContext
      multisetDefinition ⟨0, 0⟩ =
      some (libraryMultisetGenerated, ⟨152, 33⟩) := by
  simp only [multisetDefinition, M4.elaborateFuelUsing.eq_def,
    elaborateFixUsing,
    M4Paper1ComputabilityRegression.multiset_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing libraryCallback
    Paper1FrozenSignature.signature libraryFixContext multisetClauses
    ⟨2, 2⟩).bind _ = _
  rw [library_matcher_literal_exact]
  rfl

/-- Principal type of the direct Paper 1 multiset definition when the
source-defined list matcher is supplied as a generalized library binding. -/
def openMultisetWithListContextType : Ty :=
  .fn (.slot (.var ⟨29⟩) (.var ⟨121⟩))
    (.matcher (.con PatternFormer.list [.var ⟨29⟩])
      (DataTypes.list (.var ⟨121⟩)))

private theorem library_close_fuel_exact :
    (inferGeneratedUsing (unifyWithFuel 3000) libraryMultisetGenerated).bind
      (fun closed => some closed.target) =
      some openMultisetWithListContextType := by
  simp only [libraryMultisetGenerated, libraryMatcherLiteralGenerated,
    libraryGeneratedClauses, libraryGeneralClause, libraryGeneralArms,
    libraryGeneralArm, libraryGeneralBodyGenerated,
    libraryJoinClause, libraryJoinHeader, libraryJoinNext,
    libraryJoinArms, libraryJoinNilArm, libraryJoinConsArm,
    libraryJoinConsDPat, libraryJoinBodyGenerated,
    libraryWholeClause, libraryWholeNext, libraryWholeArm,
    libraryWholeBodyGenerated, libraryCatchClause, libraryCatchNext,
    libraryCatchArm, libraryCatchBody, shiftClause, shiftChecks,
    nilClauseGenerated, libraryHeadClause, libraryHeadHeader,
    libraryHeadNext, libraryHeadArm, valueConsClauseGenerated,
    Generated.fromFix, GeneratedChecks.append, GeneratedChecks.empty,
    evidenceEquations, List.append_assoc, openMultisetWithListContextType]
  rfl'

theorem open_multiset_with_list_context_infer_exact :
    M4.infer Paper1FrozenSignature.signature listLibraryContext
      multisetDefinition = some openMultisetWithListContextType := by
  have elaborated :=
    M4.elaborateFuel_success_of_solverFuel_success library_structural_fuel_exact
  cases closureEquality :
      inferGeneratedUsing (unifyWithFuel 3000) libraryMultisetGenerated with
  | none =>
      have impossible := library_close_fuel_exact
      simp [closureEquality] at impossible
  | some closed =>
      have closedTarget : closed.target = openMultisetWithListContextType := by
        have exactTarget := library_close_fuel_exact
        simpa [closureEquality] using exactTarget
      have publicClosure :=
        inferGeneratedUsing_unify_of_fuel_success closureEquality
      unfold M4.infer M4.elaborate
      rw [M4Paper1ComputabilityRegression.multisetDefinition_complexity]
      rw [show Context.initialSupply listLibraryContext = ⟨0, 0⟩ by rfl]
      rw [elaborated]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [publicClosure]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [closedTarget]
      rfl

theorem open_multiset_with_list_context_typing :
    M4.Typing Paper1FrozenSignature.signature listLibraryContext
      multisetDefinition openMultisetWithListContextType :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    open_multiset_with_list_context_infer_exact


end TypePM.Source.M4Paper1ClosedMultisetExactRegression
