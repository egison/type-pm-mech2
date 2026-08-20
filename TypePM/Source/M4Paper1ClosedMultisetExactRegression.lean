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
    Paper1FrozenSignature.signature 380

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
  { target := .var ⟨112⟩
    hard :=
      [.ty (.var ⟨70⟩) (.var ⟨70⟩),
       .ty (.var ⟨1⟩) (.var ⟨1⟩),
       .ty (.var ⟨2⟩) (DataTypes.list (.var ⟨70⟩)),
       .ty (.var ⟨0⟩) (.var ⟨0⟩),
       .cap (.var ⟨0⟩) (.var ⟨0⟩),
       .cap (.var ⟨1⟩) (.con PatternFormer.list [.var ⟨19⟩]),
       .ty (.prod [.var ⟨82⟩, .var ⟨83⟩]) (.var ⟨79⟩),
       .ty
         (.fn (.var ⟨84⟩)
           (.fn (DataTypes.list (.var ⟨84⟩))
             (DataTypes.list (.var ⟨84⟩))))
         (.fn (.var ⟨85⟩) (.var ⟨86⟩)),
       .ty (.var ⟨86⟩) (.fn (.var ⟨87⟩) (.var ⟨88⟩)),
       .ty
         (.fn (.fn (.var ⟨77⟩) (.var ⟨78⟩))
           (.fn (DataTypes.list (.var ⟨77⟩))
             (DataTypes.list (.var ⟨78⟩))))
         (.fn (.var ⟨89⟩) (.var ⟨90⟩)),
       .ty (.var ⟨90⟩) (.fn (.var ⟨91⟩) (.var ⟨92⟩)),
       .ty
         (.fn (DataTypes.list (.var ⟨76⟩))
           (.fn (DataTypes.list (.var ⟨76⟩))
             (DataTypes.list (.var ⟨76⟩))))
         (.fn (.var ⟨93⟩) (.var ⟨94⟩)),
       .ty (.prod [.var ⟨100⟩, .var ⟨101⟩]) (.var ⟨97⟩),
       .ty
         (.fn (.var ⟨102⟩)
           (.fn (DataTypes.list (.var ⟨102⟩))
             (DataTypes.list (.var ⟨102⟩))))
         (.fn (.var ⟨103⟩) (.var ⟨104⟩)),
       .ty (.var ⟨104⟩) (.fn (.var ⟨105⟩) (.var ⟨106⟩)),
       .ty
         (.fn (.fn (.var ⟨95⟩) (.var ⟨96⟩))
           (.fn (DataTypes.list (.var ⟨95⟩))
             (DataTypes.list (.var ⟨96⟩))))
         (.fn (.var ⟨107⟩) (.var ⟨108⟩)),
       .ty (.var ⟨108⟩) (.fn (.var ⟨109⟩) (.var ⟨110⟩)),
       .ty (.var ⟨94⟩) (.fn (.var ⟨111⟩) (.var ⟨112⟩))]
    pending :=
      [⟨.prod [.matcher .any (.var ⟨80⟩),
          .matcher .any (.var ⟨81⟩)],
        .slot (.prod [.var ⟨22⟩, .var ⟨23⟩]) (.var ⟨79⟩)⟩,
       ⟨.var ⟨70⟩, .var ⟨85⟩⟩,
       ⟨.var ⟨83⟩, .var ⟨87⟩⟩,
       ⟨.fn (.var ⟨79⟩) (.prod [.var ⟨82⟩, .var ⟨88⟩]),
        .var ⟨89⟩⟩,
       ⟨DataTypes.list (.prod [DataTypes.list (.var ⟨70⟩),
          DataTypes.list (.var ⟨70⟩)]), .var ⟨91⟩⟩,
       ⟨.var ⟨92⟩, .var ⟨93⟩⟩,
       ⟨.prod [.matcher .any (.var ⟨98⟩),
          .matcher .any (.var ⟨99⟩)],
        .slot (.prod [.var ⟨24⟩, .var ⟨25⟩]) (.var ⟨97⟩)⟩,
       ⟨.var ⟨70⟩, .var ⟨103⟩⟩,
       ⟨.var ⟨100⟩, .var ⟨105⟩⟩,
       ⟨.fn (.var ⟨97⟩) (.prod [.var ⟨106⟩, .var ⟨101⟩]),
        .var ⟨107⟩⟩,
       ⟨DataTypes.list (.prod [DataTypes.list (.var ⟨70⟩),
          DataTypes.list (.var ⟨70⟩)]), .var ⟨109⟩⟩,
       ⟨.var ⟨110⟩, .var ⟨111⟩⟩] }

private theorem join_cons_body_exact :
    callback
      (.mono (.var ⟨70⟩) ::
        .mono (DataTypes.list (.var ⟨70⟩)) :: fixContext)
      joinConsBody ⟨71, 19⟩ =
      some (joinConsBodyGenerated, ⟨113, 26⟩) := by
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
      ⟨70, 19⟩ = some (joinConsArm, ⟨113, 26⟩) := by
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
      some (joinArms, ⟨113, 26⟩) := by
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
      some (joinClauseGenerated, ⟨113, 26⟩) := by
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
      (.var ⟨3⟩) none ⟨113, 26⟩ =
      some (wholeValueHeader, ⟨113, 26⟩) := by
  rfl'

private def wholeValueNext : GeneratedChecks :=
  { hard := []
    pending := [⟨.prod [], .prod []⟩] }

private theorem whole_value_next_exact :
    elaborateNextMatchersUsing callback
      (.mono (.var ⟨3⟩) :: fixContext)
      wholeValueClause.nextMatchers [] ⟨113, 26⟩ =
      some (wholeValueNext, ⟨113, 26⟩) := by
  rfl'

private def wholeValueBodyGenerated : Generated :=
  { target := .var ⟨124⟩
    hard :=
      [.ty (.var ⟨0⟩) (.fn (.var ⟨113⟩) (.var ⟨114⟩)),
       .ty
         (.fn (.slot (.var ⟨0⟩) (.var ⟨1⟩))
           (.matcher (.var ⟨1⟩) (.var ⟨2⟩)))
         (.fn (.var ⟨115⟩) (.var ⟨116⟩)),
       .ty (.prod [DataTypes.list (.var ⟨117⟩),
          DataTypes.list (.var ⟨118⟩)])
         (.prod [.var ⟨3⟩, .var ⟨3⟩]),
       .ty
         (.fn (.var ⟨119⟩)
           (.fn (DataTypes.list (.var ⟨119⟩))
             (DataTypes.list (.var ⟨119⟩))))
         (.fn (.var ⟨120⟩) (.var ⟨121⟩)),
       .ty (.var ⟨121⟩) (.fn (.var ⟨123⟩) (.var ⟨124⟩)),
       .ty (.prod [DataTypes.list (.var ⟨125⟩),
          DataTypes.list (.var ⟨128⟩)])
         (.prod [.var ⟨3⟩, .var ⟨3⟩]),
       .ty (.var ⟨126⟩) (.var ⟨125⟩),
       .cap (.var ⟨29⟩) (.var ⟨28⟩),
       .ty (.var ⟨127⟩) (DataTypes.list (.var ⟨125⟩)),
       .cap (.var ⟨30⟩) (.con PatternFormer.list [.var ⟨28⟩]),
       .ty (.var ⟨126⟩) (.var ⟨128⟩),
       .cap (.var ⟨32⟩) (.var ⟨31⟩),
       .ty (.var ⟨127⟩) (DataTypes.list (.var ⟨128⟩)),
       .cap (.var ⟨33⟩) (.con PatternFormer.list [.var ⟨31⟩]),
       .ty
         (.fn (.var ⟨129⟩)
           (.fn (DataTypes.list (.var ⟨129⟩))
             (DataTypes.list (.var ⟨129⟩))))
         (.fn (.var ⟨130⟩) (.var ⟨131⟩)),
       .ty (.var ⟨131⟩) (.fn (.var ⟨133⟩) (.var ⟨134⟩)),
       .ty (.var ⟨134⟩) (.var ⟨124⟩),
       .ty (.prod [.var ⟨135⟩, .var ⟨136⟩])
         (.prod [.var ⟨3⟩, .var ⟨3⟩]),
       .ty (DataTypes.list (.var ⟨137⟩)) (.var ⟨124⟩)]
    pending :=
      [⟨.slot (.var ⟨0⟩) (.var ⟨1⟩), .var ⟨113⟩⟩,
       ⟨.slot (.var ⟨0⟩) (.var ⟨1⟩), .var ⟨115⟩⟩,
       ⟨.prod [.var ⟨114⟩, .var ⟨116⟩],
        .slot (.prod [.con PatternFormer.list [.var ⟨26⟩],
          .con PatternFormer.list [.var ⟨27⟩]])
          (.prod [.var ⟨3⟩, .var ⟨3⟩])⟩,
       ⟨.prod [], .var ⟨120⟩⟩,
       ⟨DataTypes.list (.var ⟨122⟩), .var ⟨123⟩⟩,
       ⟨.prod [.var ⟨114⟩, .var ⟨116⟩],
        .slot (.prod [.con PatternFormer.list [.var ⟨28⟩],
          .con PatternFormer.list [.var ⟨31⟩]])
          (.prod [.var ⟨3⟩, .var ⟨3⟩])⟩,
       ⟨.prod [], .var ⟨130⟩⟩,
       ⟨DataTypes.list (.var ⟨132⟩), .var ⟨133⟩⟩,
       ⟨.prod [.var ⟨114⟩, .var ⟨116⟩],
        .slot (.prod [.var ⟨34⟩, .var ⟨35⟩])
          (.prod [.var ⟨3⟩, .var ⟨3⟩])⟩] }

private theorem whole_value_body_exact :
    callback
      (.mono (.var ⟨3⟩) :: .mono (.var ⟨3⟩) :: fixContext)
      wholeValueBody ⟨113, 26⟩ =
      some (wholeValueBodyGenerated, ⟨138, 36⟩) := by
  rfl'

private def wholeValueArm : GeneratedChecks :=
  { hard := wholeValueBodyGenerated.hard
    pending := wholeValueBodyGenerated.pending ++
      [⟨wholeValueBodyGenerated.target, DataTypes.list (.prod [])⟩] }

private theorem whole_value_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [.var ⟨3⟩] (.var ⟨3⟩) []
      (.mk .var wholeValueBody) ⟨113, 26⟩ =
      some (wholeValueArm, ⟨138, 36⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨3⟩)
      ⟨113, 26⟩ = some (⟨[.var ⟨3⟩], []⟩, ⟨113, 26⟩) by rfl]
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
      ⟨113, 26⟩ = some (wholeValueArms, ⟨138, 36⟩) := by
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
      fixContext (.var ⟨3⟩) wholeValueClause ⟨113, 26⟩ =
      some (wholeValueClauseGenerated, ⟨138, 36⟩) := by
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
  [⟨.var ⟨36⟩, .var ⟨3⟩⟩]

private def catchHeader : GeneratedPPat :=
  { holes := catchHoles
    captures := []
    evidence := none
    hard := [] }

private theorem catch_header_exact :
    elaboratePPat Paper1FrozenSignature.signature catchAllClause.header
      (.var ⟨3⟩) none ⟨138, 36⟩ =
      some (catchHeader, ⟨138, 37⟩) := by
  rfl'

private def catchNext : GeneratedChecks :=
  { hard := []
    pending :=
      [⟨.matcher .any (.var ⟨138⟩),
        .slot (.var ⟨36⟩) (.var ⟨3⟩)⟩] }

private theorem catch_next_exact :
    elaborateNextMatchersUsing callback fixContext
      catchAllClause.nextMatchers catchHoles ⟨138, 37⟩ =
      some (catchNext, ⟨139, 37⟩) := by
  rfl'

private def catchBody : Generated :=
  { target := .var ⟨144⟩
    hard :=
      [.ty
        (.fn (.var ⟨139⟩)
          (.fn (DataTypes.list (.var ⟨139⟩))
            (DataTypes.list (.var ⟨139⟩))))
        (.fn (.var ⟨140⟩) (.var ⟨141⟩)),
       .ty (.var ⟨141⟩) (.fn (.var ⟨143⟩) (.var ⟨144⟩))]
    pending :=
      [⟨.var ⟨3⟩, .var ⟨140⟩⟩,
       ⟨DataTypes.list (.var ⟨142⟩), .var ⟨143⟩⟩] }

private theorem catch_body_exact :
    callback (.mono (.var ⟨3⟩) :: fixContext)
      (sourceList [.var 0]) ⟨139, 37⟩ =
      some (catchBody, ⟨145, 37⟩) := by
  rfl'

private def catchArm : GeneratedChecks :=
  { hard := catchBody.hard
    pending := catchBody.pending ++
      [⟨catchBody.target, DataTypes.list (.var ⟨3⟩)⟩] }

private theorem catch_arm_exact :
    elaborateMatcherArmUsing callback Paper1FrozenSignature.signature
      fixContext [] (.var ⟨3⟩) catchHoles
      (.mk .var (sourceList [.var 0])) ⟨139, 37⟩ =
      some (catchArm, ⟨145, 37⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨3⟩)
      ⟨139, 37⟩ = some (⟨[.var ⟨3⟩], []⟩, ⟨139, 37⟩) by rfl]
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
      ⟨139, 37⟩ = some (catchArms, ⟨145, 37⟩) := by
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
      fixContext (.var ⟨3⟩) catchAllClause ⟨138, 36⟩ =
      some (catchClauseGenerated, ⟨145, 37⟩) := by
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
      some (generatedClauses, ⟨145, 37⟩) := by
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
      some (matcherLiteralGenerated, ⟨145, 37⟩) := by
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
      Paper1FrozenSignature.signature 382 [.mono (.var ⟨0⟩)]
      multisetDefinition ⟨1, 0⟩ =
      some (multisetFixGenerated, ⟨145, 37⟩) := by
  simp only [multisetDefinition, M4.elaborateFuelUsing.eq_def,
    elaborateFixUsing,
    M4Paper1ComputabilityRegression.multiset_direct_self_check, if_true,
    Fix.domain, Fix.codomain, Fix.bodyContext, Fix.bodySupply]
  change (elaborateMatcherLiteralUsing callback
      Paper1FrozenSignature.signature fixContext multisetClauses ⟨3, 2⟩).bind _ = _
  rw [matcher_literal_exact]
  rfl

private def multisetFunctionGenerated : Generated :=
  Generated.fromLam (.var ⟨0⟩) multisetFixGenerated

private theorem multiset_function_structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 383 [] multisetWithListArgument ⟨0, 0⟩ =
      some (multisetFunctionGenerated, ⟨145, 37⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 382 [.mono (.var ⟨0⟩)]
    multisetDefinition ⟨1, 0⟩).bind
      (fun output => some (Generated.fromLam (.var ⟨0⟩) output.1,
        output.2)) = _
  rw [multiset_fix_structural_fuel_exact]
  rfl

private def closedGenerated : Generated :=
  Generated.fromApp multisetFunctionGenerated
    M4Paper1ListExactRegression.shiftedListGenerated
    (.var ⟨227⟩) (.var ⟨228⟩)

theorem structural_fuel_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 384 [] closedMultisetDefinition ⟨0, 0⟩ =
      some (closedGenerated, ⟨229, 53⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 383 [] multisetWithListArgument ⟨0, 0⟩).bind
      (fun functionOutput =>
        (M4.elaborateFuelUsing (unifyWithFuel 500)
          Paper1FrozenSignature.signature 383 [] listMatcherDefinition
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
  .fn (.slot (.var ⟨31⟩) (.var ⟨103⟩))
    (.matcher (.con PatternFormer.list [.var ⟨31⟩])
      (DataTypes.list (.var ⟨103⟩)))

private theorem close_fuel_exact :
    (inferGeneratedUsing (unifyWithFuel 500) closedGenerated).bind
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
      inferGeneratedUsing (unifyWithFuel 500) closedGenerated with
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
    Paper1FrozenSignature.signature 251

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
      Paper1FrozenSignature.signature 253 [] multisetDefinition ⟨0, 0⟩ =
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
  M4.elaborateFuel Paper1FrozenSignature.signature 251

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
    M4.elaborateFuel Paper1FrozenSignature.signature 253 []
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

end TypePM.Source.M4Paper1ClosedMultisetExactRegression
