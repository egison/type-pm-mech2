import TypePM.Source.M4TwoIndexMatchAllInitialProducer
import TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility
import TypePM.Source.Paper1Programs

/-!
# Enclosing-M4 Paper 1 catch-all initial-state regression

This regression uses the real Paper 1 catch-all clause inside one actual
source `matchAll`.  Its M4 derivation follows the executable supply order:
target at `⟨0, 0⟩`, variable pattern from `⟨0, 0⟩` to `⟨1, 1⟩`, matcher
literal from `⟨1, 1⟩` to `⟨9, 3⟩`, and body from `⟨9, 3⟩`.  A single
semantic solution satisfies the resulting `Generated.fromMatchAll` block.
At runtime the matcher is evaluated in an environment containing the actual
recursive Paper 1 List closure.  Its successful dispatch delegates that
variable to `something`, whose local reducer binds the same recursive closure
in `FuelEnvironmentSafe`.

The initial-state proof is intentionally ordered before any complete-search
execution fact and assumes none.  It projects its pattern and matcher evidence,
target equality, and matcher-to-slot conversion from that enclosing solved
derivation.  The dedicated producer needs only non-stuck local dispatch, while
this fixture separately proves the exact hit used to discharge that premise
and its finite branch obligation.  The local reducer law also remains separate.
The combined M4 block does not generate those operational facts.
-/

namespace TypePM.Source.MatcherTyping.M4TwoIndexMatchAllInitialProducerRegression

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open TypePM.Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open TypePM.StepIndexedPaper1ListSafetyRegression

def recursiveClosureType : Ty :=
  TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureType

def recursiveClosureEnvironment : ValueEnvironment := [listRecursiveClosure]

/-- Capture typing is uninhabited because the catch-all pattern-pattern header
has no captures.  The full M4 input below proves the required empty capture
list directly and never needs a structural expression-typing judgment. -/
abbrev NoCaptureExpressionTyping : EmbeddedExpressionTyping :=
  fun _ _ _ => False

def matcherContext : Context := [Scheme.mono recursiveClosureType]

def commonSolution : Subst :=
  { cap := fun _ => .any
    ty := fun id =>
      match id.index with
      | 5 => .fn (TypePM.DataTypes.list recursiveClosureType)
          (TypePM.DataTypes.list recursiveClosureType)
      | 7 | 8 => TypePM.DataTypes.list recursiveClosureType
      | _ => recursiveClosureType }

private def catchHoles : List Dual := [⟨.var ⟨2⟩, .var ⟨1⟩⟩]

private def catchHeaderGenerated : GeneratedPPat :=
  { holes := catchHoles
    captures := []
    evidence := none
    hard := [] }

private theorem catchHeader_exact :
    elaboratePPat Paper1FrozenSignature.signature catchAllClause.header
      (.var ⟨1⟩) none ⟨2, 2⟩ = some (catchHeaderGenerated, ⟨2, 3⟩) := by
  rfl'

private def catchNextGenerated : GeneratedChecks :=
  { hard := []
    pending := [⟨.matcher .any (.var ⟨2⟩),
      .slot (.var ⟨2⟩) (.var ⟨1⟩)⟩] }

private theorem catchNext_exact :
    elaborateNextMatchersUsing
      (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 19)
      matcherContext catchAllClause.nextMatchers catchHoles ⟨2, 3⟩ =
        some (catchNextGenerated, ⟨3, 3⟩) := by
  rfl'

private def catchBodyGenerated : Generated :=
  { target := .var ⟨8⟩
    hard := [
      .ty
        (.fn (.var ⟨3⟩)
          (.fn (TypePM.DataTypes.list (.var ⟨3⟩))
            (TypePM.DataTypes.list (.var ⟨3⟩))))
        (.fn (.var ⟨4⟩) (.var ⟨5⟩)),
      .ty (.var ⟨5⟩) (.fn (.var ⟨7⟩) (.var ⟨8⟩))]
    pending := [
      ⟨.var ⟨1⟩, .var ⟨4⟩⟩,
      ⟨TypePM.DataTypes.list (.var ⟨6⟩), .var ⟨7⟩⟩] }

private theorem catchBody_exact :
    M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 19
      (Scheme.mono (.var ⟨1⟩) :: matcherContext) (sourceList [.var 0])
      ⟨3, 3⟩ = some (catchBodyGenerated, ⟨9, 3⟩) := by
  rfl'

private def catchArmChecks : GeneratedChecks :=
  { hard := catchBodyGenerated.hard
    pending := catchBodyGenerated.pending ++
      [⟨catchBodyGenerated.target,
        TypePM.DataTypes.list (.var ⟨1⟩)⟩] }

private theorem catchArm_exact :
    elaborateMatcherArmUsing
      (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 19)
      Paper1FrozenSignature.signature matcherContext [] (.var ⟨1⟩)
      catchHoles (.mk .var (sourceList [.var 0])) ⟨3, 3⟩ =
        some (catchArmChecks, ⟨9, 3⟩) := by
  simp only [elaborateMatcherArmUsing]
  rw [show elaborateDPat Paper1FrozenSignature.signature .var (.var ⟨1⟩)
      ⟨3, 3⟩ = some (⟨[.var ⟨1⟩], []⟩, ⟨3, 3⟩) by rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Pattern.extendContext,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    elaborateCheckedExpressionUsing]
  rw [catchBody_exact]
  rfl

private def catchArmsGenerated : GeneratedArms :=
  ⟨catchArmChecks.append GeneratedChecks.empty⟩

private theorem catchArms_exact :
    elaborateMatcherArmsUsing
      (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 19)
      Paper1FrozenSignature.signature matcherContext [] (.var ⟨1⟩)
      catchHoles catchAllClause.arms ⟨3, 3⟩ =
        some (catchArmsGenerated, ⟨9, 3⟩) := by
  simp only [catchAllClause, MatcherClause.arms,
    elaborateMatcherArmsUsing]
  rw [catchArm_exact]
  rfl

private def catchClauseGenerated : GeneratedMatcherClause :=
  { holes := catchHoles
    evidence := none
    checks :=
      { hard := catchNextGenerated.hard ++ catchArmChecks.hard
        pending := catchNextGenerated.pending ++ catchArmChecks.pending } }

private theorem catchClause_exact :
    elaborateMatcherClauseUsing
      (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 19)
      Paper1FrozenSignature.signature matcherContext (.var ⟨1⟩)
      catchAllClause ⟨2, 2⟩ = some (catchClauseGenerated, ⟨9, 3⟩) := by
  have shape : catchAllClause.toShape.check
      Paper1FrozenSignature.signature = true := by
    simp [catchAllClause, MatcherClause.toShape, MatcherArm.toHeader,
      MatcherClauseShape.check, MatcherArmHeader.check,
      MatcherArmHeader.canonical, HoleConvention.ofCount,
      PPat.shapeOK, PPat.captureBeforeFirstHole,
      PPat.captureBeforeFirstHoleFrom, PPat.occurrences,
      PPat.holeCount, DPat.shapeOK]
  simp only [elaborateMatcherClauseUsing, shape, if_true]
  rw [catchHeader_exact]
  simp only [Option.bind_eq_bind, Option.bind_some, catchHeaderGenerated,
    Pattern.extendContext, List.map_nil, List.nil_append]
  rw [catchNext_exact]
  simp only [Option.bind_some]
  rw [catchArms_exact]
  rfl

/-- Exact output of the public recursive M4 elaborator for the single real
Paper 1 catch-all clause. -/
def catchAllMatcherGenerated : Generated :=
  { target := .matcher (.var ⟨1⟩) (.var ⟨1⟩)
    hard := [.cap (.var ⟨1⟩) .any] ++ catchClauseGenerated.checks.hard
    pending := catchClauseGenerated.checks.pending }

theorem catchAllMatcher_elaboration_exact :
    M4.elaborateFuel Paper1FrozenSignature.signature 20 matcherContext
      (.matcher [catchAllClause]) ⟨1, 1⟩ =
        some (catchAllMatcherGenerated, ⟨9, 3⟩) := by
  unfold M4.elaborateFuel M4.elaborateFuelUsing
  change elaborateMatcherLiteralUsing
      (M4.elaborateFuelUsing unify Paper1FrozenSignature.signature 19)
      Paper1FrozenSignature.signature matcherContext [catchAllClause] ⟨1, 1⟩ =
    some (catchAllMatcherGenerated, ⟨9, 3⟩)
  unfold elaborateMatcherLiteralUsing
  have checked : StaticChecksHold Paper1FrozenSignature.signature
      [catchAllClause] := by
    apply (staticChecksHold_iff Paper1FrozenSignature.signature
      [catchAllClause]).2
    simp [staticChecks, catchAllClause,
      MatcherClause.checkShapes, MatcherClause.toShape,
      MatcherClauseShapes.check, MatcherClauseShapes.catchAllLast,
      MatcherClauseShapes.isCatchAll, MatcherClauseShape.check,
      MatcherClause.header, MatcherClause.arms,
      MatcherArm.toHeader, MatcherArmHeader.check, MatcherArmHeader.canonical,
      armCoverageOK, armsCatchAllLast, finalCatchAllVariableArm,
      rootCoverageOK, MatcherTyping.DPat.isIrrefutable, MatcherArm.header,
      MatcherTyping.PPat.rootFormer?, PPat.shapeOK,
      PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
      PPat.occurrences, PPat.holeCount, HoleConvention.ofCount, DPat.shapeOK,
      Paper1FrozenSignature.signature, Paper1Signature.signature,
      Paper1Signature.patternConstructors, ListPatternSchemes.nil,
      ListPatternSchemes.cons, ListPatternSchemes.join]
  rw [(staticChecksHold_iff Paper1FrozenSignature.signature
    [catchAllClause]).1 checked]
  simp only [if_true]
  simp only [elaborateMatcherClausesUsing]
  rw [catchClause_exact]
  rfl

/-- Executable soundness supplies the matcher component at the enclosing
node's post-pattern supply and callback fuel nineteen. -/
theorem catchAllMatcher_elaborates :
    MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature 19)
      PPatElaborates DPatElaborates Paper1FrozenSignature.signature
      matcherContext [catchAllClause] ⟨1, 1⟩ catchAllMatcherGenerated
      ⟨9, 3⟩ := by
  have elaboration := M4.elaborateFuel_sound
    Paper1FrozenSignature.wellFormed catchAllMatcher_elaboration_exact
  change MatcherLiteralElaboratesUsing
    (M4.ElaboratesFuel Paper1FrozenSignature.signature 19)
    PPatElaborates DPatElaborates Paper1FrozenSignature.signature
    matcherContext [catchAllClause] ⟨1, 1⟩ catchAllMatcherGenerated ⟨9, 3⟩
    at elaboration
  exact elaboration

/-- A one-hole matcher-literal derivation can be enriched for a variable
input because inspecting that header produces no capture expressions. -/
private theorem variableInput_of_singleHoleClause
    (plain : MatcherLiteralElaboratesUsing expressionRelation PPatElaborates
      DPatElaborates signature context
      [.mk .hole nextMatchers arms] supply generated next) :
    MatcherLiteralTotalInputElaboratesUsing expressionRelation signature
      NoCaptureExpressionTyping solution atomEnvironmentTypes .var context
      [.mk .hole nextMatchers arms] supply generated next := by
  cases plain
  rename_i generatedClauses checked clauses
  cases clauses with
  | cons head tail =>
      cases head
      rename_i generatedHeader afterHeader generatedNext afterNext generatedArms
        nextMatchersElaboration shape headerElaboration armsElaboration
      cases headerElaboration
      cases tail
      exact .mk checked (.cons
        (.mk shape.check_eq_true .hole nextMatchersElaboration
          armsElaboration (by
            intro dispatch inspected
            simp [inspectPatternPattern] at inspected
            subst dispatch
            exact .nil))
        .nil)

/-- The complete actual M4 input derivation used by the producer.  This is a
proof object for the real clause, not a postulated boundary structure. -/
theorem catchAllMatcher_fullInput :
    MatcherLiteralTotalInputElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature 19)
      Paper1FrozenSignature.signature NoCaptureExpressionTyping commonSolution
      [recursiveClosureType] .var matcherContext [catchAllClause] ⟨1, 1⟩
      catchAllMatcherGenerated ⟨9, 3⟩ := by
  simpa [catchAllClause] using
    (variableInput_of_singleHoleClause
      (solution := commonSolution)
      (atomEnvironmentTypes := [recursiveClosureType])
      catchAllMatcher_elaborates)

/-! ## One enclosing M4 `matchAll` output -/

private def matchAllTargetGenerated : Generated :=
  { target := recursiveClosureType
    hard := []
    pending := [] }

def variableGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := [.var ⟨0⟩]
    hard := []
    pending := [] }

theorem variable_elaborates :
    PatternElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature 20)
      Paper1FrozenSignature.signature matcherContext [] .var [] ⟨0, 0⟩
      variableGenerated ⟨1, 1⟩ := by
  exact .var

private def matchAllBodyGenerated : Generated :=
  { target := .var ⟨0⟩
    hard := []
    pending := [] }

def catchAllVariableMatchAllGenerated : Generated :=
  Generated.fromMatchAll matchAllTargetGenerated variableGenerated
    catchAllMatcherGenerated matchAllBodyGenerated

private theorem matchAllTarget_elaborates :
    M4.ElaboratesFuel Paper1FrozenSignature.signature 20 matcherContext
      (.var 0) ⟨0, 0⟩ matchAllTargetGenerated ⟨0, 0⟩ := by
  simp [M4.ElaboratesFuel, matcherContext, matchAllTargetGenerated,
    Scheme.mono, Scheme.instantiate]

private theorem matchAllBody_elaborates :
    M4.ElaboratesFuel Paper1FrozenSignature.signature 20
      (Pattern.extendContext variableGenerated.bindings matcherContext)
      (.var 0) ⟨9, 3⟩ matchAllBodyGenerated ⟨9, 3⟩ := by
  simp [M4.ElaboratesFuel, variableGenerated, matcherContext,
    matchAllBodyGenerated, Pattern.extendContext, Scheme.mono,
    Scheme.instantiate]

/-- Capture-aware component proof for the real enclosing source order. -/
theorem catchAllVariableMatchAll_fullInput :
    Paper1CatchAllVariableMatchAllTotalInputElaboratesUsing
      19 NoCaptureExpressionTyping commonSolution [recursiveClosureType]
      matcherContext (.var 0) (.var 0) ⟨0, 0⟩
      matchAllTargetGenerated ⟨0, 0⟩ variableGenerated ⟨1, 1⟩
      catchAllMatcherGenerated ⟨9, 3⟩ matchAllBodyGenerated ⟨9, 3⟩ := by
  exact
    { targetElaboration := matchAllTarget_elaborates
      patternElaboration := variable_elaborates
      matcherInput := catchAllMatcher_fullInput
      bodyElaboration := matchAllBody_elaborates }

/-- Erasing the capture enrichment yields the actual relational M4
`matchAll` derivation, not merely four similarly named component proofs. -/
theorem catchAllVariableMatchAll_elaborates :
    MatchAllElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature 20)
      Paper1FrozenSignature.signature matcherContext (.var 0)
      (.matcher [catchAllClause]) .var (.var 0) ⟨0, 0⟩
      catchAllVariableMatchAllGenerated ⟨9, 3⟩ := by
  exact catchAllVariableMatchAll_fullInput.toMatchAllElaboratesUsing

/-- The same derivation is the `matchAll` case of the public recursive M4
expression relation at fuel twenty-one. -/
theorem catchAllVariableMatchAll_expressionElaborates :
    M4.ElaboratesFuel Paper1FrozenSignature.signature 21 matcherContext
      (.matchAll (.var 0) (.matcher [catchAllClause]) .var (.var 0)) ⟨0, 0⟩
      catchAllVariableMatchAllGenerated ⟨9, 3⟩ := by
  change MatchAllElaboratesUsing
    (M4.ElaboratesFuel Paper1FrozenSignature.signature 20)
    Paper1FrozenSignature.signature matcherContext (.var 0)
    (.matcher [catchAllClause]) .var (.var 0) ⟨0, 0⟩
    catchAllVariableMatchAllGenerated ⟨9, 3⟩
  exact catchAllVariableMatchAll_elaborates

private theorem recursiveClosureType_apply_common :
    recursiveClosureType.apply commonSolution = recursiveClosureType := by
  rfl

/-- One substitution solves target, pattern, matcher, matcher-to-slot, and
body constraints in the combined block. -/
theorem catchAllVariableMatchAll_semantic :
    catchAllVariableMatchAllGenerated.SemanticSolution commonSolution := by
  constructor
  · intro equation member
    simp [catchAllVariableMatchAllGenerated, matchAllTargetGenerated,
      variableGenerated, catchAllMatcherGenerated, catchClauseGenerated,
      catchNextGenerated, catchArmChecks, catchBodyGenerated,
      matchAllBodyGenerated, Generated.fromMatchAll] at member
    rcases member with rfl | rfl | rfl | rfl
    · change recursiveClosureType = recursiveClosureType.apply commonSolution
      exact recursiveClosureType_apply_common.symm
    · simp [commonSolution, Equation.Holds, Cap.apply]
    · simp [commonSolution, Equation.Holds, Ty.apply, Ty.applyList,
        TypePM.DataTypes.list]
    · simp [commonSolution, Equation.Holds, Ty.apply,
        TypePM.DataTypes.list]
  · intro obligation member
    simp [catchAllVariableMatchAllGenerated, matchAllTargetGenerated,
      variableGenerated, catchAllMatcherGenerated, catchClauseGenerated,
      catchNextGenerated, catchArmChecks, catchBodyGenerated,
      matchAllBodyGenerated, Generated.fromMatchAll] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ⟨.matcherToSlot, by
        simpa [commonSolution, Ty.apply, Cap.apply] using
          (CheckConversion.matcherToSlot CapabilityDemand.equal :
            CheckConversion .matcherToSlot
              (.matcher .any recursiveClosureType)
              (.slot .any recursiveClosureType))⟩
    · exact ⟨.ordinary, by
        simpa [commonSolution, Ty.apply, recursiveClosureType_apply_common] using
          (CheckConversion.ordinary :
            CheckConversion .ordinary recursiveClosureType
              recursiveClosureType)⟩
    · exact ⟨.ordinary, by
        simpa [commonSolution, Ty.apply, Ty.applyList,
          TypePM.DataTypes.list] using
          (CheckConversion.ordinary :
            CheckConversion .ordinary
              (TypePM.DataTypes.list recursiveClosureType)
              (TypePM.DataTypes.list recursiveClosureType))⟩
    · exact ⟨.ordinary, by
        simpa [commonSolution, Ty.apply, Ty.applyList,
          TypePM.DataTypes.list] using
          (CheckConversion.ordinary :
            CheckConversion .ordinary
              (TypePM.DataTypes.list recursiveClosureType)
              (TypePM.DataTypes.list recursiveClosureType))⟩
    · exact ⟨.matcherToSlot, by
        change CheckConversion .matcherToSlot
          (.matcher .any recursiveClosureType)
          (.slot .any (recursiveClosureType.apply commonSolution))
        rw [recursiveClosureType_apply_common]
        exact CheckConversion.matcherToSlot CapabilityDemand.equal⟩

theorem matcherContext_compatible :
    MonomorphicContextCompatible matcherContext [recursiveClosureType]
      commonSolution := by
  exact .cons .nil

/-! ## Actual recursive-closure runtime path -/

def recursiveClosureMatcherValue : Value :=
  .matcherV recursiveClosureEnvironment [catchAllClause] [catchAllClause]

def recursiveClosureUserAtom : MatchingAtom :=
  ⟨.var, recursiveClosureMatcherValue, listRecursiveClosure⟩

def recursiveClosurePrimitiveAtom : MatchingAtom :=
  ⟨.var, .something, listRecursiveClosure⟩

def recursiveClosureBranches : MatchingBranches :=
  [[recursiveClosurePrimitiveAtom]]

theorem recursiveClosureEnvironment_fuelSafe (index : Nat) :
    FuelEnvironmentSafe index recursiveClosureEnvironment
      [recursiveClosureType] := by
  simpa [recursiveClosureEnvironment, recursiveClosureType] using
    TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureEnvironment_fuelSafe
      index

theorem targetEvaluation_exact :
    evalFuel 3 recursiveClosureEnvironment (.var 0) =
      .ok listRecursiveClosure := by
  rfl

theorem matcherEvaluation_exact :
    evalFuel 3 recursiveClosureEnvironment (.matcher [catchAllClause]) =
      .ok recursiveClosureMatcherValue := by
  rfl

set_option maxRecDepth 100000 in
/-- The actual single-clause dispatcher returns the concrete delegated
`something` branch. -/
theorem catchAllMatcher_variable_dispatch_exact :
    dispatchMatcherClauses (evalFuel 3) recursiveClosureEnvironment
      recursiveClosureEnvironment [catchAllClause] .var listRecursiveClosure =
        .ok (.hit recursiveClosureBranches) := by
  with_unfolding_all rfl

/-- Caller relation for exactly the concrete delegated primitive atom. -/
inductive RecursiveClosureAtomRelation : TwoIndexMatchingAtomRelation where
  | primitive :
      RecursiveClosureAtomRelation (searchFuel + 1) residual environmentTypes
        bindingTypes recursiveClosurePrimitiveAtom [recursiveClosureType]

theorem recursiveClosureAtomRelation_downwardClosed :
    TwoIndexMatchingAtomRelation.DownwardClosed
      RecursiveClosureAtomRelation := by
  intro searchFuel residual environmentTypes bindingTypes atom newBindings
    typed
  cases typed
  exact .primitive

theorem recursiveClosurePrimitive_reducer_exact
    (atomEnvironment : ValueEnvironment) :
    evaluationAtomReducer (evalFuel 3) atomEnvironment
      recursiveClosurePrimitiveAtom =
        .ok (.hit ⟨[[]], [listRecursiveClosure]⟩) := by
  rfl

/-- Local preservation checks the recursive closure directly in the indexed
binding relation. -/
theorem recursiveClosureAtomReducer_twoIndexSafe :
    TwoIndexRelationalAtomReducerTypedSafe FuelEnvironmentSafe
      FuelEnvironmentSafe RecursiveClosureAtomRelation
      (evaluationAtomReducer (evalFuel 3)) := by
  intro searchFuel residual environmentTypes bindingTypes environment bindings
    atom newBindings environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | primitive =>
      let reduction : AtomReduction := ⟨[[]], [listRecursiveClosure]⟩
      refine .inr ⟨reduction, ?_, ?_⟩
      · simpa [reduction] using
          recursiveClosurePrimitive_reducer_exact (bindings ++ environment)
      · exact .intro [recursiveClosureType]
          (by simpa [reduction, recursiveClosureEnvironment] using
            recursiveClosureEnvironment_fuelSafe (searchFuel + residual))
          (by
            intro branch member
            simp [reduction] at member
            subst branch
            exact ⟨[], .nil, rfl⟩)

/-- The solved enclosing M4 `matchAll` block plus its bounded local facts
produces the actual fuel-indexed initial state.  There is no premise or earlier
declaration for the completed search. -/
theorem recursiveClosureMatchAll_initial_fromPaper1CatchAllM4AndBoundedLocalWork :
    EvaluatedTwoIndexInitialStateTyping FuelEnvironmentSafe
      FuelEnvironmentSafe 3 1 recursiveClosureEnvironment (.var 0)
      (.matcher [catchAllClause]) .var [recursiveClosureType] := by
  have produced :=
    catchAllVariableMatchAll_fullInput.evaluatedTwoIndexInitialState_of_boundedLocalWork
      (atomRelation := RecursiveClosureAtomRelation)
      (searchFuel := 2) (residual := 1)
      (combinedSemantic := catchAllVariableMatchAll_semantic)
      matcherContext_compatible
      targetEvaluation_exact matcherEvaluation_exact
      (by rw [catchAllMatcher_variable_dispatch_exact]; trivial)
      (by
        intro newBindings branches _matcherSemantic _matcherToSlot patternTyped
          dispatched branch member
        rw [catchAllMatcher_variable_dispatch_exact] at dispatched
        cases dispatched
        simp [recursiveClosureBranches] at member
        subst branch
        cases patternTyped
        exact M4TwoIndexMatchingBranchObligations.cons
          { patternTyped := PatternBinds.var
            atomSafe := ⟨rfl, by
              simpa only [matchAllTargetGenerated,
                recursiveClosureType_apply_common,
                recursiveClosurePrimitiveAtom] using
                (RecursiveClosureAtomRelation.primitive
                  (searchFuel := 1) (residual := 1)
                  (environmentTypes := [recursiveClosureType])
                  (bindingTypes := []))⟩ }
          .nil)
      IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
      IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
      IndexedMatchingInvariant.fuelEnvironmentSafe_appendClosed
      recursiveClosureAtomRelation_downwardClosed
      recursiveClosureAtomReducer_twoIndexSafe
      (recursiveClosureEnvironment_fuelSafe 4)
      (FuelEnvironmentSafe.nil 4)
      (by simp [reduceBuiltinAtom])
  simpa [variableGenerated, commonSolution, Ty.applyList, Ty.apply] using
    produced

/-- The generated initial state is immediately consumable by the generic
whole-`matchAll` composition theorem.  Target/matcher result safety and body
safety are deliberately separate inputs; they are not smuggled into the
initial-state producer. -/
theorem recursiveClosureMatchAll_safe_of_components
    (targetSafe : FuelResultSafe 3 recursiveClosureType
      (evalFuel 3 recursiveClosureEnvironment (.var 0)))
    (matcherSafe : FuelResultSafe 3 (.matcher .any recursiveClosureType)
      (evalFuel 3 recursiveClosureEnvironment (.matcher [catchAllClause])))
    (bodySafe : EvaluatedBindingBodySafeUnder (FuelEnvironmentSafe 1) 3
      resultIndex recursiveClosureEnvironment [recursiveClosureType]
      (.var 0) recursiveClosureType) :
    FuelResultSafe resultIndex (TypePM.DataTypes.list recursiveClosureType)
      (evalFuel 4 recursiveClosureEnvironment
        (.matchAll (.var 0) (.matcher [catchAllClause]) .var (.var 0))) := by
  exact matchAllFuel_twoIndexSafe
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed targetSafe
    matcherSafe
    recursiveClosureMatchAll_initial_fromPaper1CatchAllM4AndBoundedLocalWork
    bodySafe

/-! ## Independent execution witness (not used above) -/

set_option maxRecDepth 100000 in
theorem recursiveClosureSearch_exact :
    searchPatternFuel (evalFuel 3) 3 recursiveClosureEnvironment .var
      recursiveClosureMatcherValue listRecursiveClosure =
        .ok [[listRecursiveClosure]] := by
  with_unfolding_all rfl

/-- This path is genuinely outside the structural runtime environment
relation; its indexed premise is not a repackaged `EnvironmentTyping` proof. -/
theorem recursiveClosureEnvironment_not_environmentTyping :
    ¬ EnvironmentTyping recursiveClosureEnvironment
      [recursiveClosureType] := by
  simpa [recursiveClosureEnvironment, recursiveClosureType] using
    TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureEnvironment_not_environmentTyping

end TypePM.Source.MatcherTyping.M4TwoIndexMatchAllInitialProducerRegression
