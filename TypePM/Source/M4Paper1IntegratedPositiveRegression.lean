import TypePM.Source.FullM4Completion
import TypePM.Source.M4Paper1ClosedMultisetExactRegression
import TypePM.Source.M4RecursiveElaborationRegression
import TypePM.Source.MatcherDemandRegression
import TypePM.Runtime.Paper1ExecutionRegression
import TypePM.Runtime.MatchAllRegression

/-!
# Integrated positive static regressions for Paper 1

The runtime regressions close the source-defined `list` and `multiset`
libraries so that they can execute without an external environment.  The
static examples below expose the corresponding library boundaries explicitly:
the matcher constructor and the specialized matcher are ordinary source
bindings with the exact interfaces already inferred for their closed source
definitions.  This keeps the displayed match sites small enough for a
kernel-checked exact inference trace while preserving the target, pattern,
body, and binding order of the executable fixtures.
-/

namespace TypePM.Source.M4Paper1IntegratedPositiveRegression

open TypePM.Source
open TypePM.Source.Paper1Programs

set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

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

/-! ## Shared library interfaces -/

/-- The concrete `multiset something` producer used at the integer examples. -/
def multisetSomethingIntType : Ty :=
  .matcher (.con PatternFormer.list [.any]) (DataTypes.list .int)

/-- Paper 1's result type for a cons decomposition. -/
def integerConsResultsType : Ty :=
  DataTypes.list (.prod [.int, DataTypes.list .int])

/-- A generalized source-library binding for the already checked closed
`multiset` constructor. -/
def multisetConstructorContext : Context :=
  [Context.generalize []
    M4Paper1ClosedMultisetExactRegression.closedMultisetType]

/-- The source-level specialization `multiset something`, with `multiset`
supplied by the library context above. -/
def multisetSomethingUnderLibraryBinding : Expr :=
  .app (.var 0) .something

def multisetSomethingGenerated : Generated :=
  { target := .var ⟨3⟩
    hard :=
      [.ty
        (.fn (.slot (.var ⟨0⟩) (.var ⟨0⟩))
          (.matcher (.con PatternFormer.list [.var ⟨0⟩])
            (DataTypes.list (.var ⟨0⟩))))
        (.fn (.var ⟨2⟩) (.var ⟨3⟩))]
    pending :=
      [⟨.matcher .any (.var ⟨1⟩), .var ⟨2⟩⟩] }

theorem multiset_something_elaborate_exact :
    M4.elaborate Paper1FrozenSignature.signature multisetConstructorContext
      multisetSomethingUnderLibraryBinding
      multisetConstructorContext.initialSupply =
        some (multisetSomethingGenerated, ⟨4, 1⟩) := by
  unfold M4.elaborate multisetSomethingUnderLibraryBinding
    multisetConstructorContext
  rfl'

theorem multiset_something_close_exact :
    (inferGeneratedUsing unify multisetSomethingGenerated).bind
      (fun closed => some closed.target) =
        some (.matcher (.con PatternFormer.list [.any])
          (DataTypes.list (.var ⟨0⟩))) := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [multisetSomethingGenerated, DataTypes.list]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨1⟩))
          (.slot (.var ⟨0⟩) (.var ⟨0⟩)) =
        .matcherToSlot .any (.var ⟨0⟩) (.var ⟨1⟩)
          (.var ⟨0⟩) .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

/-- Exact public result for the positive `multiset something` specialization
in P1-L07. -/
theorem multiset_something_infer_exact :
    M4.infer Paper1FrozenSignature.signature multisetConstructorContext
      multisetSomethingUnderLibraryBinding =
        some (.matcher (.con PatternFormer.list [.any])
          (DataTypes.list (.var ⟨0⟩))) := by
  unfold M4.infer
  rw [multiset_something_elaborate_exact]
  exact multiset_something_close_exact

/-- Independent M4 typing relation for the positive P1-L07 matcher. -/
theorem multiset_something_typing :
    M4.Typing Paper1FrozenSignature.signature multisetConstructorContext
      multisetSomethingUnderLibraryBinding
        (.matcher (.con PatternFormer.list [.any])
          (DataTypes.list (.var ⟨0⟩))) :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    multiset_something_infer_exact

/-! ## P1-L01: the executable list join site -/

def listJoinResultType : Ty :=
  DataTypes.list (.prod [DataTypes.list .int, DataTypes.list .int])

private def listJoinTargetGenerated : Generated :=
  { target := .var ⟨15⟩
    hard :=
      [ .ty
          (.fn (.var ⟨0⟩)
            (.fn (DataTypes.list (.var ⟨0⟩))
              (DataTypes.list (.var ⟨0⟩))))
          (.fn (.var ⟨1⟩) (.var ⟨2⟩)),
        .ty
          (.fn (.var ⟨3⟩)
            (.fn (DataTypes.list (.var ⟨3⟩))
              (DataTypes.list (.var ⟨3⟩))))
          (.fn (.var ⟨4⟩) (.var ⟨5⟩)),
        .ty
          (.fn (.var ⟨6⟩)
            (.fn (DataTypes.list (.var ⟨6⟩))
              (DataTypes.list (.var ⟨6⟩))))
          (.fn (.var ⟨7⟩) (.var ⟨8⟩)),
        .ty (.var ⟨8⟩) (.fn (.var ⟨10⟩) (.var ⟨11⟩)),
        .ty (.var ⟨5⟩) (.fn (.var ⟨12⟩) (.var ⟨13⟩)),
        .ty (.var ⟨2⟩) (.fn (.var ⟨14⟩) (.var ⟨15⟩)) ]
    pending :=
      [ ⟨.int, .var ⟨1⟩⟩,
        ⟨.int, .var ⟨4⟩⟩,
        ⟨.int, .var ⟨7⟩⟩,
        ⟨DataTypes.list (.var ⟨9⟩), .var ⟨10⟩⟩,
        ⟨.var ⟨11⟩, .var ⟨12⟩⟩,
        ⟨.var ⟨13⟩, .var ⟨14⟩⟩ ] }

private def listJoinPatternGenerated : GeneratedPattern :=
  { dual :=
      { capability := .con PatternFormer.list [.var ⟨0⟩]
        target := DataTypes.list (.var ⟨16⟩) }
    bindings := [.var ⟨17⟩, .var ⟨18⟩]
    hard :=
      [ .ty (.var ⟨17⟩) (DataTypes.list (.var ⟨16⟩)),
        .cap (.var ⟨1⟩) (.con PatternFormer.list [.var ⟨0⟩]),
        .ty (.var ⟨18⟩) (DataTypes.list (.var ⟨16⟩)),
        .cap (.var ⟨2⟩) (.con PatternFormer.list [.var ⟨0⟩]) ]
    pending := [] }

private def listJoinSomethingGenerated : Generated :=
  { target := .matcher .any (.var ⟨105⟩), hard := [], pending := [] }

private def listJoinMatcherGenerated : Generated :=
  Generated.fromApp
    (M4Paper1ListExactRegression.listGeneratedAt ⟨19, 3⟩)
    listJoinSomethingGenerated (.var ⟨106⟩) (.var ⟨107⟩)

private def listJoinBodyGenerated : Generated :=
  { target := .prod [.var ⟨17⟩, .var ⟨18⟩], hard := [], pending := [] }

private def listJoinGenerated : Generated :=
  Generated.fromMatchAll listJoinTargetGenerated listJoinPatternGenerated
    listJoinMatcherGenerated listJoinBodyGenerated

private def listJoinCallback : M4.ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 149

private theorem list_join_target_exact :
    listJoinCallback [] Runtime.Paper1ExecutionRegression.target123 ⟨0, 0⟩ =
      some (listJoinTargetGenerated, ⟨16, 0⟩) := by
  rfl'

private theorem list_join_pattern_exact :
    elaboratePatternUsing listJoinCallback Paper1FrozenSignature.signature
      [] [] (.ctor PatternCtor.join [.var, .var]) [] ⟨16, 0⟩ =
      some (listJoinPatternGenerated, ⟨19, 3⟩) := by
  rfl'

private theorem list_join_matcher_exact :
    listJoinCallback []
      (.app listMatcherDefinition .something) ⟨19, 3⟩ =
      some (listJoinMatcherGenerated, ⟨108, 17⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 148 [] listMatcherDefinition
    ⟨19, 3⟩).bind _ = _
  have listAt148 := M4.elaborateFuelUsing_success_mono
    (solveHard := unifyWithFuel 500)
    (signature := Paper1FrozenSignature.signature)
    (smaller := 124) (larger := 148) (by omega)
    M4Paper1ListExactRegression.listJoin_structural_fuel_exact
  rw [listAt148]
  rfl

private theorem list_join_body_exact :
    listJoinCallback
      [.mono (.var ⟨17⟩), .mono (.var ⟨18⟩)]
      (.tuple [.var 0, .var 1]) ⟨108, 17⟩ =
      some (listJoinBodyGenerated, ⟨108, 17⟩) := by
  rfl'

private theorem list_join_structural_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 150 []
      Runtime.Paper1ExecutionRegression.listJoinAll ⟨0, 0⟩ =
      some (listJoinGenerated, ⟨108, 17⟩) := by
  change elaborateMatchAllUsing listJoinCallback
    Paper1FrozenSignature.signature []
    Runtime.Paper1ExecutionRegression.target123
    (.app listMatcherDefinition .something)
    (.ctor PatternCtor.join [.var, .var])
    (.tuple [.var 0, .var 1]) ⟨0, 0⟩ = _
  unfold elaborateMatchAllUsing
  simp only [list_join_target_exact, list_join_pattern_exact,
    list_join_matcher_exact, list_join_body_exact,
    Option.bind_eq_bind, Option.bind_some]
  rfl

private theorem list_join_close_exact :
    (inferGeneratedUsing (unifyWithFuel 2000) listJoinGenerated).bind
      (fun closed => some closed.target) = some listJoinResultType := by
  simp only [listJoinGenerated, listJoinTargetGenerated,
    listJoinPatternGenerated, listJoinMatcherGenerated,
    listJoinSomethingGenerated, listJoinBodyGenerated,
    M4Paper1ListExactRegression.listGeneratedAt,
    M4Paper1ListExactRegression.translateGenerated,
    Generated.fromMatchAll, Generated.fromApp, listJoinResultType]
  rfl'

theorem list_join_infer_exact :
    M4.infer Paper1FrozenSignature.signature []
      Runtime.Paper1ExecutionRegression.listJoinAll =
      some listJoinResultType := by
  have elaborated :=
    M4.elaborateFuel_success_of_solverFuel_success list_join_structural_exact
  cases closureEquality :
      inferGeneratedUsing (unifyWithFuel 2000) listJoinGenerated with
  | none =>
      have impossible := list_join_close_exact
      simp [closureEquality] at impossible
  | some closed =>
      have closedTarget : closed.target = listJoinResultType := by
        have exactTarget := list_join_close_exact
        simpa [closureEquality] using exactTarget
      have publicClosure :=
        inferGeneratedUsing_unify_of_fuel_success closureEquality
      unfold M4.infer M4.elaborate
      rw [show Runtime.Paper1ExecutionRegression.listJoinAll.complexity + 1 =
        150 by rfl]
      rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl]
      rw [elaborated]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [publicClosure]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [closedTarget]
      rfl

theorem list_join_typing :
    M4.Typing Paper1FrozenSignature.signature []
      Runtime.Paper1ExecutionRegression.listJoinAll listJoinResultType :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    list_join_infer_exact

/-! ## P1-L05: direct multiset-cons decomposition -/

def multisetConsResultType : Ty :=
  DataTypes.list (.prod [.int, DataTypes.list .int])

private def multisetConsPatternGenerated : GeneratedPattern :=
  { dual :=
      { capability := .con PatternFormer.list [.var ⟨0⟩]
        target := DataTypes.list (.var ⟨16⟩) }
    bindings := [.var ⟨17⟩, .var ⟨18⟩]
    hard :=
      [ .ty (.var ⟨17⟩) (.var ⟨16⟩),
        .cap (.var ⟨1⟩) (.var ⟨0⟩),
        .ty (.var ⟨18⟩) (DataTypes.list (.var ⟨16⟩)),
        .cap (.var ⟨2⟩) (.con PatternFormer.list [.var ⟨0⟩]) ]
    pending := [] }

private def multisetConsSomethingGenerated : Generated :=
  { target := .matcher .any (.var ⟨258⟩), hard := [], pending := [] }

private def multisetConsMatcherGenerated : Generated :=
  Generated.fromApp
    M4Paper1ClosedMultisetExactRegression.closedGeneratedAt19
    multisetConsSomethingGenerated (.var ⟨259⟩) (.var ⟨260⟩)

private def multisetConsBodyGenerated : Generated :=
  { target := .prod [.var ⟨17⟩, .var ⟨18⟩], hard := [], pending := [] }

private def multisetConsGenerated : Generated :=
  Generated.fromMatchAll listJoinTargetGenerated multisetConsPatternGenerated
    multisetConsMatcherGenerated multisetConsBodyGenerated

private def multisetConsCallback : M4.ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 384

private theorem multiset_cons_target_exact :
    multisetConsCallback [] Runtime.Paper1ExecutionRegression.target123
      ⟨0, 0⟩ = some (listJoinTargetGenerated, ⟨16, 0⟩) := by
  rfl'

private theorem multiset_cons_pattern_exact :
    elaboratePatternUsing multisetConsCallback Paper1FrozenSignature.signature
      [] [] (.ctor PatternCtor.cons [.var, .var]) [] ⟨16, 0⟩ =
      some (multisetConsPatternGenerated, ⟨19, 3⟩) := by
  rfl'

private theorem multiset_cons_matcher_exact :
    multisetConsCallback [] multisetSomething ⟨19, 3⟩ =
      some (multisetConsMatcherGenerated, ⟨261, 48⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 383 [] closedMultisetDefinition
    ⟨19, 3⟩).bind _ = _
  have closedAt383 := M4.elaborateFuelUsing_success_mono
    (solveHard := unifyWithFuel 500)
    (signature := Paper1FrozenSignature.signature)
    (smaller := 359) (larger := 383) (by omega)
    M4Paper1ClosedMultisetExactRegression.closed_origin19_structural_fuel_exact
  rw [closedAt383]
  rfl

private theorem multiset_cons_body_exact :
    multisetConsCallback
      [.mono (.var ⟨17⟩), .mono (.var ⟨18⟩)]
      (.tuple [.var 0, .var 1]) ⟨261, 48⟩ =
      some (multisetConsBodyGenerated, ⟨261, 48⟩) := by
  rfl'

private theorem multiset_cons_structural_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 385 []
      Runtime.Paper1ExecutionRegression.multisetCons ⟨0, 0⟩ =
      some (multisetConsGenerated, ⟨261, 48⟩) := by
  change elaborateMatchAllUsing multisetConsCallback
    Paper1FrozenSignature.signature []
    Runtime.Paper1ExecutionRegression.target123 multisetSomething
    (.ctor PatternCtor.cons [.var, .var])
    (.tuple [.var 0, .var 1]) ⟨0, 0⟩ = _
  unfold elaborateMatchAllUsing
  simp only [multiset_cons_target_exact, multiset_cons_pattern_exact,
    multiset_cons_matcher_exact, multiset_cons_body_exact,
    Option.bind_eq_bind, Option.bind_some]
  rfl

private theorem multiset_cons_close_exact :
    (inferGeneratedUsing (unifyWithFuel 4000) multisetConsGenerated).bind
      (fun closed => some closed.target) = some multisetConsResultType := by
  simp only [multisetConsGenerated, listJoinTargetGenerated,
    multisetConsPatternGenerated, multisetConsMatcherGenerated,
    multisetConsSomethingGenerated, multisetConsBodyGenerated,
    M4Paper1ClosedMultisetExactRegression.closedGeneratedAt19,
    M4Paper1ClosedMultisetExactRegression.multisetFunctionGeneratedAt,
    M4Paper1ListExactRegression.listGeneratedAt,
    M4Paper1ListExactRegression.translateGenerated,
    Generated.fromMatchAll, Generated.fromApp, multisetConsResultType]
  rfl'

theorem multiset_cons_infer_exact :
    M4.infer Paper1FrozenSignature.signature []
      Runtime.Paper1ExecutionRegression.multisetCons =
      some multisetConsResultType := by
  have elaborated :=
    M4.elaborateFuel_success_of_solverFuel_success
      multiset_cons_structural_exact
  cases closureEquality :
      inferGeneratedUsing (unifyWithFuel 4000) multisetConsGenerated with
  | none =>
      have impossible := multiset_cons_close_exact
      simp [closureEquality] at impossible
  | some closed =>
      have closedTarget : closed.target = multisetConsResultType := by
        have exactTarget := multiset_cons_close_exact
        simpa [closureEquality] using exactTarget
      have publicClosure :=
        inferGeneratedUsing_unify_of_fuel_success closureEquality
      unfold M4.infer M4.elaborate
      rw [show Runtime.Paper1ExecutionRegression.multisetCons.complexity + 1 =
        385 by rfl]
      rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl]
      rw [elaborated]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [publicClosure]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [closedTarget]
      rfl

theorem multiset_cons_typing :
    M4.Typing Paper1FrozenSignature.signature []
      Runtime.Paper1ExecutionRegression.multisetCons multisetConsResultType :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    multiset_cons_infer_exact

/-! ## P1-L02: successor pairs under the closed multiset matcher -/

def successorPairsResultType : Ty := DataTypes.list .int

private def successorTargetGenerated : Generated :=
  { target := .var ⟨20⟩
    hard :=
      [ .ty
          (.fn (.var ⟨0⟩)
            (.fn (DataTypes.list (.var ⟨0⟩))
              (DataTypes.list (.var ⟨0⟩))))
          (.fn (.var ⟨1⟩) (.var ⟨2⟩)),
        .ty
          (.fn (.var ⟨3⟩)
            (.fn (DataTypes.list (.var ⟨3⟩))
              (DataTypes.list (.var ⟨3⟩))))
          (.fn (.var ⟨4⟩) (.var ⟨5⟩)),
        .ty
          (.fn (.var ⟨6⟩)
            (.fn (DataTypes.list (.var ⟨6⟩))
              (DataTypes.list (.var ⟨6⟩))))
          (.fn (.var ⟨7⟩) (.var ⟨8⟩)),
        .ty
          (.fn (.var ⟨9⟩)
            (.fn (DataTypes.list (.var ⟨9⟩))
              (DataTypes.list (.var ⟨9⟩))))
          (.fn (.var ⟨10⟩) (.var ⟨11⟩)),
        .ty (.var ⟨11⟩) (.fn (.var ⟨13⟩) (.var ⟨14⟩)),
        .ty (.var ⟨8⟩) (.fn (.var ⟨15⟩) (.var ⟨16⟩)),
        .ty (.var ⟨5⟩) (.fn (.var ⟨17⟩) (.var ⟨18⟩)),
        .ty (.var ⟨2⟩) (.fn (.var ⟨19⟩) (.var ⟨20⟩)) ]
    pending :=
      [ ⟨.int, .var ⟨1⟩⟩,
        ⟨.int, .var ⟨4⟩⟩,
        ⟨.int, .var ⟨7⟩⟩,
        ⟨.int, .var ⟨10⟩⟩,
        ⟨DataTypes.list (.var ⟨12⟩), .var ⟨13⟩⟩,
        ⟨.var ⟨14⟩, .var ⟨15⟩⟩,
        ⟨.var ⟨16⟩, .var ⟨17⟩⟩,
        ⟨.var ⟨18⟩, .var ⟨19⟩⟩ ] }

private def successorPatternGenerated : GeneratedPattern :=
  { dual :=
      { capability := .con PatternFormer.list [.var ⟨0⟩]
        target := DataTypes.list (.var ⟨21⟩) }
    bindings := [.var ⟨22⟩]
    hard :=
      [ .ty (.fn .int (.fn .int .int))
          (.fn (.var ⟨24⟩) (.var ⟨25⟩)),
        .ty (.var ⟨25⟩) (.fn (.var ⟨26⟩) (.var ⟨27⟩)),
        .ty (.var ⟨27⟩) (.var ⟨23⟩),
        .cap (.var ⟨3⟩) (.var ⟨2⟩),
        .ty (.var ⟨28⟩) (DataTypes.list (.var ⟨23⟩)),
        .cap (.var ⟨4⟩) (.con PatternFormer.list [.var ⟨2⟩]),
        .ty (.var ⟨22⟩) (.var ⟨21⟩),
        .cap (.var ⟨1⟩) (.var ⟨0⟩),
        .ty (DataTypes.list (.var ⟨23⟩)) (DataTypes.list (.var ⟨21⟩)),
        .cap (.con PatternFormer.list [.var ⟨2⟩])
          (.con PatternFormer.list [.var ⟨0⟩]) ]
    pending :=
      [ ⟨.var ⟨22⟩, .var ⟨24⟩⟩,
        ⟨.int, .var ⟨26⟩⟩ ] }

private def successorSomethingGenerated : Generated :=
  { target := .matcher .any (.var ⟨268⟩), hard := [], pending := [] }

private def successorMatcherGenerated : Generated :=
  Generated.fromApp
    M4Paper1ClosedMultisetExactRegression.closedGeneratedAt29
    successorSomethingGenerated (.var ⟨269⟩) (.var ⟨270⟩)

private def successorBodyGenerated : Generated :=
  { target := .var ⟨22⟩, hard := [], pending := [] }

private def successorGenerated : Generated :=
  Generated.fromMatchAll successorTargetGenerated successorPatternGenerated
    successorMatcherGenerated successorBodyGenerated

private def successorCallback : M4.ExpressionElaborator :=
  M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 393

private theorem successor_target_exact :
    successorCallback []
      (sourceList [.lit 1, .lit 2, .lit 5, .lit 6]) ⟨0, 0⟩ =
      some (successorTargetGenerated, ⟨21, 0⟩) := by
  rfl'

private theorem successor_pattern_exact :
    elaboratePatternUsing successorCallback Paper1FrozenSignature.signature
      [] [] Runtime.Paper1ExecutionRegression.successorPattern [] ⟨21, 0⟩ =
      some (successorPatternGenerated, ⟨29, 5⟩) := by
  rfl'

private theorem successor_matcher_exact :
    successorCallback [] multisetSomething ⟨29, 5⟩ =
      some (successorMatcherGenerated, ⟨271, 50⟩) := by
  change (M4.elaborateFuelUsing (unifyWithFuel 500)
    Paper1FrozenSignature.signature 392 [] closedMultisetDefinition
    ⟨29, 5⟩).bind _ = _
  have closedAt392 := M4.elaborateFuelUsing_success_mono
    (solveHard := unifyWithFuel 500)
    (signature := Paper1FrozenSignature.signature)
    (smaller := 359) (larger := 392) (by omega)
    M4Paper1ClosedMultisetExactRegression.closed_origin29_structural_fuel_exact
  rw [closedAt392]
  rfl

private theorem successor_body_exact :
    successorCallback [.mono (.var ⟨22⟩)] (.var 0) ⟨271, 50⟩ =
      some (successorBodyGenerated, ⟨271, 50⟩) := by
  rfl'

private theorem successor_structural_exact :
    M4.elaborateFuelUsing (unifyWithFuel 500)
      Paper1FrozenSignature.signature 394 []
      Runtime.Paper1ExecutionRegression.successorPairs ⟨0, 0⟩ =
      some (successorGenerated, ⟨271, 50⟩) := by
  change elaborateMatchAllUsing successorCallback
    Paper1FrozenSignature.signature []
    (sourceList [.lit 1, .lit 2, .lit 5, .lit 6]) multisetSomething
    Runtime.Paper1ExecutionRegression.successorPattern (.var 0) ⟨0, 0⟩ = _
  unfold elaborateMatchAllUsing
  simp only [successor_target_exact, successor_pattern_exact,
    successor_matcher_exact, successor_body_exact,
    Option.bind_eq_bind, Option.bind_some]
  rfl

private theorem successor_close_exact :
    (inferGeneratedUsing (unifyWithFuel 5000) successorGenerated).bind
      (fun closed => some closed.target) = some successorPairsResultType := by
  simp only [successorGenerated, successorTargetGenerated,
    successorPatternGenerated, successorMatcherGenerated,
    successorSomethingGenerated, successorBodyGenerated,
    M4Paper1ClosedMultisetExactRegression.closedGeneratedAt29,
    M4Paper1ClosedMultisetExactRegression.multisetFunctionGeneratedAt,
    M4Paper1ListExactRegression.listGeneratedAt,
    M4Paper1ListExactRegression.translateGenerated,
    Generated.fromMatchAll, Generated.fromApp, successorPairsResultType]
  rfl'

theorem successor_pairs_infer_exact :
    M4.infer Paper1FrozenSignature.signature []
      Runtime.Paper1ExecutionRegression.successorPairs =
      some successorPairsResultType := by
  have elaborated :=
    M4.elaborateFuel_success_of_solverFuel_success successor_structural_exact
  cases closureEquality :
      inferGeneratedUsing (unifyWithFuel 5000) successorGenerated with
  | none =>
      have impossible := successor_close_exact
      simp [closureEquality] at impossible
  | some closed =>
      have closedTarget : closed.target = successorPairsResultType := by
        have exactTarget := successor_close_exact
        simpa [closureEquality] using exactTarget
      have publicClosure :=
        inferGeneratedUsing_unify_of_fuel_success closureEquality
      unfold M4.infer M4.elaborate
      rw [show Runtime.Paper1ExecutionRegression.successorPairs.complexity + 1 =
        394 by rfl]
      rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl]
      rw [elaborated]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [publicClosure]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [closedTarget]
      rfl

theorem successor_pairs_typing :
    M4.Typing Paper1FrozenSignature.signature []
      Runtime.Paper1ExecutionRegression.successorPairs
      successorPairsResultType :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    successor_pairs_infer_exact

/-! ## P1-L04: the open multiset definition under the list binding -/

theorem open_multiset_with_list_context_infer_exact :
    M4.infer Paper1FrozenSignature.signature
      M4Paper1ClosedMultisetExactRegression.listLibraryContext
      multisetDefinition =
      some M4Paper1ClosedMultisetExactRegression.openMultisetWithListContextType :=
  M4Paper1ClosedMultisetExactRegression.open_multiset_with_list_context_infer_exact

theorem open_multiset_with_list_context_typing :
    M4.Typing Paper1FrozenSignature.signature
      M4Paper1ClosedMultisetExactRegression.listLibraryContext
      multisetDefinition
      M4Paper1ClosedMultisetExactRegression.openMultisetWithListContextType :=
  M4Paper1ClosedMultisetExactRegression.open_multiset_with_list_context_typing

/-! ## P1-L07: the accepted `unconsWith` call -/

/-- Correct specialization of `unconsWith`: its matcher slot and its target
both range over `List Int`.  The older negative fixture intentionally uses a
different, rejected interface and is not reused here. -/
def positiveUnconsWithType : Ty :=
  .fn (.slot (.con PatternFormer.list [.any]) (DataTypes.list .int))
    (.fn (DataTypes.list .int) integerConsResultsType)

def positiveUnconsWithContext : Context :=
  [ Scheme.mono (DataTypes.list .int),
    Scheme.mono multisetSomethingIntType,
    Scheme.mono positiveUnconsWithType ]

/-- `unconsWith (multiset something) [1,2,3]`, after the three named source
library values have been placed in the context in newest-first order. -/
def unconsWithMultisetSomething : Expr :=
  .app (.app (.var 2) (.var 1)) (.var 0)

def unconsWithMultisetSomethingGenerated : Generated :=
  { target := .var ⟨3⟩
    hard :=
      [ .ty positiveUnconsWithType (.fn (.var ⟨0⟩) (.var ⟨1⟩)),
        .ty (.var ⟨1⟩) (.fn (.var ⟨2⟩) (.var ⟨3⟩)) ]
    pending :=
      [ ⟨multisetSomethingIntType, .var ⟨0⟩⟩,
        ⟨DataTypes.list .int, .var ⟨2⟩⟩ ] }

theorem uncons_with_multiset_something_elaborate_exact :
    M4.elaborate Paper1FrozenSignature.signature positiveUnconsWithContext
      unconsWithMultisetSomething positiveUnconsWithContext.initialSupply =
        some (unconsWithMultisetSomethingGenerated, ⟨4, 0⟩) := by
  unfold M4.elaborate positiveUnconsWithContext
    unconsWithMultisetSomething unconsWithMultisetSomethingGenerated
    positiveUnconsWithType multisetSomethingIntType integerConsResultsType
  rfl'

theorem uncons_with_multiset_something_close_exact :
    (inferGeneratedUsing unify unconsWithMultisetSomethingGenerated).bind
      (fun closed => some closed.target) = some integerConsResultsType := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [unconsWithMultisetSomethingGenerated, positiveUnconsWithType,
    multisetSomethingIntType, integerConsResultsType, DataTypes.list]
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
      resolve
          (.matcher (.con PatternFormer.list [.any])
            (.data DataFormer.list [.int]))
          (.slot (.con PatternFormer.list [.any])
            (.data DataFormer.list [.int])) =
        .matcherToSlot (.con PatternFormer.list [.any])
          (.con PatternFormer.list [.any])
          (.data DataFormer.list [.int])
          (.data DataFormer.list [.int]) .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

theorem uncons_with_multiset_something_infer_exact :
    M4.infer Paper1FrozenSignature.signature positiveUnconsWithContext
      unconsWithMultisetSomething = some integerConsResultsType := by
  unfold M4.infer
  rw [uncons_with_multiset_something_elaborate_exact]
  exact uncons_with_multiset_something_close_exact

theorem uncons_with_multiset_something_typing :
    M4.Typing Paper1FrozenSignature.signature positiveUnconsWithContext
      unconsWithMultisetSomething integerConsResultsType :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    uncons_with_multiset_something_infer_exact

/-! ## P1-L14: normal value-pattern mismatch -/

theorem normal_mismatch_elaborate_exact :
    M4.elaborate Paper1FrozenSignature.signature []
      Runtime.MatchAllRegression.paperIntegerValueMismatch ⟨0, 0⟩ =
        some (M4RecursiveElaborationRegression.valuePatternGenerated,
          ⟨1, 1⟩) := by
  unfold M4.elaborate Runtime.MatchAllRegression.paperIntegerValueMismatch
  rfl'

/-- P1-L14 is statically accepted with `List Int`; its empty runtime result
is a normal mismatch, not a typing failure. -/
theorem normal_mismatch_infer_exact :
    M4.infer Paper1FrozenSignature.signature []
      Runtime.MatchAllRegression.paperIntegerValueMismatch =
        some (DataTypes.list .int) := by
  unfold M4.infer
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    normal_mismatch_elaborate_exact]
  exact M4RecursiveElaborationRegression.close_value_pattern_exact

theorem normal_mismatch_typing :
    M4.Typing Paper1FrozenSignature.signature []
      Runtime.MatchAllRegression.paperIntegerValueMismatch
        (DataTypes.list .int) :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    normal_mismatch_infer_exact

end TypePM.Source.M4Paper1IntegratedPositiveRegression
