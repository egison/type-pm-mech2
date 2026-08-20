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
