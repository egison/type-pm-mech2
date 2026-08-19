import TypePM.Source.M4Elaboration
import TypePM.Source.M4FrozenSignatureRegression

/-!
# M4 user-pattern and match-site regressions

The negative cases correspond to the static errors highlighted in Paper 1's
appendix: a value pattern before its binder, an occurs-check failure in a list
tail, a list-valued expression in an integer pattern position, and the
inability of `something` to satisfy a constructor-shaped capability demand.
-/

namespace TypePM.Source.M4PatternTypingRegression

set_option linter.unusedSimpArgs false

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

def targetContext : Context := [Scheme.mono (DataTypes.list .int)]

def leftToRightValue : Pattern :=
  .tuple [.var, .value (.var 0)]

def valueBeforeBinder : Pattern :=
  .tuple [.value (.var 0), .var]

def occursTail : Pattern :=
  .ctor .cons [.var, .value (.var 0)]

def consPattern : Pattern :=
  .ctor .cons [.var, .wild]

/-- Source-order bindings are prepended without reversing them. -/
theorem binding_context_source_order (first second : Ty) (context : Context) :
    Pattern.extendContext [first, second] context =
      Scheme.mono first :: Scheme.mono second :: context := by
  rfl

/-- A value expression can read a binder synthesized to its left. -/
theorem value_after_binder_elaborates :
    elaboratePattern Paper1FrozenSignature.signature [] []
      leftToRightValue [] ⟨0, 0⟩ ≠ none := by
  simp [leftToRightValue, elaboratePattern, elaboratePatterns,
    Pattern.extendContext, elaborate, Scheme.mono, Scheme.instantiate]

/-- Reversing those two subpatterns leaves the value expression unbound. -/
theorem value_before_binder_rejected :
    inferPattern Paper1FrozenSignature.signature [] [] valueBeforeBinder =
      none := by
  simp [inferPattern, valueBeforeBinder, elaboratePattern,
    elaboratePatterns, Pattern.extendContext, elaborate,
    Scheme.mono, Scheme.instantiate]

def occursGenerated : GeneratedPattern :=
  { dual := ⟨.con PatternFormer.list [.var ⟨0⟩],
      DataTypes.list (.var ⟨0⟩)⟩
    bindings := [.var ⟨1⟩]
    hard := [
      .ty (.var ⟨1⟩) (.var ⟨0⟩),
      .cap (.var ⟨1⟩) (.var ⟨0⟩),
      .ty (.var ⟨1⟩) (DataTypes.list (.var ⟨0⟩)),
      .cap (.var ⟨2⟩) (.con PatternFormer.list [.var ⟨0⟩])]
    pending := [] }

theorem elaborate_occurs_tail_exact :
    elaboratePattern Paper1FrozenSignature.signature [] [] occursTail []
      ⟨0, 0⟩ = some (occursGenerated, ⟨2, 3⟩) := by
  simp [occursTail, occursGenerated, elaboratePattern, elaboratePatterns,
    Pattern.fieldEquations, Pattern.extendContext, elaborate,
    Scheme.mono, Scheme.instantiate,
    Paper1FrozenSignature.lookup_pattern_cons, DualScheme.instantiate,
    ListPatternSchemes.cons, PolyDual.openBound, PolyCap.openBound,
    PolyCap.openBoundList, PolyTy.openBound, PolyTy.openBoundList,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    PolyDataTypes.list, DataTypes.list]

theorem close_occurs_tail_none :
    inferGeneratedUsing unify
      ⟨occursGenerated.dual.target, occursGenerated.hard,
        occursGenerated.pending⟩ = none := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [occursGenerated, DataTypes.list]
  compute_unification

/-- The first binder would have to equal its own list type. -/
theorem occurs_check_tail_rejected :
    inferPattern Paper1FrozenSignature.signature [] [] occursTail = none := by
  unfold inferPattern
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    elaborate_occurs_tail_exact]
  simp [close_occurs_tail_none]

/-- Minimal hard constraints left by an integer/list value-pattern mismatch.
The outer list targets agree, but its value-pattern field would require a
list to be an integer. -/
def valueMismatchEquations : List Equation :=
  [ .ty (DataTypes.list (.var ⟨0⟩)) (DataTypes.list .int),
    .ty (DataTypes.list (.var ⟨1⟩)) (.var ⟨0⟩) ]

theorem value_expression_int_list_mismatch_rejected :
    unify valueMismatchEquations = none := by
  unfold unify
  simp only [valueMismatchEquations, DataTypes.list]
  compute_unification

/-- `matchAll` puts target agreement before the pattern's internal
constraints and puts matcher use in the delayed, directional list. -/
theorem matchAll_constraint_boundary
    (target matcher body : Generated) (pattern : GeneratedPattern) :
    (Generated.fromMatchAll target pattern matcher body).hard =
        target.hard ++ [.ty pattern.dual.target target.target] ++
          pattern.hard ++ matcher.hard ++ body.hard ∧
      (Generated.fromMatchAll target pattern matcher body).pending =
        target.pending ++ pattern.pending ++ matcher.pending ++
          [⟨matcher.target, .slot pattern.dual.capability target.target⟩] ++
            body.pending := by
  constructor <;> rfl

def variableMatchGenerated : Generated :=
  { target := DataTypes.list (.var ⟨0⟩)
    hard := [.ty (.var ⟨0⟩) (DataTypes.list .int)]
    pending := [⟨.matcher .any (.var ⟨1⟩),
      .slot (.var ⟨0⟩) (DataTypes.list .int)⟩] }

theorem elaborate_variable_match_exact :
    elaborateMatchAll Paper1FrozenSignature.signature targetContext
      (.var 0) .something .var (.var 0) ⟨0, 0⟩ =
      some (variableMatchGenerated, ⟨2, 1⟩) := by
  simp [elaborateMatchAll, targetContext, variableMatchGenerated,
    elaboratePattern, Pattern.extendContext, elaborate,
    Generated.fromMatchAll, Scheme.mono, Scheme.instantiate,
    DataTypes.list, Supply.nextTy]

theorem close_variable_match_exact :
    (inferGeneratedUsing unify variableMatchGenerated).bind
      (fun closed => some closed.target) =
      some (DataTypes.list (DataTypes.list .int)) := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [variableMatchGenerated, DataTypes.list]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨1⟩))
          (.slot (.var ⟨0⟩) (.data DataFormer.list [.int])) =
        .matcherToSlot .any (.var ⟨0⟩) (.var ⟨1⟩)
          (.data DataFormer.list [.int]) .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

theorem infer_variable_match_exact :
    inferMatchAll Paper1FrozenSignature.signature targetContext (.var 0)
      .something .var (.var 0) =
        some (DataTypes.list (DataTypes.list .int)) := by
  unfold inferMatchAll
  rw [show Context.initialSupply targetContext = ⟨0, 0⟩ by rfl,
    elaborate_variable_match_exact]
  simpa using close_variable_match_exact

/-- `something` selects matcher-to-slot conversion, but its fixed `Any`
producer capability then yields an impossible equality against the cons
pattern's list-shaped consumer capability. -/
theorem something_cons_resolution_exact :
    (resolve (.matcher .any .int)
      (.slot (.con PatternFormer.list [.var ⟨0⟩]) .int)).equations =
      [ .cap .any (.con PatternFormer.list [.var ⟨0⟩]),
        .ty .int .int ] := by
  rfl

theorem something_cons_capability_rejected :
    unify
      [ .cap .any (.con PatternFormer.list [.var ⟨0⟩]),
        .ty .int .int ] = none := by
  unfold unify
  compute_unification

/-- Embedded pattern arguments are read, not re-synthesized. -/
theorem embed_reads_pattern_context (dual : Dual) (supply : Supply) :
    elaboratePattern Paper1FrozenSignature.signature [] [dual] (.embed 0)
      [] supply = some (⟨dual, [], [], []⟩, supply) := by
  simp [elaboratePattern]

/-- Named pattern application consults only its frozen stored scheme. -/
theorem stored_pattern_function_interface_only :
    elaboratePattern M4FrozenSignatureRegression.onePatternFunction [] []
      (.app M4FrozenSignatureRegression.emptyListPattern []) [] ⟨0, 0⟩ =
      some
        (⟨(ListPatternSchemes.nil.instantiate ⟨0, 0⟩).1.result,
          [], [], []⟩,
          (ListPatternSchemes.nil.instantiate ⟨0, 0⟩).2) := by
  simp [elaboratePattern,
    M4FrozenSignatureRegression.lookup_emptyList_exact,
    elaboratePatterns, Pattern.fieldEquations, ListPatternSchemes.nil,
    DualScheme.instantiate]

theorem variable_match_relational :
    MatchAllElaborates Paper1FrozenSignature.signature targetContext
      (.var 0) .something .var (.var 0) ⟨0, 0⟩
      variableMatchGenerated ⟨2, 1⟩ :=
  elaborateMatchAll_sound Paper1FrozenSignature.wellFormed
    elaborate_variable_match_exact

end TypePM.Source.M4PatternTypingRegression
