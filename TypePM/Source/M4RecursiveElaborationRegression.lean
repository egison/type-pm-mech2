import TypePM.Source.M4RecursiveElaboration
import TypePM.Source.Paper1Programs

namespace TypePM.Source.M4RecursiveElaborationRegression

open TypePM.Source
open TypePM.Source.Paper1Programs

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

def valuePatternMatch : Expr :=
  .matchAll (.lit 1) .something (.value (.lit 1)) (.lit 2)

def firstMatch : Expr :=
  .matchFirst (.lit 1) .something [.mk .wild (.lit 2)]

def valuePatternGenerated : Generated :=
  { target := DataTypes.list .int
    hard := [.ty .int .int]
    pending := [⟨.matcher .any (.var ⟨0⟩), .slot (.var ⟨0⟩) .int⟩] }

def firstMatchGenerated : Generated :=
  { target := .int
    hard := [.ty (.var ⟨1⟩) .int]
    pending := [⟨.matcher .any (.var ⟨0⟩), .slot (.var ⟨0⟩) .int⟩] }

theorem elaborate_value_pattern_exact :
    M4.elaborate Paper1FrozenSignature.signature [] valuePatternMatch ⟨0, 0⟩ =
      some (valuePatternGenerated, ⟨1, 1⟩) := by
  rfl'

theorem elaborate_match_first_exact :
    M4.elaborate Paper1FrozenSignature.signature [] firstMatch ⟨0, 0⟩ =
      some (firstMatchGenerated, ⟨2, 1⟩) := by
  rfl'

theorem close_value_pattern_exact :
    (inferGeneratedUsing unify valuePatternGenerated).bind
      (fun closed => some closed.target) = some (DataTypes.list .int) := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [valuePatternGenerated, DataTypes.list]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨0⟩)) (.slot (.var ⟨0⟩) .int) =
        .matcherToSlot .any (.var ⟨0⟩) (.var ⟨0⟩) .int .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

theorem close_match_first_exact :
    (inferGeneratedUsing unify firstMatchGenerated).bind
      (fun closed => some closed.target) = some .int := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [firstMatchGenerated]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨0⟩)) (.slot (.var ⟨0⟩) .int) =
        .matcherToSlot .any (.var ⟨0⟩) (.var ⟨0⟩) .int .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

theorem infer_value_pattern_exact :
    M4.infer Paper1FrozenSignature.signature [] valuePatternMatch =
      some (DataTypes.list .int) := by
  unfold M4.infer
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    elaborate_value_pattern_exact]
  exact close_value_pattern_exact

theorem infer_match_first_exact :
    M4.infer Paper1FrozenSignature.signature [] firstMatch = some .int := by
  unfold M4.infer
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    elaborate_match_first_exact]
  exact close_match_first_exact

theorem value_pattern_typing :
    M4.Typing Paper1FrozenSignature.signature [] valuePatternMatch
      (DataTypes.list .int) :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    infer_value_pattern_exact

theorem match_first_typing :
    M4.Typing Paper1FrozenSignature.signature [] firstMatch .int :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    infer_match_first_exact

def nonexhaustiveFirst : Expr :=
  .matchFirst (.lit 1) .something [.mk (.value (.lit 1)) (.lit 2)]

theorem nonexhaustive_match_first_rejected :
    M4.infer Paper1FrozenSignature.signature [] nonexhaustiveFirst = none := by
  with_unfolding_all rfl

def escapingSelf : Expr := .fixE (.var 1)

theorem escaping_self_rejected :
    M4.infer Paper1FrozenSignature.signature [] escapingSelf = none := by
  with_unfolding_all rfl

end TypePM.Source.M4RecursiveElaborationRegression
