import TypePM.Source.M4Paper1IntegratedPositiveRegression
import TypePM.Source.M4MatchingAtomRuntimeBridge
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility

/-!
# Paper 1 safety regressions

These regressions connect the static M4 pattern evidence used by the listed
Paper 1 programs to the common-fuel runtime safety theorem.  A normal pattern
mismatch is an empty result list; it is not an evaluator error.
-/

namespace TypePM.Source.M4Paper1SafetyRegression

open TypePM.Runtime

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

/-! ## Independent baseline: `something` with an integer target -/

def variablePatternGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := [.var ⟨0⟩]
    hard := []
    pending := [] }

def variablePatternSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

def somethingVariableGenerated : Generated :=
  { target := DataTypes.list (.var ⟨0⟩)
    hard := [.ty (.var ⟨0⟩) .int]
    pending :=
      [⟨.matcher .any (.var ⟨1⟩), .slot (.var ⟨0⟩) .int⟩] }

theorem somethingVariable_elaborate_exact :
    M4.elaborate Paper1FrozenSignature.signature []
      Runtime.MatchAllRegression.somethingVariable ⟨0, 0⟩ =
        some (somethingVariableGenerated, ⟨2, 1⟩) := by
  unfold M4.elaborate Runtime.MatchAllRegression.somethingVariable
  rfl'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem somethingVariable_close_exact :
    (inferGeneratedUsing unify somethingVariableGenerated).bind
        (fun closed => some closed.target) =
      some (DataTypes.list .int) := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [somethingVariableGenerated, DataTypes.list]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherProduct, Ty.mayBecomeExpectedSlot, Ty.apply, Cap.apply,
    Subst.compose]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨1⟩)) (.slot (.var ⟨0⟩) .int) =
        .matcherToSlot .any (.var ⟨0⟩) (.var ⟨1⟩) .int .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Cap.apply]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

theorem somethingVariable_infer_exact :
    M4.infer Paper1FrozenSignature.signature []
      Runtime.MatchAllRegression.somethingVariable =
        some (DataTypes.list .int) := by
  unfold M4.infer
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    somethingVariable_elaborate_exact]
  exact somethingVariable_close_exact

theorem somethingVariable_typing :
    M4.Typing Paper1FrozenSignature.signature []
      Runtime.MatchAllRegression.somethingVariable
        (DataTypes.list .int) :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    somethingVariable_infer_exact

theorem variablePattern_elaborates :
    PatternElaborates Paper1FrozenSignature.signature [] [] .var []
      ⟨0, 0⟩ variablePatternGenerated ⟨1, 1⟩ := by
  exact .var

theorem variablePattern_semantic :
    MatcherTyping.GeneratedPatternRuntimeSolution variablePatternGenerated
      variablePatternSolution := by
  simp [MatcherTyping.GeneratedPatternRuntimeSolution,
    variablePatternGenerated, Solves]

private theorem somethingVariable_initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (environmentTyped : EnvironmentTyping environment [])
    (targetSuccess : evalFuel fuel environment (.lit 7) = .ok targetValue)
    (matcherSuccess : evalFuel fuel environment .something = .ok matcherValue)
    (targetTyped : ValueTyping targetValue .int)
    (matcherTyped : ValueTyping matcherValue (.matcher .any .int)) :
    TotalMatchingAtomTyping [] [] ⟨.var, matcherValue, targetValue⟩ [.int] := by
  cases environmentTyped
  cases fuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ fuel =>
      simp [evalFuel] at targetSuccess matcherSuccess
      subst targetValue
      subst matcherValue
      obtain ⟨newBindings, atomTyped, bindingsEq⟩ :=
        MatcherTyping.PatternElaborates.toBuiltinTotalMatchingAtomTyping
          variablePattern_elaborates Paper1FrozenSignature.runtimeCompatible
          .var variablePattern_semantic
          MonomorphicContextCompatible.nil
          (.checked matcherTyped (.matcherToSlot .equal)) .somethingVar
          targetTyped
      have newBindingsEq : newBindings = [.int] := by
        simpa [variablePatternGenerated, variablePatternSolution,
          Ty.applyList, Ty.apply] using bindingsEq.symm
      subst newBindings
      exact atomTyped

theorem somethingVariable_totalCoreTyping :
    TotalCoreTyping Runtime.MatchAllRegression.somethingVariable
      (DataTypes.list .int) [] := by
  unfold Runtime.MatchAllRegression.somethingVariable
  exact .matchAll (.core (.lit 7)) (.core (.something .int))
    somethingVariable_initialAtom (.core (.var rfl))

theorem somethingVariable_staticAndRuntimeTyping :
    M4.Typing Paper1FrozenSignature.signature []
        Runtime.MatchAllRegression.somethingVariable
        (DataTypes.list .int) ∧
      TotalCoreTyping Runtime.MatchAllRegression.somethingVariable
        (DataTypes.list .int) [] :=
  ⟨somethingVariable_typing, somethingVariable_totalCoreTyping⟩

theorem somethingVariable_eval_exact :
    evalFuel 3 [] Runtime.MatchAllRegression.somethingVariable =
      .ok (Value.buildList [.int 7]) :=
  Runtime.MatchAllRegression.something_variable_evaluates_body_under_binding

theorem somethingVariable_eval_relational :
    Eval [] Runtime.MatchAllRegression.somethingVariable
      (Value.buildList [.int 7]) :=
  evalFuel_sound somethingVariable_eval_exact

theorem somethingVariable_neverStuck (fuel : Nat) :
    (evalFuel fuel [] Runtime.MatchAllRegression.somethingVariable).NotStuck :=
  somethingVariable_totalCoreTyping.neverStuck fuel [] .nil

/-! ## P1-L13: the exact listed `something` variable expression -/

/-- The exact positive expression printed in Paper 1, P1-L13:
`matchAll [1, 2, 3] as something with $x -> x`. -/
def paperSomethingVariable : Expr :=
  .matchAll (Paper1Programs.sourceList [.lit 1, .lit 2, .lit 3])
    .something .var (.var 0)

private def paperSomethingVariableTargetGenerated : Generated :=
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

private def paperSomethingVariablePatternGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨16⟩⟩
    bindings := [.var ⟨16⟩]
    hard := []
    pending := [] }

private def paperSomethingVariableMatcherGenerated : Generated :=
  { target := .matcher .any (.var ⟨17⟩)
    hard := []
    pending := [] }

private def paperSomethingVariableBodyGenerated : Generated :=
  { target := .var ⟨16⟩
    hard := []
    pending := [] }

def paperSomethingVariableGenerated : Generated :=
  Generated.fromMatchAll paperSomethingVariableTargetGenerated
    paperSomethingVariablePatternGenerated
    paperSomethingVariableMatcherGenerated
    paperSomethingVariableBodyGenerated

theorem paperSomethingVariable_elaborate_exact :
    M4.elaborate Paper1FrozenSignature.signature [] paperSomethingVariable
      ⟨0, 0⟩ = some (paperSomethingVariableGenerated, ⟨18, 1⟩) := by
  unfold M4.elaborate paperSomethingVariable
    paperSomethingVariableGenerated paperSomethingVariableTargetGenerated
    paperSomethingVariablePatternGenerated
    paperSomethingVariableMatcherGenerated
    paperSomethingVariableBodyGenerated Paper1Programs.sourceList
  rfl'

private theorem paperSomethingVariable_close_fuel_exact :
    (inferGeneratedUsing (unifyWithFuel 2000)
      paperSomethingVariableGenerated).bind
        (fun closed => some closed.target) =
      some (DataTypes.list (DataTypes.list .int)) := by
  simp only [paperSomethingVariableGenerated,
    paperSomethingVariableTargetGenerated,
    paperSomethingVariablePatternGenerated,
    paperSomethingVariableMatcherGenerated,
    paperSomethingVariableBodyGenerated, Generated.fromMatchAll,
    DataTypes.list]
  rfl'

theorem paperSomethingVariable_close_exact :
    (inferGeneratedUsing unify paperSomethingVariableGenerated).bind
        (fun closed => some closed.target) =
      some (DataTypes.list (DataTypes.list .int)) := by
  cases closureEquality : inferGeneratedUsing (unifyWithFuel 2000)
      paperSomethingVariableGenerated with
  | none =>
      have impossible := paperSomethingVariable_close_fuel_exact
      simp [closureEquality] at impossible
  | some closed =>
      have publicClosure :=
        inferGeneratedUsing_unify_of_fuel_success closureEquality
      rw [publicClosure]
      simpa [closureEquality] using paperSomethingVariable_close_fuel_exact

theorem paperSomethingVariable_infer_exact :
    M4.infer Paper1FrozenSignature.signature [] paperSomethingVariable =
      some (DataTypes.list (DataTypes.list .int)) := by
  unfold M4.infer
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    paperSomethingVariable_elaborate_exact]
  exact paperSomethingVariable_close_exact

theorem paperSomethingVariable_typing :
    M4.Typing Paper1FrozenSignature.signature [] paperSomethingVariable
      (DataTypes.list (DataTypes.list .int)) :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed
    paperSomethingVariable_infer_exact

def paperSomethingVariablePatternSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => DataTypes.list .int }

theorem paperSomethingVariable_pattern_elaborates :
    PatternElaborates Paper1FrozenSignature.signature [] [] .var []
      ⟨16, 0⟩ paperSomethingVariablePatternGenerated ⟨17, 1⟩ := by
  exact .var

theorem paperSomethingVariable_pattern_semantic :
    MatcherTyping.GeneratedPatternRuntimeSolution
      paperSomethingVariablePatternGenerated
      paperSomethingVariablePatternSolution := by
  simp [MatcherTyping.GeneratedPatternRuntimeSolution,
    paperSomethingVariablePatternGenerated,
    paperSomethingVariablePatternSolution, Solves]

private theorem paperSomethingVariable_initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (environmentTyped : EnvironmentTyping environment [])
    (targetSuccess : evalFuel fuel environment
      (Paper1Programs.sourceList [.lit 1, .lit 2, .lit 3]) =
        .ok targetValue)
    (matcherSuccess : evalFuel fuel environment .something = .ok matcherValue)
    (targetTyped : ValueTyping targetValue (DataTypes.list .int))
    (matcherTyped : ValueTyping matcherValue
      (.matcher .any (DataTypes.list .int))) :
    TotalMatchingAtomTyping [] [] ⟨.var, matcherValue, targetValue⟩
      [DataTypes.list .int] := by
  cases environmentTyped
  cases fuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ fuel =>
      simp [evalFuel] at matcherSuccess
      subst matcherValue
      obtain ⟨newBindings, atomTyped, bindingsEq⟩ :=
        MatcherTyping.PatternElaborates.toBuiltinTotalMatchingAtomTyping
          paperSomethingVariable_pattern_elaborates
          Paper1FrozenSignature.runtimeCompatible .var
          paperSomethingVariable_pattern_semantic
          MonomorphicContextCompatible.nil
          (.checked matcherTyped (.matcherToSlot .equal)) .somethingVar
          targetTyped
      have newBindingsEq : newBindings = [DataTypes.list .int] := by
        simpa [paperSomethingVariablePatternGenerated,
          paperSomethingVariablePatternSolution, Ty.applyList, Ty.apply]
          using bindingsEq.symm
      subst newBindings
      exact atomTyped

theorem paperSomethingVariable_totalCoreTyping :
    TotalCoreTyping paperSomethingVariable
      (DataTypes.list (DataTypes.list .int)) [] := by
  unfold paperSomethingVariable Paper1Programs.sourceList
  exact .matchAll
    (.core (.listCons (.lit 1)
      (.listCons (.lit 2) (.listCons (.lit 3) (.listNil .int)))))
    (.core (.something (DataTypes.list .int)))
    paperSomethingVariable_initialAtom (.core (.var rfl))

theorem paperSomethingVariable_staticAndRuntimeTyping :
    M4.Typing Paper1FrozenSignature.signature [] paperSomethingVariable
        (DataTypes.list (DataTypes.list .int)) ∧
      TotalCoreTyping paperSomethingVariable
        (DataTypes.list (DataTypes.list .int)) [] :=
  ⟨paperSomethingVariable_typing, paperSomethingVariable_totalCoreTyping⟩

theorem paperSomethingVariable_eval_exact :
    evalFuel 5 [] paperSomethingVariable =
      .ok (Value.buildList [Value.buildList [.int 1, .int 2, .int 3]]) := by
  with_unfolding_all rfl

theorem paperSomethingVariable_eval_relational :
    Eval [] paperSomethingVariable
      (Value.buildList [Value.buildList [.int 1, .int 2, .int 3]]) :=
  evalFuel_sound paperSomethingVariable_eval_exact

theorem paperSomethingVariable_neverStuck (fuel : Nat) :
    (evalFuel fuel [] paperSomethingVariable).NotStuck :=
  paperSomethingVariable_totalCoreTyping.neverStuck fuel [] .nil

/-! ## P1-L14: normal value-pattern mismatch -/

def integerValuePattern : Pattern := .value (.lit 1)

def integerValuePatternGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .int⟩
    bindings := []
    hard := []
    pending := [] }

def integerValuePatternSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

theorem integerValuePattern_elaborates :
    PatternElaborates Paper1FrozenSignature.signature [] []
      integerValuePattern [] ⟨0, 0⟩ integerValuePatternGenerated ⟨0, 1⟩ := by
  unfold integerValuePattern integerValuePatternGenerated
  exact .value .lit

theorem integerValuePattern_supported :
    MatcherTyping.DirectRuntimePatternSupported integerValuePattern :=
  .value .lit

theorem integerValuePattern_semantic :
    MatcherTyping.GeneratedPatternRuntimeSolution integerValuePatternGenerated
      integerValuePatternSolution := by
  simp [MatcherTyping.GeneratedPatternRuntimeSolution,
    integerValuePatternGenerated, Solves]

private theorem paperIntegerValueMismatch_initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (environmentTyped : EnvironmentTyping environment [])
    (targetSuccess : evalFuel fuel environment (.lit 5) = .ok targetValue)
    (matcherSuccess : evalFuel fuel environment .something = .ok matcherValue)
    (targetTyped : ValueTyping targetValue .int)
    (matcherTyped : ValueTyping matcherValue (.matcher .any .int)) :
    TotalMatchingAtomTyping [] []
      ⟨integerValuePattern, matcherValue, targetValue⟩ [] := by
  cases environmentTyped
  cases fuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ fuel =>
      simp [evalFuel] at targetSuccess matcherSuccess
      subst targetValue
      subst matcherValue
      obtain ⟨newBindings, atomTyped, bindingsEq⟩ :=
        MatcherTyping.PatternElaborates.toBuiltinTotalMatchingAtomTyping
          integerValuePattern_elaborates Paper1FrozenSignature.runtimeCompatible
          integerValuePattern_supported
          integerValuePattern_semantic MonomorphicContextCompatible.nil
          (.checked matcherTyped (.matcherToSlot .equal)) .somethingValue
          targetTyped
      have newBindingsEq : newBindings = [] := by
        simpa [integerValuePatternGenerated, integerValuePatternSolution,
          Ty.applyList] using bindingsEq.symm
      subst newBindings
      exact atomTyped

/-- P1-L14's accepted M4 expression has a complete runtime safety
certificate.  Its value pattern contributes no bindings. -/
theorem paperIntegerValueMismatch_totalCoreTyping :
    TotalCoreTyping Runtime.MatchAllRegression.paperIntegerValueMismatch
      (DataTypes.list .int) [] := by
  unfold Runtime.MatchAllRegression.paperIntegerValueMismatch
  exact .matchAll (.core (.lit 5)) (.core (.something .int))
    paperIntegerValueMismatch_initialAtom (.core (.lit 1))

theorem paperIntegerValueMismatch_staticAndRuntimeTyping :
    M4.Typing Paper1FrozenSignature.signature []
        Runtime.MatchAllRegression.paperIntegerValueMismatch
        (DataTypes.list .int) ∧
      TotalCoreTyping Runtime.MatchAllRegression.paperIntegerValueMismatch
        (DataTypes.list .int) [] :=
  ⟨M4Paper1IntegratedPositiveRegression.normal_mismatch_typing,
    paperIntegerValueMismatch_totalCoreTyping⟩

theorem paperIntegerValueMismatch_eval_exact :
    evalFuel 3 [] Runtime.MatchAllRegression.paperIntegerValueMismatch =
      .ok Value.nilValue :=
  Runtime.MatchAllRegression.paper_integer_value_mismatch_is_empty_not_stuck

theorem paperIntegerValueMismatch_eval_relational :
    Eval [] Runtime.MatchAllRegression.paperIntegerValueMismatch
      Value.nilValue :=
  evalFuel_sound paperIntegerValueMismatch_eval_exact

theorem paperIntegerValueMismatch_neverStuck (fuel : Nat) :
    (evalFuel fuel []
      Runtime.MatchAllRegression.paperIntegerValueMismatch).NotStuck :=
  paperIntegerValueMismatch_totalCoreTyping.neverStuck fuel [] .nil

/-! ## Accepted explicit-else `matchFirst` -/

def wildcardPatternGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := []
    hard := []
    pending := [] }

def wildcardPatternSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

theorem wildcardPattern_elaborates :
    PatternElaborates Paper1FrozenSignature.signature [] [] .wild []
      ⟨0, 0⟩ wildcardPatternGenerated ⟨1, 1⟩ := by
  exact .wild

theorem wildcardPattern_semantic :
    MatcherTyping.GeneratedPatternRuntimeSolution wildcardPatternGenerated
      wildcardPatternSolution := by
  simp [MatcherTyping.GeneratedPatternRuntimeSolution,
    wildcardPatternGenerated, Solves]

private theorem firstMatch_initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (environmentTyped : EnvironmentTyping environment [])
    (targetSuccess : evalFuel fuel environment (.lit 1) = .ok targetValue)
    (matcherSuccess : evalFuel fuel environment .something = .ok matcherValue)
    (targetTyped : ValueTyping targetValue .int)
    (matcherTyped : ValueTyping matcherValue (.matcher .any .int)) :
    TotalMatchingAtomTyping [] [] ⟨.wild, matcherValue, targetValue⟩ [] := by
  cases environmentTyped
  cases fuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ fuel =>
      simp [evalFuel] at targetSuccess matcherSuccess
      subst targetValue
      subst matcherValue
      obtain ⟨newBindings, atomTyped, bindingsEq⟩ :=
        MatcherTyping.PatternElaborates.toBuiltinTotalMatchingAtomTyping
          wildcardPattern_elaborates Paper1FrozenSignature.runtimeCompatible
          .wild wildcardPattern_semantic
          MonomorphicContextCompatible.nil
          (.checked matcherTyped (.matcherToSlot .equal)) .somethingWild
          targetTyped
      have newBindingsEq : newBindings = [] := by
        simpa [wildcardPatternGenerated, wildcardPatternSolution,
          Ty.applyList] using bindingsEq.symm
      subst newBindings
      exact atomTyped

/-- The public M4-accepted one-arm example has the total runtime certificate
required by the explicit-else semantics. -/
theorem firstMatch_totalCoreTyping :
    TotalCoreTyping M4RecursiveElaborationRegression.firstMatch .int [] := by
  unfold M4RecursiveElaborationRegression.firstMatch
  exact .matchFirst (.core (.lit 1)) (.core (.something .int))
    (.cons firstMatch_initialAtom (.core (.lit 2)) .nil) (.core (.lit 3))

theorem firstMatch_staticAndRuntimeTyping :
    M4.Typing Paper1FrozenSignature.signature []
        M4RecursiveElaborationRegression.firstMatch .int ∧
      TotalCoreTyping M4RecursiveElaborationRegression.firstMatch .int [] :=
  ⟨M4RecursiveElaborationRegression.match_first_typing,
    firstMatch_totalCoreTyping⟩

theorem firstMatch_exact :
    evalFuel 3 [] M4RecursiveElaborationRegression.firstMatch = .ok (.int 2) := by
  with_unfolding_all rfl

theorem firstMatch_neverStuck (fuel : Nat) :
    (evalFuel fuel [] M4RecursiveElaborationRegression.firstMatch).NotStuck :=
  firstMatch_totalCoreTyping.neverStuck fuel [] .nil

end TypePM.Source.M4Paper1SafetyRegression
