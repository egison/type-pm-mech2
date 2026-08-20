import TypePM.Source.M4Paper1IntegratedPositiveRegression
import TypePM.Source.M4MatchingAtomRuntimeBridge

/-!
# Paper 1 safety regressions

These regressions connect the static M4 pattern evidence used by the listed
Paper 1 programs to the common-fuel runtime safety theorem.  A normal pattern
mismatch is an empty result list; it is not an evaluator error.
-/

namespace TypePM.Source.M4Paper1SafetyRegression

open TypePM.Runtime

/-! ## P1-L13: `something` with a variable pattern -/

def variablePatternGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := [.var ⟨0⟩]
    hard := []
    pending := [] }

def variablePatternSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

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
          variablePattern_elaborates .var variablePattern_semantic
          MonomorphicContextCompatible.nil matcherTyped .somethingVar
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

theorem somethingVariable_exact :
    evalFuel 3 [] Runtime.MatchAllRegression.somethingVariable =
      .ok (Value.buildList [.int 7]) :=
  Runtime.MatchAllRegression.something_variable_evaluates_body_under_binding

theorem somethingVariable_neverStuck (fuel : Nat) :
    (evalFuel fuel [] Runtime.MatchAllRegression.somethingVariable).NotStuck :=
  somethingVariable_totalCoreTyping.neverStuck fuel [] .nil

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
          integerValuePattern_elaborates integerValuePattern_supported
          integerValuePattern_semantic MonomorphicContextCompatible.nil
          matcherTyped .somethingValue targetTyped
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
    paperIntegerValueMismatch_initialAtom (.core (.lit 0))

theorem paperIntegerValueMismatch_staticAndRuntimeTyping :
    M4.Typing Paper1FrozenSignature.signature []
        Runtime.MatchAllRegression.paperIntegerValueMismatch
        (DataTypes.list .int) ∧
      TotalCoreTyping Runtime.MatchAllRegression.paperIntegerValueMismatch
        (DataTypes.list .int) [] :=
  ⟨M4Paper1IntegratedPositiveRegression.normal_mismatch_typing,
    paperIntegerValueMismatch_totalCoreTyping⟩

theorem paperIntegerValueMismatch_exact :
    evalFuel 3 [] Runtime.MatchAllRegression.paperIntegerValueMismatch =
      .ok Value.nilValue :=
  Runtime.MatchAllRegression.paper_integer_value_mismatch_is_empty_not_stuck

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
          wildcardPattern_elaborates .wild wildcardPattern_semantic
          MonomorphicContextCompatible.nil matcherTyped .somethingWild
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
