import TypePM.Source.PatternFunctionDefinition

/-!
# Pattern-function declaration boundary regressions

The nullary `unit` template and unary parameter-passing template exercise both
ends of the frozen-source/runtime agreement.  The negative examples show that
the inline runtime fragment does not silently accept private binders, value
expressions, duplicated parameters, or reordered parameters.
-/

namespace TypePM.Source.M4PatternFunctionDefinitionRegression

def unitName : PatternFunName := ⟨"unit"⟩
def passName : PatternFunName := ⟨"pass"⟩

def unitScheme : DualScheme :=
  { tyArity := 0
    capArity := 0
    fields := []
    result := { capability := .prod [], target := .prod [] }
    fieldsWellScoped := by simp
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped] }

def passScheme : DualScheme :=
  { tyArity := 1
    capArity := 1
    fields := [{ capability := .bound 0, target := .bound 0 }]
    result := { capability := .bound 0, target := .bound 0 }
    fieldsWellScoped := by
      intro field member
      simp only [List.mem_singleton] at member
      subst field
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped]
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped] }

def signature : FrozenSignature :=
  { base := Paper1Signature.signature
    patternFunctions :=
      [⟨unitName, unitScheme⟩, ⟨passName, passScheme⟩] }

def unitDefinition : PatternFunctionDefinition :=
  { name := unitName
    parameterCount := 0
    body := .tuple [] }

def passDefinition : PatternFunctionDefinition :=
  { name := passName
    parameterCount := 1
    body := .embed 0 }

theorem unit_inline_safe : unitDefinition.InlineRuntimeSafe := by
  rfl

theorem pass_inline_safe : passDefinition.InlineRuntimeSafe := by
  rfl

def unitChecked : unitDefinition.InlineChecked signature where
  scheme := unitScheme
  lookup := by rfl
  arity := by rfl
  generated :=
    { dual := ⟨.prod [], .prod []⟩
      bindings := []
      hard := []
      pending := [] }
  next := ⟨0, 0⟩
  bodyElaboration := .tuple .nil
  result_eq := by rfl
  bindings_eq := by rfl
  inlineRuntimeSafe := unit_inline_safe

def passChecked : passDefinition.InlineChecked signature where
  scheme := passScheme
  lookup := by rfl
  arity := by rfl
  generated :=
    { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
      bindings := []
      hard := []
      pending := [] }
  next := ⟨1, 1⟩
  bodyElaboration := .embed (by rfl)
  result_eq := by rfl
  bindings_eq := by rfl
  inlineRuntimeSafe := pass_inline_safe

def definitions : PatternFunctionDefinitions :=
  [unitDefinition, passDefinition]

theorem signature_wellFormed : signature.WellFormed := by
  refine
    { baseWellFormed := Paper1Signature.wellFormed
      patternFunctionNodup := ?_
      patternFunctionClosed := ?_
      patternFunctionWellFormed := ?_ }
  · decide
  · intro declaration member
    simp [signature] at member
    rcases member with rfl | rfl <;>
      simp [DualScheme.Closed, DualScheme.freeTyVars,
        DualScheme.freeCapVars, unitScheme, passScheme,
        PolyTy.freeTyVars, PolyTy.freeTyVarsList,
        PolyTy.freeCapVars, PolyTy.freeCapVarsList,
        PolyCap.freeCapVars, PolyCap.freeCapVarsList,
        dedupFirst, dedup]
  · intro declaration member
    simp [signature] at member
    rcases member with rfl | rfl
    · exact unitScheme.wellFormed
    · exact passScheme.wellFormed

theorem definitions_agree :
    PatternFunctionDefinitions.AgreeInline signature definitions := by
  refine
    { signatureWellFormed := signature_wellFormed
      namesNodup := ?_
      runtimeChecked := ?_
      sourceImplemented := ?_ }
  · decide
  · intro definition member
    simp [definitions] at member
    rcases member with rfl | rfl
    · exact ⟨unitChecked⟩
    · exact ⟨passChecked⟩
  · intro declaration member
    simp [signature] at member
    rcases member with rfl | rfl
    · exact ⟨unitDefinition, by simp [definitions], rfl⟩
    · exact ⟨passDefinition, by simp [definitions], rfl⟩

theorem instantiate_unit_exact :
    unitDefinition.body.instantiateInlineTemplate [] =
      some (.tuple []) := by
  rfl

theorem instantiate_pass_exact (argument : Pattern) :
    passDefinition.body.instantiateInlineTemplate [argument] =
      some argument := by
  rfl

def conjunctionTemplate : PatternFunctionDefinition :=
  { name := ⟨"and"⟩
    parameterCount := 2
    body := .and (.embed 0) (.embed 1) }

theorem conjunction_template_inline_safe :
    conjunctionTemplate.InlineRuntimeSafe := by
  rfl

theorem instantiate_conjunction_exact (left right : Pattern) :
    conjunctionTemplate.body.instantiateInlineTemplate [left, right] =
      some (.and left right) := by
  rfl

theorem private_binder_not_inline_safe :
    ¬ ({ name := unitName, parameterCount := 0,
          body := Pattern.var } : PatternFunctionDefinition).InlineRuntimeSafe := by
  decide

theorem value_expression_not_inline_safe :
    ¬ ({ name := unitName, parameterCount := 0,
          body := Pattern.value (.lit 0) } :
        PatternFunctionDefinition).InlineRuntimeSafe := by
  decide

theorem duplicated_parameter_not_inline_safe :
    ¬ ({ name := passName, parameterCount := 1,
          body := Pattern.tuple [.embed 0, .embed 0] } :
        PatternFunctionDefinition).InlineRuntimeSafe := by
  decide

theorem reordered_parameters_not_inline_safe :
    ¬ ({ name := passName, parameterCount := 2,
          body := Pattern.tuple [.embed 1, .embed 0] } :
        PatternFunctionDefinition).InlineRuntimeSafe := by
  decide

end TypePM.Source.M4PatternFunctionDefinitionRegression
