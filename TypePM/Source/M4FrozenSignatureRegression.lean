import TypePM.Source.FrozenSignature

/-!
# M4 frozen-signature regressions

These examples exercise the pattern-function interface boundary without
introducing source-level pattern-function bodies or a freeze checker.
-/

namespace TypePM.Source.M4FrozenSignatureRegression

def emptyListPattern : PatternFunName := ⟨"emptyList"⟩

def emptyListDeclaration : PatternFunctionDeclaration :=
  ⟨emptyListPattern, ListPatternSchemes.nil⟩

def onePatternFunction : FrozenSignature :=
  { base := Paper1Signature.signature
    patternFunctions := [emptyListDeclaration] }

theorem one_pattern_function_wellFormed : onePatternFunction.WellFormed := by
  exact
    { baseWellFormed := Paper1Signature.wellFormed
      patternFunctionNodup := by
        simp [onePatternFunction, emptyListDeclaration]
      patternFunctionClosed := by
        intro declaration member
        simp only [onePatternFunction, List.mem_cons, List.not_mem_nil,
          or_false] at member
        subst declaration
        constructor <;> rfl
      patternFunctionWellFormed := by
        intro declaration member
        simp only [onePatternFunction, List.mem_cons, List.not_mem_nil,
          or_false] at member
        subst declaration
        exact ListPatternSchemes.nil.wellFormed }

theorem lookup_emptyList_exact :
    onePatternFunction.lookupPatternFunction emptyListPattern =
      some ListPatternSchemes.nil := by
  rfl

theorem looked_up_emptyList_closed : ListPatternSchemes.nil.Closed :=
  FrozenSignature.lookupPatternFunction_closed
    one_pattern_function_wellFormed lookup_emptyList_exact

theorem looked_up_emptyList_wellFormed :
    ListPatternSchemes.nil.WellFormed :=
  FrozenSignature.lookupPatternFunction_wellFormed
    one_pattern_function_wellFormed lookup_emptyList_exact

def duplicatePatternFunction : FrozenSignature :=
  { base := Paper1Signature.signature
    patternFunctions := [emptyListDeclaration, emptyListDeclaration] }

theorem duplicate_pattern_function_not_wellFormed :
    ¬ duplicatePatternFunction.WellFormed := by
  intro wellFormed
  simpa [duplicatePatternFunction, emptyListDeclaration] using
    wellFormed.patternFunctionNodup

end TypePM.Source.M4FrozenSignatureRegression
