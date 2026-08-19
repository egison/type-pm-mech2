import TypePM.Runtime.PatternFunctionEvaluation
import TypePM.Source.M4PatternFunctionExpansionRegression

/-!
# Executable inline pattern-function regressions

The two programs exercise a nullary pattern function and a parameter-passing
pattern function through the ordinary matching engine.  Unknown, wrong-arity,
and private-binding definitions remain explicit `stuck` boundaries rather
than falling through to an unrelated matching rule.
-/

namespace TypePM.Runtime.PatternFunctionEvaluationRegression

open TypePM.Source
open TypePM.Source.M4PatternFunctionDefinitionRegression

local macro "compute_expansion" : tactic =>
  `(tactic|
    simp [TypePM.Source.PatternFunctionExpansion.expandExpr,
      TypePM.Source.PatternFunctionExpansion.expandExprList,
      TypePM.Source.PatternFunctionExpansion.expandPattern,
      TypePM.Source.PatternFunctionExpansion.expandPatterns,
      TypePM.Source.PatternFunctionExpansion.expandClause,
      TypePM.Source.PatternFunctionExpansion.expandClauses,
      TypePM.Source.PatternFunctionExpansion.expandArm,
      TypePM.Source.PatternFunctionExpansion.expandArms,
      TypePM.Source.PatternFunctionExpansion.expandMatchFirstArm,
      TypePM.Source.PatternFunctionExpansion.expandMatchFirstArms,
      PatternFunctionDefinitions.lookup,
      PatternFunctionDefinition.InlineRuntimeSafe,
      Pattern.inlineTemplateEmbeds, Pattern.inlineTemplateEmbedsList,
      Pattern.instantiateInlineTemplate, Pattern.instantiateInlineTemplates,
      definitions, unitDefinition, passDefinition, unitName, passName])

def unitProgram : Source.Expr :=
  .matchAll (.tuple []) (.tuple []) (.app unitName []) (.lit 7)

def passProgram : Source.Expr :=
  .matchAll (.lit 5) .something (.app passName [.var]) (.var 0)

def expandedUnitProgram : Source.Expr :=
  .matchAll (.tuple []) (.tuple []) (.tuple []) (.lit 7)

def expandedPassProgram : Source.Expr :=
  .matchAll (.lit 5) .something .var (.var 0)

theorem unitProgram_expands :
    PatternFunctionExpansion.expandExpr definitions unitProgram =
      some expandedUnitProgram := by
  simp [unitProgram, expandedUnitProgram]
  compute_expansion

theorem passProgram_expands :
    PatternFunctionExpansion.expandExpr definitions passProgram =
      some expandedPassProgram := by
  simp [passProgram, expandedPassProgram]
  compute_expansion

theorem unit_executes_exact :
    evalPatternFunctionsFuel definitions 12 [] unitProgram =
      .ok (Value.buildList [.int 7]) := by
  simp [evalPatternFunctionsFuel, unitProgram_expands]
  rfl

theorem pass_executes_exact :
    evalPatternFunctionsFuel definitions 12 [] passProgram =
      .ok (Value.buildList [.int 5]) := by
  simp [evalPatternFunctionsFuel, passProgram_expands]
  rfl

theorem unit_has_independent_derivation :
    EvalPatternFunctions definitions [] unitProgram
      (Value.buildList [.int 7]) :=
  evalPatternFunctionsFuel_sound unit_executes_exact

theorem pass_has_independent_derivation :
    EvalPatternFunctions definitions [] passProgram
      (Value.buildList [.int 5]) :=
  evalPatternFunctionsFuel_sound pass_executes_exact

theorem pass_success_is_fuel_monotone (fuel : Nat) (bound : 12 ≤ fuel) :
    evalPatternFunctionsFuel definitions fuel [] passProgram =
      .ok (Value.buildList [.int 5]) :=
  evalPatternFunctionsFuel_ok_of_le bound pass_executes_exact

def unknownProgram : Source.Expr :=
  .matchAll (.lit 5) .something (.app ⟨"missing"⟩ []) (.lit 0)

theorem unknown_definition_is_stuck :
    evalPatternFunctionsFuel definitions 12 [] unknownProgram = .stuck := by
  simp [evalPatternFunctionsFuel, unknownProgram]
  compute_expansion

def privateProgram : Source.Expr :=
  .matchAll (.lit 5) .something
    (.app M4PatternFunctionExpansionRegression.privateDefinition.name [])
    (.lit 0)

theorem private_binding_definition_is_stuck :
    evalPatternFunctionsFuel
      [M4PatternFunctionExpansionRegression.privateDefinition]
      12 [] privateProgram = .stuck := by
  simp [evalPatternFunctionsFuel, privateProgram,
    M4PatternFunctionExpansionRegression.privateDefinition]
  compute_expansion

end TypePM.Runtime.PatternFunctionEvaluationRegression
