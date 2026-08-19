import TypePM.Source.PatternFunctionExpansion
import TypePM.Source.M4PatternFunctionDefinitionRegression

/-!
# Inline pattern-function expansion regressions

These examples run the expansion through ordinary match sites, value-pattern
expressions, matcher-clause bodies, and the derived single-result match.  They
also pin every explicit failure boundary of the restricted runtime path.
-/

namespace TypePM.Source.M4PatternFunctionExpansionRegression

open PatternFunctionExpansion
open M4PatternFunctionDefinitionRegression

local macro "compute_expansion" : tactic =>
  `(tactic|
    simp [expandExpr, expandExprList, expandPattern, expandPatterns,
      expandClause, expandClauses, expandArm, expandArms,
      expandMatchFirstArm, expandMatchFirstArms,
      PatternFunctionDefinitions.lookup,
      PatternFunctionDefinition.InlineRuntimeSafe,
      Pattern.inlineTemplateEmbeds, Pattern.inlineTemplateEmbedsList,
      Pattern.instantiateInlineTemplate, Pattern.instantiateInlineTemplates,
      definitions, unitDefinition, passDefinition, unitName, passName])

def passArgument : Pattern :=
  .ctor PatternCtor.cons [.var, .wild]

theorem unit_expands_exact :
    expandPattern definitions (.app unitName []) = some (.tuple []) := by
  compute_expansion

theorem pass_expands_exact :
    expandPattern definitions (.app passName [passArgument]) =
      some passArgument := by
  simp [passArgument]
  compute_expansion

def nestedMatch : Expr :=
  .matchAll (.lit 1) .something (.app passName [.value (.lit 1)])
    (.tuple [])

def expandedNestedMatch : Expr :=
  .matchAll (.lit 1) .something (.value (.lit 1)) (.tuple [])

theorem complete_match_site_expands_exact :
    expandExpr definitions nestedMatch = some expandedNestedMatch := by
  simp [nestedMatch, expandedNestedMatch]
  compute_expansion

def nestedClause : MatcherClause :=
  .mk .hole .something
    [.mk .wild
      (.matchFirst (.lit 0) .something
        [.mk (.app unitName []) (.tuple [])])]

def expandedNestedClause : MatcherClause :=
  .mk .hole .something
    [.mk .wild
      (.matchFirst (.lit 0) .something
        [.mk (.tuple []) (.tuple [])])]

theorem matcher_and_matchFirst_expand_exact :
    expandExpr definitions (.matcher [nestedClause]) =
      some (.matcher [expandedNestedClause]) := by
  simp [nestedClause, expandedNestedClause]
  compute_expansion

theorem unknown_function_rejected :
    expandPattern definitions (.app ⟨"missing"⟩ []) = none := by
  compute_expansion

theorem wrong_arity_rejected :
    expandPattern definitions (.app passName []) = none := by
  compute_expansion

theorem free_embed_rejected :
    expandPattern definitions (.embed 0) = none := by
  compute_expansion

def privateDefinition : PatternFunctionDefinition :=
  { name := ⟨"private"⟩
    parameterCount := 0
    body := .var }

theorem private_binding_definition_rejected :
    expandPattern [privateDefinition] (.app privateDefinition.name []) = none := by
  simp [privateDefinition]
  compute_expansion

def duplicatedDefinition : PatternFunctionDefinition :=
  { name := ⟨"duplicate"⟩
    parameterCount := 1
    body := .tuple [.embed 0, .embed 0] }

theorem duplicated_parameter_definition_rejected :
    expandPattern [duplicatedDefinition]
      (.app duplicatedDefinition.name [.wild]) = none := by
  simp [duplicatedDefinition]
  compute_expansion

end TypePM.Source.M4PatternFunctionExpansionRegression
