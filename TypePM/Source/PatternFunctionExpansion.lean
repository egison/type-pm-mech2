import TypePM.Source.PatternFunctionDefinition

/-!
# Source expansion of the inline pattern-function fragment

The expansion traverses the complete final source syntax, including matcher
clause expressions and value patterns.  A pattern-function application is
replaced only when its runtime definition is `InlineRuntimeSafe`; otherwise
the expansion fails explicitly.  Consequently the ordinary evaluator never
receives an unexpanded `Pattern.app` or a free `Pattern.embed` from this path.
-/

namespace TypePM.Source.PatternFunctionExpansion

open TypePM.Source

mutual

def expandExpr (definitions : PatternFunctionDefinitions) :
    Expr → Option Expr
  | .var index => some (.var index)
  | .lit value => some (.lit value)
  | .something => some .something
  | .lam body => return .lam (← expandExpr definitions body)
  | .app function argument =>
      return .app (← expandExpr definitions function)
        (← expandExpr definitions argument)
  | .tuple items => return .tuple (← expandExprList definitions items)
  | .letE value body =>
      return .letE (← expandExpr definitions value)
        (← expandExpr definitions body)
  | .ctor constructor arguments =>
      return .ctor constructor (← expandExprList definitions arguments)
  | .prim operation arguments =>
      return .prim operation (← expandExprList definitions arguments)
  | .ifE condition thenBranch elseBranch =>
      return .ifE (← expandExpr definitions condition)
        (← expandExpr definitions thenBranch)
        (← expandExpr definitions elseBranch)
  | .fixE body => return .fixE (← expandExpr definitions body)
  | .matcher clauses =>
      return .matcher (← expandClauses definitions clauses)
  | .matchAll target matcher pattern body =>
      return .matchAll (← expandExpr definitions target)
        (← expandExpr definitions matcher)
        (← expandPattern definitions pattern)
        (← expandExpr definitions body)
  | .matchFirst target matcher arms =>
      return .matchFirst (← expandExpr definitions target)
        (← expandExpr definitions matcher)
        (← expandMatchFirstArms definitions arms)
termination_by expression => expression.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def expandExprList (definitions : PatternFunctionDefinitions) :
    List Expr → Option (List Expr)
  | [] => some []
  | expression :: expressions =>
      return (← expandExpr definitions expression) ::
        (← expandExprList definitions expressions)
termination_by expressions => Expr.listComplexity expressions * 3
decreasing_by all_goals simp_wf <;> omega

def expandPattern (definitions : PatternFunctionDefinitions) :
    Pattern → Option Pattern
  | .var => some .var
  | .wild => some .wild
  | .value expression =>
      return .value (← expandExpr definitions expression)
  | .ctor constructor fields =>
      return .ctor constructor (← expandPatterns definitions fields)
  | .tuple items => return .tuple (← expandPatterns definitions items)
  | .and left right =>
      return .and (← expandPattern definitions left)
        (← expandPattern definitions right)
  | .or left right =>
      return .or (← expandPattern definitions left)
        (← expandPattern definitions right)
  | .embed _ => none
  | .app function arguments => do
      let expandedArguments ← expandPatterns definitions arguments
      let definition ← definitions.lookup function
      if _arity : expandedArguments.length = definition.parameterCount then
        if _safe : definition.InlineRuntimeSafe then
          definition.body.instantiateInlineTemplate expandedArguments
        else
          none
      else
        none
termination_by pattern => pattern.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def expandPatterns (definitions : PatternFunctionDefinitions) :
    List Pattern → Option (List Pattern)
  | [] => some []
  | pattern :: patterns =>
      return (← expandPattern definitions pattern) ::
        (← expandPatterns definitions patterns)
termination_by patterns => Pattern.listComplexity patterns * 3
decreasing_by all_goals simp_wf <;> omega

def expandClause (definitions : PatternFunctionDefinitions) :
    MatcherClause → Option MatcherClause
  | .mk header nextMatchers arms =>
      return .mk header (← expandExpr definitions nextMatchers)
        (← expandArms definitions arms)
termination_by clause => clause.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def expandClauses (definitions : PatternFunctionDefinitions) :
    List MatcherClause → Option (List MatcherClause)
  | [] => some []
  | clause :: clauses =>
      return (← expandClause definitions clause) ::
        (← expandClauses definitions clauses)
termination_by clauses => MatcherClause.listComplexity clauses * 3
decreasing_by all_goals simp_wf <;> omega

def expandArm (definitions : PatternFunctionDefinitions) :
    MatcherArm → Option MatcherArm
  | .mk header body =>
      return .mk header (← expandExpr definitions body)
termination_by arm => arm.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def expandArms (definitions : PatternFunctionDefinitions) :
    List MatcherArm → Option (List MatcherArm)
  | [] => some []
  | arm :: arms =>
      return (← expandArm definitions arm) ::
        (← expandArms definitions arms)
termination_by arms => MatcherArm.listComplexity arms * 3
decreasing_by all_goals simp_wf <;> omega

def expandMatchFirstArm (definitions : PatternFunctionDefinitions) :
    MatchFirstArm → Option MatchFirstArm
  | .mk pattern body =>
      return .mk (← expandPattern definitions pattern)
        (← expandExpr definitions body)
termination_by arm => arm.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def expandMatchFirstArms (definitions : PatternFunctionDefinitions) :
    List MatchFirstArm → Option (List MatchFirstArm)
  | [] => some []
  | arm :: arms =>
      return (← expandMatchFirstArm definitions arm) ::
        (← expandMatchFirstArms definitions arms)
termination_by arms => MatchFirstArm.listComplexity arms * 3
decreasing_by all_goals simp_wf <;> omega

end

end TypePM.Source.PatternFunctionExpansion
