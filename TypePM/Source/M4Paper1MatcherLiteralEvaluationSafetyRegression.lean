import TypePM.Source.M4Paper1RecursiveClosureTotalTyping

/-!
# Paper 1 matcher-literal evaluation boundary regression

These regressions deliberately test only construction of a matcher closure.
At this step neither clause selection nor an arm body runs; in particular the
`letE`/`matchAll` body of the join clause is stored, not evaluated.
-/

namespace TypePM.Source.MatcherTyping.M4Paper1MatcherLiteralEvaluationSafetyRegression

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open M4Paper1RecursiveClosureTotalTyping

/-- The public list principal derivation supplies unconditional total safety
for evaluating its matcher body literal. -/
theorem listBody_literalEvaluationSafe :
    ∃ domain codomain,
      M4Paper1ListExactRegression.listMatcherType = .fn domain codomain ∧
      TotalEnvironmentSafe (.matcher listMatcherClauses) codomain
        [domain, .fn domain codomain] :=
  listMatcherBody_literalEvaluation_totalEnvironmentSafe

/-- The closed multiset principal derivation supplies the corresponding
literal-evaluation safety under its captured list-constructor type. -/
theorem multisetBody_literalEvaluationSafe :
    ∃ capturedListType domain codomain,
      TotalEnvironmentSafe (.matcher multisetClauses) codomain
        [domain, .fn domain codomain, capturedListType] :=
  multisetMatcherBody_literalEvaluation_totalEnvironmentSafe

/-- One unit of fuel constructs the list matcher closure exactly.  No arm,
including the join arm, has been selected or evaluated. -/
theorem listLiteral_constructsClosure_withoutDispatch
    (environment : ValueEnvironment) :
    evalFuel 1 environment (.matcher listMatcherClauses) =
      .ok (.matcherV environment listMatcherClauses listMatcherClauses) := by
  rfl

/-- The same operational boundary holds for the multiset literal. -/
theorem multisetLiteral_constructsClosure_withoutDispatch
    (environment : ValueEnvironment) :
    evalFuel 1 environment (.matcher multisetClauses) =
      .ok (.matcherV environment multisetClauses multisetClauses) := by
  rfl

end TypePM.Source.MatcherTyping.M4Paper1MatcherLiteralEvaluationSafetyRegression
