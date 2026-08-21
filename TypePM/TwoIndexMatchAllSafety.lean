import TypePM.TwoIndexMatchingSearchSafety
import TypePM.ValueIndexedMatchAllSafety

/-!
# Two-index composition rule for bounded DFS `matchAll`

The executable `evalFuel` rule uses its predecessor fuel both as the
evaluation callback fuel and as the bounded matching-search fuel.  This
module keeps that operational equality explicit by using one
`operationalFuel` parameter, while keeping the logical index retained on
matching answers and the logical index requested for body results separate.

The caller still supplies the initial-state certificate, including every
local atom-reducer obligation reachable within the bounded search.  The
theorem below only composes that certificate with the existing two-index DFS
theorem and the value-and-binding-indexed `matchAll` theorem.  It is therefore
not yet the complete fuel-indexed replacement for `commonFuelSafety`, nor a
fairness theorem for the separate lazy-prefix `matchAll` lane.
-/

namespace TypePM.Runtime

/-- A producer for the initial two-index state determined by the exact
successful target and matcher evaluations of one `matchAll` expression.

The certificate contains neither a complete-search equation nor the final
evaluation result.  Its environment and binding relations are selected by
the caller; in particular both may be `FuelEnvironmentSafe` without passing
through structural runtime typing. -/
def EvaluatedTwoIndexInitialStateTyping
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (operationalFuel bindingIndex : Nat)
    (environment : ValueEnvironment)
    (targetExpression matcherExpression : Source.Expr)
    (pattern : Source.Pattern) (bindingTypes : List Ty) : Prop :=
  ∀ targetValue matcherValue,
    evalFuel operationalFuel environment targetExpression = .ok targetValue →
    evalFuel operationalFuel environment matcherExpression = .ok matcherValue →
      TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
        (evaluationAtomReducer (evalFuel operationalFuel)) operationalFuel
        bindingIndex
        ⟨[⟨pattern, matcherValue, targetValue⟩], environment, []⟩
        bindingTypes

/-- Compose caller-supplied local two-index search preservation with whole
`matchAll` evaluation.

`operationalFuel` is honestly shared by target evaluation, matcher
evaluation, the atom-evaluation callback, DFS state visits, and body
evaluation because that is the executable `evalFuel` rule.  `bindingIndex`
is the logical index retained on completed search answers, whereas
`resultIndex` is the independently selected logical index of body results.

This theorem assumes no structural `EnvironmentTyping` or `ValueTyping`, no
equation or safety premise for the completed search, and no certificate
mentioning the final `matchAll` result.  The bounded initial-state certificate
does recursively contain local safety for each actual reducer successor. -/
theorem matchAllFuel_twoIndexSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (targetSafe : FuelResultSafe operationalFuel matcherTarget
      (evalFuel operationalFuel environment targetExpression))
    (matcherSafe : FuelResultSafe operationalFuel
      (.matcher capability matcherTarget)
      (evalFuel operationalFuel environment matcherExpression))
    (initialTyped : EvaluatedTwoIndexInitialStateTyping
      environmentInvariant bindingsInvariant operationalFuel bindingIndex
      environment targetExpression matcherExpression pattern bindingTypes)
    (bodySafe : EvaluatedBindingBodySafeUnder
      (bindingsInvariant bindingIndex) operationalFuel resultIndex environment
      bindingTypes bodyExpression bodyTarget) :
    FuelResultSafe resultIndex (TypePM.DataTypes.list bodyTarget)
      (evalFuel (operationalFuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern
          bodyExpression)) := by
  have searchSafe : EvaluatedPatternSearchSafeUnder
      (bindingsInvariant bindingIndex) operationalFuel environment
      targetExpression matcherExpression pattern bindingTypes := by
    intro targetValue matcherValue targetSuccess matcherSuccess
    exact searchPatternFuel_twoIndexSafe environmentDownward bindingsDownward
      (initialTyped targetValue matcherValue targetSuccess matcherSuccess)
  exact matchAllFuel_valueAndBindingIndexedSafe targetSafe matcherSafe
    searchSafe bodySafe

end TypePM.Runtime
