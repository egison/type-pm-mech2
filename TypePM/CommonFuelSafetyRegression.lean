import TypePM.CommonFuelSafety

/-!
# Common-fuel regression: empty user match and explicit fallback

The sole ordinary arm is a wildcard, but the user matcher returns zero
decompositions.  The typed matching search therefore returns no binding
groups and `matchFirst` evaluates its separate matcher-independent fallback.
-/

namespace TypePM.CommonFuelSafetyRegression

open TypePM.Runtime
open TypePM.Source

def noDecompositions : Source.Expr := .ctor DataCtor.nil []

def emptyClause : MatcherClause :=
  .mk .hole .something [.mk .var noDecompositions]

def emptyMatcher : Source.Expr := .matcher [emptyClause]

def wildcardElse : Source.Expr :=
  .matchFirst (.lit 0) emptyMatcher [.mk .wild (.lit 42)] (.lit 9)

private theorem emptyClause_runtimeTyping :
    RuntimeMatcherClauseTyping [] .int emptyClause := by
  apply RuntimeMatcherClauseTyping.mk
  · exact RuntimePPatTyping.hole .any
  · exact .one (.checked (.something .int) (.matcherToSlot .equal))
  · exact .cons (.mk .var (.listNil .int)) .nil

private theorem emptyClause_inputTyping :
    RuntimeMatcherClauseInputTyping [] [] .int .wild emptyClause := by
  apply RuntimeMatcherClauseInputTyping.mk
  · exact RuntimePPatTyping.hole .any
  · exact .one (.checked (.something .int) (.matcherToSlot .equal))
  · exact .cons (.mk .var (.listNil .int)) .nil
  · intro dispatch inspected
    simp [inspectPatternPattern] at inspected
    subst dispatch
    exact .nil

private theorem emptyClauses_inputTyping :
    RuntimeMatcherClausesInputTyping [] [] .int .wild [emptyClause] :=
  .cons emptyClause_inputTyping .nil

private theorem emptyMatcher_dispatches_noBranches
    (success : dispatchMatcherClauses (evalFuel fuel) atomEnvironment []
      [emptyClause] .wild (.int 0) = .ok (.hit branches)) :
    branches = [] := by
  cases fuel with
  | zero =>
      simp [dispatchMatcherClauses, firstHit, tryMatcherClause,
        inspectPatternPattern, FuelResult.traverse, tryMatcherArm,
        matchValueDataPattern, evalFuel, noDecompositions, emptyClause] at success
  | succ fuel =>
      simpa [dispatchMatcherClauses, firstHit, tryMatcherClause,
        inspectPatternPattern, FuelResult.traverse, tryMatcherArm,
        matchValueDataPattern, evalFuel, noDecompositions, emptyClause,
        decodeDecompositions, decodeProduct, Value.viewList, DataCtor.nil,
        buildMatchingBranches,
        closeMatcherArmsResult, FuelResult.bind, FuelResult.map] using success

private theorem wildcard_initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (environmentTyped : EnvironmentTyping environment [])
    (targetSuccess : evalFuel fuel environment (.lit 0) = .ok targetValue)
    (matcherSuccess : evalFuel fuel environment emptyMatcher = .ok matcherValue)
    (targetTyped : ValueTyping targetValue .int)
    (matcherTyped : ValueTyping matcherValue (.matcher .any .int)) :
    TotalMatchingAtomTyping [] []
      ⟨.wild, matcherValue, targetValue⟩ [] := by
  cases environmentTyped
  cases fuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ fuel =>
      simp [evalFuel, emptyMatcher] at targetSuccess matcherSuccess
      subst targetValue
      subst matcherValue
      apply TotalMatchingAtomTyping.user
      · intro eval atomEnvironment
        rfl
      · exact .nil
      · exact .int 0
      · exact emptyClauses_inputTyping
      · exact MatcherTyping.FinalCatchAll.last
      · intro dispatchFuel atomEnvironment holes branches dispatched
          branchesTyped branch member
        have empty := emptyMatcher_dispatches_noBranches dispatched
        subst branches
        simp at member

/-- Complete total-core certificate for the explicit-fallback program. -/
theorem wildcardElse_totalCoreTyping :
    TotalCoreTyping wildcardElse .int [] := by
  apply TotalCoreTyping.matchFirst
  · exact .core (.lit 0)
  · exact .matcher (.cons emptyClause_runtimeTyping .nil)
  · exact .cons wildcard_initialAtom (.core (.lit 42)) .nil
  · exact .core (.lit 9)

/-- Zero decompositions select the explicit fallback, not the wildcard body. -/
theorem wildcardElse_exact :
    evalFuel 21 [] wildcardElse = .ok (.int 9) := by
  with_unfolding_all rfl

/-- The common-fuel theorem now covers the user-matcher/explicit-else path. -/
theorem wildcardElse_typedResult (fuel : Nat) :
    TypedResult .int (evalFuel fuel [] wildcardElse) :=
  wildcardElse_totalCoreTyping.commonFuelSafety fuel [] .nil

/-- In particular the example never reaches `stuck`. -/
theorem wildcardElse_neverStuck (fuel : Nat) :
    (evalFuel fuel [] wildcardElse).NotStuck :=
  wildcardElse_totalCoreTyping.neverStuck fuel [] .nil

end TypePM.CommonFuelSafetyRegression
