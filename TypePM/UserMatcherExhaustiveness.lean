import TypePM.Source.M4MatcherTyping
import TypePM.UserMatcherGeneralSafety

/-!
# Runtime consequence of the final matcher catch-all

M4 matcher literals are required to end in a hole pattern-pattern whose only
data arm is a variable.  At runtime, inspecting the hole header always
succeeds.  Moreover, once a clause header has been selected,
`closeMatcherArmsResult` turns exhaustion of its data arms into a successful
empty hit.  Consequently a clause list satisfying the declarative final
catch-all condition cannot complete dispatch with `.miss`.

This module proves that syntactic fact independently of typing and then
combines it with the existing conditional preservation theorem.  Evaluation
may still time out; the theorem only rules out a normal final miss and a
rule-coverage failure for already typed callbacks.
-/

namespace TypePM.Runtime

open TypePM.Source

private theorem catchAllClauseDispatches_result_ne_miss
    {eval : ValueEnvironment → Source.Expr → FuelResult Value}
    {atomEnvironment matcherEnvironment : ValueEnvironment}
    {pattern : Source.Pattern} {target : Value}
    {next body : Source.Expr} {result : DispatchResult MatchingBranches}
    (dispatch : MatcherClauseDispatches eval atomEnvironment matcherEnvironment
      pattern target (.mk .hole next [.mk .var body]) result) :
    result ≠ .miss := by
  cases dispatch with
  | miss mismatch =>
      simp [inspectPatternPattern] at mismatch
  | matched _headerMatch _capturesEval _armsDispatch =>
      simp only [closeMatcherArmsResult]
      split <;> simp

/-- The proof-level final catch-all condition excludes a completed clause-list
dispatch whose result is `.miss`.  No evaluator-safety premise is needed for
this structural fact. -/
theorem finalCatchAll_clausesDispatch_ne_miss
    {eval : ValueEnvironment → Source.Expr → FuelResult Value}
    {atomEnvironment matcherEnvironment : ValueEnvironment}
    {clauses : List Source.MatcherClause} {pattern : Source.Pattern}
    {target : Value}
    (finalCatchAll : MatcherTyping.FinalCatchAll clauses) :
    ¬ MatcherClausesDispatch eval atomEnvironment matcherEnvironment
      pattern target clauses .miss := by
  induction finalCatchAll with
  | last =>
      intro dispatch
      cases dispatch with
      | skip missed _tail =>
          exact catchAllClauseDispatches_result_ne_miss missed rfl
  | skip tail induction =>
      intro dispatch
      cases dispatch with
      | skip _missed tailDispatch =>
          exact induction tailDispatch

/-- Executable form of `clausesDispatch_ne_miss`: a matcher satisfying the
declarative final catch-all condition cannot return a normal final miss. -/
theorem finalCatchAll_dispatch_ne_miss
    {eval : ValueEnvironment → Source.Expr → FuelResult Value}
    {atomEnvironment matcherEnvironment : ValueEnvironment}
    {clauses : List Source.MatcherClause} {pattern : Source.Pattern}
    {target : Value}
    (finalCatchAll : MatcherTyping.FinalCatchAll clauses) :
    dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
      pattern target ≠ .ok .miss := by
  intro dispatched
  exact finalCatchAll_clausesDispatch_ne_miss finalCatchAll
    ((dispatchMatcherClauses_eq_ok_iff _ _ _ _ _ _ _).mp dispatched)

/-- Typed user-matcher dispatch with a final catch-all either exhausts its
fuel or returns typed recursive matching branches.  The `.miss` alternative
of the general clause-list theorem is eliminated by the static condition. -/
theorem dispatchMatcherClauses_typedSafe_of_finalCatchAll
    {eval : ValueEnvironment → Source.Expr → FuelResult Value}
    {atomEnvironmentTypes definitionTypes : List Ty}
    {atomEnvironment matcherEnvironment : ValueEnvironment}
    {matcherTarget : Ty} {pattern : Source.Pattern} {target : Value}
    {clauses : List Source.MatcherClause}
    (evalSafe : EmbeddedEvaluatorSafe
      (fun context expression target => RuntimeTyping expression target context)
      eval)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (clausesTyped : RuntimeMatcherClausesInputTyping atomEnvironmentTypes
      definitionTypes matcherTarget pattern clauses)
    (finalCatchAll : MatcherTyping.FinalCatchAll clauses) :
    dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
        pattern target = .timeout ∨
      ∃ branches holes,
        dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
            pattern target = .ok (.hit branches) ∧
          DelegatedMatchingBranchesTyping holes branches := by
  rcases dispatchMatcherClauses_typedSafe evalSafe atomEnvironmentTyped
      matcherEnvironmentTyped targetTyped clausesTyped with
    timeout | ⟨result, success, resultTyped⟩
  · exact .inl timeout
  · cases resultTyped with
    | miss =>
        exact False.elim (finalCatchAll_dispatch_ne_miss finalCatchAll success)
    | @hit holes branches branchesTyped =>
        exact .inr ⟨branches, holes, success, branchesTyped⟩

end TypePM.Runtime
