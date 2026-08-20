import TypePM.UserMatcherExhaustiveness
import TypePM.UserMatcherGeneralSafetyRegression

/-!
# Final catch-all progress regression

The one-hole variable clause has exactly the declarative final catch-all shape.
The general theorem therefore strengthens its clause-list result from
`timeout` or a typed result (possibly `.miss`) to `timeout` or a typed hit.
-/

namespace TypePM.UserMatcherExhaustivenessRegression

open TypePM.Source TypePM.Runtime
open TypePM.UserMatcherGeneralSafetyRegression

theorem singleHole_finalCatchAll :
    MatcherTyping.FinalCatchAll [singleHoleVariableClause] :=
  .last

theorem singleHole_dispatch_typedHit :
    dispatchMatcherClauses (evalFuel 3) [] [] [singleHoleVariableClause]
        .var (.int 5) = .timeout ∨
      ∃ branches holes,
        dispatchMatcherClauses (evalFuel 3) [] [] [singleHoleVariableClause]
            .var (.int 5) = .ok (.hit branches) ∧
          DelegatedMatchingBranchesTyping holes branches := by
  exact dispatchMatcherClauses_typedSafe_of_finalCatchAll
    (coreEvaluatorSafe 3) .nil .nil (.int 5)
    (.cons oneHoleClause_input_typed .nil) singleHole_finalCatchAll

theorem singleHole_dispatch_not_miss :
    dispatchMatcherClauses (evalFuel 3) [] [] [singleHoleVariableClause]
      .var (.int 5) ≠ .ok .miss :=
  finalCatchAll_dispatch_ne_miss singleHole_finalCatchAll

end TypePM.UserMatcherExhaustivenessRegression
