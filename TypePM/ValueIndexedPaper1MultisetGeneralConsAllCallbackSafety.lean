import TypePM.Runtime.EvaluationStuckMonotonicity
import TypePM.ValueIndexedPaper1MultisetGeneralConsSafety

/-!
# Monotonicity-seeded all-callback safety for Paper 1 general cons

The direct theorem for the actual fourth multiset clause computes every
callback bound below 26 as a timeout and bound 26 as the first successful
dispatch.  This module completes the callback range as follows:

* below 26, it uses those direct timeout equations;
* at and above 26, it transports the exact completed dispatch result with
  dispatch-only evaluator-fuel approximation;
* at every callback bound, it derives recursive atom typing and then proves
  typed/no-stuck search for arbitrary DFS fuel.

This is deliberately not the still-desired structural all-callback proof.
The post-26 part is seeded by the exact dispatch computation at callback fuel
26.  It does not use a fixed successful whole-search result or matching-search
fuel monotonicity.
-/

namespace TypePM.ValueIndexedPaper1MultisetGeneralConsAllCallbackSafety

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open Source.MatcherTyping.M4Paper1MultisetSearchSafety
open ValueIndexedPaper1MultisetHeadConsSafety
open ValueIndexedPaper1MultisetGeneralConsSafety

/-- Once the actual seven-clause dispatch has completed at callback bound 26,
its exact hit and source-ordered branches are unchanged at every larger
callback bound.  Only the generic successor-approximation transport is used. -/
theorem generalCons_dispatch_exact_of_26_le
    (enough : 26 ≤ callbackFuel) (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
      closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
      multisetConsTarget = .ok (.hit multisetConsBranches) := by
  exact FuelResult.Approximates.ok_eq_of_le
    (fun fuel => dispatchMatcherClauses (evalFuel fuel) atomEnvironment
      closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
      multisetConsTarget)
    (fun fuel => dispatchMatcherClauses_evalFuel_approximates_succ
      (fuel := fuel) (atomEnvironment := atomEnvironment)
      (matcherEnvironment := closedMultisetMatcherEnvironment)
      (clauses := multisetClauses) (pattern := multisetConsPattern)
      (target := multisetConsTarget))
    (generalCons_dispatch_exact26 atomEnvironment) enough

/-- Complete callback classification.  The timeout half is direct; the hit
half is the monotonicity-seeded transport above. -/
theorem generalCons_dispatch_allCallback :
    ∀ callbackFuel atomEnvironment,
      dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
        multisetConsTarget = .timeout ∨
      dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
        multisetConsTarget = .ok (.hit multisetConsBranches) := by
  intro callbackFuel atomEnvironment
  by_cases before : callbackFuel < 26
  · exact .inl (generalCons_dispatch_timeout_before26 before atomEnvironment)
  · have bound : 26 ≤ callbackFuel := Nat.le_of_not_gt before
    exact .inr (generalCons_dispatch_exact_of_26_le bound atomEnvironment)

/-- Pattern-indexed recursive dispatch typing at every callback bound.  The
actual source patterns `$` and `$` are retained in each successful branch. -/
theorem generalCons_patternIndexedRecursiveDispatchTyping_allCallback
    (atomEnvironment : ValueEnvironment) :
    PatternIndexedRecursiveDispatchTyping expressionTyping
      (evalFuel callbackFuel) environmentTypes bindingTypes
      [.int, DataTypes.list .int]
      (dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
        multisetConsTarget) := by
  rcases generalCons_dispatch_allCallback callbackFuel atomEnvironment with
    timeout | success
  · rw [timeout]
    exact .timeout
  · rw [success]
    exact .hit (patterns := [.var, .var])
      multisetCons_dispatch_preserves_source_patterns
      (multisetConsBranch_recursiveTyping (callbackFuel := callbackFuel))

/-- Recursive atom typing for the actual general-cons atom at every evaluator
callback bound. -/
theorem generalCons_recursiveAtomTyping_allCallback :
    RecursiveTotalMatchingAtomTyping expressionTyping (evalFuel callbackFuel)
      environmentTypes bindingTypes
      ⟨multisetConsPattern, closedMultisetMatcherValue,
        multisetConsTarget⟩ [.int, DataTypes.list .int] := by
  apply RecursiveTotalMatchingAtomTyping.patternIndexedUser
  · intro atomEnvironment
    simp [multisetConsPattern, reduceBuiltinAtom]
  · intro atomEnvironment _
    exact generalCons_patternIndexedRecursiveDispatchTyping_allCallback
      atomEnvironment

/-- For every evaluator callback bound and every DFS bound, the actual
general-cons search either times out or returns well-typed answers.  No
successful whole-search execution is used as a seed. -/
theorem multisetCons_search_recursiveTypedSafe_allCallback
    (callbackFuel searchFuel : Nat) :
    TypedMatchingSearchResult [.int, DataTypes.list .int]
      (searchPatternFuel (evalFuel callbackFuel) searchFuel []
        multisetConsPattern closedMultisetMatcherValue multisetConsTarget) := by
  exact searchPatternFuel_recursiveTotalTypedSafe
    (expressionTyping := CoreExpressionTyping) (eval := evalFuel callbackFuel)
    (evalFuel_totalCore_embeddedSafe callbackFuel) .nil
    (generalCons_recursiveAtomTyping_allCallback
      (expressionTyping := CoreExpressionTyping)
      (environmentTypes := []) (bindingTypes := [])) searchFuel

/-- Arbitrary evaluator-callback and DFS-fuel search cannot get stuck. -/
theorem multisetCons_search_recursiveNeverStuck_allCallback
    (callbackFuel searchFuel : Nat) :
    (searchPatternFuel (evalFuel callbackFuel) searchFuel []
      multisetConsPattern closedMultisetMatcherValue
      multisetConsTarget).NotStuck := by
  rcases multisetCons_search_recursiveTypedSafe_allCallback callbackFuel
      searchFuel with timeout | ⟨answers, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TypePM.ValueIndexedPaper1MultisetGeneralConsAllCallbackSafety
