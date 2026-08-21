import TypePM.TwoIndexMatchingSearchSafety
import TypePM.Source.M4PatternIndexedRecursiveDispatchBridge

/-!
# Two-index producer for one user-matcher reduction

`FuelIndexedPatternDispatchTyping` classifies the result of one actual
pattern-indexed matcher dispatch.  `TwoIndexAtomReducerCertificate` is the
local interface consumed by the two-index DFS theorem.  This module connects
those two boundaries for a user-matcher atom.

The only continuation premise is a producer from bounded M4 branch work at
`searchFuel` to the corresponding successor state at that same predecessor
search index.  The caller chooses both indexed relations and the retained
logical index.  No premise contains a completed search result or
whole-evaluator safety, and this boundary does not directly request
`EnvironmentTyping` or `ValueTypings`.  Constructing the imported bounded M4
work certificate remains a separate caller obligation.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Local continuation interface for branches returned by one user matcher.
The input is the bounded M4 work certificate retained by the pattern-indexed
dispatch bridge.  The output is exactly the successor state visited after the
current state consumes one DFS visit. -/
def TwoIndexUserMatcherBranchProducer
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (searchFuel residual : Nat)
    (environmentTypes bindingTypes newBindings : List Ty)
    (environment : ValueEnvironment) (bindings : List Value)
    (remaining : List MatchingAtom) (answerTypes : List Ty) : Prop :=
  ∀ {branch},
    FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval searchFuel
      environmentTypes bindingTypes branch newBindings →
    TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
      (evaluationAtomReducer eval) searchFuel residual
      ⟨branch ++ remaining, environment, bindings⟩ answerTypes

namespace TwoIndexUserMatcherBranchProducer

/-- With no remaining DFS visit, a pending successor state is not inspected,
regardless of the contents of its worklist. -/
theorem zero :
    TwoIndexUserMatcherBranchProducer environmentInvariant bindingsInvariant
      expressionTyping eval 0 residual environmentTypes bindingTypes
      newBindings environment bindings remaining answerTypes := by
  intro branch branchTyped
  exact .zero

end TwoIndexUserMatcherBranchProducer

namespace FuelIndexedPatternDispatchTyping

/-- Convert one exact user-matcher dispatch into the reducer certificate used
by two-index DFS.  Built-in miss is required only for the concrete runtime
atom environment `bindings ++ environment`.  On a dispatch hit, the M4
pattern-indexed certificate supplies bounded work for each actual branch and
the caller's producer checks the corresponding immediate successor. -/
theorem toTwoIndexUserMatcherAtomCertificate
    (dispatchTyped : FuelIndexedPatternDispatchTyping expressionTyping eval
      searchFuel environmentTypes bindingTypes newBindings
      (dispatchMatcherClauses eval (bindings ++ environment)
        matcherEnvironment remainingClauses pattern target))
    (builtinMiss :
      reduceBuiltinAtom eval (bindings ++ environment)
        ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
          target⟩ = .ok .miss)
    (produceBranch : TwoIndexUserMatcherBranchProducer environmentInvariant
      bindingsInvariant expressionTyping eval searchFuel residual
      environmentTypes bindingTypes newBindings environment bindings remaining
      answerTypes) :
    TwoIndexAtomReducerCertificate environmentInvariant bindingsInvariant
      (evaluationAtomReducer eval) searchFuel residual environment bindings
      ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
        target⟩ remaining answerTypes := by
  generalize dispatchEq :
      dispatchMatcherClauses eval (bindings ++ environment)
        matcherEnvironment remainingClauses pattern target = dispatchResult
    at dispatchTyped
  cases dispatchTyped with
  | timeout =>
      exact .timeout (by
        unfold evaluationAtomReducer combineAtomReducers
        rw [builtinMiss]
        simp only [FuelResult.bind]
        simpa [reduceMatcherAtom] using
          congrArg (FuelResult.map clauseResultToAtomReduction) dispatchEq)
  | hit branchesTyped =>
      rename_i patterns branches
      let reduction : AtomReduction := ⟨branches, []⟩
      apply TwoIndexAtomReducerCertificate.hit reduction
      · unfold evaluationAtomReducer combineAtomReducers
        rw [builtinMiss]
        simp only [FuelResult.bind]
        simpa [reduceMatcherAtom, reduction, clauseResultToAtomReduction] using
          congrArg (FuelResult.map clauseResultToAtomReduction) dispatchEq
      · intro successor successorMember
        simp only [MatchingState.successors] at successorMember
        rcases List.mem_map.mp successorMember with
          ⟨branch, branchMember, rfl⟩
        simpa [MatchingState.continueWith, reduction] using
          produceBranch (branchesTyped.recursive_member branch branchMember)

/-- Package the same local dispatch preservation as a complete current-state
certificate.  The current environment and accumulated bindings are checked
at `searchFuel + 1 + residual`; dispatch successors are checked at
`searchFuel`, as required by `TwoIndexMatchingStateTyping.reduce`. -/
theorem toTwoIndexUserMatcherStateTyping
    (dispatchTyped : FuelIndexedPatternDispatchTyping expressionTyping eval
      searchFuel environmentTypes bindingTypes newBindings
      (dispatchMatcherClauses eval (bindings ++ environment)
        matcherEnvironment remainingClauses pattern target))
    (environmentTyped : environmentInvariant (searchFuel + 1 + residual)
      environment environmentTypes)
    (bindingsTyped : bindingsInvariant (searchFuel + 1 + residual)
      bindings bindingTypes)
    (builtinMiss :
      reduceBuiltinAtom eval (bindings ++ environment)
        ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
          target⟩ = .ok .miss)
    (produceBranch : TwoIndexUserMatcherBranchProducer environmentInvariant
      bindingsInvariant expressionTyping eval searchFuel residual
      environmentTypes bindingTypes newBindings environment bindings remaining
      answerTypes) :
    TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
      (evaluationAtomReducer eval) (searchFuel + 1) residual
      ⟨⟨pattern, .matcherV matcherEnvironment original remainingClauses,
        target⟩ :: remaining, environment, bindings⟩ answerTypes := by
  exact .reduce environmentTyped bindingsTyped
    (dispatchTyped.toTwoIndexUserMatcherAtomCertificate builtinMiss
      produceBranch)

end FuelIndexedPatternDispatchTyping

end TypePM.Runtime
