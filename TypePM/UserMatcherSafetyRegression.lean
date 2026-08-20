import TypePM.UserMatcherSafety

/-!
# Typed user-matcher regression

The regression instantiates the scoped callback premises with the real
fuel-bounded evaluator.  It therefore checks both the concrete reduction and
the `AtomReductionTyping` certificate for its delegated `something` branch.
-/

namespace TypePM.UserMatcherSafetyRegression

open TypePM.Source TypePM.Runtime

def matcher : Value :=
  .matcherV [] [singleHoleVariableClause] [singleHoleVariableClause]

def atom : MatchingAtom := ⟨.var, matcher, .int 7⟩

theorem atom_typed : SingleHoleUserAtomTyping atom .int := by
  exact .mk .nil (.int 7)

theorem evalFuel_two_singleton_body
    {matcherEnvironment : ValueEnvironment} {targetValue : Value} :
    evalFuel 2 (targetValue :: matcherEnvironment) singletonDecompositionBody =
      .ok (Value.buildList [targetValue]) := by
  with_unfolding_all rfl

theorem evalFuel_two_something (environment : ValueEnvironment) :
    evalFuel 2 environment .something = .ok .something := by
  rfl

theorem concrete_user_clause_reduction_typed :
    ∃ reduction,
      reduceMatcherAtom (evalFuel 2) [] atom = .ok (.hit reduction) ∧
      AtomReductionTyping
        (fun context expression target => RuntimeTyping expression target context)
        [] [] [.int] reduction := by
  apply reduceMatcherAtom_singleHole_typedSafe (evalFuel 2)
    (environment := []) (bindings := [])
  · exact .nil
  · exact .nil
  · exact atom_typed
  · intro matcherEnvironment definitionTypes targetValue
      environmentTyped targetTyped
    exact evalFuel_two_singleton_body
  · exact evalFuel_two_something

theorem concrete_user_clause_reduction_exact :
    reduceMatcherAtom (evalFuel 2) [] atom =
      .ok (.hit ⟨[[⟨.var, .something, .int 7⟩]], []⟩) := by
  with_unfolding_all rfl

end TypePM.UserMatcherSafetyRegression
