import TypePM.Source.M4EnvironmentIndexedRecursiveSearchBridge

/-!
# Fuel-indexed producer for environment-indexed recursive search

`M4EnvironmentIndexedRecursiveSearchBridge` proves bounded DFS safety from an
`EnvironmentIndexedMatchingStateTyping` certificate, but constructing that
certificate directly can require spelling out the whole finite local
transition tree of a concrete matcher.

This module supplies the missing compositional producer.  It consumes the
existing `FuelIndexedRecursiveMatchingAtomsTyping` evidence for pending work
and a caller-provided *local reducer preservation law*.  That law classifies
one actual reducer call as timeout or a typed hit.  A typed hit contains
fuel-indexed work evidence for each immediate branch at the strict predecessor
index.  The producer combines that branch with the remaining work and creates
the corresponding `EnvironmentIndexedAtomReducerCertificate`.

The ordinary state environment is governed by a caller-selected invariant;
accumulated bindings and returned answers retain the existing `ValueTypings`
relation.  Runtime order remains `bindings ++ environment`.  No premise
mentions the result of the complete DFS search.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Local progress and preservation for a fuel-indexed atom under a selected
ordinary-environment invariant.  In the hit case, `reduction.bindings` are
typed immediately and every returned branch carries pending-work evidence at
the strict predecessor of the atom's state index. -/
def EnvironmentIndexedFuelRecursiveAtomReducerTypedSafe
    (environmentInvariant : MatchingEnvironmentInvariant)
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (reduceAtom : AtomReducer) : Prop :=
  ∀ {fuel environmentTypes bindingTypes environment bindings atom
      newBindings},
    environmentInvariant environment environmentTypes →
    ValueTypings bindings bindingTypes →
    FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval (fuel + 1)
      environmentTypes bindingTypes atom newBindings →
    reduceAtom (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) ∧
        FuelIndexedRecursiveAtomReductionTyping expressionTyping eval fuel
          environmentTypes bindingTypes newBindings reduction

/-- The older reducer-preservation law is the special case whose environment
invariant is ordinary `EnvironmentTyping`. -/
theorem FuelIndexedRecursiveAtomReducerTypedSafe.toEnvironmentIndexed
    (safe : FuelIndexedRecursiveAtomReducerTypedSafe expressionTyping eval
      reduceAtom) :
    EnvironmentIndexedFuelRecursiveAtomReducerTypedSafe
      (fun environment environmentTypes =>
        EnvironmentTyping environment environmentTypes)
      expressionTyping eval reduceAtom := by
  intro fuel environmentTypes bindingTypes environment bindings atom
    newBindings environmentTyped bindingsTyped atomTyped
  exact safe environmentTyped bindingsTyped atomTyped

/-- Existing evaluator safety therefore supplies the new local law whenever
the selected invariant is the old ordinary environment judgment. -/
theorem evaluationAtomReducer_environmentIndexedFuelRecursiveTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval) :
    EnvironmentIndexedFuelRecursiveAtomReducerTypedSafe
      (fun environment environmentTypes =>
        EnvironmentTyping environment environmentTypes)
      expressionTyping eval (evaluationAtomReducer eval) :=
  FuelIndexedRecursiveAtomReducerTypedSafe.toEnvironmentIndexed
    (expressionTyping := expressionTyping) (eval := eval)
    (reduceAtom := evaluationAtomReducer eval)
    (evaluationAtomReducer_fuelIndexedTypedSafe
      (expressionTyping := expressionTyping) (eval := eval) evalSafe)

namespace FuelIndexedRecursiveMatchingAtomsTyping

/-- Convert bounded pending-work evidence into the environment-indexed state
certificate consumed by the generic DFS theorem.  A hit is handled solely by
its immediate reduction typing: each branch is appended to the old tail and
checked recursively at the strict predecessor index. -/
theorem toEnvironmentIndexedState
    (reducerSafe : EnvironmentIndexedFuelRecursiveAtomReducerTypedSafe
      environmentInvariant expressionTyping eval reduceAtom)
    (environmentTyped : environmentInvariant environment environmentTypes)
    (bindingsTyped : ValueTypings bindings bindingTypes)
    (workTyped : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval
      fuel environmentTypes bindingTypes work futureBindings) :
    EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom fuel
      ⟨work, environment, bindings⟩ (bindingTypes ++ futureBindings) := by
  induction fuel generalizing environment bindings bindingTypes work
      futureBindings with
  | zero =>
      exact .zero
  | succ fuel induction =>
      cases workTyped with
      | nil =>
          simpa using
            (EnvironmentIndexedMatchingStateTyping.yield
              environmentTyped bindingsTyped)
      | cons headTyped tailTyped =>
          rename_i atom headBindings atoms tailBindings
          apply EnvironmentIndexedMatchingStateTyping.reduce
            environmentTyped bindingsTyped
          rcases reducerSafe environmentTyped bindingsTyped headTyped with
            timeout | ⟨reduction, reduced, reductionTyped⟩
          · exact .timeout timeout
          · cases reductionTyped with
            | intro immediateTypes immediateTyped branchesTyped =>
                apply EnvironmentIndexedAtomReducerCertificate.hit reduction
                  reduced
                intro successor successorMember
                simp only [MatchingState.successors] at successorMember
                rcases List.mem_map.mp successorMember with
                  ⟨branch, branchMember, rfl⟩
                obtain ⟨delayedTypes, branchTyped, bindingEq⟩ :=
                  branchesTyped branch branchMember
                have branchAndTail :=
                  FuelIndexedRecursiveMatchingAtomsTyping.append fuel
                    branchTyped (by
                      simpa [List.append_assoc, bindingEq] using tailTyped)
                have newBindingsTyped :=
                  bindingsTyped.append immediateTyped
                have successorTyped := induction
                  environmentTyped newBindingsTyped branchAndTail
                have answerEq :
                    (bindingTypes ++ immediateTypes) ++
                        (delayedTypes ++ tailBindings) =
                      bindingTypes ++ (headBindings ++ tailBindings) := by
                  simp only [List.append_assoc]
                  rw [← List.append_assoc immediateTypes delayedTypes,
                    bindingEq]
                rw [answerEq] at successorTyped
                exact successorTyped

end FuelIndexedRecursiveMatchingAtomsTyping

namespace EnvironmentIndexedAtomReducerCertificate

/-- Public one-step producer.  The head atom and its remaining pending work
are combined into a state certificate; inversion exposes exactly the local
reducer certificate needed by `EnvironmentIndexedMatchingStateTyping.reduce`.
-/
theorem ofFuelIndexedRecursiveWork
    (reducerSafe : EnvironmentIndexedFuelRecursiveAtomReducerTypedSafe
      environmentInvariant expressionTyping eval reduceAtom)
    (environmentTyped : environmentInvariant environment environmentTypes)
    (bindingsTyped : ValueTypings bindings bindingTypes)
    (headTyped : FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval
      (fuel + 1) environmentTypes bindingTypes atom headBindings)
    (tailTyped : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval
      fuel environmentTypes (bindingTypes ++ headBindings) remaining
      tailBindings) :
    EnvironmentIndexedAtomReducerCertificate environmentInvariant reduceAtom
      fuel environment bindings atom remaining
      (bindingTypes ++ (headBindings ++ tailBindings)) := by
  have stateTyped :=
    FuelIndexedRecursiveMatchingAtomsTyping.toEnvironmentIndexedState
      reducerSafe environmentTyped bindingsTyped
      (FuelIndexedRecursiveMatchingAtomsTyping.cons headTyped tailTyped)
  cases stateTyped with
  | reduce environmentTyped bindingsTyped atomSafe =>
      exact atomSafe

end EnvironmentIndexedAtomReducerCertificate

/-- Reusable initial-search endpoint.  A bounded M4 recursive-work certificate
and the invariant-indexed local reducer law produce the initial state
certificate compositionally, after which the generic environment-indexed DFS
theorem applies. -/
theorem searchPatternFuel_environmentIndexedFuelRecursiveTypedSafe
    (reducerSafe : EnvironmentIndexedFuelRecursiveAtomReducerTypedSafe
      environmentInvariant expressionTyping eval (evaluationAtomReducer eval))
    (environmentTyped : environmentInvariant environment environmentTypes)
    (workTyped : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval
      fuel environmentTypes [] [⟨pattern, matcher, target⟩] bindingTypes) :
    TypedMatchingSearchResult bindingTypes
      (searchPatternFuel eval fuel environment pattern matcher target) := by
  apply searchPatternFuel_environmentIndexedTypedSafe
    (environmentInvariant := environmentInvariant)
  simpa using
    (FuelIndexedRecursiveMatchingAtomsTyping.toEnvironmentIndexedState
      reducerSafe environmentTyped (.nil) workTyped)

end TypePM.Runtime
