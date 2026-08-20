import TypePM.Source.PatternIndexedRecursiveScopedSafety
import TypePM.ValueIndexedMatchAllSafety

/-!
# Fuel-indexed M4 pattern dispatch into recursive matching

`PatternIndexedMatcherClauseResultTyping` retains the exact source patterns
placed in every branch returned by one real matcher dispatch.  The older
recursive search certificate, however, asks for a finite proof that every
recursive atom is safe at every later search bound.  A recursive matcher can
recreate the same atom, so that unbounded certificate is intentionally too
strong for a bounded search.

This module adds a search-fuel index.  A user dispatch inspected with
`fuel + 1` must certify its actual returned branches only at `fuel`, exactly
the bound with which depth-first search visits successor states.  Direct M4
patterns (`var`, `wild`, value, tuple, conjunction, and disjunction) are
lowered automatically through the existing solved-M4 `PatternBinds` theorem.
Only a user-matcher atom supplies a strictly-smaller dispatch certificate.

The matcher closure's captured environment is never coerced to the old
`EnvironmentTyping` judgment.  That premise occurs only in the final
non-recursive corollary which invokes the pre-existing M4 dispatch theorem.
-/

namespace TypePM.Runtime

open TypePM.Source
open TypePM.Source.MatcherTyping

mutual

  /-- One atom is safe for the next matching-state visit.  User dispatch is
  tied to the exact callback and its successful branches are checked at the
  strictly smaller search index. -/
  inductive FuelIndexedRecursiveMatchingAtomTyping
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      Nat → List Ty → List Ty → MatchingAtom → List Ty → Prop where
    | builtin
        (typed : MatchingAtomTyping expressionTyping environmentTypes
          bindingTypes atom newBindings) :
        FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval (fuel + 1)
          environmentTypes bindingTypes atom newBindings
    /-- An already available unbounded recursive certificate is stable at
    every finite index.  The fuel-indexed user constructor below is the route
    that avoids requiring such a certificate for recursive self dispatch. -/
    | stable
        (typed : RecursiveTotalMatchingAtomTyping expressionTyping eval
          environmentTypes bindingTypes atom newBindings) :
        FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval (fuel + 1)
          environmentTypes bindingTypes atom newBindings
    | user
        (builtinMiss : ∀ atomEnvironment,
          reduceBuiltinAtom eval atomEnvironment
            ⟨pattern, .matcherV matcherEnvironment original remaining,
              target⟩ = .ok .miss)
        (dispatch : ∀ atomEnvironment,
          EnvironmentTyping atomEnvironment
            (bindingTypes ++ environmentTypes) →
          FuelIndexedPatternDispatchTyping expressionTyping eval fuel
            environmentTypes bindingTypes newBindings
            (dispatchMatcherClauses eval atomEnvironment matcherEnvironment
              remaining pattern target)) :
        FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval (fuel + 1)
          environmentTypes bindingTypes
          ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩
          newBindings

  /-- Pending work for exactly the remaining number of state visits.  At
  index zero a nonempty worklist necessarily times out before inspecting its
  first atom, so its eventual binding index is irrelevant. -/
  inductive FuelIndexedRecursiveMatchingAtomsTyping
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      Nat → List Ty → List Ty → List MatchingAtom → List Ty → Prop where
    | zero
        (nonempty : atoms ≠ []) :
        FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval 0
          environmentTypes bindingTypes atoms newBindings
    | nil :
        FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
          environmentTypes bindingTypes [] []
    | cons
        (head : FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval
          (fuel + 1) environmentTypes bindingTypes atom headBindings)
        (tail : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval
          fuel environmentTypes (bindingTypes ++ headBindings)
          atoms tailBindings) :
        FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval (fuel + 1)
          environmentTypes bindingTypes (atom :: atoms)
          (headBindings ++ tailBindings)

  /-- Exact successful branch list with its M4-preserved source patterns and
  a bounded recursive certificate for each branch.  This main recursive
  relation deliberately does not retain `ValueTyping` for delegated matcher
  values: that older judgment cannot type a self-capturing matcher closure. -/
  inductive FuelIndexedPatternBranchesTyping
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      Nat → List Ty → List Ty → List Ty →
        List Pattern → MatchingBranches → Prop where
    | nil : FuelIndexedPatternBranchesTyping expressionTyping eval fuel
        environmentTypes bindingTypes newBindings patterns []
    | cons
        (patternsPreserved : branch.map (fun atom => atom.pattern) = patterns)
        (recursive : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping
          eval fuel environmentTypes bindingTypes branch newBindings)
        (tail : FuelIndexedPatternBranchesTyping expressionTyping eval fuel
          environmentTypes bindingTypes newBindings patterns branches) :
        FuelIndexedPatternBranchesTyping expressionTyping eval fuel
          environmentTypes bindingTypes newBindings patterns
          (branch :: branches)

  /-- Timeout-or-hit classification for the same real dispatch result.  A hit
  carries both source-pattern evidence and strictly-smaller recursive work. -/
  inductive FuelIndexedPatternDispatchTyping
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      Nat → List Ty → List Ty → List Ty →
        FuelResult (DispatchResult MatchingBranches) → Prop where
    | timeout : FuelIndexedPatternDispatchTyping expressionTyping eval fuel
        environmentTypes bindingTypes newBindings .timeout
    | hit
        (branches : FuelIndexedPatternBranchesTyping expressionTyping eval fuel
          environmentTypes bindingTypes newBindings patterns
          recursiveBranches) :
        FuelIndexedPatternDispatchTyping expressionTyping eval fuel
          environmentTypes bindingTypes newBindings
          (.ok (.hit recursiveBranches))

end

mutual

  /-- One extra available state visit can always be forgotten. -/
  theorem FuelIndexedRecursiveMatchingAtomTyping.previous
      (typing : FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval
        (fuel + 2) environmentTypes bindingTypes atom newBindings) :
      FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval
        (fuel + 1) environmentTypes bindingTypes atom newBindings := by
    cases typing with
    | builtin typed => exact .builtin typed
    | stable typed => exact .stable typed
    | user builtinMiss dispatch =>
        exact .user builtinMiss (by
          intro atomEnvironment atomEnvironmentTyped
          exact (dispatch atomEnvironment atomEnvironmentTyped).previous)

  /-- Pending work is downward closed in its remaining search bound. -/
  theorem FuelIndexedRecursiveMatchingAtomsTyping.previous
      (typing : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval
        (fuel + 1) environmentTypes bindingTypes atoms newBindings) :
      FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
        environmentTypes bindingTypes atoms newBindings := by
    cases fuel with
    | zero =>
        cases typing with
        | nil => exact .nil
        | cons head tail => exact .zero (by simp)
    | succ fuel =>
        cases typing with
        | nil => exact .nil
        | cons head tail => exact .cons head.previous tail.previous

  /-- Every exact returned branch can likewise be checked at a smaller
  remaining state bound. -/
  theorem FuelIndexedPatternBranchesTyping.previous
      (typing : FuelIndexedPatternBranchesTyping expressionTyping eval
        (fuel + 1) environmentTypes bindingTypes newBindings patterns
        branches) :
      FuelIndexedPatternBranchesTyping expressionTyping eval fuel
        environmentTypes bindingTypes newBindings patterns branches := by
    cases typing with
    | nil => exact .nil
    | cons patternsPreserved recursive tail =>
        exact .cons patternsPreserved recursive.previous tail.previous

  /-- Dispatch classifications are downward closed because only their
  returned recursive work depends on the search index. -/
  theorem FuelIndexedPatternDispatchTyping.previous
      (typing : FuelIndexedPatternDispatchTyping expressionTyping eval
        (fuel + 1) environmentTypes bindingTypes newBindings result) :
      FuelIndexedPatternDispatchTyping expressionTyping eval fuel
        environmentTypes bindingTypes newBindings result := by
    cases typing with
    | timeout => exact .timeout
    | hit branches => exact .hit branches.previous

end

namespace FuelIndexedRecursiveMatchingAtomsTyping

/-- Ordinary built-in atom work embeds at every finite search index. -/
theorem ofMatchingAtomsTyping :
    ∀ fuel {bindingTypes atoms newBindings},
      MatchingAtomsTyping expressionTyping environmentTypes
        bindingTypes atoms newBindings →
      FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
        environmentTypes bindingTypes atoms newBindings := by
  intro fuel
  induction fuel with
  | zero =>
      intro bindingTypes atoms newBindings typed
      cases typed with
      | nil => exact .nil
      | cons atom atoms headBindings tailBindings head tail =>
          exact .zero (by simp)
  | succ fuel induction =>
      intro bindingTypes atoms newBindings typed
      cases typed with
      | nil => exact .nil
      | cons atom atoms headBindings tailBindings head tail =>
          exact .cons (.builtin head) (induction tail)

end FuelIndexedRecursiveMatchingAtomsTyping

namespace FuelIndexedRecursiveMatchingAtomsTyping

/-- Existing unbounded recursive work is a sufficient (but not necessary)
certificate at every finite search index. -/
theorem ofRecursiveTotal :
    ∀ fuel {bindingTypes atoms newBindings},
      RecursiveTotalMatchingAtomsTyping expressionTyping eval environmentTypes
        bindingTypes atoms newBindings →
      FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
        environmentTypes bindingTypes atoms newBindings := by
  intro fuel
  induction fuel with
  | zero =>
      intro bindingTypes atoms newBindings typed
      cases typed with
      | nil => exact .nil
      | cons head tail => exact .zero (by simp)
  | succ fuel induction =>
      intro bindingTypes atoms newBindings typed
      cases typed with
      | nil => exact .nil
      | cons head tail => exact .cons (.stable head) (induction tail)

/-- Concatenate two bounded worklists.  The right worklist is weakened each
time a left atom consumes one state visit. -/
theorem append :
    ∀ fuel {bindingTypes leftAtoms leftBindings},
      FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
        environmentTypes bindingTypes leftAtoms leftBindings →
      ∀ {rightAtoms rightBindings},
        FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
          environmentTypes (bindingTypes ++ leftBindings)
          rightAtoms rightBindings →
        FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
          environmentTypes bindingTypes (leftAtoms ++ rightAtoms)
          (leftBindings ++ rightBindings) := by
  intro fuel
  induction fuel with
  | zero =>
      intro bindingTypes leftAtoms leftBindings left rightAtoms rightBindings
        right
      cases left with
      | zero nonempty =>
          exact .zero (by simp [nonempty])
      | nil => simpa using right
  | succ fuel induction =>
      intro bindingTypes leftAtoms leftBindings left rightAtoms rightBindings
        right
      cases left with
      | nil => simpa using right
      | cons head tail =>
          rename_i atom headBindings atoms tailBindings
          have right' : FuelIndexedRecursiveMatchingAtomsTyping
              expressionTyping eval fuel environmentTypes
              ((bindingTypes ++ headBindings) ++ tailBindings)
              rightAtoms rightBindings := by
            simpa [List.append_assoc] using right.previous
          have combined := induction tail right'
          simpa [List.append_assoc] using
            (FuelIndexedRecursiveMatchingAtomsTyping.cons head combined)

end FuelIndexedRecursiveMatchingAtomsTyping

namespace FuelIndexedPatternDispatchTyping

/-- The existing pattern-indexed unbounded dispatch certificate embeds into
the bounded relation.  This is a one-way compatibility bridge; recursive
self dispatch should normally use the genuinely fuel-indexed constructor. -/
theorem ofRecursiveTotal
    (typing : PatternIndexedRecursiveDispatchTyping expressionTyping eval
      environmentTypes bindingTypes newBindings result) :
    FuelIndexedPatternDispatchTyping expressionTyping eval fuel
      environmentTypes bindingTypes newBindings result := by
  cases typing with
  | timeout => exact .timeout
  | hit patternsPreserved branches =>
      rename_i recursiveBranches patterns
      apply FuelIndexedPatternDispatchTyping.hit
      induction recursiveBranches with
      | nil => exact .nil
      | cons branch recursiveBranches induction =>
          exact .cons
            (patternsPreserved branch (by simp))
            (FuelIndexedRecursiveMatchingAtomsTyping.ofRecursiveTotal fuel
              (branches branch (by simp)))
            (induction (by
              intro candidate member
              exact patternsPreserved candidate (by simp [member])) (by
              intro candidate member
              exact branches candidate (by simp [member])))

end FuelIndexedPatternDispatchTyping

namespace FuelIndexedPatternBranchesTyping

theorem recursive_member
    (typing : FuelIndexedPatternBranchesTyping expressionTyping eval fuel
      environmentTypes bindingTypes newBindings patterns branches) :
    ∀ branch ∈ branches,
      FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
        environmentTypes bindingTypes branch newBindings := by
  induction branches with
  | nil => simp
  | cons head tail induction =>
      cases typing with
      | cons patternsPreserved recursive rest =>
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact recursive
      · exact induction rest candidate member

theorem patterns_member
    (typing : FuelIndexedPatternBranchesTyping expressionTyping eval fuel
      environmentTypes bindingTypes newBindings patterns branches) :
    ∀ branch ∈ branches,
      branch.map (fun atom => atom.pattern) = patterns := by
  induction branches with
  | nil => simp
  | cons head tail induction =>
      cases typing with
      | cons patternsPreserved recursive rest =>
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact patternsPreserved
      · exact induction rest candidate member

end FuelIndexedPatternBranchesTyping

/-- Preservation data for one atom reduction at the strictly smaller search
index used for successor states. -/
inductive FuelIndexedRecursiveAtomReductionTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (environmentTypes bindingTypes expectedBindings : List Ty)
    (reduction : AtomReduction) : Prop where
  | intro
      (immediateTypes : List Ty)
      (immediateTyped : ValueTypings reduction.bindings immediateTypes)
      (branchesTyped : ∀ branch ∈ reduction.branches,
        ∃ delayedTypes,
          FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
            environmentTypes (bindingTypes ++ immediateTypes)
            branch delayedTypes ∧
          immediateTypes ++ delayedTypes = expectedBindings) :
      FuelIndexedRecursiveAtomReductionTyping expressionTyping eval fuel
        environmentTypes bindingTypes expectedBindings reduction

def FuelIndexedRecursiveAtomReducerTypedSafe
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (reduceAtom : AtomReducer) : Prop :=
  ∀ {fuel environmentTypes bindingTypes environment bindings atom newBindings},
    EnvironmentTyping environment environmentTypes →
    ValueTypings bindings bindingTypes →
    FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval (fuel + 1)
      environmentTypes bindingTypes atom newBindings →
    reduceAtom (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) ∧
        FuelIndexedRecursiveAtomReductionTyping expressionTyping eval fuel
          environmentTypes bindingTypes newBindings reduction

/-- Local progress and preservation for the real built-in-before-user
reducer.  The user case consumes only its exact fuel-indexed dispatch
certificate and never types the matcher closure's captured environment. -/
theorem evaluationAtomReducer_fuelIndexedTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval) :
    FuelIndexedRecursiveAtomReducerTypedSafe expressionTyping eval
      (evaluationAtomReducer eval) := by
  intro fuel environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | builtin typed =>
      rcases reduceBuiltinAtom_typedSafe expressionTyping eval evalSafe
          environmentTyped bindingsTyped typed with
        timeout | ⟨reduction, success, reductionTyped⟩
      · exact .inl (by
          simp [evaluationAtomReducer, combineAtomReducers, timeout])
      · refine .inr ⟨reduction, by
            simp [evaluationAtomReducer, combineAtomReducers, success], ?_⟩
        cases reductionTyped with
        | intro immediateTypes immediateTyped branchesTyped =>
            exact .intro immediateTypes immediateTyped (by
              intro branch member
              obtain ⟨delayedTypes, branchTyped, equality⟩ :=
                branchesTyped branch member
              exact ⟨delayedTypes,
                FuelIndexedRecursiveMatchingAtomsTyping.ofMatchingAtomsTyping
                  fuel branchTyped,
                equality⟩)
  | stable typed =>
      rcases evaluationAtomReducer_recursiveTotalTypedSafe
          (expressionTyping := expressionTyping) (eval := eval) evalSafe
          environmentTyped bindingsTyped typed with
        timeout | ⟨reduction, success, reductionTyped⟩
      · exact .inl timeout
      · refine .inr ⟨reduction, success, ?_⟩
        cases reductionTyped with
        | intro immediateTypes immediateTyped branchesTyped =>
            exact .intro immediateTypes immediateTyped (by
              intro branch member
              obtain ⟨delayedTypes, branchTyped, equality⟩ :=
                branchesTyped branch member
              exact ⟨delayedTypes,
                FuelIndexedRecursiveMatchingAtomsTyping.ofRecursiveTotal
                  fuel branchTyped,
                equality⟩)
  | user builtinMiss dispatch =>
      rename_i pattern matcherEnvironment original remaining target
      have atomEnvironmentTyped : EnvironmentTyping
          (bindings ++ environment) (bindingTypes ++ environmentTypes) :=
        bindingsTyped.appendEnvironment environmentTyped
      have classified := dispatch (bindings ++ environment)
        atomEnvironmentTyped
      generalize dispatchEq :
          dispatchMatcherClauses eval (bindings ++ environment)
            matcherEnvironment remaining pattern target = dispatchResult
        at classified
      cases classified with
      | timeout =>
          exact .inl (by
            unfold evaluationAtomReducer combineAtomReducers
            rw [builtinMiss]
            simp only [FuelResult.bind]
            simpa [reduceMatcherAtom] using
              congrArg (FuelResult.map clauseResultToAtomReduction) dispatchEq)
      | hit branchesTyped =>
          rename_i patterns recursiveBranches
          let reduction : AtomReduction := ⟨recursiveBranches, []⟩
          refine .inr ⟨reduction, ?_, ?_⟩
          · unfold evaluationAtomReducer combineAtomReducers
            rw [builtinMiss]
            simp only [FuelResult.bind]
            simpa [reduceMatcherAtom, reduction,
              clauseResultToAtomReduction] using
              congrArg (FuelResult.map clauseResultToAtomReduction) dispatchEq
          · exact .intro [] .nil (by
              intro branch member
              exact ⟨newBindings,
                by simpa using branchesTyped.recursive_member branch member,
                rfl⟩)

/-- A matching state whose work is safe for exactly `fuel` remaining state
visits. -/
inductive FuelIndexedRecursiveMatchingStateTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) : MatchingState → List Ty → Prop where
  | mk
      (environmentTyped : EnvironmentTyping environment environmentTypes)
      (bindingsTyped : ValueTypings bindings bindingTypes)
      (workTyped : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval
        fuel environmentTypes bindingTypes work futureBindings) :
      FuelIndexedRecursiveMatchingStateTyping expressionTyping eval fuel
        ⟨work, environment, bindings⟩ (bindingTypes ++ futureBindings)

def FuelIndexedRecursiveMatchingStatesTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (states : List MatchingState) (answerTypes : List Ty) : Prop :=
  ∀ state ∈ states,
    FuelIndexedRecursiveMatchingStateTyping expressionTyping eval fuel state
      answerTypes

theorem FuelIndexedRecursiveMatchingStateTyping.previous
    (typing : FuelIndexedRecursiveMatchingStateTyping expressionTyping eval
      (fuel + 1) state answerTypes) :
    FuelIndexedRecursiveMatchingStateTyping expressionTyping eval fuel state
      answerTypes := by
  cases typing with
  | mk environmentTyped bindingsTyped workTyped =>
      exact .mk environmentTyped bindingsTyped workTyped.previous

theorem FuelIndexedRecursiveMatchingStatesTyping.previous
    (typing : FuelIndexedRecursiveMatchingStatesTyping expressionTyping eval
      (fuel + 1) states answerTypes) :
    FuelIndexedRecursiveMatchingStatesTyping expressionTyping eval fuel states
      answerTypes := by
  intro state member
  exact (typing state member).previous

inductive FuelIndexedRecursiveSearchStepTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (answerTypes : List Ty) :
    SearchStep MatchingState (List Value) → Prop where
  | yield (answer : List Value)
      (answerTyped : ValueTypings answer answerTypes) :
      FuelIndexedRecursiveSearchStepTyping expressionTyping eval fuel
        answerTypes (.yield answer)
  | expand (successors : List MatchingState)
      (successorsTyped : ∀ state ∈ successors,
        FuelIndexedRecursiveMatchingStateTyping expressionTyping eval fuel
          state answerTypes) :
      FuelIndexedRecursiveSearchStepTyping expressionTyping eval fuel
        answerTypes (.expand successors)

private theorem stepMatchingState_fuelIndexedTypedSafe
    (reducerSafe : FuelIndexedRecursiveAtomReducerTypedSafe expressionTyping eval
      reduceAtom)
    (stateTyped : FuelIndexedRecursiveMatchingStateTyping expressionTyping eval
      (fuel + 1) state answerTypes) :
    (stepMatchingState reduceAtom state = .timeout) ∨
      ∃ observation,
        stepMatchingState reduceAtom state = .ok observation ∧
        FuelIndexedRecursiveSearchStepTyping expressionTyping eval fuel
          answerTypes observation := by
  cases stateTyped with
  | @mk environment environmentTypes bindings bindingTypes work futureBindings
      environmentTyped bindingsTyped workTyped =>
      cases workTyped with
      | nil =>
          exact .inr ⟨.yield bindings, rfl,
            .yield bindings (by simpa using bindingsTyped)⟩
      | cons headTyped tailTyped =>
          rename_i atom headBindings atoms tailBindings
          rcases reducerSafe environmentTyped bindingsTyped headTyped with
            timeout | ⟨reduction, reduced, reductionTyped⟩
          · exact .inl (by simp [stepMatchingState, timeout])
          · cases reductionTyped with
            | intro immediateTypes immediateTyped branchesTyped =>
              let successors : List MatchingState :=
                reduction.branches.map fun branch =>
                  ⟨branch ++ atoms, environment,
                    bindings ++ reduction.bindings⟩
              refine .inr ⟨.expand successors, ?_, .expand successors ?_⟩
              · simp [stepMatchingState, reduced,
                  MatchingState.successors, MatchingState.continueWith,
                  successors]
              · intro successor member
                simp only [successors] at member
                rcases List.mem_map.mp member with ⟨branch, branchMember, rfl⟩
                obtain ⟨delayedTypes, branchTyped, bindingEq⟩ :=
                  branchesTyped branch branchMember
                have branchAndTail :=
                  FuelIndexedRecursiveMatchingAtomsTyping.append fuel
                    branchTyped (by
                      simpa [List.append_assoc, bindingEq] using tailTyped)
                have newBindingsTyped := bindingsTyped.append immediateTyped
                have successorTyped :=
                  FuelIndexedRecursiveMatchingStateTyping.mk environmentTyped
                    newBindingsTyped branchAndTail
                have answerEq :
                    (bindingTypes ++ immediateTypes) ++
                        (delayedTypes ++ tailBindings) =
                      bindingTypes ++ (headBindings ++ tailBindings) := by
                  simp only [List.append_assoc]
                  rw [← List.append_assoc immediateTypes delayedTypes,
                    bindingEq]
                rw [answerEq] at successorTyped
                exact successorTyped

/-- The bounded search theorem follows the executable DFS fuel exactly: every
successor state and every remaining state is checked at the predecessor
index. -/
theorem depthFirstMatching_fuelIndexedTypedSafe
    (reducerSafe : FuelIndexedRecursiveAtomReducerTypedSafe expressionTyping eval
      reduceAtom)
    (statesTyped : FuelIndexedRecursiveMatchingStatesTyping expressionTyping eval
      fuel states answerTypes) :
    TypedMatchingSearchResult answerTypes
      (depthFirstFuel (stepMatchingState reduceAtom) fuel states) := by
  induction fuel generalizing states with
  | zero =>
      cases states with
      | nil => exact .inr ⟨[], rfl, by simp [MatchingAnswersTyping]⟩
      | cons state rest => exact .inl rfl
  | succ fuel induction =>
      cases states with
      | nil => exact .inr ⟨[], rfl, by simp [MatchingAnswersTyping]⟩
      | cons state rest =>
          have stateTyped := statesTyped state (by simp)
          have restTyped : FuelIndexedRecursiveMatchingStatesTyping
              expressionTyping eval fuel rest answerTypes := by
            intro candidate member
            exact (statesTyped candidate (by simp [member])).previous
          rcases stepMatchingState_fuelIndexedTypedSafe reducerSafe stateTyped with
            timeout | ⟨observation, stepped, observationTyped⟩
          · exact .inl (by simp [depthFirstFuel, timeout])
          · cases observationTyped with
            | yield answer answerTyped =>
                rcases induction restTyped with tailTimeout |
                  ⟨answers, searched, answersTyped⟩
                · exact .inl (by
                    simp [depthFirstFuel, stepped, tailTimeout,
                      FuelResult.map])
                · exact .inr ⟨answer :: answers, by
                    simp [depthFirstFuel, stepped, searched,
                      FuelResult.map], by
                    intro candidate member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact answerTyped
                    · exact answersTyped candidate member⟩
            | expand successors successorsTyped =>
                have nextTyped : FuelIndexedRecursiveMatchingStatesTyping
                    expressionTyping eval fuel (successors ++ rest)
                    answerTypes := by
                  intro candidate member
                  rcases List.mem_append.mp member with inSuccessors | inRest
                  · exact successorsTyped candidate inSuccessors
                  · exact restTyped candidate inRest
                rcases induction nextTyped with nextTimeout |
                  ⟨answers, searched, answersTyped⟩
                · exact .inl (by
                    simp [depthFirstFuel, stepped, nextTimeout])
                · exact .inr ⟨answers, by
                    simp [depthFirstFuel, stepped, searched], answersTyped⟩

/-- Direct endpoint for one already evaluated target/matcher pair. -/
theorem searchPatternFuel_fuelIndexedTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (environmentTyped : EnvironmentTyping environment environmentTypes)
    (workTyped : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval
      fuel environmentTypes [] [⟨pattern, matcher, target⟩] bindingTypes) :
    TypedMatchingSearchResult bindingTypes
      (searchPatternFuel eval fuel environment pattern matcher target) := by
  unfold searchPatternFuel
  apply depthFirstMatching_fuelIndexedTypedSafe
    (expressionTyping := expressionTyping) (eval := eval)
    (evaluationAtomReducer_fuelIndexedTypedSafe
      (expressionTyping := expressionTyping) (eval := eval) evalSafe)
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact .mk environmentTyped .nil (by simpa using workTyped)

namespace FuelIndexedRecursiveMatchingAtomsTyping

theorem singleZero :
    FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval 0
      environmentTypes [] [atom] bindingTypes :=
  .zero (by simp)

theorem singletonOfAtom
    (typing : FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval
      (fuel + 1) environmentTypes bindingTypes atom newBindings) :
    FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval (fuel + 1)
      environmentTypes bindingTypes [atom] newBindings := by
  simpa using
    (FuelIndexedRecursiveMatchingAtomsTyping.cons typing
      (FuelIndexedRecursiveMatchingAtomsTyping.nil
        (fuel := fuel) (bindingTypes := bindingTypes ++ newBindings)))

theorem singleOfAtom
    (typing : FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval
      (fuel + 1) environmentTypes [] atom bindingTypes) :
    FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval (fuel + 1)
      environmentTypes [] [atom] bindingTypes := by
  exact singletonOfAtom typing

end FuelIndexedRecursiveMatchingAtomsTyping

/-- A bounded recursive initial-work certificate supplies exactly the search
premise consumed by value-indexed `matchAll`.  Successful ordinary answer
typing is embedded into the total-plain value layer pointwise. -/
theorem evaluatedPatternSearchSafe_of_fuelIndexed
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping (evalFuel fuel))
    (environmentTyped : EnvironmentTyping environment environmentTypes)
    (work : ∀ targetValue matcherValue,
      evalFuel fuel environment targetExpression = .ok targetValue →
      evalFuel fuel environment matcherExpression = .ok matcherValue →
      FuelIndexedRecursiveMatchingAtomsTyping expressionTyping (evalFuel fuel)
        fuel environmentTypes [] [⟨pattern, matcherValue, targetValue⟩]
        bindingTypes) :
    EvaluatedPatternSearchSafe fuel environment targetExpression
      matcherExpression pattern bindingTypes := by
  intro targetValue matcherValue targetSuccess matcherSuccess
  rcases searchPatternFuel_fuelIndexedTypedSafe
      (expressionTyping := expressionTyping) (eval := evalFuel fuel)
      (fuel := fuel) (environment := environment)
      (environmentTypes := environmentTypes) (pattern := pattern)
      (matcher := matcherValue) (target := targetValue)
      (bindingTypes := bindingTypes) evalSafe environmentTyped
      (work targetValue matcherValue targetSuccess matcherSuccess) with
    timeout | ⟨answers, success, answersTyped⟩
  · exact .inl timeout
  · exact .inr ⟨answers, success, by
      intro bindings member
      exact TotalPlainValueTypings.ofTotal
        (TotalValueTypings.ofValueTypings
          (answersTyped bindings member))⟩

/-- At search index zero a nonempty initial worklist times out before the atom
is inspected, so no atom or matcher-closure premise is needed. -/
theorem searchPatternFuel_zero_fuelIndexedTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (environmentTyped : EnvironmentTyping environment environmentTypes) :
    TypedMatchingSearchResult bindingTypes
      (searchPatternFuel eval 0 environment pattern matcher target) := by
  exact searchPatternFuel_fuelIndexedTypedSafe
    (expressionTyping := expressionTyping) (eval := eval)
    evalSafe environmentTyped
    (FuelIndexedRecursiveMatchingAtomsTyping.singleZero
      (atom := ⟨pattern, matcher, target⟩))

/-- Exact-dispatch-to-search endpoint for one user matcher at a positive DFS
bound.  The recursive closure's captured environment is absent: callers
classify the real dispatch result at the predecessor search index. -/
theorem searchPatternFuel_user_fuelIndexedTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (environmentTyped : EnvironmentTyping environment environmentTypes)
    (builtinMiss : ∀ atomEnvironment,
      reduceBuiltinAtom eval atomEnvironment
        ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩ =
          .ok .miss)
    (dispatch : ∀ atomEnvironment,
      EnvironmentTyping atomEnvironment environmentTypes →
      FuelIndexedPatternDispatchTyping expressionTyping eval searchPredecessor
        environmentTypes [] bindingTypes
        (dispatchMatcherClauses eval atomEnvironment matcherEnvironment
          remaining pattern target)) :
    TypedMatchingSearchResult bindingTypes
      (searchPatternFuel eval (searchPredecessor + 1) environment pattern
        (.matcherV matcherEnvironment original remaining) target) := by
  apply searchPatternFuel_fuelIndexedTypedSafe
    (expressionTyping := expressionTyping) (eval := eval)
    evalSafe environmentTyped
  exact FuelIndexedRecursiveMatchingAtomsTyping.singleOfAtom
    (.user builtinMiss (by
      intro atomEnvironment atomEnvironmentTyped
      simpa using dispatch atomEnvironment atomEnvironmentTyped))

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

end TypePM.Source.MatcherTyping

namespace TypePM.Runtime.RecursiveTotalMatchingAtomsTyping

/-- Ordinary built-in work embeds into the unbounded recursive family. -/
theorem ofMatchingAtomsTyping
    (typing : MatchingAtomsTyping expressionTyping environmentTypes
      bindingTypes atoms newBindings) :
    RecursiveTotalMatchingAtomsTyping expressionTyping eval environmentTypes
      bindingTypes atoms newBindings := by
  induction atoms generalizing bindingTypes newBindings with
  | nil =>
      cases typing
      exact .nil
  | cons atom atoms induction =>
      cases typing with
      | cons atom atoms headBindings tailBindings head tail =>
          exact .cons (.builtin head) (induction tail)

end TypePM.Runtime.RecursiveTotalMatchingAtomsTyping

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- Concrete built-in matcher shapes paired with the exact patterns stored in
one delegated branch. -/
inductive PatternIndexedDirectMatchingAtomsShape :
    List MatchingAtom → List Pattern → Prop where
  | nil : PatternIndexedDirectMatchingAtomsShape [] []
  | cons
      (head : DirectPatternMatcherShape pattern matcher)
      (tail : PatternIndexedDirectMatchingAtomsShape atoms patterns) :
      PatternIndexedDirectMatchingAtomsShape
        (⟨pattern, matcher, target⟩ :: atoms) (pattern :: patterns)

/-- List-of-branches form of the exact direct matcher-shape evidence. -/
inductive PatternIndexedDirectMatchingBranchesShape
    (patterns : List Pattern) : MatchingBranches → Prop where
  | nil : PatternIndexedDirectMatchingBranchesShape patterns []
  | cons
      (head : PatternIndexedDirectMatchingAtomsShape branch patterns)
      (tail : PatternIndexedDirectMatchingBranchesShape patterns branches) :
      PatternIndexedDirectMatchingBranchesShape patterns (branch :: branches)

namespace PatternIndexedDirectMatchingBranchesShape

theorem member
    (typing : PatternIndexedDirectMatchingBranchesShape patterns branches) :
    ∀ branch ∈ branches,
      PatternIndexedDirectMatchingAtomsShape branch patterns := by
  induction branches with
  | nil => simp
  | cons head tail induction =>
      cases typing with
      | cons headShape tailShapes =>
          intro branch member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact headShape
          · exact induction tailShapes branch member

end PatternIndexedDirectMatchingBranchesShape

namespace PatternIndexedDelegatedMatchingBranchesTyping

theorem indexed_member
    (typing : PatternIndexedDelegatedMatchingBranchesTyping patterns holes
      branches) :
    ∀ branch ∈ branches,
      PatternIndexedDelegatedMatchingAtomsTyping branch patterns holes := by
  induction branches with
  | nil => simp
  | cons head tail induction =>
      cases typing with
      | cons headIndexed tailIndexed =>
          intro branch member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact headIndexed
          · exact induction tailIndexed branch member

end PatternIndexedDelegatedMatchingBranchesTyping

namespace PatternIndexedDelegatedMatchingAtomsTyping

theorem exact_patterns
    (typing : PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes) :
    atoms.map (fun atom => atom.pattern) = patterns := by
  induction atoms generalizing patterns holes with
  | nil =>
      cases typing
      rfl
  | cons atom atoms induction =>
      cases typing with
      | cons matcher target tail => simp [induction tail]

end PatternIndexedDelegatedMatchingAtomsTyping

/-- In the direct fragment, solved pattern binding behavior, exact delegated
value typing, and concrete matcher shapes determine ordinary atom typing. -/
theorem PatternIndexedDelegatedMatchingAtomsTyping.toDirectMatchingAtomsTyping
    (binds : PatternsBind
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes bindingTypes patterns (Dual.targets holes) newBindings)
    (indexed : PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes)
    (shapes : PatternIndexedDirectMatchingAtomsShape atoms patterns) :
    MatchingAtomsTyping
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes bindingTypes atoms newBindings := by
  induction patterns generalizing atoms holes bindingTypes newBindings with
  | nil =>
      cases indexed
      cases shapes
      cases binds
      exact .nil
  | cons pattern patterns induction =>
      cases indexed with
      | cons matcherTyped targetTyped indexedTail =>
          cases shapes with
          | cons headShape tailShapes =>
              cases binds with
              | cons headBinds tailBinds =>
                  exact .cons _ _ _ _
                    (TypePM.Source.MatcherTyping.PatternBinds.toDirectMatchingAtomTyping
                      headBinds headShape targetTyped)
                    (induction tailBinds indexedTail tailShapes)

/-- Direct M4 branches also inhabit the existing unbounded recursive dispatch
judgment.  This endpoint is intentionally limited to built-in matcher shapes;
it does not assign old environment typing to a recursive matcher closure. -/
theorem PatternIndexedDelegatedMatchingBranchesTyping.toDirectPatternIndexedRecursiveDispatch
    (binds : PatternsBind
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes bindingTypes patterns (Dual.targets holes) newBindings)
    (indexed : PatternIndexedDelegatedMatchingBranchesTyping
      patterns holes branches)
    (shapes : PatternIndexedDirectMatchingBranchesShape patterns branches) :
    PatternIndexedRecursiveDispatchTyping
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      eval environmentTypes bindingTypes newBindings (.ok (.hit branches)) := by
  exact .hit
    (fun branch member =>
      (indexed.indexed_member branch member).exact_patterns)
    (fun branch member =>
      TypePM.Runtime.RecursiveTotalMatchingAtomsTyping.ofMatchingAtomsTyping
        ((indexed.indexed_member branch member).toDirectMatchingAtomsTyping
          binds (shapes.member branch member)))

/-- Exact source-indexed branches used only at the non-recursive M4 boundary.
The main fuel-indexed runtime relation erases the old delegated `ValueTyping`
evidence after extracting source-pattern equality. -/
inductive M4FuelIndexedRecursiveBranchesTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (environmentTypes bindingTypes newBindings : List Ty) :
    MatchingBranches → Prop where
  | nil : M4FuelIndexedRecursiveBranchesTyping expressionTyping eval fuel
      environmentTypes bindingTypes newBindings []
  | cons
      (recursive : FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval
        fuel environmentTypes bindingTypes branch newBindings)
      (tail : M4FuelIndexedRecursiveBranchesTyping expressionTyping eval fuel
        environmentTypes bindingTypes newBindings branches) :
      M4FuelIndexedRecursiveBranchesTyping expressionTyping eval fuel
        environmentTypes bindingTypes newBindings (branch :: branches)

namespace PatternIndexedDelegatedMatchingAtomsTyping

theorem patterns_eq
    (typing : PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes) :
    atoms.map (fun atom => atom.pattern) = patterns := by
  induction typing with
  | nil => rfl
  | cons matcher target tail induction => simp [induction]

end PatternIndexedDelegatedMatchingAtomsTyping

namespace M4FuelIndexedRecursiveBranchesTyping

/-- Erase old delegated value typing after retaining the exact source pattern
list and bounded recursive work. -/
theorem toFuelIndexedPatternBranches
    (indexed : PatternIndexedDelegatedMatchingBranchesTyping
      patterns holes branches)
    (typing : M4FuelIndexedRecursiveBranchesTyping expressionTyping eval fuel
      environmentTypes bindingTypes newBindings branches) :
    FuelIndexedPatternBranchesTyping expressionTyping eval fuel
      environmentTypes bindingTypes newBindings patterns branches := by
  induction branches with
  | nil => exact .nil
  | cons branch branches induction =>
      cases indexed with
      | cons indexedHead indexedTail =>
      cases typing with
      | cons recursive tail =>
          exact .cons indexedHead.patterns_eq recursive
            (induction indexedTail tail)

end M4FuelIndexedRecursiveBranchesTyping

/-- A successful pattern-indexed source result plus exact bounded branch work
becomes the main recursive dispatch result. -/
theorem PatternIndexedMatcherClauseResultTyping.toFuelIndexedDispatchTyping
    (source : PatternIndexedMatcherClauseResultTyping
      (.hit branches : DispatchResult MatchingBranches))
    (recursive : M4FuelIndexedRecursiveBranchesTyping expressionTyping eval fuel
      environmentTypes bindingTypes newBindings branches) :
    FuelIndexedPatternDispatchTyping expressionTyping eval fuel environmentTypes
      bindingTypes newBindings (.ok (.hit branches)) := by
  cases source with
  | hit indexed =>
      exact .hit (recursive.toFuelIndexedPatternBranches indexed)

/-- All-direct returned branches are converted structurally.  M4 supplies the
binding behavior, delegated dispatch supplies the exact targets, and the
shape certificate selects the concrete built-in reducer path. -/
theorem PatternIndexedDelegatedMatchingBranchesTyping.toDirectFuelIndexed
    (binds : PatternsBind
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes bindingTypes patterns (Dual.targets holes) newBindings)
    (indexed : PatternIndexedDelegatedMatchingBranchesTyping
      patterns holes branches)
    (shapes : PatternIndexedDirectMatchingBranchesShape patterns branches) :
    M4FuelIndexedRecursiveBranchesTyping
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      eval fuel environmentTypes bindingTypes newBindings branches := by
  induction branches with
  | nil => exact .nil
  | cons branch branches induction =>
      cases indexed with
      | cons indexedHead indexedTail =>
          cases shapes with
          | cons shapeHead shapeTail =>
              exact .cons
                (FuelIndexedRecursiveMatchingAtomsTyping.ofMatchingAtomsTyping
                  fuel
                  (indexedHead.toDirectMatchingAtomsTyping binds shapeHead))
                (induction indexedTail shapeTail)

/-- Solved relational M4 elaboration automatically supplies bounded recursive
work for a dispatch whose returned patterns all lie in the direct built-in
fragment. -/
theorem PatternsElaborate.toDirectFuelIndexedBranches
    (elaboration : PatternsElaborate Paper1FrozenSignature.signature context
      arguments patterns bindings supply generated next)
    (supported : DirectRuntimePatternsSupported patterns)
    (semantic : GeneratedPatternsRuntimeSolution generated solution)
    (contextCompatible :
      MonomorphicContextCompatible context environmentTypes solution)
    (indexed : PatternIndexedDelegatedMatchingBranchesTyping patterns
      (generated.duals.map (RuntimeDual.apply solution)) branches)
    (shapes : PatternIndexedDirectMatchingBranchesShape patterns branches) :
    ∃ newBindings,
      M4FuelIndexedRecursiveBranchesTyping
        (fun runtimeContext expression target =>
          RuntimeTyping expression target runtimeContext)
        eval fuel environmentTypes (Ty.applyList solution bindings)
        newBindings branches ∧
      Ty.applyList solution generated.bindings =
        Ty.applyList solution bindings ++ newBindings := by
  obtain ⟨newBindings, binds, bindingsEq⟩ :=
    TypePM.Source.MatcherTyping.PatternsElaborate.toDirectRuntimePatternsBind
      elaboration supported semantic contextCompatible
  have binds' : PatternsBind
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes (Ty.applyList solution bindings) patterns
      (Dual.targets (generated.duals.map (RuntimeDual.apply solution)))
      newBindings := by
    simpa using binds
  exact ⟨newBindings,
    indexed.toDirectFuelIndexed binds' shapes,
    bindingsEq⟩

/-- Unbounded direct-fragment counterpart.  Solved M4 pattern elaboration and
the exact successful branch evidence construct `RecursiveTotalMatchingAtomsTyping`
and hence the existing `PatternIndexedRecursiveDispatchTyping` judgment. -/
theorem PatternsElaborate.toDirectPatternIndexedRecursiveDispatch
    (elaboration : PatternsElaborate Paper1FrozenSignature.signature context
      arguments patterns bindings supply generated next)
    (supported : DirectRuntimePatternsSupported patterns)
    (semantic : GeneratedPatternsRuntimeSolution generated solution)
    (contextCompatible :
      MonomorphicContextCompatible context environmentTypes solution)
    (indexed : PatternIndexedDelegatedMatchingBranchesTyping patterns
      (generated.duals.map (RuntimeDual.apply solution)) branches)
    (shapes : PatternIndexedDirectMatchingBranchesShape patterns branches) :
    ∃ newBindings,
      PatternIndexedRecursiveDispatchTyping
        (fun runtimeContext expression target =>
          RuntimeTyping expression target runtimeContext)
        eval environmentTypes (Ty.applyList solution bindings) newBindings
        (.ok (.hit branches)) ∧
      Ty.applyList solution generated.bindings =
        Ty.applyList solution bindings ++ newBindings := by
  obtain ⟨newBindings, binds, bindingsEq⟩ :=
    TypePM.Source.MatcherTyping.PatternsElaborate.toDirectRuntimePatternsBind
      elaboration supported semantic contextCompatible
  have binds' : PatternsBind
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes (Ty.applyList solution bindings) patterns
      (Dual.targets (generated.duals.map (RuntimeDual.apply solution)))
      newBindings := by
    simpa using binds
  exact ⟨newBindings,
    indexed.toDirectPatternIndexedRecursiveDispatch binds' shapes,
    bindingsEq⟩

/-- Non-recursive M4 corollary.  The pre-existing dispatcher supplies timeout
or exact source-indexed branches; the remaining premise certifies recursive
work only for a branch list returned by that same dispatch.  This theorem
retains the old matcher-environment premise because the invoked M4 dispatcher
does.  Recursive closures should use `FuelIndexedRecursiveMatchingAtomTyping.user`
directly and do not pass through this corollary. -/
theorem MatcherLiteralTotalInputElaboratesUsing.dispatchFuelIndexedSafe_of_m4Fuel
    (input : MatcherLiteralTotalInputElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature elaborationFuel)
      expressionTyping solution atomEnvironmentTypes pattern context clauses
      supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution)
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target
      ((Ty.var ⟨supply.ty⟩).apply solution))
    (recursiveWork : ∀ {branches},
      dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
          pattern target = .ok (.hit branches) →
      M4FuelIndexedRecursiveBranchesTyping expressionTyping eval searchFuel
        runtimeEnvironmentTypes bindingTypes newBindings branches) :
    FuelIndexedPatternDispatchTyping expressionTyping eval searchFuel
      runtimeEnvironmentTypes bindingTypes newBindings
      (dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
        pattern target) := by
  have finalCatchAll : FinalCatchAll clauses := by
    cases input with
    | mk checked clausesElaboration => exact checked.finalCatchAll
  rcases input.dispatchPatternIndexedSafe_of_m4Fuel bridge semantic
      contextCompatible evalSafe atomEnvironmentTyped matcherEnvironmentTyped
      targetTyped with timeout | ⟨result, dispatched, source⟩
  · rw [timeout]
    exact .timeout
  · cases source with
    | miss =>
        exact False.elim
          (finalCatchAll_dispatch_ne_miss finalCatchAll dispatched)
    | hit indexed =>
        rw [dispatched]
        exact .hit
          ((recursiveWork dispatched).toFuelIndexedPatternBranches indexed)

end TypePM.Source.MatcherTyping
