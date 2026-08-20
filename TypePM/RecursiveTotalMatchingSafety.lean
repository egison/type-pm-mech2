import TypePM.CommonFuelSafety

/-!
# Callback-indexed recursive user-matcher safety

`TotalMatchingAtomTyping` is the certificate used by the ordinary common-fuel
evaluator.  Its user-matcher constructor is intentionally indexed by all fuel
bounds.  This parallel judgment instead fixes the evaluator callback in its
index.  It can therefore retain a recursively typed matcher closure and
certify exactly the branches returned by that callback, without assuming that
unrelated evaluators produce the same matcher values or branches.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Exact operational certificate for a terminal zero-hole user-matcher atom.
The real reducer must time out, return no branches, or return the unique empty
branch.  In the two successful cases there are zero immediate bindings and
zero recursive atoms, so preservation is definitionally trivial.

This is deliberately *not* a replacement for typed recursive matcher
closures: it cannot certify any atom that delegates a pattern or returns a
binding. -/
def ZeroHoleTerminalUserAtomReduction
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (atom : MatchingAtom) : Prop :=
  ∀ atomEnvironment,
    evaluationAtomReducer eval atomEnvironment atom = .timeout ∨
      evaluationAtomReducer eval atomEnvironment atom =
        .ok (.hit ⟨[], []⟩) ∨
      evaluationAtomReducer eval atomEnvironment atom =
        .ok (.hit ⟨[[]], []⟩)

mutual

  /-- One atom whose recursive user-matcher branches are tied to the exact
  evaluator callback used by dispatch. -/
  inductive RecursiveTotalMatchingAtomTyping
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      List Ty → List Ty → MatchingAtom → List Ty → Prop where
    | builtin
        (typed : MatchingAtomTyping expressionTyping environmentTypes
          bindingTypes atom newBindings) :
        RecursiveTotalMatchingAtomTyping expressionTyping eval
          environmentTypes bindingTypes atom newBindings
    | user
        (builtinMiss : ∀ atomEnvironment,
          reduceBuiltinAtom eval atomEnvironment
            ⟨pattern, .matcherV matcherEnvironment original remaining,
              target⟩ = .ok .miss)
        (matcherEnvironmentTyped :
          EnvironmentTyping matcherEnvironment definitionTypes)
        (targetTyped : ValueTyping target matcherTarget)
        (clausesTyped : TotalRuntimeMatcherClausesInputTyping expressionTyping
          (bindingTypes ++ environmentTypes) definitionTypes matcherTarget
          pattern remaining)
        (finalCatchAll : MatcherTyping.FinalCatchAll remaining)
        (branches : ∀ (atomEnvironment : ValueEnvironment)
            {holes recursiveBranches},
          dispatchMatcherClauses eval atomEnvironment matcherEnvironment
              remaining pattern target = .ok (.hit recursiveBranches) →
          DelegatedMatchingBranchesTyping holes recursiveBranches →
          ∀ branch ∈ recursiveBranches,
            RecursiveTotalMatchingAtomsTyping expressionTyping eval
              environmentTypes bindingTypes branch newBindings) :
        RecursiveTotalMatchingAtomTyping expressionTyping eval
          environmentTypes bindingTypes
          ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩
          newBindings
    /-- A user matcher whose progress and recursive branch typing are tied to
    the exact pattern-indexed dispatch result.  Unlike `user`, this low-level
    certificate does not require the older `EnvironmentTyping` for a
    recursive matcher closure.  It instead requires each actual typed
    dispatch either to time out or to return pattern-indexed branches, all of
    which are recursively typed.  A separate source-to-runtime theorem must
    still establish where that pattern index came from. -/
    | patternIndexedUser
        (builtinMiss : ∀ atomEnvironment,
          reduceBuiltinAtom eval atomEnvironment
            ⟨pattern, .matcherV matcherEnvironment original remaining,
              target⟩ = .ok .miss)
        (dispatch : ∀ atomEnvironment,
          EnvironmentTyping atomEnvironment
            (bindingTypes ++ environmentTypes) →
          PatternIndexedRecursiveDispatchTyping expressionTyping eval
            environmentTypes bindingTypes newBindings
            (dispatchMatcherClauses eval atomEnvironment matcherEnvironment
              remaining pattern target)) :
        RecursiveTotalMatchingAtomTyping expressionTyping eval
          environmentTypes bindingTypes
          ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩
          newBindings
    /-- Terminal zero-hole operational exception.  Type preservation is
    trivial because neither successful result contains a binding or a
    recursive atom.  This constructor does not type the matcher closure and
    is not part of the general recursive-closure bridge. -/
    | zeroHoleTerminalUser
        (reduction : ZeroHoleTerminalUserAtomReduction eval atom) :
        RecursiveTotalMatchingAtomTyping expressionTyping eval
          environmentTypes bindingTypes atom []

  /-- Pending atoms typed from left to right for one fixed evaluator. -/
  inductive RecursiveTotalMatchingAtomsTyping
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      List Ty → List Ty → List MatchingAtom → List Ty → Prop where
    | nil : RecursiveTotalMatchingAtomsTyping expressionTyping eval
        environmentTypes bindingTypes [] []
    | cons
        (head : RecursiveTotalMatchingAtomTyping expressionTyping eval
          environmentTypes bindingTypes atom headBindings)
        (tail : RecursiveTotalMatchingAtomsTyping expressionTyping eval
          environmentTypes (bindingTypes ++ headBindings) atoms tailBindings) :
        RecursiveTotalMatchingAtomsTyping expressionTyping eval
          environmentTypes bindingTypes (atom :: atoms)
          (headBindings ++ tailBindings)

  /-- Exact timeout-or-hit classification for a user-matcher dispatch.  A hit
  carries pattern evidence for, and recursively types, every branch returned
  by that same dispatch.  This judgment does not by itself derive that pattern
  evidence from the dispatch input.  Making it an indexed member of the
  mutual block avoids hiding recursive evidence inside an untracked
  existential. -/
  inductive PatternIndexedRecursiveDispatchTyping
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      (environmentTypes bindingTypes newBindings : List Ty) →
      FuelResult (DispatchResult MatchingBranches) → Prop where
    | timeout : PatternIndexedRecursiveDispatchTyping expressionTyping eval
        environmentTypes bindingTypes newBindings .timeout
    | hit
        (patternsPreserved : ∀ branch ∈ recursiveBranches,
          branch.map (fun atom => atom.pattern) = patterns)
        (branches : ∀ branch ∈ recursiveBranches,
          RecursiveTotalMatchingAtomsTyping expressionTyping eval
            environmentTypes bindingTypes branch newBindings) :
        PatternIndexedRecursiveDispatchTyping expressionTyping eval
          environmentTypes bindingTypes newBindings
          (.ok (.hit recursiveBranches))

end

namespace RecursiveTotalMatchingAtomsTyping

theorem append :
    ∀ {bindingTypes leftAtoms leftBindings},
      RecursiveTotalMatchingAtomsTyping expressionTyping eval environmentTypes
        bindingTypes leftAtoms leftBindings →
      ∀ {rightAtoms rightBindings},
        RecursiveTotalMatchingAtomsTyping expressionTyping eval environmentTypes
          (bindingTypes ++ leftBindings) rightAtoms rightBindings →
        RecursiveTotalMatchingAtomsTyping expressionTyping eval environmentTypes
          bindingTypes (leftAtoms ++ rightAtoms)
          (leftBindings ++ rightBindings)
  | _, _, _, .nil, _, _, right => by simpa using right
  | bindingTypes, _, _,
      @RecursiveTotalMatchingAtomsTyping.cons _ _ _ _ atom headBindings
        atoms tailBindings head tail,
      rightAtoms, rightBindings, right => by
      have right' : RecursiveTotalMatchingAtomsTyping expressionTyping eval
          environmentTypes ((bindingTypes ++ headBindings) ++ tailBindings)
          rightAtoms rightBindings := by
        simpa [List.append_assoc] using right
      simpa [List.append_assoc] using
        RecursiveTotalMatchingAtomsTyping.cons head (tail.append right')

end RecursiveTotalMatchingAtomsTyping

/-- Preservation certificate for a callback-indexed atom reduction. -/
inductive RecursiveTotalAtomReductionTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (environmentTypes bindingTypes expectedBindings : List Ty)
    (reduction : AtomReduction) : Prop where
  | intro
      (immediateTypes : List Ty)
      (immediateTyped : ValueTypings reduction.bindings immediateTypes)
      (branchesTyped : ∀ branch ∈ reduction.branches,
        ∃ delayedTypes,
          RecursiveTotalMatchingAtomsTyping expressionTyping eval
            environmentTypes (bindingTypes ++ immediateTypes)
            branch delayedTypes ∧
          immediateTypes ++ delayedTypes = expectedBindings) :
      RecursiveTotalAtomReductionTyping expressionTyping eval environmentTypes
        bindingTypes expectedBindings reduction

/-- Local progress and preservation for the combined reducer using the same
callback stored in the atom certificate. -/
def RecursiveTotalAtomReducerTypedSafe
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (reduceAtom : AtomReducer) : Prop :=
  ∀ {environmentTypes bindingTypes environment bindings atom newBindings},
    EnvironmentTyping environment environmentTypes →
    ValueTypings bindings bindingTypes →
    RecursiveTotalMatchingAtomTyping expressionTyping eval environmentTypes
      bindingTypes atom newBindings →
    reduceAtom (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) ∧
        RecursiveTotalAtomReductionTyping expressionTyping eval
          environmentTypes bindingTypes newBindings reduction

private theorem builtinReduction_recursiveTotalTyping
    (typing : AtomReductionTyping expressionTyping environmentTypes
      bindingTypes expectedBindings reduction) :
    RecursiveTotalAtomReductionTyping expressionTyping eval environmentTypes
      bindingTypes expectedBindings reduction := by
  cases typing with
  | intro immediateTypes immediateTyped branchesTyped =>
      exact .intro immediateTypes immediateTyped (by
        intro branch member
        obtain ⟨delayedTypes, branchTyped, equality⟩ :=
          branchesTyped branch member
        exact ⟨delayedTypes, recursiveOfBuiltin branchTyped, equality⟩)
where
  recursiveOfBuiltin :
      ∀ {bindingTypes atoms newBindings},
        MatchingAtomsTyping expressionTyping environmentTypes bindingTypes
          atoms newBindings →
        RecursiveTotalMatchingAtomsTyping expressionTyping eval environmentTypes
          bindingTypes atoms newBindings
    | _, _, _, .nil => .nil
    | _, _, _, .cons _ _ _ _ head tail =>
        .cons (.builtin head) (recursiveOfBuiltin tail)

/-- Callback-parametric reducer safety.  The same callback is used for
built-in value patterns, user-clause bodies, next matchers, and recursively
created atoms. -/
theorem evaluationAtomReducer_recursiveTotalTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval) :
    RecursiveTotalAtomReducerTypedSafe expressionTyping eval
      (evaluationAtomReducer eval) := by
  intro environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | builtin typed =>
      rcases reduceBuiltinAtom_typedSafe expressionTyping eval evalSafe
          environmentTyped bindingsTyped typed with
        timeout | ⟨reduction, success, reductionTyped⟩
      · exact .inl (by
          simp [evaluationAtomReducer, combineAtomReducers, timeout])
      · exact .inr ⟨reduction, by
          simp [evaluationAtomReducer, combineAtomReducers, success],
          builtinReduction_recursiveTotalTyping reductionTyped⟩
  | user builtinMiss matcherEnvironmentTyped targetTyped clausesTyped
      finalCatchAll branches =>
      rename_i pattern matcherEnvironment original remaining target
        definitionTypes matcherTarget
      have atomEnvironmentTyped : EnvironmentTyping
          (bindings ++ environment) (bindingTypes ++ environmentTypes) :=
        bindingsTyped.appendEnvironment environmentTyped
      rcases dispatchMatcherClauses_totalTypedSafe
          (expressionTyping := expressionTyping) (eval := eval) evalSafe
          atomEnvironmentTyped matcherEnvironmentTyped targetTyped clausesTyped
        with timeout | ⟨result, dispatched, resultTyped⟩
      · exact .inl (by
          unfold evaluationAtomReducer combineAtomReducers
          rw [builtinMiss]
          simp only [FuelResult.bind]
          simpa [reduceMatcherAtom] using
            congrArg (FuelResult.map clauseResultToAtomReduction) timeout)
      · cases resultTyped with
        | miss =>
            exact False.elim
              (finalCatchAll_dispatch_ne_miss finalCatchAll dispatched)
        | @hit holes recursiveBranches recursiveBranchesTyped =>
            let reduction : AtomReduction := ⟨recursiveBranches, []⟩
            refine .inr ⟨reduction, ?_, ?_⟩
            · unfold evaluationAtomReducer combineAtomReducers
              rw [builtinMiss]
              simp only [FuelResult.bind]
              simpa [reduceMatcherAtom, reduction,
                clauseResultToAtomReduction] using
                congrArg (FuelResult.map clauseResultToAtomReduction) dispatched
            · exact .intro [] .nil (by
                intro branch member
                exact ⟨newBindings,
                  by simpa using
                    (branches (bindings ++ environment) dispatched
                      recursiveBranchesTyped branch member),
                  rfl⟩)
  | patternIndexedUser builtinMiss dispatch =>
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
      | hit patternsPreserved branchesTyped =>
        rename_i recursiveBranches patterns
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
              by simpa using
                (branchesTyped branch member),
              rfl⟩)
  | zeroHoleTerminalUser exactReduction =>
      rcases exactReduction (bindings ++ environment) with timeout |
        noBranches | oneEmptyBranch
      · exact .inl timeout
      · exact .inr ⟨⟨[], []⟩, noBranches,
          .intro [] ValueTypings.nil (by simp)⟩
      · exact .inr ⟨⟨[[]], []⟩, oneEmptyBranch,
          .intro [] ValueTypings.nil (by
            intro branch member
            simp only [List.mem_singleton] at member
            subst branch
            exact ⟨[], RecursiveTotalMatchingAtomsTyping.nil, rfl⟩)⟩

/-- A callback-indexed recursive matching state has one answer type list. -/
inductive RecursiveTotalMatchingStateTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
    MatchingState → List Ty → Prop where
  | mk
      (environmentTyped : EnvironmentTyping environment environmentTypes)
      (bindingsTyped : ValueTypings bindings bindingTypes)
      (workTyped : RecursiveTotalMatchingAtomsTyping expressionTyping eval
        environmentTypes bindingTypes work futureBindings) :
      RecursiveTotalMatchingStateTyping expressionTyping eval
        ⟨work, environment, bindings⟩ (bindingTypes ++ futureBindings)

def RecursiveTotalMatchingStatesTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (states : List MatchingState) (answerTypes : List Ty) : Prop :=
  ∀ state ∈ states,
    RecursiveTotalMatchingStateTyping expressionTyping eval state answerTypes

inductive RecursiveTotalSearchStepTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (answerTypes : List Ty) :
    SearchStep MatchingState (List Value) → Prop where
  | yield (answer : List Value)
      (answerTyped : ValueTypings answer answerTypes) :
      RecursiveTotalSearchStepTyping expressionTyping eval answerTypes
        (.yield answer)
  | expand (successors : List MatchingState)
      (successorsTyped : ∀ state ∈ successors,
        RecursiveTotalMatchingStateTyping expressionTyping eval state
          answerTypes) :
      RecursiveTotalSearchStepTyping expressionTyping eval answerTypes
        (.expand successors)

def RecursiveTotalTypedSearchStepResult
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (answerTypes : List Ty)
    (result : FuelResult (SearchStep MatchingState (List Value))) : Prop :=
  result = .timeout ∨
    ∃ observation, result = .ok observation ∧
      RecursiveTotalSearchStepTyping expressionTyping eval answerTypes
        observation

private theorem stepMatchingState_recursiveTotalTypedSafe
    (reducerSafe : RecursiveTotalAtomReducerTypedSafe expressionTyping eval
      reduceAtom)
    (stateTyped : RecursiveTotalMatchingStateTyping expressionTyping eval
      state answerTypes) :
    RecursiveTotalTypedSearchStepResult expressionTyping eval answerTypes
      (stepMatchingState reduceAtom state) := by
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
                have branchAndTail := branchTyped.append (by
                  simpa [List.append_assoc, bindingEq] using tailTyped)
                have newBindingsTyped := bindingsTyped.append immediateTyped
                have successorTyped :=
                  RecursiveTotalMatchingStateTyping.mk environmentTyped
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

private theorem depthFirstMatching_recursiveTotalTypedSafe
    (reducerSafe : RecursiveTotalAtomReducerTypedSafe expressionTyping eval
      reduceAtom)
    (statesTyped : RecursiveTotalMatchingStatesTyping expressionTyping eval
      states answerTypes)
    (fuel : Nat) :
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
          have restTyped : RecursiveTotalMatchingStatesTyping expressionTyping
              eval rest answerTypes := by
            intro candidate member
            exact statesTyped candidate (by simp [member])
          rcases stepMatchingState_recursiveTotalTypedSafe reducerSafe stateTyped
            with timeout | ⟨observation, stepped, observationTyped⟩
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
                    rcases member with rfl | tailMember
                    · exact answerTyped
                    · exact answersTyped candidate tailMember⟩
            | expand successors successorsTyped =>
                have nextTyped : RecursiveTotalMatchingStatesTyping
                    expressionTyping eval (successors ++ rest) answerTypes := by
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

/-- Callback-parametric safety of a complete recursive matching search. -/
theorem searchMatchingFuel_recursiveTotalTypedSafe
    (reducerSafe : RecursiveTotalAtomReducerTypedSafe expressionTyping eval
      reduceAtom)
    (initialTyped : RecursiveTotalMatchingStateTyping expressionTyping eval
      initial answerTypes)
    (fuel : Nat) :
    TypedMatchingSearchResult answerTypes
      (searchMatchingFuel reduceAtom fuel initial) := by
  apply depthFirstMatching_recursiveTotalTypedSafe reducerSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact initialTyped

/-- Direct endpoint for a search whose expression callbacks satisfy the
chosen total expression judgment. -/
theorem searchPatternFuel_recursiveTotalTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (environmentTyped : EnvironmentTyping environment environmentTypes)
    (atomTyped : RecursiveTotalMatchingAtomTyping expressionTyping eval
      environmentTypes [] ⟨pattern, matcher, target⟩ bindingTypes)
    (fuel : Nat) :
    TypedMatchingSearchResult bindingTypes
      (searchPatternFuel eval fuel environment pattern matcher target) := by
  unfold searchPatternFuel
  apply searchMatchingFuel_recursiveTotalTypedSafe
    (expressionTyping := expressionTyping) (eval := eval)
    (evaluationAtomReducer_recursiveTotalTypedSafe
      (expressionTyping := expressionTyping) (eval := eval) evalSafe)
  exact .mk environmentTyped .nil (by
    simpa using
      (RecursiveTotalMatchingAtomsTyping.cons atomTyped
        RecursiveTotalMatchingAtomsTyping.nil))

/-- A terminal zero-hole atom has a non-stuck bounded search without any
typing assumption on its matcher closure.  This theorem is intentionally
operational and applies only because both successful reducer results contain
no recursive atoms. -/
theorem searchPatternFuel_zeroHoleTerminal_notStuck
    (terminal : ZeroHoleTerminalUserAtomReduction eval
      ⟨pattern, matcher, target⟩)
    (fuel : Nat) (environment : ValueEnvironment) :
    (searchPatternFuel eval fuel environment pattern matcher target).NotStuck := by
  unfold searchPatternFuel searchMatchingFuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      rcases terminal environment with timeout | noBranches | oneEmptyBranch
      · simp [depthFirstFuel, stepMatchingState, timeout]
        trivial
      · simp [depthFirstFuel, stepMatchingState, noBranches,
          MatchingState.successors]
        trivial
      · cases fuel with
        | zero =>
            simp [depthFirstFuel, stepMatchingState, oneEmptyBranch,
              MatchingState.successors, MatchingState.continueWith]
            trivial
        | succ fuel =>
            simp [depthFirstFuel, stepMatchingState, oneEmptyBranch,
              MatchingState.successors, MatchingState.continueWith]
            trivial

end TypePM.Runtime
