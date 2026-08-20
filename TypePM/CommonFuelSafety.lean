import TypePM.UserMatcherExhaustiveness
import TypePM.TotalUserMatcherSafety

/-!
# Common-fuel safety for recursive matching

This module closes the evaluator-callback premise for the currently typed
runtime core.  Expression evaluation and matching search use the same
decreasing fuel.  The expression judgment below adds matcher literals,
recursive `matchAll`, and the total core `matchFirst` with its mandatory
matcher-independent fallback to `RuntimeTyping`.

The remaining explicit boundary is source-pattern typing for atoms delegated
by user matchers.  `UserMatcherGeneralSafety` proves their matcher and target
value types, but the current runtime certificates do not yet turn every
preserved source pattern into `MatchingAtomTyping`.  The `branches` field of
`TotalMatchingAtomTyping.user` is therefore tied to the branches returned by
the concrete typed dispatch.  It asks only for source-pattern certificates for
those branches, rather than for fabricated branches having the same erased
matcher and target value types.
-/

namespace TypePM.Runtime

open TypePM.Source

mutual

  /-- Atom typing for the total core.  Built-in atoms reuse the existing
  judgment.  A user atom carries the complete typed-dispatch certificate and
  only the structural source-pattern closure fact still missing from T10. -/
  inductive TotalMatchingAtomTyping :
      List Ty → List Ty → MatchingAtom → List Ty → Prop where
    | builtin
        (typed : MatchingAtomTyping
          (fun context expression target =>
            RuntimeTyping expression target context)
          environmentTypes bindingTypes atom newBindings) :
        TotalMatchingAtomTyping environmentTypes bindingTypes atom newBindings
    | user
        (builtinMiss : ∀ eval environment,
          reduceBuiltinAtom eval environment
            ⟨pattern, .matcherV matcherEnvironment original remaining,
              target⟩ = .ok .miss)
        (matcherEnvironmentTyped :
          EnvironmentTyping matcherEnvironment definitionTypes)
        (targetTyped : ValueTyping target matcherTarget)
        (clausesTyped : RuntimeMatcherClausesInputTyping
          (bindingTypes ++ environmentTypes) definitionTypes matcherTarget
          pattern remaining)
        (finalCatchAll : MatcherTyping.FinalCatchAll remaining)
        (branches : ∀ (fuel : Nat) (atomEnvironment : ValueEnvironment)
            {holes recursiveBranches},
          dispatchMatcherClauses (evalFuel fuel) atomEnvironment
              matcherEnvironment remaining pattern target =
            .ok (.hit recursiveBranches) →
          DelegatedMatchingBranchesTyping holes recursiveBranches →
          ∀ branch ∈ recursiveBranches,
            TotalMatchingAtomsTyping environmentTypes bindingTypes
              branch newBindings) :
        TotalMatchingAtomTyping environmentTypes bindingTypes
          ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩
          newBindings

  /-- Pending total-core atoms are typed from left to right. -/
  inductive TotalMatchingAtomsTyping :
      List Ty → List Ty → List MatchingAtom → List Ty → Prop where
    | nil : TotalMatchingAtomsTyping environmentTypes bindingTypes [] []
    | cons
        (head : TotalMatchingAtomTyping environmentTypes bindingTypes
          atom headBindings)
        (tail : TotalMatchingAtomsTyping environmentTypes
          (bindingTypes ++ headBindings) atoms tailBindings) :
        TotalMatchingAtomsTyping environmentTypes bindingTypes
          (atom :: atoms) (headBindings ++ tailBindings)

end

namespace TotalMatchingAtomsTyping

def ofBuiltin :
    {environmentTypes bindingTypes : List Ty} →
    {atoms : List MatchingAtom} → {newBindings : List Ty} →
    MatchingAtomsTyping
      (fun context expression target => RuntimeTyping expression target context)
      environmentTypes bindingTypes atoms newBindings →
    TotalMatchingAtomsTyping environmentTypes bindingTypes atoms newBindings
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons _ _ _ _ head tail =>
      .cons (.builtin head) (ofBuiltin tail)

theorem append :
    ∀ {bindingTypes leftAtoms leftBindings},
      TotalMatchingAtomsTyping environmentTypes bindingTypes
        leftAtoms leftBindings →
      ∀ {rightAtoms rightBindings},
        TotalMatchingAtomsTyping environmentTypes
          (bindingTypes ++ leftBindings) rightAtoms rightBindings →
        TotalMatchingAtomsTyping environmentTypes bindingTypes
          (leftAtoms ++ rightAtoms) (leftBindings ++ rightBindings)
  | _, _, _, .nil, _, _, right => by simpa using right
  | bindingTypes, _, _, @TotalMatchingAtomsTyping.cons _ _ atom headBindings
      atoms tailBindings head tail, rightAtoms, rightBindings, right => by
      have right' : TotalMatchingAtomsTyping environmentTypes
          ((bindingTypes ++ headBindings) ++ tailBindings)
          rightAtoms rightBindings := by
        simpa [List.append_assoc] using right
      simpa [List.append_assoc] using
        TotalMatchingAtomsTyping.cons head (tail.append right')

end TotalMatchingAtomsTyping

/-- Preservation certificate for one total-core atom reduction. -/
inductive TotalAtomReductionTyping
    (environmentTypes bindingTypes expectedBindings : List Ty)
    (reduction : AtomReduction) : Prop where
  | intro
      (immediateTypes : List Ty)
      (immediateTyped : ValueTypings reduction.bindings immediateTypes)
      (branchesTyped : ∀ branch ∈ reduction.branches,
        ∃ delayedTypes,
          TotalMatchingAtomsTyping environmentTypes
            (bindingTypes ++ immediateTypes) branch delayedTypes ∧
          immediateTypes ++ delayedTypes = expectedBindings) :
      TotalAtomReductionTyping environmentTypes bindingTypes
        expectedBindings reduction

/-- Local preservation and progress for the combined total-core reducer. -/
def TotalAtomReducerTypedSafe (reduceAtom : AtomReducer) : Prop :=
  ∀ {environmentTypes bindingTypes environment bindings atom newBindings},
    EnvironmentTyping environment environmentTypes →
    ValueTypings bindings bindingTypes →
    TotalMatchingAtomTyping environmentTypes bindingTypes atom newBindings →
    reduceAtom (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) ∧
        TotalAtomReductionTyping environmentTypes bindingTypes
          newBindings reduction

private theorem builtinReduction_totalTyping
    (typing : AtomReductionTyping
      (fun context expression target => RuntimeTyping expression target context)
      environmentTypes bindingTypes expectedBindings reduction) :
    TotalAtomReductionTyping environmentTypes bindingTypes
      expectedBindings reduction := by
  cases typing with
  | intro immediateTypes immediateTyped branchesTyped =>
      exact .intro immediateTypes immediateTyped (by
        intro branch member
        obtain ⟨delayedTypes, branchTyped, equality⟩ :=
          branchesTyped branch member
        exact ⟨delayedTypes,
          TotalMatchingAtomsTyping.ofBuiltin branchTyped, equality⟩)

/-- The concrete evaluator reducer is safe at every fixed fuel.  The
evaluator callback premise of both built-in and user dispatch is discharged
by `RuntimeTyping.coreSafety`; no callback hypothesis appears in this
theorem. -/
theorem evaluationAtomReducer_totalTypedSafe (fuel : Nat) :
    TotalAtomReducerTypedSafe (evaluationAtomReducer (evalFuel fuel)) := by
  intro environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | builtin typed =>
      have evalSafe : EmbeddedEvaluatorSafe
          (fun context expression target => RuntimeTyping expression target context)
          (evalFuel fuel) := by
        intro context values expression target valuesTyped expressionTyped
        exact expressionTyped.coreSafety fuel values valuesTyped
      rcases reduceBuiltinAtom_typedSafe
          (fun context expression target => RuntimeTyping expression target context)
          (evalFuel fuel) evalSafe
          environmentTyped bindingsTyped typed with
        timeout | ⟨reduction, success, reductionTyped⟩
      · exact .inl (by
          simp [evaluationAtomReducer, combineAtomReducers, timeout])
      · exact .inr ⟨reduction, by
          simp [evaluationAtomReducer, combineAtomReducers, success],
          builtinReduction_totalTyping reductionTyped⟩
  | user builtinMiss matcherEnvironmentTyped targetTyped clausesTyped
      finalCatchAll branches =>
      rename_i pattern matcherEnvironment original remaining target
        definitionTypes matcherTarget
      have atomEnvironmentTyped : EnvironmentTyping
          (bindings ++ environment) (bindingTypes ++ environmentTypes) :=
        bindingsTyped.appendEnvironment environmentTyped
      have evalSafe : EmbeddedEvaluatorSafe
          (fun context expression target => RuntimeTyping expression target context)
          (evalFuel fuel) := by
        intro context values expression target valuesTyped expressionTyped
        exact expressionTyped.coreSafety fuel values valuesTyped
      rcases dispatchMatcherClauses_typedSafe_of_finalCatchAll
          (pattern := pattern) evalSafe
          atomEnvironmentTyped matcherEnvironmentTyped targetTyped clausesTyped
          finalCatchAll with timeout |
          ⟨recursiveBranches, holes, dispatched, recursiveBranchesTyped⟩
      · exact .inl (by
          unfold evaluationAtomReducer combineAtomReducers
          rw [builtinMiss]
          simp only [FuelResult.bind]
          simpa [reduceMatcherAtom] using
            congrArg (FuelResult.map clauseResultToAtomReduction) timeout)
      · let reduction : AtomReduction := ⟨recursiveBranches, []⟩
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
              by
                simpa using
                  (branches fuel (bindings ++ environment) dispatched
                    recursiveBranchesTyped branch member),
              rfl⟩)

/-- A total matching state has one common answer type list. -/
inductive TotalMatchingStateTyping : MatchingState → List Ty → Prop where
  | mk
      (environmentTyped : EnvironmentTyping environment environmentTypes)
      (bindingsTyped : ValueTypings bindings bindingTypes)
      (workTyped : TotalMatchingAtomsTyping environmentTypes bindingTypes
        work futureBindings) :
      TotalMatchingStateTyping ⟨work, environment, bindings⟩
        (bindingTypes ++ futureBindings)

/-- Pointwise typing of the DFS state worklist. -/
def TotalMatchingStatesTyping
    (states : List MatchingState) (answerTypes : List Ty) : Prop :=
  ∀ state ∈ states, TotalMatchingStateTyping state answerTypes

/-- Typed observation of one total matching-state step. -/
inductive TotalSearchStepTyping (answerTypes : List Ty) :
    SearchStep MatchingState (List Value) → Prop where
  | yield (answer : List Value)
      (answerTyped : ValueTypings answer answerTypes) :
      TotalSearchStepTyping answerTypes (.yield answer)
  | expand (successors : List MatchingState)
      (successorsTyped : ∀ state ∈ successors,
        TotalMatchingStateTyping state answerTypes) :
      TotalSearchStepTyping answerTypes (.expand successors)

def TotalTypedSearchStepResult (answerTypes : List Ty)
    (result : FuelResult (SearchStep MatchingState (List Value))) : Prop :=
  result = .timeout ∨
    ∃ observation, result = .ok observation ∧
      TotalSearchStepTyping answerTypes observation

private theorem stepMatchingState_totalTypedSafe
    (reducerSafe : TotalAtomReducerTypedSafe reduceAtom)
    (stateTyped : TotalMatchingStateTyping state answerTypes) :
    TotalTypedSearchStepResult answerTypes
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
                  TotalMatchingStateTyping.mk environmentTyped newBindingsTyped
                    branchAndTail
                have answerEq :
                    (bindingTypes ++ immediateTypes) ++
                        (delayedTypes ++ tailBindings) =
                      bindingTypes ++ (headBindings ++ tailBindings) := by
                  simp only [List.append_assoc]
                  rw [← List.append_assoc immediateTypes delayedTypes,
                    bindingEq]
                rw [answerEq] at successorTyped
                exact successorTyped

private theorem depthFirstMatching_totalTypedSafe
    (reducerSafe : TotalAtomReducerTypedSafe reduceAtom)
    (statesTyped : TotalMatchingStatesTyping states answerTypes)
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
          have restTyped : TotalMatchingStatesTyping rest answerTypes := by
            intro candidate member
            exact statesTyped candidate (by simp [member])
          rcases stepMatchingState_totalTypedSafe reducerSafe stateTyped with
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
                    rcases member with rfl | tailMember
                    · exact answerTyped
                    · exact answersTyped candidate tailMember⟩
            | expand successors successorsTyped =>
                have nextTyped : TotalMatchingStatesTyping
                    (successors ++ rest) answerTypes := by
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

/-- Common-fuel preservation for the finite DFS matching search. -/
theorem searchMatchingFuel_totalTypedSafe
    (reducerSafe : TotalAtomReducerTypedSafe reduceAtom)
    (initialTyped : TotalMatchingStateTyping initial answerTypes)
    (fuel : Nat) :
    TypedMatchingSearchResult answerTypes
      (searchMatchingFuel reduceAtom fuel initial) := by
  apply depthFirstMatching_totalTypedSafe reducerSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact initialTyped

/-! ## Total expressions and the common-fuel theorem

The currently certifiable total expression fragment embeds all
of `RuntimeTyping`; `matcher` constructs a certified user matcher closure;
and matching expressions may occur recursively in their children and bodies.

The dynamic initial-atom premise is an evaluation-indexed preservation
bridge.  It does not predict evaluation results: it receives the typed runtime
environment and the concrete successes of the target and matcher evaluations,
then certifies exactly the initial matching atom produced by those successes.
-/
mutual

  inductive TotalCoreTyping : Source.Expr → Ty → List Ty → Prop where
    | core
        (typing : RuntimeTyping expression target context) :
        TotalCoreTyping expression target context
    | matcher
        (clauses : RuntimeMatcherClausesTyping context matcherTarget sourceClauses) :
        TotalCoreTyping (.matcher sourceClauses)
          (.matcher .any matcherTarget) context
    | matchAll
        (target : TotalCoreTyping targetExpression matcherTarget context)
        (matcher : TotalCoreTyping matcherExpression
          (.matcher capability matcherTarget) context)
        (initialAtom : ∀ {fuel environment targetValue matcherValue},
          EnvironmentTyping environment context →
          evalFuel fuel environment targetExpression = .ok targetValue →
          evalFuel fuel environment matcherExpression = .ok matcherValue →
          ValueTyping targetValue matcherTarget →
          ValueTyping matcherValue (.matcher capability matcherTarget) →
          TotalMatchingAtomTyping context []
            ⟨pattern, matcherValue, targetValue⟩ bindingTypes)
        (body : TotalCoreTyping bodyExpression bodyTarget
          (bindingTypes ++ context)) :
        TotalCoreTyping
          (.matchAll targetExpression matcherExpression pattern bodyExpression)
          (TypePM.DataTypes.list bodyTarget) context
    | matchFirst
        (target : TotalCoreTyping targetExpression matcherTarget context)
        (matcher : TotalCoreTyping matcherExpression
          (.matcher capability matcherTarget) context)
        (arms : TotalMatchFirstArmsTyping context targetExpression
          matcherExpression matcherTarget capability resultTarget sourceArms)
        (fallback : TotalCoreTyping fallbackExpression resultTarget context) :
        TotalCoreTyping
          (.matchFirst targetExpression matcherExpression sourceArms
            fallbackExpression)
          resultTarget context

  /-- Each ordinary `matchFirst` arm has one result type and records the
  binding types produced by its pattern search.  The evaluation-indexed bridge
  is preservation data only: it does not predict whether the search is empty.
  Empty searches proceed to the next arm, while the separate fallback is
  typed under the original context by `TotalCoreTyping.matchFirst`. -/
  inductive TotalMatchFirstArmsTyping :
      List Ty → Source.Expr → Source.Expr → Ty → Cap → Ty →
        List Source.MatchFirstArm → Prop where
    | nil :
        TotalMatchFirstArmsTyping context targetExpression matcherExpression
          matcherTarget capability resultTarget []
    | cons
        (initialAtom : ∀ {fuel environment targetValue matcherValue},
          EnvironmentTyping environment context →
          evalFuel fuel environment targetExpression = .ok targetValue →
          evalFuel fuel environment matcherExpression = .ok matcherValue →
          ValueTyping targetValue matcherTarget →
          ValueTyping matcherValue (.matcher capability matcherTarget) →
          TotalMatchingAtomTyping context []
            ⟨arm.pattern, matcherValue, targetValue⟩ bindingTypes)
        (body : TotalCoreTyping arm.body resultTarget
          (bindingTypes ++ context))
        (rest : TotalMatchFirstArmsTyping context targetExpression
          matcherExpression matcherTarget capability resultTarget remaining) :
        TotalMatchFirstArmsTyping context targetExpression matcherExpression
          matcherTarget capability resultTarget (arm :: remaining)

end

private theorem matchingAnswers_traverse_totalTyped
    (evalSafe : EmbeddedEvaluatorSafe
      (fun context expression target => TotalCoreTyping expression target context)
      eval)
    (environmentTyped : EnvironmentTyping environment environmentTypes)
    (bodyTyped : TotalCoreTyping body bodyTarget
      (bindingTypes ++ environmentTypes))
    (answersTyped : MatchingAnswersTyping answers bindingTypes) :
    TypedHomogeneousResults bodyTarget
      (FuelResult.traverse
        (fun bindings => eval (bindings ++ environment) body) answers) := by
  induction answers with
  | nil => exact .inr ⟨[], rfl, .nil⟩
  | cons bindings answers ih =>
      have bindingsTyped := answersTyped bindings (by simp)
      have tailTyped : MatchingAnswersTyping answers bindingTypes := by
        intro candidate member
        exact answersTyped candidate (by simp [member])
      have completeEnvironment :=
        bindingsTyped.appendEnvironment environmentTyped
      rcases evalSafe completeEnvironment bodyTyped with
        headTimeout | ⟨value, headSuccess, valueTyped⟩
      · exact .inl (by
          simp [FuelResult.traverse, headTimeout])
      · rcases ih tailTyped with tailTimeout |
          ⟨values, tailSuccess, valuesTyped⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨value :: values, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            .cons valueTyped valuesTyped⟩

/-- Safety of the source-ordered arm loop once the target and matcher have
already been evaluated.  An empty arm result preserves the original
environment and advances to the tail; a hit extends the environment with the
first typed binding group. -/
private theorem evalMatchFirstArmsFuel_totalTyped
    (evalSafe : EmbeddedEvaluatorSafe
      (fun context expression target => TotalCoreTyping expression target context)
      (evalFuel fuel))
    (environmentTyped : EnvironmentTyping environment context)
    (targetValueTyped : ValueTyping targetValue matcherTarget)
    (matcherValueTyped :
      ValueTyping matcherValue (.matcher capability matcherTarget))
    (targetSuccess : evalFuel fuel environment targetExpression = .ok targetValue)
    (matcherSuccess :
      evalFuel fuel environment matcherExpression = .ok matcherValue)
    (armsTyped : TotalMatchFirstArmsTyping context targetExpression
      matcherExpression matcherTarget capability resultTarget arms)
    (fallbackTyped : TotalCoreTyping fallback resultTarget context) :
    TypedResult resultTarget
      (evalMatchFirstArmsFuel (evalFuel fuel) fuel environment targetValue
        matcherValue arms fallback) := by
  induction armCount : arms.length using Nat.strongRecOn generalizing arms with
  | ind count induction =>
    cases armsTyped with
    | nil =>
      simpa [evalMatchFirstArmsFuel] using
        evalSafe environmentTyped fallbackTyped
    | cons initialAtom bodyTyped restTyped =>
      rename_i bindingTypes remaining arm
      have atomTyped := initialAtom environmentTyped targetSuccess matcherSuccess
        targetValueTyped matcherValueTyped
      have workTyped : TotalMatchingAtomsTyping context []
          [⟨arm.pattern, matcherValue, targetValue⟩] bindingTypes := by
        simpa using TotalMatchingAtomsTyping.cons atomTyped
          (TotalMatchingAtomsTyping.nil (bindingTypes := bindingTypes))
      have initialStateTyped : TotalMatchingStateTyping
          ⟨[⟨arm.pattern, matcherValue, targetValue⟩], environment, []⟩
          bindingTypes := by
        simpa using TotalMatchingStateTyping.mk environmentTyped
          ValueTypings.nil workTyped
      rcases searchMatchingFuel_totalTypedSafe
          (evaluationAtomReducer_totalTypedSafe fuel) initialStateTyped fuel with
        searchTimeout | ⟨answers, searchSuccess, answersTyped⟩
      · exact .inl (by
          simp [evalMatchFirstArmsFuel, searchPatternFuel, searchTimeout,
            FuelResult.bind])
      · cases answers with
        | nil =>
            have shorter : remaining.length < count := by
              simp at armCount
              omega
            have tailSafe := induction remaining.length shorter restTyped rfl
            rcases tailSafe with tailTimeout |
              ⟨value, tailSuccess, valueTyped⟩
            · exact .inl (by
                simp [evalMatchFirstArmsFuel, searchPatternFuel, searchSuccess,
                  tailTimeout, FuelResult.bind])
            · exact .inr ⟨value, by
                simp [evalMatchFirstArmsFuel, searchPatternFuel, searchSuccess,
                  tailSuccess, FuelResult.bind], valueTyped⟩
        | cons bindings remainingAnswers =>
            have bindingsTyped : ValueTypings bindings bindingTypes :=
              answersTyped bindings (by simp)
            have bodyEnvironmentTyped :=
              bindingsTyped.appendEnvironment environmentTyped
            rcases evalSafe bodyEnvironmentTyped bodyTyped with bodyTimeout |
              ⟨value, bodySuccess, valueTyped⟩
            · exact .inl (by
                simp [evalMatchFirstArmsFuel, searchPatternFuel, searchSuccess,
                  bodyTimeout, FuelResult.bind])
            · exact .inr ⟨value, by
                simp [evalMatchFirstArmsFuel, searchPatternFuel, searchSuccess,
                  bodySuccess, FuelResult.bind], valueTyped⟩

/-- **Common-fuel strong induction for the total core.**  For every fuel,
typed evaluation either exhausts that fuel or returns a value of the declared
type.  Expression children, matching search, built-in value-pattern
evaluation, user-matcher arm bodies, next-matcher expressions, and recursively
selected `matchAll` or `matchFirst` bodies all run at the one common smaller
fuel.  When every `matchFirst` arm returns no binding groups, its explicit
fallback runs under the original typed environment.

There is no `EmbeddedEvaluatorSafe` premise: the callback used by user matcher
dispatch is `evalFuel` itself and is discharged internally. -/
theorem TotalCoreTyping.commonFuelSafety
    (typing : TotalCoreTyping expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyped : EnvironmentTyping environment context) :
    TypedResult target (evalFuel fuel environment expression) := by
  induction fuel using Nat.strongRecOn generalizing expression target
      context environment with
  | ind fuel induction =>
      cases typing with
      | core coreTyping =>
          exact coreTyping.coreSafety fuel environment environmentTyped
      | @matcher context matcherTarget sourceClauses clauses =>
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel =>
              exact .inr ⟨Value.matcherClosure environment sourceClauses,
                rfl, .matcherClosure environmentTyped clauses
                  ⟨[], by simp⟩⟩
      | @matchAll targetExpression matcherTarget context matcherExpression
          capability pattern bindingTypes bodyExpression bodyTarget targetTyped
          matcherTyped initialAtom bodyTyped =>
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel =>
              have smallerSafe : EmbeddedEvaluatorSafe
                  (fun context expression target =>
                    TotalCoreTyping expression target context)
                  (evalFuel fuel) := by
                intro childContext childEnvironment childExpression childTarget
                  childEnvironmentTyped childTyped
                exact induction fuel (by omega) childTyped childEnvironment
                  childEnvironmentTyped
              rcases smallerSafe environmentTyped targetTyped with
                targetTimeout | ⟨targetValue, targetSuccess, targetValueTyped⟩
              · exact .inl (by
                  simp [evalFuel, targetTimeout, FuelResult.bind])
              · rcases smallerSafe environmentTyped matcherTyped with
                  matcherTimeout |
                  ⟨matcherValue, matcherSuccess, matcherValueTyped⟩
                · exact .inl (by
                    simp [evalFuel, targetSuccess, matcherTimeout,
                      FuelResult.bind])
                · have atomTyped :=
                    initialAtom environmentTyped targetSuccess matcherSuccess
                      targetValueTyped matcherValueTyped
                  have workTyped : TotalMatchingAtomsTyping context []
                      [⟨pattern, matcherValue, targetValue⟩] bindingTypes := by
                    simpa using TotalMatchingAtomsTyping.cons atomTyped
                      (TotalMatchingAtomsTyping.nil
                        (bindingTypes := bindingTypes))
                  have initialStateTyped : TotalMatchingStateTyping
                      ⟨[⟨pattern, matcherValue, targetValue⟩], environment, []⟩
                      bindingTypes := by
                    simpa using TotalMatchingStateTyping.mk environmentTyped
                      (ValueTypings.nil) workTyped
                  have searched := searchMatchingFuel_totalTypedSafe
                    (evaluationAtomReducer_totalTypedSafe fuel)
                    initialStateTyped fuel
                  rcases searched with searchTimeout |
                    ⟨answers, searchSuccess, answersTyped⟩
                  · exact .inl (by
                      simp [evalFuel, targetSuccess, matcherSuccess,
                        searchPatternFuel, searchTimeout, FuelResult.bind])
                  · have bodies := matchingAnswers_traverse_totalTyped
                      smallerSafe environmentTyped bodyTyped answersTyped
                    rcases bodies with bodiesTimeout |
                      ⟨values, bodiesSuccess, valuesTyped⟩
                    · exact .inl (by
                        simp [evalFuel, targetSuccess, matcherSuccess,
                          searchPatternFuel, searchSuccess, bodiesTimeout,
                          FuelResult.bind, FuelResult.map])
                    · exact .inr ⟨Value.buildList values, by
                        simp [evalFuel, targetSuccess, matcherSuccess,
                          searchPatternFuel, searchSuccess, bodiesSuccess,
                          FuelResult.bind, FuelResult.map],
                        .list valuesTyped⟩
      | matchFirst targetTyped matcherTyped armsTyped fallbackTyped =>
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel =>
              have smallerSafe : EmbeddedEvaluatorSafe
                  (fun context expression target =>
                    TotalCoreTyping expression target context)
                  (evalFuel fuel) := by
                intro childContext childEnvironment childExpression childTarget
                  childEnvironmentTyped childTyped
                exact induction fuel (by omega) childTyped childEnvironment
                  childEnvironmentTyped
              rcases smallerSafe environmentTyped targetTyped with
                targetTimeout | ⟨targetValue, targetSuccess, targetValueTyped⟩
              · exact .inl (by
                  simp [evalFuel, targetTimeout, FuelResult.bind])
              · rcases smallerSafe environmentTyped matcherTyped with
                  matcherTimeout |
                  ⟨matcherValue, matcherSuccess, matcherValueTyped⟩
                · exact .inl (by
                    simp [evalFuel, targetSuccess, matcherTimeout,
                      FuelResult.bind])
                · have armsSafe := evalMatchFirstArmsFuel_totalTyped
                    smallerSafe environmentTyped targetValueTyped matcherValueTyped
                    targetSuccess matcherSuccess armsTyped fallbackTyped
                  rcases armsSafe with armsTimeout |
                    ⟨value, armsSuccess, valueTyped⟩
                  · exact .inl (by
                      simp [evalFuel, targetSuccess, matcherSuccess,
                        armsTimeout, FuelResult.bind])
                  · exact .inr ⟨value, by
                      simp [evalFuel, targetSuccess, matcherSuccess,
                        armsSuccess, FuelResult.bind], valueTyped⟩

/-- No-stuck form of the common-fuel theorem. -/
theorem TotalCoreTyping.neverStuck
    (typing : TotalCoreTyping expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyped : EnvironmentTyping environment context) :
    (evalFuel fuel environment expression).NotStuck :=
  (typing.commonFuelSafety fuel environment environmentTyped).notStuck

/-- Callback-contract form of the same result.  Unlike the earlier
conditional matcher theorems, callers supply only the fuel; safety of the
actual recursive evaluator is a conclusion. -/
theorem evalFuel_totalCore_embeddedSafe (fuel : Nat) :
    EmbeddedEvaluatorSafe
      (fun context expression target => TotalCoreTyping expression target context)
      (evalFuel fuel) := by
  intro context environment expression target environmentTyped expressionTyped
  exact expressionTyped.commonFuelSafety fuel environment environmentTyped

/-- Ordinary-evaluator specialization of callback-parametric recursive matcher
dispatch.  The callback premise is discharged by the common-fuel theorem. -/
theorem dispatchMatcherClauses_totalCoreTypedSafe
    (fuel : Nat)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (clausesTyped : TotalRuntimeMatcherClausesInputTyping
      (fun context expression target => TotalCoreTyping expression target context)
      atomEnvironmentTypes definitionTypes matcherTarget pattern clauses) :
    dispatchMatcherClauses (evalFuel fuel) atomEnvironment matcherEnvironment
        clauses pattern target = .timeout ∨
      ∃ result,
        dispatchMatcherClauses (evalFuel fuel) atomEnvironment matcherEnvironment
            clauses pattern target = .ok result ∧
        MatcherClauseResultTyping result :=
  dispatchMatcherClauses_totalTypedSafe
    (expressionTyping := fun context expression target =>
      TotalCoreTyping expression target context) (eval := evalFuel fuel)
    (evalFuel_totalCore_embeddedSafe fuel) atomEnvironmentTyped
    matcherEnvironmentTyped targetTyped clausesTyped

/-- The same specialization packaged at the exact matcher cursor value. -/
theorem TotalMatcherClosureInputTyping.dispatch_totalCoreTypedSafe
    (typing : TotalMatcherClosureInputTyping
      (fun context expression target => TotalCoreTyping expression target context)
      atomEnvironmentTypes matcherValue matcherTarget pattern)
    (fuel : Nat)
    (atomEnvironmentTyped :
      EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (targetTyped : ValueTyping target matcherTarget) :
    dispatchMatcherValue (evalFuel fuel) atomEnvironment matcherValue pattern
        target = .timeout ∨
      ∃ result,
        dispatchMatcherValue (evalFuel fuel) atomEnvironment matcherValue pattern
            target = .ok result ∧
        MatcherClauseResultTyping result :=
  typing.dispatch_typedSafe (evalFuel_totalCore_embeddedSafe fuel)
    atomEnvironmentTyped targetTyped

end TypePM.Runtime
