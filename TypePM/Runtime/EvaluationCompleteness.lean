import TypePM.Runtime.EvaluationAdequacy

/-!
# Fuel monotonicity and finite completeness

A completed evaluation is stable under additional fuel.  Conversely, every
finite big-step derivation has a finite fuel bound.  These properties cover
ordinary and recursive closures and the callback applications of `map`.
-/

namespace TypePM.Runtime

open FuelResult

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

private theorem traverse_ok_mono
    {before after : α → FuelResult β}
    (monotone : ∀ {input output},
      before input = .ok output → after input = .ok output)
    {inputs : List α} {outputs : List β}
    (success : FuelResult.traverse before inputs = .ok outputs) :
    FuelResult.traverse after inputs = .ok outputs := by
  rw [traverse_eq_ok_iff] at success ⊢
  induction success with
  | nil => exact .nil
  | cons head tail ih => exact .cons (monotone head) ih

private theorem evalPrimitive_ok_mono
    {before after : Value → Value → FuelResult Value}
    (monotone : ∀ {function input output},
      before function input = .ok output →
        after function input = .ok output)
    {operation : PrimOp} {arguments : List Value} {result : Value}
    (success : evalPrimitive before operation arguments = .ok result) :
    evalPrimitive after operation arguments = .ok result := by
  cases operation with
  | add =>
      rcases arguments with _ | ⟨first, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨second, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · cases first <;> cases second <;> simpa [evalPrimitive] using success
      · simp [evalPrimitive] at success
  | append =>
      rcases arguments with _ | ⟨left, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨right, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · exact success
      · simp [evalPrimitive] at success
  | member =>
      rcases arguments with _ | ⟨needle, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨target, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · exact success
      · simp [evalPrimitive] at success
  | deleteFirst =>
      rcases arguments with _ | ⟨needle, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨target, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · exact success
      · simp [evalPrimitive] at success
  | map =>
      rcases arguments with _ | ⟨function, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨target, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · cases targetView : Value.viewList target with
        | none => simp [evalPrimitive, targetView] at success
        | some inputs =>
            simp only [evalPrimitive, targetView, FuelResult.map] at success
            cases oldTraversal : FuelResult.traverse (before function) inputs with
            | timeout => simp [oldTraversal] at success
            | stuck => simp [oldTraversal] at success
            | ok outputs =>
                simp [oldTraversal] at success
                subst result
                have newTraversal := traverse_ok_mono
                  (fun application => monotone application) oldTraversal
                simp [evalPrimitive, targetView, newTraversal]
      · simp [evalPrimitive] at success

private theorem matcherArmDispatches_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    (monotone : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (dispatch : MatcherArmDispatches before matcherEnvironment captureValues
      holes nextMatchers target arm result) :
    MatcherArmDispatches after matcherEnvironment captureValues holes
      nextMatchers target arm result := by
  cases dispatch with
  | miss mismatch => exact .miss mismatch
  | hit dataMatch bodyEval decompositionShape matcherEval matcherShape
      branchesBuilt =>
      exact .hit dataMatch (monotone bodyEval) decompositionShape
        (monotone matcherEval) matcherShape branchesBuilt

private theorem matcherArmsDispatch_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    (monotone : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (dispatch : MatcherArmsDispatch before matcherEnvironment captureValues
      holes nextMatchers target arms result) :
    MatcherArmsDispatch after matcherEnvironment captureValues holes
      nextMatchers target arms result := by
  induction dispatch with
  | nil => exact .nil
  | hit selected => exact .hit (matcherArmDispatches_mono monotone selected)
  | skip missed tail ih =>
      exact .skip (matcherArmDispatches_mono monotone missed) ih

private theorem matcherClauseDispatches_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    (monotone : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (dispatch : MatcherClauseDispatches before atomEnvironment
      matcherEnvironment pattern target clause result) :
    MatcherClauseDispatches after atomEnvironment matcherEnvironment pattern
      target clause result := by
  cases dispatch with
  | miss mismatch => exact .miss mismatch
  | matched headerMatch capturesEval armsDispatch =>
      exact .matched headerMatch
        ((traverse_eq_ok_iff _ _ _).mp
          (traverse_ok_mono monotone
            ((traverse_eq_ok_iff _ _ _).mpr capturesEval)))
        (matcherArmsDispatch_mono monotone armsDispatch)

private theorem matcherClausesDispatch_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    (monotone : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (dispatch : MatcherClausesDispatch before atomEnvironment
      matcherEnvironment pattern target clauses result) :
    MatcherClausesDispatch after atomEnvironment matcherEnvironment pattern
      target clauses result := by
  induction dispatch with
  | nil => exact .nil
  | hit selected => exact .hit (matcherClauseDispatches_mono monotone selected)
  | skip missed tail ih =>
      exact .skip (matcherClauseDispatches_mono monotone missed) ih

private theorem builtinAtom_hit_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    (monotone : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (success : reduceBuiltinAtom before environment atom =
      .ok (.hit reduction)) :
    reduceBuiltinAtom after environment atom = .ok (.hit reduction) := by
  rw [reduceBuiltinAtom_hit_iff] at success ⊢
  cases success with
  | somethingWild => exact .somethingWild
  | somethingVar => exact .somethingVar
  | somethingValueSuccess evaluated equal =>
      exact .somethingValueSuccess (monotone evaluated) equal
  | somethingValueFailure evaluated unequal =>
      exact .somethingValueFailure (monotone evaluated) unequal
  | and => exact .and
  | tuple zipped => exact .tuple zipped
  | productSomethingVar => exact .productSomethingVar
  | productSomethingWild => exact .productSomethingWild
  | productSomethingValue => exact .productSomethingValue

private theorem matcherAtom_hit_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    (monotone : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (success : reduceMatcherAtom before environment atom =
      .ok (.hit reduction)) :
    reduceMatcherAtom after environment atom = .ok (.hit reduction) := by
  rw [reduceMatcherAtom_hit_iff] at success ⊢
  cases success with
  | matcher clausesDispatch =>
      exact .matcher (matcherClausesDispatch_mono monotone clausesDispatch)

@[simp] private theorem map_hit_ne_miss
    (result : FuelResult α) (make : α → β) :
    FuelResult.map (fun value => DispatchResult.hit (make value)) result ≠
      .ok .miss := by
  cases result <;> simp [FuelResult.map]

private theorem reduceBuiltinAtom_matcherV_miss
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (environment matcherEnvironment : ValueEnvironment)
    (original remaining : List Source.MatcherClause)
    (pattern : Source.Pattern) (target : Value)
    (dispatchable : MatcherDispatchable pattern) :
    reduceBuiltinAtom evaluate environment
      ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩ =
        .ok .miss := by
  cases dispatchable <;> rfl

private theorem combinedAtom_hit_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    (monotone : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (success : combineAtomReducers (reduceBuiltinAtom before)
        (reduceMatcherAtom before) environment atom = .ok (.hit reduction)) :
    combineAtomReducers (reduceBuiltinAtom after)
        (reduceMatcherAtom after) environment atom = .ok (.hit reduction) := by
  cases primary : reduceBuiltinAtom before environment atom with
  | timeout => simp [combineAtomReducers, primary] at success
  | stuck => simp [combineAtomReducers, primary] at success
  | ok outcome =>
      cases outcome with
      | hit primaryReduction =>
          simp [combineAtomReducers, primary] at success
          subst primaryReduction
          exact combineAtomReducers_primary_hit _ _
            (builtinAtom_hit_mono monotone primary)
      | miss =>
          have fallback : reduceMatcherAtom before environment atom =
              .ok (.hit reduction) := by
            simpa [combineAtomReducers, primary] using success
          have matcherRelation :=
            (reduceMatcherAtom_hit_iff _ _ _ _).mp fallback
          cases matcherRelation with
          | matcher clausesDispatch =>
              rw [combineAtomReducers_primary_miss _ _
                (reduceBuiltinAtom_matcherV_miss _ _ _ _ _ _ _
                  (matcherDispatchable_of_reduceBuiltinAtom_miss primary))]
              exact matcherAtom_hit_mono monotone fallback

private theorem matchingStep_ok_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    (monotone : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (success : stepMatchingState
      (combineAtomReducers (reduceBuiltinAtom before)
        (reduceMatcherAtom before)) state = .ok observation) :
    stepMatchingState
      (combineAtomReducers (reduceBuiltinAtom after)
        (reduceMatcherAtom after)) state = .ok observation := by
  have related := stepMatchingState_sound success
  cases related with
  | yield => rfl
  | expand reduced =>
      exact MatchingStateSteps.complete (.expand
        (combinedAtom_hit_mono monotone reduced))

private theorem depthFirstFuel_step_mono
    {before after : State → FuelResult (SearchStep State Answer)}
    (monotone : ∀ {state observation},
      before state = .ok observation → after state = .ok observation)
    {fuel : Nat} {states : List State} {answers : List Answer}
    (success : depthFirstFuel before fuel states = .ok answers) :
    depthFirstFuel after fuel states = .ok answers := by
  induction fuel generalizing states answers with
  | zero =>
      cases states with
      | nil => simpa using success
      | cons state rest => simp [depthFirstFuel] at success
  | succ fuel ih =>
      cases states with
      | nil => simpa using success
      | cons state rest =>
          simp only [depthFirstFuel] at success ⊢
          rw [bind_eq_ok_iff] at success ⊢
          rcases success with ⟨observation, head, continued⟩
          refine ⟨observation, monotone head, ?_⟩
          cases observation with
          | yield answer =>
              rw [map_eq_ok_iff] at continued ⊢
              rcases continued with ⟨tailAnswers, tail, output⟩
              exact ⟨tailAnswers, ih tail, output⟩
          | expand successors => exact ih continued

private theorem evalMatchFirstArmsFuel_ok_mono
    {before after : ValueEnvironment → Source.Expr → FuelResult Value}
    {beforeFuel afterFuel : Nat}
    (evaluationMono : ∀ {environment expression value},
      before environment expression = .ok value →
        after environment expression = .ok value)
    (searchMono : ∀ {pattern bindingGroups},
      searchPatternFuel before beforeFuel environment pattern matcher target =
          .ok bindingGroups →
        searchPatternFuel after afterFuel environment pattern matcher target =
          .ok bindingGroups)
    (success : evalMatchFirstArmsFuel before beforeFuel environment target matcher
      arms = .ok result) :
    evalMatchFirstArmsFuel after afterFuel environment target matcher arms =
      .ok result := by
  induction arms with
  | nil => simp [evalMatchFirstArmsFuel] at success
  | cons arm rest ih =>
      simp only [evalMatchFirstArmsFuel] at success ⊢
      rw [bind_eq_ok_iff] at success ⊢
      rcases success with ⟨bindingGroups, searchResult, continuation⟩
      refine ⟨bindingGroups, searchMono searchResult, ?_⟩
      cases bindingGroups with
      | nil => exact ih continuation
      | cons bindings remaining => exact evaluationMono continuation

private theorem fuel_ok_succ : ∀ fuel,
    (∀ {environment expression value},
      evalFuel fuel environment expression = .ok value →
        evalFuel (fuel + 1) environment expression = .ok value) ∧
    (∀ {function argument value},
      applyFuel fuel function argument = .ok value →
        applyFuel (fuel + 1) function argument = .ok value) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro environment expression value success
        simp [evalFuel] at success
      · intro function argument value success
        simp [applyFuel] at success
  | succ fuel ih =>
      rcases ih with ⟨evalStep, applyStep⟩
      constructor
      · intro environment expression value success
        cases expression with
        | var index => simpa [evalFuel] using success
        | lit literal => simpa [evalFuel] using success
        | something => simpa [evalFuel] using success
        | lam body => simpa [evalFuel] using success
        | app function argument =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success
            rcases success with ⟨functionValue, functionResult, rest⟩
            rw [bind_eq_ok_iff] at rest
            rcases rest with ⟨argumentValue, argumentResult, application⟩
            rw [bind_eq_ok_iff]
            refine ⟨functionValue, evalStep functionResult, ?_⟩
            rw [bind_eq_ok_iff]
            exact ⟨argumentValue, evalStep argumentResult,
              applyStep application⟩
        | tuple items =>
            simp only [evalFuel] at success ⊢
            rw [map_eq_ok_iff] at success ⊢
            rcases success with ⟨values, traversal, output⟩
            exact ⟨values,
              traverse_ok_mono (fun result => evalStep result) traversal,
              output⟩
        | letE valueExpression body =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success ⊢
            rcases success with ⟨boundValue, boundResult, bodyResult⟩
            exact ⟨boundValue, evalStep boundResult, evalStep bodyResult⟩
        | ctor constructor arguments =>
            simp only [evalFuel] at success ⊢
            rw [map_eq_ok_iff] at success ⊢
            rcases success with ⟨values, traversal, output⟩
            exact ⟨values,
              traverse_ok_mono (fun result => evalStep result) traversal,
              output⟩
        | prim operation arguments =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success ⊢
            rcases success with ⟨values, traversal, primitive⟩
            exact ⟨values,
              traverse_ok_mono (fun result => evalStep result) traversal,
              evalPrimitive_ok_mono
                (fun application => applyStep application) primitive⟩
        | ifE condition thenBranch elseBranch =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success ⊢
            rcases success with ⟨conditionValue, conditionResult, branchResult⟩
            refine ⟨conditionValue, evalStep conditionResult, ?_⟩
            cases conditionValue with
            | data constructor arguments =>
                cases arguments with
                | nil =>
                    by_cases isTrue : constructor = DataCtor.true
                    · subst constructor
                      simp only [if_pos rfl] at branchResult ⊢
                      exact evalStep branchResult
                    · by_cases isFalse : constructor = DataCtor.false
                      · subst constructor
                        have falseNotTrue :
                            DataCtor.false ≠ DataCtor.true := by decide
                        simp only [if_neg falseNotTrue, if_pos rfl] at branchResult ⊢
                        exact evalStep branchResult
                      · simp [isTrue, isFalse] at branchResult
                | cons head tail => simpa using branchResult
            | int literal => simpa using branchResult
            | tuple items => simpa using branchResult
            | closure kind closureEnvironment body => simpa using branchResult
            | matcherV matcherEnvironment original remaining => simpa using branchResult
            | something => simpa using branchResult
        | fixE body => simpa [evalFuel] using success
        | matcher clauses => simpa [evalFuel] using success
        | matchAll target matcher pattern body =>
            simp only [evalFuel] at success
            rw [bind_eq_ok_iff] at success
            rcases success with ⟨targetValue, targetResult, continued⟩
            rw [bind_eq_ok_iff] at continued
            rcases continued with ⟨matcherValue, matcherResult, continued⟩
            rw [bind_eq_ok_iff] at continued
            rcases continued with ⟨bindingGroups, searchResult, bodyResult⟩
            rw [map_eq_ok_iff] at bodyResult
            rcases bodyResult with ⟨bodyValues, traversal, output⟩
            subst value
            have searchChanged :
                searchMatchingFuel
                    (combineAtomReducers
                      (reduceBuiltinAtom (evalFuel (fuel + 1)))
                      (reduceMatcherAtom (evalFuel (fuel + 1))))
                    fuel
                    ⟨[⟨pattern, matcherValue, targetValue⟩], environment, []⟩ =
                  .ok bindingGroups := by
              exact depthFirstFuel_step_mono
                (matchingStep_ok_mono
                  (fun success => evalStep success)) searchResult
            have searchRaised :
                searchMatchingFuel
                    (combineAtomReducers
                      (reduceBuiltinAtom (evalFuel (fuel + 1)))
                      (reduceMatcherAtom (evalFuel (fuel + 1))))
                    (fuel + 1)
                    ⟨[⟨pattern, matcherValue, targetValue⟩], environment, []⟩ =
                  .ok bindingGroups := by
              exact depthFirstFuel_ok_add _ searchChanged 1
            have bodiesRaised :
                FuelResult.traverse
                    (fun bindings =>
                      evalFuel (fuel + 1) (bindings ++ environment) body)
                    bindingGroups = .ok bodyValues :=
              traverse_ok_mono (fun success => evalStep success) traversal
            change
              FuelResult.bind (evalFuel (fuel + 1) environment target)
                (fun targetValue =>
                  FuelResult.bind (evalFuel (fuel + 1) environment matcher)
                    (fun matcherValue =>
                      FuelResult.bind
                        (searchMatchingFuel
                          (combineAtomReducers
                            (reduceBuiltinAtom (evalFuel (fuel + 1)))
                            (reduceMatcherAtom (evalFuel (fuel + 1))))
                          (fuel + 1)
                          ⟨[⟨pattern, matcherValue, targetValue⟩],
                            environment, []⟩)
                        (fun bindingGroups =>
                          FuelResult.map Value.buildList
                            (FuelResult.traverse
                              (fun bindings => evalFuel (fuel + 1)
                                (bindings ++ environment) body)
                              bindingGroups)))) = .ok (Value.buildList bodyValues)
            rw [evalStep targetResult]
            simp only [FuelResult.bind_ok]
            rw [evalStep matcherResult]
            simp only [FuelResult.bind_ok]
            rw [searchRaised]
            simp [bodiesRaised]
        | matchFirst target matcher arms =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success ⊢
            rcases success with ⟨targetValue, targetResult, continued⟩
            refine ⟨targetValue, evalStep targetResult, ?_⟩
            rw [bind_eq_ok_iff] at continued ⊢
            rcases continued with ⟨matcherValue, matcherResult, armsResult⟩
            refine ⟨matcherValue, evalStep matcherResult, ?_⟩
            exact evalMatchFirstArmsFuel_ok_mono
              (fun success => evalStep success)
              (fun {pattern bindingGroups} searchResult => by
                have callbackRaised := depthFirstFuel_step_mono
                  (matchingStep_ok_mono
                    (fun success => evalStep success)) searchResult
                exact depthFirstFuel_ok_add _ callbackRaised 1)
              armsResult
      · intro function argument value success
        cases function with
        | closure kind definitionEnvironment body =>
            cases kind with
            | plain =>
                simp only [applyFuel] at success ⊢
                exact evalStep success
            | recursive =>
                simp only [applyFuel] at success ⊢
                exact evalStep success
        | int literal => simp [applyFuel] at success
        | data constructor arguments => simp [applyFuel] at success
        | tuple items => simp [applyFuel] at success
        | matcherV environment original remaining => simp [applyFuel] at success
        | something => simp [applyFuel] at success

theorem evalFuel_ok_succ
    (success : evalFuel fuel environment expression = .ok value) :
    evalFuel (fuel + 1) environment expression = .ok value :=
  (fuel_ok_succ fuel).1 success

theorem applyFuel_ok_succ
    (success : applyFuel fuel function argument = .ok value) :
    applyFuel (fuel + 1) function argument = .ok value :=
  (fuel_ok_succ fuel).2 success

theorem evalFuel_ok_add
    (success : evalFuel fuel environment expression = .ok value)
    (extra : Nat) :
    evalFuel (fuel + extra) environment expression = .ok value := by
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [Nat.add_succ]
      exact evalFuel_ok_succ ih

theorem applyFuel_ok_add
    (success : applyFuel fuel function argument = .ok value)
    (extra : Nat) :
    applyFuel (fuel + extra) function argument = .ok value := by
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [Nat.add_succ]
      exact applyFuel_ok_succ ih

theorem evalFuel_ok_of_le
    (le : firstFuel ≤ secondFuel)
    (success : evalFuel firstFuel environment expression = .ok value) :
    evalFuel secondFuel environment expression = .ok value := by
  have equality : firstFuel + (secondFuel - firstFuel) = secondFuel :=
    Nat.add_sub_of_le le
  rw [← equality]
  exact evalFuel_ok_add success _

theorem applyFuel_ok_of_le
    (le : firstFuel ≤ secondFuel)
    (success : applyFuel firstFuel function argument = .ok value) :
    applyFuel secondFuel function argument = .ok value := by
  have equality : firstFuel + (secondFuel - firstFuel) = secondFuel :=
    Nat.add_sub_of_le le
  rw [← equality]
  exact applyFuel_ok_add success _

theorem Eval.complete
    (derivation : Eval environment expression value) :
    ∃ fuel, evalFuel fuel environment expression = .ok value := by
  apply Eval.rec
    (motive_1 := fun environment expression value _ =>
      ∃ fuel, evalFuel fuel environment expression = .ok value)
    (motive_2 := fun environment expressions values _ =>
      ∃ fuel,
        FuelResult.traverse (evalFuel fuel environment) expressions =
          .ok values)
    (motive_3 := fun function argument value _ =>
      ∃ fuel, applyFuel fuel function argument = .ok value)
    (motive_4 := fun function inputs outputs _ =>
      ∃ fuel,
        FuelResult.traverse (applyFuel fuel function) inputs = .ok outputs)
    (motive_5 := fun operation arguments value _ =>
      ∃ fuel,
        evalPrimitive (applyFuel fuel) operation arguments = .ok value)
    (motive_6 := fun matcherEnvironment captureValues holes nextMatchers target
        arm result _ =>
      ∃ fuel, MatcherArmDispatches (evalFuel fuel) matcherEnvironment
        captureValues holes nextMatchers target arm result)
    (motive_7 := fun matcherEnvironment captureValues holes nextMatchers target
        arms result _ =>
      ∃ fuel, MatcherArmsDispatch (evalFuel fuel) matcherEnvironment
        captureValues holes nextMatchers target arms result)
    (motive_8 := fun atomEnvironment matcherEnvironment pattern target clause
        result _ =>
      ∃ fuel, MatcherClauseDispatches (evalFuel fuel) atomEnvironment
        matcherEnvironment pattern target clause result)
    (motive_9 := fun atomEnvironment matcherEnvironment pattern target clauses
        result _ =>
      ∃ fuel, MatcherClausesDispatch (evalFuel fuel) atomEnvironment
        matcherEnvironment pattern target clauses result)
    (motive_10 := fun environment atom reduction _ =>
      ∃ fuel,
        combineAtomReducers (reduceBuiltinAtom (evalFuel fuel))
          (reduceMatcherAtom (evalFuel fuel)) environment atom =
            .ok (.hit reduction))
    (motive_11 := fun states answers _ =>
      ∃ evaluationFuel searchFuel,
        depthFirstFuel
          (stepMatchingState
            (combineAtomReducers (reduceBuiltinAtom (evalFuel evaluationFuel))
              (reduceMatcherAtom (evalFuel evaluationFuel))))
          searchFuel states = .ok answers)
    (motive_12 := fun environment body groups values _ =>
      ∃ fuel,
        FuelResult.traverse
          (fun bindings => evalFuel fuel (bindings ++ environment) body)
          groups = .ok values)
    (motive_13 := fun environment target matcher arms result _ =>
      ∃ evaluationFuel searchFuel,
        evalMatchFirstArmsFuel (evalFuel evaluationFuel) searchFuel environment
          target matcher arms = .ok result)
  case var =>
      intros environment index value lookup
      refine ⟨1, ?_⟩
      simp [evalFuel, (getElem?_eq_some_iff_lookup _ _ _).mpr lookup]
  case lit =>
      intros environment literal
      exact ⟨1, rfl⟩
  case something =>
      intro environment
      exact ⟨1, rfl⟩
  case lam =>
      intros environment body
      exact ⟨1, rfl⟩
  case app =>
      intros environment function functionValue argument argumentValue result
        functionEval argumentEval application functionIH argumentIH applicationIH
      rcases functionIH with ⟨functionFuel, functionSuccess⟩
      rcases argumentIH with ⟨argumentFuel, argumentSuccess⟩
      rcases applicationIH with ⟨applicationFuel, applicationSuccess⟩
      let common := max functionFuel (max argumentFuel applicationFuel)
      have functionLe : functionFuel ≤ common := Nat.le_max_left _ _
      have argumentLe : argumentFuel ≤ common :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have applicationLe : applicationFuel ≤ common :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      refine ⟨common + 1, ?_⟩
      simp [evalFuel,
        evalFuel_ok_of_le functionLe functionSuccess,
        evalFuel_ok_of_le argumentLe argumentSuccess,
        applyFuel_ok_of_le applicationLe applicationSuccess]
  case tuple =>
      intros environment items values itemsEval itemsIH
      rcases itemsIH with ⟨fuel, success⟩
      refine ⟨fuel + 1, ?_⟩
      simp [evalFuel, success]
  case letE =>
      intros environment valueExpression value body result valueEval bodyEval
        valueIH bodyIH
      rcases valueIH with ⟨valueFuel, valueSuccess⟩
      rcases bodyIH with ⟨bodyFuel, bodySuccess⟩
      let common := max valueFuel bodyFuel
      have valueRaised := evalFuel_ok_of_le
        (Nat.le_max_left valueFuel bodyFuel) valueSuccess
      have bodyRaised := evalFuel_ok_of_le
        (Nat.le_max_right valueFuel bodyFuel) bodySuccess
      refine ⟨common + 1, ?_⟩
      dsimp [common]
      simp only [evalFuel, valueRaised, FuelResult.bind_ok, bodyRaised]
  case ctor =>
      intros environment arguments values constructor argumentsEval argumentsIH
      rcases argumentsIH with ⟨fuel, success⟩
      refine ⟨fuel + 1, ?_⟩
      simp [evalFuel, success]
  case prim =>
      intros environment arguments values operation result argumentsEval primitive
        argumentsIH primitiveIH
      rcases argumentsIH with ⟨argumentsFuel, argumentsSuccess⟩
      rcases primitiveIH with ⟨primitiveFuel, primitiveSuccess⟩
      let common := max argumentsFuel primitiveFuel
      have argumentsRaised := traverse_ok_mono
        (fun application => evalFuel_ok_of_le
          (Nat.le_max_left argumentsFuel primitiveFuel) application)
        argumentsSuccess
      have primitiveRaised := evalPrimitive_ok_mono
        (fun application => applyFuel_ok_of_le
          (Nat.le_max_right argumentsFuel primitiveFuel) application)
        primitiveSuccess
      refine ⟨common + 1, ?_⟩
      dsimp [common]
      simp only [evalFuel, argumentsRaised, FuelResult.bind_ok,
        primitiveRaised]
  case ifTrue =>
      intros environment condition thenBranch result elseBranch conditionEval
        branchEval conditionIH branchIH
      rcases conditionIH with ⟨conditionFuel, conditionSuccess⟩
      rcases branchIH with ⟨branchFuel, branchSuccess⟩
      let common := max conditionFuel branchFuel
      have conditionRaised := evalFuel_ok_of_le
        (Nat.le_max_left conditionFuel branchFuel) conditionSuccess
      have branchRaised := evalFuel_ok_of_le
        (Nat.le_max_right conditionFuel branchFuel) branchSuccess
      refine ⟨common + 1, ?_⟩
      dsimp [common]
      simp [evalFuel, conditionRaised, branchRaised]
  case ifFalse =>
      intros environment condition elseBranch result thenBranch conditionEval
        branchEval conditionIH branchIH
      rcases conditionIH with ⟨conditionFuel, conditionSuccess⟩
      rcases branchIH with ⟨branchFuel, branchSuccess⟩
      let common := max conditionFuel branchFuel
      have falseNotTrue : DataCtor.false ≠ DataCtor.true := by decide
      have conditionRaised := evalFuel_ok_of_le
        (Nat.le_max_left conditionFuel branchFuel) conditionSuccess
      have branchRaised := evalFuel_ok_of_le
        (Nat.le_max_right conditionFuel branchFuel) branchSuccess
      refine ⟨common + 1, ?_⟩
      dsimp [common]
      simp [evalFuel, conditionRaised, branchRaised, falseNotTrue]
  case fixE =>
      intros environment body
      exact ⟨1, rfl⟩
  case matcher =>
      intros environment clauses
      exact ⟨1, rfl⟩
  case matchAll =>
      intros environment target targetValue matcher matcherValue pattern
        bindingGroups body bodyValues targetEval matcherEval matching bodiesEval
        targetIH matcherIH matchingIH bodiesIH
      rcases targetIH with ⟨targetFuel, targetSuccess⟩
      rcases matcherIH with ⟨matcherFuel, matcherSuccess⟩
      rcases matchingIH with ⟨matchingEvalFuel, searchFuel, searchSuccess⟩
      rcases bodiesIH with ⟨bodyFuel, bodiesSuccess⟩
      let common := max targetFuel
        (max matcherFuel (max matchingEvalFuel (max searchFuel bodyFuel)))
      have targetLe : targetFuel ≤ common := by
        exact Nat.le_max_left _ _
      have targetRaised := evalFuel_ok_of_le targetLe targetSuccess
      have matcherLe : matcherFuel ≤ common := by
        exact Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_max_right targetFuel _)
      have matcherRaised := evalFuel_ok_of_le matcherLe matcherSuccess
      have matchingEvalLe : matchingEvalFuel ≤ common := by
        exact Nat.le_trans
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right matcherFuel _))
          (Nat.le_max_right targetFuel _)
      have searchLe : searchFuel ≤ common := by
        exact Nat.le_trans
          (Nat.le_trans
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right matchingEvalFuel _))
            (Nat.le_max_right matcherFuel _))
          (Nat.le_max_right targetFuel _)
      have bodyLe : bodyFuel ≤ common := by
        exact Nat.le_trans
          (Nat.le_trans
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right matchingEvalFuel _))
            (Nat.le_max_right matcherFuel _))
          (Nat.le_max_right targetFuel _)
      have searchCallbackRaised := depthFirstFuel_step_mono
        (matchingStep_ok_mono
          (fun success => evalFuel_ok_of_le matchingEvalLe success))
        searchSuccess
      have searchRaised := depthFirstFuel_ok_add _ searchCallbackRaised
        (common - searchFuel)
      have searchAtCommon :
          searchMatchingFuel
            (combineAtomReducers (reduceBuiltinAtom (evalFuel common))
              (reduceMatcherAtom (evalFuel common))) common
            ⟨[⟨pattern, matcherValue, targetValue⟩], environment, []⟩ =
              .ok bindingGroups := by
        simpa [searchMatchingFuel, Nat.add_sub_of_le searchLe] using searchRaised
      have bodiesRaised := traverse_ok_mono
        (fun success => evalFuel_ok_of_le bodyLe success) bodiesSuccess
      refine ⟨common + 1, ?_⟩
      simp only [evalFuel, targetRaised, FuelResult.bind_ok, matcherRaised,
        searchPatternFuel, evaluationAtomReducer, searchAtCommon,
        bodiesRaised, FuelResult.map_ok]
  case matchFirst =>
      intros environment target targetValue matcher matcherValue arms result
        targetEval matcherEval armsEval targetIH matcherIH armsIH
      rcases targetIH with ⟨targetFuel, targetSuccess⟩
      rcases matcherIH with ⟨matcherFuel, matcherSuccess⟩
      rcases armsIH with ⟨armsEvalFuel, armsSearchFuel, armsSuccess⟩
      let common := max targetFuel
        (max matcherFuel (max armsEvalFuel armsSearchFuel))
      have targetLe : targetFuel ≤ common := by omega
      have matcherLe : matcherFuel ≤ common := by omega
      have armsEvalLe : armsEvalFuel ≤ common := by omega
      have armsSearchLe : armsSearchFuel ≤ common := by omega
      have targetRaised := evalFuel_ok_of_le targetLe targetSuccess
      have matcherRaised := evalFuel_ok_of_le matcherLe matcherSuccess
      have armsRaised :
          evalMatchFirstArmsFuel (evalFuel common) common environment
            targetValue matcherValue arms = .ok result := by
        exact evalMatchFirstArmsFuel_ok_mono
          (fun success => evalFuel_ok_of_le armsEvalLe success)
          (fun {pattern bindingGroups} searchResult => by
            have callbackRaised := depthFirstFuel_step_mono
              (matchingStep_ok_mono
                (fun success => evalFuel_ok_of_le armsEvalLe success))
              searchResult
            have fuelRaised := depthFirstFuel_ok_add _ callbackRaised
              (common - armsSearchFuel)
            simpa [searchPatternFuel, searchMatchingFuel, evaluationAtomReducer,
              Nat.add_sub_of_le armsSearchLe] using fuelRaised)
          armsSuccess
      refine ⟨common + 1, ?_⟩
      simp only [evalFuel, targetRaised, FuelResult.bind_ok, matcherRaised,
        armsRaised]
  case nil =>
      intro environment
      exact ⟨0, rfl⟩
  case cons =>
      intros environment head value tail values headEval tailEval headIH tailIH
      rcases headIH with ⟨headFuel, headSuccess⟩
      rcases tailIH with ⟨tailFuel, tailSuccess⟩
      let common := max headFuel tailFuel
      have headRaised := evalFuel_ok_of_le
        (Nat.le_max_left headFuel tailFuel) headSuccess
      have tailRaised := traverse_ok_mono
        (fun application => evalFuel_ok_of_le
          (Nat.le_max_right headFuel tailFuel) application)
        tailSuccess
      refine ⟨common, ?_⟩
      dsimp [common]
      simp only [FuelResult.traverse, headRaised, FuelResult.bind_ok,
        tailRaised, FuelResult.map_ok]
  case plain =>
      intros argument definitionEnvironment body result bodyEval bodyIH
      rcases bodyIH with ⟨fuel, success⟩
      exact ⟨fuel + 1, by simpa [applyFuel] using success⟩
  case recursive =>
      intros argument definitionEnvironment body result bodyEval bodyIH
      rcases bodyIH with ⟨fuel, success⟩
      exact ⟨fuel + 1, by simpa [applyFuel] using success⟩
  case nil =>
      intro function
      exact ⟨0, rfl⟩
  case cons =>
      intros function input output inputs outputs headApply tailApply headIH tailIH
      rcases headIH with ⟨headFuel, headSuccess⟩
      rcases tailIH with ⟨tailFuel, tailSuccess⟩
      let common := max headFuel tailFuel
      have headRaised := applyFuel_ok_of_le
        (Nat.le_max_left headFuel tailFuel) headSuccess
      have tailRaised := traverse_ok_mono
        (fun application => applyFuel_ok_of_le
          (Nat.le_max_right headFuel tailFuel) application)
        tailSuccess
      refine ⟨common, ?_⟩
      dsimp [common]
      simp only [FuelResult.traverse, headRaised, FuelResult.bind_ok,
        tailRaised, FuelResult.map_ok]
  case add =>
      intros left right
      exact ⟨0, rfl⟩
  case append =>
      intros left leftItems right rightItems leftEncoding rightEncoding
      exact ⟨0, by simp [evalPrimitive, leftEncoding, rightEncoding]⟩
  case member =>
      intros target items needle encoding
      exact ⟨0, by simp [evalPrimitive, encoding]⟩
  case deleteFirst =>
      intros target items needle encoding
      exact ⟨0, by simp [evalPrimitive, encoding]⟩
  case map =>
      intros target inputs function outputs encoding applications applicationsIH
      rcases applicationsIH with ⟨fuel, success⟩
      exact ⟨fuel, by simp [evalPrimitive, encoding, success]⟩
  case miss =>
      intros header target matcherEnvironment captureValues holes nextMatchers
        body mismatch
      exact ⟨0, .miss mismatch⟩
  case hit =>
      intros header target dataValues captureValues matcherEnvironment body
        decompositionValue decompositions nextMatchers matcherProduct matchers
        holes branches dataMatch bodyEval decompositionShape matcherEval
        matcherShape branchesBuilt bodyIH matcherIH
      rcases bodyIH with ⟨bodyFuel, bodySuccess⟩
      rcases matcherIH with ⟨matcherFuel, matcherSuccess⟩
      let common := max bodyFuel matcherFuel
      have bodyLe : bodyFuel ≤ common := Nat.le_max_left _ _
      have matcherLe : matcherFuel ≤ common := Nat.le_max_right _ _
      have bodyRaised := evalFuel_ok_of_le bodyLe bodySuccess
      have matcherRaised := evalFuel_ok_of_le matcherLe matcherSuccess
      exact ⟨common, .hit (ValueDataPatternMatches.complete dataMatch)
        bodyRaised decompositionShape matcherRaised matcherShape branchesBuilt⟩
  case nil =>
      intros matcherEnvironment captureValues holes nextMatchers target
      exact ⟨0, .nil⟩
  case hit =>
      intros matcherEnvironment captureValues holes nextMatchers target arm
        branches rest selected selectedIH
      rcases selectedIH with ⟨fuel, selectedAtFuel⟩
      exact ⟨fuel, .hit selectedAtFuel⟩
  case skip =>
      intros matcherEnvironment captureValues holes nextMatchers target arm rest
        result missed tail missedIH tailIH
      rcases missedIH with ⟨missedFuel, missedAtFuel⟩
      rcases tailIH with ⟨tailFuel, tailAtFuel⟩
      let common := max missedFuel tailFuel
      exact ⟨common,
        .skip
          (matcherArmDispatches_mono
            (fun success => evalFuel_ok_of_le (Nat.le_max_left _ _) success)
            missedAtFuel)
          (matcherArmsDispatch_mono
            (fun success => evalFuel_ok_of_le (Nat.le_max_right _ _) success)
            tailAtFuel)⟩
  case miss =>
      intros header pattern atomEnvironment matcherEnvironment target
        nextMatchers arms mismatch
      exact ⟨0, .miss mismatch⟩
  case matched =>
      intros header pattern dispatch atomEnvironment captureValues
        matcherEnvironment nextMatchers target arms result headerMatch
        capturesEval armsDispatch capturesIH armsIH
      rcases capturesIH with ⟨capturesFuel, capturesSuccess⟩
      rcases armsIH with ⟨armsFuel, armsAtFuel⟩
      let common := max capturesFuel armsFuel
      have capturesLe : capturesFuel ≤ common := Nat.le_max_left _ _
      have armsLe : armsFuel ≤ common := Nat.le_max_right _ _
      have capturesRaised := traverse_ok_mono
        (fun success => evalFuel_ok_of_le capturesLe success)
        capturesSuccess
      exact ⟨common, .matched headerMatch
        ((traverse_eq_ok_iff _ _ _).mp capturesRaised)
        (matcherArmsDispatch_mono
          (fun success => evalFuel_ok_of_le armsLe success)
          armsAtFuel)⟩
  case nil =>
      intros atomEnvironment matcherEnvironment pattern target
      exact ⟨0, .nil⟩
  case hit =>
      intros atomEnvironment matcherEnvironment pattern target clause branches
        rest selected selectedIH
      rcases selectedIH with ⟨fuel, selectedAtFuel⟩
      exact ⟨fuel, .hit selectedAtFuel⟩
  case skip =>
      intros atomEnvironment matcherEnvironment pattern target clause rest
        result missed tail missedIH tailIH
      rcases missedIH with ⟨missedFuel, missedAtFuel⟩
      rcases tailIH with ⟨tailFuel, tailAtFuel⟩
      let common := max missedFuel tailFuel
      exact ⟨common,
        .skip
          (matcherClauseDispatches_mono
            (fun success => evalFuel_ok_of_le (Nat.le_max_left _ _) success)
            missedAtFuel)
          (matcherClausesDispatch_mono
            (fun success => evalFuel_ok_of_le (Nat.le_max_right _ _) success)
            tailAtFuel)⟩
  case somethingWild =>
      intros environment target
      exact ⟨0, by rfl⟩
  case somethingVar =>
      intros environment target
      exact ⟨0, by rfl⟩
  case somethingValueSuccess =>
      intros environment expression actual target evaluated equal evaluatedIH
      rcases evaluatedIH with ⟨fuel, success⟩
      exact ⟨fuel, combineAtomReducers_primary_hit _ _
        (BuiltinAtomReduces.complete
          (.somethingValueSuccess success equal))⟩
  case somethingValueFailure =>
      intros environment expression actual target evaluated unequal evaluatedIH
      rcases evaluatedIH with ⟨fuel, success⟩
      exact ⟨fuel, combineAtomReducers_primary_hit _ _
        (BuiltinAtomReduces.complete
          (.somethingValueFailure success unequal))⟩
  case and =>
      intros environment left right matcher target
      exact ⟨0, combineAtomReducers_primary_hit _ _
        (BuiltinAtomReduces.complete .and)⟩
  case tuple =>
      intros patterns matchers targets atoms environment zipped
      exact ⟨0, combineAtomReducers_primary_hit _ _
        (BuiltinAtomReduces.complete (.tuple zipped))⟩
  case productSomethingVar =>
      intros environment matchers target
      exact ⟨0, by rfl⟩
  case productSomethingWild =>
      intros environment matchers target
      exact ⟨0, by rfl⟩
  case productSomethingValue =>
      intros environment expression matchers target
      exact ⟨0, by rfl⟩
  case matcher =>
      intros pattern environment matcherEnvironment target remaining branches
        original dispatchable clauses clausesIH
      rcases clausesIH with ⟨fuel, clausesAtFuel⟩
      have fallback :
          reduceMatcherAtom (evalFuel fuel) environment
            ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩ =
              .ok (.hit ⟨branches, []⟩) :=
        (reduceMatcherAtom_hit_iff _ _ _ _).mpr (.matcher clausesAtFuel)
      exact ⟨fuel, by
        rw [combineAtomReducers_primary_miss _ _
          (reduceBuiltinAtom_matcherV_miss _ _ _ _ _ _ _ dispatchable)]
        exact fallback⟩
  case nil =>
      exact ⟨0, 0, rfl⟩
  case yield =>
      intros rest answers environment bindings tail tailIH
      rcases tailIH with ⟨evaluationFuel, searchFuel, tailSuccess⟩
      refine ⟨evaluationFuel, searchFuel + 1, ?_⟩
      simp [depthFirstFuel, stepMatchingState, tailSuccess]
  case expand =>
      intros bindings environment atom reduction rest answers remaining
        reduced next reducedIH nextIH
      rcases reducedIH with ⟨atomFuel, atomSuccess⟩
      rcases nextIH with ⟨nextFuel, searchFuel, nextSuccess⟩
      let common := max atomFuel nextFuel
      have atomLe : atomFuel ≤ common := Nat.le_max_left _ _
      have nextLe : nextFuel ≤ common := Nat.le_max_right _ _
      have atomRaised := combinedAtom_hit_mono
        (fun success => evalFuel_ok_of_le atomLe success)
        atomSuccess
      have nextRaised := depthFirstFuel_step_mono
        (matchingStep_ok_mono
          (fun success => evalFuel_ok_of_le nextLe success))
        nextSuccess
      refine ⟨common, searchFuel + 1, ?_⟩
      simp only [depthFirstFuel, stepMatchingState, atomRaised,
        FuelResult.bind_ok]
      change depthFirstFuel
        (stepMatchingState
          (combineAtomReducers (reduceBuiltinAtom (evalFuel common))
            (reduceMatcherAtom (evalFuel common)))) searchFuel
        ((reduction.branches.map fun branch =>
          ⟨branch ++ remaining, environment,
            bindings ++ reduction.bindings⟩) ++ rest) = .ok answers
      exact nextRaised
  case nil =>
      intros environment body
      exact ⟨0, rfl⟩
  case cons =>
      intros bindings environment body value groups values head tail headIH tailIH
      rcases headIH with ⟨headFuel, headSuccess⟩
      rcases tailIH with ⟨tailFuel, tailSuccess⟩
      let common := max headFuel tailFuel
      have headLe : headFuel ≤ common := Nat.le_max_left _ _
      have tailLe : tailFuel ≤ common := Nat.le_max_right _ _
      have headRaised := evalFuel_ok_of_le headLe headSuccess
      have tailRaised := traverse_ok_mono
        (fun success => evalFuel_ok_of_le tailLe success)
        tailSuccess
      exact ⟨common, by
        simp [FuelResult.traverse, headRaised, tailRaised]⟩
  case hit =>
      intros matcher target environment bindings remaining result arm rest
        matching bodyEval matchingIH bodyIH
      rcases matchingIH with
        ⟨matchingEvalFuel, matchingSearchFuel, matchingSuccess⟩
      rcases bodyIH with ⟨bodyFuel, bodySuccess⟩
      let common := max matchingEvalFuel (max matchingSearchFuel bodyFuel)
      have matchingEvalLe : matchingEvalFuel ≤ common := by omega
      have matchingSearchLe : matchingSearchFuel ≤ common := by omega
      have bodyLe : bodyFuel ≤ common := by omega
      have callbackRaised := depthFirstFuel_step_mono
        (matchingStep_ok_mono
          (fun success => evalFuel_ok_of_le matchingEvalLe success))
        matchingSuccess
      have fuelRaised := depthFirstFuel_ok_add _ callbackRaised
        (common - matchingSearchFuel)
      have searchAtCommon :
          searchPatternFuel (evalFuel common) common environment arm.pattern
            matcher target = .ok (bindings :: remaining) := by
        simpa [searchPatternFuel, searchMatchingFuel, evaluationAtomReducer,
          Nat.add_sub_of_le matchingSearchLe] using fuelRaised
      have bodyAtCommon := evalFuel_ok_of_le bodyLe bodySuccess
      exact ⟨common, common, by
        simp [evalMatchFirstArmsFuel, searchAtCommon, bodyAtCommon]⟩
  case skip =>
      intros matcher target environment rest result arm matching tail
        matchingIH tailIH
      rcases matchingIH with
        ⟨matchingEvalFuel, matchingSearchFuel, matchingSuccess⟩
      rcases tailIH with ⟨tailEvalFuel, tailSearchFuel, tailSuccess⟩
      let common := max matchingEvalFuel
        (max matchingSearchFuel (max tailEvalFuel tailSearchFuel))
      have matchingEvalLe : matchingEvalFuel ≤ common := by omega
      have matchingSearchLe : matchingSearchFuel ≤ common := by omega
      have tailEvalLe : tailEvalFuel ≤ common := by omega
      have tailSearchLe : tailSearchFuel ≤ common := by omega
      have matchingCallbackRaised := depthFirstFuel_step_mono
        (matchingStep_ok_mono
          (fun success => evalFuel_ok_of_le matchingEvalLe success))
        matchingSuccess
      have matchingFuelRaised := depthFirstFuel_ok_add _ matchingCallbackRaised
        (common - matchingSearchFuel)
      have searchAtCommon :
          searchPatternFuel (evalFuel common) common environment arm.pattern
            matcher target = .ok [] := by
        simpa [searchPatternFuel, searchMatchingFuel, evaluationAtomReducer,
          Nat.add_sub_of_le matchingSearchLe] using matchingFuelRaised
      have tailAtCommon :
          evalMatchFirstArmsFuel (evalFuel common) common environment
            target matcher rest = .ok result := by
        exact evalMatchFirstArmsFuel_ok_mono
          (fun success => evalFuel_ok_of_le tailEvalLe success)
          (fun {pattern bindingGroups} searchResult => by
            have callbackRaised := depthFirstFuel_step_mono
              (matchingStep_ok_mono
                (fun success => evalFuel_ok_of_le tailEvalLe success))
              searchResult
            have fuelRaised := depthFirstFuel_ok_add _ callbackRaised
              (common - tailSearchFuel)
            simpa [searchPatternFuel, searchMatchingFuel, evaluationAtomReducer,
              Nat.add_sub_of_le tailSearchLe] using fuelRaised)
          tailSuccess
      exact ⟨common, common, by
        simp [evalMatchFirstArmsFuel, searchAtCommon, tailAtCommon]⟩
  case t => exact derivation

end TypePM.Runtime
