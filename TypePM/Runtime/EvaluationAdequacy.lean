import TypePM.Runtime.EvalFuel

/-!
# Adequacy of the fuel-bounded core evaluator

Successful executable evaluation produces a derivation of the independent
big-step relation.  The proof includes complete-value primitive dispatch and
the callback applications performed by `map`.
-/

namespace TypePM.Runtime

open FuelResult

private theorem traverses_to_evals
    {evaluate : Source.Expr → FuelResult Value}
    (sound : ∀ {expression value},
      evaluate expression = .ok value → Eval environment expression value)
    (traversal : Traverses evaluate expressions values) :
    Evals environment expressions values := by
  induction traversal with
  | nil => exact .nil
  | cons head tail ih => exact .cons (sound head) ih

private theorem traverses_to_appliesList
    {apply : Value → FuelResult Value}
    (sound : ∀ {input output},
      apply input = .ok output → Applies function input output)
    (traversal : Traverses apply inputs outputs) :
    AppliesList function inputs outputs := by
  induction traversal with
  | nil => exact .nil
  | cons head tail ih => exact .cons (sound head) ih

private theorem matcherArmDispatch_to_eval
    {evaluate : ValueEnvironment → Source.Expr → FuelResult Value}
    (sound : ∀ {environment expression value},
      evaluate environment expression = .ok value →
        Eval environment expression value)
    (dispatch : MatcherArmDispatches evaluate matcherEnvironment captureValues
      holes nextMatchers target arm result) :
    EvalMatcherArmDispatches matcherEnvironment captureValues holes
      nextMatchers target arm result := by
  cases dispatch with
  | miss mismatch => exact .miss mismatch
  | hit dataMatch bodyEval decompositionShape matcherEval matcherShape
      branchesBuilt =>
      exact .hit (matchValueDataPattern_sound dataMatch) (sound bodyEval)
        decompositionShape (sound matcherEval) matcherShape branchesBuilt

private theorem matcherArmsDispatch_to_eval
    {evaluate : ValueEnvironment → Source.Expr → FuelResult Value}
    (sound : ∀ {environment expression value},
      evaluate environment expression = .ok value →
        Eval environment expression value)
    (dispatch : MatcherArmsDispatch evaluate matcherEnvironment captureValues
      holes nextMatchers target arms result) :
    EvalMatcherArmsDispatch matcherEnvironment captureValues holes
      nextMatchers target arms result := by
  induction dispatch with
  | nil => exact .nil
  | hit selected => exact .hit (matcherArmDispatch_to_eval sound selected)
  | skip missed tail ih =>
      exact .skip (matcherArmDispatch_to_eval sound missed) ih

private theorem matcherClauseDispatch_to_eval
    {evaluate : ValueEnvironment → Source.Expr → FuelResult Value}
    (sound : ∀ {environment expression value},
      evaluate environment expression = .ok value →
        Eval environment expression value)
    (dispatch : MatcherClauseDispatches evaluate atomEnvironment
      matcherEnvironment pattern target clause result) :
    EvalMatcherClauseDispatches atomEnvironment matcherEnvironment pattern
      target clause result := by
  cases dispatch with
  | miss mismatch => exact .miss mismatch
  | matched headerMatch capturesEval armsDispatch =>
      exact .matched headerMatch
        (traverses_to_evals
          (fun success => sound success) capturesEval)
        (matcherArmsDispatch_to_eval sound armsDispatch)

private theorem matcherClausesDispatch_to_eval
    {evaluate : ValueEnvironment → Source.Expr → FuelResult Value}
    (sound : ∀ {environment expression value},
      evaluate environment expression = .ok value →
        Eval environment expression value)
    (dispatch : MatcherClausesDispatch evaluate atomEnvironment
      matcherEnvironment pattern target clauses result) :
    EvalMatcherClausesDispatch atomEnvironment matcherEnvironment pattern
      target clauses result := by
  induction dispatch with
  | nil => exact .nil
  | hit selected => exact .hit (matcherClauseDispatch_to_eval sound selected)
  | skip missed tail ih =>
      exact .skip (matcherClauseDispatch_to_eval sound missed) ih

private theorem builtinAtom_to_eval
    {evaluate : ValueEnvironment → Source.Expr → FuelResult Value}
    (sound : ∀ {environment expression value},
      evaluate environment expression = .ok value →
        Eval environment expression value)
    (reduced : BuiltinAtomReduces evaluate environment atom reduction) :
    EvalAtomReduces environment atom reduction := by
  cases reduced with
  | somethingWild => exact .somethingWild
  | somethingVar => exact .somethingVar
  | somethingValueSuccess evaluated equal =>
      exact .somethingValueSuccess (sound evaluated) equal
  | somethingValueFailure evaluated unequal =>
      exact .somethingValueFailure (sound evaluated) unequal
  | tuple zipped => exact .tuple zipped
  | productSomethingVar => exact .productSomethingVar
  | productSomethingWild => exact .productSomethingWild
  | productSomethingValue => exact .productSomethingValue

private theorem matcherAtom_to_eval
    {evaluate : ValueEnvironment → Source.Expr → FuelResult Value}
    (sound : ∀ {environment expression value},
      evaluate environment expression = .ok value →
        Eval environment expression value)
    (reduced : MatcherAtomReduces evaluate environment atom reduction) :
    EvalAtomReduces environment atom reduction := by
  cases reduced with
  | matcher clausesDispatch =>
      exact .matcher (matcherClausesDispatch_to_eval sound clausesDispatch)

private theorem combinedAtom_to_eval
    {evaluate : ValueEnvironment → Source.Expr → FuelResult Value}
    (sound : ∀ {environment expression value},
      evaluate environment expression = .ok value →
        Eval environment expression value)
    (success :
      combineAtomReducers (reduceBuiltinAtom evaluate)
          (reduceMatcherAtom evaluate) environment atom =
        .ok (.hit reduction)) :
    EvalAtomReduces environment atom reduction := by
  cases builtinResult : reduceBuiltinAtom evaluate environment atom with
  | timeout => simp [combineAtomReducers, builtinResult] at success
  | stuck => simp [combineAtomReducers, builtinResult] at success
  | ok outcome =>
      cases outcome with
      | hit builtinReduction =>
          simp [combineAtomReducers, builtinResult] at success
          subst builtinReduction
          exact builtinAtom_to_eval sound
            ((reduceBuiltinAtom_hit_iff _ _ _ _).mp builtinResult)
      | miss =>
          have matcherSuccess :
              reduceMatcherAtom evaluate environment atom =
                .ok (.hit reduction) := by
            simpa [combineAtomReducers, builtinResult] using success
          exact matcherAtom_to_eval sound
            ((reduceMatcherAtom_hit_iff _ _ _ _).mp matcherSuccess)

private theorem depthFirst_to_evalMatching
    {evaluate : ValueEnvironment → Source.Expr → FuelResult Value}
    (sound : ∀ {environment expression value},
      evaluate environment expression = .ok value →
        Eval environment expression value)
    (search : DepthFirst
      (stepMatchingState
        (combineAtomReducers (reduceBuiltinAtom evaluate)
          (reduceMatcherAtom evaluate))) states answers) :
    EvalMatchingSearch states answers := by
  induction search with
  | nil => exact .nil
  | yield head tail ih =>
      have stateStep := stepMatchingState_sound head
      cases stateStep with
      | yield => exact .yield ih
  | expand head next ih =>
      have stateStep := stepMatchingState_sound head
      cases stateStep with
      | expand reduced =>
          exact .expand (combinedAtom_to_eval sound reduced) ih

private theorem traverses_to_bindingGroups
    {evaluate : List Value → FuelResult Value}
    (sound : ∀ {bindings value},
      evaluate bindings = .ok value →
        Eval (bindings ++ environment) body value)
    (traversal : Traverses evaluate groups values) :
    EvalBindingGroups environment body groups values := by
  induction traversal with
  | nil => exact .nil
  | cons head tail ih => exact .cons (sound head) ih

theorem evalPrimitive_sound
    {apply : Value → Value → FuelResult Value}
    (applySound : ∀ {function input output},
      apply function input = .ok output → Applies function input output)
    {operation : PrimOp} {arguments : List Value} {result : Value}
    (success : evalPrimitive apply operation arguments = .ok result) :
    PrimitiveEvaluates operation arguments result := by
  cases operation with
  | add =>
      rcases arguments with _ | ⟨first, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨second, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · cases first <;> cases second <;> simp [evalPrimitive] at success
        subst result
        exact .add
      · simp [evalPrimitive] at success
  | append =>
      rcases arguments with _ | ⟨left, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨right, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · cases leftView : Value.viewList left <;>
          cases rightView : Value.viewList right <;>
          simp [evalPrimitive, leftView, rightView] at success
        subst result
        exact .append leftView rightView
      · simp [evalPrimitive] at success
  | member =>
      rcases arguments with _ | ⟨needle, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨target, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · cases targetView : Value.viewList target with
        | none => simp [evalPrimitive, targetView] at success
        | some items =>
            simp [evalPrimitive, targetView] at success
            subst result
            exact .member targetView
      · simp [evalPrimitive] at success
  | deleteFirst =>
      rcases arguments with _ | ⟨needle, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨target, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · cases targetView : Value.viewList target with
        | none => simp [evalPrimitive, targetView] at success
        | some items =>
            simp [evalPrimitive, targetView] at success
            subst result
            exact .deleteFirst targetView
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
            cases traversal : FuelResult.traverse (apply function) inputs with
            | timeout => simp [traversal] at success
            | stuck => simp [traversal] at success
            | ok outputs =>
                simp [traversal] at success
                subst result
                exact .map targetView
                  (traverses_to_appliesList
                    (fun application => applySound application)
                    ((traverse_eq_ok_iff _ _ _).mp traversal))
      · simp [evalPrimitive] at success

private theorem fuel_sound : ∀ fuel,
    (∀ {environment expression value},
      evalFuel fuel environment expression = .ok value →
        Eval environment expression value) ∧
    (∀ {function argument value},
      applyFuel fuel function argument = .ok value →
        Applies function argument value) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro environment expression value success
        simp [evalFuel] at success
      · intro function argument value success
        simp [applyFuel] at success
  | succ fuel ih =>
      rcases ih with ⟨evalSound, applySound⟩
      constructor
      · intro environment expression value success
        cases expression with
        | var index =>
            simp only [evalFuel] at success
            cases lookup : environment[index]? with
            | none => simp [lookup] at success
            | some found =>
                simp [lookup] at success
                subst value
                exact .var ((getElem?_eq_some_iff_lookup _ _ _).mp lookup)
        | lit literal =>
            simp [evalFuel] at success
            subst value
            exact .lit
        | something =>
            simp [evalFuel] at success
            subst value
            exact .something
        | lam body =>
            simp [evalFuel] at success
            subst value
            exact .lam
        | app function argument =>
            simp only [evalFuel] at success
            rw [bind_eq_ok_iff] at success
            rcases success with ⟨functionValue, functionResult, rest⟩
            rw [bind_eq_ok_iff] at rest
            rcases rest with ⟨argumentValue, argumentResult, application⟩
            exact .app (evalSound functionResult) (evalSound argumentResult)
              (applySound application)
        | tuple items =>
            simp only [evalFuel] at success
            rw [map_eq_ok_iff] at success
            rcases success with ⟨values, traversal, output⟩
            subst value
            exact .tuple
              (traverses_to_evals
                (fun result => evalSound result)
                ((traverse_eq_ok_iff _ _ _).mp traversal))
        | letE valueExpression body =>
            simp only [evalFuel] at success
            rw [bind_eq_ok_iff] at success
            rcases success with ⟨boundValue, boundResult, bodyResult⟩
            exact .letE (evalSound boundResult) (evalSound bodyResult)
        | ctor constructor arguments =>
            simp only [evalFuel] at success
            rw [map_eq_ok_iff] at success
            rcases success with ⟨values, traversal, output⟩
            subst value
            exact .ctor
              (traverses_to_evals
                (fun result => evalSound result)
                ((traverse_eq_ok_iff _ _ _).mp traversal))
        | prim operation arguments =>
            simp only [evalFuel] at success
            rw [bind_eq_ok_iff] at success
            rcases success with ⟨values, traversal, primitive⟩
            exact .prim
              (traverses_to_evals
                (fun result => evalSound result)
                ((traverse_eq_ok_iff _ _ _).mp traversal))
              (evalPrimitive_sound
                (fun application => applySound application) primitive)
        | ifE condition thenBranch elseBranch =>
            simp only [evalFuel] at success
            rw [bind_eq_ok_iff] at success
            rcases success with ⟨conditionValue, conditionResult, branchResult⟩
            cases conditionValue with
            | data constructor arguments =>
                cases arguments with
                | nil =>
                    by_cases isTrue : constructor = DataCtor.true
                    · subst constructor
                      simp at branchResult
                      exact .ifTrue (evalSound conditionResult)
                        (evalSound branchResult)
                    · by_cases isFalse : constructor = DataCtor.false
                      · subst constructor
                        simp [isTrue] at branchResult
                        exact .ifFalse (evalSound conditionResult)
                          (evalSound branchResult)
                      · simp [isTrue, isFalse] at branchResult
                | cons head tail => simp at branchResult
            | int literal => simp at branchResult
            | tuple items => simp at branchResult
            | closure kind closureEnvironment body => simp at branchResult
            | matcherV matcherEnvironment original remaining => simp at branchResult
            | something => simp at branchResult
        | fixE body =>
            simp [evalFuel] at success
            subst value
            exact .fixE
        | matcher clauses =>
            simp [evalFuel] at success
            subst value
            exact .matcher
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
            exact .matchAll (evalSound targetResult) (evalSound matcherResult)
              (depthFirst_to_evalMatching evalSound
                (searchMatchingFuel_sound _ searchResult))
              (traverses_to_bindingGroups
                (fun result => evalSound result)
                ((traverse_eq_ok_iff _ _ _).mp traversal))
        | matchFirst target matcher arms =>
            simp [evalFuel] at success
      · intro function argument value success
        cases function with
        | closure kind definitionEnvironment body =>
            cases kind with
            | plain =>
                simp only [applyFuel] at success
                exact .plain (evalSound success)
            | recursive =>
                simp only [applyFuel] at success
                exact .recursive (evalSound success)
        | int literal => simp [applyFuel] at success
        | data constructor arguments => simp [applyFuel] at success
        | tuple items => simp [applyFuel] at success
        | matcherV environment original remaining => simp [applyFuel] at success
        | something => simp [applyFuel] at success

theorem evalFuel_sound
    (success : evalFuel fuel environment expression = .ok value) :
    Eval environment expression value :=
  (fuel_sound fuel).1 success

theorem applyFuel_sound
    (success : applyFuel fuel function argument = .ok value) :
    Applies function argument value :=
  (fuel_sound fuel).2 success

end TypePM.Runtime
