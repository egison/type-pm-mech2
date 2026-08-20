import TypePM.Runtime.EvaluationCompleteness

/-!
# Monotonicity of completed fuel results

Increasing the depth bound may refine `timeout` to another result, but it
cannot change a completed `ok` or `stuck` result.  The approximation relation
below packages that fact compositionally for expression evaluation, matcher
callbacks, ordered clause dispatch, and matching search.
-/

namespace TypePM.Runtime

namespace FuelResult

/-- A larger fuel run may resolve a timeout; completed results are fixed. -/
inductive Approximates : FuelResult α → FuelResult α → Prop where
  | timeout (later : FuelResult α) : Approximates .timeout later
  | stuck : Approximates .stuck .stuck
  | ok (value : α) : Approximates (.ok value) (.ok value)

namespace Approximates

@[simp] theorem refl (result : FuelResult α) : Approximates result result := by
  cases result <;> constructor

theorem map {before after : FuelResult α}
    (related : Approximates before after) (function : α → β) :
    Approximates (FuelResult.map function before)
      (FuelResult.map function after) := by
  cases related <;> constructor

theorem bind
    {before after : FuelResult α}
    {beforeNext afterNext : α → FuelResult β}
    (related : Approximates before after)
    (nextRelated : ∀ value, Approximates (beforeNext value) (afterNext value)) :
    Approximates (FuelResult.bind before beforeNext)
      (FuelResult.bind after afterNext) := by
  cases related with
  | timeout later => exact .timeout _
  | stuck => exact .stuck
  | ok value => exact nextRelated value

theorem traverse
    (pointwise : ∀ input, Approximates (before input) (after input)) :
    ∀ inputs, Approximates (FuelResult.traverse before inputs)
      (FuelResult.traverse after inputs)
  | [] => .ok []
  | input :: inputs =>
      bind (pointwise input) (fun output =>
        map (traverse pointwise inputs) (output :: ·))

theorem stuck_eq (related : Approximates .stuck later) : later = .stuck := by
  cases related
  rfl

theorem ok_eq (related : Approximates (.ok value) later) :
    later = .ok value := by
  cases related
  rfl

end Approximates

end FuelResult

open FuelResult

private theorem firstHit_approximates
    (pointwise : ∀ candidate, Approximates (before candidate) (after candidate)) :
  ∀ candidates, Approximates (firstHit before candidates)
      (firstHit after candidates)
  | [] => by
      simp only [firstHit]
      exact .ok DispatchResult.miss
  | candidate :: candidates => by
      simp only [firstHit]
      exact (pointwise candidate).bind (fun outcome => by
        cases outcome with
        | hit result => exact .ok (DispatchResult.hit result)
        | miss => exact firstHit_approximates pointwise candidates)

private theorem evalPrimitive_approximates
    (application : ∀ function argument,
      Approximates (before function argument) (after function argument))
    (operation : PrimOp) (arguments : List Value) :
    Approximates (evalPrimitive before operation arguments)
      (evalPrimitive after operation arguments) := by
  cases operation with
  | add =>
      rcases arguments with _ | ⟨first, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨second, tail⟩
      · simp [evalPrimitive]
      rcases tail with _ | ⟨extra, tail⟩
      · cases first <;> cases second <;> exact Approximates.refl _
      · simp [evalPrimitive]
  | append =>
      rcases arguments with _ | ⟨left, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨right, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨extra, tail⟩
      · exact Approximates.refl _
      · exact .stuck
  | member =>
      rcases arguments with _ | ⟨needle, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨target, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨extra, tail⟩
      · exact Approximates.refl _
      · exact .stuck
  | deleteFirst =>
      rcases arguments with _ | ⟨needle, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨target, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨extra, tail⟩
      · exact Approximates.refl _
      · exact .stuck
  | pairFirst =>
      simp [evalPrimitive]
  | pairSecond =>
      simp [evalPrimitive]
  | map =>
      rcases arguments with _ | ⟨function, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨target, tail⟩
      · exact .stuck
      rcases tail with _ | ⟨extra, tail⟩
      · cases targetView : Value.viewList target with
        | none => simp only [evalPrimitive, targetView]; exact .stuck
        | some inputs =>
            simp only [evalPrimitive, targetView]
            exact Approximates.map (Approximates.traverse
              (fun input => application function input) inputs) Value.buildList
      · exact .stuck

private theorem tryMatcherArm_approximates
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (matcherEnvironment captureValues : ValueEnvironment)
    (holes : List Source.Pattern) (nextMatchers : Source.Expr)
    (target : Value) (arm : Source.MatcherArm) :
    Approximates
      (tryMatcherArm before matcherEnvironment captureValues holes
        nextMatchers target arm)
      (tryMatcherArm after matcherEnvironment captureValues holes
        nextMatchers target arm) := by
  rcases arm with ⟨header, body⟩
  simp only [tryMatcherArm]
  cases matched : matchValueDataPattern header target with
  | none => exact .ok DispatchResult.miss
  | some dataValues =>
      exact (evaluation
        (dataValues ++ captureValues ++ matcherEnvironment) body).bind
          (fun decompositionValue => by
            cases decompositionShape : decodeDecompositions holes.length decompositionValue with
            | none => exact .stuck
            | some decompositions =>
                exact (evaluation (captureValues ++ matcherEnvironment)
                  nextMatchers).bind (fun matcherProduct => by
                    cases matcherShape : decodeProduct holes.length matcherProduct with
                    | none => exact .stuck
                    | some matchers =>
                        cases branchShape : buildMatchingBranches holes matchers decompositions with
                        | none => simp only [branchShape]; exact .stuck
                        | some branches =>
                            simp only [branchShape]
                            exact .ok (DispatchResult.hit branches)))

private theorem tryMatcherClause_approximates
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (pattern : Source.Pattern) (target : Value) (clause : Source.MatcherClause) :
    Approximates
      (tryMatcherClause before atomEnvironment matcherEnvironment pattern target clause)
      (tryMatcherClause after atomEnvironment matcherEnvironment pattern target clause) := by
  rcases clause with ⟨header, nextMatchers, arms⟩
  simp only [tryMatcherClause]
  cases inspectPatternPattern header pattern with
  | none => exact .ok DispatchResult.miss
  | some dispatch =>
      exact (Approximates.traverse
        (fun expression => evaluation atomEnvironment expression)
        dispatch.captures).bind (fun captureValues =>
          Approximates.map (firstHit_approximates
            (fun arm => tryMatcherArm_approximates evaluation
              matcherEnvironment captureValues dispatch.holes nextMatchers
              target arm) arms) closeMatcherArmsResult)

private theorem dispatchMatcherClauses_approximates
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (clauses : List Source.MatcherClause) (pattern : Source.Pattern)
    (target : Value) :
    Approximates
      (dispatchMatcherClauses before atomEnvironment matcherEnvironment clauses
        pattern target)
      (dispatchMatcherClauses after atomEnvironment matcherEnvironment clauses
        pattern target) :=
  firstHit_approximates
    (fun clause => tryMatcherClause_approximates evaluation atomEnvironment
      matcherEnvironment pattern target clause) clauses

private theorem reduceMatcherAtom_approximates
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (environment : ValueEnvironment) (atom : MatchingAtom) :
    Approximates (reduceMatcherAtom before environment atom)
      (reduceMatcherAtom after environment atom) := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases matcher with
  | matcherV matcherEnvironment original remaining =>
      exact Approximates.map (dispatchMatcherClauses_approximates evaluation environment
        matcherEnvironment remaining pattern target) clauseResultToAtomReduction
  | int | data | tuple | closure | something => exact .ok DispatchResult.miss

private theorem reduceBuiltinAtom_approximates
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (environment : ValueEnvironment) (atom : MatchingAtom) :
    Approximates (reduceBuiltinAtom before environment atom)
      (reduceBuiltinAtom after environment atom) := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern <;> cases matcher <;> cases target <;>
    simp only [reduceBuiltinAtom] <;>
    first
    | exact Approximates.refl _
    | exact Approximates.map (evaluation environment _) _

private theorem evaluationAtomReducer_approximates
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (environment : ValueEnvironment) (atom : MatchingAtom) :
    Approximates (evaluationAtomReducer before environment atom)
      (evaluationAtomReducer after environment atom) := by
  unfold evaluationAtomReducer combineAtomReducers
  exact (reduceBuiltinAtom_approximates evaluation environment atom).bind
    (fun outcome => by
      cases outcome with
      | hit reduction => exact .ok (DispatchResult.hit reduction)
      | miss => exact reduceMatcherAtom_approximates evaluation environment atom)

private theorem stepMatchingState_approximates
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (state : MatchingState) :
    Approximates
      (stepMatchingState (evaluationAtomReducer before) state)
      (stepMatchingState (evaluationAtomReducer after) state) := by
  rcases state with ⟨work, environment, bindings⟩
  cases work with
  | nil => exact .ok (SearchStep.yield bindings)
  | cons atom remaining =>
      simp only [stepMatchingState]
      exact (evaluationAtomReducer_approximates evaluation
        (bindings ++ environment) atom).bind (fun outcome => by
          cases outcome with
          | miss => exact .stuck
          | hit reduction => exact .ok (SearchStep.expand
              (MatchingState.successors
                ⟨atom :: remaining, environment, bindings⟩
                remaining reduction)))

private theorem depthFirstFuel_approximates_succ
    (stepRelated : ∀ state, Approximates (before state) (after state)) :
    ∀ fuel states,
      Approximates (depthFirstFuel before fuel states)
        (depthFirstFuel after (fuel + 1) states) := by
  intro fuel
  induction fuel with
  | zero =>
      intro states
      cases states with
      | nil => exact .ok []
      | cons state rest => exact .timeout _
  | succ fuel induction =>
      intro states
      cases states with
      | nil => exact .ok []
      | cons state rest =>
          simp only [depthFirstFuel]
          exact (stepRelated state).bind (fun observation => by
            cases observation with
            | yield answer => exact Approximates.map (induction rest) (answer :: ·)
            | expand successors => exact induction (successors ++ rest))

private theorem searchPatternFuel_approximates_succ
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (fuel : Nat) (environment : ValueEnvironment) (pattern : Source.Pattern)
    (matcher target : Value) :
    Approximates (searchPatternFuel before fuel environment pattern matcher target)
      (searchPatternFuel after (fuel + 1) environment pattern matcher target) :=
  depthFirstFuel_approximates_succ
    (fun state => stepMatchingState_approximates evaluation state) fuel _

private theorem evalMatchFirstArmsFuel_approximates_succ
    (evaluation : ∀ environment expression,
      Approximates (before environment expression)
        (after environment expression))
    (fuel : Nat) (environment : ValueEnvironment) (target matcher : Value)
    (arms : List Source.MatchFirstArm) (fallback : Source.Expr) :
      Approximates
        (evalMatchFirstArmsFuel before fuel environment target matcher arms fallback)
        (evalMatchFirstArmsFuel after (fuel + 1) environment target matcher arms fallback) := by
  induction arms with
  | nil => simpa only [evalMatchFirstArmsFuel] using evaluation environment fallback
  | cons arm arms induction =>
      simp only [evalMatchFirstArmsFuel]
      exact (searchPatternFuel_approximates_succ evaluation fuel environment
        arm.pattern matcher target).bind (fun bindingGroups => by
          cases bindingGroups with
          | nil => exact induction
          | cons bindings remaining =>
              simpa only using evaluation (bindings ++ environment) arm.body)

private theorem fuel_approximates_succ : ∀ fuel,
    (∀ environment expression,
      Approximates (evalFuel fuel environment expression)
        (evalFuel (fuel + 1) environment expression)) ∧
    (∀ function argument,
      Approximates (applyFuel fuel function argument)
        (applyFuel (fuel + 1) function argument)) := by
  intro fuel
  induction fuel with
  | zero =>
      exact ⟨fun _ _ => .timeout _, fun _ _ => .timeout _⟩
  | succ fuel induction =>
      rcases induction with ⟨evalStep, applyStep⟩
      constructor
      · intro environment expression
        cases expression with
        | var index =>
            simp only [evalFuel]
            exact Approximates.refl _
        | lit literal =>
            simp only [evalFuel]
            exact .ok _
        | something =>
            simp only [evalFuel]
            exact .ok _
        | lam body =>
            simp only [evalFuel]
            exact .ok _
        | app function argument =>
            simp only [evalFuel]
            exact (evalStep environment function).bind (fun functionValue =>
              (evalStep environment argument).bind (fun argumentValue =>
                applyStep functionValue argumentValue))
        | tuple items =>
            simp only [evalFuel]
            exact (Approximates.traverse
              (fun item => evalStep environment item) items).map Value.tuple
        | letE value body =>
            simp only [evalFuel]
            exact (evalStep environment value).bind
              (fun bound => evalStep (bound :: environment) body)
        | ctor constructor arguments =>
            simp only [evalFuel]
            exact (Approximates.traverse
              (fun argument => evalStep environment argument) arguments).map
                (Value.data constructor)
        | prim operation arguments =>
            simp only [evalFuel]
            exact (Approximates.traverse
              (fun argument => evalStep environment argument) arguments).bind
                (fun values => evalPrimitive_approximates
                  (fun function argument => applyStep function argument)
                  operation values)
        | ifE condition thenBranch elseBranch =>
            simp only [evalFuel]
            exact (evalStep environment condition).bind (fun conditionValue => by
              cases conditionValue with
              | data constructor arguments =>
                  cases arguments with
                  | nil =>
                      by_cases isTrue : constructor = DataCtor.true
                      · subst constructor
                        exact evalStep environment thenBranch
                      · by_cases isFalse : constructor = DataCtor.false
                        · subst constructor
                          have falseNotTrue :
                              DataCtor.false ≠ DataCtor.true := by decide
                          simp only [if_neg falseNotTrue]
                          exact evalStep environment elseBranch
                        · simp [isTrue, isFalse]
                  | cons head tail => exact .stuck
              | int | tuple | closure | matcherV | something => exact .stuck)
        | fixE body =>
            simp only [evalFuel]
            exact .ok _
        | matcher clauses =>
            simp only [evalFuel]
            exact .ok _
        | matchAll target matcher pattern body =>
            simp only [evalFuel]
            exact (evalStep environment target).bind (fun targetValue =>
              (evalStep environment matcher).bind (fun matcherValue =>
                (searchPatternFuel_approximates_succ
                  (fun childEnvironment childExpression =>
                    evalStep childEnvironment childExpression)
                  fuel environment pattern matcherValue targetValue).bind
                    (fun bindingGroups =>
                      (Approximates.traverse
                        (fun bindings => evalStep (bindings ++ environment) body)
                        bindingGroups).map Value.buildList)))
        | matchFirst target matcher arms fallback =>
            simp only [evalFuel]
            exact (evalStep environment target).bind (fun targetValue =>
              (evalStep environment matcher).bind (fun matcherValue =>
                evalMatchFirstArmsFuel_approximates_succ
                  (fun childEnvironment childExpression =>
                    evalStep childEnvironment childExpression)
                  fuel environment targetValue matcherValue arms fallback))
      · intro function argument
        cases function with
        | closure kind environment body =>
            cases kind with
            | plain =>
                simp only [applyFuel]
                exact evalStep (argument :: environment) body
            | recursive =>
                simp only [applyFuel]
                exact evalStep
                  (argument :: Value.recursiveClosure environment body :: environment)
                  body
        | int literal => simp only [applyFuel]; exact .stuck
        | data constructor arguments => simp only [applyFuel]; exact .stuck
        | tuple items => simp only [applyFuel]; exact .stuck
        | matcherV matcherEnvironment original remaining =>
            simp only [applyFuel]
            exact .stuck
        | something => simp only [applyFuel]; exact .stuck

theorem evalFuel_approximates_succ :
    Approximates (evalFuel fuel environment expression)
      (evalFuel (fuel + 1) environment expression) :=
  (fuel_approximates_succ fuel).1 environment expression

theorem applyFuel_approximates_succ :
    Approximates (applyFuel fuel function argument)
      (applyFuel (fuel + 1) function argument) :=
  (fuel_approximates_succ fuel).2 function argument

theorem evalFuel_stuck_add
    (stuck : evalFuel fuel environment expression = .stuck) (extra : Nat) :
    evalFuel (fuel + extra) environment expression = .stuck := by
  induction extra with
  | zero => simpa
  | succ extra induction =>
      rw [Nat.add_succ]
      have related := evalFuel_approximates_succ (fuel := fuel + extra)
        (environment := environment) (expression := expression)
      rw [induction] at related
      exact related.stuck_eq

theorem applyFuel_stuck_add
    (stuck : applyFuel fuel function argument = .stuck) (extra : Nat) :
    applyFuel (fuel + extra) function argument = .stuck := by
  induction extra with
  | zero => simpa
  | succ extra induction =>
      rw [Nat.add_succ]
      have related := applyFuel_approximates_succ (fuel := fuel + extra)
        (function := function) (argument := argument)
      rw [induction] at related
      exact related.stuck_eq

theorem evalFuel_stuck_of_le
    (le : firstFuel ≤ secondFuel)
    (stuck : evalFuel firstFuel environment expression = .stuck) :
    evalFuel secondFuel environment expression = .stuck := by
  rw [← Nat.add_sub_of_le le]
  exact evalFuel_stuck_add stuck _

theorem applyFuel_stuck_of_le
    (le : firstFuel ≤ secondFuel)
    (stuck : applyFuel firstFuel function argument = .stuck) :
    applyFuel secondFuel function argument = .stuck := by
  rw [← Nat.add_sub_of_le le]
  exact applyFuel_stuck_add stuck _

/-- Eventual success rules out `stuck` at every smaller or larger fuel.
Smaller runs may still time out. -/
theorem evalFuel_neverStuck_of_eventual_success
    (success : evalFuel successfulFuel environment expression = .ok value)
    (fuel : Nat) :
    (evalFuel fuel environment expression).NotStuck := by
  cases result : evalFuel fuel environment expression with
  | timeout => trivial
  | ok value => trivial
  | stuck =>
      by_cases le : fuel ≤ successfulFuel
      · have raised := evalFuel_stuck_of_le le result
        rw [success] at raised
        contradiction
      · have successRaised := evalFuel_ok_of_le (Nat.le_of_not_ge le) success
        rw [result] at successRaised
        contradiction

/-- Eventual successful application likewise rules out `stuck` at every
smaller or larger fuel. -/
theorem applyFuel_neverStuck_of_eventual_success
    (success : applyFuel successfulFuel function argument = .ok value)
    (fuel : Nat) :
    (applyFuel fuel function argument).NotStuck := by
  cases result : applyFuel fuel function argument with
  | timeout => trivial
  | ok value => trivial
  | stuck =>
      by_cases le : fuel ≤ successfulFuel
      · have raised := applyFuel_stuck_of_le le result
        rw [success] at raised
        contradiction
      · have successRaised := applyFuel_ok_of_le (Nat.le_of_not_ge le) success
        rw [result] at successRaised
        contradiction

end TypePM.Runtime
