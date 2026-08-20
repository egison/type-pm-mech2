import TypePM.Runtime.Evaluation
import TypePM.Runtime.FuelResult
import TypePM.Runtime.ClauseDispatch
import TypePM.Runtime.CombinedAtomReducer

/-!
# Fuel-bounded core evaluator

The evaluator follows the relational rules in `Evaluation.lean`.  One unit of
fuel exposes one expression/application layer; all children of that layer
receive the same remaining fuel.  Expression lists are evaluated from left to
right.  `timeout` therefore means only that the supplied depth bound was too
small, whereas malformed variables, applications, primitive calls and
conditions produce `stuck`.

`matchAll` and core `matchFirst` use the same remaining fuel for
target evaluation, matcher evaluation, matching search, every expression
evaluated by an atom rule, and every selected body.  This is a depth bound, not
a global step counter.  Matching search preserves source order and duplicate
branches.
-/

namespace TypePM.Runtime

open FuelResult

/-- The implemented built-in-before-matcher atom reducer for one evaluation
callback. -/
def evaluationAtomReducer
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value) :
    AtomReducer :=
  combineAtomReducers (reduceBuiltinAtom evaluate) (reduceMatcherAtom evaluate)

/-- Search one already evaluated target/matcher pair. -/
def searchPatternFuel
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (environment : ValueEnvironment)
    (pattern : Source.Pattern) (matcher target : Value) :
    FuelResult (List (List Value)) :=
  searchMatchingFuel (evaluationAtomReducer evaluate) fuel
    ⟨[⟨pattern, matcher, target⟩], environment, []⟩

/-- Execute the ordinary arms of Paper 1's single-result `match` in source
order.  Each arm performs exactly the ordered search used by `matchAll`.  An
empty result continues with the next arm; a nonempty result selects its first
binding group, including when later groups are duplicates. -/
def evalMatchFirstArmsFuel
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (environment : ValueEnvironment)
    (target matcher : Value) :
    List Source.MatchFirstArm → Source.Expr → FuelResult Value
  | [], fallback => evaluate environment fallback
  | arm :: rest, fallback =>
      FuelResult.bind
        (searchPatternFuel evaluate fuel environment arm.pattern matcher target)
        fun bindingGroups =>
          match bindingGroups with
          | [] => evalMatchFirstArmsFuel evaluate fuel environment target matcher
              rest fallback
          | bindings :: _ => evaluate (bindings ++ environment) arm.body

/-- Exact connection to the Paper 1 desugaring: one source arm runs the same
ordered search as `matchAll`, then chooses its first result; only an empty
result advances to the next source arm. -/
theorem evalMatchFirstArmsFuel_orderedMatchAll_firstResult :
    evalMatchFirstArmsFuel evaluate fuel environment target matcher (arm :: rest)
        fallback =
      FuelResult.bind
        (searchPatternFuel evaluate fuel environment arm.pattern matcher target)
        (fun bindingGroups =>
          match bindingGroups with
          | [] => evalMatchFirstArmsFuel evaluate fuel environment target matcher
              rest fallback
          | bindings :: _ => evaluate (bindings ++ environment) arm.body) :=
  rfl

/-- A nonempty search result is consumed exactly as `matchAll` would produce
it, except that only the first result body is evaluated.  The tail is neither
reordered nor deduplicated; it is deliberately ignored. -/
theorem evalMatchFirstArmsFuel_firstResult
    (search : searchPatternFuel evaluate fuel environment arm.pattern matcher target =
      .ok (bindings :: remaining)) :
    evalMatchFirstArmsFuel evaluate fuel environment target matcher (arm :: rest)
        fallback =
      evaluate (bindings ++ environment) arm.body := by
  simp [evalMatchFirstArmsFuel, search]

/-- An arm with no `matchAll` result is skipped, preserving source-arm order. -/
theorem evalMatchFirstArmsFuel_skip
    (search : searchPatternFuel evaluate fuel environment arm.pattern matcher target =
      .ok []) :
    evalMatchFirstArmsFuel evaluate fuel environment target matcher (arm :: rest)
        fallback =
      evalMatchFirstArmsFuel evaluate fuel environment target matcher rest
        fallback := by
  simp [evalMatchFirstArmsFuel, search]

/-- Exhausting the ordinary arms evaluates the explicit fallback in the
original environment, without any arm-local bindings. -/
@[simp] theorem evalMatchFirstArmsFuel_nil :
    evalMatchFirstArmsFuel evaluate fuel environment target matcher [] fallback =
      evaluate environment fallback :=
  rfl

/-- Complete-value primitive execution, parameterized only at the function
application point needed by `map`. -/
def evalPrimitive
    (apply : Value → Value → FuelResult Value) :
    PrimOp → List Value → FuelResult Value
  | .add, [.int left, .int right] => .ok (.int (left + right))
  | .append, [left, right] =>
      match Value.viewList left, Value.viewList right with
      | some leftItems, some rightItems =>
          .ok (Value.buildList (leftItems ++ rightItems))
      | _, _ => .stuck
  | .member, [needle, target] =>
      match Value.viewList target with
      | some items => .ok (Value.boolValue (Value.memberStructural needle items))
      | none => .stuck
  | .deleteFirst, [needle, target] =>
      match Value.viewList target with
      | some items =>
          .ok (Value.buildList (Value.deleteFirstStructural needle items))
      | none => .stuck
  | .map, [function, target] =>
      match Value.viewList target with
      | some inputs =>
          FuelResult.map Value.buildList
            (FuelResult.traverse (apply function) inputs)
      | none => .stuck
  | .pairFirst, arguments =>
      match arguments with
      | [.tuple [first, _second]] => .ok first
      | _ => .stuck
  | .pairSecond, arguments =>
      match arguments with
      | [.tuple [_first, second]] => .ok second
      | _ => .stuck
  | _, _ => .stuck

mutual

  /-- Fuel-bounded call-by-value expression evaluation. -/
  def evalFuel : Nat → ValueEnvironment → Source.Expr → FuelResult Value
    | 0, _, _ => .timeout
    | fuel + 1, environment, expression =>
        match expression with
        | .var index =>
            match environment[index]? with
            | some value => .ok value
            | none => .stuck
        | .lit literal => .ok (.int literal)
        | .something => .ok .something
        | .lam body => .ok (Value.plainClosure environment body)
        | .app function argument =>
            FuelResult.bind (evalFuel fuel environment function) fun functionValue =>
              FuelResult.bind (evalFuel fuel environment argument) fun argumentValue =>
                applyFuel fuel functionValue argumentValue
        | .tuple items =>
            FuelResult.map Value.tuple
              (FuelResult.traverse (evalFuel fuel environment) items)
        | .letE valueExpression body =>
            FuelResult.bind (evalFuel fuel environment valueExpression) fun value =>
              evalFuel fuel (value :: environment) body
        | .ctor constructor arguments =>
            FuelResult.map (Value.data constructor)
              (FuelResult.traverse (evalFuel fuel environment) arguments)
        | .prim operation arguments =>
            FuelResult.bind
              (FuelResult.traverse (evalFuel fuel environment) arguments)
              (evalPrimitive (applyFuel fuel) operation)
        | .ifE condition thenBranch elseBranch =>
            FuelResult.bind (evalFuel fuel environment condition) fun conditionValue =>
              match conditionValue with
              | .data constructor [] =>
                  if constructor = DataCtor.true then
                    evalFuel fuel environment thenBranch
                  else if constructor = DataCtor.false then
                    evalFuel fuel environment elseBranch
                  else
                    .stuck
              | _ => .stuck
        | .fixE body => .ok (Value.recursiveClosure environment body)
        | .matcher clauses => .ok (Value.matcherClosure environment clauses)
        | .matchAll target matcher pattern body =>
            FuelResult.bind (evalFuel fuel environment target) fun targetValue =>
              FuelResult.bind (evalFuel fuel environment matcher) fun matcherValue =>
                FuelResult.bind
                  (searchPatternFuel (evalFuel fuel) fuel environment pattern
                    matcherValue targetValue)
                  fun bindingGroups =>
                    FuelResult.map Value.buildList
                      (FuelResult.traverse
                        (fun bindings =>
                          evalFuel fuel (bindings ++ environment) body)
                        bindingGroups)
        | .matchFirst target matcher arms fallback =>
            FuelResult.bind (evalFuel fuel environment target) fun targetValue =>
              FuelResult.bind (evalFuel fuel environment matcher) fun matcherValue =>
                evalMatchFirstArmsFuel (evalFuel fuel) fuel environment
                  targetValue matcherValue arms fallback

  /-- Fuel-bounded application.  The recursive closure layout is argument at
  index zero followed by self at index one. -/
  def applyFuel : Nat → Value → Value → FuelResult Value
    | 0, _, _ => .timeout
    | fuel + 1, .closure .plain definitionEnvironment body, argument =>
        evalFuel fuel (argument :: definitionEnvironment) body
    | fuel + 1, closure@(.closure .recursive definitionEnvironment body), argument =>
        evalFuel fuel (argument :: closure :: definitionEnvironment) body
    | _ + 1, _, _ => .stuck

end

end TypePM.Runtime
