import TypePM.Runtime.EvalFuel

/-!
# Trace-preserving fuel evaluator

`evalFuelTraced` is a conservative extension of `evalFuel`.  Its first
projection is definitionally the existing evaluator result; its second
projection records every bounded DFS call issued by expression evaluation,
including calls made by evaluator callbacks inside matching search, in
execution order.

The trace event deliberately carries no `Pattern.MNodeFree` proof.  Runtime
evaluation accepts the complete source syntax and cannot manufacture a
static fragment proof.  The source-side origin bridge combines an event with
the retained M4 pattern evidence before constructing
`BoundedDfsMatchingSearchTask`.

The matching evaluator itself is unchanged.  A parallel trace interpreter
mirrors its control flow and concatenates the traces of exactly those
callbacks that were reached before success, timeout, or stuck.
-/

namespace TypePM.Runtime

/-- Runtime data present at every `searchPatternFuel` invocation. -/
structure MatchingSearchTraceEvent where
  fuel : Nat
  environment : ValueEnvironment
  pattern : Source.Pattern
  matcher : Value
  target : Value

/-- Trace a left-to-right traversal.  A failed head was evaluated and hence
contributes its trace; later elements were not evaluated. -/
def traceTraverse
    (evaluate : α → FuelResult β)
    (trace : α → List MatchingSearchTraceEvent) :
    List α → List MatchingSearchTraceEvent
  | [] => []
  | item :: items =>
      let headTrace := trace item
      match evaluate item with
      | .ok _ => headTrace ++ traceTraverse evaluate trace items
      | .timeout | .stuck => headTrace

/-- Trace callback applications performed by primitive `map`. -/
def evalPrimitiveTrace
    (apply : Value → Value → FuelResult Value)
    (applyTrace : Value → Value → List MatchingSearchTraceEvent) :
    PrimOp → List Value → List MatchingSearchTraceEvent
  | .map, [function, target] =>
      match Value.viewList target with
      | some inputs =>
          traceTraverse (apply function) (applyTrace function) inputs
      | none => []
  | _, _ => []

/-- Trace a source-ordered first-hit dispatch.  A normal miss advances to the
tail; a hit, timeout, or stuck result stops after the reached candidate. -/
def firstHitTrace
    (run : Candidate → FuelResult (DispatchResult Result))
    (trace : Candidate → List MatchingSearchTraceEvent) :
    List Candidate → List MatchingSearchTraceEvent
  | [] => []
  | candidate :: rest =>
      let headTrace := trace candidate
      match run candidate with
      | .ok .miss => headTrace ++ firstHitTrace run trace rest
      | .ok (.hit _) | .timeout | .stuck => headTrace

/-- Callback trace of the syntax-directed built-in atom reducer. -/
def reduceBuiltinAtomTrace
    (_evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (trace : ValueEnvironment → Source.Expr →
      List MatchingSearchTraceEvent)
    (environment : ValueEnvironment) (atom : MatchingAtom) :
    List MatchingSearchTraceEvent :=
  match atom.pattern, atom.matcher, atom.target with
  | .value expression, .something, _ => trace environment expression
  | _, _, _ => []

/-- Callback trace of one reached user-matcher arm. -/
def tryMatcherArmTrace
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (trace : ValueEnvironment → Source.Expr →
      List MatchingSearchTraceEvent)
    (matcherEnvironment captureValues : ValueEnvironment)
    (holes : List Source.Pattern) (nextMatchers : Source.Expr)
    (target : Value) : Source.MatcherArm → List MatchingSearchTraceEvent
  | .mk header body =>
      match matchValueDataPattern header target with
      | none => []
      | some dataValues =>
          let bodyEnvironment :=
            dataValues ++ captureValues ++ matcherEnvironment
          let bodyTrace := trace bodyEnvironment body
          match evaluate bodyEnvironment body with
          | .ok decompositionValue =>
              match decodeDecompositions holes.length decompositionValue with
              | none => bodyTrace
              | some _ =>
                  bodyTrace ++ trace (captureValues ++ matcherEnvironment)
                    nextMatchers
          | .timeout | .stuck => bodyTrace

/-- Callback trace of one reached matcher clause. -/
def tryMatcherClauseTrace
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (trace : ValueEnvironment → Source.Expr →
      List MatchingSearchTraceEvent)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (pattern : Source.Pattern) (target : Value) :
    Source.MatcherClause → List MatchingSearchTraceEvent
  | .mk header nextMatchers arms =>
      match inspectPatternPattern header pattern with
      | none => []
      | some dispatch =>
          let capturesTrace := traceTraverse (evaluate atomEnvironment)
            (trace atomEnvironment) dispatch.captures
          match FuelResult.traverse (evaluate atomEnvironment)
              dispatch.captures with
          | .ok captureValues =>
              capturesTrace ++ firstHitTrace
                (tryMatcherArm evaluate matcherEnvironment captureValues
                  dispatch.holes nextMatchers target)
                (tryMatcherArmTrace evaluate trace matcherEnvironment
                  captureValues dispatch.holes nextMatchers target)
                arms
          | .timeout | .stuck => capturesTrace

/-- Callback trace of source-ordered user-matcher clause dispatch. -/
def reduceMatcherAtomTrace
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (trace : ValueEnvironment → Source.Expr →
      List MatchingSearchTraceEvent)
    (atomEnvironment : ValueEnvironment) (atom : MatchingAtom) :
    List MatchingSearchTraceEvent :=
  match atom.matcher with
  | .matcherV matcherEnvironment _ remaining =>
      firstHitTrace
        (tryMatcherClause evaluate atomEnvironment matcherEnvironment
          atom.pattern atom.target)
        (tryMatcherClauseTrace evaluate trace atomEnvironment
          matcherEnvironment atom.pattern atom.target)
        remaining
  | _ => []

/-- Callback trace of the built-in-before-user combined atom reducer. -/
def evaluationAtomReducerTrace
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (trace : ValueEnvironment → Source.Expr →
      List MatchingSearchTraceEvent)
    (environment : ValueEnvironment) (atom : MatchingAtom) :
    List MatchingSearchTraceEvent :=
  let builtinTrace := reduceBuiltinAtomTrace evaluate trace environment atom
  match reduceBuiltinAtom evaluate environment atom with
  | .ok .miss =>
      builtinTrace ++ reduceMatcherAtomTrace evaluate trace environment atom
  | .ok (.hit _) | .timeout | .stuck => builtinTrace

/-- Callback trace emitted while stepping one matching state. -/
def stepMatchingStateTrace
    (reduceTrace : ValueEnvironment → MatchingAtom →
      List MatchingSearchTraceEvent)
    (state : MatchingState) : List MatchingSearchTraceEvent :=
  match state.work with
  | [] => []
  | atom :: _ => reduceTrace (state.bindings ++ state.environment) atom

/-- Trace the exact prefix visited by bounded ordered depth-first search. -/
def depthFirstFuelTrace
    (step : State → FuelResult (SearchStep State Answer))
    (stepTrace : State → List MatchingSearchTraceEvent) :
    Nat → List State → List MatchingSearchTraceEvent
  | _, [] => []
  | 0, _ :: _ => []
  | fuel + 1, state :: rest =>
      let headTrace := stepTrace state
      match step state with
      | .ok (.yield _) =>
          headTrace ++ depthFirstFuelTrace step stepTrace fuel rest
      | .ok (.expand successors) =>
          headTrace ++ depthFirstFuelTrace step stepTrace fuel
            (successors ++ rest)
      | .timeout | .stuck => headTrace

/-- All evaluator-callback traces emitted by one bounded matching search. -/
def searchPatternFuelTrace
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (trace : ValueEnvironment → Source.Expr →
      List MatchingSearchTraceEvent)
    (fuel : Nat) (environment : ValueEnvironment)
    (pattern : Source.Pattern) (matcher target : Value) :
    List MatchingSearchTraceEvent :=
  let reduce := evaluationAtomReducer evaluate
  let reduceTrace := evaluationAtomReducerTrace evaluate trace
  depthFirstFuelTrace (stepMatchingState reduce)
    (stepMatchingStateTrace reduceTrace) fuel
    [⟨[⟨pattern, matcher, target⟩], environment, []⟩]

/-- Trace the source-ordered arm searches of `matchFirst`.  Every reached arm
is recorded before its search is run; only an empty result advances to the
next arm. -/
def evalMatchFirstArmsFuelTrace
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (trace : ValueEnvironment → Source.Expr →
      List MatchingSearchTraceEvent)
    (fuel : Nat) (environment : ValueEnvironment)
    (target matcher : Value) :
    List Source.MatchFirstArm → Source.Expr →
      List MatchingSearchTraceEvent
  | [], fallback => trace environment fallback
  | arm :: rest, fallback =>
      let event : MatchingSearchTraceEvent :=
        ⟨fuel, environment, arm.pattern, matcher, target⟩
      let searchTrace := searchPatternFuelTrace evaluate trace fuel environment
        arm.pattern matcher target
      event :: (searchTrace ++
        match searchPatternFuel evaluate fuel environment arm.pattern matcher
            target with
        | .ok [] =>
            evalMatchFirstArmsFuelTrace evaluate trace fuel environment target
              matcher rest fallback
        | .ok (bindings :: _) => trace (bindings ++ environment) arm.body
        | .timeout | .stuck => [])

mutual

  /-- The complete matching-search trace of fuel-bounded evaluation. -/
  def evalFuelTrace : Nat → ValueEnvironment → Source.Expr →
      List MatchingSearchTraceEvent
    | 0, _, _ => []
    | fuel + 1, environment, expression =>
        match expression with
        | .var _ | .lit _ | .something | .lam _ | .fixE _ | .matcher _ => []
        | .app function argument =>
            let functionTrace := evalFuelTrace fuel environment function
            match evalFuel fuel environment function with
            | .ok functionValue =>
                let argumentTrace := evalFuelTrace fuel environment argument
                match evalFuel fuel environment argument with
                | .ok argumentValue =>
                    functionTrace ++ argumentTrace ++
                      applyFuelTrace fuel functionValue argumentValue
                | .timeout | .stuck => functionTrace ++ argumentTrace
            | .timeout | .stuck => functionTrace
        | .tuple items =>
            traceTraverse (evalFuel fuel environment)
              (evalFuelTrace fuel environment) items
        | .letE valueExpression body =>
            let valueTrace := evalFuelTrace fuel environment valueExpression
            match evalFuel fuel environment valueExpression with
            | .ok value =>
                valueTrace ++ evalFuelTrace fuel (value :: environment) body
            | .timeout | .stuck => valueTrace
        | .ctor _ arguments =>
            traceTraverse (evalFuel fuel environment)
              (evalFuelTrace fuel environment) arguments
        | .prim operation arguments =>
            let argumentsTrace :=
              traceTraverse (evalFuel fuel environment)
                (evalFuelTrace fuel environment) arguments
            match FuelResult.traverse (evalFuel fuel environment) arguments with
            | .ok values =>
                argumentsTrace ++ evalPrimitiveTrace (applyFuel fuel)
                  (applyFuelTrace fuel) operation values
            | .timeout | .stuck => argumentsTrace
        | .ifE condition thenBranch elseBranch =>
            let conditionTrace := evalFuelTrace fuel environment condition
            match evalFuel fuel environment condition with
            | .ok (.data constructor []) =>
                if constructor = DataCtor.true then
                  conditionTrace ++ evalFuelTrace fuel environment thenBranch
                else if constructor = DataCtor.false then
                  conditionTrace ++ evalFuelTrace fuel environment elseBranch
                else conditionTrace
            | .ok _ | .timeout | .stuck => conditionTrace
        | .matchAll target matcher pattern body =>
            let targetTrace := evalFuelTrace fuel environment target
            match evalFuel fuel environment target with
            | .ok targetValue =>
                let matcherTrace := evalFuelTrace fuel environment matcher
                match evalFuel fuel environment matcher with
                | .ok matcherValue =>
                    let event : MatchingSearchTraceEvent :=
                      ⟨fuel, environment, pattern, matcherValue, targetValue⟩
                    let searchTrace := searchPatternFuelTrace (evalFuel fuel)
                      (evalFuelTrace fuel) fuel environment pattern matcherValue
                      targetValue
                    let tracePrefix := targetTrace ++ matcherTrace ++
                      [event] ++ searchTrace
                    match searchPatternFuel (evalFuel fuel) fuel environment
                        pattern matcherValue targetValue with
                    | .ok bindingGroups =>
                        tracePrefix ++ traceTraverse
                          (fun bindings =>
                            evalFuel fuel (bindings ++ environment) body)
                          (fun bindings =>
                            evalFuelTrace fuel (bindings ++ environment) body)
                          bindingGroups
                    | .timeout | .stuck => tracePrefix
                | .timeout | .stuck => targetTrace ++ matcherTrace
            | .timeout | .stuck => targetTrace
        | .matchFirst target matcher arms fallback =>
            let targetTrace := evalFuelTrace fuel environment target
            match evalFuel fuel environment target with
            | .ok targetValue =>
                let matcherTrace := evalFuelTrace fuel environment matcher
                match evalFuel fuel environment matcher with
                | .ok matcherValue =>
                    targetTrace ++ matcherTrace ++
                      evalMatchFirstArmsFuelTrace (evalFuel fuel)
                        (evalFuelTrace fuel) fuel environment targetValue
                        matcherValue arms fallback
                | .timeout | .stuck => targetTrace ++ matcherTrace
            | .timeout | .stuck => targetTrace

  /-- Direct trace of closure-body evaluation performed by application. -/
  def applyFuelTrace : Nat → Value → Value →
      List MatchingSearchTraceEvent
    | 0, _, _ => []
    | fuel + 1, .closure .plain definitionEnvironment body, argument =>
        evalFuelTrace fuel (argument :: definitionEnvironment) body
    | fuel + 1,
        closure@(.closure .recursive definitionEnvironment body), argument =>
        evalFuelTrace fuel (argument :: closure :: definitionEnvironment) body
    | _ + 1, _, _ => []

end

/-- Writer-style public evaluator.  The result projection is intentionally
definitionally identical to `evalFuel`. -/
def evalFuelTraced
    (fuel : Nat) (environment : ValueEnvironment) (expression : Source.Expr) :
    FuelResult Value × List MatchingSearchTraceEvent :=
  (evalFuel fuel environment expression,
    evalFuelTrace fuel environment expression)

/-- The trace extension is observationally identical to the existing
evaluator when its trace is forgotten. -/
@[simp] theorem evalFuelTraced_result :
    (evalFuelTraced fuel environment expression).1 =
      evalFuel fuel environment expression :=
  rfl

end TypePM.Runtime
