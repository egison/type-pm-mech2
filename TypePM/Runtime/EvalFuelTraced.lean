import TypePM.Runtime.EvalFuel

/-!
# Trace-preserving fuel evaluator

`evalFuelTraced` is a conservative extension of `evalFuel`.  Its first
projection is definitionally the existing evaluator result; its second
projection records every bounded DFS call issued directly by expression
evaluation, in execution order.

The trace event deliberately carries no `Pattern.MNodeFree` proof.  Runtime
evaluation accepts the complete source syntax and cannot manufacture a
static fragment proof.  The source-side origin bridge combines an event with
the retained M4 pattern evidence before constructing
`BoundedDfsMatchingSearchTask`.

This first trace boundary records evaluator-level searches.  Matching-search
callbacks still use the first projection, so searches issued inside matcher
callback evaluation require the later traced-search generalization.
-/

namespace TypePM.Runtime

/-- Runtime data present at every direct `searchPatternFuel` invocation. -/
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
      event ::
        match searchPatternFuel evaluate fuel environment arm.pattern matcher
            target with
        | .ok [] =>
            evalMatchFirstArmsFuelTrace evaluate trace fuel environment target
              matcher rest fallback
        | .ok (bindings :: _) => trace (bindings ++ environment) arm.body
        | .timeout | .stuck => []

mutual

  /-- The direct matching-search trace of fuel-bounded evaluation. -/
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
                    let tracePrefix := targetTrace ++ matcherTrace ++ [event]
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
