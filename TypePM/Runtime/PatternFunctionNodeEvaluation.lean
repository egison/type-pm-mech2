import TypePM.Runtime.PatternFunctionMatching

/-!
# Expression evaluation with scoped pattern-function nodes

The earlier `evalPatternFunctionsFuel` expands only the inline-safe source
fragment before evaluation.  General pattern functions may bind private
variables, so they instead require the isolated `MatchingTree.node` runtime
rule.  This module threads the runtime definition table through the ordinary
evaluator and replaces only the matching search used by `matchAll` and
`matchFirst`.  Its checked public entry point additionally requires proof that
every table entry has a canonical-instance source check and every frozen
declaration has a runtime body with the same name.

This is an executable semantics.  Its successful matching search is linked to
an inductive `DepthFirst` derivation over the executable state-step function;
the structural state-step witness is proved separately.  A general
preservation theorem for this evaluator is deliberately not claimed here.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Execute derived single-result matching with the scoped pattern-function
search.  Source-arm order and first-result selection agree with
`evalMatchFirstArmsFuel`; only the search engine is extended with MNodes. -/
def evalPatternFunctionNodeArmsFuel
    (definitions : PatternFunctionDefinitions)
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (environment : ValueEnvironment)
    (target matcher : Value) : List Source.MatchFirstArm → FuelResult Value
  | [] => .stuck
  | arm :: rest =>
      FuelResult.bind
        (searchPatternFunctionsFuel definitions evaluate fuel environment
          arm.pattern matcher target)
        fun bindingGroups =>
          match bindingGroups with
          | [] => evalPatternFunctionNodeArmsFuel definitions evaluate fuel
              environment target matcher rest
          | bindings :: _ => evaluate (bindings ++ environment) arm.body

mutual

  /-- Fuel-bounded call-by-value evaluation using scoped MNode search for
  pattern-function applications inside `matchAll` and `matchFirst`.
  Every other expression clause is the corresponding `evalFuel` clause. -/
  def evalPatternFunctionNodesFuel
      (definitions : PatternFunctionDefinitions) :
      Nat → ValueEnvironment → Source.Expr → FuelResult Value
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
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment function)
              fun functionValue =>
                FuelResult.bind
                  (evalPatternFunctionNodesFuel definitions fuel environment argument)
                  fun argumentValue =>
                    applyPatternFunctionNodesFuel definitions fuel functionValue
                      argumentValue
        | .tuple items =>
            FuelResult.map Value.tuple
              (FuelResult.traverse
                (evalPatternFunctionNodesFuel definitions fuel environment) items)
        | .letE valueExpression body =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment
                valueExpression)
              fun value =>
                evalPatternFunctionNodesFuel definitions fuel
                  (value :: environment) body
        | .ctor constructor arguments =>
            FuelResult.map (Value.data constructor)
              (FuelResult.traverse
                (evalPatternFunctionNodesFuel definitions fuel environment)
                arguments)
        | .prim operation arguments =>
            FuelResult.bind
              (FuelResult.traverse
                (evalPatternFunctionNodesFuel definitions fuel environment)
                arguments)
              (evalPrimitive
                (applyPatternFunctionNodesFuel definitions fuel) operation)
        | .ifE condition thenBranch elseBranch =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment condition)
              fun conditionValue =>
                match conditionValue with
                | .data constructor [] =>
                    if constructor = DataCtor.true then
                      evalPatternFunctionNodesFuel definitions fuel environment
                        thenBranch
                    else if constructor = DataCtor.false then
                      evalPatternFunctionNodesFuel definitions fuel environment
                        elseBranch
                    else
                      .stuck
                | _ => .stuck
        | .fixE body => .ok (Value.recursiveClosure environment body)
        | .matcher clauses => .ok (Value.matcherClosure environment clauses)
        | .matchAll target matcher pattern body =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment target)
              fun targetValue =>
                FuelResult.bind
                  (evalPatternFunctionNodesFuel definitions fuel environment matcher)
                  fun matcherValue =>
                    FuelResult.bind
                      (searchPatternFunctionsFuel definitions
                        (evalPatternFunctionNodesFuel definitions fuel) fuel
                        environment pattern matcherValue targetValue)
                      fun bindingGroups =>
                        FuelResult.map Value.buildList
                          (FuelResult.traverse
                            (fun bindings =>
                              evalPatternFunctionNodesFuel definitions fuel
                                (bindings ++ environment) body)
                            bindingGroups)
        | .matchFirst target matcher arms =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment target)
              fun targetValue =>
                FuelResult.bind
                  (evalPatternFunctionNodesFuel definitions fuel environment matcher)
                  fun matcherValue =>
                    evalPatternFunctionNodeArmsFuel definitions
                      (evalPatternFunctionNodesFuel definitions fuel) fuel
                      environment targetValue matcherValue arms

  /-- Application companion of `evalPatternFunctionNodesFuel`. -/
  def applyPatternFunctionNodesFuel
      (definitions : PatternFunctionDefinitions) :
      Nat → Value → Value → FuelResult Value
    | 0, _, _ => .timeout
    | fuel + 1, .closure .plain definitionEnvironment body, argument =>
        evalPatternFunctionNodesFuel definitions fuel
          (argument :: definitionEnvironment) body
    | fuel + 1,
        closure@(.closure .recursive definitionEnvironment body), argument =>
        evalPatternFunctionNodesFuel definitions fuel
          (argument :: closure :: definitionEnvironment) body
    | _ + 1, _, _ => .stuck

end

/-- Public entry point for scoped pattern-function evaluation.  The
`agreement` argument certifies that every executable definition has a
canonical-instance source check and that every frozen declaration has a body
with the same name.  The proof does not change execution; it prevents callers
from silently pairing the evaluator with an unrelated runtime table. -/
def evalCheckedPatternFunctionNodesFuel
    (signature : FrozenSignature) (definitions : PatternFunctionDefinitions)
    (_agreement : definitions.Agree signature)
    (fuel : Nat) (environment : ValueEnvironment) (expression : Source.Expr) :
    FuelResult Value :=
  evalPatternFunctionNodesFuel definitions fuel environment expression


/-- Successful execution of a top-level `matchAll` exposes a successful
scoped search with an inductive depth-first derivation over the executable
state-step function, followed by the ordinary left-to-right evaluation of all
selected bodies. -/
theorem evalPatternFunctionNodesFuel_matchAll_search_sound
    (success :
      evalPatternFunctionNodesFuel definitions (fuel + 1) environment
        (.matchAll target matcher pattern body) = .ok result) :
    ∃ targetValue matcherValue bindingGroups values,
      evalPatternFunctionNodesFuel definitions fuel environment target =
          .ok targetValue ∧
      evalPatternFunctionNodesFuel definitions fuel environment matcher =
          .ok matcherValue ∧
      searchPatternFunctionsFuel definitions
          (evalPatternFunctionNodesFuel definitions fuel) fuel environment
          pattern matcherValue targetValue = .ok bindingGroups ∧
      DepthFirst
        (stepPatternFunctionState definitions
          (evaluationAtomReducer
            (evalPatternFunctionNodesFuel definitions fuel)))
        [⟨[.atom ⟨pattern, matcherValue, targetValue⟩], environment, []⟩]
        bindingGroups ∧
      FuelResult.traverse
          (fun bindings => evalPatternFunctionNodesFuel definitions fuel
            (bindings ++ environment) body)
          bindingGroups = .ok values ∧
      result = Value.buildList values := by
  rw [evalPatternFunctionNodesFuel.eq_def] at success
  simp only at success
  rw [FuelResult.bind_eq_ok_iff] at success
  rcases success with ⟨targetValue, targetSuccess, success⟩
  rw [FuelResult.bind_eq_ok_iff] at success
  rcases success with ⟨matcherValue, matcherSuccess, success⟩
  rw [FuelResult.bind_eq_ok_iff] at success
  rcases success with ⟨bindingGroups, searchSuccess, success⟩
  rw [FuelResult.map_eq_ok_iff] at success
  rcases success with ⟨values, bodySuccess, resultEq⟩
  exact ⟨targetValue, matcherValue, bindingGroups, values, targetSuccess,
    matcherSuccess, searchSuccess,
    searchPatternFunctionsFuel_sound definitions _ searchSuccess,
    bodySuccess, resultEq.symm⟩

/-- A successful checked entry-point run of `matchAll` exposes the same
inductive depth-first derivation as the raw evaluator.  Source/runtime table
agreement is an interface precondition and does not alter execution. -/
theorem evalCheckedPatternFunctionNodesFuel_matchAll_search_sound
    (agreement : definitions.Agree signature)
    (success :
      evalCheckedPatternFunctionNodesFuel signature definitions agreement
        (fuel + 1) environment (.matchAll target matcher pattern body) =
        .ok result) :
    ∃ targetValue matcherValue bindingGroups values,
      evalPatternFunctionNodesFuel definitions fuel environment target =
          .ok targetValue ∧
      evalPatternFunctionNodesFuel definitions fuel environment matcher =
          .ok matcherValue ∧
      searchPatternFunctionsFuel definitions
          (evalPatternFunctionNodesFuel definitions fuel) fuel environment
          pattern matcherValue targetValue = .ok bindingGroups ∧
      DepthFirst
        (stepPatternFunctionState definitions
          (evaluationAtomReducer
            (evalPatternFunctionNodesFuel definitions fuel)))
        [⟨[.atom ⟨pattern, matcherValue, targetValue⟩], environment, []⟩]
        bindingGroups ∧
      FuelResult.traverse
          (fun bindings => evalPatternFunctionNodesFuel definitions fuel
            (bindings ++ environment) body)
          bindingGroups = .ok values ∧
      result = Value.buildList values := by
  exact evalPatternFunctionNodesFuel_matchAll_search_sound success

end TypePM.Runtime
