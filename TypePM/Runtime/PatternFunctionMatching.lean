import TypePM.Runtime.DepthFirstSearch
import TypePM.Runtime.EvalFuel
import TypePM.Source.PatternFunctionDefinition

/-!
# Scoped runtime matching for pattern functions

Pattern-function bodies cannot be expanded by ordinary textual substitution:
variables introduced by a body are private, while bindings introduced by the
argument patterns must be returned to the surrounding match.  `MatchingTree`
therefore adds the paper's isolated matching node (MNode) to ordinary atoms.

An MNode stores its own work, expression environment, bindings, and actual
pattern arguments.  Ordinary inner steps update only that private state.
An embedded parameter is exported as an ordinary atom immediately before the
continuation node, so bindings made by the actual argument are outer bindings.
When the node finishes, its private bindings are discarded.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- One item of scoped matching work.  The `node` fields are exactly the
private state of one pattern-function body and its actual arguments. -/
inductive MatchingTree where
  | atom (request : MatchingAtom)
  | node (work : List MatchingTree) (environment : ValueEnvironment)
      (bindings : List Value) (arguments : List Pattern)
deriving Repr

/-- A matching state whose work may contain isolated pattern-function nodes. -/
structure PatternFunctionState where
  work : List MatchingTree
  environment : ValueEnvironment
  bindings : List Value
deriving Repr

private theorem sizeOf_head_lt_node
    (head : MatchingTree) (tail : List MatchingTree)
    (environment : ValueEnvironment) (bindings : List Value)
    (arguments : List Pattern) :
    sizeOf head < sizeOf (MatchingTree.node (head :: tail) environment bindings
      arguments) := by
  simp_wf
  omega

/-- Lift an ordinary atom branch to tree work. -/
def MatchingTree.ofAtoms (atoms : List MatchingAtom) : List MatchingTree :=
  atoms.map .atom

/-- Runtime lookup plus the exact source arity check. -/
def lookupPatternFunctionApplication
    (definitions : PatternFunctionDefinitions) (name : PatternFunName)
    (arguments : List Pattern) : Option PatternFunctionDefinition := do
  let definition ← definitions.lookup name
  if arguments.length = definition.parameterCount then some definition
  else none

/-- Continue an ordinary atom reduction inside the current scope. -/
def continueTreeAtom
    (remaining : List MatchingTree) (environment : ValueEnvironment)
    (bindings : List Value) (reduction : AtomReduction) :
    List PatternFunctionState :=
  reduction.branches.map fun branch =>
    ⟨MatchingTree.ofAtoms branch ++ remaining, environment,
      bindings ++ reduction.bindings⟩

  /-- Take one step at the head of a nonempty tree worklist.  Pattern-function
  application is tested before the ordinary atom reducer, so a matcher's
  catch-all clause cannot capture it. -/
  def stepPatternFunctionHead
      (definitions : PatternFunctionDefinitions)
      (reduceAtom : ValueEnvironment → MatchingAtom →
        FuelResult (DispatchResult AtomReduction)) :
      MatchingTree → List MatchingTree → ValueEnvironment → List Value →
        FuelResult (List PatternFunctionState)
    | .atom atom, remaining, environment, bindings =>
        match atom.pattern with
        | .app name arguments =>
            match lookupPatternFunctionApplication definitions name arguments with
            | none => .stuck
            | some definition =>
                .ok [⟨[.node ([.atom ⟨definition.body, atom.matcher, atom.target⟩])
                    environment [] arguments] ++ remaining,
                  environment, bindings⟩]
        | .embed _ => .stuck
        | _ =>
            FuelResult.bind (reduceAtom (bindings ++ environment) atom) fun result =>
              match result with
              | .miss => .stuck
              | .hit reduction =>
                  .ok (continueTreeAtom remaining environment bindings reduction)
    | .node [] _privateEnvironment _privateBindings _arguments,
        remaining, environment, bindings =>
        .ok [⟨remaining, environment, bindings⟩]
    | .node (.atom atom :: privateRemaining) privateEnvironment
          privateBindings arguments,
        remaining, environment, bindings =>
        match atom.pattern with
        | .embed index =>
            match arguments[index]? with
            | none => .stuck
            | some argument =>
                .ok [⟨.atom ⟨argument, atom.matcher, atom.target⟩ ::
                    .node privateRemaining privateEnvironment privateBindings
                      arguments :: remaining,
                  environment, bindings⟩]
        | _ =>
            FuelResult.map
              (fun successors => successors.map fun successor =>
                ⟨.node successor.work successor.environment successor.bindings
                    arguments :: remaining,
                  environment, bindings⟩)
              (stepPatternFunctionHead definitions reduceAtom (.atom atom)
                privateRemaining privateEnvironment privateBindings)
    | .node (head :: privateRemaining) privateEnvironment privateBindings arguments,
        remaining, environment, bindings =>
        FuelResult.map
          (fun successors => successors.map fun successor =>
            ⟨.node successor.work successor.environment successor.bindings
                arguments :: remaining,
              environment, bindings⟩)
          (stepPatternFunctionHead definitions reduceAtom head privateRemaining
            privateEnvironment privateBindings)

/-- One complete scoped state step. -/
def stepPatternFunctionState
    (definitions : PatternFunctionDefinitions)
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (state : PatternFunctionState) :
    FuelResult (SearchStep PatternFunctionState (List Value)) :=
  match state.work with
  | [] => .ok (.yield state.bindings)
  | head :: remaining =>
      FuelResult.map SearchStep.expand
        (stepPatternFunctionHead definitions reduceAtom head remaining
          state.environment state.bindings)

/-- Execute all scoped alternatives by the same ordered depth-first search as
ordinary M5 matching. -/
def searchPatternFunctionsFuel
    (definitions : PatternFunctionDefinitions)
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (environment : ValueEnvironment)
    (pattern : Pattern) (matcher target : Value) :
    FuelResult (List (List Value)) :=
  depthFirstFuel
    (stepPatternFunctionState definitions (evaluationAtomReducer evaluate))
    fuel [⟨[.atom ⟨pattern, matcher, target⟩], environment, []⟩]

/-! ## Structural step relation -/

/-- A structural description of one successful head step.  The ordinary atom
case refers to the structural `BuiltinAtomReduces` and
`MatcherAtomReduces` through the combined reducer's successful result; the
three new constructors state the pattern-function rules directly. -/
inductive PatternFunctionHeadSteps
    (definitions : PatternFunctionDefinitions)
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)) :
    MatchingTree → List MatchingTree → ValueEnvironment → List Value →
      List PatternFunctionState → Prop where
  | application
      (found : definitions.lookup name = some definition)
      (arity : arguments.length = definition.parameterCount) :
      PatternFunctionHeadSteps definitions reduceAtom
        (.atom ⟨.app name arguments, matcher, target⟩) remaining
        environment bindings
        [⟨[.node ([.atom ⟨definition.body, matcher, target⟩]) environment []
            arguments] ++ remaining, environment, bindings⟩]
  | ordinary
      (notApplication : ∀ name arguments, pattern ≠ .app name arguments)
      (notParameter : ∀ index, pattern ≠ .embed index)
      (reduced : reduceAtom (bindings ++ environment)
        ⟨pattern, matcher, target⟩ = .ok (.hit reduction)) :
      PatternFunctionHeadSteps definitions reduceAtom
        (.atom ⟨pattern, matcher, target⟩) remaining environment bindings
        (continueTreeAtom remaining environment bindings reduction)
  | nodeDone :
      PatternFunctionHeadSteps definitions reduceAtom
        (.node [] privateEnvironment privateBindings arguments)
        remaining environment bindings [⟨remaining, environment, bindings⟩]
  | parameter
      (lookup : arguments[index]? = some argument) :
      PatternFunctionHeadSteps definitions reduceAtom
        (.node (.atom ⟨.embed index, matcher, target⟩ :: privateRemaining)
          privateEnvironment privateBindings arguments)
        remaining environment bindings
        [⟨.atom ⟨argument, matcher, target⟩ ::
            .node privateRemaining privateEnvironment privateBindings arguments ::
              remaining,
          environment, bindings⟩]
  | nodeStep
      (notParameter : ∀ index matcher target,
        head ≠ .atom ⟨.embed index, matcher, target⟩)
      (inner : PatternFunctionHeadSteps definitions reduceAtom head
        privateRemaining privateEnvironment privateBindings successors) :
      PatternFunctionHeadSteps definitions reduceAtom
        (.node (head :: privateRemaining) privateEnvironment privateBindings
          arguments)
        remaining environment bindings
        (successors.map fun successor =>
          ⟨.node successor.work successor.environment successor.bindings
              arguments :: remaining,
            environment, bindings⟩)

/-- Every successful executable head step has a structural derivation. -/
theorem stepPatternFunctionHead_sound
    {definitions : PatternFunctionDefinitions}
    {reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)}
    {head : MatchingTree} {remaining : List MatchingTree}
    {environment : ValueEnvironment} {bindings : List Value}
    {successors : List PatternFunctionState}
    (success : stepPatternFunctionHead definitions reduceAtom head remaining
      environment bindings = .ok successors) :
    PatternFunctionHeadSteps definitions reduceAtom head remaining environment
      bindings successors := by
  cases head with
  | atom atom =>
      rcases atom with ⟨pattern, matcher, target⟩
      cases pattern with
      | app name arguments =>
          simp only [stepPatternFunctionHead] at success
          cases found : definitions.lookup name with
          | none => simp [lookupPatternFunctionApplication, found] at success
          | some definition =>
              by_cases arity : arguments.length = definition.parameterCount
              · simp [lookupPatternFunctionApplication, found, arity] at success
                subst successors
                exact .application found arity
              · simp [lookupPatternFunctionApplication, found, arity] at success
      | embed index => simp [stepPatternFunctionHead] at success
      | var | wild | value | ctor | tuple | and | or =>
          simp only [stepPatternFunctionHead] at success
          rw [FuelResult.bind_eq_ok_iff] at success
          rcases success with ⟨result, reduced, continued⟩
          cases result with
          | miss => simp at continued
          | hit reduction =>
              cases continued
              exact .ordinary (by intros; simp) (by intros; simp) reduced
  | node privateWork privateEnvironment privateBindings arguments =>
      cases privateWork with
      | nil =>
          simp [stepPatternFunctionHead] at success
          subst successors
          exact .nodeDone
      | cons privateHead privateRemaining =>
          cases privateHead with
          | atom atom =>
              cases patternEq : atom.pattern with
              | embed index =>
                  simp only [stepPatternFunctionHead, patternEq] at success
                  cases lookup : arguments[index]? with
                  | none => simp [lookup] at success
                  | some argument =>
                      simp [lookup] at success
                      subst successors
                      have atomEq : atom =
                          ⟨.embed index, atom.matcher, atom.target⟩ := by
                        cases atom
                        simp_all
                      rw [atomEq]
                      exact .parameter lookup
              | var | wild | value | ctor | tuple | and | or | app =>
                  simp only [stepPatternFunctionHead, patternEq,
                    FuelResult.map_eq_ok_iff] at success
                  rcases success with ⟨innerSuccessors, stepped, rfl⟩
                  have stepped' :
                      stepPatternFunctionHead definitions reduceAtom
                        (.atom atom) privateRemaining privateEnvironment
                          privateBindings = .ok innerSuccessors := by
                    simp only [stepPatternFunctionHead, patternEq]
                    exact stepped
                  exact .nodeStep (by
                    intros index matcher target equality
                    have patternEquality := congrArg
                      (fun tree =>
                        match tree with
                        | .atom request => request.pattern
                        | .node _ _ _ _ => .wild)
                      equality
                    simp [patternEq] at patternEquality)
                    (stepPatternFunctionHead_sound stepped')
          | node work env innerBindings innerArguments =>
              simp only [stepPatternFunctionHead, FuelResult.map_eq_ok_iff]
                at success
              rcases success with ⟨innerSuccessors, stepped, rfl⟩
              exact .nodeStep (by intros; simp)
                (stepPatternFunctionHead_sound stepped)
termination_by sizeOf head
decreasing_by
  all_goals
    subst_vars
    apply sizeOf_head_lt_node

/-- Successful state stepping has a structural relational witness. -/
inductive PatternFunctionStateSteps
    (definitions : PatternFunctionDefinitions)
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)) :
    PatternFunctionState → SearchStep PatternFunctionState (List Value) → Prop where
  | yield : PatternFunctionStateSteps definitions reduceAtom
      ⟨[], environment, bindings⟩ (.yield bindings)
  | expand
      (headStep : PatternFunctionHeadSteps definitions reduceAtom head remaining
        environment bindings successors) :
      PatternFunctionStateSteps definitions reduceAtom
        ⟨head :: remaining, environment, bindings⟩ (.expand successors)

theorem stepPatternFunctionState_sound
    {definitions : PatternFunctionDefinitions}
    {reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)}
    {state : PatternFunctionState}
    {observation : SearchStep PatternFunctionState (List Value)}
    (success : stepPatternFunctionState definitions reduceAtom state =
      .ok observation) :
    PatternFunctionStateSteps definitions reduceAtom state observation := by
  rcases state with ⟨work, environment, bindings⟩
  cases work with
  | nil => cases success; exact .yield
  | cons head remaining =>
      simp only [stepPatternFunctionState, FuelResult.map_eq_ok_iff] at success
      rcases success with ⟨successors, stepped, rfl⟩
      exact .expand (stepPatternFunctionHead_sound stepped)

/-- A successful bounded scoped search has an inductive `DepthFirst`
derivation over the same executable state-step function.  Structural
soundness of each successful state step is provided separately by
`stepPatternFunctionState_sound`. -/
theorem searchPatternFunctionsFuel_sound
    (definitions : PatternFunctionDefinitions)
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    {fuel : Nat} {environment : ValueEnvironment} {pattern : Pattern}
    {matcher target : Value} {answers : List (List Value)}
    (success : searchPatternFunctionsFuel definitions evaluate fuel environment
      pattern matcher target = .ok answers) :
    DepthFirst
      (stepPatternFunctionState definitions (evaluationAtomReducer evaluate))
      [⟨[.atom ⟨pattern, matcher, target⟩], environment, []⟩] answers :=
  depthFirstFuel_sound _ success

end TypePM.Runtime
