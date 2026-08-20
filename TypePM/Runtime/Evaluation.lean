import TypePM.Runtime.ValueShape
import TypePM.Runtime.ClauseDispatch

/-!
# Relational expression evaluation

This module gives the call-by-value core of the M5 dynamic semantics.  A
runtime environment is newest first.  Consequently a plain closure evaluates
its body in `argument :: definitionEnvironment`.  A recursive closure uses
the convention fixed by the source `fixE` binder: the argument is index zero
and the closure itself is index one, so its body environment is
`argument :: closure :: definitionEnvironment`.

The `matchAll` rule and the derived surface `matchFirst` rule delegate atom
reduction and ordered search to independent relations parameterized by this
same evaluation relation.  This makes the recursive boundary through
matcher-clause expressions explicit without building the executable evaluator
into the specification.
-/

namespace TypePM.Runtime

namespace Value

/-- Canonical runtime Boolean values. -/
def boolValue (value : Bool) : Value :=
  if value then .data DataCtor.true [] else .data DataCtor.false []

/-- Structural membership used by the paper's `member` primitive. -/
def memberStructural (needle : Value) : List Value → Bool
  | [] => false
  | head :: tail => structuralEq needle head || memberStructural needle tail

/-- Remove the first structurally equal element.  Absence leaves the input
unchanged, matching Egison's `deleteFirst` primitive. -/
def deleteFirstStructural (needle : Value) : List Value → List Value
  | [] => []
  | head :: tail =>
      if structuralEq needle head then tail
      else head :: deleteFirstStructural needle tail

end Value

mutual

  /-- Big-step, call-by-value evaluation of source expressions. -/
  inductive Eval : ValueEnvironment → Source.Expr → Value → Prop where
    | var (lookup : Lookup environment index value) :
        Eval environment (.var index) value
    | lit : Eval environment (.lit literal) (.int literal)
    | something : Eval environment .something .something
    | lam :
        Eval environment (.lam body) (Value.plainClosure environment body)
    | app
        (functionEval : Eval environment function functionValue)
        (argumentEval : Eval environment argument argumentValue)
        (application : Applies functionValue argumentValue result) :
        Eval environment (.app function argument) result
    | tuple (itemsEval : Evals environment items values) :
        Eval environment (.tuple items) (.tuple values)
    | letE
        (valueEval : Eval environment valueExpression value)
        (bodyEval : Eval (value :: environment) body result) :
        Eval environment (.letE valueExpression body) result
    | ctor (argumentsEval : Evals environment arguments values) :
        Eval environment (.ctor constructor arguments) (.data constructor values)
    | prim
        (argumentsEval : Evals environment arguments values)
        (primitive : PrimitiveEvaluates operation values result) :
        Eval environment (.prim operation arguments) result
    | ifTrue
        (conditionEval :
          Eval environment condition (.data DataCtor.true []))
        (branchEval : Eval environment thenBranch result) :
        Eval environment (.ifE condition thenBranch elseBranch) result
    | ifFalse
        (conditionEval :
          Eval environment condition (.data DataCtor.false []))
        (branchEval : Eval environment elseBranch result) :
        Eval environment (.ifE condition thenBranch elseBranch) result
    | fixE :
        Eval environment (.fixE body)
          (Value.recursiveClosure environment body)
    | matcher :
        Eval environment (.matcher clauses)
          (Value.matcherClosure environment clauses)
    | matchAll
        (targetEval : Eval environment target targetValue)
        (matcherEval : Eval environment matcher matcherValue)
        (matching : EvalMatchingSearch
          [⟨[⟨pattern, matcherValue, targetValue⟩], environment, []⟩]
          bindingGroups)
        (bodiesEval : EvalBindingGroups environment body
          bindingGroups bodyValues) :
        Eval environment (.matchAll target matcher pattern body)
          (Value.buildList bodyValues)
    | matchFirst
        (targetEval : Eval environment target targetValue)
        (matcherEval : Eval environment matcher matcherValue)
        (armsEval : EvalMatchFirstArms environment targetValue matcherValue
          arms result) :
        Eval environment (.matchFirst target matcher arms) result

  /-- Left-to-right call-by-value evaluation of an expression sequence. -/
  inductive Evals : ValueEnvironment → List Source.Expr → List Value → Prop where
    | nil : Evals environment [] []
    | cons
        (headEval : Eval environment head value)
        (tailEval : Evals environment tail values) :
        Evals environment (head :: tail) (value :: values)

  /-- Application of a function value.  The recursive case records the exact
  de Bruijn layout: argument at zero and self at one. -/
  inductive Applies : Value → Value → Value → Prop where
    | plain
        (bodyEval : Eval (argument :: definitionEnvironment) body result) :
        Applies (.closure .plain definitionEnvironment body) argument result
    | recursive
        (bodyEval :
          Eval
            (argument ::
              .closure .recursive definitionEnvironment body ::
              definitionEnvironment)
            body result) :
        Applies (.closure .recursive definitionEnvironment body) argument result

  /-- Apply one function to a sequence from left to right. -/
  inductive AppliesList : Value → List Value → List Value → Prop where
    | nil : AppliesList function [] []
    | cons
        (headApply : Applies function input output)
        (tailApply : AppliesList function inputs outputs) :
        AppliesList function (input :: inputs) (output :: outputs)

  /-- Successful primitive delta rules on complete runtime values. -/
  inductive PrimitiveEvaluates : PrimOp → List Value → Value → Prop where
    | add :
        PrimitiveEvaluates .add [.int left, .int right] (.int (left + right))
    | append
        (leftEncoding : Value.viewList left = some leftItems)
        (rightEncoding : Value.viewList right = some rightItems) :
        PrimitiveEvaluates .append [left, right]
          (Value.buildList (leftItems ++ rightItems))
    | member
        (encoding : Value.viewList target = some items) :
        PrimitiveEvaluates .member [needle, target]
          (Value.boolValue (Value.memberStructural needle items))
    | deleteFirst
        (encoding : Value.viewList target = some items) :
        PrimitiveEvaluates .deleteFirst [needle, target]
          (Value.buildList (Value.deleteFirstStructural needle items))
    | map
        (encoding : Value.viewList target = some inputs)
        (applications : AppliesList function inputs outputs) :
        PrimitiveEvaluates .map [function, target]
          (Value.buildList outputs)

  /-- Relational successful attempt of one matcher arm. -/
  inductive EvalMatcherArmDispatches :
      ValueEnvironment → ValueEnvironment → List Source.Pattern →
      Source.Expr → Value → Source.MatcherArm →
      DispatchResult MatchingBranches → Prop where
    | miss
        (mismatch : matchValueDataPattern header target = none) :
        EvalMatcherArmDispatches matcherEnvironment captureValues holes
          nextMatchers target (.mk header body) .miss
    | hit
        (dataMatch : ValueDataPatternMatches header target dataValues)
        (bodyEval : Eval
          (dataValues ++ captureValues ++ matcherEnvironment)
          body decompositionValue)
        (decompositionShape :
          decodeDecompositions holes.length decompositionValue =
            some decompositions)
        (matcherEval : Eval matcherEnvironment nextMatchers matcherProduct)
        (matcherShape :
          decodeProduct holes.length matcherProduct = some matchers)
        (branchesBuilt :
          buildMatchingBranches holes matchers decompositions = some branches) :
        EvalMatcherArmDispatches matcherEnvironment captureValues holes
          nextMatchers target (.mk header body) (.hit branches)

  /-- Source-ordered first-success arm dispatch. -/
  inductive EvalMatcherArmsDispatch :
      ValueEnvironment → ValueEnvironment → List Source.Pattern →
      Source.Expr → Value → List Source.MatcherArm →
      DispatchResult MatchingBranches → Prop where
    | nil : EvalMatcherArmsDispatch matcherEnvironment captureValues holes
        nextMatchers target [] .miss
    | hit
        (selected : EvalMatcherArmDispatches matcherEnvironment captureValues
          holes nextMatchers target arm (.hit branches)) :
        EvalMatcherArmsDispatch matcherEnvironment captureValues holes
          nextMatchers target (arm :: rest) (.hit branches)
    | skip
        (missed : EvalMatcherArmDispatches matcherEnvironment captureValues
          holes nextMatchers target arm .miss)
        (tail : EvalMatcherArmsDispatch matcherEnvironment captureValues holes
          nextMatchers target rest result) :
        EvalMatcherArmsDispatch matcherEnvironment captureValues holes
          nextMatchers target (arm :: rest) result

  /-- Relational attempt of one matcher clause. -/
  inductive EvalMatcherClauseDispatches :
      ValueEnvironment → ValueEnvironment → Source.Pattern → Value →
      Source.MatcherClause → DispatchResult MatchingBranches → Prop where
    | miss
        (mismatch : inspectPatternPattern header pattern = none) :
        EvalMatcherClauseDispatches atomEnvironment matcherEnvironment
          pattern target (.mk header nextMatchers arms) .miss
    | matched
        (headerMatch : PatternPatternMatches header pattern dispatch)
        (capturesEval : Evals atomEnvironment dispatch.captures captureValues)
        (armsDispatch : EvalMatcherArmsDispatch matcherEnvironment captureValues
          dispatch.holes nextMatchers target arms armsResult) :
        EvalMatcherClauseDispatches atomEnvironment matcherEnvironment
          pattern target (.mk header nextMatchers arms)
            (closeMatcherArmsResult armsResult)

  /-- Source-ordered first-success clause dispatch. -/
  inductive EvalMatcherClausesDispatch :
      ValueEnvironment → ValueEnvironment → Source.Pattern → Value →
      List Source.MatcherClause → DispatchResult MatchingBranches → Prop where
    | nil : EvalMatcherClausesDispatch atomEnvironment matcherEnvironment
        pattern target [] .miss
    | hit
        (selected : EvalMatcherClauseDispatches atomEnvironment
          matcherEnvironment pattern target clause (.hit branches)) :
        EvalMatcherClausesDispatch atomEnvironment matcherEnvironment
          pattern target (clause :: rest) (.hit branches)
    | skip
        (missed : EvalMatcherClauseDispatches atomEnvironment matcherEnvironment
          pattern target clause .miss)
        (tail : EvalMatcherClausesDispatch atomEnvironment matcherEnvironment
          pattern target rest result) :
        EvalMatcherClausesDispatch atomEnvironment matcherEnvironment
          pattern target (clause :: rest) result

  /-- Successful atom reduction in built-in-before-matcher order. -/
  inductive EvalAtomReduces :
      ValueEnvironment → MatchingAtom → AtomReduction → Prop where
    | somethingWild : EvalAtomReduces environment
        ⟨.wild, .something, target⟩ .success
    | somethingVar : EvalAtomReduces environment
        ⟨.var, .something, target⟩ ⟨[[]], [target]⟩
    | somethingValueSuccess
        (evaluated : Eval environment expression actual)
        (equal : Value.structuralEq actual target = true) :
        EvalAtomReduces environment
          ⟨.value expression, .something, target⟩ .success
    | somethingValueFailure
        (evaluated : Eval environment expression actual)
        (unequal : Value.structuralEq actual target = false) :
        EvalAtomReduces environment
          ⟨.value expression, .something, target⟩ .failure
    | and : EvalAtomReduces environment
        ⟨.and left right, matcher, target⟩
        ⟨[[⟨left, matcher, target⟩, ⟨right, matcher, target⟩]], []⟩
    | or : EvalAtomReduces environment
        ⟨.or left right, matcher, target⟩
        ⟨[[⟨left, matcher, target⟩], [⟨right, matcher, target⟩]], []⟩
    | tuple
        (zipped : MatchingAtomsZip patterns matchers targets atoms) :
        EvalAtomReduces environment
          ⟨.tuple patterns, .tuple matchers, .tuple targets⟩ ⟨[atoms], []⟩
    | productSomethingVar : EvalAtomReduces environment
        ⟨.var, .tuple matchers, target⟩
        ⟨[[⟨.var, .something, target⟩]], []⟩
    | productSomethingWild : EvalAtomReduces environment
        ⟨.wild, .tuple matchers, target⟩
        ⟨[[⟨.wild, .something, target⟩]], []⟩
    | productSomethingValue : EvalAtomReduces environment
        ⟨.value expression, .tuple matchers, target⟩
        ⟨[[⟨.value expression, .something, target⟩]], []⟩
    | matcher
        (dispatchable : MatcherDispatchable pattern)
        (clauses : EvalMatcherClausesDispatch environment matcherEnvironment
          pattern target remaining (.hit branches)) :
        EvalAtomReduces environment
          ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩
          ⟨branches, []⟩

  /-- Complete ordered depth-first matching search. -/
  inductive EvalMatchingSearch :
      List MatchingState → List (List Value) → Prop where
    | nil : EvalMatchingSearch [] []
    | yield
        (tail : EvalMatchingSearch rest answers) :
        EvalMatchingSearch
          (⟨[], environment, bindings⟩ :: rest) (bindings :: answers)
    | expand
        (reduced : EvalAtomReduces (bindings ++ environment) atom reduction)
        (next : EvalMatchingSearch
          ((reduction.branches.map fun branch =>
            ⟨branch ++ remaining, environment,
              bindings ++ reduction.bindings⟩) ++ rest) answers) :
        EvalMatchingSearch
          (⟨atom :: remaining, environment, bindings⟩ :: rest) answers

  /-- Evaluate the result body once for every successful binding group. -/
  inductive EvalBindingGroups :
      ValueEnvironment → Source.Expr → List (List Value) →
      List Value → Prop where
    | nil : EvalBindingGroups environment body [] []
    | cons
        (head : Eval (bindings ++ environment) body value)
        (tail : EvalBindingGroups environment body groups values) :
        EvalBindingGroups environment body
          (bindings :: groups) (value :: values)

  /-- Paper 1's derived single-result `match`: try arms in source order, using
  the complete ordered `matchAll` search for each arm, and evaluate the body
  under the first binding group of the first nonempty search. -/
  inductive EvalMatchFirstArms :
      ValueEnvironment → Value → Value → List Source.MatchFirstArm →
      Value → Prop where
    | hit
        (matching : EvalMatchingSearch
          [⟨[⟨arm.pattern, matcher, target⟩], environment, []⟩]
          (bindings :: remaining))
        (bodyEval : Eval (bindings ++ environment) arm.body result) :
        EvalMatchFirstArms environment target matcher (arm :: rest) result
    | skip
        (matching : EvalMatchingSearch
          [⟨[⟨arm.pattern, matcher, target⟩], environment, []⟩] [])
        (tail : EvalMatchFirstArms environment target matcher rest result) :
        EvalMatchFirstArms environment target matcher (arm :: rest) result

end

end TypePM.Runtime
