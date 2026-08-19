import TypePM.Runtime.Values

/-!
# Relational expression evaluation

This module gives the call-by-value core of the M5 dynamic semantics.  A
runtime environment is newest first.  Consequently a plain closure evaluates
its body in `argument :: definitionEnvironment`.  A recursive closure uses
the convention fixed by the source `fixE` binder: the argument is index zero
and the closure itself is index one, so its body environment is
`argument :: closure :: definitionEnvironment`.

`matchAll` deliberately has no rule here.  Its rule belongs to the matching
engine, whose states in turn evaluate clause expressions.  Keeping that
boundary explicit avoids hiding a circular evaluator behind an abstract
callback.
-/

namespace TypePM.Runtime

namespace Value

/-- Canonical runtime Boolean values. -/
def boolValue (value : Bool) : Value :=
  if value then .data DataCtor.true [] else .data DataCtor.false []

/-- Canonical runtime list encoding. -/
def buildList : List Value → Value
  | [] => .data DataCtor.nil []
  | head :: tail => .data DataCtor.cons [head, buildList tail]

/-- Decode exactly the canonical runtime list encoding. -/
def viewList : Value → Option (List Value)
  | .data constructor [] =>
      if constructor = DataCtor.nil then some [] else none
  | .data constructor [head, tail] =>
      if constructor = DataCtor.cons then
        (viewList tail).map (head :: ·)
      else
        none
  | _ => none
termination_by value => sizeOf value

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

theorem viewList_buildList (items : List Value) :
    viewList (buildList items) = some items := by
  induction items with
  | nil => simp [buildList, viewList]
  | cons head tail ih =>
      simp [buildList, viewList, ih]

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

end

end TypePM.Runtime
