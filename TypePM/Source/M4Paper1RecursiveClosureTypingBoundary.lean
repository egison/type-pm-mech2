import TypePM.Source.M4Paper1RecursiveSafetyBoundaryRegression

/-!
# Why the old runtime environment judgment cannot type the Paper 1 matcher

The concrete closed `multiset` matcher captures two recursive function
closures.  Each closure body is a matcher literal containing an arm whose body
uses `matchAll`.  `ValueTyping.recursiveClosure` requires the closure body to
have the older `RuntimeTyping` judgment, while that judgment intentionally has
no `matcher` or `matchAll` rule.  Consequently the old
`EnvironmentTyping` field in the first boundary certificate was not merely
unproved: it excluded the real fixture.

The general completion therefore needs a callback-parametric value and
environment family with a recursive-closure rule whose body premise is the
total expression judgment.  The terminal nil search does not wait for that
family because it has zero holes, zero bindings, and zero recursive atoms; its
separate operational proof lives in
`M4Paper1RecursiveSafetyBoundaryRegression`.
-/

namespace TypePM.Source.MatcherTyping.M4Paper1RecursiveClosureTypingBoundary

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open M4Paper1RecursiveSafetyBoundaryRegression

private def IsNotMatcherLiteral : Expr → Prop
  | .matcher _ => False
  | _ => True

private theorem runtimeTyping_isNotMatcherLiteral
    (typing : RuntimeTyping expression target context) :
    IsNotMatcherLiteral expression := by
  induction typing using RuntimeTyping.rec
    (motive_2 := fun _ _ _ _ => True) with
  | var => trivial
  | lit => trivial
  | something => trivial
  | boolTrue => trivial
  | boolFalse => trivial
  | listNil => trivial
  | listCons => trivial
  | tuple => trivial
  | lam => trivial
  | app => trivial
  | letE => trivial
  | fixE => trivial
  | add => trivial
  | append => trivial
  | member => trivial
  | deleteFirst => trivial
  | map => trivial
  | pairFirst => trivial
  | pairSecond => trivial
  | ifE => trivial
  | checked source conversion induction => exact induction
  | nil => trivial
  | cons => trivial

/-- The old runtime expression judgment cannot type a matcher literal at any
type or context.  Its checked conversion rule cannot change the expression
syntax, so induction closes that wrapper as well. -/
theorem matcherLiteral_not_runtimeTyping (clauses : List MatcherClause) :
    ∀ target context, ¬ RuntimeTyping (.matcher clauses) target context := by
  intro target context typing
  exact runtimeTyping_isNotMatcherLiteral typing

/-- Therefore a recursive closure whose body is a matcher literal cannot be
typed by the old value judgment. -/
theorem recursiveMatcherClosure_not_valueTyping
    (environment : ValueEnvironment) (clauses : List MatcherClause)
    (domain codomain : Ty) :
    ¬ ValueTyping (Value.recursiveClosure environment (.matcher clauses))
      (.fn domain codomain) := by
  intro typing
  rcases typing.function_canonical with
    ⟨plainEnvironment, context, body, equality, environmentTyped, bodyTyped⟩ |
    ⟨recursiveEnvironment, context, body, equality, environmentTyped,
      bodyTyped⟩
  · cases equality
  · cases equality
    exact matcherLiteral_not_runtimeTyping clauses _ _ bodyTyped

theorem multisetRecursiveClosure_not_valueTyping :
    ∀ domain codomain,
      ¬ ValueTyping multisetRecursiveClosure (.fn domain codomain) := by
  intro domain codomain
  exact recursiveMatcherClosure_not_valueTyping [listRecursiveClosure]
    multisetClauses domain codomain

theorem listRecursiveClosure_not_valueTyping :
    ∀ domain codomain,
      ¬ ValueTyping listRecursiveClosure (.fn domain codomain) := by
  intro domain codomain
  exact recursiveMatcherClosure_not_valueTyping [] listMatcherClauses
    domain codomain

/-- This is the concrete failed field of the earlier boundary: no list of old
runtime types can certify the environment stored in the actual closed
multiset matcher value. -/
theorem closedMultisetMatcherEnvironment_not_environmentTyping :
    ∀ elementMatcherType multisetDomain multisetCodomain listDomain
        listCodomain,
      ¬ EnvironmentTyping closedMultisetMatcherEnvironment
        [elementMatcherType, .fn multisetDomain multisetCodomain,
          .fn listDomain listCodomain] := by
  intro elementMatcherType multisetDomain multisetCodomain listDomain
    listCodomain typing
  cases typing with
  | cons somethingTyped tailTyped =>
      cases tailTyped with
      | cons multisetTyped listTailTyped =>
          exact multisetRecursiveClosure_not_valueTyping _ _ multisetTyped

/-- Any general replacement for the old closure rule must at least provide
this callback-parametric shape: captured values are typed by the same total
value/environment family, and the recursive body is typed by the chosen total
expression judgment under the self and argument entries.  This structure is
an interface requirement, not an assumption used by the nil proof. -/
structure TotalRecursiveClosureRuleRequirement
    (totalValueTyping : Value → Ty → Prop)
    (totalEnvironmentTyping : ValueEnvironment → List Ty → Prop)
    (expressionTyping : EmbeddedExpressionTyping) : Prop where
  embedsOldValues : ∀ {value target},
    ValueTyping value target → totalValueTyping value target
  environmentNil : totalEnvironmentTyping [] []
  environmentCons : ∀ {value target environment context},
    totalValueTyping value target →
    totalEnvironmentTyping environment context →
    totalEnvironmentTyping (value :: environment) (target :: context)
  recursiveClosure : ∀ {environment context body domain codomain},
    totalEnvironmentTyping environment context →
    expressionTyping (domain :: .fn domain codomain :: context) body codomain →
    totalValueTyping (Value.recursiveClosure environment body)
      (.fn domain codomain)

end TypePM.Source.MatcherTyping.M4Paper1RecursiveClosureTypingBoundary
