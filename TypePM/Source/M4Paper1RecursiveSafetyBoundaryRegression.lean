import TypePM.Source.M4RecursiveMatcherInputBridge
import TypePM.Source.M4Paper1ClosedMultisetExactRegression
import TypePM.Source.Paper1Programs

/-!
# The first concrete Paper 1 recursive-matcher boundary

This regression isolates the smallest constructor path of the real seven
clause `multiset` matcher: matching the empty-list pattern against the empty
list value.  The operational theorem below is about the actual ordered clause
dispatcher and `evalFuel`; it shows that every successful run returns exactly
the unique empty decomposition branch.

The remaining certificate records the still-unsolved static/runtime closure
connection without hiding it behind an arbitrary branch-typing callback.
-/

namespace TypePM.Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression

open TypePM.Runtime
open TypePM.Source.Paper1Programs

theorem nilClause_try_exact (fuel : Nat)
    (atomEnvironment matcherEnvironment : ValueEnvironment) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      (.ctor PatternCtor.nil []) Value.nilValue nilClause = .timeout ∨
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      (.ctor PatternCtor.nil []) Value.nilValue nilClause = .ok (.hit [[]]) := by
  cases fuel with
  | zero =>
      exact .inl rfl
  | succ fuel =>
      cases fuel with
      | zero =>
          exact .inl rfl
      | succ fuel =>
          exact .inr (by with_unfolding_all rfl)

theorem nilConstructor_dispatch_exact (fuel : Nat)
    (atomEnvironment matcherEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel fuel) atomEnvironment matcherEnvironment
      multisetClauses (.ctor PatternCtor.nil []) Value.nilValue = .timeout ∨
    dispatchMatcherClauses (evalFuel fuel) atomEnvironment matcherEnvironment
      multisetClauses (.ctor PatternCtor.nil []) Value.nilValue =
        .ok (.hit [[]]) := by
  rcases nilClause_try_exact fuel atomEnvironment matcherEnvironment with
    timeout | success
  · exact .inl (by
      simp [dispatchMatcherClauses, multisetClauses, firstHit, timeout])
  · exact .inr (by
      simp [dispatchMatcherClauses, multisetClauses, firstHit, success])

theorem nilConstructor_dispatch_shape (fuel : Nat)
    (matcherEnvironment : ValueEnvironment) :
    ZeroHoleConstructorDispatchShape (evalFuel fuel) matcherEnvironment
      multisetClauses PatternCtor.nil Value.nilValue := by
  constructor
  intro atomEnvironment branches dispatched
  have ordered := firstHit_sound dispatched
  cases ordered with
  | hit selected =>
      rcases nilClause_try_exact fuel atomEnvironment matcherEnvironment with
        timeout | success
      · rw [timeout] at selected
        contradiction
      · rw [success] at selected
        cases selected
        exact .inr rfl
  | skip missed tail =>
      rcases nilClause_try_exact fuel atomEnvironment matcherEnvironment with
        timeout | success
      · rw [timeout] at missed
        contradiction
      · rw [success] at missed
        simp at missed

theorem multiset_finalCatchAll : MatcherTyping.FinalCatchAll multisetClauses :=
  (MatcherTyping.finalCatchAll_iff multisetClauses).2 (by rfl)

/-! ## The actual closed matcher value -/

def listRecursiveClosure : Value :=
  Value.recursiveClosure [] (.matcher listMatcherClauses)

def multisetRecursiveClosure : Value :=
  Value.recursiveClosure [listRecursiveClosure] (.matcher multisetClauses)

def closedMultisetMatcherEnvironment : ValueEnvironment :=
  [.something, multisetRecursiveClosure, listRecursiveClosure]

def closedMultisetMatcherValue : Value :=
  .matcherV closedMultisetMatcherEnvironment multisetClauses multisetClauses

set_option maxRecDepth 100000 in
theorem closedMultisetMatcher_eval_exact :
    evalFuel 20 [] multisetSomething = .ok closedMultisetMatcherValue := by
  with_unfolding_all rfl

/-- On the nil constructor, the real closed matcher is a terminal zero-hole
atom for every callback fuel.  This fact uses the concrete ordered dispatcher,
not a typing assumption about its recursively captured closures. -/
theorem closedMultisetNil_terminal (callbackFuel : Nat) :
    ZeroHoleTerminalUserAtomReduction (evalFuel callbackFuel)
      ⟨.ctor PatternCtor.nil [], closedMultisetMatcherValue,
        Value.nilValue⟩ := by
  intro atomEnvironment
  rcases nilConstructor_dispatch_exact callbackFuel atomEnvironment
      closedMultisetMatcherEnvironment with timeout | success
  · exact .inl (by
      simp [evaluationAtomReducer, combineAtomReducers,
        closedMultisetMatcherValue,
        TypePM.Source.MatcherTyping.reduceBuiltinAtom_constructor_miss,
        reduceMatcherAtom, timeout])
  · exact .inr (.inr (by
      simp [evaluationAtomReducer, combineAtomReducers,
        closedMultisetMatcherValue,
        TypePM.Source.MatcherTyping.reduceBuiltinAtom_constructor_miss,
        reduceMatcherAtom, success, clauseResultToAtomReduction]))

theorem closedMultisetNil_recursiveAtom (callbackFuel : Nat) :
    RecursiveTotalMatchingAtomTyping expressionTyping (evalFuel callbackFuel)
      [] []
      ⟨.ctor PatternCtor.nil [], closedMultisetMatcherValue,
        Value.nilValue⟩ [] :=
  .zeroHoleTerminalUser (closedMultisetNil_terminal callbackFuel)

/-- Unconditional no-stuck search for the actual closed multiset matcher on
the nil constructor.  This is the maximal sound endpoint before introducing
callback-parametric typing for recursive closure values. -/
theorem closedMultisetNil_search_neverStuck
    (callbackFuel searchFuel : Nat) :
    (searchPatternFuel (evalFuel callbackFuel) searchFuel []
      (.ctor PatternCtor.nil []) closedMultisetMatcherValue
      Value.nilValue).NotStuck :=
  searchPatternFuel_zeroHoleTerminal_notStuck
    (closedMultisetNil_terminal callbackFuel) searchFuel []

/-- Static M4 acceptance, exact construction of the real runtime matcher
value, and all-fuel terminal nil search are connected in one fixture theorem.
The search conclusion is unconditional; only a general typing derivation for
the captured recursive closure remains outside this endpoint. -/
theorem closedMultisetNil_fixture_staticAndOperational :
    M4.Typing Paper1FrozenSignature.signature [] closedMultisetDefinition
        M4Paper1ClosedMultisetExactRegression.closedMultisetType ∧
      evalFuel 20 [] multisetSomething = .ok closedMultisetMatcherValue ∧
      ∀ callbackFuel searchFuel,
        (searchPatternFuel (evalFuel callbackFuel) searchFuel []
          (.ctor PatternCtor.nil []) closedMultisetMatcherValue
          Value.nilValue).NotStuck := by
  exact ⟨M4Paper1ClosedMultisetExactRegression.typing,
    closedMultisetMatcher_eval_exact,
    closedMultisetNil_search_neverStuck⟩

/-- Exact non-operational data still needed to turn the real closed multiset
nil path into `RecursiveTotalMatchingAtomTyping`.  In particular, `clauses`
must come from the capture-aware M4 bridge; the branch result itself is not a
field because `nilConstructor_dispatch_shape` already proves it. -/
structure ClosedMultisetNilRuntimeBoundary
    (expressionTyping : EmbeddedExpressionTyping) (fuel : Nat)
    (matcherEnvironment : ValueEnvironment) (definitionTypes : List Ty)
    (matcherTarget : Ty) : Prop where
  matcherEnvironmentTyped :
    EnvironmentTyping matcherEnvironment definitionTypes
  targetTyped : ValueTyping Value.nilValue matcherTarget
  clauses : TotalRuntimeMatcherClausesInputTyping expressionTyping []
    definitionTypes matcherTarget (.ctor PatternCtor.nil []) multisetClauses

/-- Once the capture-aware M4 closure boundary is supplied, the actual Paper
1 nil constructor atom follows with no arbitrary branch premise. -/
theorem ClosedMultisetNilRuntimeBoundary.toRecursiveAtom
    (boundary : ClosedMultisetNilRuntimeBoundary expressionTyping fuel
      matcherEnvironment definitionTypes matcherTarget) :
    RecursiveTotalMatchingAtomTyping expressionTyping (evalFuel fuel) [] []
      ⟨.ctor PatternCtor.nil [],
        .matcherV matcherEnvironment multisetClauses multisetClauses,
        Value.nilValue⟩ [] := by
  exact recursiveZeroHoleConstructorAtom_of_m4Input
    boundary.matcherEnvironmentTyped boundary.targetTyped boundary.clauses
    multiset_finalCatchAll (nilConstructor_dispatch_shape fuel matcherEnvironment)

/-- The real dispatcher is consequently safe for every finite search budget,
provided only the exact static closure boundary and evaluator safety. -/
theorem ClosedMultisetNilRuntimeBoundary.search_typedSafe
    (boundary : ClosedMultisetNilRuntimeBoundary expressionTyping callbackFuel
      matcherEnvironment definitionTypes matcherTarget)
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping (evalFuel callbackFuel))
    (searchFuel : Nat) :
    TypedMatchingSearchResult []
      (searchPatternFuel (evalFuel callbackFuel) searchFuel []
        (.ctor PatternCtor.nil [])
        (.matcherV matcherEnvironment multisetClauses multisetClauses)
        Value.nilValue) := by
  exact searchZeroHoleConstructorFuel_recursiveTotalTypedSafe
    (expressionTyping := expressionTyping) (eval := evalFuel callbackFuel)
    (constructor := PatternCtor.nil)
    (matcherValue := .matcherV matcherEnvironment multisetClauses multisetClauses)
    (target := Value.nilValue)
    evalSafe EnvironmentTyping.nil boundary.toRecursiveAtom searchFuel

theorem ClosedMultisetNilRuntimeBoundary.search_neverStuck
    (boundary : ClosedMultisetNilRuntimeBoundary expressionTyping callbackFuel
      matcherEnvironment definitionTypes matcherTarget)
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping (evalFuel callbackFuel))
    (searchFuel : Nat) :
    (searchPatternFuel (evalFuel callbackFuel) searchFuel []
      (.ctor PatternCtor.nil [])
      (.matcherV matcherEnvironment multisetClauses multisetClauses)
      Value.nilValue).NotStuck := by
  rcases boundary.search_typedSafe evalSafe searchFuel with timeout |
    ⟨answers, success, answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-! ## Exact remaining M4 closure boundary -/

/-- The missing closed-multiset proof object is now stated entirely in source
terms.  `input` is the genuine M4 matcher-literal derivation with capture
typing for the nil input; `bridge` types only its concrete checked leaves;
`semantic` is the solver result; and `contextCompatible` connects the source
definition context to the environment stored in the evaluated closure. -/
structure ClosedMultisetNilM4Boundary
    (expressionTyping : EmbeddedExpressionTyping) (callbackFuel : Nat)
    (matcherEnvironment : ValueEnvironment) (definitionTypes : List Ty)
    (context : Context) (supply : Supply) (generated : Generated)
    (next : Supply) (solution : Subst) : Prop where
  input : MatcherLiteralTotalInputElaboratesUsing
    (M4.ElaboratesFuel Paper1FrozenSignature.signature callbackFuel)
    expressionTyping solution [] (.ctor PatternCtor.nil []) context
    multisetClauses supply generated next
  bridge : SolvedM4CheckedExpressionBridge expressionTyping
  semantic : generated.SemanticSolution solution
  contextCompatible :
    MonomorphicContextCompatible context definitionTypes solution
  matcherEnvironmentTyped :
    EnvironmentTyping matcherEnvironment definitionTypes
  targetTyped : ValueTyping Value.nilValue
    ((Ty.var ⟨supply.ty⟩).apply solution)

/-- The capture-aware M4 bridge automatically removes the source-level fields
from the runtime boundary.  No branch preservation premise is supplied. -/
theorem ClosedMultisetNilM4Boundary.toRuntimeBoundary
    (boundary : ClosedMultisetNilM4Boundary expressionTyping callbackFuel
      matcherEnvironment definitionTypes context supply generated next solution) :
    ClosedMultisetNilRuntimeBoundary expressionTyping callbackFuel
      matcherEnvironment definitionTypes
      ((Ty.var ⟨supply.ty⟩).apply solution) := by
  refine ⟨boundary.matcherEnvironmentTyped, boundary.targetTyped, ?_⟩
  exact boundary.input.toTotalInputTyping_of_m4Fuel boundary.bridge
    boundary.semantic boundary.contextCompatible

theorem ClosedMultisetNilM4Boundary.toRecursiveAtom
    (boundary : ClosedMultisetNilM4Boundary expressionTyping callbackFuel
      matcherEnvironment definitionTypes context supply generated next solution) :
    RecursiveTotalMatchingAtomTyping expressionTyping (evalFuel callbackFuel)
      [] []
      ⟨.ctor PatternCtor.nil [],
        .matcherV matcherEnvironment multisetClauses multisetClauses,
        Value.nilValue⟩ [] :=
  boundary.toRuntimeBoundary.toRecursiveAtom

theorem ClosedMultisetNilM4Boundary.search_neverStuck
    (boundary : ClosedMultisetNilM4Boundary expressionTyping callbackFuel
      matcherEnvironment definitionTypes context supply generated next solution)
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping (evalFuel callbackFuel))
    (searchFuel : Nat) :
    (searchPatternFuel (evalFuel callbackFuel) searchFuel []
      (.ctor PatternCtor.nil [])
      (.matcherV matcherEnvironment multisetClauses multisetClauses)
      Value.nilValue).NotStuck :=
  boundary.toRuntimeBoundary.search_neverStuck evalSafe searchFuel

end TypePM.Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
