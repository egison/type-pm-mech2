import TypePM.RecursiveTotalMatchingSafety
import TypePM.Source.M4MatchingAtomRuntimeBridge
import TypePM.Source.M4RecursiveMatcherTotalBridge

/-!
# Capture-aware M4 bridge for recursive matcher bodies

The recursive matcher bridge types clause bodies with a callback-parametric
expression judgment, but its earlier public endpoint did not retain the
typing of pattern-pattern captures for one concrete input pattern.  Runtime
dispatch needs exactly that extra fact.  The relations in this file keep the
original M4 derivations and add only the capture premise produced by header
inspection.

The zero-hole constructor endpoint at the end separates the remaining
operational obligation from preservation.  It asks only for the exact shape
of branches returned by the real dispatch (`[]` or `[[]]`); it does not assume
that arbitrary delegated branches already have the desired conclusion type.
-/

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- One recursive-M4 clause derivation, enriched with capture typing for one
concrete source pattern. -/
inductive MatcherClauseTotalInputElaboratesUsing
    (expressionRelation : ExpressionElaborationRelation)
    (expressionTyping : EmbeddedExpressionTyping)
    (solution : Subst) (atomEnvironmentTypes : List Ty) (pattern : Pattern)
    (context : Context) (matcherTarget : Ty) :
    MatcherClause → Supply → GeneratedMatcherClause → Supply → Prop where
  | mk {header nextMatchers arms supply generatedHeader afterHeader generatedNext
      afterNext generatedArms next}
      (shape : (MatcherClause.mk header nextMatchers arms).toShape.check
        Paper1FrozenSignature.signature = true)
      (headerElaboration : PPatElaborates Paper1FrozenSignature.signature
        header matcherTarget none supply generatedHeader afterHeader)
      (nextElaboration : NextMatchersElaborateUsing expressionRelation
        (Pattern.extendContext generatedHeader.captures context)
        nextMatchers generatedHeader.holes afterHeader generatedNext afterNext)
      (armsElaboration : MatcherArmsElaborateUsing expressionRelation
        DPatElaborates Paper1FrozenSignature.signature context
        generatedHeader.captures matcherTarget generatedHeader.holes arms
        afterNext generatedArms next)
      (captures : ∀ {dispatch},
        inspectPatternPattern header pattern = some dispatch →
        RuntimeCaptureExpressionsTyping expressionTyping atomEnvironmentTypes
          dispatch.captures (Ty.applyList solution generatedHeader.captures)) :
      MatcherClauseTotalInputElaboratesUsing expressionRelation expressionTyping
        solution atomEnvironmentTypes pattern context matcherTarget
        (.mk header nextMatchers arms) supply
        ⟨generatedHeader.holes, generatedHeader.evidence,
          ⟨generatedHeader.hard ++ generatedNext.hard ++
              generatedArms.checks.hard,
            generatedNext.pending ++ generatedArms.checks.pending⟩⟩ next

/-- Source-order list form of the capture-aware recursive-M4 relation. -/
inductive MatcherClausesTotalInputElaborateUsing
    (expressionRelation : ExpressionElaborationRelation)
    (expressionTyping : EmbeddedExpressionTyping)
    (solution : Subst) (atomEnvironmentTypes : List Ty) (pattern : Pattern)
    (context : Context) (matcherTarget : Ty) :
    List MatcherClause → Supply → GeneratedMatcherClauses → Supply → Prop where
  | nil {supply} :
      MatcherClausesTotalInputElaborateUsing expressionRelation expressionTyping
        solution atomEnvironmentTypes pattern context matcherTarget [] supply
        ⟨[], GeneratedChecks.empty⟩ supply
  | cons {clause clauses supply generatedClause afterClause generatedClauses next}
      (head : MatcherClauseTotalInputElaboratesUsing expressionRelation
        expressionTyping solution atomEnvironmentTypes pattern context
        matcherTarget clause supply generatedClause afterClause)
      (tail : MatcherClausesTotalInputElaborateUsing expressionRelation
        expressionTyping solution atomEnvironmentTypes pattern context
        matcherTarget clauses afterClause generatedClauses next) :
      MatcherClausesTotalInputElaborateUsing expressionRelation expressionTyping
        solution atomEnvironmentTypes pattern context matcherTarget
        (clause :: clauses) supply
        ⟨match generatedClause.evidence with
          | some evidence => evidence :: generatedClauses.evidences
          | none => generatedClauses.evidences,
          generatedClause.checks.append generatedClauses.checks⟩ next

/-- Literal form of the capture-aware recursive-M4 relation. -/
inductive MatcherLiteralTotalInputElaboratesUsing
    (expressionRelation : ExpressionElaborationRelation)
    (expressionTyping : EmbeddedExpressionTyping)
    (solution : Subst) (atomEnvironmentTypes : List Ty) (pattern : Pattern)
    (context : Context) :
    List MatcherClause → Supply → Generated → Supply → Prop where
  | mk {clauses supply generatedClauses next}
      (checked : StaticChecksHold Paper1FrozenSignature.signature clauses)
      (clausesElaboration : MatcherClausesTotalInputElaborateUsing
        expressionRelation expressionTyping solution atomEnvironmentTypes
        pattern context (.var ⟨supply.ty⟩) clauses
        ⟨supply.ty + 1, supply.cap + 1⟩ generatedClauses next) :
      MatcherLiteralTotalInputElaboratesUsing expressionRelation expressionTyping
        solution atomEnvironmentTypes pattern context clauses supply
        ⟨.matcher (.var ⟨supply.cap⟩) (.var ⟨supply.ty⟩),
          evidenceEquations (.var ⟨supply.cap⟩) generatedClauses.evidences ++
            generatedClauses.checks.hard,
          generatedClauses.checks.pending⟩ next

theorem MatcherClauseTotalInputElaboratesUsing.elaboration
    (input : MatcherClauseTotalInputElaboratesUsing expressionRelation
      expressionTyping solution atomEnvironmentTypes pattern context
      matcherTarget clause supply generated next) :
    MatcherClauseElaboratesUsing expressionRelation PPatElaborates DPatElaborates
      Paper1FrozenSignature.signature context matcherTarget clause supply
      generated next := by
  cases input with
  | mk shape header nextMatchers arms captures =>
      exact .mk (MatcherClauseShape.wellFormed_of_check shape)
        header nextMatchers arms

theorem MatcherClausesTotalInputElaborateUsing.elaboration
    (input : MatcherClausesTotalInputElaborateUsing expressionRelation
      expressionTyping solution atomEnvironmentTypes pattern context
      matcherTarget clauses supply generated next) :
    MatcherClausesElaborateUsing expressionRelation PPatElaborates DPatElaborates
      Paper1FrozenSignature.signature context matcherTarget clauses supply
      generated next := by
  induction input with
  | nil => exact .nil
  | cons head tail induction => exact .cons head.elaboration induction

/-- Erasing only the input-specific capture evidence recovers the independent
recursive-M4 matcher-literal derivation. -/
theorem MatcherLiteralTotalInputElaboratesUsing.elaboration
    (input : MatcherLiteralTotalInputElaboratesUsing expressionRelation
      expressionTyping solution atomEnvironmentTypes pattern context clauses
      supply generated next) :
    MatcherLiteralElaboratesUsing expressionRelation PPatElaborates DPatElaborates
      Paper1FrozenSignature.signature context clauses supply generated next := by
  cases input with
  | mk checked clauses => exact .mk checked clauses.elaboration

theorem MatcherClauseTotalInputElaboratesUsing.toTotalInputTyping_of_m4Fuel
    (input : MatcherClauseTotalInputElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      expressionTyping solution atomEnvironmentTypes pattern context
      matcherTarget clause supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalRuntimeMatcherClauseInputTyping expressionTyping atomEnvironmentTypes
      definitionTypes (matcherTarget.apply solution) pattern clause := by
  cases input with
  | mk shape header nextMatchers arms captures =>
      rename_i headerExpression nextMatcherExpression matcherArms
        generatedHeader afterHeader generatedNext afterNext generatedArms
      have headerSolved : Solves solution generatedHeader.hard := by
        intro equation member
        exact semantic.1 equation (by simp [member])
      have nextSemantic : generatedNext.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · intro obligation member
          exact semantic.2 obligation (by simp [member])
      have armsSemantic : generatedArms.checks.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · intro obligation member
          exact semantic.2 obligation (by simp [member])
      have nextContextCompatible :=
        runtimeContextCompatible_extendPatternContext
          (bindings := generatedHeader.captures) contextCompatible
      exact .mk
        (header.toRuntimePPatTyping headerSolved)
        (nextMatchers.toTotalRuntimeNextMatchersTyping_of_m4Fuel bridge
          nextSemantic nextContextCompatible)
        (arms.toTotalRuntimeMatcherArmsTyping_of_m4Fuel bridge armsSemantic
          contextCompatible)
        captures

theorem MatcherClausesTotalInputElaborateUsing.toTotalInputTyping_of_m4Fuel
    (input : MatcherClausesTotalInputElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      expressionTyping solution atomEnvironmentTypes pattern context
      matcherTarget clauses supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalRuntimeMatcherClausesInputTyping expressionTyping atomEnvironmentTypes
      definitionTypes (matcherTarget.apply solution) pattern clauses := by
  induction input with
  | nil => exact .nil
  | cons head tail induction =>
      simp only [GeneratedChecks.runtimeSolution_append] at semantic
      exact .cons
        (head.toTotalInputTyping_of_m4Fuel bridge semantic.1 contextCompatible)
        (induction semantic.2)

/-- The enriched M4 literal directly produces the input-indexed certificate
used by recursive runtime dispatch. -/
theorem MatcherLiteralTotalInputElaboratesUsing.toTotalInputTyping_of_m4Fuel
    (input : MatcherLiteralTotalInputElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      expressionTyping solution atomEnvironmentTypes pattern context clauses
      supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalRuntimeMatcherClausesInputTyping expressionTyping atomEnvironmentTypes
      definitionTypes ((Ty.var ⟨supply.ty⟩).apply solution) pattern clauses := by
  cases input with
  | mk checked clauses =>
      rename_i generatedClauses
      have clausesSemantic : generatedClauses.checks.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · exact semantic.2
      exact clauses.toTotalInputTyping_of_m4Fuel bridge clausesSemantic
        contextCompatible

end TypePM.Source.MatcherTyping

namespace TypePM.Runtime

open TypePM.Source

/-- Exact operational information needed for a constructor with no fields.
Successful dispatch may return no decomposition or the unique empty
decomposition.  Both cases bind no values. -/
structure ZeroHoleConstructorDispatchShape
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (matcherEnvironment : ValueEnvironment) (clauses : List MatcherClause)
    (constructor : PatternCtor) (target : Value) : Prop where
  branches : ∀ (atomEnvironment : ValueEnvironment) {recursiveBranches},
    dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
        (.ctor constructor []) target = .ok (.hit recursiveBranches) →
    recursiveBranches = [] ∨ recursiveBranches = [[]]

/-- M4-derived input typing plus the exact zero-hole dispatch shape is enough
to build the evaluator-indexed recursive atom certificate. -/
theorem recursiveZeroHoleConstructorAtom_of_m4Input
    (matcherEnvironmentTyped :
      EnvironmentTyping matcherEnvironment definitionTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (clausesTyped : TotalRuntimeMatcherClausesInputTyping expressionTyping
      environmentTypes definitionTypes matcherTarget (.ctor constructor [])
      clauses)
    (finalCatchAll : MatcherTyping.FinalCatchAll clauses)
    (shape : ZeroHoleConstructorDispatchShape eval matcherEnvironment clauses
      constructor target) :
    RecursiveTotalMatchingAtomTyping expressionTyping eval environmentTypes []
      ⟨.ctor constructor [], .matcherV matcherEnvironment clauses clauses,
        target⟩ [] := by
  apply RecursiveTotalMatchingAtomTyping.user
    (fun atomEnvironment => by
      exact TypePM.Source.MatcherTyping.reduceBuiltinAtom_constructor_miss
        eval atomEnvironment _ _)
    matcherEnvironmentTyped targetTyped clausesTyped finalCatchAll
  intro atomEnvironment holes recursiveBranches dispatched delegated branch member
  rcases shape.branches atomEnvironment dispatched with empty | singleton
  · subst recursiveBranches
    simp at member
  · subst recursiveBranches
    simp only [List.mem_singleton] at member
    subst branch
    exact RecursiveTotalMatchingAtomsTyping.nil

/-- The corresponding finite depth-first search is safe for the same real
evaluator callback; no statement about unrelated callbacks is required. -/
theorem searchZeroHoleConstructorFuel_recursiveTotalTypedSafe
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (environmentTyped : EnvironmentTyping environment environmentTypes)
    (atomTyped : RecursiveTotalMatchingAtomTyping expressionTyping eval
      environmentTypes []
      ⟨.ctor constructor [], matcherValue, target⟩ [])
    (fuel : Nat) :
    TypedMatchingSearchResult []
      (searchPatternFuel eval fuel environment (.ctor constructor [])
        matcherValue target) :=
  searchPatternFuel_recursiveTotalTypedSafe
    (expressionTyping := expressionTyping) (eval := eval)
    evalSafe environmentTyped atomTyped fuel

end TypePM.Runtime
