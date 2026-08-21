import TypePM.Source.M4TwoIndexPatternDispatchProducer
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility
import TypePM.Source.Paper1Programs
import TypePM.TwoIndexMatchAllSafety
import TypePM.UserMatcherExhaustiveness

/-!
# Bounded initial-state composition for one solved Paper 1 `matchAll`

This module has one deliberately narrow endpoint.  It applies only to a
source `matchAll` whose input pattern is `.var` and whose matcher is the
one-clause literal containing the actual final catch-all clause from the
Paper 1 program.  Its static premise is one left-to-right M4 derivation of the
whole node: target, pattern, matcher, then body.  In particular, the pattern
and matcher cannot both be attached to an unrelated initial supply.

The endpoint combines four separately checked pieces:

* the target, pattern, capture-aware matcher, and body components of one
  enclosing M4 `matchAll` derivation;
* one semantic solution of the combined `Generated.fromMatchAll` block;
* a non-stuck actual local dispatch whose successful branches carry finite
  `M4TwoIndexMatchingBranchObligations`;
* a caller-selected local atom relation and reducer-preservation law.

The combined solution supplies the target-pattern equality, the complete
matcher block's semantic solution, and its matcher-to-slot conversion.  The
local branch obligation receives all three, rather than accepting a separate
matcher solution that could be unrelated to the enclosing node.  The matcher
input supplies its checked final-catch-all fact, which rules out a normal
dispatch miss.  Dispatch timeout is retained as a valid local certificate; a
hit is converted from the conditional bounded branch obligations.  There is
no structural `EnvironmentTyping` or `ValueTyping` premise, no completed-search
equation/result, and no final evaluation-safety premise.

This is a bounded depth-first-search composition lemma for one concrete
Paper 1 clause.  It is not a general M4 source-to-runtime producer and makes no
claim about the separate fair-search semantics used as the APLAS default.
-/

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime
open TypePM.Source.Paper1Programs

/-- The exact capture-aware counterpart of one enclosing M4 `matchAll`
derivation for the Paper 1 catch-all literal and a variable input pattern.

The component indices record the real source order.  Expression leaves use
fuel `m4Fuel + 1`; unfolding the matcher expression spends one unit and leaves
`m4Fuel` for the literal's clauses. -/
structure Paper1CatchAllVariableMatchAllTotalInputElaboratesUsing
    (m4Fuel : Nat) (expressionTyping : EmbeddedExpressionTyping)
    (solution : Subst) (atomEnvironmentTypes : List Ty) (context : Context)
    (target body : Expr) (supply : Supply)
    (generatedTarget : Generated) (afterTarget : Supply)
    (generatedPattern : GeneratedPattern) (afterPattern : Supply)
    (generatedMatcher : Generated) (afterMatcher : Supply)
    (generatedBody : Generated) (next : Supply) : Prop where
  targetElaboration : M4.ElaboratesFuel Paper1FrozenSignature.signature
    (m4Fuel + 1) context target supply generatedTarget afterTarget
  patternElaboration : PatternElaboratesUsing
    (M4.ElaboratesFuel Paper1FrozenSignature.signature (m4Fuel + 1))
    Paper1FrozenSignature.signature context [] .var [] afterTarget
    generatedPattern afterPattern
  matcherInput : MatcherLiteralTotalInputElaboratesUsing
    (M4.ElaboratesFuel Paper1FrozenSignature.signature m4Fuel)
    Paper1FrozenSignature.signature expressionTyping solution
    atomEnvironmentTypes .var context [catchAllClause] afterPattern
    generatedMatcher afterMatcher
  bodyElaboration : M4.ElaboratesFuel Paper1FrozenSignature.signature
    (m4Fuel + 1) (Pattern.extendContext generatedPattern.bindings context)
    body afterMatcher generatedBody next

/-- Erasing capture evidence recovers the ordinary enclosing relational M4
derivation with exactly the same component supplies and generated blocks. -/
theorem Paper1CatchAllVariableMatchAllTotalInputElaboratesUsing.toMatchAllElaboratesUsing
    (input : Paper1CatchAllVariableMatchAllTotalInputElaboratesUsing
      m4Fuel expressionTyping solution atomEnvironmentTypes context target body
      supply generatedTarget afterTarget generatedPattern afterPattern
      generatedMatcher afterMatcher generatedBody next) :
    MatchAllElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature (m4Fuel + 1))
      Paper1FrozenSignature.signature context target
      (.matcher [catchAllClause]) .var body supply
      (Generated.fromMatchAll generatedTarget generatedPattern
        generatedMatcher generatedBody) next := by
  have matcherElaboration :
      M4.ElaboratesFuel Paper1FrozenSignature.signature (m4Fuel + 1)
        context (.matcher [catchAllClause]) afterPattern generatedMatcher
        afterMatcher := by
    simpa only [M4.ElaboratesFuel] using input.matcherInput.elaboration
  exact .mk input.targetElaboration input.patternElaboration
    matcherElaboration input.bodyElaboration

/-- Extract the proof-level final catch-all fact from the complete M4 input.
Keeping this projection explicit is what lets the local producer accept a
non-stuck dispatch rather than an exact timeout-or-hit equation. -/
private theorem paper1CatchAll_finalCatchAll_of_input
    (input : MatcherLiteralTotalInputElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature m4Fuel)
      Paper1FrozenSignature.signature expressionTyping solution
      environmentTypes pattern context [catchAllClause] matcherSupply
      matcherGenerated matcherNext) :
    FinalCatchAll [catchAllClause] := by
  cases input with
  | mk checked clauses => exact checked.finalCatchAll

/-- A variable pattern projected from the callback-parametric enclosing rule
is also an independent M4 variable-pattern derivation. -/
private theorem variablePatternElaboration_of_using
    (elaboration : PatternElaboratesUsing expressionRelation signature context
      [] .var [] supply generated next) :
    PatternElaborates signature context [] .var [] supply generated next := by
  cases elaboration
  exact .var

private theorem fromMatchAll_patternSemantic
    (semantic : Generated.SemanticSolution
      (Generated.fromMatchAll target pattern matcher body) solution) :
    GeneratedPatternRuntimeSolution pattern solution := by
  constructor
  · intro equation member
    exact semantic.1 equation (by
      simp [Generated.fromMatchAll, member])
  · intro obligation member
    exact semantic.2 obligation (by
      simp [Generated.fromMatchAll, member])

private theorem fromMatchAll_matcherSemantic
    (semantic : Generated.SemanticSolution
      (Generated.fromMatchAll target pattern matcher body) solution) :
    matcher.SemanticSolution solution := by
  constructor
  · intro equation member
    exact semantic.1 equation (by
      simp [Generated.fromMatchAll, member])
  · intro obligation member
    exact semantic.2 obligation (by
      simp [Generated.fromMatchAll, member])

private theorem fromMatchAll_target_eq
    (semantic : Generated.SemanticSolution
      (Generated.fromMatchAll target pattern matcher body) solution) :
    pattern.dual.target.apply solution = target.target.apply solution := by
  have solved := semantic.1 (.ty pattern.dual.target target.target) (by
    simp [Generated.fromMatchAll])
  simpa [Equation.Holds] using solved

private theorem fromMatchAll_matcherToSlot
    (semantic : Generated.SemanticSolution
      (Generated.fromMatchAll target pattern matcher body) solution) :
    ∃ conversionClass,
      CheckConversion conversionClass (matcher.target.apply solution)
        ((Ty.slot pattern.dual.capability target.target).apply solution) := by
  exact semantic.2
    ⟨matcher.target, Ty.slot pattern.dual.capability target.target⟩ (by
      simp [Generated.fromMatchAll])

/-- Produce the bounded two-index initial state from the exact corresponding
full M4 derivation of a variable-pattern `matchAll` using only the real Paper 1
final catch-all clause.

`searchFuel + 1` is shared by target evaluation, matcher evaluation, atom
callbacks, and the initial DFS state.  `residual` is the independently retained
logical answer index.  The current M4 relations do not generate actual branch
preservation or the local reducer law, so both remain honest bounded premises.
The dispatch premise is only `NotStuck`; exact hit equations are required only
inside the conditional branch obligation.  The local branch premise receives
the matcher semantics, target equality, and matcher-to-slot conversion
projected from the one combined solution. -/
theorem Paper1CatchAllVariableMatchAllTotalInputElaboratesUsing.evaluatedTwoIndexInitialState_of_boundedLocalWork
    (input : Paper1CatchAllVariableMatchAllTotalInputElaboratesUsing
      m4Fuel expressionTyping solution environmentTypes context targetExpression
      bodyExpression supply generatedTarget afterTarget generatedPattern
      afterPattern generatedMatcher afterMatcher generatedBody next)
    (combinedSemantic :
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody).SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context environmentTypes solution)
    (targetSuccess :
      evalFuel (searchFuel + 1) environment targetExpression = .ok targetValue)
    (matcherSuccess :
      evalFuel (searchFuel + 1) environment (.matcher [catchAllClause]) =
        .ok (.matcherV matcherEnvironment original [catchAllClause]))
    (dispatchNotStuck :
      (dispatchMatcherClauses (evalFuel (searchFuel + 1)) environment
        matcherEnvironment [catchAllClause] .var targetValue).NotStuck)
    (atomsSafe : ∀ {newBindings branches},
      generatedMatcher.SemanticSolution solution →
      (∃ conversionClass,
        CheckConversion conversionClass
          (generatedMatcher.target.apply solution)
          ((Ty.slot generatedPattern.dual.capability generatedTarget.target).apply
            solution)) →
      PatternBinds
          (fun runtimeContext expression target =>
            RuntimeTyping expression target runtimeContext)
          environmentTypes [] .var
          (generatedTarget.target.apply solution) newBindings →
        dispatchMatcherClauses (evalFuel (searchFuel + 1)) environment
            matcherEnvironment [catchAllClause] .var targetValue =
          .ok (.hit branches) →
        ∀ branch ∈ branches,
          M4TwoIndexMatchingBranchObligations atomRelation
            (fun runtimeContext expression target =>
              RuntimeTyping expression target runtimeContext)
            searchFuel residual environmentTypes [] branch [.var]
            [generatedTarget.target.apply solution] newBindings)
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (bindingsAppend :
      IndexedMatchingInvariant.AppendClosed bindingsInvariant)
    (atomDownward :
      TwoIndexMatchingAtomRelation.DownwardClosed atomRelation)
    (reducerSafe : TwoIndexRelationalAtomReducerTypedSafe
      environmentInvariant bindingsInvariant atomRelation
      (evaluationAtomReducer (evalFuel (searchFuel + 1))))
    (environmentTyped : environmentInvariant (searchFuel + 1 + residual)
      environment environmentTypes)
    (emptyBindingsTyped : bindingsInvariant (searchFuel + 1 + residual) [] [])
    (builtinMiss :
      reduceBuiltinAtom (evalFuel (searchFuel + 1)) environment
        ⟨.var,
          .matcherV matcherEnvironment original [catchAllClause], targetValue⟩ =
            .ok .miss) :
    EvaluatedTwoIndexInitialStateTyping environmentInvariant bindingsInvariant
      (searchFuel + 1) residual environment targetExpression
      (.matcher [catchAllClause]) .var
      (Ty.applyList solution generatedPattern.bindings) := by
  have patternElaboration :=
    variablePatternElaboration_of_using input.patternElaboration
  have patternSemantic := fromMatchAll_patternSemantic combinedSemantic
  have matcherSemantic := fromMatchAll_matcherSemantic combinedSemantic
  have targetEq := fromMatchAll_target_eq combinedSemantic
  have matcherToSlot := fromMatchAll_matcherToSlot combinedSemantic
  have finalCatchAll :=
    paper1CatchAll_finalCatchAll_of_input input.matcherInput
  obtain ⟨newBindings, patternTyped, bindingsEq⟩ :=
    TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
      patternElaboration Paper1FrozenSignature.runtimeCompatible
      DirectRuntimePatternSupported.var patternSemantic contextCompatible
  have patternTypedAtTarget :
      PatternBinds
        (fun runtimeContext expression target =>
          RuntimeTyping expression target runtimeContext)
        environmentTypes [] .var (generatedTarget.target.apply solution)
        newBindings := by
    rw [← targetEq]
    exact patternTyped
  have dispatchTyped : TwoIndexPatternDispatchCertificate
      (relationalTwoIndexMatchingBranchRelation atomRelation) searchFuel
      residual environmentTypes [] newBindings
      (dispatchMatcherClauses (evalFuel (searchFuel + 1)) environment
        matcherEnvironment [catchAllClause] .var targetValue) := by
    generalize dispatchEq :
      dispatchMatcherClauses (evalFuel (searchFuel + 1)) environment
        matcherEnvironment [catchAllClause] .var targetValue = dispatchResult
    cases dispatchResult with
    | timeout => exact .timeout
    | stuck =>
        rw [dispatchEq] at dispatchNotStuck
        exact dispatchNotStuck.elim
    | ok result =>
        cases result with
        | miss =>
            exact False.elim
              (finalCatchAll_dispatch_ne_miss finalCatchAll dispatchEq)
        | hit branches =>
            exact TwoIndexPatternDispatchCertificate.hitOfM4BranchObligations
              (atomsSafe matcherSemantic matcherToSlot patternTypedAtTarget
                dispatchEq)
  have initialState :=
    dispatchTyped.toTwoIndexUserMatcherStateTyping
      environmentDownward bindingsDownward bindingsAppend atomDownward
      reducerSafe environmentTyped emptyBindingsTyped builtinMiss
      (RelationalTwoIndexMatchingBranchTyping.nil
        (atomRelation := atomRelation) (searchFuel := searchFuel)
        (residual := residual) (environmentTypes := environmentTypes)
        (bindingTypes := newBindings))
  intro actualTarget actualMatcher actualTargetSuccess actualMatcherSuccess
  rw [targetSuccess] at actualTargetSuccess
  cases actualTargetSuccess
  rw [matcherSuccess] at actualMatcherSuccess
  cases actualMatcherSuccess
  have generatedBindingsEq :
      Ty.applyList solution generatedPattern.bindings = newBindings := by
    simpa [Ty.applyList] using bindingsEq
  rw [generatedBindingsEq]
  simpa using initialState

end TypePM.Source.MatcherTyping
