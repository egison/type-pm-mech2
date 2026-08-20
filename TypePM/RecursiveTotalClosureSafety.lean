import TypePM.Source.M4RecursiveMatcherTotalBridge

/-!
# Proof-only typing for recursive closures with total-core bodies

`ValueTyping.recursiveClosure` intentionally stores an old `RuntimeTyping`
body.  This parallel layer leaves that stable judgment unchanged and adds the
recursive closure needed when the body is typed only by `TotalCoreTyping`, for
example because it contains a matcher literal or a recursive match.

The layer is proof-only: evaluator values and source syntax are unchanged.
Its list form is also the environment judgment, so later matcher-definition
environments can contain these recursive closures without erasing their body
certificate.
-/

namespace TypePM.Runtime

mutual

  /-- A non-recursive expression certificate usable inside matcher clauses.
  `solvedM4` records only a solved static M4 derivation; in particular it does
  not imply `TotalEnvironmentSafe` or any no-stuck property.  Those dynamic
  premises remain separate from value typing below. -/
  inductive TotalRecursiveExpressionTyping : EmbeddedExpressionTyping where
    | core
        (typing : TotalCoreTyping expression target context) :
        TotalRecursiveExpressionTyping context expression target
    | solvedM4
        (elaboration : Source.MatcherTyping.CheckedExpressionElaboratesUsing
          (Source.M4.ElaboratesFuel Source.Paper1FrozenSignature.signature fuel)
          sourceContext expression expected supply generated next)
        (semantic : generated.RuntimeSolution solution)
        (contextCompatible : MonomorphicContextCompatible
          sourceContext context solution) :
        TotalRecursiveExpressionTyping context expression
          (expected.apply solution)
    | tuple
        (items : TotalRecursiveExpressionTypings context expressions targets) :
        TotalRecursiveExpressionTyping context (.tuple expressions)
          (.prod targets)

  /-- Pointwise form used for tuples.  Keeping it in the same mutual block
  avoids placing the expression relation in an external inductive parameter. -/
  inductive TotalRecursiveExpressionTypings :
      List Ty → List Source.Expr → List Ty → Prop where
    | nil : TotalRecursiveExpressionTypings context [] []
    | cons
        (head : TotalRecursiveExpressionTyping context expression target)
        (tail : TotalRecursiveExpressionTypings context expressions targets) :
        TotalRecursiveExpressionTypings context (expression :: expressions)
          (target :: targets)

end

/-- Positive structural certificate for recursive closure bodies.  Ordinary
expressions embed directly.  A matcher literal stores total clause typing
whose arm bodies use the completed non-recursive certificate above.  No
evaluation-safety premise is stored here. -/
inductive TotalRecursiveClosureBodyTyping : EmbeddedExpressionTyping where
  | expression
      (typing : TotalRecursiveExpressionTyping context expression target) :
      TotalRecursiveClosureBodyTyping context expression target
  | matcher
      (clauses : TotalRuntimeMatcherClausesTyping
        TotalRecursiveExpressionTyping
        context matcherTarget sourceClauses) :
      TotalRecursiveClosureBodyTyping context (.matcher sourceClauses)
        (.matcher .any matcherTarget)
  /-- A solved M4 matcher derivation retains its precise static capability.
  This constructor is a typing certificate only: it does not assert that arm
  evaluation or recursive dispatch is safe. -/
  | solvedMatcher
      (elaboration : Source.MatcherTyping.MatcherLiteralElaboratesUsing
        (Source.M4.ElaboratesFuel Source.Paper1FrozenSignature.signature fuel)
        Source.MatcherTyping.PPatElaborates Source.MatcherTyping.DPatElaborates
        Source.Paper1FrozenSignature.signature sourceContext sourceClauses
        supply generated next)
      (semantic : generated.SemanticSolution solution)
      (contextCompatible : MonomorphicContextCompatible
        sourceContext context solution)
      (clauses : TotalRuntimeMatcherClausesTyping
        TotalRecursiveExpressionTyping context
        ((Ty.var ⟨supply.ty⟩).apply solution) sourceClauses) :
      TotalRecursiveClosureBodyTyping context (.matcher sourceClauses)
        (generated.target.apply solution)

mutual

  /-- Runtime value typing extended only at the closure boundary.  Ordinary
  values embed unchanged; new recursive and matcher closures may capture a
  parallel total environment. -/
  inductive TotalValueTyping : Value → Ty → Prop where
    | ordinary (typing : ValueTyping value target) :
        TotalValueTyping value target
    | recursiveClosure
        (environment : TotalValueTypings values context)
        (body : TotalRecursiveClosureBodyTyping
          (domain :: .fn domain codomain :: context) bodyExpression codomain) :
        TotalValueTyping (Value.recursiveClosure values bodyExpression)
          (.fn domain codomain)
    | matcherClosure
        (environment : TotalValueTypings values definitionTypes)
        (clauses : TotalRuntimeMatcherClausesTyping
          TotalRecursiveExpressionTyping
          definitionTypes matcherTarget original)
        (cursor : ∃ tried, original = tried ++ remaining) :
        TotalValueTyping (.matcherV values original remaining)
          (.matcher .any matcherTarget)
    /-- A solved M4 literal can also type an already constructed matcher
    cursor at its precise static capability.  The explicit output equation
    keeps the value-type index constructor-shaped; this certificate still
    contains no dispatch-safety claim. -/
    | solvedMatcherClosure
        (environment : TotalValueTypings values definitionTypes)
        (elaboration : Source.MatcherTyping.MatcherLiteralElaboratesUsing
          (Source.M4.ElaboratesFuel Source.Paper1FrozenSignature.signature fuel)
          Source.MatcherTyping.PPatElaborates Source.MatcherTyping.DPatElaborates
          Source.Paper1FrozenSignature.signature sourceContext original
          supply generated next)
        (semantic : generated.SemanticSolution solution)
        (contextCompatible : MonomorphicContextCompatible
          sourceContext definitionTypes solution)
        (output_eq : generated.target.apply solution =
          .matcher capability matcherTarget)
        (cursor : ∃ tried, original = tried ++ remaining) :
        TotalValueTyping (.matcherV values original remaining)
          (.matcher capability matcherTarget)

  /-- Pointwise total typing for value sequences and environments. -/
  inductive TotalValueTypings : List Value → List Ty → Prop where
    | nil : TotalValueTypings [] []
    | cons
        (head : TotalValueTyping value target)
        (tail : TotalValueTypings values targets) :
        TotalValueTypings (value :: values) (target :: targets)

end

/-- Environments use the same newest-first pointwise convention as value
sequences. -/
abbrev TotalEnvironmentTyping := TotalValueTypings

namespace TotalValueTypings

/-- Ordinary pointwise value typing embeds into the total layer. -/
theorem ofValueTypings
    (typing : ValueTypings values targets) :
    TotalValueTypings values targets := by
  cases typing with
  | nil => exact .nil
  | cons head tail => exact .cons (.ordinary head) (ofValueTypings tail)

/-- Ordinary environment typing embeds into the total layer. -/
theorem ofEnvironmentTyping
    (typing : EnvironmentTyping environment context) :
    TotalEnvironmentTyping environment context := by
  cases typing with
  | nil => exact .nil
  | cons head tail => exact .cons (.ordinary head) (ofEnvironmentTyping tail)

/-- Concatenate two typed value sequences without changing their order. -/
theorem append
    (left : TotalValueTypings leftValues leftTargets)
    (right : TotalValueTypings rightValues rightTargets) :
    TotalValueTypings (leftValues ++ rightValues)
      (leftTargets ++ rightTargets) := by
  induction leftValues generalizing leftTargets with
  | nil =>
      cases left
      simpa using right
  | cons value values induction =>
      cases left with
      | cons head tail => exact .cons head (induction tail)

/-- A type lookup in a total environment returns a value with the same total
type. -/
theorem lookup
    {index : Nat}
    (typing : TotalValueTypings values targets)
    (found : targets[index]? = some target) :
    ∃ value, values[index]? = some value ∧ TotalValueTyping value target := by
  induction index generalizing values targets with
  | zero =>
      cases typing with
      | nil => simp at found
      | cons head tail =>
          simp at found
          subst target
          exact ⟨_, rfl, head⟩
  | succ index induction =>
      cases typing with
      | nil => simp at found
      | cons head tail =>
          simp only [List.getElem?_cons_succ] at found ⊢
          exact induction tail found

end TotalValueTypings

namespace MonomorphicContextCompatible

/-- A later substitution transports a monomorphic source/runtime context
agreement pointwise. -/
theorem postcompose
    (compatible : MonomorphicContextCompatible sourceContext runtimeContext
      earlier)
    (later : Subst) :
    MonomorphicContextCompatible sourceContext
      (runtimeContext.map (Ty.apply later))
      (Subst.compose later earlier) := by
  induction compatible with
  | nil => exact .nil
  | cons tail induction =>
      simpa only [List.map_cons, Ty.apply_compose] using
        MonomorphicContextCompatible.cons induction

end MonomorphicContextCompatible

namespace TotalValueTyping

/-- Canonical form for a function in the parallel layer.  Both closure kinds
expose a `TotalCoreTyping` body and a total captured environment. -/
theorem function_canonical
    (typing : TotalValueTyping value (.fn domain codomain)) :
      (∃ environment context bodyExpression,
        value = Value.plainClosure environment bodyExpression ∧
        TotalEnvironmentTyping environment context ∧
        TotalRecursiveClosureBodyTyping (domain :: context) bodyExpression
          codomain) ∨
      (∃ environment context bodyExpression,
        value = Value.recursiveClosure environment bodyExpression ∧
        TotalEnvironmentTyping environment context ∧
        TotalRecursiveClosureBodyTyping
          (domain :: .fn domain codomain :: context) bodyExpression codomain) := by
  cases typing with
  | ordinary source =>
      rcases source.function_canonical with
        ⟨environment, context, body, rfl, environmentTyped, bodyTyped⟩ |
        ⟨environment, context, body, rfl, environmentTyped, bodyTyped⟩
      · exact .inl ⟨environment, context, body, rfl,
          TotalValueTypings.ofEnvironmentTyping environmentTyped,
          .expression (.core (.core bodyTyped))⟩
      · exact .inr ⟨environment, context, body, rfl,
          TotalValueTypings.ofEnvironmentTyping environmentTyped,
          .expression (.core (.core bodyTyped))⟩
  | recursiveClosure environment body =>
      exact .inr ⟨_, _, _, rfl, environment, body⟩

end TotalValueTyping

/-- Typed evaluation in the parallel layer: timeout or a successfully
produced total value. -/
def TotalTypedResult (target : Ty) (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧ TotalValueTyping value target

namespace TotalTypedResult

/-- Existing preservation results embed without loss. -/
theorem ofTypedResult (typed : TypedResult target result) :
    TotalTypedResult target result := by
  rcases typed with timeout | ⟨value, success, valueTyped⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, .ordinary valueTyped⟩

/-- Total typed evaluation cannot report `stuck`. -/
theorem notStuck (typed : TotalTypedResult target result) : result.NotStuck := by
  rcases typed with timeout | ⟨value, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TotalTypedResult

/-- Common-fuel safety of one expression when its runtime environment uses the
parallel total-value judgment.  Keeping this property separate from
`TotalValueTyping.recursiveClosure` avoids a negative recursive occurrence in
the inductive definition. -/
def TotalEnvironmentSafe (expression : Source.Expr) (target : Ty)
    (context : List Ty) : Prop :=
  ∀ fuel environment,
    TotalEnvironmentTyping environment context →
      TotalTypedResult target (evalFuel fuel environment expression)

namespace RuntimeCaptureExpressionsTyping

/-- Convert the generic tuple certificate produced by the M4 bridge to the
mutually defined pointwise form used by `TotalRecursiveExpressionTyping`. -/
theorem toTotalRecursive
    (typing : RuntimeCaptureExpressionsTyping
      TotalRecursiveExpressionTyping context expressions targets) :
    TotalRecursiveExpressionTypings context expressions targets := by
  cases typing with
  | nil => exact .nil
  | cons head tail => exact .cons head tail.toTotalRecursive

end RuntimeCaptureExpressionsTyping

/-- Static solved-M4 bridge for recursive matcher-clause expressions.  The
result is a typing certificate only; it contains no environment-safety or
no-stuck conclusion. -/
def totalRecursiveExpressionBridge :
    Source.MatcherTyping.SolvedM4CheckedExpressionBridge
      TotalRecursiveExpressionTyping where
  checked := by
    intro fuel context expression expected supply generated next solution
      runtimeContext elaboration semantic contextCompatible
    exact .solvedM4 elaboration semantic contextCompatible
  tuple := by
    intro context expressions targets items
    exact .tuple items.toTotalRecursive

namespace RuntimeNextMatchersTyping

/-- Old next-matcher typing embeds into the callback-parametric total clause
family. -/
theorem toTotalCore
    (typing : RuntimeNextMatchersTyping context expression holes) :
    TotalRuntimeNextMatchersTyping
      TotalRecursiveExpressionTyping
      context expression holes :=
  ⟨.core (.core typing.runtimeTyping)⟩

end RuntimeNextMatchersTyping

namespace RuntimeMatcherArmTyping

theorem toTotalCore
    (typing : RuntimeMatcherArmTyping definitionTypes captureTypes
      matcherTarget holes arm) :
    TotalRuntimeMatcherArmTyping
      TotalRecursiveExpressionTyping
      definitionTypes captureTypes matcherTarget holes arm := by
  cases typing with
  | mk header body => exact .mk header (.core (.core body))

end RuntimeMatcherArmTyping

namespace RuntimeMatcherArmsTyping

theorem toTotalCore
    (typing : RuntimeMatcherArmsTyping definitionTypes captureTypes
      matcherTarget holes arms) :
    TotalRuntimeMatcherArmsTyping
      TotalRecursiveExpressionTyping
      definitionTypes captureTypes matcherTarget holes arms := by
  cases typing with
  | nil => exact .nil
  | cons head tail => exact .cons head.toTotalCore tail.toTotalCore

end RuntimeMatcherArmsTyping

namespace RuntimeMatcherClauseTyping

theorem toTotalCore
    (typing : RuntimeMatcherClauseTyping definitionTypes matcherTarget clause) :
    TotalRuntimeMatcherClauseTyping
      TotalRecursiveExpressionTyping
      definitionTypes matcherTarget clause := by
  cases typing with
  | mk header nextMatchers arms =>
      exact .mk header nextMatchers.toTotalCore arms.toTotalCore

end RuntimeMatcherClauseTyping

namespace RuntimeMatcherClausesTyping

/-- Pointwise lifting of an old clause certificate. -/
theorem toTotalCore
    (typing : RuntimeMatcherClausesTyping definitionTypes matcherTarget clauses) :
    TotalRuntimeMatcherClausesTyping
      TotalRecursiveExpressionTyping
      definitionTypes matcherTarget clauses := by
  cases typing with
  | nil => exact .nil
  | cons head tail => exact .cons head.toTotalCore tail.toTotalCore

end RuntimeMatcherClausesTyping

/-- Variables are safe in total environments by the parallel lookup lemma. -/
theorem totalEnvironmentSafe_var
    (found : context[index]? = some target) :
    TotalEnvironmentSafe (.var index) target context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      obtain ⟨value, valueFound, valueTyped⟩ := environmentTyped.lookup found
      exact .inr ⟨value, by simp [evalFuel, valueFound], valueTyped⟩

/-- Integer literals are safe independently of the total environment. -/
theorem totalEnvironmentSafe_lit (literal : Int) :
    TotalEnvironmentSafe (.lit literal) .int context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel => exact .inr ⟨.int literal, rfl, .ordinary (.int literal)⟩

/-- A matcher literal captures the total environment and returns the parallel
matcher-closure certificate. -/
theorem totalEnvironmentSafe_matcher
    (clausesTyped : RuntimeMatcherClausesTyping context matcherTarget clauses) :
    TotalEnvironmentSafe (.matcher clauses) (.matcher .any matcherTarget)
      context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨Value.matcherClosure environment clauses, rfl,
        .matcherClosure environmentTyped clausesTyped.toTotalCore
          ⟨[], by simp⟩⟩

/-- Total clauses can likewise be captured without reverting their recursive
arm bodies to `RuntimeTyping`.  This theorem is still only the literal
construction step; dispatch safety remains a separate theorem/premise. -/
theorem totalEnvironmentSafe_totalMatcher
    (clausesTyped : TotalRuntimeMatcherClausesTyping
      TotalRecursiveExpressionTyping
      context matcherTarget clauses) :
    TotalEnvironmentSafe (.matcher clauses) (.matcher .any matcherTarget)
      context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨Value.matcherClosure environment clauses, rfl,
        .matcherClosure environmentTyped clausesTyped ⟨[], by simp⟩⟩

/-- Evaluating a solved M4 matcher literal only constructs its closure.  The
precise source capability is retained by `solvedMatcherClosure`; this theorem
does not execute clause dispatch and therefore makes no claim about the
safety of next-matcher expressions or arm bodies. -/
theorem totalEnvironmentSafe_solvedMatcher
    (elaboration : Source.MatcherTyping.MatcherLiteralElaboratesUsing
      (Source.M4.ElaboratesFuel Source.Paper1FrozenSignature.signature fuel)
      Source.MatcherTyping.PPatElaborates Source.MatcherTyping.DPatElaborates
      Source.Paper1FrozenSignature.signature sourceContext clauses supply
      generated next)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext context solution) :
    TotalEnvironmentSafe (.matcher clauses)
      (.matcher
        ((Cap.var ⟨supply.cap⟩).apply solution.cap)
        ((Ty.var ⟨supply.ty⟩).apply solution))
      context := by
  intro runtimeFuel environment environmentTyped
  cases runtimeFuel with
  | zero => exact .inl rfl
  | succ runtimeFuel =>
      have output_eq : generated.target.apply solution =
          .matcher
            ((Cap.var ⟨supply.cap⟩).apply solution.cap)
            ((Ty.var ⟨supply.ty⟩).apply solution) := by
        cases elaboration
        rfl
      exact .inr ⟨Value.matcherClosure environment clauses, rfl,
        .solvedMatcherClosure environmentTyped elaboration semantic
          contextCompatible output_eq ⟨[], by simp⟩⟩

/-- Evaluating `fixE` constructs the recursive closure whose body is certified
by `TotalCoreTyping`. -/
theorem totalEnvironmentSafe_fixE
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: context) body codomain) :
    TotalEnvironmentSafe (.fixE body) (.fn domain codomain) context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨Value.recursiveClosure environment body, rfl,
        .recursiveClosure environmentTyped bodyTyped⟩

/-- Direct application of a parallel recursive closure preserves its result
type at the same decreasing fuel used by `evalFuel`. -/
theorem applyFuel_recursiveClosure_totalTyped
    (environmentTyped : TotalEnvironmentTyping environment context)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: context) body codomain)
    (bodySafe : TotalEnvironmentSafe body codomain
      (domain :: .fn domain codomain :: context))
    (argumentTyped : TotalValueTyping argument domain)
    (fuel : Nat) :
    TotalTypedResult codomain
      (applyFuel fuel (Value.recursiveClosure environment body) argument) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ bodyFuel =>
      let closure := Value.recursiveClosure environment body
      have closureTyped : TotalValueTyping closure (.fn domain codomain) :=
        .recursiveClosure environmentTyped bodyTyped
      exact bodySafe bodyFuel (argument :: closure :: environment)
        (.cons argumentTyped (.cons closureTyped environmentTyped))

/-- No-stuck corollary for direct recursive-closure application. -/
theorem applyFuel_recursiveClosure_neverStuck
    (environmentTyped : TotalEnvironmentTyping environment context)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: context) body codomain)
    (bodySafe : TotalEnvironmentSafe body codomain
      (domain :: .fn domain codomain :: context))
    (argumentTyped : TotalValueTyping argument domain)
    (fuel : Nat) :
    (applyFuel fuel (Value.recursiveClosure environment body) argument).NotStuck :=
  (applyFuel_recursiveClosure_totalTyped environmentTyped bodyTyped bodySafe
    argumentTyped fuel).notStuck

/-- Common-fuel preservation for the direct source form
`(fix body) argument`.  The body and argument use the same total-environment
safety interface, and application decreases exactly as the evaluator does. -/
theorem evalFixApplication_totalTyped
    (environmentTyped : TotalEnvironmentTyping environment context)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: context) body codomain)
    (bodySafe : TotalEnvironmentSafe body codomain
      (domain :: .fn domain codomain :: context))
    (argumentSafe : TotalEnvironmentSafe argument domain context)
    (fuel : Nat) :
    TotalTypedResult codomain
      (evalFuel fuel environment (.app (.fixE body) argument)) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ applicationFuel =>
      cases applicationFuel with
      | zero => exact .inl (by simp [evalFuel, FuelResult.bind])
      | succ bodyFuel =>
          have argumentResult := argumentSafe (bodyFuel + 1) environment
            environmentTyped
          rcases argumentResult with argumentTimeout |
            ⟨argumentValue, argumentSuccess, argumentTyped⟩
          · exact .inl (by
              rw [evalFuel.eq_def]
              simp only
              rw [show evalFuel (bodyFuel + 1) environment (.fixE body) =
                .ok (Value.recursiveClosure environment body) by rfl]
              rw [argumentTimeout]
              rfl)
          · have applicationResult := applyFuel_recursiveClosure_totalTyped
              environmentTyped bodyTyped bodySafe argumentTyped (bodyFuel + 1)
            rcases applicationResult with applicationTimeout |
              ⟨value, applicationSuccess, valueTyped⟩
            · exact .inl (by
                rw [evalFuel.eq_def]
                simp only
                rw [show evalFuel (bodyFuel + 1) environment (.fixE body) =
                  .ok (Value.recursiveClosure environment body) by rfl]
                rw [argumentSuccess]
                exact applicationTimeout)
            · exact .inr ⟨value, by
                rw [evalFuel.eq_def]
                simp only
                rw [show evalFuel (bodyFuel + 1) environment (.fixE body) =
                  .ok (Value.recursiveClosure environment body) by rfl]
                rw [argumentSuccess]
                exact applicationSuccess, valueTyped⟩

/-- No-stuck corollary for direct source-level `fixE` application. -/
theorem evalFixApplication_neverStuck
    (environmentTyped : TotalEnvironmentTyping environment context)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: context) body codomain)
    (bodySafe : TotalEnvironmentSafe body codomain
      (domain :: .fn domain codomain :: context))
    (argumentSafe : TotalEnvironmentSafe argument domain context)
    (fuel : Nat) :
    (evalFuel fuel environment (.app (.fixE body) argument)).NotStuck :=
  (evalFixApplication_totalTyped environmentTyped bodyTyped bodySafe
    argumentSafe fuel).notStuck

end TypePM.Runtime
