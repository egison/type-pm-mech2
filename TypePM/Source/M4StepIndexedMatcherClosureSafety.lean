import TypePM.StepIndexedClosureSafety

/-!
# Step-indexed safety of solved M4 matcher closures

This module connects solved M4 matcher-literal and matcher-root `fixE`
derivations to the generated-user-matcher branch of the step-indexed logical
relation.  It constructs only fresh matcher closures, before any clause cursor
has advanced.  Dispatch and matching-search safety remain separate.
-/

namespace TypePM.Runtime

/-- A fresh user matcher closure with a totally typed body is fuel-safe at
every index at which its captured environment is fuel-safe.  At a positive
index both the recursive lower matcher certificate and every capture are
checked at the immediately preceding index. -/
theorem fuelValueSafe_matcherClosure_of_body
    (body : TotalRecursiveClosureBodyTyping environmentTypes
      (.matcher clauses) (.matcher capability target)) :
    ∀ fuel,
      FuelEnvironmentSafe fuel environment environmentTypes →
        FuelValueSafe fuel (Value.matcherClosure environment clauses)
          (.matcher capability target)
  | 0, _ => fuelValueSafe_zero _ _
  | fuel + 1, environmentSafe =>
      .matcher
        (fuelValueSafe_matcherClosure_of_body body fuel
          environmentSafe.previous)
        (.generated (environmentTypes := environmentTypes) rfl
          environmentSafe.previous.1 environmentSafe.previous.2 body)

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- A solved M4 matcher literal supplies the exact total recursive body
certificate consumed by generated matcher safety. -/
theorem MatcherLiteralElaboratesUsing.totalRecursiveClosureBodyTyping_of_m4Fuel
    (elaboration : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel signature staticFuel) PPatElaborates DPatElaborates
      signature sourceContext clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution) :
    TotalRecursiveClosureBodyTyping runtimeContext (.matcher clauses)
      (generated.target.apply solution) := by
  have clausesTyped :=
    elaboration.toTotalMatcherClausesTyping_of_m4Fuel compatible
      (totalRecursiveExpressionBridge signature) semantic contextCompatible
  exact .solvedMatcher elaboration semantic contextCompatible clausesTyped

/-- Evaluating a solved M4 matcher literal constructs a fresh user matcher
value that is step-indexed safe whenever its aligned runtime environment is.
No evaluator equation or clause-dispatch premise is used. -/
theorem MatcherLiteralElaboratesUsing.matcherClosure_fuelValueSafe_of_m4Fuel
    (elaboration : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel signature staticFuel) PPatElaborates DPatElaborates
      signature sourceContext clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (environmentSafe : FuelEnvironmentSafe runtimeFuel environment runtimeContext) :
    FuelValueSafe runtimeFuel (Value.matcherClosure environment clauses)
      (generated.target.apply solution) := by
  have output_eq : generated.target.apply solution =
      .matcher ((Cap.var ⟨supply.cap⟩).apply solution.cap)
        ((Ty.var ⟨supply.ty⟩).apply solution) := by
    cases elaboration
    rfl
  have body := elaboration.totalRecursiveClosureBodyTyping_of_m4Fuel
    compatible semantic contextCompatible
  rw [output_eq] at body ⊢
  exact fuelValueSafe_matcherClosure_of_body body runtimeFuel environmentSafe

private theorem fromFix_body_semantic
    (semantic : (Generated.fromFix domain codomain body).SemanticSolution
      solution) :
    body.SemanticSolution solution ∧
      Equation.Holds solution (.ty body.target codomain) := by
  constructor
  · constructor
    · intro equation membership
      exact semantic.1 equation (by simp [Generated.fromFix, membership])
    · intro obligation membership
      exact semantic.2 obligation (by simpa [Generated.fromFix] using membership)
  · exact semantic.1 _ (by simp [Generated.fromFix])

private theorem fixElaboration_parts
    (elaboration : FixElaboratesUsing
      (M4.ElaboratesFuel signature staticFuel) sourceContext
      (.fixE body) start generated next) :
    ∃ generatedBody,
      M4.ElaboratesFuel signature staticFuel
        (Fix.bodyContext (Fix.domain body start)
          (Fix.codomain body start) sourceContext)
        body (Fix.bodySupply body start) generatedBody next ∧
      generated = Generated.fromFix (Fix.domain body start)
        (Fix.codomain body start) generatedBody := by
  cases elaboration with
  | fixE direct bodyElaboration => exact ⟨_, bodyElaboration, rfl⟩

/-- Generic extraction of the body certificate of a solved matcher-root
`fixE`.  Unlike the earlier Paper-1 specialization, this theorem is
parameterized by any runtime-compatible frozen signature. -/
theorem matcherFixElaboration_totalRecursiveClosureBodyTyping_of_m4Fuel
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE (.matcher clauses)) start generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution) :
    TotalRecursiveClosureBodyTyping
      ((Fix.domain (.matcher clauses) start).apply solution ::
        (.fn
          ((Fix.domain (.matcher clauses) start).apply solution)
          ((Fix.codomain (.matcher clauses) start).apply solution)) ::
        runtimeContext)
      (.matcher clauses)
      ((Fix.codomain (.matcher clauses) start).apply solution) := by
  cases staticFuel with
  | zero => contradiction
  | succ staticFuel =>
      simp only [M4.ElaboratesFuel] at elaboration
      obtain ⟨generatedBody, bodyElaboration, generated_eq⟩ :=
        fixElaboration_parts elaboration
      cases staticFuel with
      | zero => simp [M4.ElaboratesFuel] at bodyElaboration
      | succ bodyFuel =>
          simp only [M4.ElaboratesFuel] at bodyElaboration
          rw [generated_eq] at semantic
          obtain ⟨bodySemantic, bodyEquation⟩ :=
            fromFix_body_semantic semantic
          have bodyContextCompatible : MonomorphicContextCompatible
              (Fix.bodyContext (Fix.domain (.matcher clauses) start)
                (Fix.codomain (.matcher clauses) start) sourceContext)
              ((Fix.domain (.matcher clauses) start).apply solution ::
                ((Ty.fn (Fix.domain (.matcher clauses) start)
                  (Fix.codomain (.matcher clauses) start)).apply solution) ::
                runtimeContext)
              solution := by
            simp only [Fix.bodyContext]
            exact .cons (.cons contextCompatible)
          have body :=
            bodyElaboration.totalRecursiveClosureBodyTyping_of_m4Fuel
              compatible bodySemantic bodyContextCompatible
          simp only [Equation.Holds] at bodyEquation
          simpa [Ty.apply, bodyEquation] using body

/-- The fresh matcher value constructed by a matcher-root recursive closure
is fuel-safe from the aligned argument, recursive-self, and outer-environment
certificates.  The theorem deliberately leaves construction of the recursive
self certificate to the enclosing fuel induction. -/
theorem matcherFixElaboration_matcherClosure_fuelValueSafe_of_m4Fuel
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE (.matcher clauses)) start generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (argumentSafe : FuelValueSafe runtimeFuel argument
      ((Fix.domain (.matcher clauses) start).apply solution))
    (selfSafe : FuelValueSafe runtimeFuel
      (Value.recursiveClosure environment (.matcher clauses))
      (.fn
        ((Fix.domain (.matcher clauses) start).apply solution)
        ((Fix.codomain (.matcher clauses) start).apply solution)))
    (environmentSafe : FuelEnvironmentSafe runtimeFuel environment runtimeContext) :
    FuelValueSafe runtimeFuel
      (Value.matcherClosure
        (argument :: Value.recursiveClosure environment (.matcher clauses) ::
          environment)
        clauses)
      ((Fix.codomain (.matcher clauses) start).apply solution) := by
  have body :=
    matcherFixElaboration_totalRecursiveClosureBodyTyping_of_m4Fuel
      elaboration compatible semantic contextCompatible
  have capturesSafe : FuelEnvironmentSafe runtimeFuel
      (argument :: Value.recursiveClosure environment (.matcher clauses) ::
        environment)
      ((Fix.domain (.matcher clauses) start).apply solution ::
        (.fn
          ((Fix.domain (.matcher clauses) start).apply solution)
          ((Fix.codomain (.matcher clauses) start).apply solution)) ::
        runtimeContext) :=
    FuelEnvironmentSafe.cons argumentSafe
      (FuelEnvironmentSafe.cons selfSafe environmentSafe)
  simpa [Fix.codomain, Ty.apply] using
    fuelValueSafe_matcherClosure_of_body body runtimeFuel capturesSafe

end TypePM.Source.MatcherTyping
