import TypePM.Source.M4OriginMatcherProducer

/-!
# Origin-demand producer for ordinary M4 recursive closures

Unlike a matcher-root fix, an ordinary `fixE` is observed through a finite
`plainCall` tree.  The call node fixes operational fuel independently from
the argument and result observation trees.  Its body producer is quantified
over every runtime argument satisfying the requested argument observation;
it does not contain a completed evaluation equation or a concrete program.

The recursive runtime self is inserted at environment position one.  The
positive call layer stores the total body certificate as well as the dynamic
body producer, so structural typing is not hidden in an external assumption.
-/

namespace TypePM.Runtime

/-- Evaluating an ordinary `fixE` produces a recursive closure satisfying one
finite structural call observation.  The fuel used to construct the closure
is independent of the fuel used by the later call. -/
theorem evalPlainFix_originResultSafe_plainCall_of_body
    (environmentTyped : TotalEnvironmentTyping environment environmentTypes)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: environmentTypes) body codomain)
    (bodySafe : ∀ argument,
      OriginValueSafe argumentDemand argument domain →
        OriginResultSafe resultDemand codomain
          (evalFuel bodyFuel
            (argument :: Value.recursiveClosure environment body :: environment)
            body)) :
    OriginResultSafe
      (.plainCall (bodyFuel + 1) argumentDemand resultDemand)
      (.fn domain codomain)
      (evalFuel constructionFuel environment (.fixE body)) := by
  cases constructionFuel with
  | zero => exact .inl rfl
  | succ constructionFuel =>
      exact .inr ⟨Value.recursiveClosure environment body, rfl,
        OriginValueSafe.recursiveClosure environmentTyped bodyTyped bodySafe⟩

/-- A zero-fuel call observation is vacuous but still excludes `stuck` from
construction of the recursive closure. -/
theorem evalPlainFix_originResultSafe_zeroCall_of_body
    (_environmentTyped : TotalEnvironmentTyping environment environmentTypes)
    (_bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: environmentTypes) body codomain) :
    OriginResultSafe (.plainCall 0 argumentDemand resultDemand)
      (.fn domain codomain)
      (evalFuel constructionFuel environment (.fixE body)) := by
  cases constructionFuel with
  | zero => exact .inl rfl
  | succ constructionFuel =>
      exact .inr ⟨Value.recursiveClosure environment body, rfl, by
        simp only [OriginValueSafe]
        exact .zero⟩

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

private theorem plainFixElaboration_target_apply_eq
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE body) start generated next) :
    generated.target.apply solution =
      (.fn ((Fix.domain body start).apply solution)
        ((Fix.codomain body start).apply solution)) := by
  cases staticFuel with
  | zero => contradiction
  | succ staticFuel =>
      simp only [M4.ElaboratesFuel] at elaboration
      cases elaboration
      rfl

/-- Dynamic body obligation consumed by the ordinary-fix producer.  Both
child demands are arbitrary finite `OriginDemand` trees, so recursive calls
may request further finite call observations. -/
def PlainFixBodyOriginSafe
    (environment : ValueEnvironment) (body : Expr)
    (domain codomain : Ty) (bodyFuel : Nat)
    (argumentDemand resultDemand : OriginDemand) : Prop :=
  ∀ argument,
    OriginValueSafe argumentDemand argument domain →
      OriginResultSafe resultDemand codomain
        (evalFuel bodyFuel
          (argument :: Value.recursiveClosure environment body :: environment)
          body)

/-- A solved ordinary M4 `fixE`, a total body certificate, and a finite body
producer yield the exact `plainCall` observation at the solved result type.
The theorem is independent of fixture names, evaluator success equations,
and any fixed fuel value. -/
theorem fixElaboration_eval_originResultSafe_plainCall_of_m4Fuel
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE body) start generated next)
    (_semantic : generated.SemanticSolution solution)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      ((Fix.domain body start).apply solution ::
        .fn ((Fix.domain body start).apply solution)
          ((Fix.codomain body start).apply solution) :: runtimeContext)
      body ((Fix.codomain body start).apply solution))
    (environmentTyped : TotalEnvironmentTyping environment runtimeContext)
    (bodySafe : PlainFixBodyOriginSafe environment body
      ((Fix.domain body start).apply solution)
      ((Fix.codomain body start).apply solution)
      bodyFuel argumentDemand resultDemand) :
    OriginResultSafe
      (.plainCall (bodyFuel + 1) argumentDemand resultDemand)
      (generated.target.apply solution)
      (evalFuel constructionFuel environment (.fixE body)) := by
  have target_eq := plainFixElaboration_target_apply_eq
    (solution := solution) elaboration
  rw [target_eq]
  exact evalPlainFix_originResultSafe_plainCall_of_body environmentTyped
    bodyTyped bodySafe

/-- Zero-call specialization of the solved ordinary-fix producer. -/
theorem fixElaboration_eval_originResultSafe_zeroCall_of_m4Fuel
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE body) start generated next)
    (_semantic : generated.SemanticSolution solution)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      ((Fix.domain body start).apply solution ::
        .fn ((Fix.domain body start).apply solution)
          ((Fix.codomain body start).apply solution) :: runtimeContext)
      body ((Fix.codomain body start).apply solution))
    (environmentTyped : TotalEnvironmentTyping environment runtimeContext) :
    OriginResultSafe (.plainCall 0 argumentDemand resultDemand)
      (generated.target.apply solution)
      (evalFuel constructionFuel environment (.fixE body)) := by
  have target_eq := plainFixElaboration_target_apply_eq
    (solution := solution) elaboration
  rw [target_eq]
  exact evalPlainFix_originResultSafe_zeroCall_of_body environmentTyped bodyTyped

end TypePM.Source.MatcherTyping
