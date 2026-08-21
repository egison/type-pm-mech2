import TypePM.FuelUserMatcherGeneralSafety
import TypePM.Source.M4StepIndexedMatcherClosureSafety

/-!
# Origin-demand producers for solved M4 matcher values

This module generalizes the mutually recursive step-index proof previously
used by concrete Paper-1 matchers.  A matcher-root recursive closure and the
fresh matcher closure returned by its body are safe for arbitrary clauses,
types, and captured environments supplied by a total body certificate.

The public evaluation producers support finite origin observations assembled
from `none`, arbitrary `fuel` leaves, and `both`.  This is the observation
fragment justified by `FuelValueSafe`; structural function-call observations
for a plain `fixE` belong to the separate plain-recursion producer.
-/

namespace TypePM.Runtime

/-- Environment evidence needed by an origin observation whose leaves are
ordinary fuel indices.  Unsupported structural observations are false rather
than being silently weakened to `none`. -/
def FuelLeafEnvironmentSafe : OriginDemand →
    ValueEnvironment → List Ty → Prop
  | .none, _, _ => True
  | .fuel index, environment, context =>
      FuelEnvironmentSafe index environment context
  | .both left right, environment, context =>
      FuelLeafEnvironmentSafe left environment context ∧
        FuelLeafEnvironmentSafe right environment context
  | .listOf _, _, _ => False
  | .pairOf _ _, _, _ => False
  | .bool, _, _ => False
  | .int, _, _ => False
  | .plainCall _ _ _, _, _ => False

/-- Syntactic fragment of origin demands generated only from `none`, fuel
leaves, and finite conjunction. -/
inductive FuelLeafDemand : OriginDemand → Prop where
  | none : FuelLeafDemand .none
  | fuel (index : Nat) : FuelLeafDemand (.fuel index)
  | both
      (left : FuelLeafDemand leftDemand)
      (right : FuelLeafDemand rightDemand) :
      FuelLeafDemand (.both leftDemand rightDemand)

/-- Any value producer valid at every requested fuel leaf extends
compositionally to `none` and finite `both` trees. -/
theorem originValueSafe_of_fuelLeafProducer
    (producer : ∀ index,
      FuelEnvironmentSafe index environment context →
        FuelValueSafe index value target) :
    ∀ demand,
      FuelLeafEnvironmentSafe demand environment context →
        OriginValueSafe demand value target
  | .none, _ => by simp only [OriginValueSafe]
  | .fuel index, environmentSafe =>
      OriginValueSafe.ofFuel (producer index environmentSafe)
  | .both left right, environmentSafe =>
      OriginValueSafe.both
        (originValueSafe_of_fuelLeafProducer producer left environmentSafe.1)
        (originValueSafe_of_fuelLeafProducer producer right environmentSafe.2)
  | .listOf _, impossible => False.elim impossible
  | .pairOf _ _, impossible => False.elim impossible
  | .bool, impossible => False.elim impossible
  | .int, impossible => False.elim impossible
  | .plainCall _ _ _, impossible => False.elim impossible

/-- A schema-level origin environment with the same fuel-leaf observation at
every position supplies the numeric environment relations required by the
step-indexed matcher producer. -/
theorem fuelLeafEnvironmentSafe_of_originEnvironmentSafe
    (shape : FuelLeafDemand demand)
    (safe : OriginEnvironmentSafe (fun _ => demand) environment context) :
    FuelLeafEnvironmentSafe demand environment context := by
  induction shape with
  | none => trivial
  | fuel index =>
      refine ⟨safe.1, ?_⟩
      intro position target found
      have positionLt : position < context.length :=
        (List.getElem?_eq_some_iff.mp found).1
      have valueLt : position < environment.length := by
        simpa [safe.1] using positionLt
      let value := environment[position]'valueLt
      have valueFound : environment[position]? = some value :=
        List.getElem?_eq_getElem valueLt
      exact ⟨value, valueFound,
        (safe.2 position target value found valueFound).toFuel⟩
  | @both left right leftShape rightShape leftIH rightIH =>
      change OriginEnvironmentSafe
        (OriginEnvironmentDemand.both (fun _ => left) (fun _ => right))
        environment context at safe
      exact ⟨leftIH safe.bothLeft, rightIH safe.bothRight⟩

/-- Evaluation of a matcher literal is safe under any finite tree of fuel
leaves.  Operational fuel and logical observation indices remain unrelated. -/
theorem evalMatcherLiteral_originResultSafe_of_body
    (body : TotalRecursiveClosureBodyTyping environmentTypes
      (.matcher clauses) (.matcher capability target))
    (environmentSafe : FuelLeafEnvironmentSafe outputDemand environment
      environmentTypes) :
    OriginResultSafe outputDemand (.matcher capability target)
      (evalFuel operationalFuel environment (.matcher clauses)) := by
  cases operationalFuel with
  | zero => exact .inl rfl
  | succ operationalFuel =>
      exact .inr ⟨Value.matcherClosure environment clauses, rfl,
        originValueSafe_of_fuelLeafProducer
          (fun index safe =>
            fuelValueSafe_matcherClosure_of_body body index safe)
          outputDemand environmentSafe⟩

/-- The common fuel-leaf specialization only requires the environment at the
requested logical index. -/
theorem evalMatcherLiteral_originResultSafe_fuel_of_body
    (body : TotalRecursiveClosureBodyTyping environmentTypes
      (.matcher clauses) (.matcher capability target))
    (environmentSafe : FuelEnvironmentSafe resultIndex environment
      environmentTypes) :
    OriginResultSafe (.fuel resultIndex) (.matcher capability target)
      (evalFuel operationalFuel environment (.matcher clauses)) := by
  exact evalMatcherLiteral_originResultSafe_of_body body environmentSafe

mutual

  /-- A recursive closure whose body is a matcher literal is fuel-safe at
  every requested index supported by its captured environment. -/
  theorem fuelValueSafe_recursiveMatcherClosure_of_body
      (body : TotalRecursiveClosureBodyTyping
        (domain :: .fn domain (.matcher capability target) :: environmentTypes)
        (.matcher clauses) (.matcher capability target))
      (environmentTyped : TotalEnvironmentTyping environment environmentTypes) :
      ∀ fuel,
        FuelEnvironmentSafe fuel environment environmentTypes →
          FuelValueSafe fuel
            (Value.recursiveClosure environment (.matcher clauses))
            (.fn domain (.matcher capability target))
    | 0, _ => fuelValueSafe_zero _ _
    | fuel + 1, environmentSafe =>
        .function
          (fuelValueSafe_recursiveMatcherClosure_of_body body environmentTyped
            fuel environmentSafe.previous)
          (.existing (.recursiveClosure environmentTyped body)) (by
            intro argument argumentSafe
            cases fuel with
            | zero => exact .inl rfl
            | succ residual =>
                exact .inr ⟨
                  Value.matcherClosure
                    (argument ::
                      Value.recursiveClosure environment (.matcher clauses) ::
                      environment)
                    clauses,
                  rfl,
                  fuelValueSafe_appliedRecursiveMatcherClosure_of_body
                    body environmentTyped argument (residual + 1) argumentSafe
                    environmentSafe.previous⟩)

  /-- The matcher value returned by applying the recursive closure retains
  the generated-constructor proof, including the argument, recursive self,
  and outer environment at the immediately preceding index. -/
  theorem fuelValueSafe_appliedRecursiveMatcherClosure_of_body
      (body : TotalRecursiveClosureBodyTyping
        (domain :: .fn domain (.matcher capability target) :: environmentTypes)
        (.matcher clauses) (.matcher capability target))
      (environmentTyped : TotalEnvironmentTyping environment environmentTypes)
      (argument : Value) :
      ∀ fuel,
        FuelValueSafe fuel argument domain →
        FuelEnvironmentSafe fuel environment environmentTypes →
          FuelValueSafe fuel
            (Value.matcherClosure
              (argument ::
                Value.recursiveClosure environment (.matcher clauses) ::
                environment)
              clauses)
            (.matcher capability target)
    | 0, _, _ => fuelValueSafe_zero _ _
    | fuel + 1, argumentSafe, environmentSafe => by
        have capturesSafe : FuelEnvironmentSafe fuel
            (argument ::
              Value.recursiveClosure environment (.matcher clauses) ::
              environment)
            (domain :: .fn domain (.matcher capability target) ::
              environmentTypes) :=
          FuelEnvironmentSafe.cons argumentSafe.previous
            (FuelEnvironmentSafe.cons
              (fuelValueSafe_recursiveMatcherClosure_of_body body
                environmentTyped fuel environmentSafe.previous)
              environmentSafe.previous)
        exact .matcher
          (fuelValueSafe_appliedRecursiveMatcherClosure_of_body body
            environmentTyped argument fuel argumentSafe.previous
            environmentSafe.previous)
          (.generated rfl capturesSafe.1 capturesSafe.2 body)

end

/-- Evaluating a matcher-root `fixE` constructs the recursively callable
closure and satisfies any finite tree of fuel observations. -/
theorem evalMatcherFix_originResultSafe_of_body
    (body : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain (.matcher capability target) :: environmentTypes)
      (.matcher clauses) (.matcher capability target))
    (environmentTyped : TotalEnvironmentTyping environment environmentTypes)
    (environmentSafe : FuelLeafEnvironmentSafe outputDemand environment
      environmentTypes) :
    OriginResultSafe outputDemand (.fn domain (.matcher capability target))
      (evalFuel operationalFuel environment (.fixE (.matcher clauses))) := by
  cases operationalFuel with
  | zero => exact .inl rfl
  | succ operationalFuel =>
      exact .inr ⟨Value.recursiveClosure environment (.matcher clauses), rfl,
        originValueSafe_of_fuelLeafProducer
          (fun index safe =>
            fuelValueSafe_recursiveMatcherClosure_of_body body environmentTyped
              index safe)
          outputDemand environmentSafe⟩

/-- Fuel-leaf endpoint for matcher-root recursive closure construction. -/
theorem evalMatcherFix_originResultSafe_fuel_of_body
    (body : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain (.matcher capability target) :: environmentTypes)
      (.matcher clauses) (.matcher capability target))
    (environmentTyped : TotalEnvironmentTyping environment environmentTypes)
    (environmentSafe : FuelEnvironmentSafe resultIndex environment
      environmentTypes) :
    OriginResultSafe (.fuel resultIndex)
      (.fn domain (.matcher capability target))
      (evalFuel operationalFuel environment (.fixE (.matcher clauses))) := by
  exact evalMatcherFix_originResultSafe_of_body body environmentTyped
    environmentSafe

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

private theorem matcherFixElaboration_target_apply_eq
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE (.matcher clauses)) start generated next) :
    generated.target.apply solution =
      (.fn
        ((Fix.domain (.matcher clauses) start).apply solution)
        ((Fix.codomain (.matcher clauses) start).apply solution)) := by
  cases staticFuel with
  | zero => contradiction
  | succ staticFuel =>
      simp only [M4.ElaboratesFuel] at elaboration
      cases elaboration
      rfl

/-- A solved M4 matcher literal is an origin-demand producer for every finite
tree of fuel leaves. -/
theorem MatcherLiteralElaboratesUsing.eval_originResultSafe_of_m4Fuel
    (elaboration : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel signature staticFuel) PPatElaborates DPatElaborates
      signature sourceContext clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (environmentSafe : FuelLeafEnvironmentSafe outputDemand environment
      runtimeContext) :
    OriginResultSafe outputDemand (generated.target.apply solution)
      (evalFuel operationalFuel environment (.matcher clauses)) := by
  have output_eq : generated.target.apply solution =
      .matcher ((Cap.var ⟨supply.cap⟩).apply solution.cap)
        ((Ty.var ⟨supply.ty⟩).apply solution) := by
    cases elaboration
    rfl
  have body := elaboration.totalRecursiveClosureBodyTyping_of_m4Fuel
    compatible semantic contextCompatible
  rw [output_eq] at body ⊢
  exact evalMatcherLiteral_originResultSafe_of_body body environmentSafe

/-- Solved matcher-literal specialization for one requested fuel leaf. -/
theorem MatcherLiteralElaboratesUsing.eval_originResultSafe_fuel_of_m4Fuel
    (elaboration : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel signature staticFuel) PPatElaborates DPatElaborates
      signature sourceContext clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (environmentSafe : FuelEnvironmentSafe resultIndex environment
      runtimeContext) :
    OriginResultSafe (.fuel resultIndex) (generated.target.apply solution)
      (evalFuel operationalFuel environment (.matcher clauses)) := by
  exact elaboration.eval_originResultSafe_of_m4Fuel compatible semantic
    contextCompatible environmentSafe

/-- Schema-facing matcher-literal producer.  A uniform origin environment is
converted internally to the fuel-leaf environment relation. -/
theorem MatcherLiteralElaboratesUsing.eval_originResultSafe_of_originEnvironment
    (elaboration : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel signature staticFuel) PPatElaborates DPatElaborates
      signature sourceContext clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (shape : FuelLeafDemand outputDemand)
    (environmentSafe : OriginEnvironmentSafe (fun _ => outputDemand)
      environment runtimeContext) :
    OriginResultSafe outputDemand (generated.target.apply solution)
      (evalFuel operationalFuel environment (.matcher clauses)) := by
  exact elaboration.eval_originResultSafe_of_m4Fuel compatible semantic
    contextCompatible
    (fuelLeafEnvironmentSafe_of_originEnvironmentSafe shape environmentSafe)

/-- A solved matcher-root `fixE` is an origin-demand producer after the
runtime environment supplies both its total structural typing and the
requested fuel-leaf observations. -/
theorem matcherFixElaboration_eval_originResultSafe_of_m4Fuel
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE (.matcher clauses)) start generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (environmentTyped : TotalEnvironmentTyping environment runtimeContext)
    (environmentSafe : FuelLeafEnvironmentSafe outputDemand environment
      runtimeContext) :
    OriginResultSafe outputDemand (generated.target.apply solution)
      (evalFuel operationalFuel environment (.fixE (.matcher clauses))) := by
  have body := matcherFixElaboration_totalRecursiveClosureBodyTyping_of_m4Fuel
    elaboration compatible semantic contextCompatible
  have target_eq := matcherFixElaboration_target_apply_eq
    (solution := solution) elaboration
  rw [target_eq]
  exact evalMatcherFix_originResultSafe_of_body body environmentTyped environmentSafe

/-- Matcher-root `fixE` specialization for one requested fuel leaf. -/
theorem matcherFixElaboration_eval_originResultSafe_fuel_of_m4Fuel
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE (.matcher clauses)) start generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (environmentTyped : TotalEnvironmentTyping environment runtimeContext)
    (environmentSafe : FuelEnvironmentSafe resultIndex environment
      runtimeContext) :
    OriginResultSafe (.fuel resultIndex) (generated.target.apply solution)
      (evalFuel operationalFuel environment (.fixE (.matcher clauses))) := by
  exact matcherFixElaboration_eval_originResultSafe_of_m4Fuel elaboration
    compatible semantic contextCompatible environmentTyped environmentSafe

/-- Schema-facing matcher-root fix producer using the same uniform origin
environment bridge as matcher literals. -/
theorem matcherFixElaboration_eval_originResultSafe_of_originEnvironment
    (elaboration : M4.ElaboratesFuel signature staticFuel sourceContext
      (.fixE (.matcher clauses)) start generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (environmentTyped : TotalEnvironmentTyping environment runtimeContext)
    (shape : FuelLeafDemand outputDemand)
    (environmentSafe : OriginEnvironmentSafe (fun _ => outputDemand)
      environment runtimeContext) :
    OriginResultSafe outputDemand (generated.target.apply solution)
      (evalFuel operationalFuel environment (.fixE (.matcher clauses))) := by
  exact matcherFixElaboration_eval_originResultSafe_of_m4Fuel elaboration
    compatible semantic contextCompatible environmentTyped
    (fuelLeafEnvironmentSafe_of_originEnvironmentSafe shape environmentSafe)

end TypePM.Source.MatcherTyping
