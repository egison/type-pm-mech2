import TypePM.Source.M4RawOriginRecursiveProducer
import TypePM.Source.M4LetRuntimeWorldStepRegression

/-!
# Regression for the source-derived universal-input `letE` plan

The public M4 fixture generalizes one identity function and uses it at both
`Int` and matcher types.  Its body therefore places non-universal call
observations on the generalized binding.  The right-hand side is closed, so
its exact outer-environment demand is pointwise universal.

The arbitrary-fuel safety theorem precedes the independent exact execution
equation.  Consequently the safety proof cannot depend on a completed
evaluator result, and the regression does not pass merely because all runs
time out.
-/

namespace TypePM.Source.M4RawOriginLetUniversalRegression

open TypePM.Runtime
open TypePM.Source.M4LetRuntimeWorldStepRegression

/-- The existing public-M4 fixture generalizes one identity function and uses
it independently at `Int` and matcher types. -/
def fixture : Expr := expression

/-- The closed fixture has a static root request plan at every evaluator
fuel.  At positive useful fuel, the body requests non-universal call
observations from the generalized binding, while the closed right-hand side
has a pointwise universal outer input. -/
def fixtureSupported : M4.RawOriginNoStuckSupported fixture := by
  intro operationalFuel
  cases operationalFuel with
  | zero =>
      exact ⟨OriginEnvironmentDemand.none, .timeout⟩
  | succ childFuel =>
      cases childFuel with
      | zero =>
          exact ⟨OriginEnvironmentDemand.tail OriginEnvironmentDemand.none,
            .letUniversalInput .timeout (fun _ => .none) .timeout⟩
      | succ tupleChildFuel =>
          cases tupleChildFuel with
          | zero =>
              let appInput := OriginEnvironmentDemand.none
              let bodyInput := OriginEnvironmentDemand.both appInput
                (OriginEnvironmentDemand.both appInput
                  OriginEnvironmentDemand.none)
              let valueInput := OriginEnvironmentDemand.none
              have bodyPlan : M4.RawOriginRequestPlan 1 body .none bodyInput :=
                .universal
                  (.tupleFuel (resultIndex := 0)
                    (.cons
                      (.timeout (expression := .app (.var 0) (.lit 1))
                        (outputDemand := .fuel 0))
                      (.cons
                        (.timeout (expression := .app (.var 0) .something)
                          (outputDemand := .fuel 0))
                        (.nil (resultIndex := 0)))))
                  .none
              have valuePlan : M4.RawOriginRequestPlan 1 (.lam (.var 0))
                  (bodyInput 0) valueInput := by
                apply M4.RawOriginRequestPlan.universal
                  (.lamZeroCall (lambdaOperationalFuel := 1)
                    (body := .var 0) (argumentDemand := .none)
                    (resultDemand := .none))
                exact .both .none (.both .none .none)
              exact ⟨OriginEnvironmentDemand.tail bodyInput,
                .letUniversalInput valuePlan (fun _ => .none) bodyPlan⟩
          | succ appChildFuel =>
              let callDemand : OriginDemand :=
                .plainCall appChildFuel (.fuel 0) (.fuel 0)
              let functionInput :=
                OriginEnvironmentDemand.single 0 callDemand
              let appInput := OriginEnvironmentDemand.both functionInput
                OriginEnvironmentDemand.none
              let bodyInput := OriginEnvironmentDemand.both appInput
                (OriginEnvironmentDemand.both appInput
                  OriginEnvironmentDemand.none)
              let callValueInput := OriginEnvironmentDemand.tail
                (OriginEnvironmentDemand.single 0 (.fuel 0))
              let appValueInput := OriginEnvironmentDemand.both callValueInput
                callValueInput
              let valueInput := OriginEnvironmentDemand.both appValueInput
                (OriginEnvironmentDemand.both appValueInput appValueInput)
              have callValuePlan : M4.RawOriginRequestPlan
                  (appChildFuel + 2) (.lam (.var 0)) callDemand
                  callValueInput := by
                cases appChildFuel with
                | zero =>
                    exact .lamZeroCall
                | succ bodyFuel =>
                    apply M4.RawOriginRequestPlan.lamPlainCall
                      (.var (operationalFuel := bodyFuel) (position := 0)
                        (outputDemand := .fuel 0))
                    simp [OriginEnvironmentDemand.single]
                    exact OriginDemand.Le.refl (.fuel 0)
              have appValuePlan : M4.RawOriginRequestPlan
                  (appChildFuel + 2) (.lam (.var 0))
                  (.both callDemand .none) appValueInput :=
                .both callValuePlan (.universal callValuePlan .none)
              have valuePlan : M4.RawOriginRequestPlan
                  (appChildFuel + 2) (.lam (.var 0)) (bodyInput 0)
                  valueInput := by
                exact .both appValuePlan
                  (.both appValuePlan (.universal appValuePlan .none))
              have valueInputUniversal : ∀ position,
                  OriginDemand.Universal (valueInput position) := by
                intro position
                simp [valueInput, appValueInput, callValueInput,
                  OriginEnvironmentDemand.both, OriginEnvironmentDemand.tail,
                  OriginEnvironmentDemand.single]
                exact .both (.both .none .none)
                  (.both (.both .none .none) (.both .none .none))
              have firstAppPlan : M4.RawOriginRequestPlan
                  (appChildFuel + 1) (.app (.var 0) (.lit 1)) (.fuel 0)
                  appInput :=
                .app
                  (.var (operationalFuel := appChildFuel) (position := 0)
                    (outputDemand := callDemand))
                  (.litFuel (operationalFuel := appChildFuel)
                    (resultIndex := 0))
              have secondAppPlan : M4.RawOriginRequestPlan
                  (appChildFuel + 1) (.app (.var 0) .something) (.fuel 0)
                  appInput :=
                .app
                  (.var (operationalFuel := appChildFuel) (position := 0)
                    (outputDemand := callDemand))
                  (.somethingFuel (operationalFuel := appChildFuel)
                    (resultIndex := 0))
              have bodyPlan : M4.RawOriginRequestPlan
                  (appChildFuel + 2) body .none bodyInput :=
                .universal
                  (.tupleFuel
                    (.cons firstAppPlan (.cons secondAppPlan .nil)))
                  .none
              exact ⟨OriginEnvironmentDemand.tail bodyInput,
                .letUniversalInput valuePlan valueInputUniversal bodyPlan⟩

/-- The complete fixture is accepted by the public M4 inference entry point. -/
theorem fixture_infer :
    M4.infer Paper1FrozenSignature.signature [] fixture = some resultType :=
  expression_infer

/-- Public declarative M4 typing, obtained from the actual public inference
result rather than a handwritten raw derivation. -/
theorem fixture_typing :
    M4.Typing Paper1FrozenSignature.signature [] fixture resultType := by
  exact M4.infer_success_typing Paper1FrozenSignature.wellFormed fixture_infer

/-- The source-derived recursive plan proves no stuck result at every
evaluator fuel.  No completed evaluation equation occurs in this proof. -/
theorem fixture_neverStuck (operationalFuel : Nat) :
    (evalFuel operationalFuel [] fixture).NotStuck :=
  fixtureSupported.closedNeverStuck fixture_typing operationalFuel

/-- Independent post-safety execution check: the generalized identity is
used successfully at two distinct source types. -/
theorem fixture_fuelFive_exact :
    evalFuel 5 [] fixture =
      .ok (.tuple [.int 1, .something]) := by
  rfl

end TypePM.Source.M4RawOriginLetUniversalRegression
