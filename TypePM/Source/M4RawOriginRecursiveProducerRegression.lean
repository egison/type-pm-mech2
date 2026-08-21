import TypePM.Source.M4RawOriginRecursiveProducer
import TypePM.Source.Paper1Programs
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility

/-!
# Regression for the recursive raw origin-request producer

The closed fixture

```
(lambda _ => 99) ((lambda x => x) (7, something, lambda y => y))
```

is search-free and contains every source constructor in the current recursive
producer: variable, literal, `something`, tuple, lambda, and application.
The request plan is built for every evaluator fuel before public M4 typing is
used.  The exact successful evaluation appears only after the certificate-based
no-stuck theorem.
-/

namespace TypePM.Source.M4RawOriginRecursiveProducerRegression

open TypePM.Runtime
open TypePM.Source.Paper1Programs

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, tyEquations, capEquations, eliminatedVariable?,
        unificationVars, Equation.unificationVars, Ty.unificationVars,
        Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, Ty.nodeCount, Ty.nodeCountList,
        Cap.nodeCount, Cap.nodeCountList,
        Ty.occursTy, Ty.occursTyList, Cap.occurs, Cap.occursList,
        Equation.apply, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
        Subst.singleTy, Subst.singleCap, Subst.compose, Subst.id])

def fixturePayload : Expr :=
  .tuple [.lit 7, .something, .lam (.var 0)]

def fixtureIdentityApplication : Expr :=
  .app (.lam (.var 0)) fixturePayload

/-- One closed search-free expression containing all six constructors in the
recursive producer's positive fragment. -/
def fixture : Expr :=
  .app (.lam (.lit 99)) fixtureIdentityApplication

/-- The tuple payload realizes the universally safe `fuel 0` observation at
every evaluator fuel. -/
def fixturePayloadPlan : ∀ operationalFuel,
    ∃ inputDemand,
      M4.RawOriginRequestPlan operationalFuel fixturePayload (.fuel 0)
        inputDemand
  | 0 => ⟨OriginEnvironmentDemand.none, .timeout⟩
  | _childFuel + 1 =>
      ⟨OriginEnvironmentDemand.both OriginEnvironmentDemand.none
        (OriginEnvironmentDemand.both OriginEnvironmentDemand.none
          (OriginEnvironmentDemand.both OriginEnvironmentDemand.none
            OriginEnvironmentDemand.none)),
        .tupleFuel
          (.cons (.litFuel (resultIndex := 0))
            (.cons (.somethingFuel (resultIndex := 0))
              (.cons
                (.universal
                  (.lamZeroCall (argumentDemand := .none)
                    (resultDemand := .none))
                  .zero)
                .nil)))⟩

/-- The identity lambda realizes exactly the call observation needed by its
parent application.  At positive call fuel the body plan is the raw variable
constructor, so the variable case is exercised rather than hidden by a
completed evaluation equation. -/
def fixtureIdentityFunctionPlan : ∀ operationalFuel,
    ∃ inputDemand,
      M4.RawOriginRequestPlan operationalFuel (.lam (.var 0))
        (.plainCall operationalFuel (.fuel 0) .none) inputDemand
  | 0 => ⟨OriginEnvironmentDemand.none, .lamZeroCall⟩
  | bodyFuel + 1 =>
      ⟨OriginEnvironmentDemand.tail
        (OriginEnvironmentDemand.single 0 .none),
        .lamPlainCall
          (.var (operationalFuel := bodyFuel) (position := 0)
            (outputDemand := .none))
          (by
            simp [OriginEnvironmentDemand.single]
            exact OriginDemand.Le.none)⟩

def fixtureIdentityApplicationPlan : ∀ operationalFuel,
    ∃ inputDemand,
      M4.RawOriginRequestPlan operationalFuel fixtureIdentityApplication
        .none inputDemand
  | 0 => ⟨OriginEnvironmentDemand.none, .timeout⟩
  | childFuel + 1 => by
      obtain ⟨functionInput, functionPlan⟩ :=
        fixtureIdentityFunctionPlan childFuel
      obtain ⟨argumentInput, argumentPlan⟩ := fixturePayloadPlan childFuel
      exact ⟨OriginEnvironmentDemand.both functionInput argumentInput,
        .app functionPlan argumentPlan⟩

/-- `fuel 0` adds no value-shape requirement, but retains the inner
application's no-stuck certificate for use as the outer argument. -/
def fixtureIdentityApplicationArgumentPlan (operationalFuel : Nat) :
    ∃ inputDemand,
      M4.RawOriginRequestPlan operationalFuel fixtureIdentityApplication
        (.fuel 0) inputDemand := by
  obtain ⟨inputDemand, plan⟩ :=
    fixtureIdentityApplicationPlan operationalFuel
  exact ⟨inputDemand, .universal plan .zero⟩

def fixtureConstantFunctionPlan : ∀ operationalFuel,
    ∃ inputDemand,
      M4.RawOriginRequestPlan operationalFuel (.lam (.lit 99))
        (.plainCall operationalFuel (.fuel 0) .none) inputDemand
  | 0 => ⟨OriginEnvironmentDemand.none, .lamZeroCall⟩
  | bodyFuel + 1 =>
      ⟨OriginEnvironmentDemand.tail OriginEnvironmentDemand.none,
        .lamPlainCall
          (M4.RawOriginRequestPlan.rootNone
            (.litFuel (operationalFuel := bodyFuel) (resultIndex := 0)))
          (by exact OriginDemand.Le.none)⟩

/-- The fixture has a root `none` request plan at every evaluator fuel.  Each
plan fixes its per-position source demand before any semantic solution is
chosen. -/
def fixtureSupported : M4.RawOriginNoStuckSupported fixture := by
  intro operationalFuel
  cases operationalFuel with
  | zero => exact ⟨OriginEnvironmentDemand.none, .timeout⟩
  | succ childFuel =>
      obtain ⟨functionInput, functionPlan⟩ :=
        fixtureConstantFunctionPlan childFuel
      obtain ⟨argumentInput, argumentPlan⟩ :=
        fixtureIdentityApplicationArgumentPlan childFuel
      exact ⟨OriginEnvironmentDemand.both functionInput argumentInput,
        .app functionPlan argumentPlan⟩

private def fixtureGenerated : Generated :=
  { target := .var ⟨7⟩
    hard := [
      .ty (.fn (.var ⟨1⟩) (.var ⟨1⟩))
        (.fn (.var ⟨4⟩) (.var ⟨5⟩)),
      .ty (.fn (.var ⟨0⟩) .int)
        (.fn (.var ⟨6⟩) (.var ⟨7⟩))]
    pending := [
      ⟨.prod [.int, .matcher .any (.var ⟨2⟩),
          .fn (.var ⟨3⟩) (.var ⟨3⟩)], .var ⟨4⟩⟩,
      ⟨.var ⟨5⟩, .var ⟨6⟩⟩] }

private theorem fixture_elaborate :
    M4.elaborate Paper1FrozenSignature.signature [] fixture
        (Context.initialSupply []) =
      some (fixtureGenerated, ⟨8, 0⟩) := by
  rfl'

private theorem fixture_close :
    (inferGeneratedUsing unify fixtureGenerated).bind
      (fun closed => some closed.target) = some .int := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [fixtureGenerated]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  rw [saturateLoop.eq_def]
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  compute_unification
  rw [saturateLoop.eq_def]
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  compute_unification
  simp [residualEquations, Ty.apply, Ty.applyList, Cap.apply,
    Cap.applyList, Subst.compose, Subst.id, Subst.singleTy,
    Subst.singleCap]
  compute_unification

/-- The executable public M4 entry point accepts the complete fixture. -/
theorem fixture_infer :
    M4.infer Paper1FrozenSignature.signature [] fixture = some .int := by
  unfold M4.infer
  rw [fixture_elaborate]
  exact fixture_close

/-- Public declarative M4 typing used by the no-stuck wrapper. -/
theorem fixture_typing :
    M4.Typing Paper1FrozenSignature.signature [] fixture .int :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed fixture_infer

/-- Certificate-based safety for every evaluator fuel.  This theorem depends
on the plan family and public typing, not on the exact evaluation below. -/
theorem fixture_neverStuck (operationalFuel : Nat) :
    (evalFuel operationalFuel [] fixture).NotStuck :=
  fixtureSupported.closedNeverStuck
    Paper1FrozenSignature.runtimeCompatible.toSignatureCompatible
    fixture_typing operationalFuel

/-- A separate post-safety check rules out a regression whose arbitrary-fuel
theorem is useful only because every tested run times out. -/
theorem fixture_fuelFour_exact :
    evalFuel 4 [] fixture = .ok (.int 99) := by
  rfl

end TypePM.Source.M4RawOriginRecursiveProducerRegression
