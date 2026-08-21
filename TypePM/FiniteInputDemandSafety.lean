import TypePM.SchemeIndexedFuelSafety
import TypePM.Runtime.EvaluationStuckMonotonicity

/-!
# Finite input demand for the `letE`/application fragment

This module separates the algebraic requirements on a logical input index
from source elaboration.  `leastLetApplicationInputIndex` is a candidate for
the `letE`/application fragment only.  It is not selected here as the input
index for all of M4: matcher dispatch and search still need their own demand
laws.

The finite-index composition rules consume recursive child-safety callbacks.
They do not assume an equation for a completed evaluation and do not require
an all-index environment.  Consequently they are reusable induction steps,
not a class-wide source-to-runtime certificate producer.
-/

namespace TypePM.Runtime

/-- Exactly the two inequalities consumed by a finite-index `letE` induction
step.  The second inequality accounts for proving an RHS strongly enough to
extend the body environment. -/
structure LetComposableInputIndex (input : Nat → Nat → Nat) : Prop where
  child_le : ∀ fuel resultIndex,
    input fuel resultIndex ≤ input (fuel + 1) resultIndex
  rhs_for_body_le : ∀ fuel resultIndex,
    input fuel (input fuel resultIndex) ≤
      input (fuel + 1) resultIndex

/-- Application additionally needs monotonicity in the requested residual
index and enough parent input to prove the function at the positive layer
`max fuel (resultIndex + 1)`. -/
structure ApplicationComposableInputIndex (input : Nat → Nat → Nat) : Prop where
  result_mono : ∀ fuel smaller larger,
    smaller ≤ larger → input fuel smaller ≤ input fuel larger
  call_le : ∀ fuel resultIndex,
    input fuel (max fuel (resultIndex + 1)) ≤
      input (fuel + 1) resultIndex

/-- An input index with an additive, fuel-dependent reserve. -/
def additiveInputIndex (reserve : Nat → Nat)
    (fuel resultIndex : Nat) : Nat :=
  resultIndex + reserve fuel

/-- The pointwise least additive reserve satisfying both the `letE` and
application laws is `0, 1, 2, 4, 8, ...`. -/
def leastLetApplicationReserve : Nat → Nat
  | 0 => 0
  | fuel + 1 => 2 ^ fuel

/-- Add the least `letE`/application reserve to the requested residual index.
This remains a fragment candidate, not the input index for all M4 forms. -/
def leastLetApplicationInputIndex : Nat → Nat → Nat :=
  additiveInputIndex leastLetApplicationReserve

private theorem pow_two_positive (fuel : Nat) : 1 ≤ 2 ^ fuel := by
  induction fuel with
  | zero => simp
  | succ fuel induction =>
      rw [Nat.pow_succ]
      omega

private theorem succ_le_pow_two (fuel : Nat) : fuel + 1 ≤ 2 ^ fuel := by
  induction fuel with
  | zero => simp
  | succ fuel induction =>
      rw [Nat.pow_succ]
      have positive := pow_two_positive fuel
      omega

theorem leastLetApplicationReserve_child_le :
    leastLetApplicationReserve fuel ≤
      leastLetApplicationReserve (fuel + 1) := by
  cases fuel with
  | zero => simp [leastLetApplicationReserve]
  | succ fuel =>
      simp only [leastLetApplicationReserve, Nat.pow_succ]
      have positive := pow_two_positive fuel
      omega

theorem leastLetApplicationReserve_double_le :
    leastLetApplicationReserve fuel + leastLetApplicationReserve fuel ≤
      leastLetApplicationReserve (fuel + 1) := by
  cases fuel with
  | zero => simp [leastLetApplicationReserve]
  | succ fuel =>
      simp [leastLetApplicationReserve, Nat.pow_succ, Nat.mul_two]

theorem leastLetApplicationInputIndex_letComposable :
    LetComposableInputIndex leastLetApplicationInputIndex := by
  constructor
  · intro fuel resultIndex
    unfold leastLetApplicationInputIndex additiveInputIndex
    have reserve := leastLetApplicationReserve_child_le (fuel := fuel)
    omega
  · intro fuel resultIndex
    unfold leastLetApplicationInputIndex additiveInputIndex
    have reserve := leastLetApplicationReserve_double_le (fuel := fuel)
    omega

theorem leastLetApplicationInputIndex_applicationComposable :
    ApplicationComposableInputIndex leastLetApplicationInputIndex := by
  constructor
  · intro fuel smaller larger smaller_le
    unfold leastLetApplicationInputIndex additiveInputIndex
    omega
  · intro fuel resultIndex
    cases fuel with
    | zero =>
        simp [leastLetApplicationInputIndex, additiveInputIndex,
          leastLetApplicationReserve]
    | succ fuel =>
        unfold leastLetApplicationInputIndex additiveInputIndex
        simp only [leastLetApplicationReserve]
        rw [Nat.pow_succ]
        have growth := succ_le_pow_two fuel
        omega

/-- Pointwise minimality among additive natural-number reserves satisfying
both fragment laws.  Application forces reserve `1` at fuel one; thereafter
the nested-RHS law forces doubling. -/
theorem leastLetApplicationReserve_le
    (letLaws : LetComposableInputIndex (additiveInputIndex reserve))
    (applicationLaws :
      ApplicationComposableInputIndex (additiveInputIndex reserve)) :
    ∀ fuel, leastLetApplicationReserve fuel ≤ reserve fuel := by
  intro fuel
  induction fuel with
  | zero => simp [leastLetApplicationReserve]
  | succ fuel induction =>
      cases fuel with
      | zero =>
          have required := applicationLaws.call_le 0 0
          simp [additiveInputIndex] at required
          change 1 ≤ reserve 1
          omega
      | succ fuel =>
          have doubled := letLaws.rhs_for_body_le (fuel + 1) 0
          simp only [additiveInputIndex, Nat.zero_add] at doubled
          simp only [leastLetApplicationReserve] at induction ⊢
          rw [Nat.pow_succ]
          omega

/-- The previous linear choice `fuel + resultIndex` violates the nested-RHS
law already at evaluator fuel two and requested result index zero. -/
theorem linearInputIndex_not_letComposable :
    ¬ LetComposableInputIndex
      (fun fuel resultIndex => fuel + resultIndex) := by
  intro laws
  have impossible := laws.rhs_for_body_le 2 0
  omega

/-! ## Scheme-indexed finite `letE` composition -/

/-- Finite-index source-scheme `letE` composition.  The parent environment is
lowered separately to the RHS demand and body-tail demand.  The callbacks are
the recursive subderivation hypotheses; neither assumes a selected successful
RHS value. -/
theorem evalFuel_letE_schemeFiniteIndex
    {input : Nat → Nat → Nat}
    (laws : LetComposableInputIndex input)
    (outerSafe : SchemeFuelEnvironmentSafe
      (input (fuel + 1) resultIndex) solution environment sourceContext)
    (valueIH : ∀ supply,
      SchemeFuelEnvironmentSafe (input fuel (input fuel resultIndex))
          solution environment sourceContext →
        FuelResultSafe (input fuel resultIndex)
          ((scheme.instantiate supply).1.apply solution)
          (evalFuel fuel environment valueExpression))
    (bodyIH : ∀ value,
      SchemeFuelEnvironmentSafe (input fuel resultIndex) solution
          (value :: environment) (scheme :: sourceContext) →
        FuelResultSafe resultIndex bodyTarget
          (evalFuel fuel (value :: environment) bodyExpression)) :
    FuelResultSafe resultIndex bodyTarget
      (evalFuel (fuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  apply evalFuel_letE_resultSafeWith
    (boundPredicate := fun value =>
      SchemeFuelValueSafe (input fuel resultIndex) value scheme solution)
  · apply schemeFuelResultSafeWith_of_forallSupply
    intro supply
    exact valueIH supply
      (outerSafe.mono (laws.rhs_for_body_le fuel resultIndex))
  · intro value valueSafe
    exact bodyIH value (.cons valueSafe
      (outerSafe.mono (laws.child_le fuel resultIndex)))

/-- Exact M4 body-tail shape: the RHS uses `sourceContext`, while the body
uses a statically transported `closedContext`.  `closeOuter` carries only
interface-equation evidence, never an evaluator result. -/
theorem evalFuel_letE_schemeFiniteIndex_closedContext
    {input : Nat → Nat → Nat}
    (laws : LetComposableInputIndex input)
    (outerSafe : SchemeFuelEnvironmentSafe
      (input (fuel + 1) resultIndex) solution environment sourceContext)
    (closeOuter : ∀ index,
      SchemeFuelEnvironmentSafe index solution environment sourceContext →
        SchemeFuelEnvironmentSafe index solution environment closedContext)
    (valueIH : ∀ supply,
      SchemeFuelEnvironmentSafe (input fuel (input fuel resultIndex))
          solution environment sourceContext →
        FuelResultSafe (input fuel resultIndex)
          ((scheme.instantiate supply).1.apply solution)
          (evalFuel fuel environment valueExpression))
    (bodyIH : ∀ value,
      SchemeFuelEnvironmentSafe (input fuel resultIndex) solution
          (value :: environment) (scheme :: closedContext) →
        FuelResultSafe resultIndex bodyTarget
          (evalFuel fuel (value :: environment) bodyExpression)) :
    FuelResultSafe resultIndex bodyTarget
      (evalFuel (fuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  apply evalFuel_letE_resultSafeWith
    (boundPredicate := fun value =>
      SchemeFuelValueSafe (input fuel resultIndex) value scheme solution)
  · apply schemeFuelResultSafeWith_of_forallSupply
    intro supply
    exact valueIH supply
      (outerSafe.mono (laws.rhs_for_body_le fuel resultIndex))
  · intro value valueSafe
    apply bodyIH value
    exact .cons valueSafe (closeOuter _
      (outerSafe.mono (laws.child_le fuel resultIndex)))

/-- The M4 `applyFree` body tail is supplied by the static interface solution.
This is a specialization of the preceding finite-index rule. -/
theorem evalFuel_letE_schemeFiniteIndex_applyFree
    {input : Nat → Nat → Nat}
    (laws : LetComposableInputIndex input)
    (outerSafe : SchemeFuelEnvironmentSafe
      (input (fuel + 1) resultIndex) solution environment sourceContext)
    (interfaceSolved : Solves solution
      (sourceContext.interfaceEquations block))
    (valueIH : ∀ supply,
      SchemeFuelEnvironmentSafe (input fuel (input fuel resultIndex))
          solution environment sourceContext →
        FuelResultSafe (input fuel resultIndex)
          ((scheme.instantiate supply).1.apply solution)
          (evalFuel fuel environment valueExpression))
    (bodyIH : ∀ value,
      SchemeFuelEnvironmentSafe (input fuel resultIndex) solution
          (value :: environment) (scheme :: sourceContext.applyFree block) →
        FuelResultSafe resultIndex bodyTarget
          (evalFuel fuel (value :: environment) bodyExpression)) :
    FuelResultSafe resultIndex bodyTarget
      (evalFuel (fuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  exact evalFuel_letE_schemeFiniteIndex_closedContext laws outerSafe
    (fun _ safe => safe.ofApplyFreeInterface interfaceSolved) valueIH bodyIH

/-! ## Residual application safety and its demand law -/

/-- Raise the completed operational call only far enough to use a logical
function certificate, then lower the returned value to the requested residual
index. -/
theorem applyFuel_residualSafe_of_le
    (operational_le : operationalFuel ≤ logicalFuel + 1)
    (result_le : resultIndex ≤ logicalFuel)
    (functionSafe : FuelValueSafe (logicalFuel + 1) functionValue
      (.fn domain codomain))
    (argumentSafe : FuelValueSafe logicalFuel argumentValue domain) :
    FuelResultSafe resultIndex codomain
      (applyFuel operationalFuel functionValue argumentValue) := by
  have raisedSafe : FuelResultSafe logicalFuel codomain
      (applyFuel (logicalFuel + 1) functionValue argumentValue) :=
    functionSafe.apply argumentSafe
  cases actualEq : applyFuel operationalFuel functionValue argumentValue with
  | timeout => exact .inl rfl
  | stuck =>
      have raisedStuck := applyFuel_stuck_of_le operational_le actualEq
      have contradiction : False := by
        have notStuck := raisedSafe.notStuck
        rw [raisedStuck] at notStuck
        exact notStuck
      exact contradiction.elim
  | ok actual =>
      have raisedOk := applyFuel_ok_of_le operational_le actualEq
      rcases raisedSafe with raisedTimeout |
          ⟨raised, raisedSuccess, safe⟩
      · rw [raisedOk] at raisedTimeout
        contradiction
      · rw [raisedOk] at raisedSuccess
        cases raisedSuccess
        exact .inr ⟨actual, rfl, safe.mono result_le⟩

/-- Conditional expression-level application composition.  Both child
evaluations are invoked at their exact finite demands; the argument needs one
logical layer less than the function. -/
theorem evalFuel_app_schemeFiniteIndex
    {input : Nat → Nat → Nat}
    (laws : ApplicationComposableInputIndex input)
    (outerSafe : SchemeFuelEnvironmentSafe
      (input (fuel + 1) resultIndex) solution environment sourceContext)
    (functionIH : SchemeFuelEnvironmentSafe
        (input fuel (max fuel (resultIndex + 1))) solution environment
          sourceContext →
      FuelResultSafe (max fuel (resultIndex + 1)) (.fn domain codomain)
        (evalFuel fuel environment functionExpression))
    (argumentIH : SchemeFuelEnvironmentSafe
        (input fuel (max fuel (resultIndex + 1) - 1)) solution environment
          sourceContext →
      FuelResultSafe (max fuel (resultIndex + 1) - 1) domain
        (evalFuel fuel environment argumentExpression)) :
    FuelResultSafe resultIndex codomain
      (evalFuel (fuel + 1) environment
        (.app functionExpression argumentExpression)) := by
  let callIndex := max fuel (resultIndex + 1)
  have callPositive : 0 < callIndex := by
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ resultIndex)
      (Nat.le_max_right fuel (resultIndex + 1))
  have callEq : callIndex - 1 + 1 = callIndex :=
    Nat.succ_pred_eq_of_pos callPositive
  have functionEnvironmentSafe : SchemeFuelEnvironmentSafe
      (input fuel callIndex) solution environment sourceContext :=
    outerSafe.mono (laws.call_le fuel resultIndex)
  have argumentEnvironmentSafe : SchemeFuelEnvironmentSafe
      (input fuel (callIndex - 1)) solution environment sourceContext := by
    apply outerSafe.mono
    exact Nat.le_trans
      (laws.result_mono fuel (callIndex - 1) callIndex
        (Nat.pred_le callIndex))
      (laws.call_le fuel resultIndex)
  have functionSafe := functionIH (by simpa [callIndex] using
    functionEnvironmentSafe)
  have argumentSafe := argumentIH (by simpa [callIndex] using
    argumentEnvironmentSafe)
  rcases functionSafe with functionTimeout |
      ⟨functionValue, functionSuccess, functionValueSafe⟩
  · exact .inl (by simp [evalFuel, functionTimeout, FuelResult.bind])
  · rcases argumentSafe with argumentTimeout |
        ⟨argumentValue, argumentSuccess, argumentValueSafe⟩
    · exact .inl (by
        simp [evalFuel, functionSuccess, argumentTimeout, FuelResult.bind])
    · have functionAtCall : FuelValueSafe callIndex functionValue
          (.fn domain codomain) := by simpa [callIndex] using functionValueSafe
      have argumentBeforeCall : FuelValueSafe (callIndex - 1) argumentValue
          domain := by simpa [callIndex] using argumentValueSafe
      have applicationSafe : FuelResultSafe resultIndex codomain
          (applyFuel fuel functionValue argumentValue) := by
        rw [← callEq] at functionAtCall
        apply applyFuel_residualSafe_of_le
          (logicalFuel := callIndex - 1)
          (functionSafe := functionAtCall)
          (argumentSafe := argumentBeforeCall)
        · have fuel_le_call : fuel ≤ callIndex := by
            exact Nat.le_max_left fuel (resultIndex + 1)
          simpa [callEq] using fuel_le_call
        · have resultSucc_le : resultIndex + 1 ≤ callIndex := by
            exact Nat.le_max_right fuel (resultIndex + 1)
          omega
      rcases applicationSafe with applicationTimeout |
          ⟨result, applicationSuccess, resultSafe⟩
      · exact .inl (by simp [evalFuel, functionSuccess, argumentSuccess,
          applicationTimeout, FuelResult.bind])
      · exact .inr ⟨result, by simp [evalFuel, functionSuccess,
          argumentSuccess, applicationSuccess, FuelResult.bind], resultSafe⟩

end TypePM.Runtime
