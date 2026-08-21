import TypePM.StepIndexedClosureSafety
import TypePM.Runtime.EvaluationStuckMonotonicity

/-!
# Structural source-origin demands for runtime values

The existing `FuelValueSafe` relation uses one logical index for a function,
its argument, its result, and the operational fuel of the call.  A source
lambda needs more information.  In particular, a higher-order argument or
result may itself need a future call contract rather than one uniform fuel
index.

`OriginDemand` is a finite observation tree.  A call node records its
operational fuel and structurally smaller demands for its argument and
result.  `PlainCallValueSafe` is a nonrecursive, strictly positive call layer;
`OriginValueSafe` interprets the finite tree by structural recursion.  This
keeps higher-order occurrences positive without changing `FuelValueSafe`.

This module contains only the evaluator-facing relation and its application
laws.  Source elaboration bridges live in higher modules.  The relation
currently covers plain closures; recursive closures, matcher calls, and
search-specific observations require separate demand nodes and safety laws.
-/

namespace TypePM.Runtime

/-- A convenient numeric view of a call whose argument and result demands
are ordinary fuel leaves. -/
structure PlainCallDemand where
  operationalFuel : Nat
  argumentIndex : Nat
  resultIndex : Nat

namespace PlainCallDemand

/-- Safe weakening of a fuel-leaf call: run no longer, assume a stronger
argument, and request a weaker result observation. -/
structure Le (requested available : PlainCallDemand) : Prop where
  operational : requested.operationalFuel ≤ available.operationalFuel
  argument : available.argumentIndex ≤ requested.argumentIndex
  result : requested.resultIndex ≤ available.resultIndex

theorem Le.refl (call : PlainCallDemand) : call.Le call :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem Le.trans
    {requested middle available : PlainCallDemand}
    (first : requested.Le middle) (second : middle.Le available) :
    requested.Le available :=
  ⟨Nat.le_trans first.operational second.operational,
    Nat.le_trans second.argument first.argument,
    Nat.le_trans first.result second.result⟩

end PlainCallDemand

/-- A finite tree of observations requested from a runtime value. -/
inductive OriginDemand where
  | none
  | fuel (index : Nat)
  | both (left right : OriginDemand)
  | plainCall (operationalFuel : Nat)
      (argument result : OriginDemand)

namespace PlainCallDemand

/-- Embed the numeric convenience view into the structural demand tree. -/
def toOriginDemand (call : PlainCallDemand) : OriginDemand :=
  .plainCall call.operationalFuel (.fuel call.argumentIndex)
    (.fuel call.resultIndex)

end PlainCallDemand

namespace OriginDemand

/-- Semantic weakening.  Function arguments are contravariant; call fuel
and results are covariant, while `both` can be introduced or projected. -/
inductive Le : OriginDemand → OriginDemand → Prop where
  | none : Le .none available
  | fuel (indexLe : requested ≤ available) :
      Le (.fuel requested) (.fuel available)
  | both
      (left : Le requestedLeft availableLeft)
      (right : Le requestedRight availableRight) :
      Le (.both requestedLeft requestedRight)
        (.both availableLeft availableRight)
  | fromLeft
      (selected : Le requested availableLeft) :
      Le requested (.both availableLeft availableRight)
  | fromRight
      (selected : Le requested availableRight) :
      Le requested (.both availableLeft availableRight)
  | bothIntro
      (left : Le requestedLeft available)
      (right : Le requestedRight available) :
      Le (.both requestedLeft requestedRight) available
  | plainCall
      (operational : requestedFuel ≤ availableFuel)
      (argument : Le availableArgument requestedArgument)
      (result : Le requestedResult availableResult) :
      Le (.plainCall requestedFuel requestedArgument requestedResult)
        (.plainCall availableFuel availableArgument availableResult)

def Le.refl : ∀ demand, Le demand demand
  | .none => .none
  | .fuel _ => .fuel (Nat.le_refl _)
  | .both left right => .both (Le.refl left) (Le.refl right)
  | .plainCall _ argument result =>
      .plainCall (Nat.le_refl _) (Le.refl argument) (Le.refl result)

end OriginDemand

/-- A nonrecursive, strictly positive call layer.  The two predicates have
already been fixed to smaller demand trees by `OriginValueSafe`. -/
inductive PlainCallValueSafe
    (argumentSafe resultSafe : Value → Ty → Prop) :
    Nat → Value → Ty → Prop where
  | zero : PlainCallValueSafe argumentSafe resultSafe 0 value
      (.fn domain codomain)
  | closure
      (bodySafe : ∀ argument,
        argumentSafe argument domain →
          evalFuel bodyFuel (argument :: environment) body = .timeout ∨
            ∃ result,
              evalFuel bodyFuel (argument :: environment) body = .ok result ∧
                resultSafe result codomain) :
      PlainCallValueSafe argumentSafe resultSafe (bodyFuel + 1)
        (Value.plainClosure environment body) (.fn domain codomain)

/-- Interpret a finite source-origin observation tree.  The recursive calls
in the call case are on the two strict subtrees. -/
def OriginValueSafe : OriginDemand → Value → Ty → Prop
  | .none, _, _ => True
  | .fuel index, value, target => FuelValueSafe index value target
  | .both left right, value, target =>
      OriginValueSafe left value target ∧ OriginValueSafe right value target
  | .plainCall operationalFuel argumentDemand resultDemand, value, target =>
      PlainCallValueSafe
        (fun argument domain => OriginValueSafe argumentDemand argument domain)
        (fun result codomain => OriginValueSafe resultDemand result codomain)
        operationalFuel value target
termination_by demand => demand

/-- Timeout or a value satisfying one finite source-origin demand. -/
def OriginResultSafe (demand : OriginDemand) (target : Ty)
    (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧ OriginValueSafe demand value target

namespace OriginResultSafe

theorem notStuck
    (safe : OriginResultSafe demand target result) : result.NotStuck := by
  rcases safe with timeout | ⟨value, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

theorem ofFuel
    (safe : FuelResultSafe index target result) :
    OriginResultSafe (.fuel index) target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have originSafe : OriginValueSafe (.fuel index) value target := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, originSafe⟩

theorem toFuel
    (safe : OriginResultSafe (.fuel index) target result) :
    FuelResultSafe index target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have fuelSafe : FuelValueSafe index value target := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, fuelSafe⟩

theorem bothLeft
    (safe : OriginResultSafe (.both left right) target result) :
    OriginResultSafe left target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have unfolded : OriginValueSafe left value target ∧
        OriginValueSafe right value target := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, unfolded.1⟩

theorem bothRight
    (safe : OriginResultSafe (.both left right) target result) :
    OriginResultSafe right target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have unfolded : OriginValueSafe left value target ∧
        OriginValueSafe right value target := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, unfolded.2⟩

end OriginResultSafe

namespace OriginValueSafe

theorem ofFuel
    (safe : FuelValueSafe index value target) :
    OriginValueSafe (.fuel index) value target := by
  simpa only [OriginValueSafe]

theorem toFuel
    (safe : OriginValueSafe (.fuel index) value target) :
    FuelValueSafe index value target := by
  simpa only [OriginValueSafe] using safe

theorem both
    (left : OriginValueSafe leftDemand value target)
    (right : OriginValueSafe rightDemand value target) :
    OriginValueSafe (.both leftDemand rightDemand) value target := by
  simpa only [OriginValueSafe] using And.intro left right

theorem bothLeft
    (safe : OriginValueSafe (.both left right) value target) :
    OriginValueSafe left value target := by
  have unfolded : OriginValueSafe left value target ∧
      OriginValueSafe right value target := by
    simpa only [OriginValueSafe] using safe
  exact unfolded.1

theorem bothRight
    (safe : OriginValueSafe (.both left right) value target) :
    OriginValueSafe right value target := by
  have unfolded : OriginValueSafe left value target ∧
      OriginValueSafe right value target := by
    simpa only [OriginValueSafe] using safe
  exact unfolded.2

/-- Construct the exact structural call contract of one plain closure. -/
theorem plainClosure
    (bodySafe : ∀ argument,
      OriginValueSafe argumentDemand argument domain →
        OriginResultSafe resultDemand codomain
          (evalFuel bodyFuel (argument :: environment) body)) :
    OriginValueSafe
      (.plainCall (bodyFuel + 1) argumentDemand resultDemand)
      (Value.plainClosure environment body) (.fn domain codomain) := by
  simpa only [OriginValueSafe] using PlainCallValueSafe.closure bodySafe

theorem apply
    (functionSafe : OriginValueSafe
      (.plainCall operationalFuel argumentDemand resultDemand)
      functionValue (.fn domain codomain))
    (argumentSafe : OriginValueSafe argumentDemand argumentValue domain) :
    OriginResultSafe resultDemand codomain
      (applyFuel operationalFuel functionValue argumentValue) := by
  simp only [OriginValueSafe] at functionSafe
  cases functionSafe with
  | zero => exact .inl rfl
  | closure bodySafe =>
      change OriginResultSafe _ _ (evalFuel _ (_ :: _) _)
      exact bodySafe argumentValue argumentSafe

private theorem applyFuel_originResultSafe_mono
    (operationalLe : smallerFuel ≤ largerFuel)
    (safe : OriginResultSafe availableDemand target
      (applyFuel largerFuel function argument))
    (valueMono : ∀ value,
      OriginValueSafe availableDemand value target →
        OriginValueSafe requestedDemand value target) :
    OriginResultSafe requestedDemand target
      (applyFuel smallerFuel function argument) := by
  cases actualEq : applyFuel smallerFuel function argument with
  | timeout => exact .inl rfl
  | stuck =>
      have raisedStuck := applyFuel_stuck_of_le operationalLe actualEq
      have contradiction : False := by
        have notStuck := safe.notStuck
        rw [raisedStuck] at notStuck
        exact notStuck
      exact contradiction.elim
  | ok actual =>
      have raisedOk := applyFuel_ok_of_le operationalLe actualEq
      rcases safe with timeout | ⟨value, success, valueSafe⟩
      · rw [raisedOk] at timeout
        contradiction
      · rw [raisedOk] at success
        cases success
        exact .inr ⟨actual, rfl, valueMono actual valueSafe⟩

/-- Structural demand weakening, including argument contravariance and
result covariance at call nodes. -/
theorem mono
    (weaken : OriginDemand.Le requested available)
    (safe : OriginValueSafe available value target) :
    OriginValueSafe requested value target := by
  induction weaken generalizing value target with
  | none => simp only [OriginValueSafe]
  | fuel indexLe =>
      exact OriginValueSafe.ofFuel (safe.toFuel.mono indexLe)
  | both left right leftIH rightIH =>
      exact OriginValueSafe.both
        (leftIH safe.bothLeft) (rightIH safe.bothRight)
  | fromLeft selected selectedIH =>
      exact selectedIH safe.bothLeft
  | fromRight selected selectedIH =>
      exact selectedIH safe.bothRight
  | bothIntro left right leftIH rightIH =>
      exact OriginValueSafe.both (leftIH safe) (rightIH safe)
  | @plainCall requestedFuel availableFuel availableArgument
      requestedArgument requestedResult availableResult operational
      argument result argumentIH resultIH =>
      simp only [OriginValueSafe] at safe ⊢
      cases safe with
      | zero =>
          cases requestedFuel with
          | zero => exact .zero
          | succ _ => omega
      | @closure domain availableBodyFuel environment body codomain bodySafe =>
          cases requestedFuel with
          | zero => exact .zero
          | succ requestedBodyFuel =>
              apply PlainCallValueSafe.closure
              intro actualArgument actualArgumentSafe
              have availableArgumentSafe := argumentIH actualArgumentSafe
              have availableApplication : OriginResultSafe availableResult
                  codomain
                  (applyFuel (availableBodyFuel + 1)
                    (.plainClosure environment body) actualArgument) := by
                change OriginResultSafe availableResult codomain
                  (evalFuel availableBodyFuel
                    (actualArgument :: environment) body)
                exact bodySafe actualArgument availableArgumentSafe
              have lowered := applyFuel_originResultSafe_mono operational
                availableApplication (fun resultValue resultSafe =>
                  resultIH resultSafe)
              change OriginResultSafe requestedResult codomain
                (evalFuel requestedBodyFuel
                  (actualArgument :: environment) body)
              exact lowered

theorem plainCallFuelMono
    {requested available : PlainCallDemand}
    (safe : OriginValueSafe available.toOriginDemand functionValue
      (.fn domain codomain))
    (weaken : PlainCallDemand.Le requested available) :
    OriginValueSafe requested.toOriginDemand functionValue
      (.fn domain codomain) := by
  apply safe.mono
  exact .plainCall weaken.operational (.fuel weaken.argument)
    (.fuel weaken.result)

end OriginValueSafe

namespace OriginResultSafe

theorem mono
    (weaken : OriginDemand.Le requested available)
    (safe : OriginResultSafe available target result) :
    OriginResultSafe requested target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, valueSafe.mono weaken⟩

end OriginResultSafe

/-- Exact call-by-value application composition with independent finite
demand trees for the function argument and result. -/
theorem evalFuel_app_origin
    (functionSafe : OriginResultSafe
      (.plainCall childFuel argumentDemand resultDemand)
      (.fn domain codomain)
      (evalFuel childFuel environment functionExpression))
    (argumentSafe : OriginResultSafe argumentDemand domain
      (evalFuel childFuel environment argumentExpression)) :
    OriginResultSafe resultDemand codomain
      (evalFuel (childFuel + 1) environment
        (.app functionExpression argumentExpression)) := by
  rcases functionSafe with functionTimeout |
      ⟨functionValue, functionOk, functionValueSafe⟩
  · exact .inl (by simp [evalFuel, functionTimeout, FuelResult.bind])
  · rcases argumentSafe with argumentTimeout |
        ⟨argumentValue, argumentOk, argumentValueSafe⟩
    · exact .inl (by
        simp [evalFuel, functionOk, argumentTimeout, FuelResult.bind])
    · have applied := functionValueSafe.apply argumentValueSafe
      rcases applied with applicationTimeout |
          ⟨resultValue, applicationOk, resultSafe⟩
      · exact .inl (by
          simp [evalFuel, functionOk, argumentOk, applicationTimeout,
            FuelResult.bind])
      · exact .inr ⟨resultValue, by
          simp [evalFuel, functionOk, argumentOk, applicationOk,
            FuelResult.bind], resultSafe⟩

end TypePM.Runtime
