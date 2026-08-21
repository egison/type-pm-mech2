import TypePM.Runtime.EvalFuelTraced
import TypePM.OriginDemandSafety

/-!
# Origin safety refined by evaluation-trace coverage

`OriginValueSafe` proves preservation for future function calls, but its call
case records only the evaluator result.  The integrated Paper-1 induction also
has to retain every matching-search event emitted while a closure body runs.
This module defines the minimal refinement needed at that higher-order
boundary.

The event property is abstract.  The source integration instantiates it with
the existence of a typed trace annotation for the enclosing principal
derivation.  Forgetting the refinement recovers the existing origin-demand
logical relation, so this layer strengthens rather than replaces M4
preservation.
-/

namespace TypePM.Runtime

/-- A value satisfies its ordinary origin observation and, recursively, every
future function call selected by that observation emits only accepted trace
events.  Structural list and pair observations retain the refinement for
their observed fields. -/
def TracedOriginValueSafe
    (eventSafe : MatchingSearchTraceEvent → Prop) :
    OriginDemand → Value → Ty → Prop
  | .none, value, target => OriginValueSafe .none value target
  | .fuel index, value, target => OriginValueSafe (.fuel index) value target
  | .both left right, value, target =>
      TracedOriginValueSafe eventSafe left value target ∧
        TracedOriginValueSafe eventSafe right value target
  | .listOf elementDemand, value, target =>
      ∃ elementType items,
        target = DataTypes.list elementType ∧
          value = Value.buildList items ∧
            ∀ item, item ∈ items →
              TracedOriginValueSafe eventSafe elementDemand item elementType
  | .pairOf leftDemand rightDemand, value, target =>
      ∃ leftType rightType leftValue rightValue,
        target = .prod [leftType, rightType] ∧
          value = .tuple [leftValue, rightValue] ∧
            TracedOriginValueSafe eventSafe leftDemand leftValue leftType ∧
              TracedOriginValueSafe eventSafe rightDemand rightValue rightType
  | .bool, value, target => OriginValueSafe .bool value target
  | .int, value, target => OriginValueSafe .int value target
  | .plainCall callFuel argumentDemand resultDemand, value, target =>
      OriginValueSafe (.plainCall callFuel argumentDemand resultDemand)
          value target ∧
        ∃ domain codomain,
          target = .fn domain codomain ∧
            ∀ argument,
              TracedOriginValueSafe eventSafe argumentDemand argument domain →
                ((applyFuel callFuel value argument = .timeout ∨
                    ∃ resultValue,
                      applyFuel callFuel value argument = .ok resultValue ∧
                        TracedOriginValueSafe eventSafe resultDemand resultValue
                          codomain) ∧
                  ∀ event,
                    event ∈ applyFuelTrace callFuel value argument →
                      eventSafe event)
termination_by demand => demand

/-- Timeout or a successful trace-refined value, together with coverage of
every event emitted by the evaluation that produced it. -/
def TracedOriginResultSafe
    (eventSafe : MatchingSearchTraceEvent → Prop)
    (demand : OriginDemand) (target : Ty)
    (result : FuelResult Value) (trace : List MatchingSearchTraceEvent) : Prop :=
  (result = .timeout ∨
      ∃ value, result = .ok value ∧
        TracedOriginValueSafe eventSafe demand value target) ∧
    ∀ event, event ∈ trace → eventSafe event

/-- Pointwise trace-refined safety for runtime environments. -/
def TracedOriginEnvironmentSafe
    (eventSafe : MatchingSearchTraceEvent → Prop)
    (demand : OriginEnvironmentDemand)
    (values : ValueEnvironment) (targets : List Ty) : Prop :=
  values.length = targets.length ∧
    ∀ (position : Nat) (target : Ty) (value : Value),
      targets[position]? = some target →
      values[position]? = some value →
        TracedOriginValueSafe eventSafe (demand position) value target

namespace TracedOriginValueSafe

/-- Forget trace coverage and recover the existing origin-demand relation. -/
theorem forget
    (safe : TracedOriginValueSafe eventSafe demand value target) :
    OriginValueSafe demand value target := by
  induction demand generalizing value target with
  | none => simpa only [TracedOriginValueSafe] using safe
  | fuel index => simpa only [TracedOriginValueSafe] using safe
  | both left right leftIH rightIH =>
      have unfolded : TracedOriginValueSafe eventSafe left value target ∧
          TracedOriginValueSafe eventSafe right value target := by
        simpa only [TracedOriginValueSafe] using safe
      exact OriginValueSafe.both (leftIH unfolded.1) (rightIH unfolded.2)
  | listOf element elementIH =>
      simp only [TracedOriginValueSafe] at safe
      rcases safe with ⟨elementType, items, rfl, rfl, itemsSafe⟩
      induction items with
      | nil => exact OriginValueSafe.listNil
      | cons head tail induction =>
          exact OriginValueSafe.listCons
            (elementIH (itemsSafe head (by simp)))
            (induction (by
              intro item member
              exact itemsSafe item (by simp [member])))
  | pairOf left right leftIH rightIH =>
      simp only [TracedOriginValueSafe] at safe
      rcases safe with
        ⟨leftType, rightType, leftValue, rightValue, rfl, rfl,
          leftSafe, rightSafe⟩
      exact OriginValueSafe.pair (leftIH leftSafe) (rightIH rightSafe)
  | bool => simpa only [TracedOriginValueSafe] using safe
  | int => simpa only [TracedOriginValueSafe] using safe
  | plainCall callFuel argument result argumentIH resultIH =>
      have unfolded : OriginValueSafe
          (.plainCall callFuel argument result) value target ∧
          ∃ domain codomain,
            target = .fn domain codomain ∧
              ∀ actual,
                TracedOriginValueSafe eventSafe argument actual domain →
                  ((applyFuel callFuel value actual = .timeout ∨
                      ∃ resultValue,
                        applyFuel callFuel value actual = .ok resultValue ∧
                          TracedOriginValueSafe eventSafe result resultValue
                            codomain) ∧
                    ∀ event,
                      event ∈ applyFuelTrace callFuel value actual →
                        eventSafe event) := by
        simpa only [TracedOriginValueSafe] using safe
      exact unfolded.1

/-- Apply a trace-refined future-call observation. -/
theorem apply
    (functionSafe : TracedOriginValueSafe eventSafe
      (.plainCall callFuel argumentDemand resultDemand) function
      (.fn domain codomain))
    (argumentSafe : TracedOriginValueSafe eventSafe argumentDemand argument
      domain) :
    TracedOriginResultSafe eventSafe resultDemand codomain
      (applyFuel callFuel function argument)
      (applyFuelTrace callFuel function argument) := by
  simp only [TracedOriginValueSafe] at functionSafe
  rcases functionSafe with ⟨_ordinary, actualDomain, actualCodomain,
    targetEq, callSafe⟩
  have typeEq : actualDomain = domain ∧ actualCodomain = codomain := by
    exact ⟨(Ty.fn.inj targetEq).1.symm, (Ty.fn.inj targetEq).2.symm⟩
  rcases typeEq with ⟨rfl, rfl⟩
  exact callSafe argument argumentSafe

end TracedOriginValueSafe

namespace TracedOriginResultSafe

theorem forget
    (safe : TracedOriginResultSafe eventSafe demand target result trace) :
    OriginResultSafe demand target result := by
  rcases safe.1 with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, valueSafe.forget⟩

theorem notStuck
    (safe : TracedOriginResultSafe eventSafe demand target result trace) :
    result.NotStuck :=
  safe.forget.notStuck

end TracedOriginResultSafe

namespace TracedOriginEnvironmentSafe

theorem forget
    (safe : TracedOriginEnvironmentSafe eventSafe demand values targets) :
    OriginEnvironmentSafe demand values targets := by
  refine ⟨safe.1, ?_⟩
  intro position target value targetFound valueFound
  exact (safe.2 position target value targetFound valueFound).forget

end TracedOriginEnvironmentSafe

end TypePM.Runtime
