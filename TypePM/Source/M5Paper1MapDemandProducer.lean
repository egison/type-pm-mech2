import TypePM.Source.M5Paper1ArityZeroLetProducer

/-!
# Demand-specific Paper-1 map producer

Primitive `map` does not provide a raw plan for every applicable observation
of its list result.  Its canonical rule provides exactly a `listOf` result
observation, with a `plainCall` observation of the callback and a `listOf`
observation of the input at the same predecessor fuel.  This module records
that honest boundary without weakening `RawApplicablePlanFamily`.

The list-observation family is closed under `map`.  It also supplies both
children needed by `append`; the resulting append family is total because
the first-order append rules only ask their children for list observations.
-/

namespace TypePM.Source.M5Paper1MapDemandProducer

open TypePM.Runtime
open M5CompletionArchitecture
open M5Paper1SearchFreeStructuralProducer
open M5Paper1ArityZeroLetProducer

/-- A plan family dedicated to observing every element of one list result.
The element demand remains an explicit index, so clients may select it from
their own output observation. -/
structure RawListObservationPlanFamily
    (expression : Expr) (elementType : Ty) : Type where
  inputDemand : Nat → OriginDemand → OriginEnvironmentDemand
  plan : ∀ operationalFuel elementDemand,
    OriginDemandApplicable elementDemand elementType →
      M4.RawOriginRequestPlan operationalFuel expression
        (.listOf elementDemand)
        (inputDemand operationalFuel elementDemand)

namespace RawListObservationPlanFamily

/-- A total applicable-demand family can always be restricted to list
observations. -/
def ofApplicable
    (family : RawApplicablePlanFamily expression
      (DataTypes.list elementType)) :
    RawListObservationPlanFamily expression elementType where
  inputDemand := fun operationalFuel elementDemand =>
    family.inputDemand operationalFuel (.listOf elementDemand)
  plan := by
    intro operationalFuel elementDemand elementApplicable
    apply family.plan operationalFuel (.listOf elementDemand)
    simpa only [OriginDemandApplicable] using
      (show ∃ actualElement,
          DataTypes.list elementType = DataTypes.list actualElement ∧
            OriginDemandApplicable elementDemand actualElement from
        ⟨elementType, rfl, elementApplicable⟩)

/-- Demand-specific `map` composition.  Callback evaluation, input
evaluation, and the runtime callback invocation all use the same predecessor
fuel retained by `RawOriginRequestPlan.primMap`. -/
def map
    (function : RawApplicablePlanFamily functionExpression
      (.fn argumentType resultType))
    (input : RawListObservationPlanFamily inputExpression argumentType)
    (argumentDemand : OriginDemand)
    (argumentApplicable : OriginDemandApplicable argumentDemand argumentType) :
    RawListObservationPlanFamily
      (.prim .map [functionExpression, inputExpression]) resultType where
  inputDemand := fun operationalFuel resultDemand =>
    match operationalFuel with
    | 0 => OriginEnvironmentDemand.none
    | childFuel + 1 =>
        OriginEnvironmentDemand.both
          (function.inputDemand childFuel
            (.plainCall childFuel argumentDemand resultDemand))
          (input.inputDemand childFuel argumentDemand)
  plan := by
    intro operationalFuel resultDemand resultApplicable
    cases operationalFuel with
    | zero => exact .timeout
    | succ childFuel =>
        have callApplicable : OriginDemandApplicable
            (.plainCall childFuel argumentDemand resultDemand)
            (.fn argumentType resultType) := by
          simpa only [OriginDemandApplicable] using
            (show ∃ domain codomain,
                (.fn argumentType resultType : Ty) = .fn domain codomain ∧
                  OriginDemandApplicable argumentDemand domain ∧
                  OriginDemandApplicable resultDemand codomain from
              ⟨argumentType, resultType, rfl, argumentApplicable,
                resultApplicable⟩)
        exact .primMap
          (function.plan childFuel
            (.plainCall childFuel argumentDemand resultDemand) callApplicable)
          (input.plan childFuel argumentDemand argumentApplicable)

/-- Append two list-observation families and recover a total result family.
This is the composition boundary needed when a `map` expression occurs as an
append child. -/
noncomputable def append
    (left : RawListObservationPlanFamily leftExpression elementType)
    (right : RawListObservationPlanFamily rightExpression elementType) :
    RawApplicablePlanFamily (.prim .append [leftExpression, rightExpression])
      (DataTypes.list elementType) :=
  RawApplicablePlanFamily.ofPlans (by
    intro operationalFuel outputDemand applicable
    refine closeDemand (target := DataTypes.list elementType) ?_
      operationalFuel outputDemand applicable
    intro childFuel atomicDemand notNone notBoth atomicApplicable
    cases atomicDemand with
    | none => contradiction
    | both leftDemand rightDemand =>
        exact False.elim (notBoth leftDemand rightDemand rfl)
    | fuel index =>
        have elementApplicable : FuelDemandApplicable index elementType := by
          cases index with
          | zero => exact .zero _
          | succ index => exact fuelDemandApplicable_list_succ (by
              simpa only [OriginDemandApplicable] using atomicApplicable)
        let leftPlan := left.plan childFuel (.fuel index)
          (originDemandApplicable_fuel elementApplicable)
        let rightPlan := right.plan childFuel (.fuel index)
          (originDemandApplicable_fuel elementApplicable)
        exact ⟨OriginEnvironmentDemand.both
            (left.inputDemand childFuel (.fuel index))
            (OriginEnvironmentDemand.both
              (right.inputDemand childFuel (.fuel index))
              OriginEnvironmentDemand.none),
          .prim .appendFuel (.cons leftPlan (.cons rightPlan .nil))⟩
    | listOf elementDemand =>
        simp only [OriginDemandApplicable] at atomicApplicable
        rcases atomicApplicable with
          ⟨actualElement, targetEq, elementApplicable⟩
        have elementEq : actualElement = elementType := by
          simpa [DataTypes.list] using (Ty.data.inj targetEq).2.symm
        subst actualElement
        let leftPlan := left.plan childFuel elementDemand elementApplicable
        let rightPlan := right.plan childFuel elementDemand elementApplicable
        exact ⟨OriginEnvironmentDemand.both
            (left.inputDemand childFuel elementDemand)
            (OriginEnvironmentDemand.both
              (right.inputDemand childFuel elementDemand)
              OriginEnvironmentDemand.none),
          .prim .append (.cons leftPlan (.cons rightPlan .nil))⟩
    | pairOf leftDemand rightDemand =>
        simp [OriginDemandApplicable, DataTypes.list] at atomicApplicable
    | bool =>
        simp [OriginDemandApplicable, DataTypes.bool, DataTypes.list,
          DataFormer.bool, DataFormer.list] at atomicApplicable
    | int | plainCall _ _ _ =>
        simp [OriginDemandApplicable, DataTypes.list] at atomicApplicable)

end RawListObservationPlanFamily

end TypePM.Source.M5Paper1MapDemandProducer
