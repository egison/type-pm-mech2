import TypePM.Source.M5Paper1SearchFreeStructuralProducer

/-!
# General arity-zero let composition

The S6 raw rule is context-indexed and therefore cannot be another constructor
of `RawOriginRequestPlan`.  This module composes two ordinary child plan
families at that boundary and exports one principal request producer through
the elaboration-indexed evidence branch.
-/

namespace TypePM.Source.M5Paper1ArityZeroLetProducer

open TypePM.Runtime
open M5CompletionArchitecture
open M5PrincipalOriginCertificate
open M5Paper1SearchFreeStructuralProducer

/-- An ordinary child-plan producer with one fixed result shape.  Its input
demand is selected before runtime values are known and is uniform across all
later uses of the plan. -/
structure RawApplicablePlanFamily (expression : Expr) (target : Ty) : Type where
  inputDemand : Nat → OriginDemand → OriginEnvironmentDemand
  plan : ∀ operationalFuel outputDemand,
    OriginDemandApplicable outputDemand target →
      M4.RawOriginRequestPlan operationalFuel expression outputDemand
        (inputDemand operationalFuel outputDemand)

/-- Canonical search-free syntax supplies an ordinary child-plan family. -/
noncomputable def RawApplicablePlanFamily.ofPlanScope
    (tree : PlanScope expression target) :
    RawApplicablePlanFamily expression target where
  inputDemand := M5Paper1SearchFreeStructuralProducer.inputDemand tree
  plan := by
    classical
    intro operationalFuel outputDemand applicable
    have selected := tree.plan operationalFuel outputDemand applicable
    rw [M5Paper1SearchFreeStructuralProducer.inputDemand,
      dif_pos applicable]
    exact Classical.choose_spec selected

namespace RawApplicablePlanFamily

/-- Select one stable input-demand policy from an existence theorem. -/
noncomputable def ofPlans
    (plans : ∀ operationalFuel outputDemand,
      OriginDemandApplicable outputDemand target →
        ∃ inputDemand,
          M4.RawOriginRequestPlan operationalFuel expression outputDemand
            inputDemand) :
    RawApplicablePlanFamily expression target := by
  classical
  exact
    { inputDemand := fun operationalFuel outputDemand =>
        if applicable : OriginDemandApplicable outputDemand target then
          Classical.choose (plans operationalFuel outputDemand applicable)
        else OriginEnvironmentDemand.none
      plan := by
        intro operationalFuel outputDemand applicable
        simp only [dif_pos applicable]
        exact Classical.choose_spec
          (plans operationalFuel outputDemand applicable) }

/-- An open variable supports every result observation directly. -/
def var (position : Nat) (target : Ty) :
    RawApplicablePlanFamily (.var position) target where
  inputDemand := fun _ outputDemand =>
    OriginEnvironmentDemand.single position outputDemand
  plan := by
    intro operationalFuel outputDemand _applicable
    exact .var

/-- The canonical something matcher supports every applicable observation of
its matcher result type. -/
noncomputable def something (target : Ty) :
    RawApplicablePlanFamily .something (.matcher .any target) :=
  ofPlanScope .something

/-- Binary tuple composition over two arbitrary child families. -/
noncomputable def tuple
    (left : RawApplicablePlanFamily leftExpression leftTarget)
    (right : RawApplicablePlanFamily rightExpression rightTarget) :
    RawApplicablePlanFamily (.tuple [leftExpression, rightExpression])
      (.prod [leftTarget, rightTarget]) :=
  ofPlans (by
    intro operationalFuel outputDemand applicable
    refine M5Paper1SearchFreeStructuralProducer.closeDemand
      (target := .prod [leftTarget, rightTarget]) ?_ operationalFuel
        outputDemand applicable
    intro childFuel atomicDemand notNone notBoth atomicApplicable
    cases atomicDemand with
    | none => contradiction
    | both leftDemand rightDemand =>
        exact False.elim (notBoth leftDemand rightDemand rfl)
    | fuel index =>
        have fieldsApplicable : FuelDemandApplicable index leftTarget ∧
            FuelDemandApplicable index rightTarget := by
          cases index with
          | zero => exact ⟨.zero _, .zero _⟩
          | succ index =>
              exact fuelDemandApplicable_pair_succ (by
                simpa only [OriginDemandApplicable] using atomicApplicable)
        let leftPlan := left.plan childFuel (.fuel index)
          (originDemandApplicable_fuel fieldsApplicable.1)
        let rightPlan := right.plan childFuel (.fuel index)
          (originDemandApplicable_fuel fieldsApplicable.2)
        exact ⟨OriginEnvironmentDemand.both
            (left.inputDemand childFuel (.fuel index))
            (OriginEnvironmentDemand.both
              (right.inputDemand childFuel (.fuel index))
              OriginEnvironmentDemand.none),
          .tupleFuel (.cons leftPlan (.cons rightPlan .nil))⟩
    | pairOf leftDemand rightDemand =>
        simp only [OriginDemandApplicable] at atomicApplicable
        rcases atomicApplicable with
          ⟨actualLeft, actualRight, targetEq,
            ⟨leftApplicable, rightApplicable⟩⟩
        have fieldsEq : leftTarget = actualLeft ∧ rightTarget = actualRight := by
          simpa using Ty.prod.inj targetEq
        rcases fieldsEq with ⟨rfl, rfl⟩
        let leftPlan := left.plan childFuel leftDemand leftApplicable
        let rightPlan := right.plan childFuel rightDemand rightApplicable
        exact ⟨OriginEnvironmentDemand.both
            (left.inputDemand childFuel leftDemand)
            (right.inputDemand childFuel rightDemand),
          .tuplePair leftPlan rightPlan⟩
    | listOf element =>
        simp only [OriginDemandApplicable] at atomicApplicable
        rcases atomicApplicable with ⟨elementType, impossible, _⟩
        simp [DataTypes.list] at impossible
    | bool => simp [OriginDemandApplicable, DataTypes.bool] at atomicApplicable
    | int | plainCall _ _ _ =>
        simp [OriginDemandApplicable] at atomicApplicable)

/-- Canonical list-cons composition over arbitrary head and tail families. -/
noncomputable def listCons
    (head : RawApplicablePlanFamily headExpression elementType)
    (tail : RawApplicablePlanFamily tailExpression (DataTypes.list elementType)) :
    RawApplicablePlanFamily
      (.ctor .cons [headExpression, tailExpression])
      (DataTypes.list elementType) :=
  ofPlans (by
    intro operationalFuel outputDemand applicable
    refine M5Paper1SearchFreeStructuralProducer.closeDemand
      (target := DataTypes.list elementType) ?_ operationalFuel outputDemand
        applicable
    intro childFuel atomicDemand notNone notBoth atomicApplicable
    cases atomicDemand with
    | none => contradiction
    | both left right => exact False.elim (notBoth left right rfl)
    | fuel index =>
        have elementApplicable : FuelDemandApplicable index elementType := by
          cases index with
          | zero => exact .zero _
          | succ index => exact fuelDemandApplicable_list_succ (by
              simpa only [OriginDemandApplicable] using atomicApplicable)
        let headPlan := head.plan childFuel (.fuel index)
          (originDemandApplicable_fuel elementApplicable)
        have tailApplicable : OriginDemandApplicable
            (.listOf (.fuel index)) (DataTypes.list elementType) := by
          simpa only [OriginDemandApplicable] using
            (show ∃ actualElement,
                DataTypes.list elementType = DataTypes.list actualElement ∧
                  FuelDemandApplicable index actualElement from
              ⟨elementType, rfl, elementApplicable⟩)
        let tailPlan := tail.plan childFuel (.listOf (.fuel index))
          tailApplicable
        exact ⟨OriginEnvironmentDemand.both
            (head.inputDemand childFuel (.fuel index))
            (OriginEnvironmentDemand.both
              (tail.inputDemand childFuel (.listOf (.fuel index)))
              OriginEnvironmentDemand.none),
          .ctor .listConsFuel (.cons headPlan (.cons tailPlan .nil))⟩
    | listOf elementDemand =>
        simp only [OriginDemandApplicable] at atomicApplicable
        rcases atomicApplicable with
          ⟨actualElement, targetEq, elementApplicable⟩
        have elementEq : actualElement = elementType := by
          simpa [DataTypes.list] using (Ty.data.inj targetEq).2.symm
        subst actualElement
        let headPlan := head.plan childFuel elementDemand elementApplicable
        have tailApplicable : OriginDemandApplicable
            (.listOf elementDemand) (DataTypes.list elementType) := by
          simpa only [OriginDemandApplicable] using
            (show ∃ actualElement,
                DataTypes.list elementType = DataTypes.list actualElement ∧
                  OriginDemandApplicable elementDemand actualElement from
              ⟨elementType, rfl, elementApplicable⟩)
        let tailPlan := tail.plan childFuel (.listOf elementDemand)
          tailApplicable
        exact ⟨OriginEnvironmentDemand.both
            (head.inputDemand childFuel elementDemand)
            (OriginEnvironmentDemand.both
              (tail.inputDemand childFuel (.listOf elementDemand))
              OriginEnvironmentDemand.none),
          .ctor .listCons (.cons headPlan (.cons tailPlan .nil))⟩
    | pairOf left right =>
        simp [OriginDemandApplicable, DataTypes.list] at atomicApplicable
    | bool =>
        simp [OriginDemandApplicable, DataTypes.bool, DataTypes.list,
          DataFormer.bool, DataFormer.list] at atomicApplicable
    | int | plainCall _ _ _ =>
        simp [OriginDemandApplicable, DataTypes.list] at atomicApplicable)

/-- List append composition over two arbitrary list families. -/
noncomputable def append
    (left : RawApplicablePlanFamily leftExpression (DataTypes.list elementType))
    (right : RawApplicablePlanFamily rightExpression (DataTypes.list elementType)) :
    RawApplicablePlanFamily (.prim .append [leftExpression, rightExpression])
      (DataTypes.list elementType) :=
  ofPlans (by
    intro operationalFuel outputDemand applicable
    refine M5Paper1SearchFreeStructuralProducer.closeDemand
      (target := DataTypes.list elementType) ?_ operationalFuel outputDemand
        applicable
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
        have listApplicable : OriginDemandApplicable
            (.listOf (.fuel index)) (DataTypes.list elementType) := by
          simpa only [OriginDemandApplicable] using
            (show ∃ actualElement,
                DataTypes.list elementType = DataTypes.list actualElement ∧
                  FuelDemandApplicable index actualElement from
              ⟨elementType, rfl, elementApplicable⟩)
        let leftPlan := left.plan childFuel (.listOf (.fuel index)) listApplicable
        let rightPlan := right.plan childFuel (.listOf (.fuel index)) listApplicable
        exact ⟨OriginEnvironmentDemand.both
            (left.inputDemand childFuel (.listOf (.fuel index)))
            (OriginEnvironmentDemand.both
              (right.inputDemand childFuel (.listOf (.fuel index)))
              OriginEnvironmentDemand.none),
          .prim .appendFuel (.cons leftPlan (.cons rightPlan .nil))⟩
    | listOf elementDemand =>
        simp only [OriginDemandApplicable] at atomicApplicable
        rcases atomicApplicable with
          ⟨actualElement, targetEq, elementApplicable⟩
        have elementEq : actualElement = elementType := by
          simpa [DataTypes.list] using (Ty.data.inj targetEq).2.symm
        subst actualElement
        have listApplicable : OriginDemandApplicable
            (.listOf elementDemand) (DataTypes.list elementType) := by
          simpa only [OriginDemandApplicable] using
            (show ∃ actualElement,
                DataTypes.list elementType = DataTypes.list actualElement ∧
                  OriginDemandApplicable elementDemand actualElement from
              ⟨elementType, rfl, elementApplicable⟩)
        let leftPlan := left.plan childFuel (.listOf elementDemand) listApplicable
        let rightPlan := right.plan childFuel (.listOf elementDemand) listApplicable
        exact ⟨OriginEnvironmentDemand.both
            (left.inputDemand childFuel (.listOf elementDemand))
            (OriginEnvironmentDemand.both
              (right.inputDemand childFuel (.listOf elementDemand))
              OriginEnvironmentDemand.none),
          .prim .append (.cons leftPlan (.cons rightPlan .nil))⟩
    | pairOf left right =>
        simp [OriginDemandApplicable, DataTypes.list] at atomicApplicable
    | bool =>
        simp [OriginDemandApplicable, DataTypes.bool, DataTypes.list,
          DataFormer.bool, DataFormer.list] at atomicApplicable
    | int | plainCall _ _ _ =>
        simp [OriginDemandApplicable, DataTypes.list] at atomicApplicable)

/-- Membership composition over an arbitrary element and list family. -/
noncomputable def member
    (item : RawApplicablePlanFamily itemExpression elementType)
    (items : RawApplicablePlanFamily itemsExpression (DataTypes.list elementType)) :
    RawApplicablePlanFamily (.prim .member [itemExpression, itemsExpression])
      DataTypes.bool :=
  ofPlans (by
    intro operationalFuel outputDemand applicable
    refine M5Paper1SearchFreeStructuralProducer.closeDemand
      (target := DataTypes.bool) ?_ operationalFuel outputDemand applicable
    intro childFuel atomicDemand notNone notBoth atomicApplicable
    cases atomicDemand with
    | none => contradiction
    | both left right => exact False.elim (notBoth left right rfl)
    | fuel index | bool =>
        let itemPlan := item.plan childFuel .none (by
          simp [OriginDemandApplicable])
        have itemsApplicable : OriginDemandApplicable (.listOf .none)
            (DataTypes.list elementType) := by
          simpa only [OriginDemandApplicable] using
            (show ∃ actualElement,
                DataTypes.list elementType = DataTypes.list actualElement ∧ True
              from ⟨elementType, rfl, trivial⟩)
        let itemsPlan := items.plan childFuel (.listOf .none) itemsApplicable
        exact ⟨OriginEnvironmentDemand.both
            (item.inputDemand childFuel .none)
            (OriginEnvironmentDemand.both
              (items.inputDemand childFuel (.listOf .none))
              OriginEnvironmentDemand.none),
          .prim (by first | exact .memberFuel | exact .member)
            (.cons itemPlan (.cons itemsPlan .nil))⟩
    | pairOf left right =>
        simp [OriginDemandApplicable, DataTypes.bool] at atomicApplicable
    | listOf element =>
        simp [OriginDemandApplicable, DataTypes.bool, DataTypes.list,
          DataFormer.bool, DataFormer.list] at atomicApplicable
    | int | plainCall _ _ _ =>
        simp [OriginDemandApplicable, DataTypes.bool] at atomicApplicable)

/-- Delete-first composition over an arbitrary element and list family. -/
noncomputable def deleteFirst
    (item : RawApplicablePlanFamily itemExpression elementType)
    (items : RawApplicablePlanFamily itemsExpression (DataTypes.list elementType)) :
    RawApplicablePlanFamily
      (.prim .deleteFirst [itemExpression, itemsExpression])
      (DataTypes.list elementType) :=
  ofPlans (by
    intro operationalFuel outputDemand applicable
    refine M5Paper1SearchFreeStructuralProducer.closeDemand
      (target := DataTypes.list elementType) ?_ operationalFuel outputDemand
        applicable
    intro childFuel atomicDemand notNone notBoth atomicApplicable
    cases atomicDemand with
    | none => contradiction
    | both left right => exact False.elim (notBoth left right rfl)
    | fuel index =>
        have elementApplicable : FuelDemandApplicable index elementType := by
          cases index with
          | zero => exact .zero _
          | succ index => exact fuelDemandApplicable_list_succ (by
              simpa only [OriginDemandApplicable] using atomicApplicable)
        let itemPlan := item.plan childFuel .none (by
          simp [OriginDemandApplicable])
        have itemsApplicable : OriginDemandApplicable
            (.listOf (.fuel index)) (DataTypes.list elementType) := by
          simpa only [OriginDemandApplicable] using
            (show ∃ actualElement,
                DataTypes.list elementType = DataTypes.list actualElement ∧
                  FuelDemandApplicable index actualElement from
              ⟨elementType, rfl, elementApplicable⟩)
        let itemsPlan := items.plan childFuel (.listOf (.fuel index))
          itemsApplicable
        exact ⟨OriginEnvironmentDemand.both
            (item.inputDemand childFuel .none)
            (OriginEnvironmentDemand.both
              (items.inputDemand childFuel (.listOf (.fuel index)))
              OriginEnvironmentDemand.none),
          .prim .deleteFirstFuel (.cons itemPlan (.cons itemsPlan .nil))⟩
    | listOf elementDemand =>
        simp only [OriginDemandApplicable] at atomicApplicable
        rcases atomicApplicable with
          ⟨actualElement, targetEq, elementApplicable⟩
        have elementEq : actualElement = elementType := by
          simpa [DataTypes.list] using (Ty.data.inj targetEq).2.symm
        subst actualElement
        let itemPlan := item.plan childFuel .none (by
          simp [OriginDemandApplicable])
        have itemsApplicable : OriginDemandApplicable
            (.listOf elementDemand) (DataTypes.list elementType) := by
          simpa only [OriginDemandApplicable] using
            (show ∃ actualElement,
                DataTypes.list elementType = DataTypes.list actualElement ∧
                  OriginDemandApplicable elementDemand actualElement from
              ⟨elementType, rfl, elementApplicable⟩)
        let itemsPlan := items.plan childFuel (.listOf elementDemand)
          itemsApplicable
        exact ⟨OriginEnvironmentDemand.both
            (item.inputDemand childFuel .none)
            (OriginEnvironmentDemand.both
              (items.inputDemand childFuel (.listOf elementDemand))
              OriginEnvironmentDemand.none),
          .prim .deleteFirst (.cons itemPlan (.cons itemsPlan .nil))⟩
    | pairOf left right =>
        simp [OriginDemandApplicable, DataTypes.list] at atomicApplicable
    | bool =>
        simp [OriginDemandApplicable, DataTypes.bool, DataTypes.list,
          DataFormer.bool, DataFormer.list] at atomicApplicable
    | int | plainCall _ _ _ =>
        simp [OriginDemandApplicable, DataTypes.list] at atomicApplicable)

/-- First projection from an arbitrary binary-product family. -/
noncomputable def pairFirst
    (pair : RawApplicablePlanFamily pairExpression
      (.prod [leftTarget, rightTarget])) :
    RawApplicablePlanFamily (.prim .pairFirst [pairExpression]) leftTarget :=
  ofPlans (by
    intro operationalFuel outputDemand applicable
    refine M5Paper1SearchFreeStructuralProducer.closeDemand
      (target := leftTarget) ?_ operationalFuel outputDemand applicable
    intro childFuel atomicDemand notNone notBoth atomicApplicable
    have pairApplicable : OriginDemandApplicable
        (.pairOf atomicDemand .none) (.prod [leftTarget, rightTarget]) := by
      simpa only [OriginDemandApplicable] using
        (show ∃ actualLeft actualRight,
            (.prod [leftTarget, rightTarget] : Ty) =
                .prod [actualLeft, actualRight] ∧
              OriginDemandApplicable atomicDemand actualLeft ∧ True from
          ⟨leftTarget, rightTarget, rfl, atomicApplicable, trivial⟩)
    let pairPlan := pair.plan childFuel (.pairOf atomicDemand .none)
      pairApplicable
    exact ⟨OriginEnvironmentDemand.both
        (pair.inputDemand childFuel (.pairOf atomicDemand .none))
        OriginEnvironmentDemand.none,
      .prim .pairFirst (.cons pairPlan .nil)⟩)

/-- Second projection from an arbitrary binary-product family. -/
noncomputable def pairSecond
    (pair : RawApplicablePlanFamily pairExpression
      (.prod [leftTarget, rightTarget])) :
    RawApplicablePlanFamily (.prim .pairSecond [pairExpression]) rightTarget :=
  ofPlans (by
    intro operationalFuel outputDemand applicable
    refine M5Paper1SearchFreeStructuralProducer.closeDemand
      (target := rightTarget) ?_ operationalFuel outputDemand applicable
    intro childFuel atomicDemand notNone notBoth atomicApplicable
    have pairApplicable : OriginDemandApplicable
        (.pairOf .none atomicDemand) (.prod [leftTarget, rightTarget]) := by
      simpa only [OriginDemandApplicable] using
        (show ∃ actualLeft actualRight,
            (.prod [leftTarget, rightTarget] : Ty) =
                .prod [actualLeft, actualRight] ∧
              True ∧ OriginDemandApplicable atomicDemand actualRight from
          ⟨leftTarget, rightTarget, rfl, trivial, atomicApplicable⟩)
    let pairPlan := pair.plan childFuel (.pairOf .none atomicDemand)
      pairApplicable
    exact ⟨OriginEnvironmentDemand.both
        (pair.inputDemand childFuel (.pairOf .none atomicDemand))
        OriginEnvironmentDemand.none,
      .prim .pairSecond (.cons pairPlan .nil)⟩)

/-- Conditional composition over arbitrary compatible branch families. -/
noncomputable def ifE
    (condition : RawApplicablePlanFamily conditionExpression DataTypes.bool)
    (thenBranch : RawApplicablePlanFamily thenExpression target)
    (elseBranch : RawApplicablePlanFamily elseExpression target) :
    RawApplicablePlanFamily
      (.ifE conditionExpression thenExpression elseExpression) target :=
  ofPlans (by
    intro operationalFuel outputDemand applicable
    refine M5Paper1SearchFreeStructuralProducer.closeDemand
      (target := target) ?_ operationalFuel outputDemand applicable
    intro childFuel atomicDemand notNone notBoth atomicApplicable
    let conditionPlan := condition.plan childFuel .bool (by
      simp [OriginDemandApplicable])
    let thenPlan := thenBranch.plan childFuel atomicDemand atomicApplicable
    let elsePlan := elseBranch.plan childFuel atomicDemand atomicApplicable
    exact ⟨OriginEnvironmentDemand.both
        (condition.inputDemand childFuel .bool)
        (OriginEnvironmentDemand.both
          (thenBranch.inputDemand childFuel atomicDemand)
          (elseBranch.inputDemand childFuel atomicDemand)),
      .ifE conditionPlan thenPlan elsePlan⟩)

end RawApplicablePlanFamily

/-- The body's position-zero request is a valid observation of the value
result.  This is the precise non-vacuous compatibility condition needed to
feed the evaluated right-hand side to the generalized body environment. -/
def BindingDemandApplicable
    (_value : RawApplicablePlanFamily valueExpression valueTarget)
    (body : RawApplicablePlanFamily bodyExpression bodyTarget) : Prop :=
  ∀ childFuel outputDemand,
    OriginDemandApplicable outputDemand bodyTarget →
      OriginDemandApplicable
        (body.inputDemand childFuel outputDemand 0) valueTarget

/-- Outer environment demand selected by the S6 composition. -/
def inputDemand
    (value : RawApplicablePlanFamily valueExpression valueTarget)
    (body : RawApplicablePlanFamily bodyExpression bodyTarget)
    (operationalFuel : Nat) (outputDemand : OriginDemand) :
    OriginEnvironmentDemand :=
  match operationalFuel with
  | 0 => OriginEnvironmentDemand.none
  | childFuel + 1 =>
      let bodyInput := body.inputDemand childFuel outputDemand
      OriginEnvironmentDemand.both
        (value.inputDemand childFuel (bodyInput 0))
        (OriginEnvironmentDemand.tail bodyInput)

/-- General S6 composition of arbitrary value and body child-plan producers.
The evaluator predecessor `childFuel` is shared by both children, and the
outer target/demand pair remains arbitrary. -/
noncomputable def requestProducer
    (derivation : M4.PrincipalTypingDerivation signature context
      (.letE valueExpression bodyExpression) principal)
    (value : RawApplicablePlanFamily valueExpression valueTarget)
    (body : RawApplicablePlanFamily bodyExpression bodyTarget)
    (bindingApplicable : BindingDemandApplicable value body)
    (fixedTarget : PrincipalFixedTarget derivation bodyTarget)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext)
    (contextArityZero : M4.ContextSchemeArityZero context) :
    PrincipalOriginRequestProducer derivation runtimeContext where
  inputDemand := inputDemand value body
  request := by
    intro operationalFuel outputDemand target instantiation applicable
    rcases instantiation with ⟨later, targetEq⟩
    have targetExpected : target = bodyTarget := by
      calc
        target = principal.apply later := targetEq.symm
        _ = bodyTarget.apply later := by rw [fixedTarget.principal_eq]
        _ = bodyTarget := fixedTarget.target_stable later
    have bodyApplicable : OriginDemandApplicable outputDemand bodyTarget := by
      simpa [targetExpected] using applicable
    have environmentTransport : ∀ later,
        principal.apply later = target →
          ∀ environment,
            OriginEnvironmentSafe
                (inputDemand value body operationalFuel outputDemand)
                environment runtimeContext →
              SchemeOriginEnvironmentSafe
                (inputDemand value body operationalFuel outputDemand)
                (Subst.compose later derivation.closure.substitution)
                environment context := by
      intro later _targetEq environment environmentSafe
      have postcomposed := contextCompatible.postcompose later
      rw [stable later] at postcomposed
      exact environmentSafe.toSchemeOrigin postcomposed
    cases operationalFuel with
    | zero => exact ⟨.raw .timeout environmentTransport⟩
    | succ childFuel =>
        let bodyInput := body.inputDemand childFuel outputDemand
        let valueInput := value.inputDemand childFuel (bodyInput 0)
        have bindingDemandApplicable :
            OriginDemandApplicable (bodyInput 0) valueTarget :=
          bindingApplicable childFuel outputDemand bodyApplicable
        let letPlan : M4.RawOriginLetArityZeroPlan context childFuel
            valueExpression bodyExpression outputDemand valueInput bodyInput :=
          { contextArityZero := contextArityZero
            valuePlan := value.plan childFuel (bodyInput 0)
              bindingDemandApplicable
            bodyPlan := body.plan childFuel outputDemand bodyApplicable }
        exact ⟨.elaboration (by
          intro staticFuel supply generated next sourceElaboration
          cases staticFuel with
          | zero => exact False.elim sourceElaboration
          | succ staticFuel =>
              simpa [inputDemand, bodyInput, valueInput] using
                letPlan.exactCertificate sourceElaboration)
          (by simpa [inputDemand, bodyInput, valueInput] using
            environmentTransport)⟩

theorem derivationRequestProducer
    (derivation : M4.PrincipalTypingDerivation signature context
      (.letE valueExpression bodyExpression) principal)
    (value : RawApplicablePlanFamily valueExpression valueTarget)
    (body : RawApplicablePlanFamily bodyExpression bodyTarget)
    (bindingApplicable : BindingDemandApplicable value body)
    (fixedTarget : PrincipalFixedTarget derivation bodyTarget)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext)
    (contextArityZero : M4.ContextSchemeArityZero context) :
    DerivationRequestProducer derivation runtimeContext :=
  ⟨requestProducer derivation value body bindingApplicable fixedTarget
    runtimeContext contextCompatible stable contextArityZero⟩

end TypePM.Source.M5Paper1ArityZeroLetProducer
