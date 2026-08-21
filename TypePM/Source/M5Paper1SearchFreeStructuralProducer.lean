import TypePM.Source.M5Paper1RuntimeProducer

/-!
# Canonical search-free Paper-1 producer

This module closes the first structural slice of the final M5 producer.  Its
syntax judgment contains only runtime shapes for which the raw producer has a
canonical result rule: integer/pair trees, Boolean and list constructors,
`add`, `member`, `deleteFirst`, and conditionals.  No arbitrary constructor or
primitive is admitted by the scope.
-/

namespace TypePM.Source.M5Paper1SearchFreeStructuralProducer

open TypePM.Runtime
open M5CompletionArchitecture
open M5PrincipalOriginCertificate
open M5Paper1RuntimeProducer

/-- Search-free source expressions with a statically stated result shape. -/
inductive PlanScope : Expr → Ty → Prop where
  | var : PlanScope (.var position) target
  | something : PlanScope .something (.matcher .any target)
  | pairTree (tree : PairTree expression target) :
      PlanScope expression target
  | tuple
      (left : PlanScope leftExpression leftTarget)
      (right : PlanScope rightExpression rightTarget) :
      PlanScope (.tuple [leftExpression, rightExpression])
        (.prod [leftTarget, rightTarget])
  | boolTrue : PlanScope (.ctor .true []) DataTypes.bool
  | boolFalse : PlanScope (.ctor .false []) DataTypes.bool
  | listNil : PlanScope (.ctor .nil []) (DataTypes.list elementType)
  | listCons
      (head : PlanScope headExpression elementType)
      (tail : PlanScope tailExpression (DataTypes.list elementType)) :
      PlanScope
        (.ctor .cons [headExpression, tailExpression])
        (DataTypes.list elementType)
  | add
      (left : PlanScope leftExpression .int)
      (right : PlanScope rightExpression .int) :
      PlanScope (.prim .add [leftExpression, rightExpression]) .int
  | append
      (left : PlanScope leftExpression (DataTypes.list elementType))
      (right : PlanScope rightExpression (DataTypes.list elementType)) :
      PlanScope (.prim .append [leftExpression, rightExpression])
        (DataTypes.list elementType)
  | member
      (item : PlanScope itemExpression elementType)
      (items : PlanScope itemsExpression (DataTypes.list elementType)) :
      PlanScope (.prim .member [itemExpression, itemsExpression])
        DataTypes.bool
  | deleteFirst
      (item : PlanScope itemExpression elementType)
      (items : PlanScope itemsExpression (DataTypes.list elementType)) :
      PlanScope
        (.prim .deleteFirst [itemExpression, itemsExpression])
        (DataTypes.list elementType)
  | pairFirst
      (pair : PlanScope pairExpression
        (.prod [leftTarget, rightTarget])) :
      PlanScope (.prim .pairFirst [pairExpression]) leftTarget
  | pairSecond
      (pair : PlanScope pairExpression
        (.prod [leftTarget, rightTarget])) :
      PlanScope (.prim .pairSecond [pairExpression]) rightTarget
  | ifE
      (condition : PlanScope conditionExpression DataTypes.bool)
      (thenBranch : PlanScope thenExpression target)
      (elseBranch : PlanScope elseExpression target) :
      PlanScope
        (.ifE conditionExpression thenExpression elseExpression) target

theorem fuelDemandApplicable_list_succ
    (applicable : FuelDemandApplicable (index + 1)
      (DataTypes.list elementType)) :
    FuelDemandApplicable (index + 1) elementType := by
  generalize targetEq : DataTypes.list elementType = target at applicable
  cases applicable <;>
    simp_all [DataTypes.list, DataTypes.bool, DataFormer.list, DataFormer.bool]

theorem fuelDemandApplicable_pair_succ
    (applicable : FuelDemandApplicable (index + 1)
      (.prod [leftTarget, rightTarget])) :
    FuelDemandApplicable (index + 1) leftTarget ∧
      FuelDemandApplicable (index + 1) rightTarget := by
  generalize targetEq : Ty.prod [leftTarget, rightTarget] = target at applicable
  cases applicable with
  | @prod _ itemTypes items =>
      have itemTypesEq : [leftTarget, rightTarget] = itemTypes :=
        Ty.prod.inj targetEq
      subst itemTypes
      cases items with
      | cons leftApplicable tail =>
          cases tail with
          | cons rightApplicable tail =>
              cases tail with
              | nil => exact ⟨leftApplicable, rightApplicable⟩
  | int | bool | list | matcher | slot => cases targetEq

private theorem bool_ne_list_type (elementType : Ty) :
    DataTypes.bool ≠ DataTypes.list elementType := by
  intro equality
  have formerEq := (Ty.data.inj equality).1
  simp [DataFormer.bool, DataFormer.list] at formerEq

private theorem int_ne_list_type (elementType : Ty) :
    Ty.int ≠ DataTypes.list elementType := by
  intro equality
  cases equality

/-- Close atomic raw rules under timeout, `none`, and finite conjunctions of
demands.  The atomic callback is needed only at positive evaluator fuel. -/
theorem closeDemand
    (atomic : ∀ childFuel outputDemand,
      outputDemand ≠ .none →
      (∀ left right, outputDemand ≠ .both left right) →
      OriginDemandApplicable outputDemand target →
        ∃ inputDemand,
          M4.RawOriginRequestPlan (childFuel + 1) expression outputDemand
            inputDemand) :
    ∀ operationalFuel outputDemand,
      OriginDemandApplicable outputDemand target →
        ∃ inputDemand,
          M4.RawOriginRequestPlan operationalFuel expression outputDemand
            inputDemand := by
  intro operationalFuel outputDemand applicable
  cases operationalFuel with
  | zero => exact ⟨OriginEnvironmentDemand.none, .timeout⟩
  | succ childFuel =>
      induction outputDemand with
      | none =>
          obtain ⟨inputDemand, available⟩ := atomic childFuel (.fuel 0)
            (by simp) (by simp)
            (originDemandApplicable_fuel_zero target)
          exact ⟨inputDemand, .universal available .none⟩
      | fuel index =>
          exact atomic childFuel (.fuel index) (by simp) (by simp) applicable
      | both left right leftIH rightIH =>
          have applicable' : OriginDemandApplicable left target ∧
              OriginDemandApplicable right target := by
            simpa only [OriginDemandApplicable] using applicable
          obtain ⟨leftInput, leftPlan⟩ := leftIH applicable'.1
          obtain ⟨rightInput, rightPlan⟩ := rightIH applicable'.2
          exact ⟨OriginEnvironmentDemand.both leftInput rightInput,
            .both leftPlan rightPlan⟩
      | listOf element =>
          exact atomic childFuel (.listOf element) (by simp) (by simp)
            applicable
      | pairOf left right =>
          exact atomic childFuel (.pairOf left right) (by simp) (by simp)
            applicable
      | bool => exact atomic childFuel .bool (by simp) (by simp) applicable
      | int => exact atomic childFuel .int (by simp) (by simp) applicable
      | plainCall callFuel argument result =>
          exact atomic childFuel (.plainCall callFuel argument result)
            (by simp) (by simp) applicable

/-- Every canonical search-free expression has a raw request plan at every
evaluator fuel and every structurally applicable result observation. -/
theorem PlanScope.plan
    (tree : PlanScope expression target) :
    ∀ operationalFuel outputDemand,
      OriginDemandApplicable outputDemand target →
        ∃ inputDemand,
          M4.RawOriginRequestPlan operationalFuel expression outputDemand
            inputDemand := by
  induction tree with
  | var =>
      intro operationalFuel outputDemand applicable
      exact ⟨OriginEnvironmentDemand.single _ outputDemand, .var⟩
  | @something target =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | fuel index =>
          exact ⟨OriginEnvironmentDemand.none, .somethingFuel⟩
      | both left right =>
          exact False.elim (notBoth left right rfl)
      | listOf element | pairOf _ _ | bool | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable, DataTypes.list, DataTypes.bool] at applicable
  | pairTree tree => exact tree.plan
  | @tuple leftExpression leftTarget rightExpression rightTarget left right
      leftIH rightIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
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
                  simpa only [OriginDemandApplicable] using applicable)
          obtain ⟨leftInput, leftPlan⟩ := leftIH childFuel (.fuel index)
            (originDemandApplicable_fuel fieldsApplicable.1)
          obtain ⟨rightInput, rightPlan⟩ := rightIH childFuel (.fuel index)
            (originDemandApplicable_fuel fieldsApplicable.2)
          exact ⟨OriginEnvironmentDemand.both leftInput
              (OriginEnvironmentDemand.both rightInput
                OriginEnvironmentDemand.none),
            .tupleFuel (.cons leftPlan (.cons rightPlan .nil))⟩
      | pairOf leftDemand rightDemand =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨actualLeft, actualRight, targetEq, ⟨leftApplicable,
              rightApplicable⟩⟩
          have fieldsEq : leftTarget = actualLeft ∧ rightTarget = actualRight := by
            simpa using Ty.prod.inj targetEq
          rcases fieldsEq with ⟨rfl, rfl⟩
          obtain ⟨leftInput, leftPlan⟩ :=
            leftIH childFuel leftDemand leftApplicable
          obtain ⟨rightInput, rightPlan⟩ :=
            rightIH childFuel rightDemand rightApplicable
          exact ⟨OriginEnvironmentDemand.both leftInput rightInput,
            .tuplePair leftPlan rightPlan⟩
      | listOf element =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨elementType, impossible, _⟩
          simp [DataTypes.list] at impossible
      | bool =>
          simp [OriginDemandApplicable, DataTypes.bool] at applicable
      | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable] at applicable
  | boolTrue =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | both left right => exact False.elim (notBoth left right rfl)
      | fuel index => exact ⟨OriginEnvironmentDemand.none,
          .ctor .boolTrueFuel .nil⟩
      | bool => exact ⟨OriginEnvironmentDemand.none, .ctor .boolTrue .nil⟩
      | pairOf left right =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨leftType, rightType, impossible, ⟨_left, _right⟩⟩
          simp [DataTypes.bool] at impossible
      | listOf element =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨elementType, impossible, _⟩
          exact False.elim (bool_ne_list_type elementType impossible)
      | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable, DataTypes.bool] at applicable
  | boolFalse =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | both left right => exact False.elim (notBoth left right rfl)
      | fuel index => exact ⟨OriginEnvironmentDemand.none,
          .ctor .boolFalseFuel .nil⟩
      | bool => exact ⟨OriginEnvironmentDemand.none, .ctor .boolFalse .nil⟩
      | pairOf left right =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨leftType, rightType, impossible, ⟨_left, _right⟩⟩
          simp [DataTypes.bool] at impossible
      | listOf element =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨elementType, impossible, _⟩
          exact False.elim (bool_ne_list_type elementType impossible)
      | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable, DataTypes.bool] at applicable
  | @listNil elementType =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | both left right => exact False.elim (notBoth left right rfl)
      | fuel index => exact ⟨OriginEnvironmentDemand.none,
          .ctor .listNilFuel .nil⟩
      | listOf element => exact ⟨OriginEnvironmentDemand.none,
          .ctor .listNil .nil⟩
      | pairOf left right =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨leftType, rightType, impossible, ⟨_left, _right⟩⟩
          simp [DataTypes.list] at impossible
      | bool =>
          simp only [OriginDemandApplicable] at applicable
          simp [DataTypes.bool, DataTypes.list, DataFormer.bool,
            DataFormer.list] at applicable
      | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable, DataTypes.list] at applicable
  | @listCons headExpression elementType tailExpression head tail headIH tailIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | both left right => exact False.elim (notBoth left right rfl)
      | fuel index =>
          have elementApplicable : FuelDemandApplicable index elementType := by
            cases index with
            | zero => exact .zero _
            | succ index =>
                exact fuelDemandApplicable_list_succ (by
                  simpa only [OriginDemandApplicable] using applicable)
          obtain ⟨headInput, headPlan⟩ := headIH childFuel (.fuel index)
            (originDemandApplicable_fuel elementApplicable)
          obtain ⟨tailInput, tailPlan⟩ := tailIH childFuel
            (.listOf (.fuel index)) (by
              simpa only [OriginDemandApplicable] using
                (show ∃ actualElement,
                    DataTypes.list elementType = DataTypes.list actualElement ∧
                      FuelDemandApplicable index actualElement from
                  ⟨elementType, rfl, elementApplicable⟩))
          exact ⟨OriginEnvironmentDemand.both headInput
              (OriginEnvironmentDemand.both tailInput
                OriginEnvironmentDemand.none),
            .ctor .listConsFuel (.cons headPlan (.cons tailPlan .nil))⟩
      | listOf elementDemand =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨actualElement, targetEq, elementApplicable⟩
          have elementEq : actualElement = elementType := by
            simpa [DataTypes.list] using (Ty.data.inj targetEq).2.symm
          subst actualElement
          obtain ⟨headInput, headPlan⟩ :=
            headIH childFuel elementDemand elementApplicable
          obtain ⟨tailInput, tailPlan⟩ := tailIH childFuel
            (.listOf elementDemand) (by
              simpa only [OriginDemandApplicable] using
                (show ∃ actualElement,
                    DataTypes.list elementType = DataTypes.list actualElement ∧
                      OriginDemandApplicable elementDemand actualElement from
                  ⟨elementType, rfl, elementApplicable⟩))
          exact ⟨OriginEnvironmentDemand.both headInput
              (OriginEnvironmentDemand.both tailInput
                OriginEnvironmentDemand.none),
            .ctor .listCons (.cons headPlan (.cons tailPlan .nil))⟩
      | pairOf left right =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨leftType, rightType, impossible, ⟨_left, _right⟩⟩
          simp [DataTypes.list] at impossible
      | bool =>
          simp only [OriginDemandApplicable] at applicable
          simp [DataTypes.bool, DataTypes.list, DataFormer.bool,
            DataFormer.list] at applicable
      | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable, DataTypes.list] at applicable
  | @add leftExpression rightExpression left right leftIH rightIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | both leftDemand rightDemand =>
          exact False.elim (notBoth leftDemand rightDemand rfl)
      | fuel index =>
          obtain ⟨leftInput, leftPlan⟩ := leftIH childFuel .int (by
            simp [OriginDemandApplicable])
          obtain ⟨rightInput, rightPlan⟩ := rightIH childFuel .int (by
            simp [OriginDemandApplicable])
          exact ⟨OriginEnvironmentDemand.both leftInput
              (OriginEnvironmentDemand.both rightInput
                OriginEnvironmentDemand.none),
            .prim .addFuel
              (.cons leftPlan (.cons rightPlan .nil))⟩
      | int =>
          obtain ⟨leftInput, leftPlan⟩ := leftIH childFuel .int (by
            simp [OriginDemandApplicable])
          obtain ⟨rightInput, rightPlan⟩ := rightIH childFuel .int (by
            simp [OriginDemandApplicable])
          exact ⟨OriginEnvironmentDemand.both leftInput
              (OriginEnvironmentDemand.both rightInput
                OriginEnvironmentDemand.none),
            .prim .add (.cons leftPlan (.cons rightPlan .nil))⟩
      | pairOf leftDemand rightDemand =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨leftType, rightType, impossible, ⟨_left, _right⟩⟩
          simp at impossible
      | listOf element =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨elementType, impossible, _⟩
          exact False.elim (int_ne_list_type elementType impossible)
      | bool =>
          simp [OriginDemandApplicable, DataTypes.bool, DataFormer.bool] at applicable
      | plainCall _ _ _ =>
          simp [OriginDemandApplicable] at applicable
  | @append leftExpression elementType rightExpression left right leftIH rightIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | both leftDemand rightDemand =>
          exact False.elim (notBoth leftDemand rightDemand rfl)
      | fuel index =>
          have elementApplicable : FuelDemandApplicable index elementType := by
            cases index with
            | zero => exact .zero _
            | succ index =>
                exact fuelDemandApplicable_list_succ (by
                  simpa only [OriginDemandApplicable] using applicable)
          have listFuelApplicable : OriginDemandApplicable
              (.listOf (.fuel index)) (DataTypes.list elementType) := by
            simpa only [OriginDemandApplicable] using
              (show ∃ actualElement,
                  DataTypes.list elementType = DataTypes.list actualElement ∧
                    FuelDemandApplicable index actualElement from
                ⟨elementType, rfl, elementApplicable⟩)
          obtain ⟨leftInput, leftPlan⟩ :=
            leftIH childFuel (.listOf (.fuel index)) listFuelApplicable
          obtain ⟨rightInput, rightPlan⟩ :=
            rightIH childFuel (.listOf (.fuel index)) listFuelApplicable
          exact ⟨OriginEnvironmentDemand.both leftInput
              (OriginEnvironmentDemand.both rightInput
                OriginEnvironmentDemand.none),
            .prim .appendFuel (.cons leftPlan (.cons rightPlan .nil))⟩
      | listOf elementDemand =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨actualElement, targetEq, elementApplicable⟩
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
          obtain ⟨leftInput, leftPlan⟩ :=
            leftIH childFuel (.listOf elementDemand) listApplicable
          obtain ⟨rightInput, rightPlan⟩ :=
            rightIH childFuel (.listOf elementDemand) listApplicable
          exact ⟨OriginEnvironmentDemand.both leftInput
              (OriginEnvironmentDemand.both rightInput
                OriginEnvironmentDemand.none),
            .prim .append (.cons leftPlan (.cons rightPlan .nil))⟩
      | pairOf leftDemand rightDemand =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨leftType, rightType, impossible, ⟨_left, _right⟩⟩
          simp [DataTypes.list] at impossible
      | bool =>
          simp only [OriginDemandApplicable] at applicable
          simp [DataTypes.bool, DataTypes.list, DataFormer.bool,
            DataFormer.list] at applicable
      | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable, DataTypes.list] at applicable
  | @member itemExpression elementType itemsExpression item items itemIH itemsIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | both left right => exact False.elim (notBoth left right rfl)
      | fuel index =>
          obtain ⟨itemInput, itemPlan⟩ := itemIH childFuel .none (by
            simp [OriginDemandApplicable])
          obtain ⟨itemsInput, itemsPlan⟩ := itemsIH childFuel
            (.listOf .none) (by
              simpa only [OriginDemandApplicable] using
                (show ∃ actualElement,
                    DataTypes.list elementType = DataTypes.list actualElement ∧
                      True from ⟨elementType, rfl, trivial⟩))
          exact ⟨OriginEnvironmentDemand.both itemInput
              (OriginEnvironmentDemand.both itemsInput
                OriginEnvironmentDemand.none),
            .prim .memberFuel
              (.cons itemPlan (.cons itemsPlan .nil))⟩
      | bool =>
          obtain ⟨itemInput, itemPlan⟩ := itemIH childFuel .none (by
            simp [OriginDemandApplicable])
          obtain ⟨itemsInput, itemsPlan⟩ := itemsIH childFuel
            (.listOf .none) (by
              simpa only [OriginDemandApplicable] using
                (show ∃ actualElement,
                    DataTypes.list elementType = DataTypes.list actualElement ∧
                      True from ⟨elementType, rfl, trivial⟩))
          exact ⟨OriginEnvironmentDemand.both itemInput
              (OriginEnvironmentDemand.both itemsInput
                OriginEnvironmentDemand.none),
            .prim .member (.cons itemPlan (.cons itemsPlan .nil))⟩
      | pairOf left right =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨leftType, rightType, impossible, ⟨_left, _right⟩⟩
          simp [DataTypes.bool] at impossible
      | listOf element =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨elementType, impossible, _⟩
          simp [DataTypes.bool, DataTypes.list, DataFormer.bool,
            DataFormer.list] at impossible
      | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable, DataTypes.bool] at applicable
  | @deleteFirst itemExpression elementType itemsExpression item items itemIH
      itemsIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      cases outputDemand with
      | none => contradiction
      | both left right => exact False.elim (notBoth left right rfl)
      | fuel index =>
          have elementApplicable : FuelDemandApplicable index elementType := by
            cases index with
            | zero => exact .zero _
            | succ index =>
                exact fuelDemandApplicable_list_succ (by
                  simpa only [OriginDemandApplicable] using applicable)
          obtain ⟨itemInput, itemPlan⟩ := itemIH childFuel .none (by
            simp [OriginDemandApplicable])
          obtain ⟨itemsInput, itemsPlan⟩ := itemsIH childFuel
            (.listOf (.fuel index)) (by
              simpa only [OriginDemandApplicable] using
                (show ∃ actualElement,
                    DataTypes.list elementType = DataTypes.list actualElement ∧
                      FuelDemandApplicable index actualElement from
                  ⟨elementType, rfl, elementApplicable⟩))
          exact ⟨OriginEnvironmentDemand.both itemInput
              (OriginEnvironmentDemand.both itemsInput
                OriginEnvironmentDemand.none),
            .prim .deleteFirstFuel (.cons itemPlan (.cons itemsPlan .nil))⟩
      | listOf elementDemand =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨actualElement, targetEq, elementApplicable⟩
          have elementEq : actualElement = elementType := by
            simpa [DataTypes.list] using (Ty.data.inj targetEq).2.symm
          subst actualElement
          obtain ⟨itemInput, itemPlan⟩ := itemIH childFuel .none (by
            simp [OriginDemandApplicable])
          obtain ⟨itemsInput, itemsPlan⟩ := itemsIH childFuel
            (.listOf elementDemand) (by
              simpa only [OriginDemandApplicable] using
                (show ∃ actualElement,
                    DataTypes.list elementType = DataTypes.list actualElement ∧
                      OriginDemandApplicable elementDemand actualElement from
                  ⟨elementType, rfl, elementApplicable⟩))
          exact ⟨OriginEnvironmentDemand.both itemInput
              (OriginEnvironmentDemand.both itemsInput
                OriginEnvironmentDemand.none),
            .prim .deleteFirst (.cons itemPlan (.cons itemsPlan .nil))⟩
      | pairOf left right =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with
            ⟨leftType, rightType, impossible, ⟨_left, _right⟩⟩
          simp [DataTypes.list] at impossible
      | bool =>
          simp only [OriginDemandApplicable] at applicable
          simp [DataTypes.bool, DataTypes.list, DataFormer.bool,
            DataFormer.list] at applicable
      | int | plainCall _ _ _ =>
          simp [OriginDemandApplicable, DataTypes.list] at applicable
  | @pairFirst pairExpression leftTarget rightTarget pair pairIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      have pairApplicable : OriginDemandApplicable
          (.pairOf outputDemand .none) (.prod [leftTarget, rightTarget]) := by
        simpa only [OriginDemandApplicable] using
          (show ∃ actualLeft actualRight,
              (Ty.prod [leftTarget, rightTarget]) =
                  (Ty.prod [actualLeft, actualRight]) ∧
                OriginDemandApplicable outputDemand actualLeft ∧ True from
            ⟨leftTarget, rightTarget, rfl, applicable, trivial⟩)
      obtain ⟨pairInput, pairPlan⟩ := pairIH childFuel
        (.pairOf outputDemand .none) pairApplicable
      exact ⟨OriginEnvironmentDemand.both pairInput OriginEnvironmentDemand.none,
        .prim .pairFirst (.cons pairPlan .nil)⟩
  | @pairSecond pairExpression leftTarget rightTarget pair pairIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      have pairApplicable : OriginDemandApplicable
          (.pairOf .none outputDemand) (.prod [leftTarget, rightTarget]) := by
        simpa only [OriginDemandApplicable] using
          (show ∃ actualLeft actualRight,
              (Ty.prod [leftTarget, rightTarget]) =
                  (Ty.prod [actualLeft, actualRight]) ∧
                True ∧ OriginDemandApplicable outputDemand actualRight from
            ⟨leftTarget, rightTarget, rfl, trivial, applicable⟩)
      obtain ⟨pairInput, pairPlan⟩ := pairIH childFuel
        (.pairOf .none outputDemand) pairApplicable
      exact ⟨OriginEnvironmentDemand.both pairInput OriginEnvironmentDemand.none,
        .prim .pairSecond (.cons pairPlan .nil)⟩
  | @ifE conditionExpression thenExpression target elseExpression condition
      thenBranch elseBranch conditionIH thenIH elseIH =>
      apply closeDemand
      intro childFuel outputDemand notNone notBoth applicable
      obtain ⟨conditionInput, conditionPlan⟩ := conditionIH childFuel .bool (by
        simp [OriginDemandApplicable])
      obtain ⟨thenInput, thenPlan⟩ := thenIH childFuel outputDemand applicable
      obtain ⟨elseInput, elsePlan⟩ := elseIH childFuel outputDemand applicable
      exact ⟨OriginEnvironmentDemand.both conditionInput
          (OriginEnvironmentDemand.both thenInput elseInput),
        .ifE conditionPlan thenPlan elsePlan⟩

/-- The principal representative is exactly one substitution-stable canonical
result type.  This is a static side condition, not a hidden runtime producer. -/
structure PrincipalFixedTarget
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (target : Ty) : Prop where
  principal_eq : principal = target
  target_stable : ∀ substitution, target.apply substitution = target

/-- Derivation-indexed scope for the proven canonical structural fragment. -/
def RuntimeScope : M5CompletionArchitecture.RuntimeScope :=
  fun {_signature} {_context} {expression} {_principal} derivation =>
    ∃ target,
      PlanScope expression target ∧
        PrincipalFixedTarget derivation target ∧ expression.MNodeFree

noncomputable def inputDemand
    (tree : PlanScope expression target) :
    Nat → OriginDemand → OriginEnvironmentDemand := by
  classical
  exact fun operationalFuel outputDemand =>
    if applicable : OriginDemandApplicable outputDemand target then
      Classical.choose (tree.plan operationalFuel outputDemand applicable)
    else OriginEnvironmentDemand.none

noncomputable def requestProducer
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (tree : PlanScope expression expected)
    (fixedTarget : PrincipalFixedTarget derivation expected)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext) :
    PrincipalOriginRequestProducer derivation runtimeContext where
  inputDemand := inputDemand tree
  request := by
    classical
    intro operationalFuel outputDemand target instantiation applicable
    rcases instantiation with ⟨later, targetEq⟩
    have targetExpected : target = expected := by
      calc
        target = principal.apply later := targetEq.symm
        _ = expected.apply later := by rw [fixedTarget.principal_eq]
        _ = expected := fixedTarget.target_stable later
    have applicableExpected : OriginDemandApplicable outputDemand expected := by
      simpa [targetExpected] using applicable
    have selected := tree.plan operationalFuel outputDemand applicableExpected
    have plan : M4.RawOriginRequestPlan operationalFuel expression outputDemand
        (inputDemand tree operationalFuel outputDemand) := by
      rw [inputDemand, dif_pos applicableExpected]
      exact Classical.choose_spec selected
    exact ⟨.raw plan (by
      intro later _targetEq environment environmentSafe
      have postcomposed := contextCompatible.postcompose later
      rw [stable later] at postcomposed
      exact environmentSafe.toSchemeOrigin postcomposed)⟩

theorem derivationRequestProducer
    (scope : RuntimeScope derivation)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext) :
    DerivationRequestProducer derivation runtimeContext := by
  rcases scope with ⟨target, tree, fixedTarget, mnodeFree⟩
  exact ⟨requestProducer derivation tree fixedTarget runtimeContext
    contextCompatible stable⟩

end TypePM.Source.M5Paper1SearchFreeStructuralProducer
