import TypePM.ValueIndexedMatchAllSafety

/-!
# Stable first-order postconditions for value-indexed evaluation

`FuelValueSafe` deliberately loses one index across executable boundaries.
For first-order values such as integers, pairs, and Lists, a stronger but
still concrete postcondition is useful: the returned value is safe at every
index.  The rules in this module retain the canonical fields or List members
needed by projections, `append`, and `map`; they make no claim about arbitrary
values sharing the same static type.
-/

namespace TypePM.Runtime

/-- A concrete value is safe at every step index. -/
def AllFuelValueSafe (value : Value) (target : Ty) : Prop :=
  ∀ fuel, FuelValueSafe fuel value target

/-- A result either times out or returns a value satisfying the supplied
concrete postcondition. -/
def FuelResultSafeWith {α : Type} (predicate : α → Prop)
    (result : FuelResult α) : Prop :=
  result = .timeout ∨ ∃ value, result = .ok value ∧ predicate value

/-- All-index safety as a result postcondition. -/
abbrev AllFuelResultSafe (target : Ty) (result : FuelResult Value) : Prop :=
  FuelResultSafeWith (fun value => AllFuelValueSafe value target) result

/-- A canonical List whose members satisfy an arbitrary concrete
postcondition. -/
def ListValueSafeWith (predicate : Value → Prop) (value : Value) : Prop :=
  ∃ values, value = Value.buildList values ∧
    ∀ item ∈ values, predicate item

abbrev ListResultSafeWith (predicate : Value → Prop)
    (result : FuelResult Value) : Prop :=
  FuelResultSafeWith (ListValueSafeWith predicate) result

/-- A canonical List together with all-index safety of each member. -/
def AllFuelListValueSafe (value : Value) (element : Ty) : Prop :=
  ∃ values, value = Value.buildList values ∧
    ∀ item ∈ values, AllFuelValueSafe item element

abbrev AllFuelListResultSafe (element : Ty)
    (result : FuelResult Value) : Prop :=
  FuelResultSafeWith (fun value => AllFuelListValueSafe value element) result

/-- A concrete binary tuple and all-index safety of its two fields. -/
def AllFuelPairValueSafe (value : Value) (firstType secondType : Ty) : Prop :=
  ∃ first second,
    value = .tuple [first, second] ∧
      AllFuelValueSafe first firstType ∧
      AllFuelValueSafe second secondType

abbrev AllFuelPairResultSafe (firstType secondType : Ty)
    (result : FuelResult Value) : Prop :=
  FuelResultSafeWith
    (fun value => AllFuelPairValueSafe value firstType secondType) result

/-- Exact binary tuple fields with arbitrary concrete postconditions. -/
def PairValueSafeWith (firstPredicate secondPredicate : Value → Prop)
    (value : Value) : Prop :=
  ∃ first second,
    value = .tuple [first, second] ∧
      firstPredicate first ∧ secondPredicate second

abbrev PairResultSafeWith (firstPredicate secondPredicate : Value → Prop)
    (result : FuelResult Value) : Prop :=
  FuelResultSafeWith (PairValueSafeWith firstPredicate secondPredicate) result

/-- The concrete dynamic fact needed by `map`.  Its domain is restricted to
arguments already known safe at every index. -/
def AllFuelFunctionSafe (value : Value) (domain codomain : Ty) : Prop :=
  ∀ fuel argument,
    AllFuelValueSafe argument domain →
      AllFuelResultSafe codomain (applyFuel fuel value argument)

abbrev AllFuelFunctionResultSafe (domain codomain : Ty)
    (result : FuelResult Value) : Prop :=
  FuelResultSafeWith
    (fun value => AllFuelFunctionSafe value domain codomain) result

/-- Dynamic function safety parameterized by concrete argument and result
postconditions. -/
def FunctionSafeWith (argumentPredicate resultPredicate : Value → Prop)
    (value : Value) : Prop :=
  ∀ fuel argument,
    argumentPredicate argument →
      FuelResultSafeWith resultPredicate (applyFuel fuel value argument)

abbrev FunctionResultSafeWith
    (argumentPredicate resultPredicate : Value → Prop)
    (result : FuelResult Value) : Prop :=
  FuelResultSafeWith
    (FunctionSafeWith argumentPredicate resultPredicate) result

theorem FuelResultSafeWith.mono
    (safe : FuelResultSafeWith firstPredicate result)
    (implication : ∀ value, firstPredicate value → secondPredicate value) :
    FuelResultSafeWith secondPredicate result := by
  rcases safe with timeout | ⟨value, success, valuePost⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, implication value valuePost⟩

theorem ListResultSafeWith.mono
    (safe : ListResultSafeWith firstPredicate result)
    (implication : ∀ value, firstPredicate value → secondPredicate value) :
    ListResultSafeWith secondPredicate result := by
  apply FuelResultSafeWith.mono safe
  intro listValue listPost
  obtain ⟨values, rfl, valuesPost⟩ := listPost
  exact ⟨values, rfl, fun value member =>
    implication value (valuesPost value member)⟩

theorem AllFuelResultSafe.toFuelResultSafe
    (safe : AllFuelResultSafe target result) (fuel : Nat) :
    FuelResultSafe fuel target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, valueSafe fuel⟩

theorem AllFuelListValueSafe.toAllFuelValueSafe
    (safe : AllFuelListValueSafe value element) :
    AllFuelValueSafe value (TypePM.DataTypes.list element) := by
  obtain ⟨values, rfl, itemsSafe⟩ := safe
  intro fuel
  exact fuelValueSafe_list_of_forall element fuel values
    (fun item member => itemsSafe item member fuel)

theorem AllFuelListResultSafe.toAllFuelResultSafe
    (safe : AllFuelListResultSafe element result) :
    AllFuelResultSafe (TypePM.DataTypes.list element) result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, valueSafe.toAllFuelValueSafe⟩

theorem AllFuelPairValueSafe.toAllFuelValueSafe
    (safe : AllFuelPairValueSafe value firstType secondType) :
    AllFuelValueSafe value (.prod [firstType, secondType]) := by
  obtain ⟨first, second, rfl, firstSafe, secondSafe⟩ := safe
  intro fuel
  induction fuel with
  | zero => exact fuelValueSafe_zero _ _
  | succ fuel induction =>
      exact fuelValueSafe_tuple induction
        (.cons (firstSafe (fuel + 1))
          (.cons (secondSafe (fuel + 1)) .nil))

theorem AllFuelPairResultSafe.toAllFuelResultSafe
    (safe : AllFuelPairResultSafe firstType secondType result) :
    AllFuelResultSafe (.prod [firstType, secondType]) result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, valueSafe.toAllFuelValueSafe⟩

/-- `letE` transports any concrete postcondition on the bound value to any
concrete postcondition on its body result. -/
theorem evalFuel_letE_resultSafeWith
    (valueSafe : FuelResultSafeWith boundPredicate
      (evalFuel fuel environment valueExpression))
    (bodySafe : ∀ value, boundPredicate value →
      FuelResultSafeWith bodyPredicate
        (evalFuel fuel (value :: environment) bodyExpression)) :
    FuelResultSafeWith bodyPredicate
      (evalFuel (fuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  rcases valueSafe with valueTimeout | ⟨value, valueSuccess, valuePost⟩
  · exact .inl (by simp [evalFuel, valueTimeout, FuelResult.bind])
  · rcases bodySafe value valuePost with bodyTimeout |
      ⟨result, bodySuccess, resultPost⟩
    · exact .inl (by
        simp [evalFuel, valueSuccess, bodyTimeout, FuelResult.bind])
    · exact .inr ⟨result, by
        simp [evalFuel, valueSuccess, bodySuccess, FuelResult.bind], resultPost⟩

/-- A successful variable lookup retains any concrete value postcondition. -/
theorem evalFuel_var_resultSafeWith
    (found : environment[index]? = some value)
    (valueSafe : predicate value) :
    ∀ fuel,
      FuelResultSafeWith predicate (evalFuel fuel environment (.var index))
  | 0 => .inl rfl
  | fuel + 1 => .inr ⟨value, by simp [evalFuel, found], valueSafe⟩

/-- Predicate-parameterized binary tuple construction. -/
theorem evalFuel_tuplePair_resultSafeWith
    (firstSafe : FuelResultSafeWith firstPredicate
      (evalFuel fuel environment firstExpression))
    (secondSafe : FuelResultSafeWith secondPredicate
      (evalFuel fuel environment secondExpression)) :
    PairResultSafeWith firstPredicate secondPredicate
      (evalFuel (fuel + 1) environment
        (.tuple [firstExpression, secondExpression])) := by
  rcases firstSafe with firstTimeout | ⟨first, firstSuccess, firstPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, firstTimeout, FuelResult.map])
  · rcases secondSafe with secondTimeout |
      ⟨second, secondSuccess, secondPost⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, firstSuccess, secondTimeout,
          FuelResult.bind, FuelResult.map])
    · exact .inr ⟨.tuple [first, second], by
        simp [evalFuel, FuelResult.traverse, firstSuccess, secondSuccess,
          FuelResult.bind, FuelResult.map],
        ⟨first, second, rfl, firstPost, secondPost⟩⟩

/-- Pair construction retains the exact two fields and their all-index
certificates. -/
theorem evalFuel_tuplePair_allFuelSafe
    (firstSafe : AllFuelResultSafe firstType
      (evalFuel fuel environment firstExpression))
    (secondSafe : AllFuelResultSafe secondType
      (evalFuel fuel environment secondExpression)) :
    AllFuelPairResultSafe firstType secondType
      (evalFuel (fuel + 1) environment
        (.tuple [firstExpression, secondExpression])) := by
  rcases firstSafe with firstTimeout | ⟨first, firstSuccess, firstPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, firstTimeout, FuelResult.map])
  · rcases secondSafe with secondTimeout |
      ⟨second, secondSuccess, secondPost⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, firstSuccess, secondTimeout,
          FuelResult.bind, FuelResult.map])
    · exact .inr ⟨.tuple [first, second], by
        simp [evalFuel, FuelResult.traverse, firstSuccess, secondSuccess,
          FuelResult.bind, FuelResult.map],
        ⟨first, second, rfl, firstPost, secondPost⟩⟩

/-- The empty constructor produces a canonical all-index-safe List. -/
theorem evalFuel_listNil_allFuelSafe (fuel : Nat) :
    AllFuelListResultSafe element
      (evalFuel (fuel + 1) environment (.ctor DataCtor.nil [])) := by
  exact .inr ⟨Value.nilValue, by
    simp [evalFuel, FuelResult.traverse, FuelResult.map, Value.nilValue],
    ⟨[], rfl, by simp⟩⟩

/-- Predicate-parameterized empty List construction. -/
theorem evalFuel_listNil_resultSafeWith (fuel : Nat) :
    ListResultSafeWith predicate
      (evalFuel (fuel + 1) environment (.ctor DataCtor.nil [])) := by
  exact .inr ⟨Value.nilValue, by
    simp [evalFuel, FuelResult.traverse, FuelResult.map, Value.nilValue],
    ⟨[], rfl, by simp⟩⟩

/-- List construction retains the head certificate and the tail's canonical
member certificates. -/
theorem evalFuel_listCons_allFuelSafe
    (headSafe : AllFuelResultSafe element
      (evalFuel fuel environment headExpression))
    (tailSafe : AllFuelListResultSafe element
      (evalFuel fuel environment tailExpression)) :
    AllFuelListResultSafe element
      (evalFuel (fuel + 1) environment
        (.ctor DataCtor.cons [headExpression, tailExpression])) := by
  rcases headSafe with headTimeout | ⟨head, headSuccess, headPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, headTimeout, FuelResult.map])
  · rcases tailSafe with tailTimeout |
      ⟨tail, tailSuccess, tailPost⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, headSuccess, tailTimeout,
          FuelResult.bind, FuelResult.map])
    · obtain ⟨items, rfl, itemsSafe⟩ := tailPost
      exact .inr ⟨Value.buildList (head :: items), by
        simp [evalFuel, FuelResult.traverse, headSuccess, tailSuccess,
          FuelResult.bind, FuelResult.map, Value.buildList, Value.consValue],
        ⟨head :: items, rfl, by
          intro item member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact headPost
          · exact itemsSafe item member⟩⟩

/-- Predicate-parameterized List construction. -/
theorem evalFuel_listCons_resultSafeWith
    (headSafe : FuelResultSafeWith predicate
      (evalFuel fuel environment headExpression))
    (tailSafe : ListResultSafeWith predicate
      (evalFuel fuel environment tailExpression)) :
    ListResultSafeWith predicate
      (evalFuel (fuel + 1) environment
        (.ctor DataCtor.cons [headExpression, tailExpression])) := by
  rcases headSafe with headTimeout | ⟨head, headSuccess, headPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, headTimeout, FuelResult.map])
  · rcases tailSafe with tailTimeout |
      ⟨tail, tailSuccess, tailPost⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, headSuccess, tailTimeout,
          FuelResult.bind, FuelResult.map])
    · obtain ⟨items, rfl, itemsSafe⟩ := tailPost
      exact .inr ⟨Value.buildList (head :: items), by
        simp [evalFuel, FuelResult.traverse, headSuccess, tailSuccess,
          FuelResult.bind, FuelResult.map, Value.buildList, Value.consValue],
        ⟨head :: items, rfl, by
          intro item member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact headPost
          · exact itemsSafe item member⟩⟩

/-- First projection is safe for the exact pair value returned by its child. -/
theorem evalFuel_pairFirst_allFuelSafe
    (pairSafe : AllFuelPairResultSafe firstType secondType
      (evalFuel fuel environment pairExpression)) :
    AllFuelResultSafe firstType
      (evalFuel (fuel + 1) environment
        (.prim PrimOp.pairFirst [pairExpression])) := by
  rcases pairSafe with pairTimeout | ⟨pair, pairSuccess, pairPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, pairTimeout, FuelResult.bind])
  · obtain ⟨first, second, rfl, firstPost, secondPost⟩ := pairPost
    exact .inr ⟨first, by
      simp [evalFuel, FuelResult.traverse, pairSuccess, evalPrimitive,
        FuelResult.bind], firstPost⟩

/-- Second projection is safe for the exact pair value returned by its child. -/
theorem evalFuel_pairSecond_allFuelSafe
    (pairSafe : AllFuelPairResultSafe firstType secondType
      (evalFuel fuel environment pairExpression)) :
    AllFuelResultSafe secondType
      (evalFuel (fuel + 1) environment
        (.prim PrimOp.pairSecond [pairExpression])) := by
  rcases pairSafe with pairTimeout | ⟨pair, pairSuccess, pairPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, pairTimeout, FuelResult.bind])
  · obtain ⟨first, second, rfl, firstPost, secondPost⟩ := pairPost
    exact .inr ⟨second, by
      simp [evalFuel, FuelResult.traverse, pairSuccess, evalPrimitive,
        FuelResult.bind], secondPost⟩

/-- Predicate-parameterized first projection. -/
theorem evalFuel_pairFirst_resultSafeWith
    (pairSafe : PairResultSafeWith firstPredicate secondPredicate
      (evalFuel fuel environment pairExpression)) :
    FuelResultSafeWith firstPredicate
      (evalFuel (fuel + 1) environment
        (.prim PrimOp.pairFirst [pairExpression])) := by
  rcases pairSafe with pairTimeout | ⟨pair, pairSuccess, pairPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, pairTimeout, FuelResult.bind])
  · obtain ⟨first, second, rfl, firstPost, secondPost⟩ := pairPost
    exact .inr ⟨first, by
      simp [evalFuel, FuelResult.traverse, pairSuccess, evalPrimitive,
        FuelResult.bind], firstPost⟩

/-- Predicate-parameterized second projection. -/
theorem evalFuel_pairSecond_resultSafeWith
    (pairSafe : PairResultSafeWith firstPredicate secondPredicate
      (evalFuel fuel environment pairExpression)) :
    FuelResultSafeWith secondPredicate
      (evalFuel (fuel + 1) environment
        (.prim PrimOp.pairSecond [pairExpression])) := by
  rcases pairSafe with pairTimeout | ⟨pair, pairSuccess, pairPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, pairTimeout, FuelResult.bind])
  · obtain ⟨first, second, rfl, firstPost, secondPost⟩ := pairPost
    exact .inr ⟨second, by
      simp [evalFuel, FuelResult.traverse, pairSuccess, evalPrimitive,
        FuelResult.bind], secondPost⟩

/-- Concatenation preserves canonical List members and their all-index
certificates. -/
theorem evalFuel_append_allFuelSafe
    (leftSafe : AllFuelListResultSafe element
      (evalFuel fuel environment leftExpression))
    (rightSafe : AllFuelListResultSafe element
      (evalFuel fuel environment rightExpression)) :
    AllFuelListResultSafe element
      (evalFuel (fuel + 1) environment
        (.prim PrimOp.append [leftExpression, rightExpression])) := by
  rcases leftSafe with leftTimeout | ⟨left, leftSuccess, leftPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, leftTimeout, FuelResult.bind])
  · rcases rightSafe with rightTimeout | ⟨right, rightSuccess, rightPost⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, leftSuccess, rightTimeout,
          FuelResult.bind])
    · obtain ⟨leftItems, rfl, leftItemsSafe⟩ := leftPost
      obtain ⟨rightItems, rfl, rightItemsSafe⟩ := rightPost
      exact .inr ⟨Value.buildList (leftItems ++ rightItems), by
        simp [evalFuel, FuelResult.traverse, leftSuccess, rightSuccess,
          evalPrimitive, FuelResult.bind],
        ⟨leftItems ++ rightItems, rfl, by
          intro item member
          rcases List.mem_append.mp member with member | member
          · exact leftItemsSafe item member
          · exact rightItemsSafe item member⟩⟩

/-- Predicate-parameterized concatenation rule. -/
theorem evalFuel_append_resultSafeWith
    (leftSafe : ListResultSafeWith predicate
      (evalFuel fuel environment leftExpression))
    (rightSafe : ListResultSafeWith predicate
      (evalFuel fuel environment rightExpression)) :
    ListResultSafeWith predicate
      (evalFuel (fuel + 1) environment
        (.prim PrimOp.append [leftExpression, rightExpression])) := by
  rcases leftSafe with leftTimeout | ⟨left, leftSuccess, leftPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, leftTimeout, FuelResult.bind])
  · rcases rightSafe with rightTimeout | ⟨right, rightSuccess, rightPost⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, leftSuccess, rightTimeout,
          FuelResult.bind])
    · obtain ⟨leftItems, rfl, leftItemsSafe⟩ := leftPost
      obtain ⟨rightItems, rfl, rightItemsSafe⟩ := rightPost
      exact .inr ⟨Value.buildList (leftItems ++ rightItems), by
        simp [evalFuel, FuelResult.traverse, leftSuccess, rightSuccess,
          evalPrimitive, FuelResult.bind],
        ⟨leftItems ++ rightItems, rfl, by
          intro item member
          rcases List.mem_append.mp member with member | member
          · exact leftItemsSafe item member
          · exact rightItemsSafe item member⟩⟩

private theorem traverseAllFuelFunction
    (functionSafe : AllFuelFunctionSafe function domain codomain)
    (itemsSafe : ∀ item ∈ items, AllFuelValueSafe item domain) :
    FuelResultSafeWith
      (fun outputs => ∀ output ∈ outputs, AllFuelValueSafe output codomain)
      (FuelResult.traverse (applyFuel fuel function) items) := by
  induction items with
  | nil => exact .inr ⟨[], rfl, by simp⟩
  | cons item items induction =>
      rcases functionSafe fuel item (itemsSafe item (by simp)) with
        itemTimeout | ⟨output, itemSuccess, outputSafe⟩
      · exact .inl (by simp [FuelResult.traverse, itemTimeout])
      · have tailItemsSafe : ∀ candidate ∈ items,
          AllFuelValueSafe candidate domain := by
          intro candidate member
          exact itemsSafe candidate (by simp [member])
        rcases induction tailItemsSafe with tailTimeout |
          ⟨outputs, tailSuccess, outputsSafe⟩
        · exact .inl (by
            simp [FuelResult.traverse, itemSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨output :: outputs, by
            simp [FuelResult.traverse, itemSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact outputSafe
            · exact outputsSafe candidate member⟩

private theorem traverseFunctionSafeWith
    (functionSafe : FunctionSafeWith argumentPredicate resultPredicate function)
    (itemsSafe : ∀ item ∈ items, argumentPredicate item) :
    FuelResultSafeWith
      (fun outputs => ∀ output ∈ outputs, resultPredicate output)
      (FuelResult.traverse (applyFuel fuel function) items) := by
  induction items with
  | nil => exact .inr ⟨[], rfl, by simp⟩
  | cons item items induction =>
      rcases functionSafe fuel item (itemsSafe item (by simp)) with
        itemTimeout | ⟨output, itemSuccess, outputSafe⟩
      · exact .inl (by simp [FuelResult.traverse, itemTimeout])
      · have tailItemsSafe : ∀ candidate ∈ items,
          argumentPredicate candidate := by
          intro candidate member
          exact itemsSafe candidate (by simp [member])
        rcases induction tailItemsSafe with tailTimeout |
          ⟨outputs, tailSuccess, outputsSafe⟩
        · exact .inl (by
            simp [FuelResult.traverse, itemSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨output :: outputs, by
            simp [FuelResult.traverse, itemSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact outputSafe
            · exact outputsSafe candidate member⟩

/-- Predicate-parameterized `map` rule. -/
theorem evalFuel_map_resultSafeWith
    (functionSafe : FunctionResultSafeWith argumentPredicate resultPredicate
      (evalFuel fuel environment functionExpression))
    (inputSafe : ListResultSafeWith argumentPredicate
      (evalFuel fuel environment inputExpression)) :
    ListResultSafeWith resultPredicate
      (evalFuel (fuel + 1) environment
        (.prim PrimOp.map [functionExpression, inputExpression])) := by
  rcases functionSafe with functionTimeout |
    ⟨function, functionSuccess, functionPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, functionTimeout, FuelResult.bind])
  · rcases inputSafe with inputTimeout | ⟨input, inputSuccess, inputPost⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, functionSuccess, inputTimeout,
          FuelResult.bind])
    · obtain ⟨items, rfl, itemsSafe⟩ := inputPost
      rcases traverseFunctionSafeWith (fuel := fuel) functionPost itemsSafe with
        mapTimeout | ⟨outputs, mapSuccess, outputsSafe⟩
      · exact .inl (by
          simp [evalFuel, FuelResult.traverse, functionSuccess, inputSuccess,
            evalPrimitive, mapTimeout, FuelResult.bind, FuelResult.map])
      · exact .inr ⟨Value.buildList outputs, by
          simp [evalFuel, FuelResult.traverse, functionSuccess, inputSuccess,
            evalPrimitive, mapSuccess, FuelResult.bind, FuelResult.map],
          ⟨outputs, rfl, outputsSafe⟩⟩

/-- `map` uses only the concrete function returned by its first child and
the canonical members returned by its second child. -/
theorem evalFuel_map_allFuelSafe
    (functionSafe : AllFuelFunctionResultSafe domain codomain
      (evalFuel fuel environment functionExpression))
    (inputSafe : AllFuelListResultSafe domain
      (evalFuel fuel environment inputExpression)) :
    AllFuelListResultSafe codomain
      (evalFuel (fuel + 1) environment
        (.prim PrimOp.map [functionExpression, inputExpression])) := by
  rcases functionSafe with functionTimeout |
    ⟨function, functionSuccess, functionPost⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, functionTimeout, FuelResult.bind])
  · rcases inputSafe with inputTimeout | ⟨input, inputSuccess, inputPost⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, functionSuccess, inputTimeout,
          FuelResult.bind])
    · obtain ⟨items, rfl, itemsSafe⟩ := inputPost
      rcases traverseAllFuelFunction (fuel := fuel) functionPost itemsSafe with
        mapTimeout | ⟨outputs, mapSuccess, outputsSafe⟩
      · exact .inl (by
          simp [evalFuel, FuelResult.traverse, functionSuccess, inputSuccess,
            evalPrimitive, mapTimeout, FuelResult.bind, FuelResult.map])
      · exact .inr ⟨Value.buildList outputs, by
          simp [evalFuel, FuelResult.traverse, functionSuccess, inputSuccess,
            evalPrimitive, mapSuccess, FuelResult.bind, FuelResult.map],
          ⟨outputs, rfl, outputsSafe⟩⟩

/-! ## All-evaluation-fuel wrappers -/

theorem evalFuel_tuplePair_resultSafeWith_all
    (firstSafe : ∀ fuel, FuelResultSafeWith firstPredicate
      (evalFuel fuel environment firstExpression))
    (secondSafe : ∀ fuel, FuelResultSafeWith secondPredicate
      (evalFuel fuel environment secondExpression)) :
    ∀ fuel, PairResultSafeWith firstPredicate secondPredicate
      (evalFuel fuel environment
        (.tuple [firstExpression, secondExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_tuplePair_resultSafeWith
      (firstSafe fuel) (secondSafe fuel)

theorem evalFuel_tuplePair_allFuelSafe_all
    (firstSafe : ∀ fuel, AllFuelResultSafe firstType
      (evalFuel fuel environment firstExpression))
    (secondSafe : ∀ fuel, AllFuelResultSafe secondType
      (evalFuel fuel environment secondExpression)) :
    ∀ fuel, AllFuelPairResultSafe firstType secondType
      (evalFuel fuel environment
        (.tuple [firstExpression, secondExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_tuplePair_allFuelSafe
      (firstSafe fuel) (secondSafe fuel)

theorem evalFuel_listNil_allFuelSafe_all :
    ∀ fuel, AllFuelListResultSafe element
      (evalFuel fuel environment (.ctor DataCtor.nil []))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_listNil_allFuelSafe fuel

theorem evalFuel_listNil_resultSafeWith_all :
    ∀ fuel, ListResultSafeWith predicate
      (evalFuel fuel environment (.ctor DataCtor.nil []))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_listNil_resultSafeWith fuel

theorem evalFuel_listCons_allFuelSafe_all
    (headSafe : ∀ fuel, AllFuelResultSafe element
      (evalFuel fuel environment headExpression))
    (tailSafe : ∀ fuel, AllFuelListResultSafe element
      (evalFuel fuel environment tailExpression)) :
    ∀ fuel, AllFuelListResultSafe element
      (evalFuel fuel environment
        (.ctor DataCtor.cons [headExpression, tailExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_listCons_allFuelSafe
      (headSafe fuel) (tailSafe fuel)

theorem evalFuel_listCons_resultSafeWith_all
    (headSafe : ∀ fuel, FuelResultSafeWith predicate
      (evalFuel fuel environment headExpression))
    (tailSafe : ∀ fuel, ListResultSafeWith predicate
      (evalFuel fuel environment tailExpression)) :
    ∀ fuel, ListResultSafeWith predicate
      (evalFuel fuel environment
        (.ctor DataCtor.cons [headExpression, tailExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_listCons_resultSafeWith
      (headSafe fuel) (tailSafe fuel)

theorem evalFuel_pairFirst_allFuelSafe_all
    (pairSafe : ∀ fuel, AllFuelPairResultSafe firstType secondType
      (evalFuel fuel environment pairExpression)) :
    ∀ fuel, AllFuelResultSafe firstType
      (evalFuel fuel environment (.prim PrimOp.pairFirst [pairExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_pairFirst_allFuelSafe (pairSafe fuel)

theorem evalFuel_pairSecond_allFuelSafe_all
    (pairSafe : ∀ fuel, AllFuelPairResultSafe firstType secondType
      (evalFuel fuel environment pairExpression)) :
    ∀ fuel, AllFuelResultSafe secondType
      (evalFuel fuel environment (.prim PrimOp.pairSecond [pairExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_pairSecond_allFuelSafe (pairSafe fuel)

theorem evalFuel_pairFirst_resultSafeWith_all
    (pairSafe : ∀ fuel,
      PairResultSafeWith firstPredicate secondPredicate
        (evalFuel fuel environment pairExpression)) :
    ∀ fuel, FuelResultSafeWith firstPredicate
      (evalFuel fuel environment (.prim PrimOp.pairFirst [pairExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_pairFirst_resultSafeWith (pairSafe fuel)

theorem evalFuel_pairSecond_resultSafeWith_all
    (pairSafe : ∀ fuel,
      PairResultSafeWith firstPredicate secondPredicate
        (evalFuel fuel environment pairExpression)) :
    ∀ fuel, FuelResultSafeWith secondPredicate
      (evalFuel fuel environment (.prim PrimOp.pairSecond [pairExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_pairSecond_resultSafeWith (pairSafe fuel)

theorem evalFuel_append_allFuelSafe_all
    (leftSafe : ∀ fuel, AllFuelListResultSafe element
      (evalFuel fuel environment leftExpression))
    (rightSafe : ∀ fuel, AllFuelListResultSafe element
      (evalFuel fuel environment rightExpression)) :
    ∀ fuel, AllFuelListResultSafe element
      (evalFuel fuel environment
        (.prim PrimOp.append [leftExpression, rightExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_append_allFuelSafe
      (leftSafe fuel) (rightSafe fuel)

theorem evalFuel_map_allFuelSafe_all
    (functionSafe : ∀ fuel, AllFuelFunctionResultSafe domain codomain
      (evalFuel fuel environment functionExpression))
    (inputSafe : ∀ fuel, AllFuelListResultSafe domain
      (evalFuel fuel environment inputExpression)) :
    ∀ fuel, AllFuelListResultSafe codomain
      (evalFuel fuel environment
        (.prim PrimOp.map [functionExpression, inputExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_map_allFuelSafe
      (functionSafe fuel) (inputSafe fuel)

theorem evalFuel_append_resultSafeWith_all
    (leftSafe : ∀ fuel, ListResultSafeWith predicate
      (evalFuel fuel environment leftExpression))
    (rightSafe : ∀ fuel, ListResultSafeWith predicate
      (evalFuel fuel environment rightExpression)) :
    ∀ fuel, ListResultSafeWith predicate
      (evalFuel fuel environment
        (.prim PrimOp.append [leftExpression, rightExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_append_resultSafeWith
      (leftSafe fuel) (rightSafe fuel)

theorem evalFuel_map_resultSafeWith_all
    (functionSafe : ∀ fuel,
      FunctionResultSafeWith argumentPredicate resultPredicate
        (evalFuel fuel environment functionExpression))
    (inputSafe : ∀ fuel, ListResultSafeWith argumentPredicate
      (evalFuel fuel environment inputExpression)) :
    ∀ fuel, ListResultSafeWith resultPredicate
      (evalFuel fuel environment
        (.prim PrimOp.map [functionExpression, inputExpression]))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_map_resultSafeWith
      (functionSafe fuel) (inputSafe fuel)

theorem evalFuel_letE_resultSafeWith_all
    (valueSafe : ∀ fuel,
      FuelResultSafeWith boundPredicate
        (evalFuel fuel environment valueExpression))
    (bodySafe : ∀ fuel value, boundPredicate value →
      FuelResultSafeWith bodyPredicate
        (evalFuel fuel (value :: environment) bodyExpression)) :
    ∀ fuel, FuelResultSafeWith bodyPredicate
      (evalFuel fuel environment (.letE valueExpression bodyExpression))
  | 0 => .inl rfl
  | fuel + 1 => evalFuel_letE_resultSafeWith
      (valueSafe fuel) (bodySafe fuel)

/-! ## Value-indexed `matchAll` with a stable body postcondition -/

/-- A concrete postcondition for every body evaluation selected by a typed
binding group. -/
def EvaluatedBindingBodySafeWith
    (fuel : Nat) (environment : ValueEnvironment)
    (bindingTypes : List Ty) (bodyExpression : Source.Expr)
    (predicate : Value → Prop) : Prop :=
  ∀ bindings,
    TotalPlainValueTypings bindings bindingTypes →
      FuelResultSafeWith predicate
        (evalFuel fuel (bindings ++ environment) bodyExpression)

private theorem traverseEvaluatedBodiesSafeWith
    (answersTyped : TotalPlainMatchingAnswersTyping answers bindingTypes)
    (bodySafe : EvaluatedBindingBodySafeWith fuel environment bindingTypes
      bodyExpression predicate) :
    FuelResultSafeWith
      (fun values => ∀ value ∈ values, predicate value)
      (FuelResult.traverse
        (fun bindings => evalFuel fuel (bindings ++ environment) bodyExpression)
        answers) := by
  induction answers with
  | nil => exact .inr ⟨[], rfl, by simp⟩
  | cons bindings answers induction =>
      have bindingsTyped := answersTyped bindings (by simp)
      have tailTyped : TotalPlainMatchingAnswersTyping answers bindingTypes := by
        intro candidate member
        exact answersTyped candidate (by simp [member])
      rcases bodySafe bindings bindingsTyped with bodyTimeout |
        ⟨value, bodySuccess, valuePost⟩
      · exact .inl (by simp [FuelResult.traverse, bodyTimeout])
      · rcases induction tailTyped with tailTimeout |
          ⟨values, tailSuccess, valuesPost⟩
        · exact .inl (by
            simp [FuelResult.traverse, bodySuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨value :: values, by
            simp [FuelResult.traverse, bodySuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact valuePost
            · exact valuesPost candidate member⟩

/-- The value-indexed `matchAll` rule with an arbitrary concrete
postcondition on each returned body value. -/
theorem matchAllFuel_valueIndexedListSafeWith
    (targetSafe : FuelResultSafe fuel matcherTarget
      (evalFuel fuel environment targetExpression))
    (matcherSafe : FuelResultSafe fuel (.matcher capability matcherTarget)
      (evalFuel fuel environment matcherExpression))
    (searchSafe : EvaluatedPatternSearchSafe fuel environment
      targetExpression matcherExpression pattern bindingTypes)
    (bodySafe : EvaluatedBindingBodySafeWith fuel environment bindingTypes
      bodyExpression predicate) :
    ListResultSafeWith predicate
      (evalFuel (fuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern bodyExpression)) := by
  rcases targetSafe with targetTimeout |
    ⟨targetValue, targetSuccess, targetValueSafe⟩
  · exact .inl (by
      simp [evalFuel, targetTimeout, FuelResult.bind])
  · rcases matcherSafe with matcherTimeout |
      ⟨matcherValue, matcherSuccess, matcherValueSafe⟩
    · exact .inl (by
        simp [evalFuel, targetSuccess, matcherTimeout, FuelResult.bind])
    · rcases searchSafe targetValue matcherValue targetSuccess matcherSuccess with
        searchTimeout | ⟨answers, searchSuccess, answersTyped⟩
      · exact .inl (by
          simp [evalFuel, targetSuccess, matcherSuccess, searchTimeout,
            FuelResult.bind])
      · rcases traverseEvaluatedBodiesSafeWith answersTyped bodySafe with
          bodiesTimeout | ⟨values, bodiesSuccess, valuesPost⟩
        · exact .inl (by
            simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
              bodiesTimeout, FuelResult.bind, FuelResult.map])
        · exact .inr ⟨Value.buildList values, by
            simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
              bodiesSuccess, FuelResult.bind, FuelResult.map],
            ⟨values, rfl, valuesPost⟩⟩

/-- Stable first-order specialization of the preceding rule. -/
theorem matchAllFuel_valueIndexedAllFuelSafe
    (targetSafe : FuelResultSafe fuel matcherTarget
      (evalFuel fuel environment targetExpression))
    (matcherSafe : FuelResultSafe fuel (.matcher capability matcherTarget)
      (evalFuel fuel environment matcherExpression))
    (searchSafe : EvaluatedPatternSearchSafe fuel environment
      targetExpression matcherExpression pattern bindingTypes)
    (bodySafe : EvaluatedBindingBodySafeWith fuel environment bindingTypes
      bodyExpression (fun value => AllFuelValueSafe value bodyTarget)) :
    AllFuelListResultSafe bodyTarget
      (evalFuel (fuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern bodyExpression)) :=
  matchAllFuel_valueIndexedListSafeWith targetSafe matcherSafe searchSafe bodySafe

end TypePM.Runtime
