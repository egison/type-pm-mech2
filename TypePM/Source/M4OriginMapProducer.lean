import TypePM.Source.M4OriginPlainFixProducer
import TypePM.ValueIndexedStableFirstOrderSafety

/-!
# Origin-demand producer for primitive map

The callback and every mapped element use the same operational fuel selected
by the surrounding `map` evaluation.  Argument and result observations remain
independent finite `OriginDemand` trees.  A companion all-call theorem adapts
the stronger callback premise expected by the existing predicate-parametric
`evalFuel_map_resultSafeWith` rule.
-/

namespace TypePM.Runtime

namespace ListOfValueSafe

/-- Forget only the inductive wrapper of a structural list observation. -/
theorem toListValueSafeWith
    (safe : ListOfValueSafe
      (fun value target => OriginValueSafe elementDemand value target)
      value (DataTypes.list elementType)) :
    ListValueSafeWith
      (fun item => OriginValueSafe elementDemand item elementType) value := by
  generalize targetEq : DataTypes.list elementType = target at safe
  induction safe with
  | @nil storedElementType =>
      cases targetEq
      exact ⟨[], rfl, by simp⟩
  | @cons headValue storedElementType tailValues head tail tailIH =>
      cases targetEq
      obtain ⟨tailItems, tailEq, tailItemsSafe⟩ := tailIH rfl
      have tailItemsEq : tailItems = tailValues := by
        have viewed := congrArg Value.viewList tailEq
        symm
        simpa using viewed
      subst tailItems
      exact ⟨headValue :: tailValues, rfl, by
        intro item member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact head
        · exact tailItemsSafe item member⟩

end ListOfValueSafe

/-- Rebuild the structural list observation from the predicate form returned
by the generic map rule. -/
theorem originValueSafe_listOf_of_listValueSafeWith
    (safe : ListValueSafeWith
      (fun item => OriginValueSafe elementDemand item elementType) value) :
    OriginValueSafe (.listOf elementDemand) value
      (DataTypes.list elementType) := by
  obtain ⟨items, rfl, itemsSafe⟩ := safe
  induction items with
  | nil => exact OriginValueSafe.listNil
  | cons head tail induction =>
      exact OriginValueSafe.listCons
        (itemsSafe head (by simp))
        (induction (by
          intro item member
          exact itemsSafe item (by simp [member])))

/-- Convert a structural list-result observation to the predicate interface
used by `evalFuel_map_resultSafeWith`. -/
theorem OriginResultSafe.toListResultSafeWith
    (safe : OriginResultSafe (.listOf elementDemand)
      (DataTypes.list elementType) result) :
    ListResultSafeWith
      (fun item => OriginValueSafe elementDemand item elementType) result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have unfolded : ListOfValueSafe
        (fun item target => OriginValueSafe elementDemand item target)
        value (DataTypes.list elementType) := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, unfolded.toListValueSafeWith⟩

/-- Convert the generic predicate result of map back to one structural list
observation. -/
theorem originResultSafe_listOf_of_listResultSafeWith
    (safe : ListResultSafeWith
      (fun item => OriginValueSafe elementDemand item elementType) result) :
    OriginResultSafe (.listOf elementDemand)
      (DataTypes.list elementType) result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success,
      originValueSafe_listOf_of_listValueSafeWith valueSafe⟩

/-- Strong adapter for the existing generic map theorem.  The child
evaluation returns one function that supports the same input/output demands
at every callback fuel. -/
def OriginFunctionResultSafeAllCalls
    (argumentDemand resultDemand : OriginDemand)
    (domain codomain : Ty) (result : FuelResult Value) : Prop :=
  FuelResultSafeWith
    (fun function => ∀ callbackFuel,
      OriginValueSafe
        (.plainCall callbackFuel argumentDemand resultDemand)
        function (.fn domain codomain))
    result

/-- Direct reuse of `evalFuel_map_resultSafeWith` for callbacks certified at
every operational fuel. -/
theorem evalFuel_map_originResultSafe_allCalls
    (functionSafe : OriginFunctionResultSafeAllCalls argumentDemand
      resultDemand domain codomain
      (evalFuel childFuel environment functionExpression))
    (inputSafe : OriginResultSafe (.listOf argumentDemand)
      (DataTypes.list domain)
      (evalFuel childFuel environment inputExpression)) :
    OriginResultSafe (.listOf resultDemand) (DataTypes.list codomain)
      (evalFuel (childFuel + 1) environment
        (.prim PrimOp.map [functionExpression, inputExpression])) := by
  have functionPredicateSafe : FunctionResultSafeWith
      (fun argument => OriginValueSafe argumentDemand argument domain)
      (fun result => OriginValueSafe resultDemand result codomain)
      (evalFuel childFuel environment functionExpression) := by
    rcases functionSafe with timeout | ⟨function, success, allCalls⟩
    · exact .inl timeout
    · exact .inr ⟨function, success, by
        intro callbackFuel argument argumentSafe
        change OriginResultSafe resultDemand codomain
          (applyFuel callbackFuel function argument)
        exact OriginValueSafe.apply (allCalls callbackFuel) argumentSafe⟩
  exact originResultSafe_listOf_of_listResultSafeWith
    (evalFuel_map_resultSafeWith functionPredicateSafe
      inputSafe.toListResultSafeWith)

private theorem traverse_originCallSafe
    (functionSafe : OriginValueSafe
      (.plainCall callbackFuel argumentDemand resultDemand)
      function (.fn domain codomain))
    (itemsSafe : ∀ item ∈ items,
      OriginValueSafe argumentDemand item domain) :
    FuelResultSafeWith
      (fun outputs => ∀ output ∈ outputs,
        OriginValueSafe resultDemand output codomain)
      (FuelResult.traverse (applyFuel callbackFuel function) items) := by
  induction items with
  | nil => exact .inr ⟨[], rfl, by simp⟩
  | cons item items induction =>
      rcases OriginValueSafe.apply functionSafe
          (itemsSafe item (by simp)) with
        headTimeout | ⟨output, headSuccess, outputSafe⟩
      · exact .inl (by
          simp [FuelResult.traverse, headTimeout])
      · rcases induction (by
            intro candidate member
            exact itemsSafe candidate (by simp [member])) with
          tailTimeout | ⟨outputs, tailSuccess, outputsSafe⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨output :: outputs, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact outputSafe
            · exact outputsSafe candidate member⟩

/-- Exact common-fuel producer used by primitive map.  Only the callback call
at `childFuel` is required; no stronger all-fuel function premise is hidden. -/
theorem evalFuel_map_originResultSafe
    (functionSafe : OriginResultSafe
      (.plainCall childFuel argumentDemand resultDemand)
      (.fn domain codomain)
      (evalFuel childFuel environment functionExpression))
    (inputSafe : OriginResultSafe (.listOf argumentDemand)
      (DataTypes.list domain)
      (evalFuel childFuel environment inputExpression)) :
    OriginResultSafe (.listOf resultDemand) (DataTypes.list codomain)
      (evalFuel (childFuel + 1) environment
        (.prim PrimOp.map [functionExpression, inputExpression])) := by
  rcases functionSafe with functionTimeout |
    ⟨function, functionSuccess, functionValueSafe⟩
  · exact .inl (by
      simp [evalFuel, FuelResult.traverse, functionTimeout, FuelResult.bind])
  · rcases inputSafe with inputTimeout |
      ⟨input, inputSuccess, inputValueSafe⟩
    · exact .inl (by
        simp [evalFuel, FuelResult.traverse, functionSuccess, inputTimeout,
          FuelResult.bind])
    · have inputListSafe : ListValueSafeWith
          (fun item => OriginValueSafe argumentDemand item domain) input := by
        have unfolded : ListOfValueSafe
            (fun item target => OriginValueSafe argumentDemand item target)
            input (DataTypes.list domain) := by
          simpa only [OriginValueSafe] using inputValueSafe
        exact unfolded.toListValueSafeWith
      obtain ⟨items, rfl, itemsSafe⟩ := inputListSafe
      rcases traverse_originCallSafe functionValueSafe itemsSafe with
        mapTimeout | ⟨outputs, mapSuccess, outputsSafe⟩
      · exact .inl (by
          simp [evalFuel, FuelResult.traverse, functionSuccess, inputSuccess,
            evalPrimitive, mapTimeout, FuelResult.bind, FuelResult.map])
      · exact .inr ⟨Value.buildList outputs, by
          simp [evalFuel, FuelResult.traverse, functionSuccess, inputSuccess,
            evalPrimitive, mapSuccess, FuelResult.bind, FuelResult.map],
          originValueSafe_listOf_of_listValueSafeWith
            ⟨outputs, rfl, outputsSafe⟩⟩

end TypePM.Runtime
