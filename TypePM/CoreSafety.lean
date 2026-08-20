import TypePM.RuntimeTyping

/-!
# Canonical core safety

For the certified canonical core, bounded evaluation has only two
outcomes: fuel exhaustion or a value of the source type.  This is stronger
than a bare no-`stuck` statement: the successful branch is a preservation
theorem, while the two constructors together are typed ready progress.
-/

namespace TypePM.Runtime

/-- A typed evaluation result is either ordinary fuel exhaustion or a
successfully produced value of the indicated type.  The definition records
the positive observations, rather than defining safety as inequality with
`stuck`. -/
def TypedResult (target : Ty) (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧ ValueTyping value target

/-- List-valued counterpart used by left-to-right tuple evaluation. -/
def TypedResults (targets : List Ty) (result : FuelResult (List Value)) : Prop :=
  result = .timeout ∨
    ∃ values, result = .ok values ∧ ValueTypings values targets

namespace TypedResult

/-- Typed ready progress, exposing the two possible evaluator observations. -/
theorem progress
    (typed : TypedResult target result) :
    result = .timeout ∨
      ∃ value, result = .ok value ∧ ValueTyping value target := by
  exact typed

/-- A typed result cannot be the runtime rule-coverage failure. -/
theorem notStuck (typed : TypedResult target result) : result.NotStuck := by
  rcases typed with timeout | ⟨value, success, _typing⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-- Combine two already proved expression results in the evaluator's
left-to-right traversal shape. -/
theorem pairTraverse
    (left : TypedResult leftTarget leftResult)
    (right : TypedResult rightTarget rightResult) :
    TypedResults [leftTarget, rightTarget]
      (FuelResult.bind leftResult fun leftValue =>
        FuelResult.map (leftValue :: ·)
          (FuelResult.bind rightResult fun rightValue =>
            FuelResult.map (rightValue :: ·) (.ok []))) := by
  rcases left with leftTimeout | ⟨leftValue, leftSuccess, leftTyping⟩
  · exact .inl (by simp [leftTimeout, FuelResult.bind])
  · rcases right with rightTimeout |
      ⟨rightValue, rightSuccess, rightTyping⟩
    · exact .inl (by
        simp [leftSuccess, rightTimeout, FuelResult.bind, FuelResult.map])
    · exact .inr ⟨[leftValue, rightValue], by
        simp [leftSuccess, rightSuccess, FuelResult.bind, FuelResult.map],
        .cons leftTyping (.cons rightTyping .nil)⟩

end TypedResult

namespace ListValueTypings

protected def apply
    (substitution : Subst) :
    (typing : ListValueTypings values element) →
      ListValueTypings values (element.apply substitution)
  | .nil => .nil
  | .cons head tail =>
      .cons (head.apply substitution) (tail.apply substitution)

end ListValueTypings

namespace CheckConversion

theorem source_apply_eq_of_int_target
    (conversion : CheckConversion conversionClass source target)
    (targetEq : target.apply substitution = .int) :
    source.apply substitution = .int := by
  cases conversion with
  | ordinary => exact targetEq
  | matcherToSlot => simp [Ty.apply] at targetEq
  | productMatcher => simp [Ty.apply] at targetEq
  | productMatcherToSlot => simp [Ty.apply] at targetEq

theorem source_apply_eq_of_data_target
    (conversion : CheckConversion conversionClass source target)
    (targetEq : target.apply substitution = .data former arguments) :
    source.apply substitution = .data former arguments := by
  cases conversion with
  | ordinary => exact targetEq
  | matcherToSlot => simp [Ty.apply] at targetEq
  | productMatcher => simp [Ty.apply] at targetEq
  | productMatcherToSlot => simp [Ty.apply] at targetEq

end CheckConversion

namespace ValueTyping

private structure CanonicalProperties
    (value : Value) (target : Ty) : Prop where
  intShape : ∀ substitution, target.apply substitution = .int →
    ∃ literal, value = .int literal
  boolShape : ∀ substitution,
    target.apply substitution = TypePM.DataTypes.bool →
      value = .data DataCtor.true [] ∨
        value = .data DataCtor.false []
  listShape : ∀ substitution element,
    target.apply substitution = TypePM.DataTypes.list element →
      ∃ values, value = Value.buildList values ∧
        ListValueTypings values element

private theorem canonicalProperties
    (typing : ValueTyping value target) :
    CanonicalProperties value target := by
  refine @ValueTyping.rec
    (motive_1 := fun value target _ => CanonicalProperties value target)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ typing
  · intro literal
    refine ⟨?_, ?_, ?_⟩
    · intro _ _
      exact ⟨literal, rfl⟩
    · intro _ equality
      simp [Ty.apply, TypePM.DataTypes.bool] at equality
    · intro _ _ equality
      simp [Ty.apply, TypePM.DataTypes.list] at equality
  · refine ⟨?_, ?_, ?_⟩
    · intro _ equality
      simp [Ty.apply, TypePM.DataTypes.bool] at equality
    · intro _ _
      exact .inl rfl
    · intro _ _ equality
      simp [Ty.apply, Ty.applyList, TypePM.DataTypes.bool,
        TypePM.DataTypes.list] at equality
  · refine ⟨?_, ?_, ?_⟩
    · intro _ equality
      simp [Ty.apply, TypePM.DataTypes.bool] at equality
    · intro _ _
      exact .inr rfl
    · intro _ _ equality
      simp [Ty.apply, Ty.applyList, TypePM.DataTypes.bool,
        TypePM.DataTypes.list] at equality
  · intro _values _targets _items _itemsIH
    refine ⟨?_, ?_, ?_⟩ <;> intros
    · simp [Ty.apply] at *
    · simp [Ty.apply, TypePM.DataTypes.bool] at *
    · simp [Ty.apply, TypePM.DataTypes.list] at *
  · intro values sourceElement items _itemsIH
    refine ⟨?_, ?_, ?_⟩
    · intro _ equality
      simp [Ty.apply, Ty.applyList, TypePM.DataTypes.list] at equality
    · intro _ equality
      simp [Ty.apply, Ty.applyList, TypePM.DataTypes.bool,
        TypePM.DataTypes.list] at equality
    · intro substitution element equality
      have elementEq : sourceElement.apply substitution = element := by
        simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.list] using equality
      refine ⟨values, rfl, ?_⟩
      rw [← elementEq]
      exact items.apply substitution
  · intro _value _sourceTarget _class _target source conversion sourceIH
    refine ⟨?_, ?_, ?_⟩
    · intro substitution equality
      exact sourceIH.intShape substitution
        (TypePM.Runtime.CheckConversion.source_apply_eq_of_int_target
          conversion equality)
    · intro substitution equality
      exact sourceIH.boolShape substitution
        (TypePM.Runtime.CheckConversion.source_apply_eq_of_data_target
          conversion equality)
    · intro substitution element equality
      exact sourceIH.listShape substitution element
        (TypePM.Runtime.CheckConversion.source_apply_eq_of_data_target
          conversion equality)
  · intro _value _sourceTarget source earlier sourceIH
    refine ⟨?_, ?_, ?_⟩
    · intro substitution equality
      exact sourceIH.intShape (Subst.compose substitution earlier) (by
        simpa only [Ty.apply_compose] using equality)
    · intro substitution equality
      exact sourceIH.boolShape (Subst.compose substitution earlier) (by
        simpa only [Ty.apply_compose] using equality)
    · intro substitution element equality
      exact sourceIH.listShape (Subst.compose substitution earlier) element (by
        simpa only [Ty.apply_compose] using equality)
  · trivial
  · intros
    trivial
  · intro
    trivial
  · intros
    trivial

/-- An integer-typed value has the evaluator's canonical integer shape. -/
theorem int_canonical
    (typing : ValueTyping value .int) :
    ∃ literal, value = .int literal := by
  exact (canonicalProperties typing).intShape Subst.id (by simp)

/-- A Boolean-typed value has one of the two canonical nullary data shapes.
This is the fact that rules out the evaluator's malformed-condition branch. -/
theorem bool_canonical
    (typing : ValueTyping value TypePM.DataTypes.bool) :
    value = .data DataCtor.true [] ∨
      value = .data DataCtor.false [] := by
  exact (canonicalProperties typing).boolShape Subst.id (by simp)

/-- A list-typed value is a canonical proper constructor encoding. -/
theorem list_canonical
    (typing : ValueTyping value (TypePM.DataTypes.list element)) :
    ∃ values, value = Value.buildList values ∧
      ListValueTypings values element := by
  exact (canonicalProperties typing).listShape Subst.id element (by simp)

theorem boolValue (value : Bool) :
    ValueTyping (Value.boolValue value) TypePM.DataTypes.bool := by
  cases value <;> simp [Value.boolValue]
  · exact .boolFalse
  · exact .boolTrue

end ValueTyping

namespace ListValueTypings

protected def append :
    (left : ListValueTypings leftValues element) →
    (right : ListValueTypings rightValues element) →
      ListValueTypings (leftValues ++ rightValues) element
  | .nil, right => right
  | .cons head tail, right => .cons head (tail.append right)

protected def deleteFirstStructural
    (needle : Value) :
    (typing : ListValueTypings values element) →
      ListValueTypings (Value.deleteFirstStructural needle values) element
  | .nil => .nil
  | .cons head tail => by
      simp only [Value.deleteFirstStructural]
      split
      · exact tail
      · exact .cons head (tail.deleteFirstStructural needle)

end ListValueTypings

/-- **Theorem 5.7, certified core.**  Expression evaluation preserves the
runtime type, and every fuel-bounded evaluation is ready: it either times out
or produces a typed value.  The certified constructors cover integers,
canonical Booleans and Lists, tuples, integer addition, `append`, `member`,
`deleteFirst`, and same-result-type conditionals. -/
theorem RuntimeTyping.coreSafety
    (typing : RuntimeTyping expression target)
    (fuel : Nat) (environment : ValueEnvironment) :
    TypedResult target (evalFuel fuel environment expression) := by
  apply RuntimeTyping.rec
    (motive_1 := fun expression target _ =>
      ∀ fuel environment, TypedResult target
        (evalFuel fuel environment expression))
    (motive_2 := fun expressions targets _ =>
      ∀ fuel environment, TypedResults targets
        (FuelResult.traverse (evalFuel fuel environment) expressions))
  case lit =>
          intro value fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .int _⟩
  case boolTrue =>
          intro fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .boolTrue⟩
  case boolFalse =>
          intro fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .boolFalse⟩
  case listNil =>
          intro element fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel =>
              exact .inr ⟨Value.buildList [], rfl, .list .nil⟩
  case listCons =>
          intro headExpression element tailExpression head tail headIH tailIH
            fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [headExpression, tailExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (headIH fuel environment)
              (tailIH fuel environment)
          rcases children with timeout | ⟨values, success, valuesTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
          · cases valuesTyping with
            | cons headTyping tailTyping =>
                cases tailTyping with
                | cons tailValueTyping nilTyping =>
                    cases nilTyping
                    obtain ⟨tailValues, tailEq, tailValuesTyping⟩ :=
                      tailValueTyping.list_canonical
                    subst tailEq
                    exact .inr ⟨Value.buildList (_ :: tailValues), by
                      simp [evalFuel, success, FuelResult.map,
                        Value.buildList, Value.consValue],
                      .list (.cons headTyping tailValuesTyping)⟩
          }
  case tuple =>
          intro expressions targets items itemsIH fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children := itemsIH fuel environment
          rcases children with timeout | ⟨values, success, childrenTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
          · exact .inr ⟨.tuple values, by
              simp [evalFuel, success, FuelResult.map], .tuple childrenTyping⟩
          }
  case add =>
          intro leftExpression rightExpression left right leftIH rightIH
            fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults [.int, .int]
              (FuelResult.traverse (evalFuel fuel environment)
                [leftExpression, rightExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (leftIH fuel environment)
              (rightIH fuel environment)
          rcases children with timeout | ⟨values, success, valuesTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · cases valuesTyping with
            | cons leftTyping tailTyping =>
                cases tailTyping with
                | cons rightTyping nilTyping =>
                    cases nilTyping
                    obtain ⟨leftValue, rfl⟩ := leftTyping.int_canonical
                    obtain ⟨rightValue, rfl⟩ := rightTyping.int_canonical
                    exact .inr ⟨.int (leftValue + rightValue), by
                      simp [evalFuel, success, evalPrimitive,
                        FuelResult.bind], .int _⟩
          }
  case append =>
          intro leftExpression element rightExpression left right leftIH rightIH
            fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [TypePM.DataTypes.list element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [leftExpression, rightExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (leftIH fuel environment)
              (rightIH fuel environment)
          rcases children with timeout | ⟨values, success, valuesTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · cases valuesTyping with
            | cons leftTyping tailTyping =>
                cases tailTyping with
                | cons rightTyping nilTyping =>
                    cases nilTyping
                    obtain ⟨leftItems, leftEq, leftItemsTyping⟩ :=
                      leftTyping.list_canonical
                    obtain ⟨rightItems, rightEq, rightItemsTyping⟩ :=
                      rightTyping.list_canonical
                    subst leftEq
                    subst rightEq
                    exact .inr ⟨Value.buildList (leftItems ++ rightItems), by
                      simp [evalFuel, success, evalPrimitive,
                        FuelResult.bind],
                      .list (leftItemsTyping.append rightItemsTyping)⟩
          }
  case member =>
          intro needleExpression element targetExpression needle list needleIH
            listIH fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [needleExpression, targetExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (needleIH fuel environment)
              (listIH fuel environment)
          rcases children with timeout | ⟨values, success, valuesTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · cases valuesTyping with
            | @cons needleValue _ _ _ needleTyping tailTyping =>
                cases tailTyping with
                | cons listTyping nilTyping =>
                    cases nilTyping
                    obtain ⟨items, listEq, itemsTyping⟩ :=
                      listTyping.list_canonical
                    subst listEq
                    exact .inr
                      ⟨Value.boolValue
                          (Value.memberStructural needleValue items), by
                        simp [evalFuel, success, evalPrimitive,
                          FuelResult.bind],
                        ValueTyping.boolValue _⟩
          }
  case deleteFirst =>
          intro needleExpression element targetExpression needle list needleIH
            listIH fuel environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [needleExpression, targetExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (needleIH fuel environment)
              (listIH fuel environment)
          rcases children with timeout | ⟨values, success, valuesTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · cases valuesTyping with
            | @cons needleValue _ _ _ needleTyping tailTyping =>
                cases tailTyping with
                | cons listTyping nilTyping =>
                    cases nilTyping
                    obtain ⟨items, listEq, itemsTyping⟩ :=
                      listTyping.list_canonical
                    subst listEq
                    exact .inr ⟨_, by
                      simp [evalFuel, success, evalPrimitive,
                        FuelResult.bind],
                      .list (itemsTyping.deleteFirstStructural needleValue)⟩
          }
  case ifE =>
          intro conditionExpression thenExpression branchTarget elseExpression
            condition thenBranch elseBranch conditionIH thenIH elseIH fuel
            environment
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have conditionResult := conditionIH fuel environment
          rcases conditionResult with timeout |
            ⟨conditionValue, success, conditionTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · rcases conditionTyping.bool_canonical with isTrue | isFalse
            · subst conditionValue
              have branchResult := thenIH fuel environment
              rcases branchResult with branchTimeout |
                ⟨value, branchSuccess, valueTyping⟩
              · exact .inl (by
                  simp [evalFuel, success, branchTimeout, FuelResult.bind])
              · exact .inr ⟨value, by
                  simp [evalFuel, success, branchSuccess, FuelResult.bind],
                  valueTyping⟩
            · subst conditionValue
              have branchResult := elseIH fuel environment
              have falseNeTrue : DataCtor.false ≠ DataCtor.true := by decide
              rcases branchResult with branchTimeout |
                ⟨value, branchSuccess, valueTyping⟩
              · exact .inl (by
                  simp [evalFuel, success, branchTimeout, FuelResult.bind,
                    falseNeTrue])
              · exact .inr ⟨value, by
                  simp [evalFuel, success, branchSuccess, FuelResult.bind,
                    falseNeTrue],
                  valueTyping⟩
          }
  case checked =>
          intro expression sourceTarget conversionClass target source conversion
            sourceIH fuel environment
          have sourceResult := sourceIH fuel environment
          rcases sourceResult with timeout | ⟨value, success, valueTyping⟩
          · exact .inl timeout
          · exact .inr ⟨value, success, .checked valueTyping conversion⟩
  case instantiated =>
          intro expression sourceTarget source substitution sourceIH fuel
            environment
          have sourceResult := sourceIH fuel environment
          rcases sourceResult with timeout | ⟨value, success, valueTyping⟩
          · exact .inl timeout
          · exact .inr ⟨value, success, valueTyping.apply substitution⟩
  case nil =>
      intro fuel environment
      exact .inr ⟨[], rfl, .nil⟩
  case cons =>
      intro expression target expressions targets head tail headIH tailIH fuel
        environment
      have headResult := headIH fuel environment
      rcases headResult with headTimeout |
        ⟨headValue, headSuccess, headTyping⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · have tailResult := tailIH fuel environment
        rcases tailResult with tailTimeout |
          ⟨tailValues, tailSuccess, tailTyping⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            .cons headTyping tailTyping⟩
  case t => exact typing

/-- List preservation/progress used by tuple and constructor evaluation. -/
theorem RuntimeTypings.coreSafety
    (typing : RuntimeTypings expressions targets)
    (fuel : Nat) (environment : ValueEnvironment) :
    TypedResults targets
      (FuelResult.traverse (evalFuel fuel environment) expressions) := by
  apply RuntimeTypings.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun expressions targets _ =>
      ∀ fuel environment, TypedResults targets
        (FuelResult.traverse (evalFuel fuel environment) expressions))
  case lit | boolTrue | boolFalse | listNil | listCons | tuple | add |
      append | member | deleteFirst | ifE | checked | instantiated =>
    simp
  case nil =>
    intro fuel environment
    exact .inr ⟨[], rfl, .nil⟩
  case cons =>
      intro expression target expressions targets head tail _ tailIH fuel
        environment
      have headResult := head.coreSafety fuel environment
      rcases headResult with headTimeout |
        ⟨headValue, headSuccess, headTyping⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · have tailResult := tailIH fuel environment
        rcases tailResult with tailTimeout |
          ⟨tailValues, tailSuccess, tailTyping⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            .cons headTyping tailTyping⟩
  case t => exact typing

end TypePM.Runtime

namespace TypePM.Source

namespace Typing

/-- Source-facing form of conditional core safety.  It combines theorem 5.6's
state-erasure bridge with the mutual runtime preservation/progress theorem. -/
theorem coreSafety
    {signature : Signature} {expression : Expr} {target : Ty}
    (typing : Typing signature [] expression target)
    (compatible : Runtime.SignatureCompatible signature)
    (supported : Runtime.RuntimeSupported expression)
    (fuel : Nat) :
    Runtime.TypedResult target (Runtime.evalFuel fuel [] expression) :=
  (typing.toRuntimeTyping compatible supported).coreSafety fuel []

end Typing

end TypePM.Source
