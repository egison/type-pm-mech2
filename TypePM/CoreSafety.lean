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

namespace EnvironmentTyping

theorem lookup
    {index : Nat}
    (typing : EnvironmentTyping environment context)
    (found : context[index]? = some target) :
    ∃ value, environment[index]? = some value ∧ ValueTyping value target := by
  induction index generalizing environment context with
  | zero =>
      cases typing with
      | nil => simp at found
      | cons head tail =>
          simp at found
          subst target
          exact ⟨_, rfl, head⟩
  | succ index induction =>
      cases typing with
      | nil => simp at found
      | cons head tail =>
          simp only [List.getElem?_cons_succ] at found ⊢
          exact induction tail found

end EnvironmentTyping

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
    (motive_4 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ typing
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
  · intro _values _context _bodyExpression _codomain _domain
      _environment _body _environmentIH
    refine ⟨?_, ?_, ?_⟩ <;> intros
    · simp [Ty.apply] at *
    · simp [Ty.apply, TypePM.DataTypes.bool] at *
    · simp [Ty.apply, TypePM.DataTypes.list] at *
  · intro _values _context _bodyExpression _codomain _domain
      _environment _body _environmentIH
    refine ⟨?_, ?_, ?_⟩ <;> intros
    · simp [Ty.apply] at *
    · simp [Ty.apply, TypePM.DataTypes.bool] at *
    · simp [Ty.apply, TypePM.DataTypes.list] at *
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
  · trivial
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
`deleteFirst`, same-result-type conditionals, typed environments, closures,
and direct `lam`/`fixE` applications. -/
theorem RuntimeTyping.coreSafety
    (typing : RuntimeTyping expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    TypedResult target (evalFuel fuel environment expression) := by
  apply RuntimeTyping.rec
    (motive_1 := fun expression target context _ =>
      ∀ fuel environment, EnvironmentTyping environment context →
        TypedResult target
        (evalFuel fuel environment expression))
    (motive_2 := fun expressions targets context _ =>
      ∀ fuel environment, EnvironmentTyping environment context →
        TypedResults targets
        (FuelResult.traverse (evalFuel fuel environment) expressions))
  case var =>
      intro context index target lookup fuel environment environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          obtain ⟨value, found, valueTyping⟩ :=
            EnvironmentTyping.lookup environmentTyping lookup
          exact .inr ⟨value, by simp [evalFuel, found], valueTyping⟩
  case lit =>
          intro context value fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .int _⟩
  case boolTrue =>
          intro context fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .boolTrue⟩
  case boolFalse =>
          intro context fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .boolFalse⟩
  case listNil =>
          intro context element fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel =>
              exact .inr ⟨Value.buildList [], rfl, .list .nil⟩
  case listCons =>
          intro headExpression element context tailExpression head tail headIH
            tailIH fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [headExpression, tailExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (headIH fuel environment environmentTyping)
              (tailIH fuel environment environmentTyping)
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
          intro expressions targets context items itemsIH fuel environment
            environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children := itemsIH fuel environment environmentTyping
          rcases children with timeout | ⟨values, success, childrenTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
          · exact .inr ⟨.tuple values, by
              simp [evalFuel, success, FuelResult.map], .tuple childrenTyping⟩
          }
  case lam =>
      intro bodyExpression codomain domain context body bodyIH fuel environment
        environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          exact .inr ⟨Value.plainClosure environment bodyExpression, rfl,
            .plainClosure environmentTyping body⟩
  case fixE =>
      intro bodyExpression codomain domain context body bodyIH fuel environment
        environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          exact .inr ⟨Value.recursiveClosure environment bodyExpression, rfl,
            .recursiveClosure environmentTyping body⟩
  case appLam =>
      intro bodyExpression codomain domain context argumentExpression body
        argument bodyIH argumentIH fuel environment environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          cases fuel with
          | zero => exact .inl rfl
          | succ innerFuel =>
              have argumentResult :=
                argumentIH (innerFuel + 1) environment environmentTyping
              rcases argumentResult with timeout |
                ⟨argumentValue, success, argumentValueTyping⟩
              · exact .inl (by
                  rw [show innerFuel + 1 + 1 = Nat.succ (Nat.succ innerFuel) by omega]
                  rw [evalFuel.eq_def]
                  simp only
                  rw [show evalFuel (innerFuel + 1) environment
                    (.lam bodyExpression) =
                      .ok (Value.plainClosure environment bodyExpression) by rfl]
                  rw [timeout]
                  rfl)
              · have bodyResult := bodyIH innerFuel
                  (argumentValue :: environment)
                  (.cons argumentValueTyping environmentTyping)
                rcases bodyResult with bodyTimeout |
                  ⟨value, bodySuccess, valueTyping⟩
                · exact .inl (by
                    rw [show innerFuel + 1 + 1 = Nat.succ (Nat.succ innerFuel) by omega]
                    rw [evalFuel.eq_def]
                    simp only
                    rw [show evalFuel (innerFuel + 1) environment
                      (.lam bodyExpression) =
                        .ok (Value.plainClosure environment bodyExpression) by rfl]
                    rw [success]
                    exact bodyTimeout)
                · exact .inr ⟨value, by
                    rw [show innerFuel + 1 + 1 = Nat.succ (Nat.succ innerFuel) by omega]
                    rw [evalFuel.eq_def]
                    simp only
                    rw [show evalFuel (innerFuel + 1) environment
                      (.lam bodyExpression) =
                        .ok (Value.plainClosure environment bodyExpression) by rfl]
                    rw [success]
                    exact bodySuccess, valueTyping⟩
  case appFix =>
      intro bodyExpression codomain domain context argumentExpression body
        argument bodyIH argumentIH fuel environment environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          cases fuel with
          | zero => exact .inl rfl
          | succ innerFuel =>
              have argumentResult :=
                argumentIH (innerFuel + 1) environment environmentTyping
              rcases argumentResult with timeout |
                ⟨argumentValue, success, argumentValueTyping⟩
              · exact .inl (by
                  rw [show innerFuel + 1 + 1 = Nat.succ (Nat.succ innerFuel) by omega]
                  rw [evalFuel.eq_def]
                  simp only
                  rw [show evalFuel (innerFuel + 1) environment
                    (.fixE bodyExpression) =
                      .ok (Value.recursiveClosure environment bodyExpression) by rfl]
                  rw [timeout]
                  rfl)
              · let closure :=
                  Value.recursiveClosure environment bodyExpression
                have closureTyping :
                    ValueTyping closure (.fn domain codomain) :=
                  .recursiveClosure environmentTyping body
                have bodyResult := bodyIH innerFuel
                  (argumentValue :: closure :: environment)
                  (.cons argumentValueTyping
                    (.cons closureTyping environmentTyping))
                rcases bodyResult with bodyTimeout |
                  ⟨value, bodySuccess, valueTyping⟩
                · exact .inl (by
                    rw [show innerFuel + 1 + 1 = Nat.succ (Nat.succ innerFuel) by omega]
                    rw [evalFuel.eq_def]
                    simp only
                    rw [show evalFuel (innerFuel + 1) environment
                      (.fixE bodyExpression) = .ok closure by rfl]
                    rw [success]
                    exact bodyTimeout)
                · exact .inr ⟨value, by
                    rw [show innerFuel + 1 + 1 = Nat.succ (Nat.succ innerFuel) by omega]
                    rw [evalFuel.eq_def]
                    simp only
                    rw [show evalFuel (innerFuel + 1) environment
                      (.fixE bodyExpression) = .ok closure by rfl]
                    rw [success]
                    exact bodySuccess, valueTyping⟩
  case add =>
          intro leftExpression context rightExpression left right leftIH rightIH
            fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults [.int, .int]
              (FuelResult.traverse (evalFuel fuel environment)
                [leftExpression, rightExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (leftIH fuel environment environmentTyping)
              (rightIH fuel environment environmentTyping)
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
          intro leftExpression element context rightExpression left right leftIH
            rightIH fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [TypePM.DataTypes.list element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [leftExpression, rightExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (leftIH fuel environment environmentTyping)
              (rightIH fuel environment environmentTyping)
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
          intro needleExpression element context targetExpression needle list
            needleIH listIH fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [needleExpression, targetExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (needleIH fuel environment environmentTyping)
              (listIH fuel environment environmentTyping)
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
          intro needleExpression element context targetExpression needle list
            needleIH listIH fuel environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [needleExpression, targetExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (needleIH fuel environment environmentTyping)
              (listIH fuel environment environmentTyping)
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
          intro conditionExpression context thenExpression branchTarget elseExpression
            condition thenBranch elseBranch conditionIH thenIH elseIH fuel
            environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have conditionResult := conditionIH fuel environment environmentTyping
          rcases conditionResult with timeout |
            ⟨conditionValue, success, conditionTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · rcases conditionTyping.bool_canonical with isTrue | isFalse
            · subst conditionValue
              have branchResult := thenIH fuel environment environmentTyping
              rcases branchResult with branchTimeout |
                ⟨value, branchSuccess, valueTyping⟩
              · exact .inl (by
                  simp [evalFuel, success, branchTimeout, FuelResult.bind])
              · exact .inr ⟨value, by
                  simp [evalFuel, success, branchSuccess, FuelResult.bind],
                  valueTyping⟩
            · subst conditionValue
              have branchResult := elseIH fuel environment environmentTyping
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
          intro expression sourceTarget context conversionClass target source
            conversion sourceIH fuel environment environmentTyping
          have sourceResult := sourceIH fuel environment environmentTyping
          rcases sourceResult with timeout | ⟨value, success, valueTyping⟩
          · exact .inl timeout
          · exact .inr ⟨value, success, .checked valueTyping conversion⟩
  case instantiated =>
          intro expression sourceTarget context source substitution sourceIH fuel
            environment environmentTyping
          have sourceResult := sourceIH fuel environment environmentTyping
          rcases sourceResult with timeout | ⟨value, success, valueTyping⟩
          · exact .inl timeout
          · exact .inr ⟨value, success, valueTyping.apply substitution⟩
  case nil =>
      intro context fuel environment environmentTyping
      exact .inr ⟨[], rfl, .nil⟩
  case cons =>
      intro expression target context expressions targets head tail headIH tailIH
        fuel environment environmentTyping
      have headResult := headIH fuel environment environmentTyping
      rcases headResult with headTimeout |
        ⟨headValue, headSuccess, headTyping⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · have tailResult := tailIH fuel environment environmentTyping
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
  all_goals assumption

/-- List preservation/progress used by tuple and constructor evaluation. -/
theorem RuntimeTypings.coreSafety
    (typing : RuntimeTypings expressions targets context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    TypedResults targets
      (FuelResult.traverse (evalFuel fuel environment) expressions) := by
  apply RuntimeTypings.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun expressions targets context _ =>
      ∀ fuel environment, EnvironmentTyping environment context →
        TypedResults targets
        (FuelResult.traverse (evalFuel fuel environment) expressions))
  case var | lit | boolTrue | boolFalse | listNil | listCons | tuple | lam |
      appLam | appFix | fixE | add | append | member | deleteFirst | ifE |
      checked | instantiated =>
    simp
  case nil =>
    intro context fuel environment environmentTyping
    exact .inr ⟨[], rfl, .nil⟩
  case cons =>
      intro expression target context expressions targets head tail _ tailIH fuel
        environment environmentTyping
      have headResult := head.coreSafety fuel environment environmentTyping
      rcases headResult with headTimeout |
        ⟨headValue, headSuccess, headTyping⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · have tailResult := tailIH fuel environment environmentTyping
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
  all_goals assumption

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
  (typing.toRuntimeTyping compatible supported).coreSafety fuel [] .nil

end Typing

end TypePM.Source
