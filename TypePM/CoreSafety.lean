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

/-- Homogeneous counterpart used for the result of applying one function to
every element of a canonical runtime list. -/
def TypedHomogeneousResults
    (target : Ty) (result : FuelResult (List Value)) : Prop :=
  result = .timeout ∨
    ∃ values, result = .ok values ∧ ListValueTypings values target

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
  | productMatcherToSlot => simp [Ty.apply] at targetEq

theorem source_apply_eq_of_data_target
    (conversion : CheckConversion conversionClass source target)
    (targetEq : target.apply substitution = .data former arguments) :
    source.apply substitution = .data former arguments := by
  cases conversion with
  | ordinary => exact targetEq
  | matcherToSlot => simp [Ty.apply] at targetEq
  | productMatcherToSlot => simp [Ty.apply] at targetEq

theorem source_apply_eq_of_fn_target
    (conversion : CheckConversion conversionClass source target)
    (targetEq : target.apply substitution = .fn domain codomain) :
    source.apply substitution = .fn domain codomain := by
  cases conversion with
  | ordinary => exact targetEq
  | matcherToSlot => simp [Ty.apply] at targetEq
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ typing
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
  · intro _target
    refine ⟨?_, ?_, ?_⟩ <;> intros
    · simp [Ty.apply, Cap.apply] at *
    · simp [Ty.apply, Cap.apply, TypePM.DataTypes.bool] at *
    · simp [Ty.apply, Cap.apply, TypePM.DataTypes.list] at *
  · intro _values _definitionTypes _matcherTarget _original _remaining
      _environment _clauses _cursor _environmentIH
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

private def FunctionShape (value : Value) (target : Ty) : Prop :=
  ∀ substitution domain codomain,
    target.apply substitution = .fn domain codomain →
      (∃ environment context bodyExpression,
        value = Value.plainClosure environment bodyExpression ∧
        EnvironmentTyping environment context ∧
        RuntimeTyping bodyExpression codomain (domain :: context)) ∨
      (∃ environment context bodyExpression,
        value = Value.recursiveClosure environment bodyExpression ∧
        EnvironmentTyping environment context ∧
        RuntimeTyping bodyExpression codomain
          (domain :: .fn domain codomain :: context))

private theorem functionShape
    (typing : ValueTyping value target) : FunctionShape value target := by
  refine @ValueTyping.rec
    (motive_1 := fun value target _ => FunctionShape value target)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ typing
  · intro literal substitution domain codomain equality
    simp [Ty.apply] at equality
  · intro substitution domain codomain equality
    simp [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] at equality
  · intro substitution domain codomain equality
    simp [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] at equality
  · intro _values _targets _items _itemsIH substitution domain codomain equality
    simp [Ty.apply] at equality
  · intro _values _element _items _itemsIH substitution domain codomain equality
    simp [Ty.apply, TypePM.DataTypes.list] at equality
  · intro values context bodyExpression sourceCodomain sourceDomain
      environment body _environmentIH substitution domain codomain equality
    have parts := Ty.fn.inj equality
    exact .inl ⟨values, Ty.applyList substitution context, bodyExpression, rfl,
      environment.apply substitution, by
        simpa [Ty.apply, Ty.applyList, parts.1, parts.2] using
          body.applyContext substitution⟩
  · intro values context bodyExpression sourceCodomain sourceDomain
      environment body _environmentIH substitution domain codomain equality
    have parts := Ty.fn.inj equality
    exact .inr ⟨values, Ty.applyList substitution context, bodyExpression, rfl,
      environment.apply substitution, by
        simpa [Ty.apply, Ty.applyList, parts.1, parts.2] using
          body.applyContext substitution⟩
  · intro _target substitution domain codomain equality
    simp [Ty.apply, Cap.apply] at equality
  · intro _values _definitionTypes _matcherTarget _original _remaining
      _environment _clauses _cursor _environmentIH substitution
      domain codomain equality
    simp [Ty.apply] at equality
  · intro _value _sourceTarget _class _target source conversion sourceIH
      substitution domain codomain equality
    exact sourceIH substitution domain codomain
      (TypePM.Runtime.CheckConversion.source_apply_eq_of_fn_target
        conversion equality)
  · intro _value _sourceTarget source earlier sourceIH substitution domain
      codomain equality
    exact sourceIH (Subst.compose substitution earlier) domain codomain (by
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

/-- A function-typed value is one of the evaluator's two closure forms, and
its captured environment and body carry the corresponding runtime types. -/
theorem function_canonical
    (typing : ValueTyping value (.fn domain codomain)) :
      (∃ environment context bodyExpression,
        value = Value.plainClosure environment bodyExpression ∧
        EnvironmentTyping environment context ∧
        RuntimeTyping bodyExpression codomain (domain :: context)) ∨
      (∃ environment context bodyExpression,
        value = Value.recursiveClosure environment bodyExpression ∧
        EnvironmentTyping environment context ∧
        RuntimeTyping bodyExpression codomain
          (domain :: .fn domain codomain :: context)) := by
  exact functionShape typing Subst.id domain codomain (by simp)

/-- Runtime shapes that can implement a matcher or matcher slot.  The middle
case retains the complete closure certificate: definition-environment types,
original clause typing, and validity of the remaining-clause cursor. -/
def MatcherRuntimeShape (value : Value) : Prop :=
  value = .something ∨
    (∃ environment definitionTypes matcherTarget original remaining,
      value = .matcherV environment original remaining ∧
      EnvironmentTyping environment definitionTypes ∧
      RuntimeMatcherClausesTyping definitionTypes matcherTarget original ∧
      ∃ tried, original = tried ++ remaining) ∨
    ∃ values, value = .tuple values

private structure DispatchCanonicalProperties
    (value : Value) (target : Ty) : Prop where
  productShape : ∀ substitution targets,
    target.apply substitution = .prod targets →
      ∃ values, value = .tuple values ∧ ValueTypings values targets
  matcherShape : ∀ substitution capability matcherTarget,
    target.apply substitution = .matcher capability matcherTarget →
      MatcherRuntimeShape value
  slotShape : ∀ substitution capability matcherTarget,
    target.apply substitution = .slot capability matcherTarget →
      MatcherRuntimeShape value

private theorem dispatchCanonicalProperties
    (typing : ValueTyping value target) :
    DispatchCanonicalProperties value target := by
  refine @ValueTyping.rec
    (motive_1 := fun value target _ => DispatchCanonicalProperties value target)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ typing
  · intro literal
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp [Ty.apply] at *
  · refine ⟨?_, ?_, ?_⟩ <;> intros <;>
      simp [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] at *
  · refine ⟨?_, ?_, ?_⟩ <;> intros <;>
      simp [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] at *
  · intro values sourceTargets items _itemsIH
    refine ⟨?_, ?_, ?_⟩
    · intro substitution targets equality
      have targetsEq : Ty.applyList substitution sourceTargets = targets := by
        simpa [Ty.apply] using equality
      subst targets
      exact ⟨values, rfl, items.apply substitution⟩
    · intros; simp [Ty.apply] at *
    · intros; simp [Ty.apply] at *
  · intro _values _element _items _itemsIH
    refine ⟨?_, ?_, ?_⟩ <;> intros <;>
      simp [Ty.apply, TypePM.DataTypes.list] at *
  · intro _values _context _body _codomain _domain _environment _bodyTyping _ih
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp [Ty.apply] at *
  · intro _values _context _body _codomain _domain _environment _bodyTyping _ih
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp [Ty.apply] at *
  · intro target
    refine ⟨?_, ?_, ?_⟩
    · intros; simp [Ty.apply, Cap.apply] at *
    · intro _ _ _ _; exact Or.inl rfl
    · intros; simp [Ty.apply, Cap.apply] at *
  · intro environment definitionTypes target original remaining
      environmentTyped clauses cursor _environmentIH
    refine ⟨?_, ?_, ?_⟩
    · intros; simp [Ty.apply] at *
    · intro _ _ _ _
      exact Or.inr (Or.inl ⟨environment, definitionTypes, target, original,
        remaining, rfl, environmentTyped, clauses, cursor⟩)
    · intros; simp [Ty.apply] at *
  · intro _value _sourceTarget _class _target source conversion sourceIH
    refine ⟨?_, ?_, ?_⟩
    · intro substitution targets equality
      cases conversion with
      | ordinary => exact sourceIH.productShape substitution targets equality
      | matcherToSlot => simp [Ty.apply] at equality
      | productMatcherToSlot => simp [Ty.apply] at equality
    · intro substitution capability matcherTarget equality
      cases conversion with
      | ordinary =>
          exact sourceIH.matcherShape substitution capability matcherTarget equality
      | matcherToSlot => simp [Ty.apply] at equality
      | productMatcherToSlot => simp [Ty.apply] at equality
    · intro substitution capability matcherTarget equality
      cases conversion with
      | ordinary =>
          exact sourceIH.slotShape substitution capability matcherTarget equality
      | @matcherToSlot producer consumer sourceTarget demand =>
          exact sourceIH.matcherShape substitution
            (producer.apply substitution.cap) (sourceTarget.apply substitution)
            (by simp [Ty.apply])
      | @productMatcherToSlot duals consumer nonempty demand =>
          obtain ⟨values, valueEq, _itemsTyped⟩ :=
            sourceIH.productShape substitution
              (Ty.applyList substitution (duals.map Dual.matcherType)) (by
                simp [Ty.apply])
          exact Or.inr (Or.inr ⟨values, valueEq⟩)
  · intro _value _sourceTarget source earlier sourceIH
    refine ⟨?_, ?_, ?_⟩
    · intro substitution targets equality
      exact sourceIH.productShape (Subst.compose substitution earlier) targets (by
        simpa only [Ty.apply_compose] using equality)
    · intro substitution capability matcherTarget equality
      exact sourceIH.matcherShape (Subst.compose substitution earlier)
        capability matcherTarget (by
          simpa only [Ty.apply_compose] using equality)
    · intro substitution capability matcherTarget equality
      exact sourceIH.slotShape (Subst.compose substitution earlier)
        capability matcherTarget (by
          simpa only [Ty.apply_compose] using equality)
  · trivial
  · intros; trivial
  · intro; trivial
  · intros; trivial
  · trivial
  · intros; trivial

/-- A product-typed value is an exact runtime tuple with pointwise typed
components.  Clause dispatch uses this to justify `decodeProduct` for the
zero/many conventions. -/
theorem product_canonical
    (typing : ValueTyping value (.prod targets)) :
    ∃ values, value = .tuple values ∧ ValueTypings values targets := by
  exact (dispatchCanonicalProperties typing).productShape Subst.id targets (by simp)

/-- A matcher-typed value has one of the three executable matcher shapes:
`something`, a certified user matcher closure, or a product of matchers. -/
theorem matcher_canonical
    (typing : ValueTyping value (.matcher capability matcherTarget)) :
    MatcherRuntimeShape value := by
  exact (dispatchCanonicalProperties typing).matcherShape Subst.id capability
    matcherTarget (by simp)

/-- Slot checking does not invent a new runtime form: a slot is represented by
the same canonical values as a matcher. -/
theorem slot_canonical
    (typing : ValueTyping value (.slot capability matcherTarget)) :
    MatcherRuntimeShape value := by
  exact (dispatchCanonicalProperties typing).slotShape Subst.id capability
    matcherTarget (by simp)

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

/-- Pointwise safety lifts to the evaluator's left-to-right homogeneous
traversal.  This separates host-list recursion from expression-evaluation
recursion in the `map` proof. -/
protected def traverseTyped
    (applyValue : Value → FuelResult Value)
    (safe : ∀ {value}, ValueTyping value source →
      TypedResult target (applyValue value)) :
    (typing : ListValueTypings values source) →
      TypedHomogeneousResults target
        (FuelResult.traverse applyValue values)
  | .nil => .inr ⟨[], rfl, .nil⟩
  | .cons head tail => by
      rcases safe head with headTimeout |
        ⟨output, headSuccess, outputTyping⟩
      · exact .inl (by
          simp [FuelResult.traverse, headTimeout])
      · rcases tail.traverseTyped applyValue safe with tailTimeout |
          ⟨outputs, tailSuccess, outputsTyping⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨output :: outputs, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            .cons outputTyping outputsTyping⟩

end ListValueTypings

/-- **Theorem 5.7, certified core.**  Expression evaluation preserves the
runtime type, and every fuel-bounded evaluation is ready: it either times out
or produces a typed value.  The certified constructors cover integers,
canonical Booleans and Lists, tuples, integer addition, `append`, `member`,
`deleteFirst`, `map`, monomorphic `letE`, same-result-type conditionals, typed
environments, closures, and applications with an arbitrary typed function
expression. -/
private theorem RuntimeTyping.coreSafetyBound
    (typing : RuntimeTyping expression target context)
    (budget fuel : Nat) (fuelBound : fuel ≤ budget)
    (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    TypedResult target (evalFuel fuel environment expression) := by
  apply RuntimeTyping.rec
    (motive_1 := fun expression target context _ =>
      ∀ fuel, fuel ≤ budget → ∀ environment,
        EnvironmentTyping environment context →
        TypedResult target
        (evalFuel fuel environment expression))
    (motive_2 := fun expressions targets context _ =>
      ∀ fuel, fuel ≤ budget → ∀ environment,
        EnvironmentTyping environment context →
        TypedResults targets
        (FuelResult.traverse (evalFuel fuel environment) expressions))
  case var =>
      intro context index target lookup fuel _fuelBound environment environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          obtain ⟨value, found, valueTyping⟩ :=
            EnvironmentTyping.lookup environmentTyping lookup
          exact .inr ⟨value, by simp [evalFuel, found], valueTyping⟩
  case lit =>
          intro context value fuel _fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .int _⟩
  case something =>
          intro context target fuel _fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨.something, rfl, .something target⟩
  case boolTrue =>
          intro context fuel _fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .boolTrue⟩
  case boolFalse =>
          intro context fuel _fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => exact .inr ⟨_, rfl, .boolFalse⟩
  case listNil =>
          intro context element fuel _fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel =>
              exact .inr ⟨Value.buildList [], rfl, .list .nil⟩
  case listCons =>
          intro headExpression element context tailExpression head tail headIH
            tailIH fuel fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [headExpression, tailExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (headIH fuel (by omega) environment environmentTyping)
              (tailIH fuel (by omega) environment environmentTyping)
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
          intro expressions targets context items itemsIH fuel fuelBound environment
            environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children := itemsIH fuel (by omega) environment environmentTyping
          rcases children with timeout | ⟨values, success, childrenTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
          · exact .inr ⟨.tuple values, by
              simp [evalFuel, success, FuelResult.map], .tuple childrenTyping⟩
          }
  case lam =>
      intro bodyExpression codomain domain context body bodyIH fuel _fuelBound environment
        environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          exact .inr ⟨Value.plainClosure environment bodyExpression, rfl,
            .plainClosure environmentTyping body⟩
  case fixE =>
      intro bodyExpression codomain domain context body bodyIH fuel _fuelBound environment
        environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          exact .inr ⟨Value.recursiveClosure environment bodyExpression, rfl,
            .recursiveClosure environmentTyping body⟩
  case app =>
      intro functionExpression domain codomain context argumentExpression function
        argument functionIH argumentIH fuel fuelBound environment environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ applicationFuel =>
          have functionResult :=
            functionIH applicationFuel (by omega) environment environmentTyping
          rcases functionResult with functionTimeout |
            ⟨functionValue, functionSuccess, functionValueTyping⟩
          · exact .inl (by
              simp [evalFuel, functionTimeout, FuelResult.bind])
          · have argumentResult :=
              argumentIH applicationFuel (by omega) environment environmentTyping
            rcases argumentResult with argumentTimeout |
              ⟨argumentValue, argumentSuccess, argumentValueTyping⟩
            · exact .inl (by
                simp [evalFuel, functionSuccess, argumentTimeout,
                  FuelResult.bind])
            · cases applicationFuel with
              | zero => exact .inl (by simp [evalFuel])
              | succ bodyFuel =>
                rcases functionValueTyping.function_canonical with
                  ⟨definitionEnvironment, definitionContext, bodyExpression,
                    functionEq, definitionEnvironmentTyping, bodyTyping⟩ |
                  ⟨definitionEnvironment, definitionContext, bodyExpression,
                    functionEq, definitionEnvironmentTyping, bodyTyping⟩
                · subst functionValue
                  have bodyResult := bodyTyping.coreSafetyBound bodyFuel bodyFuel
                    (Nat.le_refl _)
                    (argumentValue :: definitionEnvironment)
                    (.cons argumentValueTyping definitionEnvironmentTyping)
                  rcases bodyResult with bodyTimeout |
                    ⟨value, bodySuccess, valueTyping⟩
                  · exact .inl (by
                      rw [evalFuel.eq_def]
                      simp only
                      rw [functionSuccess, argumentSuccess]
                      exact bodyTimeout)
                  · exact .inr ⟨value, by
                      rw [evalFuel.eq_def]
                      simp only
                      rw [functionSuccess, argumentSuccess]
                      exact bodySuccess, valueTyping⟩
                · subst functionValue
                  let closure := Value.recursiveClosure definitionEnvironment
                    bodyExpression
                  have closureTyping :
                      ValueTyping closure (.fn domain codomain) :=
                    .recursiveClosure definitionEnvironmentTyping bodyTyping
                  have bodyResult := bodyTyping.coreSafetyBound bodyFuel bodyFuel
                    (Nat.le_refl _)
                    (argumentValue :: closure :: definitionEnvironment)
                    (.cons argumentValueTyping
                      (.cons closureTyping definitionEnvironmentTyping))
                  rcases bodyResult with bodyTimeout |
                    ⟨value, bodySuccess, valueTyping⟩
                  · exact .inl (by
                      rw [evalFuel.eq_def]
                      simp only
                      rw [functionSuccess, argumentSuccess]
                      exact bodyTimeout)
                  · exact .inr ⟨value, by
                      rw [evalFuel.eq_def]
                      simp only
                      rw [functionSuccess, argumentSuccess]
                      exact bodySuccess,
                      valueTyping⟩
  case letE =>
      intro valueExpression valueTarget context bodyExpression bodyTarget value body
        valueIH bodyIH fuel fuelBound environment environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          have valueResult :=
            valueIH fuel (by omega) environment environmentTyping
          rcases valueResult with valueTimeout |
            ⟨valueResult, valueSuccess, valueTyping⟩
          · exact .inl (by
              simp [evalFuel, valueTimeout, FuelResult.bind])
          · have bodyResult := bodyIH fuel (by omega)
              (valueResult :: environment) (.cons valueTyping environmentTyping)
            rcases bodyResult with bodyTimeout |
              ⟨result, bodySuccess, resultTyping⟩
            · exact .inl (by
                simp [evalFuel, valueSuccess, bodyTimeout, FuelResult.bind])
            · exact .inr ⟨result, by
                simp [evalFuel, valueSuccess, bodySuccess, FuelResult.bind],
                resultTyping⟩
  case add =>
          intro leftExpression context rightExpression left right leftIH rightIH
            fuel fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults [.int, .int]
              (FuelResult.traverse (evalFuel fuel environment)
                [leftExpression, rightExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (leftIH fuel (by omega) environment environmentTyping)
              (rightIH fuel (by omega) environment environmentTyping)
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
            rightIH fuel fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [TypePM.DataTypes.list element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [leftExpression, rightExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (leftIH fuel (by omega) environment environmentTyping)
              (rightIH fuel (by omega) environment environmentTyping)
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
            needleIH listIH fuel fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [needleExpression, targetExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (needleIH fuel (by omega) environment environmentTyping)
              (listIH fuel (by omega) environment environmentTyping)
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
            needleIH listIH fuel fuelBound environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel fuel environment)
                [needleExpression, targetExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (needleIH fuel (by omega) environment environmentTyping)
              (listIH fuel (by omega) environment environmentTyping)
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
  case map =>
          intro functionExpression domain codomain context targetExpression
            function target functionIH targetIH fuel fuelBound environment
              environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ primitiveFuel =>
            have children : TypedResults
                [.fn domain codomain, TypePM.DataTypes.list domain]
                (FuelResult.traverse (evalFuel primitiveFuel environment)
                  [functionExpression, targetExpression]) := by
              simpa [FuelResult.traverse] using TypedResult.pairTraverse
                (functionIH primitiveFuel (by omega) environment environmentTyping)
                (targetIH primitiveFuel (by omega) environment environmentTyping)
            rcases children with timeout | ⟨values, success, valuesTyping⟩
            · exact .inl (by
                simp [evalFuel, timeout, FuelResult.bind])
            · cases valuesTyping with
              | @cons functionValue _ _ _ functionValueTyping tailTyping =>
                cases tailTyping with
                | @cons targetValue _ _ _ targetValueTyping nilTyping =>
                  cases nilTyping
                  obtain ⟨inputs, targetEq, inputsTyping⟩ :=
                    targetValueTyping.list_canonical
                  subst targetValue
                  rcases functionValueTyping.function_canonical with
                    ⟨definitionEnvironment, definitionContext, bodyExpression,
                      functionEq, definitionEnvironmentTyping, bodyTyping⟩ |
                    ⟨definitionEnvironment, definitionContext, bodyExpression,
                      functionEq, definitionEnvironmentTyping, bodyTyping⟩
                  · subst functionValue
                    cases primitiveFuel with
                    | zero =>
                      exfalso
                      simp [FuelResult.traverse, evalFuel] at success
                    | succ bodyFuel =>
                      have mapped : TypedHomogeneousResults codomain
                          (FuelResult.traverse
                            (applyFuel (bodyFuel + 1)
                              (Value.plainClosure definitionEnvironment
                                bodyExpression)) inputs) :=
                        inputsTyping.traverseTyped _ (fun inputTyping => by
                          rw [show applyFuel (bodyFuel + 1)
                            (Value.plainClosure definitionEnvironment
                              bodyExpression) _ =
                            evalFuel bodyFuel (_ :: definitionEnvironment)
                              bodyExpression by rfl]
                          exact bodyTyping.coreSafetyBound bodyFuel bodyFuel
                            (Nat.le_refl _)
                            (_ :: definitionEnvironment)
                            (.cons inputTyping definitionEnvironmentTyping))
                      rcases mapped with mappedTimeout |
                        ⟨outputs, mappedSuccess, outputsTyping⟩
                      · exact .inl (by
                          rw [evalFuel.eq_def]
                          simp only
                          rw [success]
                          simp [evalPrimitive, mappedTimeout, FuelResult.map])
                      · exact .inr ⟨Value.buildList outputs, by
                          rw [evalFuel.eq_def]
                          simp only
                          rw [success]
                          simp [evalPrimitive, mappedSuccess, FuelResult.map],
                          .list outputsTyping⟩
                  · subst functionValue
                    let closure := Value.recursiveClosure definitionEnvironment
                      bodyExpression
                    have closureTyping :
                        ValueTyping closure (.fn domain codomain) :=
                      .recursiveClosure definitionEnvironmentTyping bodyTyping
                    cases primitiveFuel with
                    | zero =>
                      exfalso
                      simp [FuelResult.traverse, evalFuel] at success
                    | succ bodyFuel =>
                      have mapped : TypedHomogeneousResults codomain
                          (FuelResult.traverse
                            (applyFuel (bodyFuel + 1) closure) inputs) :=
                        inputsTyping.traverseTyped _ (fun inputTyping => by
                          rw [show applyFuel (bodyFuel + 1) closure _ =
                            evalFuel bodyFuel
                              (_ :: closure :: definitionEnvironment)
                              bodyExpression by rfl]
                          exact bodyTyping.coreSafetyBound bodyFuel bodyFuel
                            (Nat.le_refl _)
                            (_ :: closure :: definitionEnvironment)
                            (.cons inputTyping (.cons closureTyping
                              definitionEnvironmentTyping)))
                      rcases mapped with mappedTimeout |
                        ⟨outputs, mappedSuccess, outputsTyping⟩
                      · exact .inl (by
                          rw [evalFuel.eq_def]
                          simp only
                          rw [success]
                          simp [evalPrimitive, closure, mappedTimeout,
                            FuelResult.map])
                      · exact .inr ⟨Value.buildList outputs, by
                          rw [evalFuel.eq_def]
                          simp only
                          rw [success]
                          simp [evalPrimitive, closure, mappedSuccess,
                            FuelResult.map],
                          .list outputsTyping⟩
  case pairFirst =>
      intro pairExpression firstTarget secondTarget context pair pairIH fuel
        fuelBound environment environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ primitiveFuel =>
          have pairResult :=
            pairIH primitiveFuel (by omega) environment environmentTyping
          rcases pairResult with pairTimeout |
            ⟨pairValue, pairSuccess, pairTyping⟩
          · exact .inl (by
              simp [evalFuel, pairTimeout, FuelResult.bind,
                FuelResult.traverse])
          · obtain ⟨values, rfl, valuesTyping⟩ := pairTyping.product_canonical
            cases valuesTyping with
            | cons firstTyping tailTyping =>
                cases tailTyping with
                | cons secondTyping nilTyping =>
                    cases nilTyping
                    exact .inr ⟨_, by
                      simp [evalFuel, pairSuccess, evalPrimitive,
                        FuelResult.bind, FuelResult.traverse], firstTyping⟩
  case pairSecond =>
      intro pairExpression firstTarget secondTarget context pair pairIH fuel
        fuelBound environment environmentTyping
      cases fuel with
      | zero => exact .inl rfl
      | succ primitiveFuel =>
          have pairResult :=
            pairIH primitiveFuel (by omega) environment environmentTyping
          rcases pairResult with pairTimeout |
            ⟨pairValue, pairSuccess, pairTyping⟩
          · exact .inl (by
              simp [evalFuel, pairTimeout, FuelResult.bind,
                FuelResult.traverse])
          · obtain ⟨values, rfl, valuesTyping⟩ := pairTyping.product_canonical
            cases valuesTyping with
            | cons firstTyping tailTyping =>
                cases tailTyping with
                | cons secondTyping nilTyping =>
                    cases nilTyping
                    exact .inr ⟨_, by
                      simp [evalFuel, pairSuccess, evalPrimitive,
                        FuelResult.bind, FuelResult.traverse], secondTyping⟩
  case ifE =>
          intro conditionExpression context thenExpression branchTarget elseExpression
            condition thenBranch elseBranch conditionIH thenIH elseIH fuel fuelBound
            environment environmentTyping
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel => {
          have conditionResult := conditionIH fuel (by omega) environment environmentTyping
          rcases conditionResult with timeout |
            ⟨conditionValue, success, conditionTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · rcases conditionTyping.bool_canonical with isTrue | isFalse
            · subst conditionValue
              have branchResult := thenIH fuel (by omega) environment environmentTyping
              rcases branchResult with branchTimeout |
                ⟨value, branchSuccess, valueTyping⟩
              · exact .inl (by
                  simp [evalFuel, success, branchTimeout, FuelResult.bind])
              · exact .inr ⟨value, by
                  simp [evalFuel, success, branchSuccess, FuelResult.bind],
                  valueTyping⟩
            · subst conditionValue
              have branchResult := elseIH fuel (by omega) environment environmentTyping
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
            conversion sourceIH fuel fuelBound environment environmentTyping
          have sourceResult := sourceIH fuel fuelBound environment environmentTyping
          rcases sourceResult with timeout | ⟨value, success, valueTyping⟩
          · exact .inl timeout
          · exact .inr ⟨value, success, .checked valueTyping conversion⟩
  case nil =>
      intro context fuel _fuelBound environment environmentTyping
      exact .inr ⟨[], rfl, .nil⟩
  case cons =>
      intro expression target context expressions targets head tail headIH tailIH
        fuel fuelBound environment environmentTyping
      have headResult := headIH fuel fuelBound environment environmentTyping
      rcases headResult with headTimeout |
        ⟨headValue, headSuccess, headTyping⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · have tailResult := tailIH fuel fuelBound environment environmentTyping
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
termination_by budget
decreasing_by all_goals simp_wf <;> subst_vars <;> omega

/-- **Theorem 5.7, certified core.**  Public preservation and ready-progress
theorem, obtained by choosing the evaluation fuel itself as the recursive
proof budget. -/
theorem RuntimeTyping.coreSafety
    (typing : RuntimeTyping expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    TypedResult target (evalFuel fuel environment expression) :=
  typing.coreSafetyBound fuel fuel (Nat.le_refl _) environment environmentTyping

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
  case var | lit | something | boolTrue | boolFalse | listNil | listCons | tuple | lam |
      app | letE | fixE | add | append | member | deleteFirst | map | pairFirst |
      pairSecond | ifE |
      checked =>
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
