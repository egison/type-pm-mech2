import TypePM.RecursiveTotalClosureSafety

/-!
# Plain closures over total environments

`TotalValueTyping` can type the recursive matcher closures used by Paper 1,
but its ordinary plain-closure case is inherited from `ValueTyping` and can
therefore capture only an old `EnvironmentTyping`.  This module adds a
parallel proof-only layer in which an ordinary lambda may capture a
`TotalEnvironmentTyping`, including recursive matcher closures.

Dynamic body safety remains separate from structural value typing.  The
`TotalPlainFunctionSafe` certificate records exactly the additional fact
needed by application and `map`: applying the produced function to a typed
argument times out or returns a typed value.
-/

namespace TypePM.Runtime

mutual

  /-- Total value typing extended with ordinary closures over total captured
  environments.  The `list` case is needed because `map` may return closures
  that are not representable by the older homogeneous value judgment. -/
  inductive TotalPlainValueTyping : Value → Ty → Prop where
    | existing (typing : TotalValueTyping value target) :
        TotalPlainValueTyping value target
    | tuple (items : TotalPlainValueTypings values targets) :
        TotalPlainValueTyping (.tuple values) (.prod targets)
    | plainClosure
        (environment : TotalPlainValueTypings values context)
        (body : TotalRecursiveClosureBodyTyping
          (domain :: context) bodyExpression codomain) :
        TotalPlainValueTyping (Value.plainClosure values bodyExpression)
          (.fn domain codomain)
    | list (items : TotalPlainListValueTypings values element) :
        TotalPlainValueTyping (Value.buildList values)
          (TypePM.DataTypes.list element)

  /-- Pointwise typing for captured environments in the extended layer. -/
  inductive TotalPlainValueTypings : List Value → List Ty → Prop where
    | nil : TotalPlainValueTypings [] []
    | cons
        (head : TotalPlainValueTyping value target)
        (tail : TotalPlainValueTypings values targets) :
        TotalPlainValueTypings (value :: values) (target :: targets)

  /-- Homogeneous host-list typing in the extended layer. -/
  inductive TotalPlainListValueTypings : List Value → Ty → Prop where
    | nil : TotalPlainListValueTypings [] element
    | cons
        (head : TotalPlainValueTyping value element)
        (tail : TotalPlainListValueTypings values element) :
        TotalPlainListValueTypings (value :: values) element

end

/-- Newest-first runtime environments in the plain-total layer. -/
abbrev TotalPlainEnvironmentTyping := TotalPlainValueTypings

namespace TotalPlainValueTypings

/-- Every existing total environment embeds into the extended layer. -/
theorem ofTotal
    (typing : TotalValueTypings values targets) :
    TotalPlainValueTypings values targets := by
  cases typing with
  | nil => exact .nil
  | cons head tail => exact .cons (.existing head) (ofTotal tail)

/-- Lookup preserves the extended value type. -/
theorem lookup
    {index : Nat}
    (typing : TotalPlainValueTypings values targets)
    (found : targets[index]? = some target) :
    ∃ value, values[index]? = some value ∧
      TotalPlainValueTyping value target := by
  induction index generalizing values targets with
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

/-- Concatenation preserves pointwise typing and source order. -/
theorem append
    (left : TotalPlainValueTypings leftValues leftTargets)
    (right : TotalPlainValueTypings rightValues rightTargets) :
    TotalPlainValueTypings (leftValues ++ rightValues)
      (leftTargets ++ rightTargets) := by
  induction leftValues generalizing leftTargets with
  | nil =>
      cases left
      simpa using right
  | cons value values induction =>
      cases left with
      | cons head tail => exact .cons head (induction tail)

end TotalPlainValueTypings

namespace TotalPlainListValueTypings

/-- Old homogeneous lists embed pointwise. -/
theorem ofOld
    : ∀ {values element},
      ListValueTypings values element →
      TotalPlainListValueTypings values element
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (.existing (.ordinary head)) (ofOld tail)

/-- Homogeneous concatenation used by `append`. -/
theorem append
    (left : TotalPlainListValueTypings leftValues element)
    (right : TotalPlainListValueTypings rightValues element) :
    TotalPlainListValueTypings (leftValues ++ rightValues) element := by
  induction leftValues with
  | nil =>
      cases left
      simpa using right
  | cons value values induction =>
      cases left with
      | cons head tail => exact .cons head (induction tail)

end TotalPlainListValueTypings

namespace TotalPlainValueTyping

/-- Canonical form for functions in the extended layer.  Both ordinary and
recursive closures expose their total captured environment and structural
body certificate. -/
theorem function_canonical
    (typing : TotalPlainValueTyping value (.fn domain codomain)) :
      (∃ environment context bodyExpression,
        value = Value.plainClosure environment bodyExpression ∧
        TotalPlainEnvironmentTyping environment context ∧
        TotalRecursiveClosureBodyTyping (domain :: context) bodyExpression
          codomain) ∨
      (∃ environment context bodyExpression,
        value = Value.recursiveClosure environment bodyExpression ∧
        TotalPlainEnvironmentTyping environment context ∧
        TotalRecursiveClosureBodyTyping
          (domain :: .fn domain codomain :: context) bodyExpression codomain) := by
  cases typing with
  | existing old =>
      rcases old.function_canonical with
        ⟨environment, context, body, rfl, environmentTyped, bodyTyped⟩ |
        ⟨environment, context, body, rfl, environmentTyped, bodyTyped⟩
      · exact .inl ⟨environment, context, body, rfl,
          TotalPlainValueTypings.ofTotal environmentTyped, bodyTyped⟩
      · exact .inr ⟨environment, context, body, rfl,
          TotalPlainValueTypings.ofTotal environmentTyped, bodyTyped⟩
  | plainClosure environment body =>
      exact .inl ⟨_, _, _, rfl, environment, body⟩

/-- Canonical form for Lists whose elements may themselves be extended
closures. -/
theorem list_canonical
    (typing : TotalPlainValueTyping value (TypePM.DataTypes.list element)) :
    ∃ values, value = Value.buildList values ∧
      TotalPlainListValueTypings values element := by
  cases typing with
  | existing old =>
      cases old with
      | ordinary source =>
          obtain ⟨values, equality, items⟩ := source.list_canonical
          exact ⟨values, equality, TotalPlainListValueTypings.ofOld items⟩
  | list items => exact ⟨_, rfl, items⟩

/-- Canonical form for tuples whose fields may include extended closures. -/
theorem product_canonical
    (typing : TotalPlainValueTyping value (.prod targets)) :
    ∃ values, value = .tuple values ∧ TotalPlainValueTypings values targets := by
  cases typing with
  | existing old =>
      cases old with
      | ordinary source =>
          obtain ⟨values, equality, items⟩ := source.product_canonical
          exact ⟨values, equality,
            TotalPlainValueTypings.ofTotal
              (TotalValueTypings.ofValueTypings items)⟩
  | tuple items => exact ⟨_, rfl, items⟩

end TotalPlainValueTyping

/-- Typed evaluation result in the extended layer. -/
def TotalPlainTypedResult (target : Ty) (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧ TotalPlainValueTyping value target

namespace TotalPlainTypedResult

theorem notStuck
    (typed : TotalPlainTypedResult target result) : result.NotStuck := by
  rcases typed with timeout | ⟨value, success, valueTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TotalPlainTypedResult

/-- Expression safety under environments that may contain both recursive
matcher closures and ordinary closures capturing such values. -/
def TotalPlainEnvironmentSafe (expression : Source.Expr) (target : Ty)
    (context : List Ty) : Prop :=
  ∀ fuel environment,
    TotalPlainEnvironmentTyping environment context →
      TotalPlainTypedResult target (evalFuel fuel environment expression)

/-- Typed left-to-right evaluation of a source expression list. -/
def TotalPlainTypedResults (targets : List Ty)
    (result : FuelResult (List Value)) : Prop :=
  result = .timeout ∨
    ∃ values, result = .ok values ∧ TotalPlainValueTypings values targets

/-- Pointwise expression safety, used by tuple and constructor evaluation. -/
inductive TotalPlainExpressionsSafe (context : List Ty) :
    List Source.Expr → List Ty → Prop where
  | nil : TotalPlainExpressionsSafe context [] []
  | cons
      (head : TotalPlainEnvironmentSafe expression target context)
      (tail : TotalPlainExpressionsSafe context expressions targets) :
      TotalPlainExpressionsSafe context (expression :: expressions)
        (target :: targets)

namespace TotalPlainExpressionsSafe

/-- Pointwise safety follows the evaluator's exact traversal order. -/
theorem traverse
    (safe : TotalPlainExpressionsSafe context expressions targets)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyped : TotalPlainEnvironmentTyping environment context) :
    TotalPlainTypedResults targets
      (FuelResult.traverse (evalFuel fuel environment) expressions) := by
  induction safe with
  | nil => exact .inr ⟨[], rfl, .nil⟩
  | cons head tail induction =>
      rcases head fuel environment environmentTyped with headTimeout |
        ⟨headValue, headSuccess, headTyped⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · rcases induction with tailTimeout |
          ⟨tailValues, tailSuccess, tailTyped⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], .cons headTyped tailTyped⟩

end TotalPlainExpressionsSafe

/-- A typed function value together with the dynamic body fact needed to
apply it.  Keeping this separate avoids placing a negative recursive use of
expression safety inside the inductive value judgment. -/
structure TotalPlainFunctionSafe
    (value : Value) (domain codomain : Ty) : Prop where
  typed : TotalPlainValueTyping value (.fn domain codomain)
  applyTyped : ∀ fuel argument,
    TotalPlainValueTyping argument domain →
      TotalPlainTypedResult codomain (applyFuel fuel value argument)

/-- Evaluation of a function expression either times out or produces a
function that is safe to apply. -/
def TotalPlainFunctionResult (domain codomain : Ty)
    (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧
      TotalPlainFunctionSafe value domain codomain

/-- Function-expression form of `TotalPlainEnvironmentSafe`. -/
def TotalPlainFunctionEnvironmentSafe (expression : Source.Expr)
    (domain codomain : Ty) (context : List Ty) : Prop :=
  ∀ fuel environment,
    TotalPlainEnvironmentTyping environment context →
      TotalPlainFunctionResult domain codomain
        (evalFuel fuel environment expression)

namespace TotalPlainFunctionResult

theorem toTypedResult
    (safe : TotalPlainFunctionResult domain codomain result) :
    TotalPlainTypedResult (.fn domain codomain) result := by
  rcases safe with timeout | ⟨value, success, functionSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, functionSafe.typed⟩

end TotalPlainFunctionResult

/-- Direct application of a plain closure over a total environment. -/
theorem applyFuel_totalPlainClosure_typed
    (environmentTyped : TotalPlainEnvironmentTyping environment context)
    (_bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: context) body codomain)
    (bodySafe : TotalPlainEnvironmentSafe body codomain (domain :: context))
    (argumentTyped : TotalPlainValueTyping argument domain)
    (fuel : Nat) :
    TotalPlainTypedResult codomain
      (applyFuel fuel (Value.plainClosure environment body) argument) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ bodyFuel =>
      exact bodySafe bodyFuel (argument :: environment)
        (.cons argumentTyped environmentTyped)

/-- No-stuck corollary for direct application of the extended plain
closure. -/
theorem applyFuel_totalPlainClosure_neverStuck
    (environmentTyped : TotalPlainEnvironmentTyping environment context)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: context) body codomain)
    (bodySafe : TotalPlainEnvironmentSafe body codomain (domain :: context))
    (argumentTyped : TotalPlainValueTyping argument domain)
    (fuel : Nat) :
    (applyFuel fuel (Value.plainClosure environment body) argument).NotStuck :=
  (applyFuel_totalPlainClosure_typed environmentTyped bodyTyped bodySafe
    argumentTyped fuel).notStuck

/-- A lambda evaluated in a total environment produces an applicable plain
closure. -/
theorem totalPlainFunctionEnvironmentSafe_lam
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: context) body codomain)
    (bodySafe : TotalPlainEnvironmentSafe body codomain (domain :: context)) :
    TotalPlainFunctionEnvironmentSafe (.lam body) domain codomain context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨Value.plainClosure environment body, rfl,
        ⟨.plainClosure environmentTyped bodyTyped,
          fun applyFuel argument argumentTyped =>
            applyFuel_totalPlainClosure_typed environmentTyped bodyTyped
              bodySafe argumentTyped applyFuel⟩⟩

/-- Plain lambda construction as ordinary expression safety. -/
theorem totalPlainEnvironmentSafe_lam
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: context) body codomain)
    (bodySafe : TotalPlainEnvironmentSafe body codomain (domain :: context)) :
    TotalPlainEnvironmentSafe (.lam body) (.fn domain codomain) context := by
  intro fuel environment environmentTyped
  exact (totalPlainFunctionEnvironmentSafe_lam bodyTyped bodySafe fuel
    environment environmentTyped).toTypedResult

/-- Variables are safe in the extended environment. -/
theorem totalPlainEnvironmentSafe_var
    (found : context[index]? = some target) :
    TotalPlainEnvironmentSafe (.var index) target context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      obtain ⟨value, valueFound, valueTyped⟩ := environmentTyped.lookup found
      exact .inr ⟨value, by simp [evalFuel, valueFound], valueTyped⟩

/-- Integer literals are independent of the captured environment. -/
theorem totalPlainEnvironmentSafe_lit (literal : Int) :
    TotalPlainEnvironmentSafe (.lit literal) .int context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨.int literal, rfl, .existing (.ordinary (.int literal))⟩

/-- Tuple construction preserves all field types, including extended closure
fields. -/
theorem totalPlainEnvironmentSafe_tuple
    (itemsSafe : TotalPlainExpressionsSafe context expressions targets) :
    TotalPlainEnvironmentSafe (.tuple expressions) (.prod targets) context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      rcases itemsSafe.traverse childFuel environment environmentTyped with
        timeout | ⟨values, success, valuesTyped⟩
      · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
      · exact .inr ⟨.tuple values, by
          simp [evalFuel, success, FuelResult.map], .tuple valuesTyped⟩

/-- Canonical Boolean constructors are independent of the environment. -/
theorem totalPlainEnvironmentSafe_boolTrue :
    TotalPlainEnvironmentSafe (.ctor DataCtor.true [])
      TypePM.DataTypes.bool context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      exact .inr ⟨Value.boolValue true, by
        simp [evalFuel, FuelResult.traverse, FuelResult.map, Value.boolValue],
        .existing (.ordinary .boolTrue)⟩

theorem totalPlainEnvironmentSafe_boolFalse :
    TotalPlainEnvironmentSafe (.ctor DataCtor.false [])
      TypePM.DataTypes.bool context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      exact .inr ⟨Value.boolValue false, by
        simp [evalFuel, FuelResult.traverse, FuelResult.map, Value.boolValue],
        .existing (.ordinary .boolFalse)⟩

/-- Empty and nonempty canonical Lists remain in the extended homogeneous
list judgment. -/
theorem totalPlainEnvironmentSafe_listNil :
    TotalPlainEnvironmentSafe (.ctor DataCtor.nil [])
      (TypePM.DataTypes.list element) context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      exact .inr ⟨Value.buildList [], by
        simp [evalFuel, FuelResult.traverse, FuelResult.map,
          Value.buildList, Value.nilValue], .list .nil⟩

theorem totalPlainEnvironmentSafe_listCons
    (headSafe : TotalPlainEnvironmentSafe headExpression element context)
    (tailSafe : TotalPlainEnvironmentSafe tailExpression
      (TypePM.DataTypes.list element) context) :
    TotalPlainEnvironmentSafe
      (.ctor DataCtor.cons [headExpression, tailExpression])
      (TypePM.DataTypes.list element) context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      have children := (TotalPlainExpressionsSafe.cons headSafe
        (TotalPlainExpressionsSafe.cons tailSafe
          TotalPlainExpressionsSafe.nil)).traverse
            childFuel environment environmentTyped
      rcases children with timeout | ⟨values, success, valuesTyped⟩
      · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
      · cases valuesTyped with
        | cons headTyped tailTypes =>
            cases tailTypes with
            | cons tailTyped nilTypes =>
                cases nilTypes
                obtain ⟨tailValues, tailEq, tailValuesTyped⟩ :=
                  tailTyped.list_canonical
                subst tailEq
                exact .inr ⟨Value.buildList (_ :: tailValues), by
                  simp [evalFuel, success, FuelResult.map,
                    Value.buildList, Value.consValue],
                  .list (.cons headTyped tailValuesTyped)⟩

/-- Pair projections preserve the corresponding field type. -/
theorem totalPlainEnvironmentSafe_pairFirst
    (pairSafe : TotalPlainEnvironmentSafe pairExpression
      (.prod [firstTarget, secondTarget]) context) :
    TotalPlainEnvironmentSafe
      (.prim PrimOp.pairFirst [pairExpression]) firstTarget context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      rcases pairSafe childFuel environment environmentTyped with
        pairTimeout | ⟨pairValue, pairSuccess, pairTyped⟩
      · exact .inl (by
          simp [evalFuel, FuelResult.traverse, pairTimeout, FuelResult.bind])
      · obtain ⟨values, pairEq, valuesTyped⟩ := pairTyped.product_canonical
        subst pairValue
        cases valuesTyped with
        | cons firstTyped tailTyped =>
            cases tailTyped with
            | cons secondTyped nilTyped =>
                cases nilTyped
                exact .inr ⟨_, by
                  simp [evalFuel, FuelResult.traverse, pairSuccess,
                    evalPrimitive, FuelResult.bind], firstTyped⟩

theorem totalPlainEnvironmentSafe_pairSecond
    (pairSafe : TotalPlainEnvironmentSafe pairExpression
      (.prod [firstTarget, secondTarget]) context) :
    TotalPlainEnvironmentSafe
      (.prim PrimOp.pairSecond [pairExpression]) secondTarget context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      rcases pairSafe childFuel environment environmentTyped with
        pairTimeout | ⟨pairValue, pairSuccess, pairTyped⟩
      · exact .inl (by
          simp [evalFuel, FuelResult.traverse, pairTimeout, FuelResult.bind])
      · obtain ⟨values, pairEq, valuesTyped⟩ := pairTyped.product_canonical
        subst pairValue
        cases valuesTyped with
        | cons firstTyped tailTyped =>
            cases tailTyped with
            | cons secondTyped nilTyped =>
                cases nilTyped
                exact .inr ⟨_, by
                  simp [evalFuel, FuelResult.traverse, pairSuccess,
                    evalPrimitive, FuelResult.bind], secondTyped⟩

/-- List append preserves the extended element judgment. -/
theorem totalPlainEnvironmentSafe_append
    (leftSafe : TotalPlainEnvironmentSafe leftExpression
      (TypePM.DataTypes.list element) context)
    (rightSafe : TotalPlainEnvironmentSafe rightExpression
      (TypePM.DataTypes.list element) context) :
    TotalPlainEnvironmentSafe
      (.prim PrimOp.append [leftExpression, rightExpression])
      (TypePM.DataTypes.list element) context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      have children := (TotalPlainExpressionsSafe.cons leftSafe
        (TotalPlainExpressionsSafe.cons rightSafe
          TotalPlainExpressionsSafe.nil)).traverse
            childFuel environment environmentTyped
      rcases children with timeout | ⟨values, success, valuesTyped⟩
      · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
      · cases valuesTyped with
        | cons leftTyped tailTyped =>
            cases tailTyped with
            | cons rightTyped nilTyped =>
                cases nilTyped
                obtain ⟨leftValues, leftEq, leftValuesTyped⟩ :=
                  leftTyped.list_canonical
                obtain ⟨rightValues, rightEq, rightValuesTyped⟩ :=
                  rightTyped.list_canonical
                subst leftEq
                subst rightEq
                exact .inr ⟨Value.buildList (leftValues ++ rightValues), by
                  simp [evalFuel, success, evalPrimitive, FuelResult.bind],
                  .list (leftValuesTyped.append rightValuesTyped)⟩

/-- Additional environment invariant needed when a variable is used as a
function.  Structural environment typing alone cannot imply this property:
it records a closure body's type, but deliberately does not record that the
body is dynamically safe. -/
def TotalPlainFunctionLookupSafe (index : Nat) (domain codomain : Ty)
    (context : List Ty) : Prop :=
  ∀ environment,
    TotalPlainEnvironmentTyping environment context →
      ∃ function,
        environment[index]? = some function ∧
        TotalPlainFunctionSafe function domain codomain

/-- Typed binding groups returned by one concrete pattern search. -/
def TotalPlainMatchingAnswersTyping
    (answers : List (List Value)) (bindingTypes : List Ty) : Prop :=
  ∀ bindings ∈ answers, TotalPlainValueTypings bindings bindingTypes

/-- Dynamic search certificate tied to the actual evaluator, pattern,
matcher value, and target value.  This is deliberately weaker than assuming
the result of `matchAll`: it certifies only the search phase and retains the
exact successful binding groups. -/
def TotalPlainPatternSearchSafe
    (pattern : Source.Pattern) (matcherTarget : Ty) (capability : Cap)
    (bindingTypes context : List Ty) : Prop :=
  ∀ fuel environment target matcher,
    TotalPlainEnvironmentTyping environment context →
    TotalPlainValueTyping target matcherTarget →
    TotalPlainValueTyping matcher (.matcher capability matcherTarget) →
      searchPatternFuel (evalFuel fuel) fuel environment pattern matcher target =
          .timeout ∨
        ∃ answers,
          searchPatternFuel (evalFuel fuel) fuel environment pattern matcher
              target = .ok answers ∧
          TotalPlainMatchingAnswersTyping answers bindingTypes

private theorem traverseTotalPlainMatchingBodies
    (bodySafe : TotalPlainEnvironmentSafe body bodyTarget
      (bindingTypes ++ context))
    (environmentTyped : TotalPlainEnvironmentTyping environment context)
    (answersTyped : TotalPlainMatchingAnswersTyping answers bindingTypes)
    (fuel : Nat) :
    (FuelResult.traverse
      (fun bindings => evalFuel fuel (bindings ++ environment) body)
      answers = .timeout) ∨
      ∃ values,
        FuelResult.traverse
          (fun bindings => evalFuel fuel (bindings ++ environment) body)
          answers = .ok values ∧
        TotalPlainListValueTypings values bodyTarget := by
  induction answers with
  | nil => exact .inr ⟨[], rfl, .nil⟩
  | cons bindings rest induction =>
      have bindingsTyped := answersTyped bindings (by simp)
      have restTyped : TotalPlainMatchingAnswersTyping rest bindingTypes := by
        intro candidate member
        exact answersTyped candidate (by simp [member])
      rcases bodySafe fuel (bindings ++ environment)
          (bindingsTyped.append environmentTyped) with bodyTimeout |
          ⟨value, bodySuccess, valueTyped⟩
      · exact .inl (by simp [FuelResult.traverse, bodyTimeout])
      · rcases induction restTyped with restTimeout |
          ⟨values, restSuccess, valuesTyped⟩
        · exact .inl (by
            simp [FuelResult.traverse, bodySuccess, restTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨value :: values, by
            simp [FuelResult.traverse, bodySuccess, restSuccess,
              FuelResult.bind, FuelResult.map], .cons valueTyped valuesTyped⟩

/-- A function-variable expression is safe exactly when the environment
invariant supplies the dynamic application certificate at that index. -/
theorem totalPlainFunctionEnvironmentSafe_var
    (lookupSafe : TotalPlainFunctionLookupSafe index domain codomain context) :
    TotalPlainFunctionEnvironmentSafe (.var index) domain codomain context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      obtain ⟨function, found, functionSafe⟩ :=
        lookupSafe environment environmentTyped
      exact .inr ⟨function, by simp [evalFuel, found], functionSafe⟩

/-- Application is safe when the function expression produces an applicable
function and the argument expression is safe. -/
theorem totalPlainEnvironmentSafe_app
    (functionSafe : TotalPlainFunctionEnvironmentSafe functionExpression
      domain codomain context)
    (argumentSafe : TotalPlainEnvironmentSafe argumentExpression domain context) :
    TotalPlainEnvironmentSafe (.app functionExpression argumentExpression)
      codomain context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ applicationFuel =>
      rcases functionSafe applicationFuel environment environmentTyped with
        functionTimeout | ⟨functionValue, functionSuccess, functionValueSafe⟩
      · exact .inl (by
          simp [evalFuel, functionTimeout, FuelResult.bind])
      · rcases argumentSafe applicationFuel environment environmentTyped with
          argumentTimeout | ⟨argumentValue, argumentSuccess, argumentTyped⟩
        · exact .inl (by
            simp [evalFuel, functionSuccess, argumentTimeout,
              FuelResult.bind])
        · rcases functionValueSafe.applyTyped applicationFuel argumentValue
              argumentTyped with applicationTimeout |
              ⟨value, applicationSuccess, valueTyped⟩
          · exact .inl (by
              simp [evalFuel, functionSuccess, argumentSuccess,
                applicationTimeout, FuelResult.bind])
          · exact .inr ⟨value, by
              simp [evalFuel, functionSuccess, argumentSuccess,
                applicationSuccess, FuelResult.bind], valueTyped⟩

/-- `matchAll` safety from an evaluation-indexed certificate for its exact
pattern search.  User-matcher recursion is not hidden here: it must be used
to construct `matcherSafe` and `searchSafe` for the concrete matcher. -/
theorem totalPlainEnvironmentSafe_matchAll
    (targetSafe : TotalPlainEnvironmentSafe targetExpression matcherTarget context)
    (matcherSafe : TotalPlainEnvironmentSafe matcherExpression
      (.matcher capability matcherTarget) context)
    (searchSafe : TotalPlainPatternSearchSafe pattern matcherTarget capability
      bindingTypes context)
    (bodySafe : TotalPlainEnvironmentSafe bodyExpression bodyTarget
      (bindingTypes ++ context)) :
    TotalPlainEnvironmentSafe
      (.matchAll targetExpression matcherExpression pattern bodyExpression)
      (TypePM.DataTypes.list bodyTarget) context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      rcases targetSafe childFuel environment environmentTyped with
        targetTimeout | ⟨targetValue, targetSuccess, targetTyped⟩
      · exact .inl (by simp [evalFuel, targetTimeout, FuelResult.bind])
      · rcases matcherSafe childFuel environment environmentTyped with
          matcherTimeout | ⟨matcherValue, matcherSuccess, matcherTyped⟩
        · exact .inl (by
            simp [evalFuel, targetSuccess, matcherTimeout, FuelResult.bind])
        · rcases searchSafe childFuel environment targetValue matcherValue
              environmentTyped targetTyped matcherTyped with searchTimeout |
              ⟨answers, searchSuccess, answersTyped⟩
          · exact .inl (by
              simp [evalFuel, targetSuccess, matcherSuccess, searchTimeout,
                FuelResult.bind])
          · rcases traverseTotalPlainMatchingBodies bodySafe environmentTyped
                answersTyped childFuel with bodyTimeout |
                ⟨values, bodySuccess, valuesTyped⟩
            · exact .inl (by
                simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
                  bodyTimeout, FuelResult.bind, FuelResult.map])
            · exact .inr ⟨Value.buildList values, by
                simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
                  bodySuccess, FuelResult.bind, FuelResult.map],
                .list valuesTyped⟩

/-- Monomorphic let extends the total environment with the value produced by
its left-hand side. -/
theorem totalPlainEnvironmentSafe_letE
    (valueSafe : TotalPlainEnvironmentSafe valueExpression valueTarget context)
    (bodySafe : TotalPlainEnvironmentSafe body bodyTarget
      (valueTarget :: context)) :
    TotalPlainEnvironmentSafe (.letE valueExpression body) bodyTarget context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      rcases valueSafe childFuel environment environmentTyped with
        valueTimeout | ⟨value, valueSuccess, valueTyped⟩
      · exact .inl (by simp [evalFuel, valueTimeout, FuelResult.bind])
      · rcases bodySafe childFuel (value :: environment)
            (.cons valueTyped environmentTyped) with bodyTimeout |
            ⟨result, bodySuccess, resultTyped⟩
        · exact .inl (by
            simp [evalFuel, valueSuccess, bodyTimeout, FuelResult.bind])
        · exact .inr ⟨result, by
            simp [evalFuel, valueSuccess, bodySuccess, FuelResult.bind],
            resultTyped⟩

namespace TotalPlainListValueTypings

/-- Pointwise applicable-function safety lifts through the evaluator's
left-to-right traversal used by `map`. -/
theorem traverseApplyTyped
    (functionSafe : TotalPlainFunctionSafe function domain codomain)
    (fuel : Nat) :
    ∀ {values}, TotalPlainListValueTypings values domain →
      (FuelResult.traverse (applyFuel fuel function) values = .timeout) ∨
        ∃ outputs,
          FuelResult.traverse (applyFuel fuel function) values = .ok outputs ∧
          TotalPlainListValueTypings outputs codomain
  | _, .nil => .inr ⟨[], rfl, .nil⟩
  | _, .cons head tail => by
      rcases functionSafe.applyTyped fuel _ head with headTimeout |
        ⟨output, headSuccess, outputTyped⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · rcases traverseApplyTyped functionSafe fuel tail with tailTimeout |
          ⟨outputs, tailSuccess, outputsTyped⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨output :: outputs, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], .cons outputTyped outputsTyped⟩

end TotalPlainListValueTypings

/-- `map` is safe for functions whose application certificate is retained by
the function-expression safety premise. -/
theorem totalPlainEnvironmentSafe_map
    (functionSafe : TotalPlainFunctionEnvironmentSafe functionExpression
      domain codomain context)
    (targetSafe : TotalPlainEnvironmentSafe targetExpression
      (TypePM.DataTypes.list domain) context) :
    TotalPlainEnvironmentSafe
      (.prim PrimOp.map [functionExpression, targetExpression])
      (TypePM.DataTypes.list codomain) context := by
  intro fuel environment environmentTyped
  cases fuel with
  | zero => exact .inl rfl
  | succ primitiveFuel =>
      rcases functionSafe primitiveFuel environment environmentTyped with
        functionTimeout | ⟨functionValue, functionSuccess, functionValueSafe⟩
      · exact .inl (by
          simp [evalFuel, FuelResult.traverse, functionTimeout,
            FuelResult.bind])
      · rcases targetSafe primitiveFuel environment environmentTyped with
          targetTimeout | ⟨targetValue, targetSuccess, targetTyped⟩
        · exact .inl (by
            simp [evalFuel, FuelResult.traverse, functionSuccess,
              targetTimeout, FuelResult.bind, FuelResult.map])
        · obtain ⟨inputs, targetEq, inputsTyped⟩ := targetTyped.list_canonical
          subst targetValue
          rcases inputsTyped.traverseApplyTyped functionValueSafe primitiveFuel with
            mappedTimeout | ⟨outputs, mappedSuccess, outputsTyped⟩
          · exact .inl (by
              simp [evalFuel, FuelResult.traverse, functionSuccess,
                targetSuccess, evalPrimitive, mappedTimeout, FuelResult.bind,
                FuelResult.map])
          · exact .inr ⟨Value.buildList outputs, by
              simp [evalFuel, FuelResult.traverse, functionSuccess,
                targetSuccess, evalPrimitive, mappedSuccess, FuelResult.bind,
                FuelResult.map], .list outputsTyped⟩

end TypePM.Runtime
