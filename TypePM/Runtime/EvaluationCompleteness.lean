import TypePM.Runtime.EvaluationAdequacy

/-!
# Fuel monotonicity and finite completeness

A completed evaluation is stable under additional fuel.  Conversely, every
finite big-step derivation has a finite fuel bound.  These properties cover
ordinary and recursive closures and the callback applications of `map`.
-/

namespace TypePM.Runtime

open FuelResult

private theorem traverse_ok_mono
    {before after : α → FuelResult β}
    (monotone : ∀ {input output},
      before input = .ok output → after input = .ok output)
    {inputs : List α} {outputs : List β}
    (success : FuelResult.traverse before inputs = .ok outputs) :
    FuelResult.traverse after inputs = .ok outputs := by
  rw [traverse_eq_ok_iff] at success ⊢
  induction success with
  | nil => exact .nil
  | cons head tail ih => exact .cons (monotone head) ih

private theorem evalPrimitive_ok_mono
    {before after : Value → Value → FuelResult Value}
    (monotone : ∀ {function input output},
      before function input = .ok output →
        after function input = .ok output)
    {operation : PrimOp} {arguments : List Value} {result : Value}
    (success : evalPrimitive before operation arguments = .ok result) :
    evalPrimitive after operation arguments = .ok result := by
  cases operation with
  | add =>
      rcases arguments with _ | ⟨first, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨second, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · cases first <;> cases second <;> simpa [evalPrimitive] using success
      · simp [evalPrimitive] at success
  | append =>
      rcases arguments with _ | ⟨left, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨right, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · exact success
      · simp [evalPrimitive] at success
  | member =>
      rcases arguments with _ | ⟨needle, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨target, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · exact success
      · simp [evalPrimitive] at success
  | deleteFirst =>
      rcases arguments with _ | ⟨needle, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨target, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · exact success
      · simp [evalPrimitive] at success
  | map =>
      rcases arguments with _ | ⟨function, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨target, tail⟩
      · simp [evalPrimitive] at success
      rcases tail with _ | ⟨extra, tail⟩
      · cases targetView : Value.viewList target with
        | none => simp [evalPrimitive, targetView] at success
        | some inputs =>
            simp only [evalPrimitive, targetView, FuelResult.map] at success
            cases oldTraversal : FuelResult.traverse (before function) inputs with
            | timeout => simp [oldTraversal] at success
            | stuck => simp [oldTraversal] at success
            | ok outputs =>
                simp [oldTraversal] at success
                subst result
                have newTraversal := traverse_ok_mono
                  (fun application => monotone application) oldTraversal
                simp [evalPrimitive, targetView, newTraversal]
      · simp [evalPrimitive] at success

private theorem fuel_ok_succ : ∀ fuel,
    (∀ {environment expression value},
      evalFuel fuel environment expression = .ok value →
        evalFuel (fuel + 1) environment expression = .ok value) ∧
    (∀ {function argument value},
      applyFuel fuel function argument = .ok value →
        applyFuel (fuel + 1) function argument = .ok value) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro environment expression value success
        simp [evalFuel] at success
      · intro function argument value success
        simp [applyFuel] at success
  | succ fuel ih =>
      rcases ih with ⟨evalStep, applyStep⟩
      constructor
      · intro environment expression value success
        cases expression with
        | var index => simpa [evalFuel] using success
        | lit literal => simpa [evalFuel] using success
        | something => simpa [evalFuel] using success
        | lam body => simpa [evalFuel] using success
        | app function argument =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success
            rcases success with ⟨functionValue, functionResult, rest⟩
            rw [bind_eq_ok_iff] at rest
            rcases rest with ⟨argumentValue, argumentResult, application⟩
            rw [bind_eq_ok_iff]
            refine ⟨functionValue, evalStep functionResult, ?_⟩
            rw [bind_eq_ok_iff]
            exact ⟨argumentValue, evalStep argumentResult,
              applyStep application⟩
        | tuple items =>
            simp only [evalFuel] at success ⊢
            rw [map_eq_ok_iff] at success ⊢
            rcases success with ⟨values, traversal, output⟩
            exact ⟨values,
              traverse_ok_mono (fun result => evalStep result) traversal,
              output⟩
        | letE valueExpression body =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success ⊢
            rcases success with ⟨boundValue, boundResult, bodyResult⟩
            exact ⟨boundValue, evalStep boundResult, evalStep bodyResult⟩
        | ctor constructor arguments =>
            simp only [evalFuel] at success ⊢
            rw [map_eq_ok_iff] at success ⊢
            rcases success with ⟨values, traversal, output⟩
            exact ⟨values,
              traverse_ok_mono (fun result => evalStep result) traversal,
              output⟩
        | prim operation arguments =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success ⊢
            rcases success with ⟨values, traversal, primitive⟩
            exact ⟨values,
              traverse_ok_mono (fun result => evalStep result) traversal,
              evalPrimitive_ok_mono
                (fun application => applyStep application) primitive⟩
        | ifE condition thenBranch elseBranch =>
            simp only [evalFuel] at success ⊢
            rw [bind_eq_ok_iff] at success ⊢
            rcases success with ⟨conditionValue, conditionResult, branchResult⟩
            refine ⟨conditionValue, evalStep conditionResult, ?_⟩
            cases conditionValue with
            | data constructor arguments =>
                cases arguments with
                | nil =>
                    by_cases isTrue : constructor = DataCtor.true
                    · subst constructor
                      simp only [if_pos rfl] at branchResult ⊢
                      exact evalStep branchResult
                    · by_cases isFalse : constructor = DataCtor.false
                      · subst constructor
                        have falseNotTrue :
                            DataCtor.false ≠ DataCtor.true := by decide
                        simp only [if_neg falseNotTrue, if_pos rfl] at branchResult ⊢
                        exact evalStep branchResult
                      · simp [isTrue, isFalse] at branchResult
                | cons head tail => simpa using branchResult
            | int literal => simpa using branchResult
            | tuple items => simpa using branchResult
            | closure kind closureEnvironment body => simpa using branchResult
            | matcherV matcherEnvironment original remaining => simpa using branchResult
            | something => simpa using branchResult
        | fixE body => simpa [evalFuel] using success
        | matcher clauses => simpa [evalFuel] using success
        | matchAll target matcher pattern body => simp [evalFuel] at success
      · intro function argument value success
        cases function with
        | closure kind definitionEnvironment body =>
            cases kind with
            | plain =>
                simp only [applyFuel] at success ⊢
                exact evalStep success
            | recursive =>
                simp only [applyFuel] at success ⊢
                exact evalStep success
        | int literal => simp [applyFuel] at success
        | data constructor arguments => simp [applyFuel] at success
        | tuple items => simp [applyFuel] at success
        | matcherV environment original remaining => simp [applyFuel] at success
        | something => simp [applyFuel] at success

theorem evalFuel_ok_succ
    (success : evalFuel fuel environment expression = .ok value) :
    evalFuel (fuel + 1) environment expression = .ok value :=
  (fuel_ok_succ fuel).1 success

theorem applyFuel_ok_succ
    (success : applyFuel fuel function argument = .ok value) :
    applyFuel (fuel + 1) function argument = .ok value :=
  (fuel_ok_succ fuel).2 success

theorem evalFuel_ok_add
    (success : evalFuel fuel environment expression = .ok value)
    (extra : Nat) :
    evalFuel (fuel + extra) environment expression = .ok value := by
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [Nat.add_succ]
      exact evalFuel_ok_succ ih

theorem applyFuel_ok_add
    (success : applyFuel fuel function argument = .ok value)
    (extra : Nat) :
    applyFuel (fuel + extra) function argument = .ok value := by
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [Nat.add_succ]
      exact applyFuel_ok_succ ih

theorem evalFuel_ok_of_le
    (le : firstFuel ≤ secondFuel)
    (success : evalFuel firstFuel environment expression = .ok value) :
    evalFuel secondFuel environment expression = .ok value := by
  have equality : firstFuel + (secondFuel - firstFuel) = secondFuel :=
    Nat.add_sub_of_le le
  rw [← equality]
  exact evalFuel_ok_add success _

theorem applyFuel_ok_of_le
    (le : firstFuel ≤ secondFuel)
    (success : applyFuel firstFuel function argument = .ok value) :
    applyFuel secondFuel function argument = .ok value := by
  have equality : firstFuel + (secondFuel - firstFuel) = secondFuel :=
    Nat.add_sub_of_le le
  rw [← equality]
  exact applyFuel_ok_add success _

theorem Eval.complete
    (derivation : Eval environment expression value) :
    ∃ fuel, evalFuel fuel environment expression = .ok value := by
  apply Eval.rec
    (motive_1 := fun environment expression value _ =>
      ∃ fuel, evalFuel fuel environment expression = .ok value)
    (motive_2 := fun environment expressions values _ =>
      ∃ fuel,
        FuelResult.traverse (evalFuel fuel environment) expressions =
          .ok values)
    (motive_3 := fun function argument value _ =>
      ∃ fuel, applyFuel fuel function argument = .ok value)
    (motive_4 := fun function inputs outputs _ =>
      ∃ fuel,
        FuelResult.traverse (applyFuel fuel function) inputs = .ok outputs)
    (motive_5 := fun operation arguments value _ =>
      ∃ fuel,
        evalPrimitive (applyFuel fuel) operation arguments = .ok value)
  case var =>
      intros environment index value lookup
      refine ⟨1, ?_⟩
      simp [evalFuel, (getElem?_eq_some_iff_lookup _ _ _).mpr lookup]
  case lit =>
      intros environment literal
      exact ⟨1, rfl⟩
  case something =>
      intro environment
      exact ⟨1, rfl⟩
  case lam =>
      intros environment body
      exact ⟨1, rfl⟩
  case app =>
      intros environment function functionValue argument argumentValue result
        functionEval argumentEval application functionIH argumentIH applicationIH
      rcases functionIH with ⟨functionFuel, functionSuccess⟩
      rcases argumentIH with ⟨argumentFuel, argumentSuccess⟩
      rcases applicationIH with ⟨applicationFuel, applicationSuccess⟩
      let common := max functionFuel (max argumentFuel applicationFuel)
      have functionLe : functionFuel ≤ common := Nat.le_max_left _ _
      have argumentLe : argumentFuel ≤ common :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have applicationLe : applicationFuel ≤ common :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      refine ⟨common + 1, ?_⟩
      simp [evalFuel,
        evalFuel_ok_of_le functionLe functionSuccess,
        evalFuel_ok_of_le argumentLe argumentSuccess,
        applyFuel_ok_of_le applicationLe applicationSuccess]
  case tuple =>
      intros environment items values itemsEval itemsIH
      rcases itemsIH with ⟨fuel, success⟩
      refine ⟨fuel + 1, ?_⟩
      simp [evalFuel, success]
  case letE =>
      intros environment valueExpression value body result valueEval bodyEval
        valueIH bodyIH
      rcases valueIH with ⟨valueFuel, valueSuccess⟩
      rcases bodyIH with ⟨bodyFuel, bodySuccess⟩
      let common := max valueFuel bodyFuel
      have valueRaised := evalFuel_ok_of_le
        (Nat.le_max_left valueFuel bodyFuel) valueSuccess
      have bodyRaised := evalFuel_ok_of_le
        (Nat.le_max_right valueFuel bodyFuel) bodySuccess
      refine ⟨common + 1, ?_⟩
      dsimp [common]
      simp only [evalFuel, valueRaised, FuelResult.bind_ok, bodyRaised]
  case ctor =>
      intros environment arguments values constructor argumentsEval argumentsIH
      rcases argumentsIH with ⟨fuel, success⟩
      refine ⟨fuel + 1, ?_⟩
      simp [evalFuel, success]
  case prim =>
      intros environment arguments values operation result argumentsEval primitive
        argumentsIH primitiveIH
      rcases argumentsIH with ⟨argumentsFuel, argumentsSuccess⟩
      rcases primitiveIH with ⟨primitiveFuel, primitiveSuccess⟩
      let common := max argumentsFuel primitiveFuel
      have argumentsRaised := traverse_ok_mono
        (fun application => evalFuel_ok_of_le
          (Nat.le_max_left argumentsFuel primitiveFuel) application)
        argumentsSuccess
      have primitiveRaised := evalPrimitive_ok_mono
        (fun application => applyFuel_ok_of_le
          (Nat.le_max_right argumentsFuel primitiveFuel) application)
        primitiveSuccess
      refine ⟨common + 1, ?_⟩
      dsimp [common]
      simp only [evalFuel, argumentsRaised, FuelResult.bind_ok,
        primitiveRaised]
  case ifTrue =>
      intros environment condition thenBranch result elseBranch conditionEval
        branchEval conditionIH branchIH
      rcases conditionIH with ⟨conditionFuel, conditionSuccess⟩
      rcases branchIH with ⟨branchFuel, branchSuccess⟩
      let common := max conditionFuel branchFuel
      have conditionRaised := evalFuel_ok_of_le
        (Nat.le_max_left conditionFuel branchFuel) conditionSuccess
      have branchRaised := evalFuel_ok_of_le
        (Nat.le_max_right conditionFuel branchFuel) branchSuccess
      refine ⟨common + 1, ?_⟩
      dsimp [common]
      simp [evalFuel, conditionRaised, branchRaised]
  case ifFalse =>
      intros environment condition elseBranch result thenBranch conditionEval
        branchEval conditionIH branchIH
      rcases conditionIH with ⟨conditionFuel, conditionSuccess⟩
      rcases branchIH with ⟨branchFuel, branchSuccess⟩
      let common := max conditionFuel branchFuel
      have falseNotTrue : DataCtor.false ≠ DataCtor.true := by decide
      have conditionRaised := evalFuel_ok_of_le
        (Nat.le_max_left conditionFuel branchFuel) conditionSuccess
      have branchRaised := evalFuel_ok_of_le
        (Nat.le_max_right conditionFuel branchFuel) branchSuccess
      refine ⟨common + 1, ?_⟩
      dsimp [common]
      simp [evalFuel, conditionRaised, branchRaised, falseNotTrue]
  case fixE =>
      intros environment body
      exact ⟨1, rfl⟩
  case matcher =>
      intros environment clauses
      exact ⟨1, rfl⟩
  case nil =>
      intro environment
      exact ⟨0, rfl⟩
  case cons =>
      intros environment head value tail values headEval tailEval headIH tailIH
      rcases headIH with ⟨headFuel, headSuccess⟩
      rcases tailIH with ⟨tailFuel, tailSuccess⟩
      let common := max headFuel tailFuel
      have headRaised := evalFuel_ok_of_le
        (Nat.le_max_left headFuel tailFuel) headSuccess
      have tailRaised := traverse_ok_mono
        (fun application => evalFuel_ok_of_le
          (Nat.le_max_right headFuel tailFuel) application)
        tailSuccess
      refine ⟨common, ?_⟩
      dsimp [common]
      simp only [FuelResult.traverse, headRaised, FuelResult.bind_ok,
        tailRaised, FuelResult.map_ok]
  case plain =>
      intros argument definitionEnvironment body result bodyEval bodyIH
      rcases bodyIH with ⟨fuel, success⟩
      exact ⟨fuel + 1, by simpa [applyFuel] using success⟩
  case recursive =>
      intros argument definitionEnvironment body result bodyEval bodyIH
      rcases bodyIH with ⟨fuel, success⟩
      exact ⟨fuel + 1, by simpa [applyFuel] using success⟩
  case nil =>
      intro function
      exact ⟨0, rfl⟩
  case cons =>
      intros function input output inputs outputs headApply tailApply headIH tailIH
      rcases headIH with ⟨headFuel, headSuccess⟩
      rcases tailIH with ⟨tailFuel, tailSuccess⟩
      let common := max headFuel tailFuel
      have headRaised := applyFuel_ok_of_le
        (Nat.le_max_left headFuel tailFuel) headSuccess
      have tailRaised := traverse_ok_mono
        (fun application => applyFuel_ok_of_le
          (Nat.le_max_right headFuel tailFuel) application)
        tailSuccess
      refine ⟨common, ?_⟩
      dsimp [common]
      simp only [FuelResult.traverse, headRaised, FuelResult.bind_ok,
        tailRaised, FuelResult.map_ok]
  case add =>
      intros left right
      exact ⟨0, rfl⟩
  case append =>
      intros left leftItems right rightItems leftEncoding rightEncoding
      exact ⟨0, by simp [evalPrimitive, leftEncoding, rightEncoding]⟩
  case member =>
      intros target items needle encoding
      exact ⟨0, by simp [evalPrimitive, encoding]⟩
  case deleteFirst =>
      intros target items needle encoding
      exact ⟨0, by simp [evalPrimitive, encoding]⟩
  case map =>
      intros target inputs function outputs encoding applications applicationsIH
      rcases applicationsIH with ⟨fuel, success⟩
      exact ⟨fuel, by simp [evalPrimitive, encoding, success]⟩
  case t => exact derivation

end TypePM.Runtime
