import TypePM.ValueIndexedStableFirstOrderSafety
import TypePM.StepIndexedPaper1ListSafetyRegression
import TypePM.Source.M4Paper1ListJoinSearchSafety

/-!
# Value-indexed safety of the recursive Paper 1 List join arm

The top-level List join regression evaluates a closed `matchAll`.  This
module moves the same value-indexed argument into the recursive matcher's
selected `cons` arm.  The environment below is not an arbitrary typed
environment: it is exactly the data-pattern values followed by the actual
matcher captures used while dispatching the join clause on `[1, 2, 3]`.
-/

namespace TypePM.ValueIndexedPaper1ListClauseBodySafety

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1ListJoinSearchSafety
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open StepIndexedPaper1ListSafetyRegression

def list23Value : Value := Value.buildList [.int 2, .int 3]

def actualJoinConsEnvironment : ValueEnvironment :=
  [.int 1, list23Value, .something, listRecursiveClosure]

def actualJoinConsContext : List Ty :=
  [.int, DataTypes.list .int, concreteListDomain,
    .fn concreteListDomain concreteListCodomain]

def innerJoinBindingTypes : List Ty :=
  [DataTypes.list .int, DataTypes.list .int]

def innerJoinBodyTarget : Ty :=
  .prod [DataTypes.list .int, DataTypes.list .int]

def list23JoinAnswers : List (List Value) :=
  [ [Value.nilValue, list23Value],
    [Value.buildList [.int 2], Value.buildList [.int 3]],
    [list23Value, Value.nilValue] ]

def actualJoinConsResult : Value :=
  Value.buildList
    [ .tuple [Value.nilValue, list123Value],
      .tuple [Value.buildList [.int 1], list23Value],
      .tuple [Value.buildList [.int 1, .int 2], Value.buildList [.int 3]],
      .tuple [list123Value, Value.nilValue] ]

/-- The environment is exactly the one assembled by `tryMatcherArm`: the
two `cons` fields, no pattern-header captures, and the generated matcher's
concrete captured argument/self pair. -/
theorem actualJoinConsEnvironment_eq_runtime_layout :
    [.int 1, list23Value] ++ [] ++ [.something, listRecursiveClosure] =
      actualJoinConsEnvironment := by
  rfl

private theorem intList_fuelValueSafe (values : List Int) (fuel : Nat) :
    FuelValueSafe fuel
      (Value.buildList (values.map Value.int)) (DataTypes.list .int) := by
  apply fuelValueSafe_list_of_forall .int fuel
  intro value member
  simp only [List.mem_map] at member
  obtain ⟨literal, _, rfl⟩ := member
  exact fuelValueSafe_int literal fuel

private theorem intList_allFuelListValueSafe (values : List Int) :
    AllFuelListValueSafe (Value.buildList (values.map Value.int)) .int := by
  exact ⟨values.map Value.int, rfl, by
    intro item member fuel
    simp only [List.mem_map] at member
    obtain ⟨literal, _, rfl⟩ := member
    exact fuelValueSafe_int literal fuel⟩

theorem list23_fuelValueSafe (fuel : Nat) :
    FuelValueSafe fuel list23Value (DataTypes.list .int) := by
  simpa [list23Value] using intList_fuelValueSafe [2, 3] fuel

private theorem pair_fuelValueSafe
    (firstSafe : FuelValueSafe fuel first (DataTypes.list .int))
    (secondSafe : FuelValueSafe fuel second (DataTypes.list .int)) :
    FuelValueSafe fuel (.tuple [first, second]) innerJoinBodyTarget := by
  induction fuel with
  | zero => exact fuelValueSafe_zero _ _
  | succ fuel induction =>
      exact fuelValueSafe_tuple
        (induction firstSafe.previous secondSafe.previous)
        (.cons firstSafe (.cons secondSafe .nil))

/-- Step-indexed safety of the actual selected-arm environment, including
the concrete recursive self value rather than a structurally typed stand-in. -/
theorem actualJoinConsEnvironment_fuelSafe (fuel : Nat) :
    FuelEnvironmentSafe fuel actualJoinConsEnvironment
      actualJoinConsContext := by
  exact FuelEnvironmentSafe.cons (fuelValueSafe_int 1 fuel)
    (FuelEnvironmentSafe.cons (list23_fuelValueSafe fuel)
      (FuelEnvironmentSafe.cons
        (something_concreteListDomain_fuelValueSafe fuel)
        (FuelEnvironmentSafe.cons
          (listRecursiveClosure_concreteFuelValueSafe fuel)
          (FuelEnvironmentSafe.nil fuel))))

private theorem totalPlainInt (literal : Int) :
    TotalPlainValueTyping (.int literal) .int :=
  .existing (.ordinary (.int literal))

private theorem totalPlainIntList (values : List Int) :
    TotalPlainValueTyping (Value.buildList (values.map Value.int))
      (DataTypes.list .int) := by
  apply TotalPlainValueTyping.list
  induction values with
  | nil => exact .nil
  | cons value values induction => exact .cons (totalPlainInt value) induction

theorem list23JoinAnswers_totalPlainTyping :
    TotalPlainMatchingAnswersTyping list23JoinAnswers
      innerJoinBindingTypes := by
  intro answer member
  simp only [list23JoinAnswers, List.mem_cons] at member
  rcases member with rfl | member
  · exact .cons (by
        simpa [Value.buildList, Value.nilValue] using totalPlainIntList [])
      (.cons (by simpa [list23Value] using totalPlainIntList [2, 3]) .nil)
  · rcases member with rfl | member
    · exact .cons (by simpa using totalPlainIntList [2])
        (.cons (by simpa using totalPlainIntList [3]) .nil)
    · rcases member with rfl | member
      · exact .cons (by simpa [list23Value] using totalPlainIntList [2, 3])
          (.cons (by
            simpa [Value.buildList, Value.nilValue] using totalPlainIntList [])
            .nil)
      · simp at member

set_option maxRecDepth 100000 in
theorem list23Join_search_exact :
    searchPatternFuel (evalFuel 24) 24 actualJoinConsEnvironment
      TotalPlainClosureSafetyRegression.listJoinPattern
      listMatcherSomethingValue list23Value = .ok list23JoinAnswers := by
  with_unfolding_all rfl

/-- The concrete recursive matcher searches the actual tail `[2, 3]` safely
at every common evaluator/search fuel. -/
theorem list23Join_concretePatternSearchSafe :
    ConcretePatternSearchSafe actualJoinConsEnvironment
      TotalPlainClosureSafetyRegression.listJoinPattern
      listMatcherSomethingValue list23Value innerJoinBindingTypes :=
  concretePatternSearchSafe_of_exact list23Join_search_exact
    list23JoinAnswers_totalPlainTyping

theorem actualTail_evaluation_fuelSafe :
    ∀ fuel, FuelResultSafe fuel (DataTypes.list .int)
      (evalFuel fuel actualJoinConsEnvironment (.var 1))
  | 0 => .inl rfl
  | fuel + 1 => .inr ⟨list23Value, rfl, list23_fuelValueSafe (fuel + 1)⟩

theorem actualTail_evaluation_shape :
    ∀ fuel, evalFuel fuel actualJoinConsEnvironment (.var 1) = .timeout ∨
      evalFuel fuel actualJoinConsEnvironment (.var 1) = .ok list23Value
  | 0 => .inl rfl
  | _ + 1 => .inr rfl

/-- Calling the actual recursive self entry on the actual captured
`something` argument produces the concrete matcher cursor. -/
theorem actualSelfApplication_evaluation_fuelSafe :
    ∀ fuel, FuelResultSafe fuel concreteListCodomain
      (evalFuel fuel actualJoinConsEnvironment (.app (.var 3) (.var 2)))
  | 0 => .inl rfl
  | 1 => .inl rfl
  | 2 => .inl rfl
  | fuel + 3 => .inr ⟨listMatcherSomethingValue, rfl,
      listMatcherClosure_concreteFuelValueSafe .something (fuel + 3)
        (something_concreteListDomain_fuelValueSafe (fuel + 3))⟩

theorem actualSelfApplication_evaluation_shape :
    ∀ fuel,
      evalFuel fuel actualJoinConsEnvironment (.app (.var 3) (.var 2)) =
          .timeout ∨
        evalFuel fuel actualJoinConsEnvironment (.app (.var 3) (.var 2)) =
          .ok listMatcherSomethingValue
  | 0 => .inl rfl
  | 1 => .inl rfl
  | 2 => .inl rfl
  | _ + 3 => .inr rfl

theorem actualInnerJoin_evaluatedPatternSearchSafe (fuel : Nat) :
    EvaluatedPatternSearchSafe fuel actualJoinConsEnvironment (.var 1)
      (.app (.var 3) (.var 2))
      TotalPlainClosureSafetyRegression.listJoinPattern
      innerJoinBindingTypes := by
  intro targetValue matcherValue targetSuccess matcherSuccess
  rcases actualTail_evaluation_shape fuel with targetTimeout | targetExact
  · rw [targetSuccess] at targetTimeout
    contradiction
  · have target_eq : targetValue = list23Value := by
      rw [targetSuccess] at targetExact
      exact FuelResult.ok.inj targetExact
    rcases actualSelfApplication_evaluation_shape fuel with matcherTimeout |
      matcherExact
    · rw [matcherSuccess] at matcherTimeout
      contradiction
    · have matcher_eq : matcherValue = listMatcherSomethingValue := by
        rw [matcherSuccess] at matcherExact
        exact FuelResult.ok.inj matcherExact
      subst targetValue
      subst matcherValue
      exact list23Join_concretePatternSearchSafe fuel

private theorem totalPlainInt_fuelValueSafe
    (typed : TotalPlainValueTyping value .int) (fuel : Nat) :
    FuelValueSafe fuel value .int := by
  cases typed with
  | existing total =>
      cases total with
      | ordinary ordinary =>
          obtain ⟨literal, rfl⟩ := ordinary.int_canonical
          exact fuelValueSafe_int literal fuel

private theorem TotalPlainListValueTypings.intMembersFuelSafe
    (fuel : Nat) : ∀ {values},
    TotalPlainListValueTypings values .int →
      ∀ value ∈ values, FuelValueSafe fuel value .int
  | _, .nil => by simp
  | _, .cons head tail => by
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · simpa [equality] using totalPlainInt_fuelValueSafe head fuel
      · exact TotalPlainListValueTypings.intMembersFuelSafe fuel tail
          candidate member

private theorem totalPlainIntList_fuelValueSafe
    (typed : TotalPlainValueTyping value (DataTypes.list .int))
    (fuel : Nat) : FuelValueSafe fuel value (DataTypes.list .int) := by
  obtain ⟨values, rfl, items⟩ := typed.list_canonical
  exact fuelValueSafe_list_of_forall .int fuel values
    (TotalPlainListValueTypings.intMembersFuelSafe fuel items)

theorem actualInnerJoinTupleBody_fuelSafe (fuel : Nat) :
    EvaluatedBindingBodySafe fuel actualJoinConsEnvironment
      innerJoinBindingTypes (.tuple [.var 0, .var 1])
      innerJoinBodyTarget := by
  intro bindings bindingsTyped
  cases bindingsTyped with
  | cons firstTyped tailTyped =>
      cases tailTyped with
      | cons secondTyped restTyped =>
          cases restTyped
          cases fuel with
          | zero => exact .inl rfl
          | succ fuel =>
              cases fuel with
              | zero => exact .inl rfl
              | succ residual =>
                  exact .inr ⟨.tuple [_, _], rfl,
                    pair_fuelValueSafe
                      (totalPlainIntList_fuelValueSafe firstTyped
                        (residual + 2))
                      (totalPlainIntList_fuelValueSafe secondTyped
                        (residual + 2))⟩

private theorem totalPlainIntList_allFuelValueSafe
    (typed : TotalPlainValueTyping value (DataTypes.list .int)) :
    AllFuelValueSafe value (DataTypes.list .int) :=
  fun fuel => totalPlainIntList_fuelValueSafe typed fuel

private theorem totalPlainIntList_allFuelListValueSafe
    (typed : TotalPlainValueTyping value (DataTypes.list .int)) :
    AllFuelListValueSafe value .int := by
  obtain ⟨values, rfl, items⟩ := typed.list_canonical
  exact ⟨values, rfl, by
    intro item member fuel
    exact TotalPlainListValueTypings.intMembersFuelSafe fuel items item member⟩

/-- The selected tuple body has the stronger first-order postcondition needed
by the enclosing `letE`, `map`, and `append` rules. -/
theorem actualInnerJoinTupleBody_allFuelSafe (fuel : Nat) :
    EvaluatedBindingBodySafeWith fuel actualJoinConsEnvironment
      innerJoinBindingTypes (.tuple [.var 0, .var 1])
      (fun value => AllFuelValueSafe value innerJoinBodyTarget) := by
  intro bindings bindingsTyped
  cases bindingsTyped with
  | cons firstTyped tailTyped =>
      cases tailTyped with
      | cons secondTyped restTyped =>
          cases restTyped
          have firstSafe : AllFuelValueSafe _ (DataTypes.list .int) :=
            totalPlainIntList_allFuelValueSafe firstTyped
          have secondSafe : AllFuelValueSafe _ (DataTypes.list .int) :=
            totalPlainIntList_allFuelValueSafe secondTyped
          cases fuel with
          | zero => exact .inl rfl
          | succ childFuel =>
              exact (evalFuel_tuplePair_allFuelSafe
                (evalFuel_var_resultSafeWith (index := 0) rfl firstSafe
                  childFuel)
                (evalFuel_var_resultSafeWith (index := 1) rfl secondSafe
                  childFuel)).toAllFuelResultSafe

theorem actualInnerJoinTupleBody_pairSafe (fuel : Nat) :
    EvaluatedBindingBodySafeWith fuel actualJoinConsEnvironment
      innerJoinBindingTypes (.tuple [.var 0, .var 1])
      (PairValueSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int)) := by
  intro bindings bindingsTyped
  cases bindingsTyped with
  | cons firstTyped tailTyped =>
      cases tailTyped with
      | cons secondTyped restTyped =>
          cases restTyped
          have firstSafe : AllFuelListValueSafe _ .int :=
            totalPlainIntList_allFuelListValueSafe firstTyped
          have secondSafe : AllFuelListValueSafe _ .int :=
            totalPlainIntList_allFuelListValueSafe secondTyped
          cases fuel with
          | zero => exact .inl rfl
          | succ childFuel =>
              exact evalFuel_tuplePair_resultSafeWith
                (evalFuel_var_resultSafeWith (index := 0) rfl firstSafe
                  childFuel)
                (evalFuel_var_resultSafeWith (index := 1) rfl secondSafe
                  childFuel)

/-- This is the recursive `matchAll` inside the real `listJoinConsBody`.
Both formerly open premises are now concrete: lookup index 3 is the actual
recursive closure, and search uses only the matcher value returned by that
call at the same fuel. -/
theorem actualListSplitTailResults_fuelResultSafe (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel (fuel + 1) actualJoinConsEnvironment
        listSplitTailResults) := by
  exact matchAllFuel_valueIndexedSafe
    (actualTail_evaluation_fuelSafe fuel)
    (actualSelfApplication_evaluation_fuelSafe fuel)
    (actualInnerJoin_evaluatedPatternSearchSafe fuel)
    (actualInnerJoinTupleBody_fuelSafe fuel)

/-- Stable first-order form of the recursive `matchAll` result. -/
theorem actualListSplitTailResults_allFuelSafe (fuel : Nat) :
    AllFuelListResultSafe innerJoinBodyTarget
      (evalFuel (fuel + 1) actualJoinConsEnvironment
        listSplitTailResults) := by
  exact matchAllFuel_valueIndexedAllFuelSafe
    (actualTail_evaluation_fuelSafe fuel)
    (actualSelfApplication_evaluation_fuelSafe fuel)
    (actualInnerJoin_evaluatedPatternSearchSafe fuel)
    (actualInnerJoinTupleBody_allFuelSafe fuel)

theorem actualListSplitTailResults_allFuelSafe_all :
    ∀ fuel, AllFuelListResultSafe innerJoinBodyTarget
      (evalFuel fuel actualJoinConsEnvironment listSplitTailResults)
  | 0 => .inl rfl
  | fuel + 1 => actualListSplitTailResults_allFuelSafe fuel

theorem actualListSplitTailResults_pairSafe (fuel : Nat) :
    ListResultSafeWith
      (PairValueSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int))
      (evalFuel (fuel + 1) actualJoinConsEnvironment
        listSplitTailResults) := by
  exact matchAllFuel_valueIndexedListSafeWith
    (actualTail_evaluation_fuelSafe fuel)
    (actualSelfApplication_evaluation_fuelSafe fuel)
    (actualInnerJoin_evaluatedPatternSearchSafe fuel)
    (actualInnerJoinTupleBody_pairSafe fuel)

theorem actualListSplitTailResults_pairSafe_all :
    ∀ fuel, ListResultSafeWith
      (PairValueSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int))
      (evalFuel fuel actualJoinConsEnvironment listSplitTailResults)
  | 0 => .inl rfl
  | fuel + 1 => actualListSplitTailResults_pairSafe fuel

/-! ## Stable safety of the pair-destructuring map callback -/

def putCurrentAtPrefixEndBody : Source.Expr :=
  .letE (.prim PrimOp.pairSecond [.var 0])
    (.letE (.prim PrimOp.pairFirst [.var 1])
      (.tuple [
        .ctor DataCtor.cons [.var 4, .var 0],
        .var 1]))

theorem putCurrentAtPrefixEnd_eq :
    putCurrentAtPrefixEnd = .lam putCurrentAtPrefixEndBody := by
  rfl

/-- Application of the actual pair-destructuring callback is proved from
the projection, `letE`, List-construction, and tuple rules. -/
theorem putCurrentAtPrefixEndBody_pairSafe
    (boundValue argument : Value)
    (argumentSafe : PairValueSafeWith
      (fun value => AllFuelListValueSafe value .int)
      (fun value => AllFuelListValueSafe value .int) argument) :
    ∀ fuel, PairResultSafeWith
      (fun value => AllFuelListValueSafe value .int)
      (fun value => AllFuelListValueSafe value .int)
      (evalFuel fuel (argument :: boundValue :: actualJoinConsEnvironment)
        putCurrentAtPrefixEndBody) := by
  have pairVariableSafe : ∀ fuel,
      PairResultSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int)
        (evalFuel fuel
          (argument :: boundValue :: actualJoinConsEnvironment) (.var 0)) :=
    evalFuel_var_resultSafeWith rfl argumentSafe
  have secondProjectionSafe : ∀ fuel,
      AllFuelListResultSafe .int
        (evalFuel fuel
          (argument :: boundValue :: actualJoinConsEnvironment)
          (.prim PrimOp.pairSecond [.var 0])) :=
    evalFuel_pairSecond_resultSafeWith_all pairVariableSafe
  rw [show putCurrentAtPrefixEndBody =
      .letE (.prim PrimOp.pairSecond [.var 0])
        (.letE (.prim PrimOp.pairFirst [.var 1])
          (.tuple [
            .ctor DataCtor.cons [.var 4, .var 0],
            .var 1])) by rfl]
  apply evalFuel_letE_resultSafeWith_all secondProjectionSafe
  intro projectionFuel second secondSafe
  have pairAfterSecondSafe : ∀ fuel,
      PairResultSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int)
        (evalFuel fuel
          (second :: argument :: boundValue :: actualJoinConsEnvironment)
          (.var 1)) :=
    evalFuel_var_resultSafeWith rfl argumentSafe
  have firstProjectionSafe : ∀ fuel,
      AllFuelListResultSafe .int
        (evalFuel fuel
          (second :: argument :: boundValue :: actualJoinConsEnvironment)
          (.prim PrimOp.pairFirst [.var 1])) :=
    evalFuel_pairFirst_resultSafeWith_all pairAfterSecondSafe
  apply evalFuel_letE_resultSafeWith_all firstProjectionSafe
  intro resultFuel first firstSafe
  let finalEnvironment :=
    first :: second :: argument :: boundValue :: actualJoinConsEnvironment
  have currentSafe : AllFuelValueSafe (.int 1) .int :=
    fun fuel => fuelValueSafe_int 1 fuel
  have currentVariableSafe : ∀ fuel,
      AllFuelResultSafe .int (evalFuel fuel finalEnvironment (.var 4)) :=
    evalFuel_var_resultSafeWith rfl currentSafe
  have firstVariableSafe : ∀ fuel,
      AllFuelListResultSafe .int
        (evalFuel fuel finalEnvironment (.var 0)) :=
    evalFuel_var_resultSafeWith rfl firstSafe
  have extendedPrefixSafe : ∀ fuel,
      AllFuelListResultSafe .int
        (evalFuel fuel finalEnvironment
          (.ctor DataCtor.cons [.var 4, .var 0])) :=
    evalFuel_listCons_allFuelSafe_all currentVariableSafe firstVariableSafe
  have secondVariableSafe : ∀ fuel,
      AllFuelListResultSafe .int
        (evalFuel fuel finalEnvironment (.var 1)) :=
    evalFuel_var_resultSafeWith rfl secondSafe
  simpa [finalEnvironment] using
    (evalFuel_tuplePair_resultSafeWith_all
      extendedPrefixSafe secondVariableSafe resultFuel)

theorem putCurrentAtPrefixEnd_functionSafeWith (boundValue : Value) :
    ∀ fuel,
      FunctionResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel (boundValue :: actualJoinConsEnvironment)
          putCurrentAtPrefixEnd)
  | 0 => .inl rfl
  | fuel + 1 => by
      refine .inr ⟨Value.plainClosure
        (boundValue :: actualJoinConsEnvironment)
        putCurrentAtPrefixEndBody, ?_, ?_⟩
      · simp [putCurrentAtPrefixEnd_eq, evalFuel]
      · intro applicationFuel argument argumentSafe
        cases applicationFuel with
        | zero => exact .inl rfl
        | succ bodyFuel =>
            change FuelResultSafeWith
              (PairValueSafeWith
                (fun value => AllFuelListValueSafe value .int)
                (fun value => AllFuelListValueSafe value .int))
              (evalFuel bodyFuel
                (argument :: boundValue :: actualJoinConsEnvironment)
                putCurrentAtPrefixEndBody)
            exact putCurrentAtPrefixEndBody_pairSafe
              boundValue argument argumentSafe bodyFuel

/-! ## Compositional safety of the arm continuation -/

def actualJoinBaseExpression : Source.Expr :=
  sourceList
    [.tuple [sourceList [],
      .ctor DataCtor.cons [.var 1, .var 2]]]

private theorem actualJoinBase_pairSafe (boundValue : Value) :
    ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel (boundValue :: actualJoinConsEnvironment)
          actualJoinBaseExpression) := by
  let environment := boundValue :: actualJoinConsEnvironment
  have emptyListSafe : ∀ fuel,
      AllFuelListResultSafe .int
        (evalFuel fuel environment (sourceList [])) := by
    simpa [sourceList] using
      (evalFuel_listNil_allFuelSafe_all (environment := environment)
        (element := .int))
  have currentSafe : AllFuelValueSafe (.int 1) .int :=
    fun fuel => fuelValueSafe_int 1 fuel
  have currentVariableSafe : ∀ fuel,
      AllFuelResultSafe .int (evalFuel fuel environment (.var 1)) :=
    evalFuel_var_resultSafeWith rfl currentSafe
  have tailSafe : AllFuelListValueSafe list23Value .int := by
    simpa [list23Value] using intList_allFuelListValueSafe [2, 3]
  have tailVariableSafe : ∀ fuel,
      AllFuelListResultSafe .int (evalFuel fuel environment (.var 2)) :=
    evalFuel_var_resultSafeWith rfl tailSafe
  have wholeListSafe : ∀ fuel,
      AllFuelListResultSafe .int
        (evalFuel fuel environment
          (.ctor DataCtor.cons [.var 1, .var 2])) :=
    evalFuel_listCons_allFuelSafe_all currentVariableSafe tailVariableSafe
  have pairSafe : ∀ fuel,
      PairResultSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int)
        (evalFuel fuel environment
          (.tuple [sourceList [],
            .ctor DataCtor.cons [.var 1, .var 2]])) :=
    evalFuel_tuplePair_resultSafeWith_all emptyListSafe wholeListSafe
  have emptyPairListSafe : ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel environment (sourceList [])) := by
    simpa [sourceList] using
      (evalFuel_listNil_resultSafeWith_all
        (environment := environment)
        (predicate := PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int)))
  simpa [actualJoinBaseExpression, sourceList, environment] using
    (evalFuel_listCons_resultSafeWith_all pairSafe emptyPairListSafe)

private theorem actualJoinMap_pairSafe
    (boundValue : Value)
    (boundSafe : ListValueSafeWith
      (PairValueSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int)) boundValue) :
    ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel (boundValue :: actualJoinConsEnvironment)
          (.prim PrimOp.map [putCurrentAtPrefixEnd, .var 0])) := by
  have inputSafe : ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel (boundValue :: actualJoinConsEnvironment) (.var 0)) :=
    evalFuel_var_resultSafeWith rfl boundSafe
  exact evalFuel_map_resultSafeWith_all
    (putCurrentAtPrefixEnd_functionSafeWith boundValue) inputSafe

private theorem actualJoinContinuation_pairSafe
    (boundValue : Value)
    (boundSafe : ListValueSafeWith
      (PairValueSafeWith
        (fun value => AllFuelListValueSafe value .int)
        (fun value => AllFuelListValueSafe value .int)) boundValue) :
    ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel (boundValue :: actualJoinConsEnvironment)
          (.prim PrimOp.append
            [actualJoinBaseExpression,
              .prim PrimOp.map [putCurrentAtPrefixEnd, .var 0]])) :=
  evalFuel_append_resultSafeWith_all
    (actualJoinBase_pairSafe boundValue)
    (actualJoinMap_pairSafe boundValue boundSafe)

/-- After the concrete recursive-search certificate has been supplied, the
continuation of the whole arm is assembled from the value-indexed `matchAll`,
`letE`, projection, List construction, `map`, and `append` rules. -/
theorem actualListJoinConsBody_listPairSafe_compositional :
    ∀ fuel,
      ListResultSafeWith
        (PairValueSafeWith
          (fun value => AllFuelListValueSafe value .int)
          (fun value => AllFuelListValueSafe value .int))
        (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) := by
  rw [show listJoinConsBody =
      .letE listSplitTailResults
        (.prim PrimOp.append
          [actualJoinBaseExpression,
            .prim PrimOp.map [putCurrentAtPrefixEnd, .var 0]]) by rfl]
  exact evalFuel_letE_resultSafeWith_all
    actualListSplitTailResults_pairSafe_all
    (fun fuel value safe => actualJoinContinuation_pairSafe value safe fuel)

private theorem listPairPost_toAllFuelValueSafe
    (safe : PairValueSafeWith
      (fun value => AllFuelListValueSafe value .int)
      (fun value => AllFuelListValueSafe value .int) value) :
    AllFuelValueSafe value innerJoinBodyTarget := by
  obtain ⟨first, second, rfl, firstSafe, secondSafe⟩ := safe
  exact (AllFuelPairValueSafe.toAllFuelValueSafe
    ⟨first, second, rfl, firstSafe.toAllFuelValueSafe,
      secondSafe.toAllFuelValueSafe⟩)

/-- All-fuel safety of the full actual `listJoinConsBody`.  The surrounding
arm is assembled compositionally and does not use the exact equation for the
whole body.  Its concrete recursive-search certificate is still obtained
from the exact search run and search-fuel monotonicity. -/
theorem actualListJoinConsBody_fuelResultSafe_compositional (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) := by
  have stable : AllFuelListResultSafe innerJoinBodyTarget
      (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) :=
    ListResultSafeWith.mono
      (actualListJoinConsBody_listPairSafe_compositional fuel)
      (fun _ safe => listPairPost_toAllFuelValueSafe safe)
  exact stable.toAllFuelResultSafe.toFuelResultSafe fuel

theorem actualListJoinConsBody_neverStuck_compositional (fuel : Nat) :
    (evalFuel fuel actualJoinConsEnvironment listJoinConsBody).NotStuck :=
  (actualListJoinConsBody_fuelResultSafe_compositional fuel).notStuck

set_option maxRecDepth 100000 in
theorem actualListJoinConsBody_exact :
    evalFuel 24 actualJoinConsEnvironment listJoinConsBody =
      .ok actualJoinConsResult := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- The actual second data arm of the selected join clause completes at the
same callback fuel as the published concrete dispatch.  This equation also
checks decomposition decoding, next-matcher evaluation, and branch building;
it is therefore stronger than evaluating the arm body in isolation. -/
theorem actualListJoinConsArm_try_exact :
    tryMatcherArm (evalFuel 24) [.something, listRecursiveClosure] []
      [.var, .var]
      (.tuple
        [.app (.var 1) (.var 0),
          .app (.var 1) (.var 0)])
      list123Value
      (.mk (.ctor DataCtor.cons [.var, .var]) listJoinConsBody) =
        .ok (.hit listJoinBranches) := by
  with_unfolding_all rfl

/-- Closed all-fuel safety under the original public name.  The separate
whole-body exact equation is not used here; the lower-level concrete search
certificate remains exact-seeded. -/
theorem actualListJoinConsBody_fuelResultSafe (fuel : Nat) :
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel fuel actualJoinConsEnvironment listJoinConsBody) :=
  actualListJoinConsBody_fuelResultSafe_compositional fuel

theorem actualListJoinConsBody_neverStuck (fuel : Nat) :
    (evalFuel fuel actualJoinConsEnvironment listJoinConsBody).NotStuck :=
  (actualListJoinConsBody_fuelResultSafe fuel).notStuck

/-- A concrete regression bundle sharing one actual dispatch layout,
recursive-self application, exact-seeded value-indexed search, recursive
`matchAll`, and selected arm body.  It does not quantify over an unrelated
matcher value of the same type, and it is not a general M4 clause bridge. -/
structure ActualListJoinConsArmSafety : Prop where
  dispatch : dispatchMatcherClauses (evalFuel 24) []
    [.something, listRecursiveClosure] listMatcherClauses
    TotalPlainClosureSafetyRegression.listJoinPattern list123Value =
      .ok (.hit listJoinBranches)
  selectedArm :
    tryMatcherArm (evalFuel 24) [.something, listRecursiveClosure] []
      [.var, .var]
      (.tuple
        [.app (.var 1) (.var 0),
          .app (.var 1) (.var 0)])
      list123Value
      (.mk (.ctor DataCtor.cons [.var, .var]) listJoinConsBody) =
        .ok (.hit listJoinBranches)
  environment : ∀ fuel,
    FuelEnvironmentSafe fuel actualJoinConsEnvironment actualJoinConsContext
  selfApplication : ∀ fuel,
    FuelResultSafe fuel concreteListCodomain
      (evalFuel fuel actualJoinConsEnvironment (.app (.var 3) (.var 2)))
  search : ConcretePatternSearchSafe actualJoinConsEnvironment
    TotalPlainClosureSafetyRegression.listJoinPattern
    listMatcherSomethingValue list23Value innerJoinBindingTypes
  recursiveMatchAll : ∀ fuel,
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel (fuel + 1) actualJoinConsEnvironment listSplitTailResults)
  armBody : ∀ fuel,
    FuelResultSafe fuel (DataTypes.list innerJoinBodyTarget)
      (evalFuel fuel actualJoinConsEnvironment listJoinConsBody)

theorem actualListJoinConsArmSafety : ActualListJoinConsArmSafety :=
  ⟨listJoin_dispatch_exact,
    actualListJoinConsArm_try_exact,
    actualJoinConsEnvironment_fuelSafe,
    actualSelfApplication_evaluation_fuelSafe,
    list23Join_concretePatternSearchSafe,
    actualListSplitTailResults_fuelResultSafe,
    actualListJoinConsBody_fuelResultSafe_compositional⟩

end TypePM.ValueIndexedPaper1ListClauseBodySafety
