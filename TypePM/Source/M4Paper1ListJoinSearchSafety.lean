import TypePM.Runtime.Paper1ExecutionRegression
import TypePM.Runtime.EvaluationStuckMonotonicity
import TypePM.Source.M4Paper1RecursiveClosureTotalTyping
import TypePM.Source.M4Paper1IntegratedPositiveRegression
import TypePM.TotalPlainClosureSafetyRegression

/-!
# Concrete search safety for the Paper 1 list join pattern

This module keeps the dynamic certificate tied to the matcher value that the
actual recursive `list` constructor returns.  The older
`TotalPlainPatternSearchSafe` quantifies over every value with a matching
static type; that stronger statement cannot be obtained from one concrete
matcher dispatch.
-/

namespace TypePM.Source.MatcherTyping.M4Paper1ListJoinSearchSafety

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open M4Paper1RecursiveSafetyBoundaryRegression

def listMatcherSomethingValue : Value :=
  .matcherV [.something, listRecursiveClosure]
    listMatcherClauses listMatcherClauses

def list123Value : Value := Value.buildList [.int 1, .int 2, .int 3]

def listJoinAnswers : List (List Value) :=
  [ [Value.nilValue, list123Value],
    [Value.buildList [.int 1], Value.buildList [.int 2, .int 3]],
    [Value.buildList [.int 1, .int 2], Value.buildList [.int 3]],
    [list123Value, Value.nilValue] ]

def listJoinBranches : MatchingBranches :=
  [ [⟨.var, listMatcherSomethingValue, Value.nilValue⟩,
      ⟨.var, listMatcherSomethingValue, list123Value⟩],
    [⟨.var, listMatcherSomethingValue, Value.buildList [.int 1]⟩,
      ⟨.var, listMatcherSomethingValue, Value.buildList [.int 2, .int 3]⟩],
    [⟨.var, listMatcherSomethingValue, Value.buildList [.int 1, .int 2]⟩,
      ⟨.var, listMatcherSomethingValue, Value.buildList [.int 3]⟩],
    [⟨.var, listMatcherSomethingValue, list123Value⟩,
      ⟨.var, listMatcherSomethingValue, Value.nilValue⟩] ]

/-- Search preservation for one actual environment, matcher value, and target
value.  Unlike `TotalPlainPatternSearchSafe`, this proposition does not make a
claim about unrelated matcher closures that merely have the same type. -/
def ConcretePatternSearchSafe
    (environment : ValueEnvironment) (pattern : Pattern)
    (matcher target : Value) (bindingTypes : List Ty) : Prop :=
  ∀ fuel,
    searchPatternFuel (evalFuel fuel) fuel environment pattern matcher target =
        .timeout ∨
      ∃ answers,
        searchPatternFuel (evalFuel fuel) fuel environment pattern matcher target =
            .ok answers ∧
          TotalPlainMatchingAnswersTyping answers bindingTypes

/-- Shape-only pattern index for one actual successful dispatch.  This is the
part of the existing pattern-indexed bridge that remains meaningful before a
parallel total typing for recursively captured matcher values is available. -/
def ConcreteDispatchPreservesPatterns
    (branches : MatchingBranches) (patterns : List Pattern) : Prop :=
  ∀ branch ∈ branches, branch.map (fun atom => atom.pattern) = patterns

set_option maxRecDepth 100000 in
theorem listJoin_search_exact :
    searchPatternFuel (evalFuel 24) 24 []
      TotalPlainClosureSafetyRegression.listJoinPattern
      listMatcherSomethingValue list123Value = .ok listJoinAnswers := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
/-- Exact ordered clause dispatch beneath the successful search.  In
particular this is not an oracle replacing the list matcher. -/
theorem listJoin_dispatch_exact :
    dispatchMatcherClauses (evalFuel 24) []
      [.something, listRecursiveClosure] listMatcherClauses
      TotalPlainClosureSafetyRegression.listJoinPattern list123Value =
        .ok (.hit listJoinBranches) := by
  with_unfolding_all rfl


/-- Raising both the expression callback fuel and the DFS fuel preserves a
completed concrete search.  This is the operational monotonicity needed by
the actual matcher-value certificate below. -/
theorem searchPatternFuel_evalFuel_approximates_succ
    (fuel : Nat) (environment : ValueEnvironment) (pattern : Pattern)
    (matcher target : Value) :
    FuelResult.Approximates
      (searchPatternFuel (evalFuel fuel) fuel environment pattern matcher target)
      (searchPatternFuel (evalFuel (fuel + 1)) (fuel + 1) environment pattern
        matcher target) :=
  searchPatternFuel_approximates_succ
    (fun childEnvironment childExpression =>
      evalFuel_approximates_succ (fuel := fuel)
        (environment := childEnvironment) (expression := childExpression))
    fuel environment pattern matcher target

theorem searchPatternFuel_evalFuel_approximates_add
    (fuel extra : Nat) (environment : ValueEnvironment) (pattern : Pattern)
    (matcher target : Value) :
    FuelResult.Approximates
      (searchPatternFuel (evalFuel fuel) fuel environment pattern matcher target)
      (searchPatternFuel (evalFuel (fuel + extra)) (fuel + extra) environment
        pattern matcher target) := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      exact FuelResult.Approximates.refl _
  | succ extra induction =>
      rw [Nat.add_succ]
      exact induction.trans
        (searchPatternFuel_evalFuel_approximates_succ
          (fuel + extra) environment pattern matcher target)

theorem searchPatternFuel_evalFuel_approximates_of_le
    (le : firstFuel ≤ secondFuel) (environment : ValueEnvironment)
    (pattern : Pattern) (matcher target : Value) :
    FuelResult.Approximates
      (searchPatternFuel (evalFuel firstFuel) firstFuel environment pattern
        matcher target)
      (searchPatternFuel (evalFuel secondFuel) secondFuel environment pattern
        matcher target) := by
  rw [← Nat.add_sub_of_le le]
  exact searchPatternFuel_evalFuel_approximates_add firstFuel
    (secondFuel - firstFuel) environment pattern matcher target

/-- One exact successful common-fuel search plus typed answers determines a
value-indexed safety certificate at every fuel.  Smaller completed searches
cannot disagree with the success, and larger searches preserve it. -/
theorem concretePatternSearchSafe_of_exact
    (success : searchPatternFuel (evalFuel successfulFuel) successfulFuel
      environment pattern matcher target = .ok answers)
    (answersTyped : TotalPlainMatchingAnswersTyping answers bindingTypes) :
    ConcretePatternSearchSafe environment pattern matcher target bindingTypes := by
  intro fuel
  by_cases le : fuel ≤ successfulFuel
  · have related := searchPatternFuel_evalFuel_approximates_of_le le environment
      pattern matcher target
    cases current : searchPatternFuel (evalFuel fuel) fuel environment pattern
        matcher target with
    | timeout => exact .inl rfl
    | stuck =>
        rw [current, success] at related
        cases related
    | ok currentAnswers =>
        rw [current, success] at related
        have answers_eq : currentAnswers = answers := by
          cases related
          rfl
        subst currentAnswers
        exact .inr ⟨answers, rfl, answersTyped⟩
  · have reverseLe : successfulFuel ≤ fuel := by omega
    have related := searchPatternFuel_evalFuel_approximates_of_le reverseLe
      environment pattern matcher target
    rw [success] at related
    exact .inr ⟨answers, related.ok_eq, answersTyped⟩

set_option maxRecDepth 100000 in
theorem listJoin_search_exact_above (extra : Nat) :
    searchPatternFuel (evalFuel (24 + extra)) (24 + extra) []
      TotalPlainClosureSafetyRegression.listJoinPattern
      listMatcherSomethingValue list123Value = .ok listJoinAnswers := by
  have related := searchPatternFuel_evalFuel_approximates_add 24 extra []
    TotalPlainClosureSafetyRegression.listJoinPattern
    listMatcherSomethingValue list123Value
  rw [listJoin_search_exact] at related
  exact related.ok_eq

private theorem int_totalPlainTyping (literal : Int) :
    TotalPlainValueTyping (.int literal) .int :=
  .existing (.ordinary (.int literal))

private theorem list1_totalPlainTyping :
    TotalPlainValueTyping (Value.buildList [.int 1]) (DataTypes.list .int) :=
  .list (.cons (int_totalPlainTyping 1) .nil)

private theorem list2_totalPlainTyping :
    TotalPlainValueTyping (Value.buildList [.int 2]) (DataTypes.list .int) :=
  .list (.cons (int_totalPlainTyping 2) .nil)

private theorem list3_totalPlainTyping :
    TotalPlainValueTyping (Value.buildList [.int 3]) (DataTypes.list .int) :=
  .list (.cons (int_totalPlainTyping 3) .nil)

private theorem list12_totalPlainTyping :
    TotalPlainValueTyping (Value.buildList [.int 1, .int 2])
      (DataTypes.list .int) :=
  .list (.cons (int_totalPlainTyping 1)
    (.cons (int_totalPlainTyping 2) .nil))

private theorem list23_totalPlainTyping :
    TotalPlainValueTyping (Value.buildList [.int 2, .int 3])
      (DataTypes.list .int) :=
  .list (.cons (int_totalPlainTyping 2)
    (.cons (int_totalPlainTyping 3) .nil))

private theorem list123_totalPlainTyping :
    TotalPlainValueTyping list123Value (DataTypes.list .int) :=
  .list (.cons (int_totalPlainTyping 1)
    (.cons (int_totalPlainTyping 2)
      (.cons (int_totalPlainTyping 3) .nil)))

private theorem nil_totalPlainTyping :
    TotalPlainValueTyping Value.nilValue (DataTypes.list .int) :=
  .list .nil

theorem listJoinAnswers_totalPlainTyping :
    TotalPlainMatchingAnswersTyping listJoinAnswers
      [DataTypes.list .int, DataTypes.list .int] := by
  intro answer member
  simp only [listJoinAnswers, List.mem_cons] at member
  rcases member with rfl | member
  · exact .cons nil_totalPlainTyping (.cons list123_totalPlainTyping .nil)
  · rcases member with rfl | member
    · exact .cons list1_totalPlainTyping (.cons list23_totalPlainTyping .nil)
    · rcases member with rfl | member
      · exact .cons list12_totalPlainTyping (.cons list3_totalPlainTyping .nil)
      · rcases member with rfl | member
        · exact .cons list123_totalPlainTyping (.cons nil_totalPlainTyping .nil)
        · simp at member

/-- The actual recursive list matcher and the actual three-element target
have a typed join search at every common fuel.  The proof executes the real
ordered clause dispatcher at fuel 24.  Simultaneous evaluator/search
monotonicity then shows that smaller completed runs can only be that same
answer and larger runs preserve it. -/
theorem listJoin_concretePatternSearchSafe :
    ConcretePatternSearchSafe []
      TotalPlainClosureSafetyRegression.listJoinPattern
      listMatcherSomethingValue list123Value
      [DataTypes.list .int, DataTypes.list .int] :=
  concretePatternSearchSafe_of_exact listJoin_search_exact
    listJoinAnswers_totalPlainTyping

theorem listJoin_dispatch_preserves_source_patterns :
    ConcreteDispatchPreservesPatterns listJoinBranches [.var, .var] := by
  intro branch member
  simp [listJoinBranches] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

/-- Static M4 acceptance, the actual ordered runtime dispatch, exact source
pattern retention, and all-fuel typed search are bundled without an
arbitrary branch-typing callback. -/
structure ActualListJoinSearchCertificate : Prop where
  sourceTyping : M4.Typing Paper1FrozenSignature.signature []
    Runtime.Paper1ExecutionRegression.listJoinAll
    TypePM.Source.M4Paper1IntegratedPositiveRegression.listJoinResultType
  dispatch : dispatchMatcherClauses (evalFuel 24) []
    [.something, listRecursiveClosure] listMatcherClauses
    TotalPlainClosureSafetyRegression.listJoinPattern list123Value =
      .ok (.hit listJoinBranches)
  patterns : ConcreteDispatchPreservesPatterns listJoinBranches [.var, .var]
  search : ConcretePatternSearchSafe []
    TotalPlainClosureSafetyRegression.listJoinPattern
    listMatcherSomethingValue list123Value
    [DataTypes.list .int, DataTypes.list .int]

theorem actualListJoinSearchCertificate : ActualListJoinSearchCertificate :=
  ⟨TypePM.Source.M4Paper1IntegratedPositiveRegression.list_join_typing,
    listJoin_dispatch_exact, listJoin_dispatch_preserves_source_patterns,
    listJoin_concretePatternSearchSafe⟩

end TypePM.Source.MatcherTyping.M4Paper1ListJoinSearchSafety
