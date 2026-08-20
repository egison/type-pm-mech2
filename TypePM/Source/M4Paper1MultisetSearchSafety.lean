import TypePM.Source.M4Paper1ListJoinSearchSafety

/-!
# Concrete search safety for the Paper 1 multiset cons pattern

The P1-L05 regression below uses the actual closed seven-clause multiset
matcher.  Clause dispatch, delegated source patterns, search answers, and
answer types are fixed to the real executable values; no callback is allowed
to assign types to arbitrary branches.
-/

namespace TypePM.Source.MatcherTyping.M4Paper1MultisetSearchSafety

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open M4Paper1RecursiveSafetyBoundaryRegression
open M4Paper1ListJoinSearchSafety

def multisetConsPattern : Pattern := .ctor PatternCtor.cons [.var, .var]

def multisetConsTarget : Value :=
  Value.buildList [.int 1, .int 2, .int 3]

def multisetConsAnswers : List (List Value) :=
  [ [.int 1, Value.buildList [.int 2, .int 3]],
    [.int 2, Value.buildList [.int 1, .int 3]],
    [.int 3, Value.buildList [.int 1, .int 2]] ]

def multisetConsBranches : MatchingBranches :=
  [ [⟨.var, .something, .int 1⟩,
      ⟨.var, closedMultisetMatcherValue,
        Value.buildList [.int 2, .int 3]⟩],
    [⟨.var, .something, .int 2⟩,
      ⟨.var, closedMultisetMatcherValue,
        Value.buildList [.int 1, .int 3]⟩],
    [⟨.var, .something, .int 3⟩,
      ⟨.var, closedMultisetMatcherValue,
        Value.buildList [.int 1, .int 2]⟩] ]

set_option maxRecDepth 100000 in
/-- Exact selection of the general-cons clause and its three decompositions
under the actual closed matcher environment. -/
theorem multisetCons_dispatch_exact :
    dispatchMatcherClauses (evalFuel 29) []
      closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
      multisetConsTarget = .ok (.hit multisetConsBranches) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem multisetCons_search_exact :
    searchPatternFuel (evalFuel 29) 29 [] multisetConsPattern
      closedMultisetMatcherValue multisetConsTarget =
        .ok multisetConsAnswers := by
  with_unfolding_all rfl

private theorem int_totalPlainTyping (literal : Int) :
    TotalPlainValueTyping (.int literal) .int :=
  .existing (.ordinary (.int literal))

private theorem intList_itemsTyping : ∀ literals : List Int,
    TotalPlainListValueTypings (literals.map Value.int) .int
  | [] => .nil
  | literal :: literals =>
      .cons (int_totalPlainTyping literal) (intList_itemsTyping literals)

private theorem intList_totalPlainTyping (literals : List Int) :
    TotalPlainValueTyping (Value.buildList (literals.map Value.int))
      (DataTypes.list .int) :=
  .list (intList_itemsTyping literals)

theorem multisetConsAnswers_totalPlainTyping :
    TotalPlainMatchingAnswersTyping multisetConsAnswers
      [.int, DataTypes.list .int] := by
  intro answer member
  simp only [multisetConsAnswers, List.mem_cons] at member
  rcases member with rfl | member
  · exact .cons (int_totalPlainTyping 1)
      (.cons (by simpa using intList_totalPlainTyping [2, 3]) .nil)
  · rcases member with rfl | member
    · exact .cons (int_totalPlainTyping 2)
        (.cons (by simpa using intList_totalPlainTyping [1, 3]) .nil)
    · rcases member with rfl | member
      · exact .cons (int_totalPlainTyping 3)
          (.cons (by simpa using intList_totalPlainTyping [1, 2]) .nil)
      · simp at member

theorem multisetCons_dispatch_preserves_source_patterns :
    ConcreteDispatchPreservesPatterns multisetConsBranches [.var, .var] := by
  intro branch member
  simp [multisetConsBranches] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- All common fuel bounds are safe for the concrete P1-L05 search.  At low
fuel the search may time out; every completed run has the three typed answers
computed by the real seven-clause matcher. -/
theorem multisetCons_concretePatternSearchSafe :
    ConcretePatternSearchSafe [] multisetConsPattern
      closedMultisetMatcherValue multisetConsTarget
      [.int, DataTypes.list .int] :=
  concretePatternSearchSafe_of_exact multisetCons_search_exact
    multisetConsAnswers_totalPlainTyping

/-- Static acceptance and the value-indexed operational certificate for
P1-L05.  The source pattern list is retained by the same concrete dispatch
whose answers are typed. -/
structure ActualMultisetConsSearchCertificate : Prop where
  sourceTyping : M4.Typing Paper1FrozenSignature.signature []
    Runtime.Paper1ExecutionRegression.multisetCons
    TypePM.Source.M4Paper1IntegratedPositiveRegression.multisetConsResultType
  dispatch : dispatchMatcherClauses (evalFuel 29) []
    closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
    multisetConsTarget = .ok (.hit multisetConsBranches)
  patterns : ConcreteDispatchPreservesPatterns multisetConsBranches [.var, .var]
  search : ConcretePatternSearchSafe [] multisetConsPattern
    closedMultisetMatcherValue multisetConsTarget
    [.int, DataTypes.list .int]

theorem actualMultisetConsSearchCertificate :
    ActualMultisetConsSearchCertificate :=
  ⟨TypePM.Source.M4Paper1IntegratedPositiveRegression.multiset_cons_typing,
    multisetCons_dispatch_exact,
    multisetCons_dispatch_preserves_source_patterns,
    multisetCons_concretePatternSearchSafe⟩

/-! ## P1-L02: value-dependent successor pairs -/

def successorTarget : Value :=
  Value.buildList [.int 1, .int 2, .int 5, .int 6]

def successorPattern : Pattern :=
  Runtime.Paper1ExecutionRegression.successorPattern

def successorTailPattern : Pattern :=
  .ctor PatternCtor.cons
    [.value (.prim .add [.var 0, .lit 1]), .wild]

theorem successorPattern_eq :
    successorPattern = .ctor PatternCtor.cons [.var, successorTailPattern] := by
  rfl

def successorAnswers : List (List Value) := [[.int 1], [.int 5]]

def successorDispatchBranches : MatchingBranches :=
  [ [⟨.var, .something, .int 1⟩,
      ⟨successorTailPattern,
        closedMultisetMatcherValue,
        Value.buildList [.int 2, .int 5, .int 6]⟩],
    [⟨.var, .something, .int 2⟩,
      ⟨successorTailPattern,
        closedMultisetMatcherValue,
        Value.buildList [.int 1, .int 5, .int 6]⟩],
    [⟨.var, .something, .int 5⟩,
      ⟨successorTailPattern,
        closedMultisetMatcherValue,
        Value.buildList [.int 1, .int 2, .int 6]⟩],
    [⟨.var, .something, .int 6⟩,
      ⟨successorTailPattern,
        closedMultisetMatcherValue,
        Value.buildList [.int 1, .int 2, .int 5]⟩] ]

set_option maxRecDepth 100000 in
/-- The actual ordered dispatcher preserves the complete second source
pattern, including its value expression and wildcard. -/
theorem successorPairs_dispatch_exact :
    dispatchMatcherClauses (evalFuel 39) []
      closedMultisetMatcherEnvironment multisetClauses successorPattern
      successorTarget = .ok (.hit successorDispatchBranches) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem successorPairs_search_exact :
    searchPatternFuel (evalFuel 39) 39 [] successorPattern
      closedMultisetMatcherValue successorTarget = .ok successorAnswers := by
  with_unfolding_all rfl

theorem successorAnswers_totalPlainTyping :
    TotalPlainMatchingAnswersTyping successorAnswers [.int] := by
  intro answer member
  simp only [successorAnswers, List.mem_cons] at member
  rcases member with rfl | member
  · exact .cons (int_totalPlainTyping 1) .nil
  · rcases member with rfl | member
    · exact .cons (int_totalPlainTyping 5) .nil
    · simp at member

/-- The general-cons header extracts exactly the two child patterns of the
displayed source pattern.  The second child is retained as the complete
constructor/value/wildcard tree rather than collapsed to a generic hole. -/
theorem successorPairs_dispatch_preserves_source_patterns :
    ConcreteDispatchPreservesPatterns successorDispatchBranches
      [.var, successorTailPattern] := by
  intro branch member
  simp [successorDispatchBranches] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem successorPairs_concretePatternSearchSafe :
    ConcretePatternSearchSafe [] successorPattern
      closedMultisetMatcherValue successorTarget [.int] :=
  concretePatternSearchSafe_of_exact successorPairs_search_exact
    successorAnswers_totalPlainTyping

structure ActualSuccessorPairsSearchCertificate : Prop where
  sourceTyping : M4.Typing Paper1FrozenSignature.signature []
    Runtime.Paper1ExecutionRegression.successorPairs
    TypePM.Source.M4Paper1IntegratedPositiveRegression.successorPairsResultType
  sourcePattern : successorPattern =
    .ctor PatternCtor.cons [.var, successorTailPattern]
  dispatch : dispatchMatcherClauses (evalFuel 39) []
    closedMultisetMatcherEnvironment multisetClauses successorPattern
    successorTarget = .ok (.hit successorDispatchBranches)
  patterns : ConcreteDispatchPreservesPatterns successorDispatchBranches
    [.var, successorTailPattern]
  search : ConcretePatternSearchSafe [] successorPattern
    closedMultisetMatcherValue successorTarget [.int]

theorem actualSuccessorPairsSearchCertificate :
    ActualSuccessorPairsSearchCertificate :=
  ⟨TypePM.Source.M4Paper1IntegratedPositiveRegression.successor_pairs_typing,
    successorPattern_eq,
    successorPairs_dispatch_exact,
    successorPairs_dispatch_preserves_source_patterns,
    successorPairs_concretePatternSearchSafe⟩

end TypePM.Source.MatcherTyping.M4Paper1MultisetSearchSafety
