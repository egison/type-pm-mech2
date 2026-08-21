import TypePM.FairTwoIndexMatchingSearchSafety

/-!
# Built-in variable regression for fair two-index matching safety

This executable regression runs two fair rounds over one reduction-tree node.
Its head is an actual built-in variable match and its tail is an already
completed state.  The first round therefore exercises both kinds of child:
the variable hit produces a left child, while the unvisited completed state
becomes a right child after downward weakening.  The second round yields both
integer bindings in left-before-right order.
-/

namespace TypePM.Runtime.FairTwoIndexMatchingSearchSafetyRegression

open TypePM.Source

/-- The callback is deliberately unusable: the built-in variable rule does
not evaluate an embedded expression. -/
def unusedEvaluation : ValueEnvironment → Source.Expr → FuelResult Value :=
  fun _ _ => .stuck

abbrev builtinVariableReducer : AtomReducer :=
  reduceBuiltinAtom unusedEvaluation

def integerTarget : Value := .int 7

def preservedTarget : Value := .int 9

def variableAtom : MatchingAtom :=
  ⟨.var, .something, integerTarget⟩

def variableReduction : AtomReduction :=
  ⟨[[]], [integerTarget]⟩

def variableState : MatchingState :=
  ⟨[variableAtom], [], []⟩

def completedState : MatchingState :=
  ⟨[], [], [integerTarget]⟩

def preservedCompletedState : MatchingState :=
  ⟨[], [], [preservedTarget]⟩

theorem variableReducer_exact :
    builtinVariableReducer [] variableAtom =
      .ok (.hit variableReduction) := by
  rfl

theorem variableSuccessors_exact :
    MatchingState.successors variableState [] variableReduction =
      [completedState] := by
  rfl

theorem completedState_twoIndex (fuel : Nat) :
    TwoIndexMatchingStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
      builtinVariableReducer (fuel + 1) 1 completedState [.int] := by
  exact .yield (FuelEnvironmentSafe.nil (fuel + 1 + 1))
    (FuelEnvironmentSafe.cons
      (fuelValueSafe_int 7 (fuel + 1 + 1))
      (FuelEnvironmentSafe.nil (fuel + 1 + 1)))

theorem preservedCompletedState_twoIndex (fuel : Nat) :
    TwoIndexMatchingStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
      builtinVariableReducer (fuel + 1) 1 preservedCompletedState [.int] := by
  exact .yield (FuelEnvironmentSafe.nil (fuel + 1 + 1))
    (FuelEnvironmentSafe.cons
      (fuelValueSafe_int 9 (fuel + 1 + 1))
      (FuelEnvironmentSafe.nil (fuel + 1 + 1)))

theorem variableState_twoIndex :
    TwoIndexMatchingStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
      builtinVariableReducer 2 1 variableState [.int] := by
  apply TwoIndexMatchingStateTyping.reduce
    (FuelEnvironmentSafe.nil 3) (FuelEnvironmentSafe.nil 3)
  apply TwoIndexAtomReducerCertificate.hit variableReduction
    variableReducer_exact
  intro successor member
  have singleton : successor = completedState := by
    simpa [MatchingState.successors, MatchingState.continueWith,
      variableReduction, completedState] using member
  subst successor
  exact completedState_twoIndex 0

def initialNode : List MatchingState :=
  [variableState, preservedCompletedState]

theorem initialNode_twoIndex :
    TwoIndexMatchingStatesTyping FuelEnvironmentSafe FuelEnvironmentSafe
      builtinVariableReducer 2 1 initialNode [.int] := by
  intro state member
  simp [initialNode] at member
  rcases member with rfl | rfl
  · exact variableState_twoIndex
  · exact preservedCompletedState_twoIndex 1

def expectedFirstPrefix : FairSearchPrefix MatchingState (List Value) :=
  { answers := []
    frontier := [[completedState], [preservedCompletedState]] }

/-- The first round keeps the generated left child before the distinct
preserved right child. -/
theorem oneRound_exact :
    fairReductionPrefix (stepMatchingState builtinVariableReducer) 1
      initialNode = .ok expectedFirstPrefix := by
  rfl

def expectedPrefix : FairSearchPrefix MatchingState (List Value) :=
  { answers := [[integerTarget], [preservedTarget]]
    frontier := [] }

/-- The generated left child is visited before the preserved right child in
the second fair round. -/
theorem twoRounds_exact :
    fairReductionPrefix (stepMatchingState builtinVariableReducer) 2
      initialNode = .ok expectedPrefix := by
  rfl

theorem twoRounds_prefixTyped :
    TwoIndexFairSearchPrefixTyping FuelEnvironmentSafe FuelEnvironmentSafe
      builtinVariableReducer 0 1 expectedPrefix [.int] := by
  exact fairReductionPrefix_twoIndexSafe
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    2 0 initialNode_twoIndex twoRounds_exact

theorem twoRounds_resultSafe :
    TwoIndexFairSearchResultSafe FuelEnvironmentSafe FuelEnvironmentSafe
      builtinVariableReducer 0 1
      (fairReductionPrefix (stepMatchingState builtinVariableReducer) 2
        initialNode) [.int] := by
  exact fairReductionPrefix_twoIndexResultSafe
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    2 0 initialNode initialNode_twoIndex

theorem twoRounds_neverStuck :
    (fairReductionPrefix (stepMatchingState builtinVariableReducer) 2
      initialNode).NotStuck := by
  exact twoRounds_resultSafe.notStuck

end TypePM.Runtime.FairTwoIndexMatchingSearchSafetyRegression
