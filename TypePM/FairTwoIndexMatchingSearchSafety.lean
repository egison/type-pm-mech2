import TypePM.Runtime.FairReductionTreeSearch
import TypePM.TwoIndexMatchingSearchSafety

/-!
# Two-index safety for bounded fair matching prefixes

This module connects the executable binary-reduction-tree prefix search to
the actual `MatchingState` transition and its two-index typing judgment.  The
fair-search round count is an operational bound: a frontier with `n + 1`
rounds available contains states typed at search index `n + 1`; one successful
round yields answers safe at the retained logical index and leaves both its
left and right child nodes typed at search index `n`.

This is a safety theorem for finite observed prefixes.  It does not state
fairness or liveness, and it does not claim that a reachable answer exists.
State-level `timeout` remains an allowed result, while a typed prefix cannot
return `stuck`.  The atom reducer is kept unchanged through every round.
-/

namespace TypePM.Runtime

/-- Answers already observed by fair matching are safe at the retained
logical index. -/
abbrev TwoIndexFairAnswerTyping
    (bindingsInvariant : IndexedMatchingInvariant)
    (residual : Nat) (answerTypes : List Ty) (bindings : List Value) : Prop :=
  bindingsInvariant residual bindings answerTypes

/-- Every state in every reduction-tree node has the same remaining-round
index and retained answer index. -/
abbrev TwoIndexFairFrontierTyping
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (reduceAtom : AtomReducer) (roundIndex residual : Nat)
    (frontier : List (List MatchingState)) (answerTypes : List Ty) : Prop :=
  FairFrontierSafe
    (fun state => TwoIndexMatchingStateTyping environmentInvariant
      bindingsInvariant reduceAtom roundIndex residual state answerTypes)
    frontier

/-- The products of one successful fair round.  Generated left children and
preserved right tails both live at the strict predecessor round index. -/
def TwoIndexFairRoundTyping
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (reduceAtom : AtomReducer) (roundIndex residual : Nat)
    (round : FairRound MatchingState (List Value))
    (answerTypes : List Ty) : Prop :=
  AllSafe (TwoIndexFairAnswerTyping bindingsInvariant residual answerTypes)
      round.answers ∧
    TwoIndexFairFrontierTyping environmentInvariant bindingsInvariant
      reduceAtom roundIndex residual round.leftNodes answerTypes ∧
    TwoIndexFairFrontierTyping environmentInvariant bindingsInvariant
      reduceAtom roundIndex residual round.rightNodes answerTypes

/-- A finite fair-search snapshot records safe observed answers and a
frontier at the stated remaining-round index. -/
def TwoIndexFairSearchPrefixTyping
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (reduceAtom : AtomReducer) (roundIndex residual : Nat)
    (snapshot : FairSearchPrefix MatchingState (List Value))
    (answerTypes : List Ty) : Prop :=
  AllSafe (TwoIndexFairAnswerTyping bindingsInvariant residual answerTypes)
      snapshot.answers ∧
    TwoIndexFairFrontierTyping environmentInvariant bindingsInvariant
      reduceAtom roundIndex residual snapshot.frontier answerTypes

/-- Timeout or a safely typed finite fair-search prefix.  This predicate does
not require the remaining frontier to be empty. -/
def TwoIndexFairSearchResultSafe
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (reduceAtom : AtomReducer) (roundIndex residual : Nat)
    (result : FuelResult (FairSearchPrefix MatchingState (List Value)))
    (answerTypes : List Ty) : Prop :=
  result = .timeout ∨
    ∃ snapshot,
      result = .ok snapshot ∧
        TwoIndexFairSearchPrefixTyping environmentInvariant bindingsInvariant
          reduceAtom roundIndex residual snapshot answerTypes

theorem TwoIndexFairSearchResultSafe.notStuck
    (safe : TwoIndexFairSearchResultSafe environmentInvariant
      bindingsInvariant reduceAtom roundIndex residual result answerTypes) :
    result.NotStuck := by
  rcases safe with timeout | ⟨snapshot, success, snapshotTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-- The indexed information exposed by one successful actual matching-state
step. -/
inductive TwoIndexFairMatchingStepTyping
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (reduceAtom : AtomReducer) (roundIndex residual : Nat)
    (answerTypes : List Ty) :
    SearchStep MatchingState (List Value) → Prop where
  | yield
      (answerTyped : bindingsInvariant residual bindings answerTypes) :
      TwoIndexFairMatchingStepTyping environmentInvariant bindingsInvariant
        reduceAtom roundIndex residual answerTypes (.yield bindings)
  | expand
      (successorsTyped : TwoIndexMatchingStatesTyping environmentInvariant
        bindingsInvariant reduceAtom roundIndex residual successors
        answerTypes) :
      TwoIndexFairMatchingStepTyping environmentInvariant bindingsInvariant
        reduceAtom roundIndex residual answerTypes (.expand successors)

/-- A successful actual state step consumes one operational search layer.
Completed bindings are weakened to the retained logical index, whereas hit
successors already carry the strict predecessor index in the local
certificate. -/
theorem stepMatchingState_twoIndexFairSafe
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (stateTyped : TwoIndexMatchingStateTyping environmentInvariant
      bindingsInvariant reduceAtom (roundIndex + 1) residual state
      answerTypes)
    (success : stepMatchingState reduceAtom state = .ok observation) :
    TwoIndexFairMatchingStepTyping environmentInvariant bindingsInvariant
      reduceAtom roundIndex residual answerTypes observation := by
  cases stateTyped with
  | yield environmentTyped bindingsTyped =>
      simp only [stepMatchingState] at success
      cases success
      exact .yield
        (bindingsDownward.mono bindingsTyped (by omega))
  | reduce environmentTyped bindingsTyped atomSafe =>
      cases atomSafe with
      | timeout reduced =>
          simp [stepMatchingState, reduced] at success
      | hit reduction reduced successorsTyped =>
          simp [stepMatchingState, reduced] at success
          subst observation
          exact .expand successorsTyped

/-- A state with one available round cannot make the actual matching step
return the runtime coverage-failure result `stuck`.  Local timeout remains
possible. -/
theorem stepMatchingState_twoIndexFair_notStuck
    (stateTyped : TwoIndexMatchingStateTyping environmentInvariant
      bindingsInvariant reduceAtom (roundIndex + 1) residual state
      answerTypes) :
    (stepMatchingState reduceAtom state).NotStuck := by
  cases stateTyped with
  | yield environmentTyped bindingsTyped => trivial
  | reduce environmentTyped bindingsTyped atomSafe =>
      cases atomSafe with
      | timeout reduced =>
          simp [stepMatchingState, reduced, FuelResult.NotStuck]
      | hit reduction reduced successorsTyped =>
          simp [stepMatchingState, reduced, FuelResult.NotStuck]

/-- One successful fair round consumes exactly one round index throughout
the frontier.  Right children use downward closure for the unvisited tails;
left children use the strict-predecessor successor certificates produced by
the visited heads. -/
theorem fairReductionRound_twoIndexSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    {frontier : List (List MatchingState)}
    (frontierTyped : TwoIndexFairFrontierTyping environmentInvariant
      bindingsInvariant reduceAtom (roundIndex + 1) residual frontier
      answerTypes)
    {round : FairRound MatchingState (List Value)}
    (success : fairReductionRound (stepMatchingState reduceAtom) frontier =
      .ok round) :
    TwoIndexFairRoundTyping environmentInvariant bindingsInvariant reduceAtom
      roundIndex residual round answerTypes := by
  induction frontier generalizing round with
  | nil =>
      simp only [fairReductionRound] at success
      cases success
      simp [TwoIndexFairRoundTyping, FairRound.empty, AllSafe,
        FairFrontierSafe]
  | cons node frontier induction =>
      have remainingFrontierTyped : TwoIndexFairFrontierTyping
          environmentInvariant bindingsInvariant reduceAtom (roundIndex + 1)
          residual frontier answerTypes := by
        intro candidate member
        exact frontierTyped candidate (by simp [member])
      cases node with
      | nil =>
          exact induction remainingFrontierTyped success
      | cons state tail =>
          have nodeTyped := frontierTyped (state :: tail) (by simp)
          have stateTyped : TwoIndexMatchingStateTyping environmentInvariant
              bindingsInvariant reduceAtom (roundIndex + 1) residual state
              answerTypes :=
            nodeTyped state (by simp)
          have tailTypedAtSuccessor : TwoIndexMatchingStatesTyping
              environmentInvariant bindingsInvariant reduceAtom
              (roundIndex + 1) residual tail answerTypes := by
            intro candidate member
            exact nodeTyped candidate (by simp [member])
          have tailTyped : TwoIndexMatchingStatesTyping environmentInvariant
              bindingsInvariant reduceAtom roundIndex residual tail
              answerTypes :=
            tailTypedAtSuccessor.previous environmentDownward bindingsDownward
          simp only [fairReductionRound] at success
          rw [FuelResult.bind_eq_ok_iff] at success
          rcases success with ⟨observation, stepped, continued⟩
          rw [FuelResult.map_eq_ok_iff] at continued
          rcases continued with ⟨rest, restResult, outputEq⟩
          have restTyped := induction remainingFrontierTyped restResult
          have observationTyped := stepMatchingState_twoIndexFairSafe
            bindingsDownward stateTyped stepped
          cases observation with
          | yield answer =>
              cases observationTyped with
              | yield answerTyped =>
                  simp only at outputEq
                  subst round
                  rcases restTyped with
                    ⟨answersTyped, leftTyped, rightTyped⟩
                  refine ⟨?_, leftTyped, ?_⟩
                  · intro candidate member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact answerTyped
                    · exact answersTyped candidate member
                  · exact FairFrontierSafe.append
                      (nonemptyNode_safe tailTyped) rightTyped
          | expand successors =>
              cases observationTyped with
              | expand successorsTyped =>
                  simp only at outputEq
                  subst round
                  rcases restTyped with
                    ⟨answersTyped, leftTyped, rightTyped⟩
                  exact ⟨answersTyped,
                    FairFrontierSafe.append
                      (nonemptyNode_safe successorsTyped) leftTyped,
                    FairFrontierSafe.append
                      (nonemptyNode_safe tailTyped) rightTyped⟩

/-- A frontier whose states have one available round cannot make that round
return `stuck`. -/
theorem fairReductionRound_twoIndex_notStuck
    {frontier : List (List MatchingState)}
    (frontierTyped : TwoIndexFairFrontierTyping environmentInvariant
      bindingsInvariant reduceAtom (roundIndex + 1) residual frontier
      answerTypes) :
    (fairReductionRound (stepMatchingState reduceAtom) frontier).NotStuck := by
  induction frontier with
  | nil => trivial
  | cons node frontier induction =>
      have remainingFrontierTyped : TwoIndexFairFrontierTyping
          environmentInvariant bindingsInvariant reduceAtom (roundIndex + 1)
          residual frontier answerTypes := by
        intro candidate member
        exact frontierTyped candidate (by simp [member])
      cases node with
      | nil => exact induction remainingFrontierTyped
      | cons state tail =>
          have stateTyped : TwoIndexMatchingStateTyping environmentInvariant
              bindingsInvariant reduceAtom (roundIndex + 1) residual state
              answerTypes :=
            frontierTyped (state :: tail) (by simp) state (by simp)
          simp only [fairReductionRound]
          apply FuelResult.bind_notStuck
            (resultSafe := stepMatchingState_twoIndexFair_notStuck stateTyped)
          intro observation
          exact FuelResult.map_notStuck _
            (induction remainingFrontierTyped)

/-- Adding one typed round to a prefix preserves old answers and installs the
strict-predecessor frontier produced by the round. -/
theorem FairSearchPrefix.advance_twoIndexSafe
    {snapshot : FairSearchPrefix MatchingState (List Value)}
    {round : FairRound MatchingState (List Value)}
    (prefixTyped : TwoIndexFairSearchPrefixTyping environmentInvariant
      bindingsInvariant reduceAtom (roundIndex + 1) residual snapshot
      answerTypes)
    (roundTyped : TwoIndexFairRoundTyping environmentInvariant
      bindingsInvariant reduceAtom roundIndex residual round answerTypes) :
    TwoIndexFairSearchPrefixTyping environmentInvariant bindingsInvariant
      reduceAtom roundIndex residual (snapshot.advance round) answerTypes := by
  rcases prefixTyped with ⟨oldAnswersTyped, oldFrontierTyped⟩
  rcases roundTyped with ⟨newAnswersTyped, leftTyped, rightTyped⟩
  exact ⟨AllSafe.append oldAnswersTyped newAnswersTyped,
    FairFrontierSafe.append leftTyped rightTyped⟩

/-- Running any finite number of successful rounds consumes that many
operational index layers and preserves the retained logical index on all
observed answers.  `remaining` permits callers to retain additional search
layers on the returned frontier. -/
theorem fairReductionRounds_twoIndexSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (rounds remaining : Nat)
    {snapshot output : FairSearchPrefix MatchingState (List Value)}
    (prefixTyped : TwoIndexFairSearchPrefixTyping environmentInvariant
      bindingsInvariant reduceAtom (rounds + remaining) residual snapshot
      answerTypes)
    (success : fairReductionRounds (stepMatchingState reduceAtom) rounds
      snapshot = .ok output) :
    TwoIndexFairSearchPrefixTyping environmentInvariant bindingsInvariant
      reduceAtom remaining residual output answerTypes := by
  induction rounds generalizing snapshot output with
  | zero =>
      simp only [fairReductionRounds] at success
      cases success
      simpa using prefixTyped
  | succ rounds induction =>
      have indexEq : Nat.succ rounds + remaining =
          (rounds + remaining) + 1 := by omega
      rw [indexEq] at prefixTyped
      simp only [fairReductionRounds] at success
      rw [FuelResult.bind_eq_ok_iff] at success
      rcases success with ⟨round, roundResult, continued⟩
      have roundTyped := fairReductionRound_twoIndexSafe
        environmentDownward bindingsDownward prefixTyped.2 roundResult
      have advancedTyped :=
        FairSearchPrefix.advance_twoIndexSafe prefixTyped roundTyped
      exact induction advancedTyped continued

/-- Typed finite-round fair matching can return only `timeout` or a prefix;
it never returns `stuck`. -/
theorem fairReductionRounds_twoIndex_notStuck
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (rounds remaining : Nat)
    (snapshot : FairSearchPrefix MatchingState (List Value))
    (prefixTyped : TwoIndexFairSearchPrefixTyping environmentInvariant
      bindingsInvariant reduceAtom (rounds + remaining) residual snapshot
      answerTypes) :
    (fairReductionRounds (stepMatchingState reduceAtom) rounds snapshot).NotStuck := by
  induction rounds generalizing snapshot with
  | zero => trivial
  | succ rounds induction =>
      have indexEq : Nat.succ rounds + remaining =
          (rounds + remaining) + 1 := by omega
      rw [indexEq] at prefixTyped
      cases result : fairReductionRound (stepMatchingState reduceAtom)
          snapshot.frontier with
      | timeout =>
          simp [fairReductionRounds, result, FuelResult.NotStuck]
      | stuck =>
          have contradiction := fairReductionRound_twoIndex_notStuck
            prefixTyped.2
          simp [result, FuelResult.NotStuck] at contradiction
      | ok round =>
          simp only [fairReductionRounds, result, FuelResult.bind_ok]
          have roundTyped := fairReductionRound_twoIndexSafe
            environmentDownward bindingsDownward prefixTyped.2 result
          exact induction (snapshot.advance round)
            (FairSearchPrefix.advance_twoIndexSafe prefixTyped roundTyped)

/-- Packaged result safety for any bounded fair execution: local exhaustion
is `timeout`; every successful observation contains safe answers and a safe
remaining frontier; `stuck` is impossible. -/
theorem fairReductionRounds_twoIndexResultSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (rounds remaining : Nat)
    (snapshot : FairSearchPrefix MatchingState (List Value))
    (prefixTyped : TwoIndexFairSearchPrefixTyping environmentInvariant
      bindingsInvariant reduceAtom (rounds + remaining) residual snapshot
      answerTypes) :
    TwoIndexFairSearchResultSafe environmentInvariant bindingsInvariant
      reduceAtom remaining residual
      (fairReductionRounds (stepMatchingState reduceAtom) rounds snapshot)
      answerTypes := by
  cases result : fairReductionRounds (stepMatchingState reduceAtom) rounds
      snapshot with
  | timeout => exact .inl rfl
  | stuck =>
      have contradiction := fairReductionRounds_twoIndex_notStuck
        environmentDownward bindingsDownward rounds remaining snapshot
        prefixTyped
      simp [result, FuelResult.NotStuck] at contradiction
  | ok output =>
      exact .inr ⟨output, rfl,
        fairReductionRounds_twoIndexSafe environmentDownward bindingsDownward
          rounds remaining prefixTyped result⟩

/-- Public finite-prefix safety for actual matching states.  The input state
list is one binary-reduction-tree node. -/
theorem fairReductionPrefix_twoIndexSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (rounds remaining : Nat) {states : List MatchingState}
    (statesTyped : TwoIndexMatchingStatesTyping environmentInvariant
      bindingsInvariant reduceAtom (rounds + remaining) residual states
      answerTypes)
    {output : FairSearchPrefix MatchingState (List Value)}
    (success : fairReductionPrefix (stepMatchingState reduceAtom) rounds
      states = .ok output) :
    TwoIndexFairSearchPrefixTyping environmentInvariant bindingsInvariant
      reduceAtom remaining residual output answerTypes := by
  apply fairReductionRounds_twoIndexSafe environmentDownward bindingsDownward
    rounds remaining
      (snapshot := { answers := [], frontier := nonemptyNode states })
  · exact ⟨by simp [AllSafe], nonemptyNode_safe statesTyped⟩
  · exact success

/-- Public non-stuck theorem for the same bounded fair prefix.  It is a
safety result only; it makes no claim that any answer will be reached within
the selected number of rounds. -/
theorem fairReductionPrefix_twoIndex_notStuck
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (rounds remaining : Nat) (states : List MatchingState)
    (statesTyped : TwoIndexMatchingStatesTyping environmentInvariant
      bindingsInvariant reduceAtom (rounds + remaining) residual states
      answerTypes) :
    (fairReductionPrefix (stepMatchingState reduceAtom) rounds states).NotStuck := by
  apply fairReductionRounds_twoIndex_notStuck environmentDownward
    bindingsDownward rounds remaining
      { answers := [], frontier := nonemptyNode states }
  exact ⟨by simp [AllSafe], nonemptyNode_safe statesTyped⟩

/-- Packaged timeout-or-prefix safety for the public actual-matching entry
point. -/
theorem fairReductionPrefix_twoIndexResultSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (rounds remaining : Nat) (states : List MatchingState)
    (statesTyped : TwoIndexMatchingStatesTyping environmentInvariant
      bindingsInvariant reduceAtom (rounds + remaining) residual states
      answerTypes) :
    TwoIndexFairSearchResultSafe environmentInvariant bindingsInvariant
      reduceAtom remaining residual
      (fairReductionPrefix (stepMatchingState reduceAtom) rounds states)
      answerTypes := by
  apply fairReductionRounds_twoIndexResultSafe environmentDownward
    bindingsDownward rounds remaining
      { answers := [], frontier := nonemptyNode states }
  exact ⟨by simp [AllSafe], nonemptyNode_safe statesTyped⟩

end TypePM.Runtime
