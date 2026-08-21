import TypePM.ValueIndexedMatchingSearchSafety
import TypePM.Runtime.MatchingSearch

/-!
# Two-index safety for bounded matching search

The number of DFS states that may still be visited is an operational search
budget.  The logical index retained on successful answers is a different
quantity.  This module keeps them separate.

A state with search budget `searchFuel` and requested answer index `residual`
requires its environment and accumulated bindings at
`searchFuel + residual`.  The certificate reserves one indexed layer per
possible state visit; a concrete reducer law must still prove that this budget
is sufficient for its callback.  Callers can incorporate a larger
callback-dependent offset in the selected invariant.  A completed answer is
weakened only at the end to `residual`.

The local certificate describes one actual reducer call and its immediate
successors.  It contains neither a complete-search equation nor a desired
answer list.
-/

namespace TypePM.Runtime

/-- A logical-indexed relation for a runtime environment or binding group. -/
abbrev IndexedMatchingInvariant :=
  Nat → List Value → List Ty → Prop

namespace IndexedMatchingInvariant

/-- One logical layer may be forgotten. -/
def DownwardClosed (invariant : IndexedMatchingInvariant) : Prop :=
  ∀ {index values targets},
    invariant (index + 1) values targets → invariant index values targets

/-- Equally indexed binding groups may be concatenated in runtime order. -/
def AppendClosed (invariant : IndexedMatchingInvariant) : Prop :=
  ∀ {index leftValues leftTypes rightValues rightTypes},
    invariant index leftValues leftTypes →
      invariant index rightValues rightTypes →
        invariant index (leftValues ++ rightValues)
          (leftTypes ++ rightTypes)

/-- Downward closure iterated from any larger logical index. -/
theorem DownwardClosed.mono
    (downward : DownwardClosed invariant)
    (safe : invariant larger values targets)
    (smaller_le : smaller ≤ larger) :
    invariant smaller values targets := by
  induction larger generalizing smaller with
  | zero =>
      have smaller_eq : smaller = 0 := Nat.eq_zero_of_le_zero smaller_le
      subst smaller
      exact safe
  | succ larger induction =>
      by_cases equal : smaller = larger + 1
      · subst smaller
        exact safe
      · have smaller_le_larger : smaller ≤ larger := by omega
        exact induction (downward safe) smaller_le_larger

theorem fuelEnvironmentSafe_downwardClosed :
    DownwardClosed FuelEnvironmentSafe := by
  intro index values targets safe
  exact safe.previous

theorem fuelEnvironmentSafe_appendClosed :
    AppendClosed FuelEnvironmentSafe := by
  intro index leftValues leftTypes rightValues rightTypes left right
  exact left.append right

end IndexedMatchingInvariant

mutual

  /-- One bounded matching state with independent search and result indices. -/
  inductive TwoIndexMatchingStateTyping
      (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
      (reduceAtom : AtomReducer) :
      Nat → Nat → MatchingState → List Ty → Prop where
    | zero :
        TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
          reduceAtom 0 residual state answerTypes
    | yield
        (environmentTyped : environmentInvariant (fuel + 1 + residual)
          environment environmentTypes)
        (bindingsTyped : bindingsInvariant (fuel + 1 + residual)
          bindings answerTypes) :
        TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
          reduceAtom (fuel + 1) residual
          ⟨[], environment, bindings⟩ answerTypes
    | reduce
        (environmentTyped : environmentInvariant (fuel + 1 + residual)
          environment environmentTypes)
        (bindingsTyped : bindingsInvariant (fuel + 1 + residual)
          bindings bindingTypes)
        (atomSafe : TwoIndexAtomReducerCertificate environmentInvariant
          bindingsInvariant reduceAtom fuel residual environment bindings atom
          remaining answerTypes) :
        TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
          reduceAtom (fuel + 1) residual
          ⟨atom :: remaining, environment, bindings⟩ answerTypes

  /-- Timeout or immediate successor preservation for one reducer call. -/
  inductive TwoIndexAtomReducerCertificate
      (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
      (reduceAtom : AtomReducer) :
      Nat → Nat → ValueEnvironment → List Value → MatchingAtom →
        List MatchingAtom → List Ty → Prop where
    | timeout
        (reduced : reduceAtom (bindings ++ environment) atom = .timeout) :
        TwoIndexAtomReducerCertificate environmentInvariant bindingsInvariant
          reduceAtom fuel residual environment bindings atom remaining
          answerTypes
    | hit
        (reduction : AtomReduction)
        (reduced : reduceAtom (bindings ++ environment) atom =
          .ok (.hit reduction))
        (successorsTyped : ∀ successor ∈
          MatchingState.successors
            ⟨atom :: remaining, environment, bindings⟩ remaining reduction,
          TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
            reduceAtom fuel residual successor answerTypes) :
        TwoIndexAtomReducerCertificate environmentInvariant bindingsInvariant
          reduceAtom fuel residual environment bindings atom remaining
          answerTypes

end

mutual

  /-- Forget one available DFS visit and its corresponding logical layer. -/
  theorem TwoIndexMatchingStateTyping.previous
      (environmentDownward :
        IndexedMatchingInvariant.DownwardClosed environmentInvariant)
      (bindingsDownward :
        IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
      (typing : TwoIndexMatchingStateTyping environmentInvariant
        bindingsInvariant reduceAtom (fuel + 1) residual state answerTypes) :
      TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
        reduceAtom fuel residual state answerTypes := by
    cases fuel with
    | zero =>
        cases typing <;> exact .zero
    | succ fuel =>
        cases typing with
        | yield environmentTyped bindingsTyped =>
            have indexEq : fuel + 1 + 1 + residual =
                (fuel + 1 + residual) + 1 := by omega
            rw [indexEq] at environmentTyped bindingsTyped
            exact .yield (environmentDownward environmentTyped)
              (bindingsDownward bindingsTyped)
        | reduce environmentTyped bindingsTyped atomSafe =>
            have indexEq : fuel + 1 + 1 + residual =
                (fuel + 1 + residual) + 1 := by omega
            rw [indexEq] at environmentTyped bindingsTyped
            exact .reduce (environmentDownward environmentTyped)
              (bindingsDownward bindingsTyped)
              (atomSafe.previous environmentDownward bindingsDownward)

  /-- Reducer certificates inherit downward closure from their successors. -/
  theorem TwoIndexAtomReducerCertificate.previous
      (environmentDownward :
        IndexedMatchingInvariant.DownwardClosed environmentInvariant)
      (bindingsDownward :
        IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
      (typing : TwoIndexAtomReducerCertificate environmentInvariant
        bindingsInvariant reduceAtom (fuel + 1) residual environment bindings
        atom remaining answerTypes) :
      TwoIndexAtomReducerCertificate environmentInvariant bindingsInvariant
        reduceAtom fuel residual environment bindings atom remaining
        answerTypes := by
    cases typing with
    | timeout reduced => exact .timeout reduced
    | hit reduction reduced successorsTyped =>
        exact .hit reduction reduced (by
          intro successor member
          exact (successorsTyped successor member).previous
            environmentDownward bindingsDownward)

end

/-- Pointwise safety for the ordered DFS state list. -/
def TwoIndexMatchingStatesTyping
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (reduceAtom : AtomReducer) (searchFuel residual : Nat)
    (states : List MatchingState) (answerTypes : List Ty) : Prop :=
  ∀ state ∈ states,
    TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
      reduceAtom searchFuel residual state answerTypes

theorem TwoIndexMatchingStatesTyping.previous
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (typing : TwoIndexMatchingStatesTyping environmentInvariant
      bindingsInvariant reduceAtom (fuel + 1) residual states answerTypes) :
    TwoIndexMatchingStatesTyping environmentInvariant bindingsInvariant
      reduceAtom fuel residual states answerTypes := by
  intro state member
  exact (typing state member).previous environmentDownward bindingsDownward

/-- Two-index local certificates lift to the exact bounded DFS. -/
theorem depthFirstMatching_twoIndexSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (statesTyped : TwoIndexMatchingStatesTyping environmentInvariant
      bindingsInvariant reduceAtom searchFuel residual states answerTypes) :
    MatchingSearchResultSafeWith (bindingsInvariant residual) answerTypes
      (depthFirstFuel (stepMatchingState reduceAtom) searchFuel states) := by
  induction searchFuel generalizing states with
  | zero =>
      cases states with
      | nil => exact .inr ⟨[], rfl, by
          intro answer member
          simp at member⟩
      | cons state rest => exact .inl rfl
  | succ searchFuel induction =>
      cases states with
      | nil => exact .inr ⟨[], rfl, by
          intro answer member
          simp at member⟩
      | cons state rest =>
          have stateTyped := statesTyped state (by simp)
          have restTyped : TwoIndexMatchingStatesTyping environmentInvariant
              bindingsInvariant reduceAtom searchFuel residual rest
              answerTypes := by
            intro candidate member
            exact (statesTyped candidate (by simp [member])).previous
              environmentDownward bindingsDownward
          cases stateTyped with
          | yield environmentTyped bindingsTyped =>
              rename_i environment environmentTypes bindings
              have answerSafe : bindingsInvariant residual bindings
                  answerTypes :=
                bindingsDownward.mono bindingsTyped (by omega)
              rcases induction restTyped with tailTimeout |
                ⟨answers, searched, answersSafe⟩
              · exact .inl (by
                  simp [depthFirstFuel, stepMatchingState, tailTimeout,
                    FuelResult.map])
              · exact .inr ⟨bindings :: answers, by
                    simp [depthFirstFuel, stepMatchingState, searched,
                      FuelResult.map], by
                    intro candidate member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact answerSafe
                    · exact answersSafe candidate member⟩
          | reduce environmentTyped bindingsTyped atomSafe =>
              rename_i environment environmentTypes bindings bindingTypes atom
                remaining
              cases atomSafe with
              | timeout reduced =>
                  exact .inl (by
                    simp [depthFirstFuel, stepMatchingState, reduced])
              | hit reduction reduced successorsTyped =>
                  let current : MatchingState :=
                    ⟨atom :: remaining, environment, bindings⟩
                  let successors :=
                    MatchingState.successors current remaining reduction
                  have nextTyped : TwoIndexMatchingStatesTyping
                      environmentInvariant bindingsInvariant reduceAtom
                      searchFuel residual (successors ++ rest) answerTypes := by
                    intro candidate member
                    rcases List.mem_append.mp member with inSuccessors | inRest
                    · exact successorsTyped candidate (by
                        simpa [successors, current] using inSuccessors)
                    · exact restTyped candidate inRest
                  rcases induction nextTyped with nextTimeout |
                    ⟨answers, searched, answersSafe⟩
                  · exact .inl (by
                      simp [depthFirstFuel, stepMatchingState, reduced,
                        successors, current, nextTimeout])
                  · exact .inr ⟨answers, by
                        simp [depthFirstFuel, stepMatchingState, reduced,
                          successors, current, searched], answersSafe⟩

/-- Direct two-index endpoint for one already evaluated target/matcher pair. -/
theorem searchPatternFuel_twoIndexSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (initialTyped : TwoIndexMatchingStateTyping environmentInvariant
      bindingsInvariant (evaluationAtomReducer eval) searchFuel residual
      ⟨[⟨pattern, matcher, target⟩], environment, []⟩ bindingTypes) :
    MatchingSearchResultSafeWith (bindingsInvariant residual) bindingTypes
      (searchPatternFuel eval searchFuel environment pattern matcher target) := by
  unfold searchPatternFuel searchMatchingFuel
  apply depthFirstMatching_twoIndexSafe environmentDownward bindingsDownward
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact initialTyped

end TypePM.Runtime
