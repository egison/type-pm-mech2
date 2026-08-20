import TypePM.Source.M4PatternIndexedRecursiveDispatchBridge

/-!
# Environment-indexed bounded matching search

`M4PatternIndexedRecursiveDispatchBridge` keeps the original
`EnvironmentTyping` judgment in its general M4 endpoint.  That is appropriate
for ordinary values, but it cannot classify an environment containing a
recursive closure whose body uses matcher literals or `matchAll`.

This module adds a parallel, proof-only search boundary.  The ordinary
environment is checked by a caller-selected relation.  Each nonempty state
then carries a *local reducer certificate*: the next atom either times out, or
its actual reduction produces successor states certified at the strictly
smaller DFS index.  Thus the premise is about one reducer call, not about the
result of the complete search.  No existing runtime or typing judgment is
weakened.

The relation intentionally keeps ordinary `ValueTypings` for accumulated
answers.  A caller whose fixed environment contains a recursive closure can
therefore use `FuelEnvironmentSafe` (or a more precise invariant) for that
environment while proving ordinary first-order bindings in the existing
value-typing layer.
-/

namespace TypePM.Runtime

/-- A caller-selected, type-indexed invariant for the ordinary environment of
one matching state.  It may be instantiated by `EnvironmentTyping`, by a
fuel-indexed logical relation, or by a concrete fixture invariant. -/
abbrev MatchingEnvironmentInvariant := ValueEnvironment → List Ty → Prop

mutual

  /-- Bounded safety of one matching state under an arbitrary ordinary-
  environment invariant.  The zero index is unconditional: a nonempty DFS
  worklist times out before inspecting the state, environment, or bindings. -/
  inductive EnvironmentIndexedMatchingStateTyping
      (environmentInvariant : MatchingEnvironmentInvariant)
      (reduceAtom : AtomReducer) : Nat → MatchingState → List Ty → Prop where
    | zero :
        EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom 0
          state answerTypes
    | yield
        (environmentTyped : environmentInvariant environment environmentTypes)
        (bindingsTyped : ValueTypings bindings answerTypes) :
        EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom
          (fuel + 1) ⟨[], environment, bindings⟩ answerTypes
    | reduce
        (environmentTyped : environmentInvariant environment environmentTypes)
        (bindingsTyped : ValueTypings bindings bindingTypes)
        (atomSafe : EnvironmentIndexedAtomReducerCertificate
          environmentInvariant reduceAtom fuel environment bindings atom
          remaining answerTypes) :
        EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom
          (fuel + 1) ⟨atom :: remaining, environment, bindings⟩ answerTypes

  /-- Exact local certificate for the reducer call at the head of one state.
  A successful hit checks only its concrete successor states at the predecessor
  DFS index; neither a desired answer list nor a completed-search equation is a
  field. -/
  inductive EnvironmentIndexedAtomReducerCertificate
      (environmentInvariant : MatchingEnvironmentInvariant)
      (reduceAtom : AtomReducer) : Nat → ValueEnvironment → List Value →
        MatchingAtom → List MatchingAtom → List Ty → Prop where
    | timeout
        (reduced : reduceAtom (bindings ++ environment) atom = .timeout) :
        EnvironmentIndexedAtomReducerCertificate environmentInvariant reduceAtom
          fuel environment bindings atom remaining answerTypes
    | hit
        (reduction : AtomReduction)
        (reduced : reduceAtom (bindings ++ environment) atom =
          .ok (.hit reduction))
        (successorsTyped : ∀ successor ∈
          MatchingState.successors
            ⟨atom :: remaining, environment, bindings⟩ remaining reduction,
          EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom
            fuel successor answerTypes) :
        EnvironmentIndexedAtomReducerCertificate environmentInvariant reduceAtom
          fuel environment bindings atom remaining answerTypes

end

mutual

  /-- Forget one available DFS state visit. -/
  theorem EnvironmentIndexedMatchingStateTyping.previous
      (typing : EnvironmentIndexedMatchingStateTyping environmentInvariant
        reduceAtom (fuel + 1) state answerTypes) :
      EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom fuel
        state answerTypes := by
    cases fuel with
    | zero =>
        cases typing with
        | yield environmentTyped bindingsTyped =>
            exact .zero
        | reduce environmentTyped bindingsTyped atomSafe =>
            exact .zero
    | succ fuel =>
        cases typing with
        | yield environmentTyped bindingsTyped =>
            exact .yield environmentTyped bindingsTyped
        | reduce environmentTyped bindingsTyped atomSafe =>
            exact .reduce environmentTyped bindingsTyped atomSafe.previous

  /-- A local hit certificate is downward closed because every concrete
  successor certificate is downward closed. -/
  theorem EnvironmentIndexedAtomReducerCertificate.previous
      (typing : EnvironmentIndexedAtomReducerCertificate environmentInvariant
        reduceAtom (fuel + 1) environment bindings atom remaining answerTypes) :
      EnvironmentIndexedAtomReducerCertificate environmentInvariant reduceAtom
        fuel environment bindings atom remaining answerTypes := by
    cases typing with
    | timeout reduced => exact .timeout reduced
    | hit reduction reduced successorsTyped =>
        exact .hit reduction reduced (by
          intro successor member
          exact (successorsTyped successor member).previous)

end

/-- Pointwise form for the ordered DFS state list. -/
def EnvironmentIndexedMatchingStatesTyping
    (environmentInvariant : MatchingEnvironmentInvariant)
    (reduceAtom : AtomReducer) (fuel : Nat) (states : List MatchingState)
    (answerTypes : List Ty) : Prop :=
  ∀ state ∈ states,
    EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom fuel
      state answerTypes

theorem EnvironmentIndexedMatchingStatesTyping.previous
    (typing : EnvironmentIndexedMatchingStatesTyping environmentInvariant
      reduceAtom (fuel + 1) states answerTypes) :
    EnvironmentIndexedMatchingStatesTyping environmentInvariant reduceAtom fuel
      states answerTypes := by
  intro state member
  exact (typing state member).previous

/-- A finite tree of local reducer calls.  This is stronger than any one DFS
fuel certificate but still strictly local: a hit stores only its immediate
successors, recursively, and never stores a complete-search result. -/
inductive EnvironmentIndexedFiniteMatchingStateTyping
    (environmentInvariant : MatchingEnvironmentInvariant)
    (reduceAtom : AtomReducer) : MatchingState → List Ty → Prop where
  | yield
      (environmentTyped : environmentInvariant environment environmentTypes)
      (bindingsTyped : ValueTypings bindings answerTypes) :
      EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
        reduceAtom ⟨[], environment, bindings⟩ answerTypes
  | timeout
      (environmentTyped : environmentInvariant environment environmentTypes)
      (bindingsTyped : ValueTypings bindings bindingTypes)
      (reduced : reduceAtom (bindings ++ environment) atom = .timeout) :
      EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
        reduceAtom ⟨atom :: remaining, environment, bindings⟩ answerTypes
  | hit
      (environmentTyped : environmentInvariant environment environmentTypes)
      (bindingsTyped : ValueTypings bindings bindingTypes)
      (reduction : AtomReduction)
      (reduced : reduceAtom (bindings ++ environment) atom =
        .ok (.hit reduction))
      (successorsTyped : ∀ successor ∈
        MatchingState.successors
          ⟨atom :: remaining, environment, bindings⟩ remaining reduction,
        EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
          reduceAtom successor answerTypes) :
      EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
        reduceAtom ⟨atom :: remaining, environment, bindings⟩ answerTypes

/-- A finite local-reduction tree supplies the bounded certificate at every
DFS index. -/
theorem EnvironmentIndexedFiniteMatchingStateTyping.toFuel
    (typing : EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
      reduceAtom state answerTypes) :
    ∀ fuel,
      EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom fuel
        state answerTypes := by
  intro fuel
  induction fuel generalizing state with
  | zero =>
      cases typing with
      | yield environmentTyped bindingsTyped =>
          exact .zero
      | timeout environmentTyped bindingsTyped reduced =>
          exact .zero
      | hit environmentTyped bindingsTyped reduction reduced successorsTyped =>
          exact .zero
  | succ fuel induction =>
      cases typing with
      | yield environmentTyped bindingsTyped =>
          exact .yield environmentTyped bindingsTyped
      | timeout environmentTyped bindingsTyped reduced =>
          exact .reduce environmentTyped bindingsTyped (.timeout reduced)
      | hit environmentTyped bindingsTyped reduction reduced successorsTyped =>
          exact .reduce environmentTyped bindingsTyped (.hit reduction reduced (by
            intro successor member
            exact induction (successorsTyped successor member)))

/-- Local reducer certificates lift to the exact bounded DFS implementation.
Every returned answer has ordinary pointwise value typing, while the ordinary
environment itself is governed only by the caller-selected invariant. -/
theorem depthFirstMatching_environmentIndexedTypedSafe
    (statesTyped : EnvironmentIndexedMatchingStatesTyping environmentInvariant
      reduceAtom fuel states answerTypes) :
    TypedMatchingSearchResult answerTypes
      (depthFirstFuel (stepMatchingState reduceAtom) fuel states) := by
  induction fuel generalizing states with
  | zero =>
      cases states with
      | nil => exact .inr ⟨[], rfl, by simp [MatchingAnswersTyping]⟩
      | cons state rest => exact .inl rfl
  | succ fuel induction =>
      cases states with
      | nil => exact .inr ⟨[], rfl, by simp [MatchingAnswersTyping]⟩
      | cons state rest =>
          have stateTyped := statesTyped state (by simp)
          have restTyped : EnvironmentIndexedMatchingStatesTyping
              environmentInvariant reduceAtom fuel rest answerTypes := by
            intro candidate member
            exact (statesTyped candidate (by simp [member])).previous
          cases stateTyped with
          | yield environmentTyped bindingsTyped =>
              rename_i environment environmentTypes bindings
              rcases induction restTyped with tailTimeout |
                ⟨answers, searched, answersTyped⟩
              · exact .inl (by
                  simp [depthFirstFuel, stepMatchingState, tailTimeout,
                    FuelResult.map])
              · exact .inr ⟨bindings :: answers, by
                    simp [depthFirstFuel, stepMatchingState, searched,
                      FuelResult.map], by
                    intro candidate member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact bindingsTyped
                    · exact answersTyped candidate member⟩
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
                  have nextTyped : EnvironmentIndexedMatchingStatesTyping
                      environmentInvariant reduceAtom fuel
                      (successors ++ rest) answerTypes := by
                    intro candidate member
                    rcases List.mem_append.mp member with inSuccessors | inRest
                    · exact successorsTyped candidate (by
                        simpa [successors, current] using inSuccessors)
                    · exact restTyped candidate inRest
                  rcases induction nextTyped with nextTimeout |
                    ⟨answers, searched, answersTyped⟩
                  · exact .inl (by
                      simp [depthFirstFuel, stepMatchingState, reduced,
                        successors, current, nextTimeout])
                  · exact .inr ⟨answers, by
                        simp [depthFirstFuel, stepMatchingState, reduced,
                          successors, current, searched], answersTyped⟩

/-- Direct endpoint for one already evaluated target/matcher pair.  The
initial certificate may use an invariant that accepts recursive closures in
`environment`; no conversion to old `EnvironmentTyping` is performed. -/
theorem searchPatternFuel_environmentIndexedTypedSafe
    (initialTyped : EnvironmentIndexedMatchingStateTyping environmentInvariant
      (evaluationAtomReducer eval) fuel
      ⟨[⟨pattern, matcher, target⟩], environment, []⟩ bindingTypes) :
    TypedMatchingSearchResult bindingTypes
      (searchPatternFuel eval fuel environment pattern matcher target) := by
  unfold searchPatternFuel searchMatchingFuel
  apply depthFirstMatching_environmentIndexedTypedSafe
    (environmentInvariant := environmentInvariant)
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact initialTyped

end TypePM.Runtime
