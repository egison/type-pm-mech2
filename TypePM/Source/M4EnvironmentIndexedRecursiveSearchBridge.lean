import TypePM.Source.M4PatternIndexedRecursiveDispatchBridge
import TypePM.ValueIndexedMatchingSearchSafety

/-!
# Environment-indexed bounded matching search

`M4PatternIndexedRecursiveDispatchBridge` keeps the original
`EnvironmentTyping` judgment in its general M4 endpoint.  That is appropriate
for ordinary values, but it cannot classify an environment containing a
recursive closure whose body uses matcher literals or `matchAll`.

This module adds a parallel, proof-only search boundary.  The ordinary
environment and the accumulated bindings/answers are checked by two
independent caller-selected relations.  Each nonempty state then carries a
*local reducer certificate*: the next atom either times out, or its actual
reduction produces successor states certified at the strictly smaller DFS
index.  Thus the premise is about one reducer call, not about the result of
the complete search.  No existing runtime or typing judgment is weakened.

Separating the two relations is essential for recursive closures.  A caller
may use `FuelEnvironmentSafe` for both the fixed environment and returned
bindings, possibly at different logical indices.  The older structural
endpoint remains below as the specialization whose binding relation is
`ValueTypings`.
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
      (bindingsInvariant : MatchingBindingsInvariant)
      (reduceAtom : AtomReducer) : Nat → MatchingState → List Ty → Prop where
    | zero :
        EnvironmentIndexedMatchingStateTyping environmentInvariant
          bindingsInvariant reduceAtom 0 state answerTypes
    | yield
        (environmentTyped : environmentInvariant environment environmentTypes)
        (bindingsTyped : bindingsInvariant bindings answerTypes) :
        EnvironmentIndexedMatchingStateTyping environmentInvariant
          bindingsInvariant reduceAtom (fuel + 1)
          ⟨[], environment, bindings⟩ answerTypes
    | reduce
        (environmentTyped : environmentInvariant environment environmentTypes)
        (bindingsTyped : bindingsInvariant bindings bindingTypes)
        (atomSafe : EnvironmentIndexedAtomReducerCertificate
          environmentInvariant bindingsInvariant reduceAtom fuel environment
          bindings atom remaining answerTypes) :
        EnvironmentIndexedMatchingStateTyping environmentInvariant
          bindingsInvariant reduceAtom (fuel + 1)
          ⟨atom :: remaining, environment, bindings⟩ answerTypes

  /-- Exact local certificate for the reducer call at the head of one state.
  A successful hit checks only its concrete successor states at the predecessor
  DFS index; neither a desired answer list nor a completed-search equation is a
  field. -/
  inductive EnvironmentIndexedAtomReducerCertificate
      (environmentInvariant : MatchingEnvironmentInvariant)
      (bindingsInvariant : MatchingBindingsInvariant)
      (reduceAtom : AtomReducer) : Nat → ValueEnvironment → List Value →
        MatchingAtom → List MatchingAtom → List Ty → Prop where
    | timeout
        (reduced : reduceAtom (bindings ++ environment) atom = .timeout) :
        EnvironmentIndexedAtomReducerCertificate environmentInvariant
          bindingsInvariant reduceAtom fuel environment bindings atom remaining
          answerTypes
    | hit
        (reduction : AtomReduction)
        (reduced : reduceAtom (bindings ++ environment) atom =
          .ok (.hit reduction))
        (successorsTyped : ∀ successor ∈
          MatchingState.successors
            ⟨atom :: remaining, environment, bindings⟩ remaining reduction,
          EnvironmentIndexedMatchingStateTyping environmentInvariant
            bindingsInvariant reduceAtom fuel successor answerTypes) :
        EnvironmentIndexedAtomReducerCertificate environmentInvariant
          bindingsInvariant reduceAtom fuel environment bindings atom remaining
          answerTypes

end

mutual

  /-- Forget one available DFS state visit. -/
  theorem EnvironmentIndexedMatchingStateTyping.previous
      (typing : EnvironmentIndexedMatchingStateTyping environmentInvariant
        bindingsInvariant reduceAtom (fuel + 1) state answerTypes) :
      EnvironmentIndexedMatchingStateTyping environmentInvariant
        bindingsInvariant reduceAtom fuel state answerTypes := by
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
        bindingsInvariant reduceAtom (fuel + 1) environment bindings atom
        remaining answerTypes) :
      EnvironmentIndexedAtomReducerCertificate environmentInvariant
        bindingsInvariant reduceAtom fuel environment bindings atom remaining
        answerTypes := by
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
    (bindingsInvariant : MatchingBindingsInvariant) (reduceAtom : AtomReducer)
    (fuel : Nat) (states : List MatchingState) (answerTypes : List Ty) : Prop :=
  ∀ state ∈ states,
    EnvironmentIndexedMatchingStateTyping environmentInvariant
      bindingsInvariant reduceAtom fuel state answerTypes

theorem EnvironmentIndexedMatchingStatesTyping.previous
    (typing : EnvironmentIndexedMatchingStatesTyping environmentInvariant
      bindingsInvariant reduceAtom (fuel + 1) states answerTypes) :
    EnvironmentIndexedMatchingStatesTyping environmentInvariant
      bindingsInvariant reduceAtom fuel states answerTypes := by
  intro state member
  exact (typing state member).previous

/-- A finite tree of local reducer calls.  This is stronger than any one DFS
fuel certificate but still strictly local: a hit stores only its immediate
successors, recursively, and never stores a complete-search result. -/
inductive EnvironmentIndexedFiniteMatchingStateTyping
    (environmentInvariant : MatchingEnvironmentInvariant)
    (bindingsInvariant : MatchingBindingsInvariant)
    (reduceAtom : AtomReducer) : MatchingState → List Ty → Prop where
  | yield
      (environmentTyped : environmentInvariant environment environmentTypes)
      (bindingsTyped : bindingsInvariant bindings answerTypes) :
      EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
        bindingsInvariant reduceAtom ⟨[], environment, bindings⟩ answerTypes
  | timeout
      (environmentTyped : environmentInvariant environment environmentTypes)
      (bindingsTyped : bindingsInvariant bindings bindingTypes)
      (reduced : reduceAtom (bindings ++ environment) atom = .timeout) :
      EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
        bindingsInvariant reduceAtom
        ⟨atom :: remaining, environment, bindings⟩ answerTypes
  | hit
      (environmentTyped : environmentInvariant environment environmentTypes)
      (bindingsTyped : bindingsInvariant bindings bindingTypes)
      (reduction : AtomReduction)
      (reduced : reduceAtom (bindings ++ environment) atom =
        .ok (.hit reduction))
      (successorsTyped : ∀ successor ∈
        MatchingState.successors
          ⟨atom :: remaining, environment, bindings⟩ remaining reduction,
        EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
          bindingsInvariant reduceAtom successor answerTypes) :
      EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
        bindingsInvariant reduceAtom
        ⟨atom :: remaining, environment, bindings⟩ answerTypes

/-- A finite local-reduction tree supplies the bounded certificate at every
DFS index. -/
theorem EnvironmentIndexedFiniteMatchingStateTyping.toFuel
    (typing : EnvironmentIndexedFiniteMatchingStateTyping environmentInvariant
      bindingsInvariant reduceAtom state answerTypes) :
    ∀ fuel,
      EnvironmentIndexedMatchingStateTyping environmentInvariant
        bindingsInvariant reduceAtom fuel state answerTypes := by
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
The fixed environment and every returned answer use the two independently
selected relations. -/
theorem depthFirstMatching_environmentIndexedSafeWith
    (statesTyped : EnvironmentIndexedMatchingStatesTyping environmentInvariant
      bindingsInvariant reduceAtom fuel states answerTypes) :
    MatchingSearchResultSafeWith bindingsInvariant answerTypes
      (depthFirstFuel (stepMatchingState reduceAtom) fuel states) := by
  induction fuel generalizing states with
  | zero =>
      cases states with
      | nil => exact .inr ⟨[], rfl, by
          intro answer member
          simp at member⟩
      | cons state rest => exact .inl rfl
  | succ fuel induction =>
      cases states with
      | nil => exact .inr ⟨[], rfl, by
          intro answer member
          simp at member⟩
      | cons state rest =>
          have stateTyped := statesTyped state (by simp)
          have restTyped : EnvironmentIndexedMatchingStatesTyping
              environmentInvariant bindingsInvariant reduceAtom fuel rest
              answerTypes := by
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
                      environmentInvariant bindingsInvariant reduceAtom fuel
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

/-- Direct endpoint for one already evaluated target/matcher pair under two
caller-selected relations.  No conversion to `EnvironmentTyping` or
`ValueTypings` is performed. -/
theorem searchPatternFuel_environmentIndexedSafeWith
    (initialTyped : EnvironmentIndexedMatchingStateTyping environmentInvariant
      bindingsInvariant (evaluationAtomReducer eval) fuel
      ⟨[⟨pattern, matcher, target⟩], environment, []⟩ bindingTypes) :
    MatchingSearchResultSafeWith bindingsInvariant bindingTypes
      (searchPatternFuel eval fuel environment pattern matcher target) := by
  unfold searchPatternFuel searchMatchingFuel
  apply depthFirstMatching_environmentIndexedSafeWith
    (environmentInvariant := environmentInvariant)
    (bindingsInvariant := bindingsInvariant)
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact initialTyped

/-- Structural-binding specialization retained for existing callers. -/
theorem depthFirstMatching_environmentIndexedTypedSafe
    (statesTyped : EnvironmentIndexedMatchingStatesTyping environmentInvariant
      ValueTypings reduceAtom fuel states answerTypes) :
    TypedMatchingSearchResult answerTypes
      (depthFirstFuel (stepMatchingState reduceAtom) fuel states) :=
  depthFirstMatching_environmentIndexedSafeWith statesTyped

/-- Structural-binding specialization retained for existing callers.  The
fixed environment may still use a relation that admits recursive closures. -/
theorem searchPatternFuel_environmentIndexedTypedSafe
    (initialTyped : EnvironmentIndexedMatchingStateTyping environmentInvariant
      ValueTypings (evaluationAtomReducer eval) fuel
      ⟨[⟨pattern, matcher, target⟩], environment, []⟩ bindingTypes) :
    TypedMatchingSearchResult bindingTypes
      (searchPatternFuel eval fuel environment pattern matcher target) :=
  searchPatternFuel_environmentIndexedSafeWith initialTyped

end TypePM.Runtime
