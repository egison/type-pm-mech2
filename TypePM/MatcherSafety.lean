import TypePM.CoreSafety
import TypePM.Runtime.MatchingSearch

/-!
# Conditional safety for matching states

This module is deliberately separate from the closed integer/tuple expression
core in `RuntimeTyping` and `CoreSafety`.  It certifies the matching machinery
under an explicit typing relation for expressions embedded in value patterns.
User-defined matcher clauses, constructor patterns, and pattern functions need
additional callback preservation proofs before they can instantiate the atom
reducer contract below.

The order of the two contexts is significant.  `bindingTypes` describes the
source-ordered pattern bindings already collected by a matching state, while
`environmentTypes` describes the ordinary expression environment.  Embedded
expressions are checked in `bindingTypes ++ environmentTypes`, exactly as the
runtime evaluates them in `bindings ++ environment`.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Abstract typing for expressions evaluated inside value patterns. -/
abbrev EmbeddedExpressionTyping := List Ty → Source.Expr → Ty → Prop

/-- The evaluator callback used by value patterns either times out or returns
a value of the requested type.  This is the explicit termination/preservation
assumption at the boundary of the current matcher theorem. -/
def EmbeddedEvaluatorSafe
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value) : Prop :=
  ∀ {environmentTypes environment expression target},
    EnvironmentTyping environment environmentTypes →
    expressionTyping environmentTypes expression target →
    TypedResult target (eval environment expression)

mutual

  /-- Binding types contributed by the currently certified pattern fragment.
  Constructor, embedded pattern-function, and pattern-application nodes are
  intentionally absent until their runtime rules have preservation proofs. -/
  inductive PatternBinds
      (expressionTyping : EmbeddedExpressionTyping) :
      List Ty → List Ty → Pattern → Ty → List Ty → Prop where
    | var : PatternBinds expressionTyping environmentTypes bindingTypes
        .var target [target]
    | wild : PatternBinds expressionTyping environmentTypes bindingTypes
        .wild target []
    | value
        (typed : expressionTyping (bindingTypes ++ environmentTypes)
          expression target) :
        PatternBinds expressionTyping environmentTypes bindingTypes
          (.value expression) target []
    | tuple
        (items : PatternsBind expressionTyping environmentTypes bindingTypes
          patterns targets newBindings) :
        PatternBinds expressionTyping environmentTypes bindingTypes
          (.tuple patterns) (.prod targets) newBindings
    | and
        (left : PatternBinds expressionTyping environmentTypes bindingTypes
          leftPattern target leftBindings)
        (right : PatternBinds expressionTyping environmentTypes
          (bindingTypes ++ leftBindings) rightPattern target rightBindings) :
        PatternBinds expressionTyping environmentTypes bindingTypes
          (.and leftPattern rightPattern) target
          (leftBindings ++ rightBindings)

  /-- Left-to-right pattern-list binding.  Later items see all bindings from
  earlier items before the ordinary environment. -/
  inductive PatternsBind
      (expressionTyping : EmbeddedExpressionTyping) :
      List Ty → List Ty → List Pattern → List Ty → List Ty → Prop where
    | nil : PatternsBind expressionTyping environmentTypes bindingTypes
        [] [] []
    | cons
        (head : PatternBinds expressionTyping environmentTypes bindingTypes
          pattern target headBindings)
        (tail : PatternsBind expressionTyping environmentTypes
          (bindingTypes ++ headBindings) patterns targets tailBindings) :
        PatternsBind expressionTyping environmentTypes bindingTypes
          (pattern :: patterns) (target :: targets)
          (headBindings ++ tailBindings)

end

mutual

  /-- A pending atom is well typed in the built-in matcher fragment.  Its last
  index is the source-ordered type list that successful completion adds. -/
  inductive MatchingAtomTyping
      (expressionTyping : EmbeddedExpressionTyping) :
      List Ty → List Ty → MatchingAtom → List Ty → Prop where
    | somethingVar
        (targetTyped : ValueTyping target targetType) :
        MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨.var, .something, target⟩ [targetType]
    | somethingWild
        (targetTyped : ValueTyping target targetType) :
        MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨.wild, .something, target⟩ []
    | somethingValue
        (expressionTyped : expressionTyping
          (bindingTypes ++ environmentTypes) expression targetType)
        (targetTyped : ValueTyping target targetType) :
        MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨.value expression, .something, target⟩ []
    | tuple
        (atoms : List MatchingAtom)
        (zipped : MatchingAtomsZip patterns matchers targets atoms)
        (children : MatchingAtomsTyping expressionTyping environmentTypes
          bindingTypes atoms newBindings) :
        MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨.tuple patterns, .tuple matchers, .tuple targets⟩ newBindings
    | and
        (left : MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨leftPattern, matcher, target⟩ leftBindings)
        (right : MatchingAtomTyping expressionTyping environmentTypes
          (bindingTypes ++ leftBindings)
          ⟨rightPattern, matcher, target⟩ rightBindings) :
        MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨.and leftPattern rightPattern, matcher, target⟩
          (leftBindings ++ rightBindings)
    | productVar
        (targetTyped : ValueTyping target targetType) :
        MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨.var, .tuple matchers, target⟩ [targetType]
    | productWild
        (targetTyped : ValueTyping target targetType) :
        MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨.wild, .tuple matchers, target⟩ []
    | productValue
        (expressionTyped : expressionTyping
          (bindingTypes ++ environmentTypes) expression targetType)
        (targetTyped : ValueTyping target targetType) :
        MatchingAtomTyping expressionTyping environmentTypes bindingTypes
          ⟨.value expression, .tuple matchers, target⟩ []

  /-- Pending atoms are typed sequentially.  Each later atom sees the binding
  types produced by all atoms to its left. -/
  inductive MatchingAtomsTyping
      (expressionTyping : EmbeddedExpressionTyping) :
      List Ty → List Ty → List MatchingAtom → List Ty → Prop where
    | nil : MatchingAtomsTyping expressionTyping environmentTypes
        bindingTypes [] []
    | cons
        (atom : MatchingAtom) (atoms : List MatchingAtom)
        (headBindings tailBindings : List Ty)
        (head : MatchingAtomTyping expressionTyping environmentTypes
          bindingTypes atom headBindings)
        (tail : MatchingAtomsTyping expressionTyping environmentTypes
          (bindingTypes ++ headBindings) atoms tailBindings) :
        MatchingAtomsTyping expressionTyping environmentTypes bindingTypes
          (atom :: atoms) (headBindings ++ tailBindings)

end

/-! ## Typed environment and work-list algebra -/

theorem MatchingAtomTyping.and_atoms
    {expressionTyping : EmbeddedExpressionTyping}
    {environmentTypes bindingTypes : List Ty}
    {leftPattern rightPattern : Source.Pattern} {matcher target : Value}
    {leftBindings rightBindings : List Ty}
    (left : MatchingAtomTyping expressionTyping environmentTypes bindingTypes
      ⟨leftPattern, matcher, target⟩ leftBindings)
    (right : MatchingAtomTyping expressionTyping environmentTypes
      (bindingTypes ++ leftBindings)
      ⟨rightPattern, matcher, target⟩ rightBindings) :
    MatchingAtomsTyping expressionTyping environmentTypes bindingTypes
      [⟨leftPattern, matcher, target⟩, ⟨rightPattern, matcher, target⟩]
      (leftBindings ++ rightBindings) := by
  have tail : MatchingAtomsTyping expressionTyping environmentTypes
      (bindingTypes ++ leftBindings)
      [⟨rightPattern, matcher, target⟩] rightBindings := by
    simpa using
      MatchingAtomsTyping.cons _ [] rightBindings [] right
        (MatchingAtomsTyping.nil (bindingTypes :=
          (bindingTypes ++ leftBindings) ++ rightBindings))
  exact MatchingAtomsTyping.cons _ _ leftBindings rightBindings left tail

theorem ValueTypings.appendEnvironment :
    ∀ {bindings bindingTypes}, ValueTypings bindings bindingTypes →
      EnvironmentTyping environment environmentTypes →
      EnvironmentTyping (bindings ++ environment)
        (bindingTypes ++ environmentTypes)
  | _, _, .nil, environmentTyped => environmentTyped
  | _, _, .cons head tail, environmentTyped =>
      .cons head (tail.appendEnvironment environmentTyped)

theorem ValueTypings.append :
    ∀ {leftValues leftTypes}, ValueTypings leftValues leftTypes →
      ValueTypings rightValues rightTypes →
      ValueTypings (leftValues ++ rightValues) (leftTypes ++ rightTypes)
  | _, _, .nil, right => right
  | _, _, .cons head tail, right => .cons head (tail.append right)

theorem MatchingAtomsTyping.append :
    ∀ {bindingTypes leftAtoms leftBindings},
      MatchingAtomsTyping expressionTyping environmentTypes bindingTypes
        leftAtoms leftBindings →
      ∀ {rightAtoms rightBindings},
        MatchingAtomsTyping expressionTyping environmentTypes
          (bindingTypes ++ leftBindings) rightAtoms rightBindings →
        MatchingAtomsTyping expressionTyping environmentTypes bindingTypes
          (leftAtoms ++ rightAtoms) (leftBindings ++ rightBindings)
  | _, _, _, .nil, _, _, right => by simpa using right
  | bindingTypes, _, _,
      @MatchingAtomsTyping.cons _ _ _ atom atoms headBindings tailBindings
        head tail,
      rightAtoms, rightBindings, right => by
      have right' : MatchingAtomsTyping expressionTyping environmentTypes
          ((bindingTypes ++ headBindings) ++ tailBindings)
          rightAtoms rightBindings := by
        simpa [List.append_assoc] using right
      simpa [List.append_assoc] using
        MatchingAtomsTyping.cons atom (atoms ++ rightAtoms) headBindings
          (tailBindings ++ rightBindings) head
          (tail.append right')

/-- One reduction preserves the atom's promised binding types on every
actual continuation branch.  An empty branch list is ordinary match failure,
so it needs no fictitious successor proof. -/
inductive AtomReductionTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (environmentTypes bindingTypes expectedBindings : List Ty)
    (reduction : AtomReduction) : Prop where
  | intro
      (immediateTypes : List Ty)
      (immediateTyped : ValueTypings reduction.bindings immediateTypes)
      (branchesTyped : ∀ branch ∈ reduction.branches,
        ∃ delayedTypes,
          MatchingAtomsTyping expressionTyping environmentTypes
            (bindingTypes ++ immediateTypes) branch delayedTypes ∧
          immediateTypes ++ delayedTypes = expectedBindings) :
      AtomReductionTyping expressionTyping environmentTypes bindingTypes
        expectedBindings reduction

/-- A typed atom reducer is locally preserving and has progress on every atom
inside the certified fragment.  `timeout` is allowed; `stuck` and `.miss` are
not. -/
def AtomReducerTypedSafe
    (expressionTyping : EmbeddedExpressionTyping)
    (reduceAtom : AtomReducer) : Prop :=
  ∀ {environmentTypes bindingTypes environment bindings atom newBindings},
    EnvironmentTyping environment environmentTypes →
    ValueTypings bindings bindingTypes →
    MatchingAtomTyping expressionTyping environmentTypes bindingTypes
      atom newBindings →
    reduceAtom (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) ∧
        AtomReductionTyping expressionTyping environmentTypes bindingTypes
          newBindings reduction

/-! ## Built-in matcher preservation and local progress -/

theorem reduceBuiltinAtom_typedSafe
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval) :
    AtomReducerTypedSafe expressionTyping (reduceBuiltinAtom eval) := by
  intro environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  rcases atom with ⟨pattern, matcher, target⟩
  cases atomTyped with
  | somethingVar targetTyped =>
      exact .inr ⟨_, rfl,
        ⟨_, .cons targetTyped .nil, by
          intro branch member
          simp at member
          subst branch
          exact ⟨[], .nil, rfl⟩⟩⟩
  | somethingWild targetTyped =>
      exact .inr ⟨_, rfl,
        ⟨[], .nil, by
          intro branch member
          simp [AtomReduction.success] at member
          subst branch
          exact ⟨[], .nil, rfl⟩⟩⟩
  | somethingValue expressionTyped targetTyped =>
      have completeEnvironment :=
        bindingsTyped.appendEnvironment environmentTyped
      have evaluated := evalSafe completeEnvironment expressionTyped
      rcases evaluated with timeout | ⟨actual, success, actualTyped⟩
      · exact .inl (by simp [reduceBuiltinAtom, timeout, FuelResult.map])
      · by_cases equal : Value.structuralEq actual target = true
        · exact .inr ⟨AtomReduction.success, by
            simp [reduceBuiltinAtom, success, equal, FuelResult.map],
            ⟨[], .nil, by
              intro branch member
              simp [AtomReduction.success] at member
              subst branch
              exact ⟨[], .nil, rfl⟩⟩⟩
        · have unequal : Value.structuralEq actual target = false := by
            cases check : Value.structuralEq actual target <;> simp_all
          exact .inr ⟨AtomReduction.failure, by
            simp [reduceBuiltinAtom, success, unequal, FuelResult.map],
            ⟨[], .nil, by simp [AtomReduction.failure]⟩⟩
  | tuple atoms zipped children =>
      exact .inr ⟨⟨[atoms], []⟩, by
        simp [reduceBuiltinAtom, zipped.complete],
        ⟨[], .nil, by
          intro branch member
          simp at member
          subst branch
          exact ⟨_, by simpa using children, rfl⟩⟩⟩
  | and leftTyped rightTyped =>
      exact .inr ⟨_, rfl,
        ⟨[], .nil, by
          intro branch member
          simp at member
          subst branch
          exact ⟨_, by simpa using leftTyped.and_atoms rightTyped, rfl⟩⟩⟩
  | productVar targetTyped =>
      exact .inr ⟨_, rfl,
        ⟨[], .nil, by
          intro branch member
          simp at member
          subst branch
          exact ⟨_,
            .cons _ [] _ [] (.somethingVar targetTyped) .nil, rfl⟩⟩⟩
  | productWild targetTyped =>
      exact .inr ⟨_, rfl,
        ⟨[], .nil, by
          intro branch member
          simp at member
          subst branch
          exact ⟨[], .cons _ [] [] [] (.somethingWild targetTyped) .nil,
            rfl⟩⟩⟩
  | productValue expressionTyped targetTyped =>
      exact .inr ⟨_, rfl,
        ⟨[], .nil, by
          intro branch member
          simp at member
          subst branch
          exact ⟨[],
            by simpa using
              MatchingAtomsTyping.cons _ []
                [] [] (.somethingValue expressionTyped targetTyped) .nil,
            rfl⟩⟩⟩

/-- Direct local progress corollary.  In particular, a value-pattern
mismatch is a hit with zero branches, never `stuck`. -/
theorem reduceBuiltinAtom_typed_progress
    (evalSafe : EmbeddedEvaluatorSafe expressionTyping eval)
    (environmentTyped : EnvironmentTyping environment environmentTypes)
    (bindingsTyped : ValueTypings bindings bindingTypes)
    (atomTyped : MatchingAtomTyping expressionTyping environmentTypes
      bindingTypes atom newBindings) :
    reduceBuiltinAtom eval (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceBuiltinAtom eval (bindings ++ environment) atom =
          .ok (.hit reduction) := by
  rcases reduceBuiltinAtom_typedSafe expressionTyping eval evalSafe
      environmentTyped bindingsTyped atomTyped with timeout |
      ⟨reduction, success, _preserved⟩
  · exact .inl timeout
  · exact .inr ⟨reduction, success⟩

/-! ## Matching-state preservation and finite DFS safety -/

/-- A matching state is typed by the type list of every answer reachable from
it. -/
inductive MatchingStateTyping
    (expressionTyping : EmbeddedExpressionTyping) :
    MatchingState → List Ty → Prop where
  | mk
      (environmentTyped : EnvironmentTyping environment environmentTypes)
      (bindingsTyped : ValueTypings bindings bindingTypes)
      (workTyped : MatchingAtomsTyping expressionTyping environmentTypes
        bindingTypes work futureBindings) :
      MatchingStateTyping expressionTyping
        ⟨work, environment, bindings⟩ (bindingTypes ++ futureBindings)

/-- Typed observation of one state step. -/
inductive SearchStepTyping
    (expressionTyping : EmbeddedExpressionTyping) (answerTypes : List Ty) :
    SearchStep MatchingState (List Value) → Prop where
  | yield (answer : List Value)
      (answerTyped : ValueTypings answer answerTypes) :
      SearchStepTyping expressionTyping answerTypes (.yield answer)
  | expand
      (successors : List MatchingState)
      (successorsTyped : ∀ state ∈ successors,
        MatchingStateTyping expressionTyping state answerTypes) :
      SearchStepTyping expressionTyping answerTypes (.expand successors)

def TypedSearchStepResult
    (expressionTyping : EmbeddedExpressionTyping) (answerTypes : List Ty)
    (result : FuelResult (SearchStep MatchingState (List Value))) : Prop :=
  result = .timeout ∨
    ∃ observation, result = .ok observation ∧
      SearchStepTyping expressionTyping answerTypes observation

theorem stepMatchingState_typedSafe
    (reducerSafe : AtomReducerTypedSafe expressionTyping reduceAtom)
    (stateTyped : MatchingStateTyping expressionTyping state answerTypes) :
    TypedSearchStepResult expressionTyping answerTypes
      (stepMatchingState reduceAtom state) := by
  cases stateTyped with
  | @mk environment environmentTypes bindings bindingTypes work
      futureBindings environmentTyped bindingsTyped workTyped =>
      cases workTyped with
      | nil =>
          exact .inr ⟨.yield bindings, rfl,
            .yield bindings (by simpa using bindingsTyped)⟩
      | cons atom atoms headBindings tailBindings headTyped tailTyped =>
          rcases reducerSafe environmentTyped bindingsTyped headTyped with
            timeout | ⟨reduction, reduced, reductionTyped⟩
          · exact .inl (by simp [stepMatchingState, timeout])
          · cases reductionTyped with
            | intro immediateTypes immediateTyped branchesTyped =>
              let successors : List MatchingState :=
                reduction.branches.map fun branch =>
                  ⟨branch ++ atoms, environment,
                    bindings ++ reduction.bindings⟩
              refine .inr ⟨.expand successors, ?_, ?_⟩
              · simp [stepMatchingState, reduced,
                  MatchingState.successors, MatchingState.continueWith,
                  successors]
              · apply SearchStepTyping.expand successors
                intro successor member
                simp only [successors] at member
                rcases List.mem_map.mp member with ⟨branch, branchMember, rfl⟩
                rcases branchesTyped branch branchMember with
                  ⟨delayedTypes, branchTyped, bindingEq⟩
                have tailAfterBranch := tailTyped
                have branchAndTail := branchTyped.append (by
                  simpa [List.append_assoc, bindingEq] using tailAfterBranch)
                have newBindingsTyped :=
                  bindingsTyped.append immediateTyped
                have successorTyped :=
                  MatchingStateTyping.mk environmentTyped newBindingsTyped
                    branchAndTail
                have answerEq :
                    (bindingTypes ++ immediateTypes) ++
                        (delayedTypes ++ tailBindings) =
                      bindingTypes ++ (headBindings ++ tailBindings) := by
                  calc
                    _ = bindingTypes ++
                        (immediateTypes ++ (delayedTypes ++ tailBindings)) :=
                      List.append_assoc _ _ _
                    _ = bindingTypes ++
                        ((immediateTypes ++ delayedTypes) ++ tailBindings) :=
                      congrArg (bindingTypes ++ ·)
                        (List.append_assoc _ _ _).symm
                    _ = _ := congrArg (bindingTypes ++ ·)
                      (congrArg (· ++ tailBindings) bindingEq)
                rw [answerEq] at successorTyped
                exact successorTyped

/-- Pointwise typing for a DFS worklist. -/
def MatchingStatesTyping
    (expressionTyping : EmbeddedExpressionTyping)
    (states : List MatchingState) (answerTypes : List Ty) : Prop :=
  ∀ state ∈ states, MatchingStateTyping expressionTyping state answerTypes

/-- Every answer returned by a successful typed search has the common binding
type list. -/
def MatchingAnswersTyping (answers : List (List Value))
    (answerTypes : List Ty) : Prop :=
  ∀ answer ∈ answers, ValueTypings answer answerTypes

def TypedMatchingSearchResult (answerTypes : List Ty)
    (result : FuelResult (List (List Value))) : Prop :=
  result = .timeout ∨
    ∃ answers, result = .ok answers ∧
      MatchingAnswersTyping answers answerTypes

theorem depthFirstMatching_typedSafe
    (reducerSafe : AtomReducerTypedSafe expressionTyping reduceAtom)
    (statesTyped : MatchingStatesTyping expressionTyping states answerTypes)
    (fuel : Nat) :
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
          have restTyped : MatchingStatesTyping expressionTyping rest answerTypes := by
            intro candidate member
            exact statesTyped candidate (by simp [member])
          rcases stepMatchingState_typedSafe reducerSafe stateTyped with
            timeout | ⟨observation, stepped, observationTyped⟩
          · exact .inl (by simp [depthFirstFuel, timeout])
          · cases observationTyped with
            | yield answer answerTyped =>
                rcases induction restTyped with tailTimeout |
                  ⟨answers, searched, answersTyped⟩
                · exact .inl (by
                    simp [depthFirstFuel, stepped, tailTimeout,
                      FuelResult.map])
                · exact .inr ⟨answer :: answers, by
                    simp [depthFirstFuel, stepped, searched,
                      FuelResult.map], by
                    intro answer member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | tailMember
                    · exact answerTyped
                    · exact answersTyped answer tailMember⟩
            | expand successors successorsTyped =>
                have nextTyped : MatchingStatesTyping expressionTyping
                    (successors ++ rest) answerTypes := by
                  intro candidate member
                  rcases List.mem_append.mp member with inSuccessors | inRest
                  · exact successorsTyped candidate inSuccessors
                  · exact restTyped candidate inRest
                rcases induction nextTyped with nextTimeout |
                  ⟨answers, searched, answersTyped⟩
                · exact .inl (by
                    simp [depthFirstFuel, stepped, nextTimeout])
                · exact .inr ⟨answers, by
                    simp [depthFirstFuel, stepped, searched], answersTyped⟩

/-- Preservation and local progress lift through every finite DFS bound. -/
theorem searchMatchingFuel_typedSafe
    (reducerSafe : AtomReducerTypedSafe expressionTyping reduceAtom)
    (initialTyped : MatchingStateTyping expressionTyping initial answerTypes)
    (fuel : Nat) :
    TypedMatchingSearchResult answerTypes
      (searchMatchingFuel reduceAtom fuel initial) := by
  apply depthFirstMatching_typedSafe reducerSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact initialTyped

/-- Typed finite matching search never reports missing runtime rules. -/
theorem searchMatchingFuel_typed_notStuck
    (reducerSafe : AtomReducerTypedSafe expressionTyping reduceAtom)
    (initialTyped : MatchingStateTyping expressionTyping initial answerTypes)
    (fuel : Nat) :
    (searchMatchingFuel reduceAtom fuel initial).NotStuck := by
  rcases searchMatchingFuel_typedSafe reducerSafe initialTyped fuel with
    timeout | ⟨answers, success, _typed⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TypePM.Runtime
