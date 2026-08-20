import TypePM.CommonFuelSafety
import TypePM.Runtime.PatternFunctionNodeEvaluation
import TypePM.Source.PatternFunctionFreeze

/-!
# Typed boundary for scoped pattern-function nodes

This module isolates the three rules introduced by `MatchingTree.node` from
the ordinary atom reducer.  Application opens only a runtime definition tied
to a checked frozen declaration; parameter export produces an ordinary atom
with an explicit total-core typing certificate; and node completion preserves
the outer typed frame while discarding the private bindings.

These local certificates are intentionally weaker than a full MNode search
safety theorem, but they are not assumptions of that theorem's conclusion.
The remaining bridge is precise: `PatternElaborates` preserves an embedded
source pattern, whereas `DelegatedMatchingAtomsTyping` currently records only
the matcher and target value types.  Until that source-pattern fact is carried
to `TotalMatchingAtomTyping`, typed user-matcher branches cannot populate the
recursive MNode worklist in general.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- The outer state retained while an isolated pattern-function node runs. -/
structure PatternFunctionOuterFrameTyping
    (environment : ValueEnvironment) (bindings : List Value)
    (environmentTypes bindingTypes : List Ty) : Prop where
  environmentTyped : EnvironmentTyping environment environmentTypes
  bindingsTyped : ValueTypings bindings bindingTypes

/-- A statically checked application about to enter a fresh MNode.  Runtime
lookup is tied to `PatternFunctionDefinitions.Agree`, and the value indices
record that the matcher and target agree on the function result type. -/
structure MNodeApplicationTyping
    (signature : FrozenSignature) (definitions : PatternFunctionDefinitions)
    (name : PatternFunName) (arguments : List Pattern)
    (matcher target : Value) (environment : ValueEnvironment)
    (bindings : List Value) (environmentTypes bindingTypes : List Ty)
    (definition : PatternFunctionDefinition) (resultCapability : Cap)
    (resultTarget : Ty) : Prop where
  agreement : definitions.Agree signature
  found : definitions.lookup name = some definition
  arity : arguments.length = definition.parameterCount
  checkedResult : ∃ checked : definition.Checked signature,
    resultCapability =
      (checked.scheme.instantiate ⟨0, 0⟩).1.result.capability.apply
        checked.solution.cap ∧
    resultTarget =
      (checked.scheme.instantiate ⟨0, 0⟩).1.result.target.apply
        checked.solution
  matcherTyped : ValueTyping matcher (.matcher resultCapability resultTarget)
  targetTyped : ValueTyping target resultTarget
  outer : PatternFunctionOuterFrameTyping environment bindings
    environmentTypes bindingTypes

namespace MNodeApplicationTyping

/-- Agreement makes the body selected by runtime lookup a genuinely checked
source definition, rather than an unrelated table entry. -/
theorem checked
    (typing : MNodeApplicationTyping signature definitions name arguments
      matcher target environment bindings environmentTypes bindingTypes
      definition resultCapability resultTarget) :
    Nonempty (definition.Checked signature) := by
  obtain ⟨checked, _capability, _target⟩ := typing.checkedResult
  exact ⟨checked⟩

/-- The application lookup used by the executable MNode rule succeeds with
the same checked definition and the statically certified arity. -/
theorem lookup
    (typing : MNodeApplicationTyping signature definitions name arguments
      matcher target environment bindings environmentTypes bindingTypes
      definition resultCapability resultTarget) :
    lookupPatternFunctionApplication definitions name arguments =
      some definition := by
  simp [lookupPatternFunctionApplication, typing.found, typing.arity]

/-- Typed application cannot take the MNode `.stuck` branch.  It starts one
private node with the checked body, the original environment, no private
bindings, and the source-ordered actual pattern arguments. -/
theorem step
    (typing : MNodeApplicationTyping signature definitions name arguments
      matcher target environment bindings environmentTypes bindingTypes
      definition resultCapability resultTarget)
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction)) (remaining : List MatchingTree) :
    stepPatternFunctionHead definitions reduceAtom
        (.atom ⟨.app name arguments, matcher, target⟩) remaining environment
        bindings =
      .ok [⟨[.node
          [.atom ⟨definition.body, matcher, target⟩]
          environment [] arguments] ++ remaining,
        environment, bindings⟩] ∧
      Nonempty (definition.Checked signature) ∧
      PatternFunctionOuterFrameTyping environment bindings environmentTypes
        bindingTypes := by
  exact ⟨by
    simp [stepPatternFunctionHead, lookupPatternFunctionApplication,
      typing.found, typing.arity], typing.checked, typing.outer⟩

end MNodeApplicationTyping

/-- Typing data for exporting one embedded parameter from a private node.
The private frame stays isolated.  The selected actual pattern is certified
as an ordinary total-core atom in the outer frame, so its future bindings are
outer bindings rather than private node bindings. -/
structure MNodeParameterTyping
    (arguments : List Pattern) (index : Nat) (argument : Pattern)
    (matcher target : Value)
    (outerEnvironment privateEnvironment : ValueEnvironment)
    (outerBindings privateBindings : List Value)
    (outerEnvironmentTypes outerBindingTypes privateEnvironmentTypes
      privateBindingTypes exportedTypes : List Ty) : Prop where
  argumentLookup : arguments[index]? = some argument
  outer : PatternFunctionOuterFrameTyping outerEnvironment outerBindings
    outerEnvironmentTypes outerBindingTypes
  privateEnvironmentTyped :
    EnvironmentTyping privateEnvironment privateEnvironmentTypes
  privateBindingsTyped : ValueTypings privateBindings privateBindingTypes
  exportedAtomTyped : TotalMatchingAtomTyping outerEnvironmentTypes
    outerBindingTypes ⟨argument, matcher, target⟩ exportedTypes

namespace MNodeParameterTyping

/-- Parameter export cannot get stuck on lookup.  The exact typed actual
pattern is placed before the private continuation node, leaving both frames'
stored values unchanged. -/
theorem step
    (typing : MNodeParameterTyping arguments index argument matcher target
      outerEnvironment privateEnvironment outerBindings privateBindings
      outerEnvironmentTypes outerBindingTypes privateEnvironmentTypes
      privateBindingTypes exportedTypes)
    (definitions : PatternFunctionDefinitions)
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (privateRemaining remaining : List MatchingTree) :
    stepPatternFunctionHead definitions reduceAtom
        (.node (.atom ⟨.embed index, matcher, target⟩ :: privateRemaining)
          privateEnvironment privateBindings arguments)
        remaining outerEnvironment outerBindings =
      .ok [⟨.atom ⟨argument, matcher, target⟩ ::
          .node privateRemaining privateEnvironment privateBindings arguments ::
            remaining,
        outerEnvironment, outerBindings⟩] ∧
      TotalMatchingAtomTyping outerEnvironmentTypes outerBindingTypes
        ⟨argument, matcher, target⟩ exportedTypes ∧
      PatternFunctionOuterFrameTyping outerEnvironment outerBindings
        outerEnvironmentTypes outerBindingTypes ∧
      EnvironmentTyping privateEnvironment privateEnvironmentTypes ∧
      ValueTypings privateBindings privateBindingTypes := by
  exact ⟨by simp [stepPatternFunctionHead, typing.argumentLookup],
    typing.exportedAtomTyped, typing.outer, typing.privateEnvironmentTyped,
    typing.privateBindingsTyped⟩

end MNodeParameterTyping

/-- Completion needs no claim about private binding types: the evaluator
discards them.  The certificate records exactly the outer frame that must be
preserved. -/
structure MNodeDoneTyping
    (outerEnvironment : ValueEnvironment) (outerBindings : List Value)
    (outerEnvironmentTypes outerBindingTypes : List Ty) : Prop where
  outer : PatternFunctionOuterFrameTyping outerEnvironment outerBindings
    outerEnvironmentTypes outerBindingTypes

namespace MNodeDoneTyping

/-- Finishing a node resumes the outer continuation with the same typed
environment and bindings, regardless of the private values being discarded. -/
theorem step
    (typing : MNodeDoneTyping outerEnvironment outerBindings
      outerEnvironmentTypes outerBindingTypes)
    (definitions : PatternFunctionDefinitions)
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (privateEnvironment : ValueEnvironment) (privateBindings : List Value)
    (arguments : List Pattern) (remaining : List MatchingTree) :
    stepPatternFunctionHead definitions reduceAtom
        (.node [] privateEnvironment privateBindings arguments)
        remaining outerEnvironment outerBindings =
      .ok [⟨remaining, outerEnvironment, outerBindings⟩] ∧
      PatternFunctionOuterFrameTyping outerEnvironment outerBindings
        outerEnvironmentTypes outerBindingTypes := by
  exact ⟨rfl, typing.outer⟩

end MNodeDoneTyping

/-! ## Reusable typed DFS assembly for scoped matching states -/

/-- Pointwise typing of the worklist consumed by the scoped depth-first
search.  The concrete state invariant is a parameter: the MNode-specific
proof only has to show that one successful state step preserves it. -/
def ScopedMatchingStatesTyping
    (stateTyping : PatternFunctionState → List Ty → Prop)
    (states : List PatternFunctionState) (answerTypes : List Ty) : Prop :=
  ∀ state ∈ states, stateTyping state answerTypes

/-- Typed result of one scoped-state step.  A yielded answer has the common
answer type; every expanded successor preserves the caller's state
invariant. -/
inductive ScopedSearchStepTyping
    (stateTyping : PatternFunctionState → List Ty → Prop)
    (answerTypes : List Ty) :
    SearchStep PatternFunctionState (List Value) → Prop where
  | yield (answer : List Value)
      (answerTyped : ValueTypings answer answerTypes) :
      ScopedSearchStepTyping stateTyping answerTypes (.yield answer)
  | expand (successors : List PatternFunctionState)
      (successorsTyped : ∀ state ∈ successors,
        stateTyping state answerTypes) :
      ScopedSearchStepTyping stateTyping answerTypes (.expand successors)

/-- Local preservation/progress contract for the executable scoped-state
step.  Timeout is allowed; `stuck` is not. -/
def ScopedStateStepTypedSafe
    (definitions : PatternFunctionDefinitions)
    (reduceAtom : ValueEnvironment → MatchingAtom →
      FuelResult (DispatchResult AtomReduction))
    (stateTyping : PatternFunctionState → List Ty → Prop) : Prop :=
  ∀ {state answerTypes},
    stateTyping state answerTypes →
    stepPatternFunctionState definitions reduceAtom state = .timeout ∨
      ∃ observation,
        stepPatternFunctionState definitions reduceAtom state =
            .ok observation ∧
          ScopedSearchStepTyping stateTyping answerTypes observation

/-- A locally safe scoped-state step makes the complete finite DFS safe.
This theorem is independent of the details of the MNode invariant and is the
assembly counterpart of `depthFirstMatching_typedSafe` for ordinary matching
states. -/
theorem depthFirstScopedMatching_typedSafe
    (stepSafe : ScopedStateStepTypedSafe definitions reduceAtom stateTyping)
    (statesTyped : ScopedMatchingStatesTyping stateTyping states answerTypes)
    (fuel : Nat) :
    TypedMatchingSearchResult answerTypes
      (depthFirstFuel (stepPatternFunctionState definitions reduceAtom)
        fuel states) := by
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
          have restTyped : ScopedMatchingStatesTyping stateTyping rest
              answerTypes := by
            intro candidate member
            exact statesTyped candidate (by simp [member])
          rcases stepSafe stateTyped with
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
                    intro candidate member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | tailMember
                    · exact answerTyped
                    · exact answersTyped candidate tailMember⟩
            | expand successors successorsTyped =>
                have nextTyped : ScopedMatchingStatesTyping stateTyping
                    (successors ++ rest) answerTypes := by
                  intro candidate member
                  rcases List.mem_append.mp member with
                    inSuccessors | inRest
                  · exact successorsTyped candidate inSuccessors
                  · exact restTyped candidate inRest
                rcases induction nextTyped with nextTimeout |
                  ⟨answers, searched, answersTyped⟩
                · exact .inl (by
                    simp [depthFirstFuel, stepped, nextTimeout])
                · exact .inr ⟨answers, by
                    simp [depthFirstFuel, stepped, searched], answersTyped⟩

/-- Initial-state specialization for the public scoped search function. -/
theorem searchPatternFunctionsFuel_typedSafe_of_stateStep
    (stepSafe : ScopedStateStepTypedSafe definitions
      (evaluationAtomReducer evaluate) stateTyping)
    (initialTyped : stateTyping
      ⟨[.atom ⟨pattern, matcher, target⟩], environment, []⟩ answerTypes)
    (fuel : Nat) :
    TypedMatchingSearchResult answerTypes
      (searchPatternFunctionsFuel definitions evaluate fuel environment
        pattern matcher target) := by
  unfold searchPatternFunctionsFuel
  apply depthFirstScopedMatching_typedSafe stepSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact initialTyped

/-! ## Concrete checked MNode fragment

The invariant below is intentionally structural.  Ordinary atoms use the
total-core certificate, applications must select an actually checked runtime
definition, and an embedded parameter is typed in the outer frame rather than
the node's private frame.  The fragment permits arbitrary recursive ordinary
atom reduction inside a checked body.  It also permits a private body to call
a checked definition whose body directly embeds one of its arguments; the
exported argument may itself be an embedded parameter of the caller.  General
nested bodies require a fully stack-indexed version of the same invariant.
-/

/-- A total-core atom that is genuinely handled by the ordinary reducer arm,
rather than by either MNode-specific pattern form. -/
structure CheckedOrdinaryAtomTyping
    (environmentTypes bindingTypes : List Ty) (atom : MatchingAtom)
    (newBindings : List Ty) : Prop where
  typed : TotalMatchingAtomTyping environmentTypes bindingTypes atom newBindings
  notApplication : ∀ name arguments, atom.pattern ≠ .app name arguments
  notParameter : ∀ index, atom.pattern ≠ .embed index

/-- Source-ordered ordinary atoms returned by one reducer branch. -/
inductive CheckedOrdinaryAtomsTyping :
    List Ty → List Ty → List MatchingAtom → List Ty → Prop where
  | nil : CheckedOrdinaryAtomsTyping environmentTypes bindingTypes [] []
  | cons
      (head : CheckedOrdinaryAtomTyping environmentTypes bindingTypes atom
        headBindings)
      (tail : CheckedOrdinaryAtomsTyping environmentTypes
        (bindingTypes ++ headBindings) atoms tailBindings) :
      CheckedOrdinaryAtomsTyping environmentTypes bindingTypes
        (atom :: atoms) (headBindings ++ tailBindings)

namespace CheckedOrdinaryAtomsTyping

/-- Forgetting the source-form exclusions recovers the total-core branch
certificate. -/
theorem total :
    ∀ {environmentTypes bindingTypes atoms newBindings},
      CheckedOrdinaryAtomsTyping environmentTypes bindingTypes atoms
        newBindings →
      TotalMatchingAtomsTyping environmentTypes bindingTypes atoms newBindings
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail => .cons head.typed (total tail)

end CheckedOrdinaryAtomsTyping

mutual

  /-- Typed outer work.  The last index is the binding type list after all
  work has completed. -/
  inductive CheckedScopedWorkTyping
      (signature : FrozenSignature)
      (definitions : PatternFunctionDefinitions) (environmentTypes : List Ty) :
      List Ty → List MatchingTree → List Ty → Prop where
    | nil : CheckedScopedWorkTyping signature definitions environmentTypes
        bindingTypes [] bindingTypes
    | ordinary
        (head : CheckedOrdinaryAtomTyping environmentTypes bindingTypes atom
          newBindings)
        (tail : CheckedScopedWorkTyping signature definitions environmentTypes
          (bindingTypes ++ newBindings) remaining answerTypes) :
        CheckedScopedWorkTyping signature definitions environmentTypes
          bindingTypes (.atom atom :: remaining) answerTypes
    | application
        (found : definitions.lookup name = some definition)
        (checked : Nonempty (definition.Checked signature))
        (arity : arguments.length = definition.parameterCount)
        (body : CheckedMNodeWorkTyping signature definitions environmentTypes
          bindingTypes arguments environmentTypes []
          [.atom ⟨definition.body, matcher, target⟩] afterNodeTypes)
        (tail : CheckedScopedWorkTyping signature definitions environmentTypes
          afterNodeTypes remaining answerTypes) :
        CheckedScopedWorkTyping signature definitions environmentTypes
          bindingTypes
          (.atom ⟨.app name arguments, matcher, target⟩ :: remaining)
          answerTypes
    | node
        (privateEnvironmentTyped :
          EnvironmentTyping privateEnvironment privateEnvironmentTypes)
        (privateBindingsTyped :
          ValueTypings privateBindings privateBindingTypes)
        (inside : CheckedMNodeWorkTyping signature definitions environmentTypes
          bindingTypes arguments privateEnvironmentTypes privateBindingTypes
          privateWork afterNodeTypes)
        (tail : CheckedScopedWorkTyping signature definitions environmentTypes
          afterNodeTypes remaining answerTypes) :
        CheckedScopedWorkTyping signature definitions environmentTypes
          bindingTypes
          (.node privateWork privateEnvironment privateBindings arguments ::
            remaining) answerTypes

  /-- Typed work stored in one MNode.  Ordinary bindings extend only the
  private frame.  Embedded arguments extend only the outer frame. -/
  inductive CheckedMNodeWorkTyping
      (signature : FrozenSignature)
      (definitions : PatternFunctionDefinitions)
      (environmentTypes : List Ty) :
      List Ty → List Pattern → List Ty → List Ty →
        List MatchingTree → List Ty → Prop where
    | nil : CheckedMNodeWorkTyping signature definitions environmentTypes
        outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
        [] outerBindingTypes
    | ordinary
        (head : CheckedOrdinaryAtomTyping privateEnvironmentTypes
          privateBindingTypes atom newPrivateBindings)
        (tail : CheckedMNodeWorkTyping signature definitions
          environmentTypes outerBindingTypes arguments
          privateEnvironmentTypes (privateBindingTypes ++ newPrivateBindings)
          remaining answerTypes) :
        CheckedMNodeWorkTyping signature definitions environmentTypes
          outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
          (.atom atom :: remaining) answerTypes
    | parameter
        (lookup : arguments[index]? = some argument)
        (exported : CheckedScopedWorkTyping signature definitions
          environmentTypes outerBindingTypes
          [.atom ⟨argument, matcher, target⟩] afterExportTypes)
        (tail : CheckedMNodeWorkTyping signature definitions
          environmentTypes afterExportTypes
          arguments privateEnvironmentTypes privateBindingTypes remaining
          answerTypes) :
        CheckedMNodeWorkTyping signature definitions environmentTypes
          outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
          (.atom ⟨.embed index, matcher, target⟩ :: remaining) answerTypes
    | applicationParameter
        (found : definitions.lookup name = some definition)
        (checked : Nonempty (definition.Checked signature))
        (arity : nestedArguments.length = definition.parameterCount)
        (body : definition.body = .embed parameterIndex)
        (nestedLookup : nestedArguments[parameterIndex]? =
          some (.embed outerIndex))
        (outerLookup : arguments[outerIndex]? = some outerArgument)
        (exported : CheckedScopedWorkTyping signature definitions
          environmentTypes outerBindingTypes
          [.atom ⟨outerArgument, matcher, target⟩] afterExportTypes)
        (tail : CheckedMNodeWorkTyping signature definitions environmentTypes
          afterExportTypes arguments privateEnvironmentTypes privateBindingTypes
          remaining answerTypes) :
        CheckedMNodeWorkTyping signature definitions environmentTypes
          outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
          (.atom ⟨.app name nestedArguments, matcher, target⟩ :: remaining)
          answerTypes
    | nestedParameterNode
        (nestedEnvironmentTyped :
          EnvironmentTyping nestedEnvironment nestedEnvironmentTypes)
        (nestedBindingsTyped :
          ValueTypings nestedBindings nestedBindingTypes)
        (nestedLookup : nestedArguments[parameterIndex]? =
          some (.embed outerIndex))
        (outerLookup : arguments[outerIndex]? = some outerArgument)
        (exported : CheckedScopedWorkTyping signature definitions
          environmentTypes outerBindingTypes
          [.atom ⟨outerArgument, matcher, target⟩] afterExportTypes)
        (tail : CheckedMNodeWorkTyping signature definitions environmentTypes
          afterExportTypes arguments privateEnvironmentTypes privateBindingTypes
          remaining answerTypes) :
        CheckedMNodeWorkTyping signature definitions environmentTypes
          outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
          (.node [.atom ⟨.embed parameterIndex, matcher, target⟩]
              nestedEnvironment nestedBindings nestedArguments :: remaining)
          answerTypes
    | nestedDone
        (nestedEnvironmentTyped :
          EnvironmentTyping nestedEnvironment nestedEnvironmentTypes)
        (nestedBindingsTyped :
          ValueTypings nestedBindings nestedBindingTypes)
        (tail : CheckedMNodeWorkTyping signature definitions environmentTypes
          outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
          remaining answerTypes) :
        CheckedMNodeWorkTyping signature definitions environmentTypes
          outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
          (.node [] nestedEnvironment nestedBindings nestedArguments :: remaining)
          answerTypes

end

/-- A concrete scoped state has typed runtime values and structurally typed
work with one common final outer binding type list. -/
inductive CheckedScopedStateTyping
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions) :
    PatternFunctionState → List Ty → Prop where
  | mk
      (environmentTyped : EnvironmentTyping environment environmentTypes)
      (bindingsTyped : ValueTypings bindings bindingTypes)
      (workTyped : CheckedScopedWorkTyping signature definitions
        environmentTypes bindingTypes work answerTypes) :
      CheckedScopedStateTyping signature definitions
        ⟨work, environment, bindings⟩ answerTypes

namespace CheckedScopedWorkTyping

/-- Agreement supplies the checked certificate for the exact runtime body
selected by lookup. -/
theorem applicationOfAgreement
    (agreement : definitions.Agree signature)
    (found : definitions.lookup name = some definition)
    (arity : arguments.length = definition.parameterCount)
    (body : CheckedMNodeWorkTyping signature definitions environmentTypes
      bindingTypes arguments environmentTypes []
      [.atom ⟨definition.body, matcher, target⟩] afterNodeTypes)
    (tail : CheckedScopedWorkTyping signature definitions environmentTypes
      afterNodeTypes remaining answerTypes) :
    CheckedScopedWorkTyping signature definitions environmentTypes bindingTypes
      (.atom ⟨.app name arguments, matcher, target⟩ :: remaining)
      answerTypes :=
  .application found (agreement.lookup_checked found) arity body tail

/-- Sequential composition of typed outer work. -/
theorem append :
    ∀ {bindingTypes leftWork middleTypes},
      CheckedScopedWorkTyping signature definitions environmentTypes
        bindingTypes leftWork middleTypes →
      ∀ {rightWork answerTypes},
        CheckedScopedWorkTyping signature definitions environmentTypes
          middleTypes rightWork answerTypes →
        CheckedScopedWorkTyping signature definitions environmentTypes
          bindingTypes (leftWork ++ rightWork) answerTypes
  | _, _, _, .nil, _, _, right => by simpa using right
  | _, _, _, .ordinary head tail, _, _, right =>
      .ordinary head (append tail right)
  | _, _, _, .application found checked arity body tail, _, _, right =>
      .application found checked arity body (append tail right)
  | _, _, _, .node privateEnvironmentTyped privateBindingsTyped inside tail,
      _, _, right =>
      .node privateEnvironmentTyped privateBindingsTyped inside
        (append tail right)

/-- Prepend total-core atoms to already typed outer work. -/
theorem prependTotalAtoms
    (atomsTyped : CheckedOrdinaryAtomsTyping environmentTypes bindingTypes atoms
      newBindings)
    (tail : CheckedScopedWorkTyping signature definitions environmentTypes
      (bindingTypes ++ newBindings) work answerTypes) :
    CheckedScopedWorkTyping signature definitions environmentTypes bindingTypes
      (MatchingTree.ofAtoms atoms ++ work) answerTypes := by
  cases atomsTyped with
  | nil => simpa [MatchingTree.ofAtoms] using tail
  | cons head rest =>
      simp only [MatchingTree.ofAtoms, List.map_cons, List.cons_append]
      exact .ordinary head (by
        simpa [MatchingTree.ofAtoms, List.append_assoc] using
          prependTotalAtoms rest (by
          simpa [List.append_assoc] using tail))
termination_by atoms.length

end CheckedScopedWorkTyping

namespace CheckedMNodeWorkTyping

/-- Prepend total-core atoms to already typed private work. -/
theorem prependTotalAtoms
    (atomsTyped : CheckedOrdinaryAtomsTyping privateEnvironmentTypes
      privateBindingTypes atoms newBindings)
    (tail : CheckedMNodeWorkTyping signature definitions outerEnvironmentTypes
      outerBindingTypes arguments privateEnvironmentTypes
      (privateBindingTypes ++ newBindings) work answerTypes) :
    CheckedMNodeWorkTyping signature definitions outerEnvironmentTypes
      outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
      (MatchingTree.ofAtoms atoms ++ work) answerTypes := by
  cases atomsTyped with
  | nil => simpa [MatchingTree.ofAtoms] using tail
  | cons head rest =>
      simp only [MatchingTree.ofAtoms, List.map_cons, List.cons_append]
      exact .ordinary head (by
        simpa [MatchingTree.ofAtoms, List.append_assoc] using
          prependTotalAtoms rest (by
          simpa [List.append_assoc] using tail))
termination_by atoms.length

end CheckedMNodeWorkTyping


/-- One ordinary reduction preserves the stronger non-MNode branch
certificate.  This is the precise reusable bridge still required from a user
matcher whose dispatch can return source patterns. -/
inductive CheckedScopedAtomReductionTyping
    (environmentTypes bindingTypes expectedBindings : List Ty)
    (reduction : AtomReduction) : Prop where
  | intro
      (immediateTypes : List Ty)
      (immediateTyped : ValueTypings reduction.bindings immediateTypes)
      (branchesTyped : ∀ branch ∈ reduction.branches,
        ∃ delayedTypes,
          CheckedOrdinaryAtomsTyping environmentTypes
            (bindingTypes ++ immediateTypes) branch delayedTypes ∧
          immediateTypes ++ delayedTypes = expectedBindings) :
      CheckedScopedAtomReductionTyping environmentTypes bindingTypes
        expectedBindings reduction

/-- Reducer safety needed by the checked scoped fragment.  It strengthens
`TotalAtomReducerTypedSafe` only at the exact missing boundary: patterns in
successful recursive branches remain ordinary. -/
def CheckedScopedAtomReducerTypedSafe (reduceAtom : AtomReducer) : Prop :=
  ∀ {environmentTypes bindingTypes environment bindings atom newBindings},
    EnvironmentTyping environment environmentTypes →
    ValueTypings bindings bindingTypes →
    CheckedOrdinaryAtomTyping environmentTypes bindingTypes atom newBindings →
    reduceAtom (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) ∧
        CheckedScopedAtomReductionTyping environmentTypes bindingTypes
          newBindings reduction

/-- Upgrade the existing total reducer theorem once the concrete successful
branches have the retained source-pattern evidence.  This isolates the
missing user-matcher bridge without postulating a branch unrelated to the
actual reduction. -/
theorem checkedScopedAtomReducerTypedSafe_of_total
    (totalSafe : TotalAtomReducerTypedSafe reduceAtom)
    (preservesSourcePatterns :
      ∀ {environmentTypes bindingTypes environment bindings atom newBindings
          reduction},
        EnvironmentTyping environment environmentTypes →
        ValueTypings bindings bindingTypes →
        CheckedOrdinaryAtomTyping environmentTypes bindingTypes atom
          newBindings →
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) →
        TotalAtomReductionTyping environmentTypes bindingTypes newBindings
          reduction →
        CheckedScopedAtomReductionTyping environmentTypes bindingTypes
          newBindings reduction) :
    CheckedScopedAtomReducerTypedSafe reduceAtom := by
  intro environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  rcases totalSafe environmentTyped bindingsTyped atomTyped.typed with
    timeout | ⟨reduction, reduced, reductionTyped⟩
  · exact .inl timeout
  · exact .inr ⟨reduction, reduced,
      preservesSourcePatterns environmentTyped bindingsTyped atomTyped reduced
        reductionTyped⟩

private theorem stepPatternFunctionHead_checkedOrdinary
    (typed : CheckedOrdinaryAtomTyping environmentTypes bindingTypes atom
      newBindings) :
    stepPatternFunctionHead definitions reduceAtom (.atom atom) remaining
        environment bindings =
      FuelResult.bind (reduceAtom (bindings ++ environment) atom) fun result =>
        match result with
        | .miss => .stuck
        | .hit reduction =>
            .ok (continueTreeAtom remaining environment bindings reduction) := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern <;> try rfl
  · exact False.elim (typed.notParameter _ rfl)
  · exact False.elim (typed.notApplication _ _ rfl)

private theorem stepPatternFunctionHead_nodeCheckedOrdinary
    (typed : CheckedOrdinaryAtomTyping environmentTypes bindingTypes atom
      newBindings) :
    stepPatternFunctionHead definitions reduceAtom
        (.node (.atom atom :: privateRemaining) privateEnvironment
          privateBindings arguments)
        remaining outerEnvironment outerBindings =
      FuelResult.map
        (fun successors => successors.map fun successor =>
          ⟨.node successor.work successor.environment successor.bindings
              arguments :: remaining,
            outerEnvironment, outerBindings⟩)
        (FuelResult.bind (reduceAtom (privateBindings ++ privateEnvironment) atom)
          fun result =>
            match result with
            | .miss => .stuck
            | .hit reduction =>
                .ok (continueTreeAtom privateRemaining privateEnvironment
                  privateBindings reduction)) := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern <;> try rfl
  · exact False.elim (typed.notParameter _ rfl)
  · exact False.elim (typed.notApplication _ _ rfl)

/-- Preservation/progress for an MNode whose checked body belongs to the
recursive ordinary-plus-parameter fragment. -/
private theorem CheckedMNodeWorkTyping.stepNodeCheckedSafe
    (reducerSafe : CheckedScopedAtomReducerTypedSafe reduceAtom)
    (outerEnvironmentTyped :
      EnvironmentTyping outerEnvironment outerEnvironmentTypes)
    (outerBindingsTyped : ValueTypings outerBindings outerBindingTypes)
    (privateEnvironmentTyped :
      EnvironmentTyping privateEnvironment privateEnvironmentTypes)
    (privateBindingsTyped : ValueTypings privateBindings privateBindingTypes)
    (inside : CheckedMNodeWorkTyping signature definitions
      outerEnvironmentTypes outerBindingTypes arguments privateEnvironmentTypes
      privateBindingTypes privateWork afterNodeTypes)
    (tail : CheckedScopedWorkTyping signature definitions
      outerEnvironmentTypes afterNodeTypes remaining answerTypes) :
    stepPatternFunctionHead definitions reduceAtom
        (.node privateWork privateEnvironment privateBindings arguments)
        remaining outerEnvironment outerBindings = .timeout ∨
      ∃ successors,
        stepPatternFunctionHead definitions reduceAtom
            (.node privateWork privateEnvironment privateBindings arguments)
            remaining outerEnvironment outerBindings = .ok successors ∧
        ∀ successor ∈ successors,
          CheckedScopedStateTyping signature definitions successor answerTypes := by
  cases inside with
  | nil =>
      exact .inr ⟨_, rfl, by
        intro successor member
        simp only [List.mem_singleton] at member
        subst successor
        exact .mk outerEnvironmentTyped outerBindingsTyped tail⟩
  | ordinary head rest =>
      rename_i atom newPrivateBindings privateRemaining
      rcases reducerSafe privateEnvironmentTyped privateBindingsTyped head with
        timeout | ⟨reduction, reduced, reductionTyped⟩
      · exact .inl (by
          rw [stepPatternFunctionHead_nodeCheckedOrdinary head, timeout]
          rfl)
      · cases reductionTyped with
        | intro immediateTypes immediateTyped branchesTyped =>
            let successors : List PatternFunctionState :=
              reduction.branches.map fun branch =>
                ⟨.node (MatchingTree.ofAtoms branch ++ privateRemaining)
                    privateEnvironment (privateBindings ++ reduction.bindings)
                    arguments :: remaining,
                  outerEnvironment, outerBindings⟩
            refine .inr ⟨successors, ?_, ?_⟩
            · rw [stepPatternFunctionHead_nodeCheckedOrdinary head, reduced]
              simp [continueTreeAtom, successors, FuelResult.map,
                Function.comp_def]
            · intro successor member
              simp only [successors, List.mem_map] at member
              rcases member with ⟨branch, branchMember, rfl⟩
              obtain ⟨delayedTypes, branchTyped, bindingEq⟩ :=
                branchesTyped branch branchMember
              have rest' : CheckedMNodeWorkTyping signature definitions
                  outerEnvironmentTypes outerBindingTypes arguments
                  privateEnvironmentTypes
                  ((privateBindingTypes ++ immediateTypes) ++ delayedTypes)
                  privateRemaining afterNodeTypes := by
                simpa [List.append_assoc, bindingEq] using rest
              exact .mk outerEnvironmentTyped outerBindingsTyped
                (.node privateEnvironmentTyped
                  (privateBindingsTyped.append immediateTyped)
                  (CheckedMNodeWorkTyping.prependTotalAtoms branchTyped rest')
                  tail)
  | parameter lookup exported rest =>
      rename_i index argument matcher target afterExportTypes privateRemaining
      let successors : List PatternFunctionState :=
        [⟨.atom ⟨argument, matcher, target⟩ ::
            .node privateRemaining privateEnvironment privateBindings arguments ::
              remaining,
          outerEnvironment, outerBindings⟩]
      refine .inr ⟨successors, by
        simp [successors, stepPatternFunctionHead, lookup], ?_⟩
      intro successor member
      simp only [successors, List.mem_singleton] at member
      subst successor
      exact .mk outerEnvironmentTyped outerBindingsTyped
        (exported.append
          (.node privateEnvironmentTyped privateBindingsTyped rest tail))
  | applicationParameter found checked arity body nestedLookup outerLookup
      exported rest =>
      rename_i name definition parameterIndex nestedArguments outerIndex
        outerArgument matcher target afterExportTypes privateRemaining
      let successors : List PatternFunctionState := [⟨
        [MatchingTree.node
          (MatchingTree.node
              [.atom ⟨.embed parameterIndex, matcher, target⟩]
              privateEnvironment [] nestedArguments :: privateRemaining)
          privateEnvironment privateBindings arguments] ++ remaining,
        outerEnvironment, outerBindings⟩]
      refine .inr ⟨successors, ?_, ?_⟩
      · simp [successors, stepPatternFunctionHead,
          lookupPatternFunctionApplication, found, arity, body]
      · intro successor member
        simp only [successors, List.mem_singleton] at member
        subst successor
        exact .mk outerEnvironmentTyped outerBindingsTyped
          (.node privateEnvironmentTyped privateBindingsTyped
            (.nestedParameterNode privateEnvironmentTyped .nil nestedLookup
              outerLookup exported rest)
            tail)
  | nestedParameterNode nestedEnvironmentTyped nestedBindingsTyped nestedLookup
      outerLookup exported rest =>
      rename_i nestedEnvironment nestedEnvironmentTypes nestedBindings
        nestedBindingTypes nestedArguments parameterIndex outerIndex
        outerArgument matcher target afterExportTypes privateRemaining
      let successors : List PatternFunctionState := [⟨
        [MatchingTree.node
          (.atom ⟨.embed outerIndex, matcher, target⟩ ::
            .node [] nestedEnvironment nestedBindings nestedArguments ::
              privateRemaining)
          privateEnvironment privateBindings arguments] ++ remaining,
        outerEnvironment, outerBindings⟩]
      refine .inr ⟨successors, ?_, ?_⟩
      · simp [successors, stepPatternFunctionHead, nestedLookup]
      · intro successor member
        simp only [successors, List.mem_singleton] at member
        subst successor
        exact .mk outerEnvironmentTyped outerBindingsTyped
          (.node privateEnvironmentTyped privateBindingsTyped
            (.parameter outerLookup exported
              (.nestedDone nestedEnvironmentTyped nestedBindingsTyped rest))
            tail)
  | nestedDone nestedEnvironmentTyped nestedBindingsTyped rest =>
      rename_i nestedEnvironment nestedEnvironmentTypes nestedBindings
        nestedBindingTypes privateRemaining nestedArguments
      let successors : List PatternFunctionState := [⟨
        [.node privateRemaining privateEnvironment privateBindings arguments] ++
          remaining,
        outerEnvironment, outerBindings⟩]
      refine .inr ⟨successors, ?_, ?_⟩
      · simp [successors, stepPatternFunctionHead]
      · intro successor member
        simp only [successors, List.mem_singleton] at member
        subst successor
        exact .mk outerEnvironmentTyped outerBindingsTyped
          (.node privateEnvironmentTyped privateBindingsTyped rest tail)

/-- The concrete checked state invariant satisfies the local DFS contract. -/
theorem stepPatternFunctionState_checkedScopedSafe
    (reducerSafe : CheckedScopedAtomReducerTypedSafe reduceAtom) :
    ScopedStateStepTypedSafe definitions reduceAtom
      (CheckedScopedStateTyping signature definitions) := by
  intro state answerTypes stateTyped
  rcases state with ⟨work, environment, bindings⟩
  cases stateTyped with
  | mk environmentTyped bindingsTyped workTyped =>
      rename_i environmentTypes bindingTypes
      cases workTyped with
      | nil =>
          exact .inr ⟨.yield bindings, rfl,
            .yield bindings (by simpa using bindingsTyped)⟩
      | ordinary head tail =>
          rename_i atom newBindings remaining
          rcases reducerSafe environmentTyped bindingsTyped head with
            timeout | ⟨reduction, reduced, reductionTyped⟩
          · exact .inl (by
              change FuelResult.map SearchStep.expand
                (stepPatternFunctionHead definitions reduceAtom (.atom atom)
                  remaining environment bindings) = .timeout
              rw [stepPatternFunctionHead_checkedOrdinary head, timeout]
              rfl)
          · cases reductionTyped with
            | intro immediateTypes immediateTyped branchesTyped =>
                let successors : List PatternFunctionState :=
                  reduction.branches.map fun branch =>
                    ⟨MatchingTree.ofAtoms branch ++ remaining, environment,
                      bindings ++ reduction.bindings⟩
                refine .inr ⟨.expand successors, ?_, .expand successors ?_⟩
                · change FuelResult.map SearchStep.expand
                      (stepPatternFunctionHead definitions reduceAtom (.atom atom)
                        remaining environment bindings) =
                    .ok (.expand successors)
                  rw [stepPatternFunctionHead_checkedOrdinary head, reduced]
                  simp [continueTreeAtom, successors, FuelResult.map]
                · intro successor member
                  simp only [successors, List.mem_map] at member
                  rcases member with ⟨branch, branchMember, rfl⟩
                  obtain ⟨delayedTypes, branchTyped, bindingEq⟩ :=
                    branchesTyped branch branchMember
                  have tail' : CheckedScopedWorkTyping signature definitions
                      environmentTypes
                      ((bindingTypes ++ immediateTypes) ++ delayedTypes) remaining
                      answerTypes := by
                    simpa [List.append_assoc, bindingEq] using tail
                  exact .mk environmentTyped
                    (bindingsTyped.append immediateTyped)
                    (CheckedScopedWorkTyping.prependTotalAtoms branchTyped tail')
      | application found checked arity body tail =>
          rename_i name definition arguments matcher target afterNodeTypes
            remaining
          let successors : List PatternFunctionState := [⟨
            [.node [.atom ⟨definition.body, matcher, target⟩]
              environment [] arguments] ++ remaining,
            environment, bindings⟩]
          refine .inr ⟨.expand successors, by
            simp [successors, stepPatternFunctionState,
              stepPatternFunctionHead, lookupPatternFunctionApplication,
              found, arity], .expand successors ?_⟩
          intro successor member
          simp only [successors, List.mem_singleton] at member
          subst successor
          exact .mk environmentTyped bindingsTyped
            (.node environmentTyped .nil body tail)
      | node privateEnvironmentTyped privateBindingsTyped inside tail =>
          rcases inside.stepNodeCheckedSafe reducerSafe environmentTyped
              bindingsTyped privateEnvironmentTyped privateBindingsTyped tail with
            timeout | ⟨successors, stepped, successorsTyped⟩
          · exact .inl (by simp [stepPatternFunctionState, timeout])
          · exact .inr ⟨.expand successors, by
                simp [stepPatternFunctionState, stepped, FuelResult.map],
              .expand successors successorsTyped⟩

/-- Finite depth-first safety for the checked recursive MNode fragment. -/
theorem depthFirstCheckedScopedMatching_typedSafe
    (reducerSafe : CheckedScopedAtomReducerTypedSafe reduceAtom)
    (statesTyped : ScopedMatchingStatesTyping
      (CheckedScopedStateTyping signature definitions) states answerTypes)
    (fuel : Nat) :
    TypedMatchingSearchResult answerTypes
      (depthFirstFuel (stepPatternFunctionState definitions reduceAtom)
        fuel states) :=
  depthFirstScopedMatching_typedSafe
    (stepPatternFunctionState_checkedScopedSafe reducerSafe) statesTyped fuel

/-- Initial-state checked search safety.  The reducer premise is the explicit
source-pattern preservation bridge needed for user-matcher branches. -/
theorem searchPatternFunctionsFuel_checkedScopedSafe
    (reducerSafe : CheckedScopedAtomReducerTypedSafe
      (evaluationAtomReducer evaluate))
    (initialTyped : CheckedScopedStateTyping signature definitions
      ⟨[.atom ⟨pattern, matcher, target⟩], environment, []⟩ answerTypes)
    (fuel : Nat) :
    TypedMatchingSearchResult answerTypes
      (searchPatternFunctionsFuel definitions evaluate fuel environment
        pattern matcher target) :=
  searchPatternFunctionsFuel_typedSafe_of_stateStep
    (stepPatternFunctionState_checkedScopedSafe reducerSafe) initialTyped fuel

/-- The common-fuel total expression judgment supplies the evaluator callback
used by recursively typed matcher clauses.  A future source-pattern
preservation bridge can therefore feed `CheckedScopedAtomReducerTypedSafe`
without adding another evaluator assumption. -/
theorem evalFuel_totalCore_checkedScopedCallbackSafe (fuel : Nat) :
    EmbeddedEvaluatorSafe
      (fun context expression target => TotalCoreTyping expression target context)
      (evalFuel fuel) :=
  evalFuel_totalCore_embeddedSafe fuel

/-! ## Safety exported through the checked evaluator on the simulation fragment -/

/-- On the evaluator-independent fragment, a checked frozen program inherits
the ordinary evaluator's type preservation and no-stuck theorem exactly.
This result uses the existing evaluator equality; it does not assume safety
of the MNode evaluator. -/
theorem RuntimeTyping.checkedPatternFunctionNodesSafety
    (typing : RuntimeTyping expression target context)
    (independent : expression.EvaluatorIndependent)
    (agreement : definitions.Agree signature)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyped : EnvironmentTyping environment context) :
    TypedResult target
      (evalCheckedPatternFunctionNodesFuel signature definitions agreement fuel
        environment expression) := by
  unfold evalCheckedPatternFunctionNodesFuel
  rw [evaluatorIndependent_nodeEvaluation_eq_evalFuel independent]
  exact typing.coreSafety fuel environment environmentTyped

/-- No-stuck projection of `checkedPatternFunctionNodesSafety`. -/
theorem RuntimeTyping.checkedPatternFunctionNodesNeverStuck
    (typing : RuntimeTyping expression target context)
    (independent : expression.EvaluatorIndependent)
    (agreement : definitions.Agree signature)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyped : EnvironmentTyping environment context) :
    (evalCheckedPatternFunctionNodesFuel signature definitions agreement fuel
      environment expression).NotStuck :=
  (typing.checkedPatternFunctionNodesSafety independent agreement fuel
    environment environmentTyped).notStuck

/-- A package returned by the public freeze checker can be passed directly to
the preservation theorem on the proved simulation fragment.  The successful
checker equation records the public construction path; all semantic evidence
comes from the returned package's kernel-checked agreement field. -/
theorem RuntimeTyping.freezeCheckedPatternFunctionNodesSafety
    {base : Signature} {baseWellFormed : base.WellFormed}
    {sources : List PatternFunctionSourceDefinition}
    {program : FrozenPatternFunctionProgram}
    (_frozen : PatternFunctionFreeze.freezePatternFunctions base baseWellFormed
      sources = some program)
    (typing : RuntimeTyping expression target context)
    (independent : expression.EvaluatorIndependent)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyped : EnvironmentTyping environment context) :
    TypedResult target
      (evalCheckedPatternFunctionNodesFuel program.signature program.definitions
        program.agreement fuel environment expression) :=
  typing.checkedPatternFunctionNodesSafety independent program.agreement fuel
    environment environmentTyped

end TypePM.Runtime
