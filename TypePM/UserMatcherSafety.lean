import TypePM.MatcherSafety
import TypePM.Runtime.ClauseDispatch

/-!
# First typed user-matcher reduction

This module certifies one concrete but genuine user-defined matcher clause:
a one-hole pattern-pattern header, one variable data arm, a singleton
decomposition body, and `something` as the delegated matcher.  It exercises
the real clause dispatcher and its environment order without claiming the
still-missing full M4 elaboration-to-runtime bridge.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- The arm body returns its data-pattern binding as one decomposition. -/
def singletonDecompositionBody : Source.Expr :=
  .ctor DataCtor.cons [.var 0, .ctor DataCtor.nil []]

/-- The first runtime-certified user matcher clause. -/
def singleHoleVariableClause : Source.MatcherClause :=
  .mk .hole .something [.mk .var singletonDecompositionBody]

theorem singletonDecompositionBody_typed
    (definitionTypes : List Ty) (target : Ty) :
    RuntimeTyping singletonDecompositionBody (TypePM.DataTypes.list target)
      (target :: definitionTypes) := by
  exact .listCons (.var rfl) (.listNil target)

theorem singleHoleVariableClause_typed
    (definitionTypes : List Ty) (target : Ty) :
    RuntimeMatcherClauseTyping definitionTypes target
      singleHoleVariableClause := by
  exact .mk (.hole .any)
    (.one (.checked (.something target) (.matcherToSlot .equal)))
    (.cons (.mk .var (singletonDecompositionBody_typed definitionTypes target))
      .nil)

/-- A scoped atom judgment for the first user-matcher slice.  The ordinary
`MatchingAtomTyping` judgment remains the built-in fragment; successful user
dispatch below produces continuations in that existing judgment. -/
inductive SingleHoleUserAtomTyping :
    MatchingAtom → Ty → Prop where
  | mk
      (environment : EnvironmentTyping matcherEnvironment definitionTypes)
      (target : ValueTyping targetValue targetType) :
      SingleHoleUserAtomTyping
        ⟨.var,
          .matcherV matcherEnvironment [singleHoleVariableClause]
            [singleHoleVariableClause],
          targetValue⟩ targetType

theorem SingleHoleUserAtomTyping.matcherValueTyping
    (typing : SingleHoleUserAtomTyping atom targetType) :
    ValueTyping atom.matcher (.matcher .any targetType) := by
  cases typing with
  | mk environment target =>
      exact .matcherClosure environment
        (.cons (singleHoleVariableClause_typed _ _) .nil) ⟨[], rfl⟩

/-- Local preservation/progress contract for the scoped user-matcher atom.
Its conclusion is the per-atom obligation used by `AtomReducerTypedSafe`:
every produced branch is certified by `MatchingAtomsTyping`, and no proof
assumes the reducer's result. -/
def SingleHoleUserAtomReducerTypedSafe
    (eval : ValueEnvironment → Source.Expr → FuelResult Value) : Prop :=
  ∀ {environmentTypes bindingTypes environment bindings atom targetType},
    EnvironmentTyping environment environmentTypes →
    ValueTypings bindings bindingTypes →
    SingleHoleUserAtomTyping atom targetType →
    (∀ {matcherEnvironment definitionTypes targetValue},
      EnvironmentTyping matcherEnvironment definitionTypes →
      ValueTyping targetValue targetType →
      eval (targetValue :: matcherEnvironment) singletonDecompositionBody =
        .ok (Value.buildList [targetValue])) →
    (∀ matcherEnvironment,
      eval matcherEnvironment .something = .ok .something) →
    ∃ reduction,
      reduceMatcherAtom eval (bindings ++ environment) atom =
        .ok (.hit reduction) ∧
      AtomReductionTyping
        (fun context expression target => RuntimeTyping expression target context)
        environmentTypes bindingTypes [targetType] reduction

theorem reduceMatcherAtom_singleHole_typedSafe
    (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
    SingleHoleUserAtomReducerTypedSafe eval := by
  intro environmentTypes bindingTypes environment bindings atom targetType
    environmentTyped bindingsTyped atomTyped bodyEval somethingEval
  cases atomTyped
  rename_i matcherEnvironment definitionTypes targetValue environmentTyping targetTyping
  let reduction : AtomReduction :=
    ⟨[[⟨.var, .something, targetValue⟩]], []⟩
  refine ⟨reduction, ?_, ?_⟩
  · have bodySuccess := bodyEval environmentTyping targetTyping
    have nextSuccess := somethingEval matcherEnvironment
    have decompositionSuccess :
        decodeDecompositions 1 (Value.buildList [targetValue]) =
          some [[targetValue]] := by
      simp [decodeDecompositions, List.mapM_cons]
    have branchesSuccess :
        buildMatchingBranches [.var] [.something] [[targetValue]] =
          some [[⟨.var, .something, targetValue⟩]] := by
      simp [buildMatchingBranches, List.mapM_cons, zipMatchingAtoms]
    have clauseSuccess :
        tryMatcherClause eval (bindings ++ environment) matcherEnvironment
          .var targetValue singleHoleVariableClause =
          .ok (.hit [[⟨.var, .something, targetValue⟩]]) := by
      simp [tryMatcherClause, inspectPatternPattern, FuelResult.traverse,
        firstHit, tryMatcherArm, singleHoleVariableClause,
        matchValueDataPattern, bodySuccess, nextSuccess,
        decompositionSuccess, branchesSuccess, closeMatcherArmsResult, FuelResult.bind,
        FuelResult.map]
    have dispatchSuccess :
        dispatchMatcherClauses eval (bindings ++ environment) matcherEnvironment
          [singleHoleVariableClause] .var targetValue =
          .ok (.hit [[⟨.var, .something, targetValue⟩]]) := by
      simp [dispatchMatcherClauses, firstHit, clauseSuccess]
    simp [reduceMatcherAtom, dispatchSuccess, clauseResultToAtomReduction,
      reduction, FuelResult.map]
  · refine ⟨[], .nil, ?_⟩
    intro branch member
    simp [reduction] at member
    subst branch
    exact ⟨[targetType],
      .cons _ [] [targetType] [] (.somethingVar targetTyping) .nil,
      rfl⟩

/-! ## Decoder consequences of the canonical forms -/

theorem ValueTypings.length_eq :
    (typing : ValueTypings values targets) → values.length = targets.length
  | .nil => rfl
  | .cons _ tail => by simp [tail.length_eq]

/-- A typed product of arity at least two passes the exact product decoder. -/
theorem ValueTyping.decodeProduct_many
    (atLeastTwo : 2 ≤ targets.length)
    (typing : ValueTyping value (.prod targets)) :
    ∃ values, value = .tuple values ∧
      decodeProduct targets.length value = some values ∧
      ValueTypings values targets := by
  obtain ⟨values, rfl, valuesTyped⟩ := typing.product_canonical
  exact ⟨values, rfl,
    decodeProduct_many_exact atLeastTwo values valuesTyped.length_eq,
    valuesTyped⟩

/-- A value with the statically selected zero/one/many hole-product type
passes the corresponding runtime decoder.  The decoded values retain the
source-ordered hole target types. -/
theorem ValueTyping.decodeHoleProduct
    (typing : ValueTyping value (runtimeHoleProductTarget holes)) :
    ∃ values,
      decodeProduct holes.length value = some values ∧
      ValueTypings values (Dual.targets holes) := by
  cases holes with
  | nil =>
      obtain ⟨values, rfl, valuesTyped⟩ := typing.product_canonical
      cases valuesTyped
      exact ⟨[], rfl, .nil⟩
  | cons first rest =>
      cases rest with
      | nil =>
          exact ⟨[value], rfl, .cons typing .nil⟩
      | cons second rest =>
          obtain ⟨values, rfl, valuesTyped⟩ := typing.product_canonical
          refine ⟨values, ?_, valuesTyped⟩
          have length : values.length = (first :: second :: rest).length := by
            simpa [Dual.targets] using valuesTyped.length_eq
          exact decodeProduct_many_exact (by simp) values
            length

/-- Pointwise typing for a decoded list of matcher decompositions. -/
inductive HoleDecompositionsTyping (holes : List Dual) :
    List (List Value) → Prop where
  | nil : HoleDecompositionsTyping holes []
  | cons
      (head : ValueTypings values (Dual.targets holes))
      (tail : HoleDecompositionsTyping holes decompositions) :
      HoleDecompositionsTyping holes (values :: decompositions)

/-- Pointwise decoding of a host list of typed hole products. -/
theorem ListValueTypings.decodeHoleProducts
    (typing : ListValueTypings values (runtimeHoleProductTarget holes)) :
    ∃ decompositions,
      List.mapM (decodeProduct holes.length) values = some decompositions ∧
      HoleDecompositionsTyping holes decompositions := by
  cases values with
  | nil =>
      cases typing
      exact ⟨[], rfl, .nil⟩
  | cons headValue tailValues =>
      cases typing with
      | cons headTyped tailTyped =>
          obtain ⟨head, headDecoded, headTyping⟩ :=
            headTyped.decodeHoleProduct
          obtain ⟨tail, tailDecoded, tailTyping⟩ :=
            tailTyped.decodeHoleProducts
          refine ⟨head :: tail, ?_, .cons headTyping tailTyping⟩
          simp [List.mapM_cons, headDecoded, tailDecoded]

/-- A canonical typed list of hole products always passes the full
decomposition decoder, for zero, one, and many holes. -/
theorem ValueTyping.decodeDecompositions_typed
    (typing : ValueTyping value
      (TypePM.DataTypes.list (runtimeHoleProductTarget holes))) :
    ∃ decompositions,
      decodeDecompositions holes.length value = some decompositions ∧
      HoleDecompositionsTyping holes decompositions := by
  obtain ⟨values, rfl, valuesTyped⟩ := typing.list_canonical
  simp only [TypePM.Runtime.decodeDecompositions,
    Value.viewList_buildList]
  exact valuesTyped.decodeHoleProducts

/-- A typed canonical list always passes one-hole decomposition decoding; the
decoder preserves source list order and wraps each element as one product. -/
theorem ValueTyping.decodeDecompositions_one
    (typing : ValueTyping value (TypePM.DataTypes.list element)) :
    ∃ values, value = Value.buildList values ∧
      decodeDecompositions 1 value = some (values.map (fun item => [item])) ∧
      ListValueTypings values element := by
  obtain ⟨values, rfl, valuesTyped⟩ := typing.list_canonical
  refine ⟨values, rfl, ?_, valuesTyped⟩
  simp only [decodeDecompositions, Value.viewList_buildList]
  change List.mapM (decodeProduct 1) values =
    some (values.map (fun item => [item]))
  have decoded : ∀ items : List Value,
      List.mapM (decodeProduct 1) items =
        some (items.map (fun item => [item])) := by
    intro items
    rw [← List.mapM'_eq_mapM]
    induction items with
    | nil => rfl
    | cons head tail induction => simp [List.mapM', induction]
  exact decoded values

end TypePM.Runtime
