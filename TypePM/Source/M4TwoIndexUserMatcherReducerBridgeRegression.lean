import TypePM.Source.M4TwoIndexPatternDispatchProducer
import TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility
import TypePM.ValueIndexedPaper1MultisetGeneralConsFuelIndexedRegression

/-!
# Actual Paper 1 user-dispatch regression for the two-index bridge

The closed Paper 1 multiset matcher handles a variable pattern by dispatching
its real seventh clause and returning one delegated `something` atom.  This
regression runs that dispatch in an ordinary matching environment containing
the actual recursive List closure.  The environment is safe in the indexed
relation and is provably outside the traditional structural
`EnvironmentTyping` relation defined in this repository.

The caller-selected atom relation classifies exactly the delegated built-in
variable atom.  Its local reducer law types the recursive closure binding with
`FuelEnvironmentSafe`; no structural `ValueTyping` is involved.  An independent
M4 elaboration of the delegated variable pattern fixes its source-ordered
binding type, and a finite atom obligation converts the actual singleton
dispatch to the two-index certificate.  It passes through
`toTwoIndexUserMatcherStateTyping` and then `searchPatternFuel_twoIndexSafe`
for all three required state visits without a complete-search equation or a
whole-evaluator safety premise.

The same executable search succeeds with the recursive closure as its answer
when given three state visits.  That exact equation is kept in a separate
regression theorem; it is not used by the two-index safety proof.  The answer
has `FuelEnvironmentSafe` evidence but no structural `ValueTypings` evidence.
A separate negative theorem records that the replaced M4 branch-work relation
could not express this positive-index branch.
-/

namespace TypePM.Source.M4TwoIndexUserMatcherReducerBridgeRegression

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open TypePM.Source.MatcherTyping
open TypePM.Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open TypePM.Source.MatcherTyping.M4Paper1RecursiveClosureTypingBoundary
open TypePM.ValueIndexedPaper1MultisetGeneralConsSafety
open TypePM.ValueIndexedPaper1MultisetGeneralConsFuelIndexedRegression

abbrev CoreExpressionTyping : EmbeddedExpressionTyping :=
  TypePM.ValueIndexedPaper1MultisetGeneralConsFuelIndexedRegression.CoreExpressionTyping

def recursiveClosureType : Ty :=
  TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureType

def recursiveClosureEnvironment : ValueEnvironment :=
  [listRecursiveClosure]

def recursiveClosureVariableAtom : MatchingAtom :=
  ⟨.var, closedMultisetMatcherValue, listRecursiveClosure⟩

def recursiveClosurePrimitiveAtom : MatchingAtom :=
  ⟨.var, .something, listRecursiveClosure⟩

/-- The independent M4 synthesis result for the variable pattern delegated by
the successful catch-all clause. -/
def recursiveClosureVariableGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := [.var ⟨0⟩]
    hard := []
    pending := [] }

def recursiveClosureVariableSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => recursiveClosureType }

theorem recursiveClosureVariable_elaborates :
    PatternElaborates Paper1FrozenSignature.signature
      [Scheme.mono recursiveClosureType] [] .var []
      ⟨0, 0⟩ recursiveClosureVariableGenerated ⟨1, 1⟩ := by
  exact .var

theorem recursiveClosureVariable_supported :
    DirectRuntimePatternSupported .var :=
  .var

theorem recursiveClosureVariable_semantic :
    GeneratedPatternRuntimeSolution recursiveClosureVariableGenerated
      recursiveClosureVariableSolution := by
  simp [GeneratedPatternRuntimeSolution, recursiveClosureVariableGenerated,
    Solves]

set_option maxRecDepth 100000 in
/-- Callback fuel two executes the real catch-all variable clause. -/
theorem recursiveClosure_variable_dispatch_exact :
    dispatchMatcherClauses (evalFuel 2) recursiveClosureEnvironment
      closedMultisetMatcherEnvironment multisetClauses .var
      listRecursiveClosure =
        .ok (.hit (variableBranches listRecursiveClosure)) := by
  with_unfolding_all rfl

theorem recursiveClosureEnvironment_fuelSafe (index : Nat) :
    FuelEnvironmentSafe index recursiveClosureEnvironment
      [recursiveClosureType] := by
  simpa [recursiveClosureEnvironment, recursiveClosureType] using
    TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureEnvironment_fuelSafe
      index

/-- Fixture atom relation for the delegated built-in variable atom.  It is
available at every positive search index and leaves the retained logical
index independent. -/
inductive RecursiveClosureAtomRelation : TwoIndexMatchingAtomRelation where
  | primitive :
      RecursiveClosureAtomRelation (searchFuel + 1) residual environmentTypes
        bindingTypes recursiveClosurePrimitiveAtom [recursiveClosureType]

theorem recursiveClosureAtomRelation_downwardClosed :
    TwoIndexMatchingAtomRelation.DownwardClosed
      RecursiveClosureAtomRelation := by
  intro searchFuel residual environmentTypes bindingTypes atom newBindings
    typed
  cases typed
  exact .primitive

/-- The delegated built-in atom has the same exact reduction in every runtime
atom environment. -/
theorem recursiveClosure_primitive_reducer_exact_any
    (atomEnvironment : ValueEnvironment) :
    evaluationAtomReducer (evalFuel 2) atomEnvironment
      recursiveClosurePrimitiveAtom =
        .ok (.hit ⟨[[]], [listRecursiveClosure]⟩) := by
  rfl

/-- Local reducer preservation for the fixture relation.  Its immediate
binding is checked directly in the caller-selected indexed relation. -/
theorem recursiveClosureAtomReducer_twoIndexSafe :
    TwoIndexRelationalAtomReducerTypedSafe FuelEnvironmentSafe
      FuelEnvironmentSafe RecursiveClosureAtomRelation
      (evaluationAtomReducer (evalFuel 2)) := by
  intro searchFuel residual environmentTypes bindingTypes environment bindings
    atom newBindings environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | primitive =>
      let reduction : AtomReduction := ⟨[[]], [listRecursiveClosure]⟩
      refine .inr ⟨reduction, ?_, ?_⟩
      · simpa [reduction] using
          recursiveClosure_primitive_reducer_exact_any
            (bindings ++ environment)
      · exact .intro [recursiveClosureType]
          (by simpa [reduction, recursiveClosureEnvironment] using
            recursiveClosureEnvironment_fuelSafe (searchFuel + residual))
          (by
            intro branch member
            simp [reduction] at member
            subst branch
            exact ⟨[], .nil, rfl⟩)

/-- M4 variable-pattern elaboration plus one bounded local atom obligation
generate the branch-work certificate for the exact actual dispatch at
predecessor search index two. -/
theorem recursiveClosure_variable_dispatch_twoIndex :
    TwoIndexPatternDispatchCertificate
      (relationalTwoIndexMatchingBranchRelation
        RecursiveClosureAtomRelation)
      2 1 [recursiveClosureType] [] [recursiveClosureType]
      (dispatchMatcherClauses (evalFuel 2) recursiveClosureEnvironment
        closedMultisetMatcherEnvironment multisetClauses .var
        listRecursiveClosure) := by
  rw [recursiveClosure_variable_dispatch_exact]
  obtain ⟨newBindings, dispatchTyped, bindingsEq⟩ :=
    PatternElaborates.toSingletonTwoIndexDispatch
      (atomRelation := RecursiveClosureAtomRelation)
      (searchFuel := 2) (residual := 1)
      (environmentTypes := [recursiveClosureType])
      (branches := variableBranches listRecursiveClosure)
      recursiveClosureVariable_elaborates
      Paper1FrozenSignature.runtimeCompatible
      recursiveClosureVariable_supported
      recursiveClosureVariable_semantic
      (MonomorphicContextCompatible.cons MonomorphicContextCompatible.nil)
      (by
        intro newBindings patternTyped branch member
        simp [variableBranches] at member
        subst branch
        cases patternTyped
        exact M4TwoIndexMatchingBranchObligations.cons
          { patternTyped := PatternBinds.var
            atomSafe := ⟨rfl, by
              simpa [recursiveClosureVariableGenerated,
                recursiveClosureVariableSolution, Ty.apply,
                Ty.applyList,
                recursiveClosurePrimitiveAtom] using
                (RecursiveClosureAtomRelation.primitive
                  (searchFuel := 1) (residual := 1)
                  (environmentTypes := [recursiveClosureType])
                  (bindingTypes := []))⟩ }
          .nil)
  have newBindingsEq : newBindings = [recursiveClosureType] := by
    simpa [recursiveClosureVariableGenerated,
      recursiveClosureVariableSolution, Ty.applyList, Ty.apply] using
        bindingsEq.symm
  subst newBindings
  exact dispatchTyped

/-- The actual user atom is safe for all three required state visits.  The
dispatch branch and empty remaining work are combined structurally before
the generic producer builds successor states. -/
theorem recursiveClosure_variable_initial_twoIndex :
    TwoIndexMatchingStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
      (evaluationAtomReducer (evalFuel 2)) 3 1
      ⟨[recursiveClosureVariableAtom], recursiveClosureEnvironment, []⟩
      [recursiveClosureType] := by
  have stateTyped :=
    recursiveClosure_variable_dispatch_twoIndex.toTwoIndexUserMatcherStateTyping
      (environmentInvariant := FuelEnvironmentSafe)
      (bindingsInvariant := FuelEnvironmentSafe)
      (atomRelation := RecursiveClosureAtomRelation)
      (eval := evalFuel 2)
      (environment := recursiveClosureEnvironment)
      (bindings := [])
      (matcherEnvironment := closedMultisetMatcherEnvironment)
      (original := multisetClauses)
      (remainingClauses := multisetClauses)
      (pattern := .var)
      (target := listRecursiveClosure)
      (remaining := [])
      (tailBindings := [])
      IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
      IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
      IndexedMatchingInvariant.fuelEnvironmentSafe_appendClosed
      recursiveClosureAtomRelation_downwardClosed
      recursiveClosureAtomReducer_twoIndexSafe
      (recursiveClosureEnvironment_fuelSafe 4)
      (FuelEnvironmentSafe.nil 4)
      (by simp [reduceBuiltinAtom])
      (RelationalTwoIndexMatchingBranchTyping.nil
        (atomRelation := RecursiveClosureAtomRelation)
        (searchFuel := 2) (residual := 1)
        (environmentTypes := [recursiveClosureType])
        (bindingTypes := [recursiveClosureType]))
  simpa [recursiveClosureVariableAtom, closedMultisetMatcherValue] using
    stateTyped

/-- End-to-end use of the generic two-index search theorem.  This proof uses
only the initial local state certificate above; no equation for the complete
search appears among its premises. -/
theorem recursiveClosure_variable_search_twoIndexSafe :
    MatchingSearchResultSafeWith (FuelEnvironmentSafe 1)
      [recursiveClosureType]
      (searchPatternFuel (evalFuel 2) 3 recursiveClosureEnvironment .var
        closedMultisetMatcherValue listRecursiveClosure) := by
  exact searchPatternFuel_twoIndexSafe
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    recursiveClosure_variable_initial_twoIndex

theorem recursiveClosure_variable_search_neverStuck :
    (searchPatternFuel (evalFuel 2) 3 recursiveClosureEnvironment .var
      closedMultisetMatcherValue listRecursiveClosure).NotStuck :=
  recursiveClosure_variable_search_twoIndexSafe.notStuck

/-- The first actual reduction is the user-dispatch hit classified above. -/
theorem recursiveClosure_variable_reducer_exact :
    evaluationAtomReducer (evalFuel 2) recursiveClosureEnvironment
      recursiveClosureVariableAtom =
        .ok (.hit ⟨variableBranches listRecursiveClosure, []⟩) := by
  unfold evaluationAtomReducer combineAtomReducers
  simp [recursiveClosureVariableAtom, reduceBuiltinAtom, reduceMatcherAtom,
    closedMultisetMatcherValue, recursiveClosure_variable_dispatch_exact,
    clauseResultToAtomReduction]

/-- Its delegated built-in atom binds the recursive closure itself. -/
theorem recursiveClosure_primitive_reducer_exact :
    evaluationAtomReducer (evalFuel 2) recursiveClosureEnvironment
      recursiveClosurePrimitiveAtom =
        .ok (.hit ⟨[[]], [listRecursiveClosure]⟩) := by
  rfl

/-- The imported positive-index M4 work relation cannot certify this actual
delegated atom: every built-in route requires the impossible structural
`ValueTyping` proof for the recursive closure, while the user constructors
apply only to a `.matcherV` atom rather than this built-in `.something` atom. -/
theorem recursiveClosure_primitiveBranch_not_positiveFuelIndexed :
    ∀ searchPredecessor,
      ¬ FuelIndexedRecursiveMatchingAtomsTyping CoreExpressionTyping
        (evalFuel 2) (searchPredecessor + 1) [recursiveClosureType] []
        [recursiveClosurePrimitiveAtom] [recursiveClosureType] := by
  intro searchPredecessor
  induction searchPredecessor with
  | zero =>
      intro typing
      generalize atomsEq : [recursiveClosurePrimitiveAtom] = atoms at typing
      generalize outputsEq : [recursiveClosureType] = outputs at typing
      cases typing with
      | nil => simp at atomsEq
      | cons head tail =>
          simp only [List.cons.injEq] at atomsEq
          rcases atomsEq with ⟨rfl, rfl⟩
          cases tail with
          | zero nonempty => exact (nonempty rfl).elim
          | nil =>
              simp at outputsEq
              subst outputsEq
              cases head with
              | builtin atomTyped =>
                  cases atomTyped with
                  | somethingVar targetTyped =>
                      exact listRecursiveClosure_not_valueTyping _ _ targetTyped
              | stable atomTyped =>
                  cases atomTyped with
                  | builtin builtinTyped =>
                      cases builtinTyped with
                      | somethingVar targetTyped =>
                          exact listRecursiveClosure_not_valueTyping _ _
                            targetTyped
  | succ searchPredecessor induction =>
      intro typing
      exact induction typing.previous

theorem recursiveClosure_variable_step_exact :
    stepMatchingState (evaluationAtomReducer (evalFuel 2))
      ⟨[recursiveClosureVariableAtom], recursiveClosureEnvironment, []⟩ =
        .ok (.expand
          [⟨[recursiveClosurePrimitiveAtom], recursiveClosureEnvironment,
            []⟩]) := by
  simp [stepMatchingState, recursiveClosure_variable_reducer_exact,
    MatchingState.successors, MatchingState.continueWith, variableBranches,
    recursiveClosurePrimitiveAtom]

theorem recursiveClosure_primitive_step_exact :
    stepMatchingState (evaluationAtomReducer (evalFuel 2))
      ⟨[recursiveClosurePrimitiveAtom], recursiveClosureEnvironment, []⟩ =
        .ok (.expand
          [⟨[], recursiveClosureEnvironment, [listRecursiveClosure]⟩]) := by
  simp [stepMatchingState, recursiveClosure_primitive_reducer_exact,
    MatchingState.successors, MatchingState.continueWith]

theorem recursiveClosure_yield_step_exact :
    stepMatchingState (evaluationAtomReducer (evalFuel 2))
      ⟨[], recursiveClosureEnvironment, [listRecursiveClosure]⟩ =
        .ok (.yield [listRecursiveClosure]) := by
  rfl

/-- Independent operational regression: three visits process the user atom,
the delegated built-in atom, and the final yield state.  This theorem is not
used by `recursiveClosure_variable_search_twoIndexSafe`. -/
theorem recursiveClosure_variable_search_exact :
    searchPatternFuel (evalFuel 2) 3 recursiveClosureEnvironment .var
      closedMultisetMatcherValue listRecursiveClosure =
        .ok [[listRecursiveClosure]] := by
  unfold searchPatternFuel searchMatchingFuel
  change depthFirstFuel (stepMatchingState
      (evaluationAtomReducer (evalFuel 2))) 3
      [⟨[recursiveClosureVariableAtom], recursiveClosureEnvironment, []⟩] =
        .ok [[listRecursiveClosure]]
  simp [depthFirstFuel, recursiveClosure_variable_step_exact,
    recursiveClosure_primitive_step_exact, recursiveClosure_yield_step_exact,
    FuelResult.map]

/-- The concrete successful answer is safe at the retained logical index,
independently of the complete-search equation. -/
theorem recursiveClosure_successAnswer_fuelSafe :
    FuelEnvironmentSafe 1 [listRecursiveClosure] [recursiveClosureType] := by
  simpa [recursiveClosureEnvironment] using
    recursiveClosureEnvironment_fuelSafe 1

/-- The ordinary matching environment used above is excluded by the
traditional structural environment judgment in this repository. -/
theorem recursiveClosureEnvironment_not_environmentTyping :
    ¬ EnvironmentTyping recursiveClosureEnvironment
      [recursiveClosureType] := by
  simpa [recursiveClosureEnvironment, recursiveClosureType] using
    TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureEnvironment_not_environmentTyping

/-- The concrete successful answer is likewise excluded by structural
`ValueTypings`, even though it is safe in the indexed relation. -/
theorem recursiveClosure_successAnswer_not_valueTypings :
    ¬ ValueTypings [listRecursiveClosure] [recursiveClosureType] := by
  simpa [recursiveClosureType] using
    TypePM.Source.M4TwoIndexRecursiveClosureSearchRegression.recursiveClosureBindings_not_valueTypings

end TypePM.Source.M4TwoIndexUserMatcherReducerBridgeRegression
