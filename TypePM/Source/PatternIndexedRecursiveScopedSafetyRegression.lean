import TypePM.Source.PatternIndexedRecursiveScopedSafety
import TypePM.PatternFunctionSafetyRegression
import TypePM.UserMatcherSafety

/-!
# User-matcher branch entering a checked MNode

The clause below delegates the first field of a constructor pattern.  That
field is a publicly frozen pattern-function application.  The regression
therefore exercises the exact path that erased branch typing cannot express:
user dispatch preserves `.app`, checked lookup creates an MNode, the body
exports its parameter, and the ordinary variable reducer returns the result.
-/

namespace TypePM.Source.PatternIndexedRecursiveScopedSafetyRegression

open TypePM.Runtime
open TypePM.PatternFunctionSafetyRegression
open TypePM.Source.MatcherTyping
open TypePM.Source.PatternFunctionFreeze

def applicationFieldClause : MatcherClause :=
  .mk (.ctor PatternCtor.cons [.hole, .wild]) .something
    [.mk .var singletonDecompositionBody]

def delegatedApplicationPattern : Pattern :=
  .app identityName [.var]

def constructorApplicationPattern : Pattern :=
  .ctor PatternCtor.cons [delegatedApplicationPattern, .wild]

def applicationFieldMatcher : Value :=
  .matcherV [] [applicationFieldClause] [applicationFieldClause]

def applicationFieldAtom : MatchingAtom :=
  ⟨constructorApplicationPattern, applicationFieldMatcher, .int 31⟩

abbrev CoreExpressionTyping : EmbeddedExpressionTyping :=
  fun context expression target => TotalCoreTyping expression target context

theorem applicationFieldClause_inputTyped :
    TotalRuntimeMatcherClauseInputTyping CoreExpressionTyping [] [] .int
      constructorApplicationPattern applicationFieldClause := by
  apply TotalRuntimeMatcherClauseInputTyping.mk
      (holes := [⟨.any, .int⟩]) (captureTypes := [])
  · apply RuntimePPatTyping.ctor
    have wildField : RuntimePPatTyping .wild .int [] [] := .wild
    exact RuntimePPatsTyping.cons (.hole .any)
      (RuntimePPatsTyping.cons wildField .nil)
  · exact ⟨.core (.checked (.something .int) (.matcherToSlot .equal))⟩
  · exact .cons
      (.mk RuntimeDPatTyping.var
        (.core (singletonDecompositionBody_typed [] .int))) .nil
  · intro dispatch inspected
    simp [constructorApplicationPattern, delegatedApplicationPattern,
      inspectPatternPattern, inspectPatternPatterns] at inspected
    subst dispatch
    exact .nil

theorem applicationFieldClauses_inputTyped :
    TotalRuntimeMatcherClausesInputTyping CoreExpressionTyping [] [] .int
      constructorApplicationPattern [applicationFieldClause] :=
  .cons applicationFieldClause_inputTyped .nil

theorem applicationField_dispatch_exact :
    dispatchMatcherClauses (evalFuel 4) [] [] [applicationFieldClause]
      constructorApplicationPattern (.int 31) =
        .ok (.hit [[⟨delegatedApplicationPattern, .something, .int 31⟩]]) := by
  with_unfolding_all rfl

theorem applicationField_dispatch_patternIndexed :
    PatternIndexedDelegatedMatchingBranchesTyping
      [delegatedApplicationPattern] [⟨.any, .int⟩]
      [[⟨delegatedApplicationPattern, .something, .int 31⟩]] := by
  exact .cons
    (.cons (.checked (.something .int) (.matcherToSlot .equal)) (.int 31) .nil)
    .nil

theorem applicationField_dispatch_patternIndexedSafe :
    ∃ patterns holes,
      PatternIndexedDelegatedMatchingBranchesTyping patterns holes
        [[⟨delegatedApplicationPattern, .something, .int 31⟩]] := by
  have safe := dispatchMatcherClauses_patternIndexedTotalTypedSafe
    (expressionTyping := CoreExpressionTyping) (eval := evalFuel 4)
    (atomEnvironment := []) (matcherEnvironment := [])
    (pattern := constructorApplicationPattern) (target := .int 31)
    (clauses := [applicationFieldClause])
    (evalFuel_totalCore_embeddedSafe 4) .nil .nil (.int 31)
    applicationFieldClauses_inputTyped
  rw [applicationField_dispatch_exact] at safe
  rcases safe with _ | ⟨result, equality, typed⟩
  · contradiction
  · cases equality
    cases typed with
    | hit indexed => exact ⟨_, _, indexed⟩

theorem delegatedApplication_checkedWork :
    CheckedScopedWorkTyping frozenIdentity.signature frozenIdentity.definitions
      [] []
      [.atom ⟨delegatedApplicationPattern, .something, .int 31⟩] [.int] := by
  unfold delegatedApplicationPattern
  apply CheckedScopedWorkTyping.applicationOfAgreement frozenIdentity.agreement
    frozenIdentity_lookup rfl
  · apply CheckedMNodeWorkTyping.parameter (index := 0) (argument := .var) rfl
    · exact .ordinary
        ⟨.builtin (.somethingVar (.int 31)), by intros; simp, by intros; simp⟩
        .nil
    · exact .nil
  · exact .nil

theorem delegatedApplication_patternIndexedChecked :
    PatternIndexedCheckedScopedAtomsTyping frozenIdentity.signature
      frozenIdentity.definitions [] []
      [⟨delegatedApplicationPattern, .something, .int 31⟩]
      [delegatedApplicationPattern] [⟨.any, .int⟩] [.int] := by
  apply PatternIndexedCheckedScopedAtomsTyping.application
    (hole := ⟨.any, .int⟩)
  · cases applicationField_dispatch_patternIndexed with
    | cons head tail => exact head
  · exact delegatedApplication_checkedWork

/-- The ordinary atom reached after parameter export uses the existing
callback-indexed recursive reducer theorem, in parallel with the `.app`
classification above. -/
theorem exportedVariable_recursiveReductionSafe :
    evaluationAtomReducer (evalFuel 4) [] ⟨.var, .something, .int 31⟩ =
        .timeout ∨
      ∃ reduction,
        evaluationAtomReducer (evalFuel 4) []
            ⟨.var, .something, .int 31⟩ = .ok (.hit reduction) ∧
        RecursiveTotalAtomReductionTyping CoreExpressionTyping (evalFuel 4)
          [] [] [.int] reduction := by
  exact evaluationAtomReducer_recursiveBuiltinTypedSafe
    (expressionTyping := CoreExpressionTyping) (eval := evalFuel 4)
    (evalFuel_totalCore_embeddedSafe 4) .nil .nil (.somethingVar (.int 31))

def applicationFieldSuccessfulDispatch :
    CheckedScopedSuccessfulUserDispatch frozenIdentity.signature
      frozenIdentity.definitions [] [] [.int] (evalFuel 4) [] []
      [applicationFieldClause] constructorApplicationPattern (.int 31) where
  branches := [[⟨delegatedApplicationPattern, .something, .int 31⟩]]
  success := applicationField_dispatch_exact
  patterns := [delegatedApplicationPattern]
  holes := [⟨.any, .int⟩]
  indexed := applicationField_dispatch_patternIndexed
  checked := by
    intro branch member indexed
    simp only [List.mem_singleton] at member
    subst branch
    exact delegatedApplication_patternIndexedChecked

theorem applicationField_reduction_patternIndexedChecked :
    evaluationAtomReducer (evalFuel 4) [] applicationFieldAtom =
        .ok (.hit ⟨[[⟨delegatedApplicationPattern, .something, .int 31⟩]], []⟩) ∧
      ∀ branch ∈
          [[⟨delegatedApplicationPattern, .something, .int 31⟩]],
        PatternIndexedCheckedScopedAtomsTyping frozenIdentity.signature
          frozenIdentity.definitions [] [] branch
          [delegatedApplicationPattern] [⟨.any, .int⟩] [.int] := by
  exact CheckedScopedSuccessfulUserDispatch.evaluationAtomReducer_exact
    (dispatch := applicationFieldSuccessfulDispatch) rfl

def applicationFieldInitialState : PatternFunctionState :=
  ⟨[.atom applicationFieldAtom], [], []⟩

theorem public_frozen_user_to_mnode_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenIdentity.definitions
        (evaluationAtomReducer (evalFuel 4)))
      8 [applicationFieldInitialState] = .ok [[.int 31]] := by
  rw [frozenIdentity_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_user_to_mnode_typed :
    TypedMatchingSearchResult [.int]
      (depthFirstFuel
        (stepPatternFunctionState frozenIdentity.definitions
          (evaluationAtomReducer (evalFuel 4)))
        8 [applicationFieldInitialState]) := by
  rw [public_frozen_user_to_mnode_exact]
  exact .inr ⟨[[.int 31]], rfl, by
    intro answer member
    simp only [List.mem_singleton] at member
    subst answer
    exact .cons (.int 31) .nil⟩

theorem public_frozen_user_to_mnode_neverStuck :
    (depthFirstFuel
      (stepPatternFunctionState frozenIdentity.definitions
        (evaluationAtomReducer (evalFuel 4)))
      8 [applicationFieldInitialState]).NotStuck := by
  rw [public_frozen_user_to_mnode_exact]
  trivial

theorem public_freeze_user_to_mnode_fixture :
    freezePatternFunctions Paper1Signature.signature
        Paper1Signature.wellFormed [identitySource] = some frozenIdentity ∧
      depthFirstFuel
        (stepPatternFunctionState frozenIdentity.definitions
          (evaluationAtomReducer (evalFuel 4)))
        8 [applicationFieldInitialState] = .ok [[.int 31]] :=
  ⟨public_identity_freeze_exact, public_frozen_user_to_mnode_exact⟩

end TypePM.Source.PatternIndexedRecursiveScopedSafetyRegression
