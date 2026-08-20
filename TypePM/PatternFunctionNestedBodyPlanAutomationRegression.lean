import TypePM.PatternFunctionNestedBodyPlanAutomation
import TypePM.PatternFunctionSafetyRegression

/-!
# Automatic nested-application body-plan regressions

The public two-definition freezes are reused unchanged.  The compiler
reconstructs the surrounding conjunction/tuple plan, while the resolver
supplies a checked execution certificate for each nested application leaf,
including its concrete parameter exports.
-/

namespace TypePM.PatternFunctionNestedBodyPlanAutomationRegression

open Source Runtime
open PatternFunctionSafetyRegression

private def exportedVariable23 :
    CheckedScopedWorkTyping frozenNested.signature frozenNested.definitions
      [] [] [.atom ⟨.var, .something, .int 23⟩] [.int] :=
  .ordinary
    (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 23))) .nil

def nestedIdentityExecution :
    CheckedBodyResolvedApplication frozenNested.signature
      frozenNested.definitions [] [.var] [] identityName [.embed 0]
      .something (.int 23) where
  definition := identityDefinition
  found := frozenNested_identity_lookup
  checked := frozenNested.agreement.lookup_checked frozenNested_identity_lookup
  arity := rfl
  answerTypes := [.int]
  execution := CheckedBodyExecution.applicationParameter
    frozenNested_identity_lookup
    (frozenNested.agreement.lookup_checked frozenNested_identity_lookup)
    rfl rfl rfl rfl exportedVariable23

def nestedCallerResolver :
    CheckedNestedBodyResolver frozenNested.signature frozenNested.definitions
      [] [.var] where
  exports :=
    { resolve := fun outerBindingTypes index matcher target =>
        match outerBindingTypes, index, matcher, target with
        | [], 0, .something, .int 23 =>
            some ⟨[.int], CheckedBodyExecution.parameter rfl
              exportedVariable23⟩
        | _, _, _, _ => none }
  applications outerBindingTypes name nestedArguments matcher target :=
    match outerBindingTypes, name, nestedArguments, matcher, target with
    | [], ⟨"identity"⟩, [.embed 0], .something, .int 23 =>
        some nestedIdentityExecution
    | _, _, _, _, _ => none

def nestedCallerCompilation :=
  CheckedBodyExecution.compileNested nestedCallerResolver []
    ⟨callerDefinition.body, .something, .int 23⟩

theorem nestedCallerCompilation_isSome :
    nestedCallerCompilation.isSome = true := by
  simp [nestedCallerCompilation, CheckedBodyExecution.compileNested,
    CheckedBodyExecution.compileNestedFuel, nestedCallerResolver,
    callerDefinition, identityName]

def nestedCallerCompilationResult :=
  nestedCallerCompilation.get nestedCallerCompilation_isSome

theorem nestedCallerCompilation_answerTypes :
    nestedCallerCompilationResult.1 = [.int] := by
  simp [nestedCallerCompilationResult, nestedCallerCompilation,
    CheckedBodyExecution.compileNested,
    CheckedBodyExecution.compileNestedFuel, nestedCallerResolver,
    nestedIdentityExecution, callerDefinition, identityName]

def nestedCallerBodyExecution :
    CheckedBodyExecution frozenNested.signature frozenNested.definitions
      [] [.var] [] ⟨callerDefinition.body, .something, .int 23⟩ [.int] :=
  nestedCallerCompilation_answerTypes ▸ nestedCallerCompilationResult.2

theorem nestedInitialState_checked_automatic :
    CheckedScopedStateTyping frozenNested.signature frozenNested.definitions
      nestedInitialState [.int] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfCheckedBodyExecution
    frozenNested.agreement frozenNested_caller_lookup rfl
    nestedCallerBodyExecution .nil

theorem public_frozen_nested_automatic_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenNested.definitions variableOnlyReducer)
      12 [nestedInitialState] = .ok [[.int 23]] :=
  public_frozen_nested_scoped_dfs_exact

theorem public_frozen_nested_automatic_typed :
    TypedMatchingSearchResult [.int]
      (depthFirstFuel
        (stepPatternFunctionState frozenNested.definitions variableOnlyReducer)
        12 [nestedInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    variableOnlyReducer_checkedSafe variableOnlyReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact nestedInitialState_checked_automatic

theorem public_frozen_nested_automatic_never_stuck :
    (depthFirstFuel
      (stepPatternFunctionState frozenNested.definitions variableOnlyReducer)
      12 [nestedInitialState]).NotStuck := by
  rw [public_frozen_nested_automatic_exact]
  trivial

/-! ## Two parameters threaded through a nested checked conjunction -/

private def exportedVariable31 :
    CheckedScopedWorkTyping frozenCompound.signature frozenCompound.definitions
      [] [] [.atom ⟨.var, .something, .int 31⟩] [.int] :=
  .ordinary
    (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 31))) .nil

private def exportedWildcard31 :
    CheckedScopedWorkTyping frozenCompound.signature frozenCompound.definitions
      [] [.int] [.atom ⟨.wild, .something, .int 31⟩] [.int] :=
  .ordinary
    (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingWild (.int 31))) .nil

def nestedConjoinExecution :
    CheckedBodyResolvedApplication frozenCompound.signature
      frozenCompound.definitions [] [.var, .wild] [] conjoinName
      [.embed 0, .embed 1] .something (.int 31) where
  definition := conjoinDefinition
  found := frozenCompound_conjoin_lookup
  checked := frozenCompound.agreement.lookup_checked frozenCompound_conjoin_lookup
  arity := rfl
  answerTypes := [.int]
  execution := CheckedBodyExecution.applicationAndParameters
    frozenCompound_conjoin_lookup
    (frozenCompound.agreement.lookup_checked frozenCompound_conjoin_lookup)
    rfl rfl rfl rfl rfl rfl rfl exportedVariable31 exportedWildcard31

def binaryCallerResolver :
    CheckedNestedBodyResolver frozenCompound.signature
      frozenCompound.definitions [] [.var, .wild] where
  exports :=
    { resolve := fun outerBindingTypes index matcher target =>
        match outerBindingTypes, index, matcher, target with
        | [], 0, .something, .int 31 =>
            some ⟨[.int], CheckedBodyExecution.parameter rfl
              exportedVariable31⟩
        | [.int], 1, .something, .int 31 =>
            some ⟨[.int], CheckedBodyExecution.parameter rfl
              exportedWildcard31⟩
        | _, _, _, _ => none }
  applications outerBindingTypes name nestedArguments matcher target :=
    match outerBindingTypes, name, nestedArguments, matcher, target with
    | [], ⟨"conjoin"⟩, [.embed 0, .embed 1], .something, .int 31 =>
        some nestedConjoinExecution
    | _, _, _, _, _ => none

def binaryCallerCompilation :=
  CheckedBodyExecution.compileNested binaryCallerResolver []
    ⟨binaryCallerDefinition.body, .something, .int 31⟩

theorem binaryCallerCompilation_isSome :
    binaryCallerCompilation.isSome = true := by
  simp [binaryCallerCompilation, CheckedBodyExecution.compileNested,
    CheckedBodyExecution.compileNestedFuel, binaryCallerResolver,
    binaryCallerDefinition, conjoinName]

def binaryCallerCompilationResult :=
  binaryCallerCompilation.get binaryCallerCompilation_isSome

theorem binaryCallerCompilation_answerTypes :
    binaryCallerCompilationResult.1 = [.int] := by
  simp [binaryCallerCompilationResult, binaryCallerCompilation,
    CheckedBodyExecution.compileNested,
    CheckedBodyExecution.compileNestedFuel, binaryCallerResolver,
    nestedConjoinExecution, binaryCallerDefinition, conjoinName]

def binaryCallerBodyExecution :
    CheckedBodyExecution frozenCompound.signature frozenCompound.definitions
      [] [.var, .wild] []
      ⟨binaryCallerDefinition.body, .something, .int 31⟩ [.int] :=
  binaryCallerCompilation_answerTypes ▸ binaryCallerCompilationResult.2

def binaryCallerInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app binaryCallerName [.var, .wild], .something, .int 31⟩],
    [], []⟩

theorem binaryCallerInitialState_checked_automatic :
    CheckedScopedStateTyping frozenCompound.signature frozenCompound.definitions
      binaryCallerInitialState [.int] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfCheckedBodyExecution
    frozenCompound.agreement frozenCompound_caller_lookup rfl
    binaryCallerBodyExecution .nil

set_option maxRecDepth 100000 in
theorem public_frozen_binary_caller_automatic_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenCompound.definitions variableOnlyReducer)
      20 [binaryCallerInitialState] = .ok [[.int 31]] := by
  rw [frozenCompound_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_binary_caller_automatic_typed :
    TypedMatchingSearchResult [.int]
      (depthFirstFuel
        (stepPatternFunctionState frozenCompound.definitions variableOnlyReducer)
        20 [binaryCallerInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    variableOnlyReducer_checkedSafe variableOnlyReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact binaryCallerInitialState_checked_automatic

theorem public_frozen_binary_caller_automatic_never_stuck :
    (depthFirstFuel
      (stepPatternFunctionState frozenCompound.definitions variableOnlyReducer)
      20 [binaryCallerInitialState]).NotStuck := by
  rw [public_frozen_binary_caller_automatic_exact]
  trivial

end TypePM.PatternFunctionNestedBodyPlanAutomationRegression
