import TypePM.PatternFunctionPrivateBodyPlanAutomation
import TypePM.PatternFunctionSafetyRegression

/-!
# Private-binding body-plan regressions

The publicly frozen `privateExport` body first introduces an MNode-private
variable, uses it in a value pattern, and finally exports its actual argument.
The structural compiler tracks the private type while keeping the final outer
answer independent.  Separate leaf checks pin wildcard and disjunction
support; disjunction retains both concrete branch typings.
-/

namespace TypePM.PatternFunctionPrivateBodyPlanAutomationRegression

open Source Runtime
open Source.PatternFunctionFreeze
open PatternFunctionSafetyRegression

def privateExportName : PatternFunName := ⟨"privateExport"⟩

def privateExportBody : Pattern :=
  .and .var (.and (.value (.var 0)) (.embed 0))

def privateExportSource : PatternFunctionSourceDefinition :=
  { name := privateExportName
    scheme := identityScheme
    body := privateExportBody }

def privateExportGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := [.var ⟨0⟩]
    hard := [
      .ty (.var ⟨0⟩) .int,
      .cap (.var ⟨1⟩) .any,
      .ty (.var ⟨0⟩) (.var ⟨0⟩),
      .cap (.var ⟨0⟩) (.var ⟨1⟩)]
    pending := [] }

theorem privateExport_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          [privateExportSource]) []
        (identityScheme.instantiate ⟨0, 0⟩).1.fields privateExportBody []
        (identityScheme.instantiate ⟨0, 0⟩).2 =
      some (privateExportGenerated, ⟨1, 2⟩) := by
  simp [privateExportSource, privateExportBody, privateExportGenerated,
    identityScheme, elaboratePattern, Pattern.extendContext,
    Pattern.dualEquations, elaborate, Scheme.mono, Scheme.instantiate,
    DualScheme.instantiate, PolyDual.openBound,
    PolyCap.openBound, PolyTy.openBound, Scheme.boundTyInstance,
    Scheme.boundCapInstance]

theorem privateExport_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature
        [privateExportSource]) [privateExportSource] = true := by
  have blockSemantic :
      (resultCheckBlock privateExportGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          identitySolution := by
    constructor
    · simp [resultCheckBlock, privateExportGenerated, identityScheme,
        identitySolution, Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Ty.apply]
    · simp [resultCheckBlock, privateExportGenerated]
  have noPending :
      (resultCheckBlock privateExportGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result).pending = [] := rfl
  have accepts :=
    (Generated.blockAccepts_iff_exists_semanticSolution_of_pending_eq_nil
      (resultCheckBlock privateExportGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result) noPending).2
      ⟨identitySolution, blockSemantic⟩
  have succeeds := accepts.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases inferenceEq : inferGeneratedUsing unify
      (resultCheckBlock privateExportGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result) with
  | none => exact False.elim (succeeds inferenceEq)
  | some result =>
      simp only [privateExportSource, checkBodies, Bool.and_true]
      change (checkBody
        (PatternFunctionFreeze.signature Paper1Signature.signature
          [privateExportSource]) identityScheme privateExportBody).isSome = true
      simp only [checkBody]
      rw [privateExport_elaboration_exact]
      simp [inferenceEq]

set_option maxRecDepth 100000 in
theorem public_private_export_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [privateExportSource]).isSome = true := by
  have names :
      (([privateExportSource] : List PatternFunctionSourceDefinition).map
        PatternFunctionSourceDefinition.name).Nodup := by decide
  have closed : interfacesClosed [privateExportSource] = true := by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed,
    dif_pos privateExport_bodies_checked]
  rfl

def frozenPrivateExport : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed [privateExportSource]).get
      public_private_export_freeze_succeeds

theorem public_private_export_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [privateExportSource] =
        some frozenPrivateExport := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [privateExportSource] with
  | none =>
      have success := public_private_export_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenPrivateExport, frozenEq]

def privateExportDefinition : PatternFunctionDefinition :=
  { name := privateExportName
    parameterCount := 1
    body := privateExportBody }

theorem frozenPrivateExport_definitions_exact :
    frozenPrivateExport.definitions = [privateExportDefinition] := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenPrivateExport) public_private_export_freeze_exact
  simpa [PatternFunctionFreeze.definitions, privateExportSource,
    PatternFunctionSourceDefinition.runtimeDefinition,
    privateExportDefinition, identityScheme] using definitionsEq

theorem frozenPrivateExport_lookup :
    frozenPrivateExport.definitions.lookup privateExportName =
      some privateExportDefinition := by
  rw [frozenPrivateExport_definitions_exact]
  rfl

private def exportedVariable37 :
    CheckedScopedWorkTyping frozenPrivateExport.signature
      frozenPrivateExport.definitions [] []
      [.atom ⟨.var, .something, .int 37⟩] [.int] :=
  .ordinary
    (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 37))) .nil

def privateExportResolver :
    CheckedPrivateBodyResolver frozenPrivateExport.signature
      frozenPrivateExport.definitions [] [.var] where
  exports :=
    { resolve := fun outerBindingTypes index matcher target =>
        match outerBindingTypes, index, matcher, target with
        | [], 0, .something, .int 37 =>
            some ⟨[.int], CheckedBodyExecution.parameter rfl
              exportedVariable37⟩
        | _, _, _, _ => none }
  targets target :=
    match target with
    | .int 37 => some ⟨.int, .int 37⟩
    | _ => none
  ordinary privateEnvironmentTypes privateBindingTypes atom :=
    match privateEnvironmentTypes, privateBindingTypes, atom with
    | [], [.int], ⟨.value (.var 0), .something, .int 37⟩ =>
        some ⟨[], CheckedOrdinaryAtomTyping.ofBuiltin
          (.somethingValue (.var rfl) (.int 37))⟩
    | [], [], ⟨.or .var .var, .something, .int 37⟩ =>
        some ⟨[.int], CheckedOrdinaryAtomTyping.ofBuiltin
          (.or (.somethingVar (.int 37)) (.somethingVar (.int 37)))⟩
    | _, _, _ => none

def privateExportCompilation :=
  CheckedPrivateBodyExecution.compile privateExportResolver [] [] []
    ⟨privateExportDefinition.body, .something, .int 37⟩

theorem privateExportCompilation_isSome :
    privateExportCompilation.isSome = true := by
  simp [privateExportCompilation, CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateExportResolver,
    privateExportDefinition, privateExportBody]

def privateExportCompilationResult :=
  privateExportCompilation.get privateExportCompilation_isSome

theorem privateExportCompilation_outerTypes :
    privateExportCompilationResult.1 = [.int] := by
  simp [privateExportCompilationResult, privateExportCompilation,
    CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateExportResolver,
    privateExportDefinition, privateExportBody]

theorem privateExportCompilation_privateTypes :
    privateExportCompilationResult.2.1 = [.int] := by
  have projectedExact :
      privateExportCompilation.map (fun result => result.2.1) =
        some [.int] := by
    simp [privateExportCompilation,
      CheckedPrivateBodyExecution.compile,
      CheckedPrivateBodyExecution.compileFuel, privateExportResolver,
      privateExportDefinition, privateExportBody]
  have projectedSome :
      (privateExportCompilation.map (fun result => result.2.1)).isSome =
        true := by
    simp [projectedExact]
  have projectedGet :
      (privateExportCompilation.map (fun result => result.2.1)).get
        projectedSome = [.int] := by
    simp [projectedExact]
  simpa [privateExportCompilationResult, Option.get_map] using projectedGet

def privateExportBodyExecution :
    CheckedPrivateBodyExecution frozenPrivateExport.signature
      frozenPrivateExport.definitions [] [.var] [] [] []
      ⟨privateExportDefinition.body, .something, .int 37⟩ [.int] [.int] :=
  by
    have outerEq := privateExportCompilation_outerTypes
    have privateEq := privateExportCompilation_privateTypes
    generalize resultEq : privateExportCompilationResult = result at outerEq privateEq
    have execution := privateExportCompilationResult.2.2
    rw [resultEq] at execution
    rcases result with ⟨outerTypes, privateTypes, _⟩
    change outerTypes = [.int] at outerEq
    change privateTypes = [.int] at privateEq
    subst outerTypes
    subst privateTypes
    exact execution

def privateExportInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app privateExportName [.var], .something, .int 37⟩], [], []⟩

theorem privateExportInitialState_checked_automatic :
    CheckedScopedStateTyping frozenPrivateExport.signature
      frozenPrivateExport.definitions privateExportInitialState [.int] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfCheckedPrivateBodyExecution
    frozenPrivateExport.agreement frozenPrivateExport_lookup rfl
    privateExportBodyExecution .nil

/-! The reducer below keeps every successful built-in branch exact and turns
only a genuine built-in miss into timeout.  This makes its checked scoped
safety proof independent of user matcher dispatch. -/

def privateBuiltinReducer (environment : ValueEnvironment)
    (atom : MatchingAtom) : FuelResult (DispatchResult AtomReduction) :=
  match reduceBuiltinAtom (evalFuel 4) environment atom with
  | .ok .miss => .timeout
  | result => result

private theorem builtinReduction_checkedTyping
    (typing : AtomReductionTyping
      (fun context expression target => RuntimeTyping expression target context)
      environmentTypes bindingTypes expectedBindings reduction) :
    CheckedScopedAtomReductionTyping environmentTypes bindingTypes
      expectedBindings reduction := by
  cases typing with
  | intro immediateTypes immediateTyped branchesTyped =>
      exact .intro immediateTypes immediateTyped (by
        intro branch member
        obtain ⟨delayedTypes, branchTyped, equality⟩ :=
          branchesTyped branch member
        exact ⟨delayedTypes,
          CheckedOrdinaryAtomsTyping.ofBuiltin branchTyped, equality⟩)

theorem privateBuiltinReducer_checkedSafe :
    CheckedScopedAtomReducerTypedSafe privateBuiltinReducer := by
  intro environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  cases atomTyped.typed with
  | builtin typed =>
      have evalSafe : EmbeddedEvaluatorSafe
          (fun context expression target => RuntimeTyping expression target context)
          (evalFuel 4) := by
        intro context values expression target valuesTyped expressionTyped
        exact expressionTyped.coreSafety 4 values valuesTyped
      rcases reduceBuiltinAtom_typedSafe
          (fun context expression target => RuntimeTyping expression target context)
          (evalFuel 4) evalSafe environmentTyped bindingsTyped typed with
        timeout | ⟨reduction, success, reductionTyped⟩
      · exact .inl (by simp [privateBuiltinReducer, timeout])
      · exact .inr ⟨reduction, by simp [privateBuiltinReducer, success],
          builtinReduction_checkedTyping reductionTyped⟩
  | user builtinMiss matcherEnvironmentTyped targetTyped clausesTyped
      finalCatchAll branches =>
      exact .inl (by
        simp [privateBuiltinReducer,
          builtinMiss (evalFuel 4) (bindings ++ environment)])

theorem privateBuiltinReducer_structuralSafe :
    CheckedBodyReducerSafe privateBuiltinReducer := by
  intro environment atom atoms expansion
  cases expansion with
  | and => rfl
  | tuple zipped => simp [privateBuiltinReducer, reduceBuiltinAtom, zipped]

set_option maxRecDepth 100000 in
theorem public_frozen_private_export_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenPrivateExport.definitions
        privateBuiltinReducer)
      16 [privateExportInitialState] = .ok [[.int 37]] := by
  rw [frozenPrivateExport_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_private_export_typed (fuel : Nat) :
    TypedMatchingSearchResult [.int]
      (depthFirstFuel
        (stepPatternFunctionState frozenPrivateExport.definitions
          privateBuiltinReducer)
        fuel [privateExportInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    privateBuiltinReducer_checkedSafe privateBuiltinReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact privateExportInitialState_checked_automatic

theorem public_frozen_private_export_never_stuck (fuel : Nat) :
    (depthFirstFuel
      (stepPatternFunctionState frozenPrivateExport.definitions
        privateBuiltinReducer)
      fuel [privateExportInitialState]).NotStuck := by
  rcases public_frozen_private_export_typed fuel with timeout |
    ⟨answers, success, _answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

def privateWildcardCompilation :=
  CheckedPrivateBodyExecution.compile privateExportResolver [] [] []
    ⟨.wild, .something, .int 37⟩

theorem privateWildcardCompilation_isSome :
    privateWildcardCompilation.isSome = true := by
  simp [privateWildcardCompilation, CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateExportResolver]

/-- Both actual disjunction branches are present in the resolver certificate;
the compiler never accepts the erased fact that some branch was checked. -/
def privateOrCompilation :=
  CheckedPrivateBodyExecution.compile privateExportResolver [] [] []
    ⟨.or .var .var, .something, .int 37⟩

theorem privateOrCompilation_isSome : privateOrCompilation.isSome = true := by
  simp [privateOrCompilation, CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateExportResolver]

end TypePM.PatternFunctionPrivateBodyPlanAutomationRegression
