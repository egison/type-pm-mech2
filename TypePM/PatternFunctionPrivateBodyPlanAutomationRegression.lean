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
  constructors _ _ _ _ _ _ := none
  applications _ _ _ _ _ := none

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

/-! ## A private binding followed by a nested checked application

This fixture exercises the combined compiler boundary directly.  The first
child adds an MNode-private binding.  The second child calls the separately
checked public `identity` pattern function and exports its actual argument to
the outer frame.  The nested application's proof is universally quantified
over the private continuation frame, so it preserves the first child's
private binding rather than forgetting or retyping it. -/

def privateNestedName : PatternFunName := ⟨"privateNested"⟩

def privateNestedBody : Pattern :=
  .and .var (.app identityName [.embed 0])

def privateNestedSource : PatternFunctionSourceDefinition :=
  { name := privateNestedName
    scheme := identityScheme
    body := privateNestedBody }

def privateNestedSources : List PatternFunctionSourceDefinition :=
  [identitySource, privateNestedSource]

def privateNestedGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := [.var ⟨0⟩]
    hard := [
      .ty .int .int,
      .cap .any .any,
      .ty (.var ⟨0⟩) .int,
      .cap (.var ⟨0⟩) .any]
    pending := [] }

theorem privateNested_identity_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          privateNestedSources) []
        (identityScheme.instantiate ⟨0, 0⟩).1.fields (.embed 0) []
        (identityScheme.instantiate ⟨0, 0⟩).2 =
      some (identityGenerated, ⟨0, 0⟩) := by
  simp [privateNestedSources, privateNestedSource, privateNestedBody,
    identitySource, identityScheme, identityGenerated, elaboratePattern,
    PatternFunctionFreeze.signature,
    PatternFunctionSourceDefinition.declaration, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound, PolyTy.openBound,
    Scheme.boundTyInstance, Scheme.boundCapInstance]

theorem privateNested_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          privateNestedSources) []
        (identityScheme.instantiate ⟨0, 0⟩).1.fields privateNestedBody []
        (identityScheme.instantiate ⟨0, 0⟩).2 =
      some (privateNestedGenerated, ⟨1, 1⟩) := by
  simp [privateNestedSources, privateNestedSource, privateNestedBody,
    identitySource, identityScheme, identityName, privateNestedName,
    privateNestedGenerated, elaboratePattern, elaboratePatterns,
    Pattern.dualEquations,
    PatternFunctionFreeze.signature,
    FrozenSignature.lookupPatternFunction,
    PatternFunctionSourceDefinition.declaration, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound, PolyTy.openBound,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    Pattern.fieldEquations]

private theorem checkedBody_isSome_of_semantic
    {frozen : FrozenSignature}
    (elaboration : elaboratePattern frozen []
        (scheme.instantiate ⟨0, 0⟩).1.fields body []
        (scheme.instantiate ⟨0, 0⟩).2 = some (generated, next))
    (noPending : (resultCheckBlock generated
      (scheme.instantiate ⟨0, 0⟩).1.result).pending = [])
    (semantic : (resultCheckBlock generated
      (scheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution solution) :
    (checkBody frozen scheme body).isSome = true := by
  have accepts :=
    (Generated.blockAccepts_iff_exists_semanticSolution_of_pending_eq_nil
      (resultCheckBlock generated
        (scheme.instantiate ⟨0, 0⟩).1.result) noPending).2
      ⟨solution, semantic⟩
  have succeeds := accepts.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases inferenceEq : inferGeneratedUsing unify
      (resultCheckBlock generated
        (scheme.instantiate ⟨0, 0⟩).1.result) with
  | none => exact False.elim (succeeds inferenceEq)
  | some result => simp [checkBody, elaboration, inferenceEq]

theorem privateNested_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature
        privateNestedSources) privateNestedSources = true := by
  have identitySemantic :
      (resultCheckBlock identityGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          identitySolution := by
    constructor <;>
      simp [resultCheckBlock, identityGenerated, identityScheme,
        identitySolution, Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Ty.apply]
  have privateNestedSemantic :
      (resultCheckBlock privateNestedGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          identitySolution := by
    constructor <;>
      simp [resultCheckBlock, privateNestedGenerated, identityScheme,
        identitySolution, Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Ty.apply]
  have identityChecked := checkedBody_isSome_of_semantic
    privateNested_identity_elaboration_exact (solution := identitySolution)
    (by rfl) identitySemantic
  have privateNestedChecked := checkedBody_isSome_of_semantic
    privateNested_elaboration_exact (solution := identitySolution)
    (by rfl) privateNestedSemantic
  simpa [privateNestedSources, identitySource, privateNestedSource,
    privateNestedBody, identityScheme, checkBodies] using
      And.intro identityChecked privateNestedChecked

set_option maxRecDepth 100000 in
theorem public_private_nested_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed privateNestedSources).isSome = true := by
  have names :
      (privateNestedSources.map
        PatternFunctionSourceDefinition.name).Nodup := by decide
  have closed : interfacesClosed privateNestedSources = true := by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed,
    dif_pos privateNested_bodies_checked]
  rfl

def frozenPrivateNested : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed privateNestedSources).get
      public_private_nested_freeze_succeeds

theorem public_private_nested_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed privateNestedSources =
        some frozenPrivateNested := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed privateNestedSources with
  | none =>
      have success := public_private_nested_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenPrivateNested, frozenEq]

def privateNestedDefinition : PatternFunctionDefinition :=
  { name := privateNestedName
    parameterCount := 1
    body := privateNestedBody }

theorem frozenPrivateNested_definitions_exact :
    frozenPrivateNested.definitions =
      [identityDefinition, privateNestedDefinition] := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenPrivateNested) public_private_nested_freeze_exact
  simpa [PatternFunctionFreeze.definitions, privateNestedSources,
    identitySource, privateNestedSource,
    PatternFunctionSourceDefinition.runtimeDefinition,
    identityDefinition, privateNestedDefinition, privateNestedBody,
    identityScheme] using definitionsEq

theorem frozenPrivateNested_identity_lookup :
    frozenPrivateNested.definitions.lookup identityName =
      some identityDefinition := by
  rw [frozenPrivateNested_definitions_exact]
  rfl

theorem frozenPrivateNested_lookup :
    frozenPrivateNested.definitions.lookup privateNestedName =
      some privateNestedDefinition := by
  rw [frozenPrivateNested_definitions_exact]
  rfl

private def privateNestedExportedVariable43 :
    CheckedScopedWorkTyping frozenPrivateNested.signature
      frozenPrivateNested.definitions [] []
      [.atom ⟨.var, .something, .int 43⟩] [.int] :=
  .ordinary
    (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 43))) .nil

def privateNestedIdentityExecution :
    CheckedBodyResolvedApplication frozenPrivateNested.signature
      frozenPrivateNested.definitions [] [.var] [] identityName [.embed 0]
      .something (.int 43) where
  definition := identityDefinition
  found := frozenPrivateNested_identity_lookup
  checked := frozenPrivateNested.agreement.lookup_checked
    frozenPrivateNested_identity_lookup
  arity := rfl
  answerTypes := [.int]
  execution := CheckedBodyExecution.applicationParameter
    frozenPrivateNested_identity_lookup
    (frozenPrivateNested.agreement.lookup_checked
      frozenPrivateNested_identity_lookup)
    rfl rfl rfl rfl privateNestedExportedVariable43

def privateNestedResolver :
    CheckedPrivateBodyResolver frozenPrivateNested.signature
      frozenPrivateNested.definitions [] [.var] where
  exports :=
    { resolve := fun outerBindingTypes index matcher target =>
        match outerBindingTypes, index, matcher, target with
        | [], 0, .something, .int 43 =>
            some ⟨[.int], CheckedBodyExecution.parameter rfl
              privateNestedExportedVariable43⟩
        | _, _, _, _ => none }
  targets target :=
    match target with
    | .int 43 => some ⟨.int, .int 43⟩
    | _ => none
  ordinary _ _ _ := none
  constructors _ _ _ _ _ _ := none
  applications outerBindingTypes name nestedArguments matcher target :=
    match outerBindingTypes, name, nestedArguments, matcher, target with
    | [], ⟨"identity"⟩, [.embed 0], .something, .int 43 =>
        some privateNestedIdentityExecution
    | _, _, _, _, _ => none

def privateNestedCompilation :=
  CheckedPrivateBodyExecution.compile privateNestedResolver [] [] []
    ⟨privateNestedDefinition.body, .something, .int 43⟩

theorem privateNestedCompilation_isSome :
    privateNestedCompilation.isSome = true := by
  simp [privateNestedCompilation, CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateNestedResolver,
    privateNestedDefinition, privateNestedBody, identityName]

def privateNestedCompilationResult :=
  privateNestedCompilation.get privateNestedCompilation_isSome

theorem privateNestedCompilation_outerTypes :
    privateNestedCompilationResult.1 = [.int] := by
  simp [privateNestedCompilationResult, privateNestedCompilation,
    CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateNestedResolver,
    privateNestedIdentityExecution, privateNestedDefinition,
    privateNestedBody, identityName]

theorem privateNestedCompilation_privateTypes :
    privateNestedCompilationResult.2.1 = [.int] := by
  have projectedExact :
      privateNestedCompilation.map (fun result => result.2.1) =
        some [.int] := by
    simp [privateNestedCompilation, CheckedPrivateBodyExecution.compile,
      CheckedPrivateBodyExecution.compileFuel, privateNestedResolver,
      privateNestedIdentityExecution, privateNestedDefinition,
      privateNestedBody, identityName]
  have projectedSome :
      (privateNestedCompilation.map (fun result => result.2.1)).isSome =
        true := by simp [projectedExact]
  have projectedGet :
      (privateNestedCompilation.map (fun result => result.2.1)).get
        projectedSome = [.int] := by simp [projectedExact]
  simpa [privateNestedCompilationResult, Option.get_map] using projectedGet

def privateNestedBodyExecution :
    CheckedPrivateBodyExecution frozenPrivateNested.signature
      frozenPrivateNested.definitions [] [.var] [] [] []
      ⟨privateNestedDefinition.body, .something, .int 43⟩ [.int] [.int] := by
  have outerEq := privateNestedCompilation_outerTypes
  have privateEq := privateNestedCompilation_privateTypes
  generalize resultEq : privateNestedCompilationResult = result at outerEq privateEq
  have execution := privateNestedCompilationResult.2.2
  rw [resultEq] at execution
  rcases result with ⟨outerTypes, privateTypes, _⟩
  change outerTypes = [.int] at outerEq
  change privateTypes = [.int] at privateEq
  subst outerTypes
  subst privateTypes
  exact execution

def privateNestedInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app privateNestedName [.var], .something, .int 43⟩], [], []⟩

theorem privateNestedInitialState_checked_automatic :
    CheckedScopedStateTyping frozenPrivateNested.signature
      frozenPrivateNested.definitions privateNestedInitialState [.int] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfCheckedPrivateBodyExecution
    frozenPrivateNested.agreement frozenPrivateNested_lookup rfl
    privateNestedBodyExecution .nil

set_option maxRecDepth 100000 in
theorem public_frozen_private_nested_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenPrivateNested.definitions
        privateBuiltinReducer)
      20 [privateNestedInitialState] = .ok [[.int 43]] := by
  rw [frozenPrivateNested_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_private_nested_typed (fuel : Nat) :
    TypedMatchingSearchResult [.int]
      (depthFirstFuel
        (stepPatternFunctionState frozenPrivateNested.definitions
          privateBuiltinReducer)
        fuel [privateNestedInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    privateBuiltinReducer_checkedSafe privateBuiltinReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact privateNestedInitialState_checked_automatic

theorem public_frozen_private_nested_never_stuck (fuel : Nat) :
    (depthFirstFuel
      (stepPatternFunctionState frozenPrivateNested.definitions
        privateBuiltinReducer)
      fuel [privateNestedInitialState]).NotStuck := by
  rcases public_frozen_private_nested_typed fuel with timeout |
    ⟨answers, success, _answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-! ## Proof-bearing constructor mismatch

This smallest constructor fixture is deliberately a normal match failure.
The actual final-catch-all matcher returns zero decompositions for the `nil`
constructor pattern.  The resolver carries that exact user-atom certificate;
it does not infer constructor semantics from an erased matcher value. -/

def privateConstructorName : PatternFunName := ⟨"privateConstructor"⟩

def privateConstructorScheme : DualScheme :=
  { tyArity := 0
    capArity := 0
    fields := []
    result := ⟨.con PatternFormer.list [.any], PolyDataTypes.list .int⟩
    fieldsWellScoped := by simp
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped,
        PolyDataTypes.list] }

def privateConstructorBody : Pattern :=
  .ctor PatternCtor.nil []

def privateConstructorSource : PatternFunctionSourceDefinition :=
  { name := privateConstructorName
    scheme := privateConstructorScheme
    body := privateConstructorBody }

def privateConstructorGenerated : GeneratedPattern :=
  { dual := ⟨.con PatternFormer.list [.var ⟨0⟩],
      DataTypes.list (.var ⟨0⟩)⟩
    bindings := []
    hard := []
    pending := [] }

def privateConstructorSolution : Subst :=
  { ty := fun _ => .int
    cap := fun _ => .any }

theorem privateConstructor_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          [privateConstructorSource]) [] [] privateConstructorBody []
        (privateConstructorScheme.instantiate ⟨0, 0⟩).2 =
      some (privateConstructorGenerated, ⟨1, 1⟩) := by
  simp [privateConstructorSource, privateConstructorScheme,
    privateConstructorBody, privateConstructorGenerated, elaboratePattern,
    elaboratePatterns, Pattern.fieldEquations,
    PatternFunctionFreeze.signature, FrozenSignature.lookupPatternConstructor,
    PatternFunctionSourceDefinition.declaration, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound, PolyCap.openBoundList,
    PolyTy.openBound, PolyTy.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list,
    ListPatternSchemes.nil]

theorem privateConstructor_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature
        [privateConstructorSource]) [privateConstructorSource] = true := by
  have semantic :
      (resultCheckBlock privateConstructorGenerated
        (privateConstructorScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          privateConstructorSolution := by
    constructor <;>
      simp [resultCheckBlock, privateConstructorGenerated,
        privateConstructorScheme, privateConstructorSolution,
        Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyCap.openBoundList, PolyTy.openBound, PolyTy.openBoundList,
        Scheme.boundTyInstance, Scheme.boundCapInstance, Cap.apply,
        Cap.applyList, Ty.apply, Ty.applyList, PolyDataTypes.list,
        DataTypes.list]
  have checked := checkedBody_isSome_of_semantic
    privateConstructor_elaboration_exact (solution := privateConstructorSolution)
    (by rfl) semantic
  simpa [privateConstructorSource, privateConstructorScheme,
    privateConstructorBody, checkBodies] using checked

set_option maxRecDepth 100000 in
theorem public_private_constructor_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [privateConstructorSource]).isSome = true := by
  have names :
      (([privateConstructorSource] : List PatternFunctionSourceDefinition).map
        PatternFunctionSourceDefinition.name).Nodup := by decide
  have closed : interfacesClosed [privateConstructorSource] = true := by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed,
    dif_pos privateConstructor_bodies_checked]
  rfl

def frozenPrivateConstructor : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed [privateConstructorSource]).get
      public_private_constructor_freeze_succeeds

theorem public_private_constructor_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [privateConstructorSource] =
        some frozenPrivateConstructor := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [privateConstructorSource] with
  | none =>
      have success := public_private_constructor_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenPrivateConstructor, frozenEq]

def privateConstructorDefinition : PatternFunctionDefinition :=
  { name := privateConstructorName
    parameterCount := 0
    body := privateConstructorBody }

theorem frozenPrivateConstructor_definitions_exact :
    frozenPrivateConstructor.definitions = [privateConstructorDefinition] := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenPrivateConstructor)
    public_private_constructor_freeze_exact
  simpa [PatternFunctionFreeze.definitions, privateConstructorSource,
    PatternFunctionSourceDefinition.runtimeDefinition,
    privateConstructorDefinition, privateConstructorScheme] using definitionsEq

theorem frozenPrivateConstructor_lookup :
    frozenPrivateConstructor.definitions.lookup privateConstructorName =
      some privateConstructorDefinition := by
  rw [frozenPrivateConstructor_definitions_exact]
  rfl

def constructorMissClause : MatcherClause :=
  .mk .hole .something [.mk .var (.ctor DataCtor.nil [])]

def constructorMissMatcher : Value :=
  .matcherV [] [constructorMissClause] [constructorMissClause]

def constructorTarget : Value := Value.nilValue

private theorem constructorMissClause_inputTyped :
    RuntimeMatcherClauseInputTyping [] []
      (DataTypes.list .int) (.ctor PatternCtor.nil [])
      constructorMissClause := by
  apply RuntimeMatcherClauseInputTyping.mk
      (holes := [⟨.any, DataTypes.list .int⟩]) (captureTypes := [])
  · exact .hole .any
  · exact .one (.checked (.something (DataTypes.list .int))
      (.matcherToSlot .equal))
  · exact .cons (.mk .var (.listNil (DataTypes.list .int))) .nil
  · intro dispatch inspected
    simp [inspectPatternPattern] at inspected
    subst dispatch
    exact .nil

private theorem constructorMissClauses_inputTyped :
    RuntimeMatcherClausesInputTyping [] []
      (DataTypes.list .int) (.ctor PatternCtor.nil [])
      [constructorMissClause] :=
  .cons constructorMissClause_inputTyped .nil

private theorem constructorMiss_dispatches_noBranches
    (success : dispatchMatcherClauses (evalFuel fuel) atomEnvironment []
      [constructorMissClause] (.ctor PatternCtor.nil []) constructorTarget =
        .ok (.hit branches)) :
    branches = [] := by
  cases fuel with
  | zero =>
      simp [dispatchMatcherClauses, firstHit, tryMatcherClause,
        inspectPatternPattern, FuelResult.traverse, tryMatcherArm,
        matchValueDataPattern, evalFuel, constructorMissClause,
        constructorTarget] at success
  | succ fuel =>
      simpa [dispatchMatcherClauses, firstHit, tryMatcherClause,
        inspectPatternPattern, FuelResult.traverse, tryMatcherArm,
        matchValueDataPattern, evalFuel, constructorMissClause,
        constructorTarget, Value.nilValue, Value.viewList,
        decodeDecompositions, closeMatcherArmsResult, buildMatchingBranches,
        zipMatchingAtoms,
        FuelResult.bind, FuelResult.map] using success

private def constructorOrdinaryLeaf (original : List MatcherClause) :
    CheckedPrivateBodyOrdinaryLeaf [] []
      ⟨.ctor PatternCtor.nil [],
        .matcherV [] original [constructorMissClause], constructorTarget⟩ where
  newPrivateBindings := []
  typed :=
    { typed := .user
        (by intro eval environment; rfl)
        .nil
        (.list .nil)
        constructorMissClauses_inputTyped
        .last
        (by
          intro fuel atomEnvironment holes branches dispatched
            branchesTyped branch member
          have empty := constructorMiss_dispatches_noBranches dispatched
          subst branches
          simp at member)
      notApplication := by intro name arguments equality; simp at equality
      notParameter := by intro index equality; simp at equality }

def privateConstructorResolver :
    CheckedPrivateBodyResolver frozenPrivateConstructor.signature
      frozenPrivateConstructor.definitions [] [] where
  exports := { resolve := fun _ _ _ _ => none }
  targets target :=
    match target with
    | .data ⟨"nil"⟩ [] =>
        some ⟨DataTypes.list .int, .list .nil⟩
    | _ => none
  ordinary _ _ _ := none
  constructors privateEnvironmentTypes privateBindingTypes constructor fields
      matcher target :=
    match privateEnvironmentTypes, privateBindingTypes, constructor, fields,
        matcher, target with
    | [], [], ⟨"nil"⟩, [],
        .matcherV [] original
          [⟨.hole, .something, [⟨.var, .ctor ⟨"nil"⟩ []⟩]⟩],
        .data ⟨"nil"⟩ [] => some (constructorOrdinaryLeaf original)
    | _, _, _, _, _, _ => none
  applications _ _ _ _ _ := none

def privateConstructorCompilation :=
  CheckedPrivateBodyExecution.compile privateConstructorResolver [] [] []
    ⟨privateConstructorDefinition.body, constructorMissMatcher,
      constructorTarget⟩

private theorem privateConstructorResolver_exact :
    privateConstructorResolver.constructors [] []
      PatternCtor.nil [] constructorMissMatcher constructorTarget =
        some (constructorOrdinaryLeaf [constructorMissClause]) := by
  rfl

private theorem privateConstructorTargetResolver_exact :
    privateConstructorResolver.targets constructorTarget =
      some ⟨DataTypes.list .int, .list .nil⟩ := by
  rfl

/-- The constructor certificate concerns only the MNode-private frame; a
nonempty outer frame passes through the compiler unchanged. -/
def privateConstructorOuterCompilation :=
  CheckedPrivateBodyExecution.compile privateConstructorResolver [.int] [] []
    ⟨privateConstructorDefinition.body, constructorMissMatcher,
      constructorTarget⟩

theorem privateConstructorOuterCompilation_frames :
    privateConstructorOuterCompilation.map
        (fun result => (result.1, result.2.1)) = some ([.int], []) := by
  simp [privateConstructorOuterCompilation,
    CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateConstructorResolver,
    privateConstructorDefinition, privateConstructorBody,
    constructorMissMatcher, constructorMissClause, constructorOrdinaryLeaf,
    constructorTarget, Value.nilValue, PatternCtor.nil, DataCtor.nil]

theorem privateConstructorCompilation_isSome :
    privateConstructorCompilation.isSome = true := by
  simp [privateConstructorCompilation, CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateConstructorResolver,
    privateConstructorDefinition, privateConstructorBody,
    constructorMissMatcher, constructorMissClause, constructorTarget,
    Value.nilValue, PatternCtor.nil, DataCtor.nil]

def privateConstructorCompilationResult :=
  privateConstructorCompilation.get privateConstructorCompilation_isSome

theorem privateConstructorCompilation_outerTypes :
    privateConstructorCompilationResult.1 = [] := by
  simp [privateConstructorCompilationResult, privateConstructorCompilation,
    CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel, privateConstructorResolver,
    privateConstructorDefinition, privateConstructorBody,
    constructorMissMatcher, constructorMissClause, constructorTarget,
    Value.nilValue, PatternCtor.nil, DataCtor.nil]

theorem privateConstructorCompilation_privateTypes :
    privateConstructorCompilationResult.2.1 = [] := by
  have projectedExact :
      privateConstructorCompilation.map (fun result => result.2.1) =
        some [] := by
    simp [privateConstructorCompilation,
      CheckedPrivateBodyExecution.compile,
      CheckedPrivateBodyExecution.compileFuel, privateConstructorResolver,
      privateConstructorDefinition, privateConstructorBody,
      constructorMissMatcher, constructorMissClause, constructorOrdinaryLeaf,
      constructorTarget,
      Value.nilValue, PatternCtor.nil, DataCtor.nil]
  have projectedSome :
      (privateConstructorCompilation.map (fun result => result.2.1)).isSome =
        true := by simp [projectedExact]
  have projectedGet :
      (privateConstructorCompilation.map (fun result => result.2.1)).get
        projectedSome = [] := by simp [projectedExact]
  simpa [privateConstructorCompilationResult, Option.get_map] using projectedGet

def privateConstructorBodyExecution :
    CheckedPrivateBodyExecution frozenPrivateConstructor.signature
      frozenPrivateConstructor.definitions [] [] [] [] []
      ⟨privateConstructorDefinition.body, constructorMissMatcher,
        constructorTarget⟩ [] [] := by
  have outerEq := privateConstructorCompilation_outerTypes
  have privateEq := privateConstructorCompilation_privateTypes
  generalize resultEq : privateConstructorCompilationResult = result at outerEq privateEq
  have execution := privateConstructorCompilationResult.2.2
  rw [resultEq] at execution
  rcases result with ⟨outerTypes, privateTypes, _⟩
  change outerTypes = [] at outerEq
  change privateTypes = [] at privateEq
  subst outerTypes
  subst privateTypes
  exact execution

def privateConstructorInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app privateConstructorName [], constructorMissMatcher,
    constructorTarget⟩], [], []⟩

theorem privateConstructorInitialState_checked_automatic :
    CheckedScopedStateTyping frozenPrivateConstructor.signature
      frozenPrivateConstructor.definitions privateConstructorInitialState [] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfCheckedPrivateBodyExecution
    frozenPrivateConstructor.agreement frozenPrivateConstructor_lookup rfl
    privateConstructorBodyExecution .nil

/-- Constructor atoms are closed as an ordinary mismatch; every other atom
uses the existing built-in-only reducer. -/
def constructorMismatchReducer (environment : ValueEnvironment)
    (atom : MatchingAtom) : FuelResult (DispatchResult AtomReduction) :=
  match atom.pattern with
  | .ctor _ _ => .ok (.hit .failure)
  | _ => privateBuiltinReducer environment atom

theorem constructorMismatchReducer_checkedSafe :
    CheckedScopedAtomReducerTypedSafe constructorMismatchReducer := by
  intro environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern <;>
    try simpa [constructorMismatchReducer] using
      (privateBuiltinReducer_checkedSafe environmentTyped bindingsTyped atomTyped)
  case ctor constructor fields =>
    exact .inr ⟨.failure, rfl, .intro [] .nil (by
      intro branch member
      simp [AtomReduction.failure] at member)⟩

theorem constructorMismatchReducer_structuralSafe :
    CheckedBodyReducerSafe constructorMismatchReducer := by
  intro environment atom atoms expansion
  cases expansion with
  | and => rfl
  | tuple zipped =>
      simp [constructorMismatchReducer, privateBuiltinReducer,
        reduceBuiltinAtom, zipped]

/-- On the concrete constructor atom, the small reducer agrees with the
actual final-catch-all matcher dispatch rather than inventing a success. -/
theorem constructorMismatchReducer_agrees_with_actual_dispatch :
    constructorMismatchReducer []
        ⟨.ctor PatternCtor.nil [], constructorMissMatcher, constructorTarget⟩ =
      evaluationAtomReducer (evalFuel 4) []
        ⟨.ctor PatternCtor.nil [], constructorMissMatcher,
          constructorTarget⟩ := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
theorem public_frozen_private_constructor_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenPrivateConstructor.definitions
        constructorMismatchReducer)
      20 [privateConstructorInitialState] = .ok [] := by
  rw [frozenPrivateConstructor_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_private_constructor_typed (fuel : Nat) :
    TypedMatchingSearchResult []
      (depthFirstFuel
        (stepPatternFunctionState frozenPrivateConstructor.definitions
          constructorMismatchReducer)
        fuel [privateConstructorInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    constructorMismatchReducer_checkedSafe
    constructorMismatchReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact privateConstructorInitialState_checked_automatic

theorem public_frozen_private_constructor_never_stuck (fuel : Nat) :
    (depthFirstFuel
      (stepPatternFunctionState frozenPrivateConstructor.definitions
        constructorMismatchReducer)
      fuel [privateConstructorInitialState]).NotStuck := by
  rcases public_frozen_private_constructor_typed fuel with timeout |
    ⟨answers, success, _answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-! ## Proof-bearing successful constructor dispatch

The `cons` pattern below has one binding-producing field and one wildcard
field.  Its concrete user matcher executes the real clause dispatcher and
returns one delegated variable atom, so this fixture distinguishes a genuine
constructor success from the zero-decomposition `nil` mismatch above.
-/

def privateSuccessfulConstructorName : PatternFunName :=
  ⟨"privateSuccessfulConstructor"⟩

def privateSuccessfulConstructorBody : Pattern :=
  .ctor PatternCtor.cons [.var, .wild]

def privateSuccessfulConstructorSource : PatternFunctionSourceDefinition :=
  { name := privateSuccessfulConstructorName
    scheme := privateConstructorScheme
    body := privateSuccessfulConstructorBody }

def privateSuccessfulConstructorGenerated : GeneratedPattern :=
  { dual := ⟨.con PatternFormer.list [.var ⟨0⟩],
      DataTypes.list (.var ⟨0⟩)⟩
    bindings := [.var ⟨1⟩]
    hard := [
      .ty (.var ⟨1⟩) (.var ⟨0⟩),
      .cap (.var ⟨1⟩) (.var ⟨0⟩),
      .ty (.var ⟨2⟩) (DataTypes.list (.var ⟨0⟩)),
      .cap (.var ⟨2⟩) (.con PatternFormer.list [.var ⟨0⟩])]
    pending := [] }

def privateSuccessfulConstructorSolution : Subst :=
  { ty := fun index =>
      if index.index = 2 then DataTypes.list .int else .int
    cap := fun index =>
      if index.index = 2 then .con PatternFormer.list [.any] else .any }

theorem privateSuccessfulConstructor_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          [privateSuccessfulConstructorSource]) [] []
        privateSuccessfulConstructorBody []
        (privateConstructorScheme.instantiate ⟨0, 0⟩).2 =
      some (privateSuccessfulConstructorGenerated, ⟨3, 3⟩) := by
  simp [privateSuccessfulConstructorSource, privateSuccessfulConstructorBody,
    privateSuccessfulConstructorGenerated, privateConstructorScheme,
    elaboratePattern, elaboratePatterns, Pattern.fieldEquations,
    PatternFunctionFreeze.signature,
    FrozenSignature.lookupPatternConstructor, ListPatternSchemes.cons,
    DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
    PolyCap.openBoundList, PolyTy.openBound, PolyTy.openBoundList,
    Scheme.boundTyInstance, Scheme.boundCapInstance, PolyDataTypes.list,
    DataTypes.list]

theorem privateSuccessfulConstructor_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature
        [privateSuccessfulConstructorSource])
      [privateSuccessfulConstructorSource] = true := by
  have semantic :
      (resultCheckBlock privateSuccessfulConstructorGenerated
        (privateConstructorScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          privateSuccessfulConstructorSolution := by
    constructor <;>
      simp [resultCheckBlock, privateSuccessfulConstructorGenerated,
        privateConstructorScheme, privateSuccessfulConstructorSolution,
        Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyCap.openBoundList, PolyTy.openBound, PolyTy.openBoundList,
        Scheme.boundTyInstance, Scheme.boundCapInstance, Cap.apply,
        Cap.applyList, Ty.apply, Ty.applyList, PolyDataTypes.list,
        DataTypes.list]
  have checked := checkedBody_isSome_of_semantic
    privateSuccessfulConstructor_elaboration_exact
    (solution := privateSuccessfulConstructorSolution) (by rfl) semantic
  simpa [privateSuccessfulConstructorSource, privateConstructorScheme,
    privateSuccessfulConstructorBody, checkBodies] using checked

set_option maxRecDepth 100000 in
theorem public_private_successful_constructor_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed
      [privateSuccessfulConstructorSource]).isSome = true := by
  have names :
      (([privateSuccessfulConstructorSource] :
        List PatternFunctionSourceDefinition).map
          PatternFunctionSourceDefinition.name).Nodup := by decide
  have closed : interfacesClosed [privateSuccessfulConstructorSource] = true :=
    by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed,
    dif_pos privateSuccessfulConstructor_bodies_checked]
  rfl

def frozenPrivateSuccessfulConstructor : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed
    [privateSuccessfulConstructorSource]).get
      public_private_successful_constructor_freeze_succeeds

theorem public_private_successful_constructor_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [privateSuccessfulConstructorSource] =
        some frozenPrivateSuccessfulConstructor := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [privateSuccessfulConstructorSource] with
  | none =>
      have success := public_private_successful_constructor_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenPrivateSuccessfulConstructor, frozenEq]

def privateSuccessfulConstructorDefinition : PatternFunctionDefinition :=
  { name := privateSuccessfulConstructorName
    parameterCount := 0
    body := privateSuccessfulConstructorBody }

theorem frozenPrivateSuccessfulConstructor_definitions_exact :
    frozenPrivateSuccessfulConstructor.definitions =
      [privateSuccessfulConstructorDefinition] := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenPrivateSuccessfulConstructor)
    public_private_successful_constructor_freeze_exact
  simpa [PatternFunctionFreeze.definitions,
    privateSuccessfulConstructorSource,
    PatternFunctionSourceDefinition.runtimeDefinition,
    privateSuccessfulConstructorDefinition, privateConstructorScheme] using
      definitionsEq

theorem frozenPrivateSuccessfulConstructor_lookup :
    frozenPrivateSuccessfulConstructor.definitions.lookup
        privateSuccessfulConstructorName =
      some privateSuccessfulConstructorDefinition := by
  rw [frozenPrivateSuccessfulConstructor_definitions_exact]
  rfl

def successfulConstructorDecompositionBody : Source.Expr :=
  .ctor DataCtor.cons [.var 0, .ctor DataCtor.nil []]

def successfulConstructorClause : MatcherClause :=
  .mk (.ctor PatternCtor.cons [.hole, .wild]) .something
    [.mk (.ctor DataCtor.cons [.var, .wild])
      successfulConstructorDecompositionBody]

def successfulConstructorFallbackClause : MatcherClause :=
  .mk .hole .something [.mk .var (.ctor DataCtor.nil [])]

def successfulConstructorMatcher : Value :=
  .matcherV []
    [successfulConstructorClause, successfulConstructorFallbackClause]
    [successfulConstructorClause, successfulConstructorFallbackClause]

def successfulConstructorTarget : Value :=
  .data DataCtor.cons [.int 7, .data DataCtor.nil []]

private theorem successfulConstructorClause_inputTyped
    (atomEnvironmentTypes : List Ty) :
    RuntimeMatcherClauseInputTyping atomEnvironmentTypes []
      (DataTypes.list .int) privateSuccessfulConstructorBody
      successfulConstructorClause := by
  apply RuntimeMatcherClauseInputTyping.mk
      (holes := [⟨.any, .int⟩]) (captureTypes := [])
  · apply RuntimePPatTyping.ctor
    exact RuntimePPatsTyping.cons (.hole .any)
      (RuntimePPatsTyping.cons
        (target := DataTypes.list .int) .wild .nil)
  · exact .one (.checked (.something .int) (.matcherToSlot .equal))
  · apply RuntimeMatcherArmsTyping.cons
    · apply RuntimeMatcherArmTyping.mk
        (RuntimeDPatTyping.ctor (.listCons .int)
          (RuntimeDPatsTyping.cons .var
            (RuntimeDPatsTyping.cons .wild .nil)))
      exact .listCons (.var rfl) (.listNil .int)
    · exact .nil
  · intro dispatch inspected
    simp [privateSuccessfulConstructorBody, inspectPatternPattern,
      inspectPatternPatterns] at inspected
    subst dispatch
    exact .nil

private theorem successfulConstructorFallbackClause_inputTyped
    (atomEnvironmentTypes : List Ty) :
    RuntimeMatcherClauseInputTyping atomEnvironmentTypes []
      (DataTypes.list .int) privateSuccessfulConstructorBody
      successfulConstructorFallbackClause := by
  apply RuntimeMatcherClauseInputTyping.mk
      (holes := [⟨.any, DataTypes.list .int⟩]) (captureTypes := [])
  · exact .hole .any
  · exact .one (.checked (.something (DataTypes.list .int))
      (.matcherToSlot .equal))
  · exact .cons (.mk .var (.listNil (DataTypes.list .int))) .nil
  · intro dispatch inspected
    simp [privateSuccessfulConstructorBody, inspectPatternPattern] at inspected
    subst dispatch
    exact .nil

private theorem successfulConstructorClauses_inputTyped
    (atomEnvironmentTypes : List Ty) :
    RuntimeMatcherClausesInputTyping atomEnvironmentTypes []
      (DataTypes.list .int) privateSuccessfulConstructorBody
      [successfulConstructorClause, successfulConstructorFallbackClause] :=
  .cons (successfulConstructorClause_inputTyped atomEnvironmentTypes)
    (.cons (successfulConstructorFallbackClause_inputTyped atomEnvironmentTypes)
      .nil)

private theorem successfulConstructorDecompositionBody_eval
    (fuel : Nat) (environment : ValueEnvironment) :
    evalFuel (fuel + 2) (.int 7 :: environment)
        successfulConstructorDecompositionBody =
      .ok (Value.buildList [.int 7]) := by
  cases fuel <;> rfl

private theorem successfulConstructor_next_eval
    (fuel : Nat) (environment : ValueEnvironment) :
    evalFuel (fuel + 2) environment .something = .ok .something := by
  cases fuel <;> rfl

private theorem successfulConstructor_dispatch_zero
    (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel 0) atomEnvironment []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget =
      .timeout := by
  with_unfolding_all rfl

private theorem successfulConstructor_dispatch_one
    (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel 1) atomEnvironment []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget =
      .timeout := by
  with_unfolding_all rfl

private theorem successfulConstructor_dispatch_from_two
    (fuel : Nat) (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel (fuel + 2)) atomEnvironment []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget =
      .ok (.hit [[⟨.var, .something, .int 7⟩]]) := by
  simp [dispatchMatcherClauses, firstHit, tryMatcherClause,
    inspectPatternPattern, inspectPatternPatterns, FuelResult.traverse,
    tryMatcherArm, matchValueDataPattern, matchValueDataPatterns,
    PatternDispatch.empty, PatternDispatch.append,
    successfulConstructorClause,
    privateSuccessfulConstructorBody, successfulConstructorTarget,
    successfulConstructorDecompositionBody_eval fuel,
    successfulConstructor_next_eval fuel,
    Value.consValue, Value.buildList, Value.nilValue, Value.viewList,
    decodeDecompositions, closeMatcherArmsResult,
    buildMatchingBranches, zipMatchingAtoms, List.mapM_cons,
    FuelResult.bind, FuelResult.map]

private theorem successfulConstructor_dispatches_singleBranch
    (success : dispatchMatcherClauses (evalFuel fuel) atomEnvironment []
      [successfulConstructorClause, successfulConstructorFallbackClause]
      privateSuccessfulConstructorBody
      successfulConstructorTarget = .ok (.hit branches)) :
    branches = [[⟨.var, .something, .int 7⟩]] := by
  cases fuel with
  | zero =>
      rw [successfulConstructor_dispatch_zero] at success
      contradiction
  | succ fuel =>
      cases fuel with
      | zero =>
          rw [successfulConstructor_dispatch_one] at success
          contradiction
      | succ fuel =>
          rw [successfulConstructor_dispatch_from_two fuel atomEnvironment]
            at success
          simpa using success.symm

private def successfulConstructorOrdinaryLeaf
    (privateEnvironmentTypes privateBindingTypes : List Ty)
    (original : List MatcherClause) :
    CheckedPrivateBodyOrdinaryLeaf privateEnvironmentTypes privateBindingTypes
      ⟨.ctor ⟨"cons"⟩ [.var, .wild],
        .matcherV [] original
          [⟨.ctor ⟨"cons"⟩ [.hole, .wild], .something,
              [⟨.ctor ⟨"cons"⟩ [.var, .wild],
                .ctor ⟨"cons"⟩ [.var 0, .ctor ⟨"nil"⟩ []]⟩]⟩,
            ⟨.hole, .something, [⟨.var, .ctor ⟨"nil"⟩ []⟩]⟩],
        .data ⟨"cons"⟩ [.int 7, .data ⟨"nil"⟩ []]⟩ where
  newPrivateBindings := [.int]
  typed :=
    { typed := .user
        (by intro eval environment; rfl)
        .nil
        (.list (.cons (.int 7) .nil))
        (successfulConstructorClauses_inputTyped
          (privateBindingTypes ++ privateEnvironmentTypes))
        (.skip .last)
        (by
          intro fuel atomEnvironment holes branches dispatched
            branchesTyped branch member
          have exactBranches :=
            successfulConstructor_dispatches_singleBranch dispatched
          subst branches
          simp only [List.mem_singleton] at member
          subst branch
          exact .cons (.builtin (.somethingVar (.int 7))) .nil)
      notApplication := by
        intro name arguments equality
        simp at equality
      notParameter := by
        intro index equality
        simp at equality }

def privateSuccessfulConstructorResolver :
    CheckedPrivateBodyResolver frozenPrivateSuccessfulConstructor.signature
      frozenPrivateSuccessfulConstructor.definitions [] [] where
  exports := { resolve := fun _ _ _ _ => none }
  targets target :=
    match target with
    | .data ⟨"cons"⟩ [.int 7, .data ⟨"nil"⟩ []] =>
        some ⟨DataTypes.list .int, .list (.cons (.int 7) .nil)⟩
    | _ => none
  ordinary _ _ _ := none
  constructors privateEnvironmentTypes privateBindingTypes constructor fields
      matcher target :=
    match constructor, fields, matcher, target with
    | ⟨"cons"⟩, [.var, .wild],
        .matcherV [] original
          [⟨.ctor ⟨"cons"⟩ [.hole, .wild], .something,
              [⟨.ctor ⟨"cons"⟩ [.var, .wild],
                .ctor ⟨"cons"⟩ [.var 0, .ctor ⟨"nil"⟩ []]⟩]⟩,
            ⟨.hole, .something, [⟨.var, .ctor ⟨"nil"⟩ []⟩]⟩],
        .data ⟨"cons"⟩ [.int 7, .data ⟨"nil"⟩ []] =>
          some (successfulConstructorOrdinaryLeaf
            privateEnvironmentTypes privateBindingTypes original)
    | _, _, _, _ => none
  applications _ _ _ _ _ := none

def privateSuccessfulConstructorCompilation :=
  CheckedPrivateBodyExecution.compile privateSuccessfulConstructorResolver
    [] [] []
    ⟨privateSuccessfulConstructorDefinition.body,
      successfulConstructorMatcher, successfulConstructorTarget⟩

theorem privateSuccessfulConstructorCompilation_isSome :
    privateSuccessfulConstructorCompilation.isSome = true := by
  simp [privateSuccessfulConstructorCompilation,
    CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel,
    privateSuccessfulConstructorResolver,
    privateSuccessfulConstructorDefinition,
    privateSuccessfulConstructorBody, successfulConstructorMatcher,
    successfulConstructorClause, successfulConstructorFallbackClause,
    successfulConstructorDecompositionBody, successfulConstructorTarget,
    successfulConstructorOrdinaryLeaf,
    PatternCtor.cons, DataCtor.cons, DataCtor.nil]

def privateSuccessfulConstructorCompilationResult :=
  privateSuccessfulConstructorCompilation.get
    privateSuccessfulConstructorCompilation_isSome

theorem privateSuccessfulConstructorCompilation_frames :
    (privateSuccessfulConstructorCompilationResult.1,
      privateSuccessfulConstructorCompilationResult.2.1) = ([], [.int]) := by
  have projectedExact :
      privateSuccessfulConstructorCompilation.map
          (fun result => (result.1, result.2.1)) =
        some ([], [.int]) := by
    simp [privateSuccessfulConstructorCompilation,
      CheckedPrivateBodyExecution.compile,
      CheckedPrivateBodyExecution.compileFuel,
      privateSuccessfulConstructorResolver,
      privateSuccessfulConstructorDefinition,
      privateSuccessfulConstructorBody, successfulConstructorMatcher,
      successfulConstructorClause, successfulConstructorFallbackClause,
      successfulConstructorDecompositionBody, successfulConstructorTarget,
      successfulConstructorOrdinaryLeaf,
      PatternCtor.cons, DataCtor.cons, DataCtor.nil]
  have projectedSome :
      (privateSuccessfulConstructorCompilation.map
        (fun result => (result.1, result.2.1))).isSome = true := by
    simp [projectedExact]
  have projectedGet :
      (privateSuccessfulConstructorCompilation.map
        (fun result => (result.1, result.2.1))).get projectedSome =
          ([], [.int]) := by
    simp [projectedExact]
  simpa [privateSuccessfulConstructorCompilationResult, Option.get_map] using
    projectedGet

/-- The constructor proof changes only the private frame: a nonempty outer
frame and a pre-existing private binding are threaded exactly. -/
def privateSuccessfulConstructorThreadedCompilation :=
  CheckedPrivateBodyExecution.compile privateSuccessfulConstructorResolver
    [.int] [.int] [DataTypes.bool]
    ⟨privateSuccessfulConstructorDefinition.body,
      successfulConstructorMatcher, successfulConstructorTarget⟩

theorem privateSuccessfulConstructorThreadedCompilation_frames :
    privateSuccessfulConstructorThreadedCompilation.map
        (fun result => (result.1, result.2.1)) =
      some ([.int], [DataTypes.bool, .int]) := by
  simp [privateSuccessfulConstructorThreadedCompilation,
    CheckedPrivateBodyExecution.compile,
    CheckedPrivateBodyExecution.compileFuel,
    privateSuccessfulConstructorResolver,
    privateSuccessfulConstructorDefinition,
    privateSuccessfulConstructorBody, successfulConstructorMatcher,
    successfulConstructorClause, successfulConstructorFallbackClause,
    successfulConstructorDecompositionBody, successfulConstructorTarget,
    successfulConstructorOrdinaryLeaf,
    PatternCtor.cons, DataCtor.cons, DataCtor.nil]

def privateSuccessfulConstructorBodyExecution :
    CheckedPrivateBodyExecution frozenPrivateSuccessfulConstructor.signature
      frozenPrivateSuccessfulConstructor.definitions [] [] [] [] []
      ⟨privateSuccessfulConstructorDefinition.body,
        successfulConstructorMatcher, successfulConstructorTarget⟩ [] [.int] := by
  have frames := privateSuccessfulConstructorCompilation_frames
  generalize resultEq : privateSuccessfulConstructorCompilationResult = result
    at frames
  have execution := privateSuccessfulConstructorCompilationResult.2.2
  rw [resultEq] at execution
  rcases result with ⟨outerTypes, privateTypes, execution⟩
  change (outerTypes, privateTypes) = ([], [.int]) at frames
  cases frames
  exact execution

def privateSuccessfulConstructorInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app privateSuccessfulConstructorName [],
    successfulConstructorMatcher, successfulConstructorTarget⟩], [], []⟩

theorem privateSuccessfulConstructorInitialState_checked_automatic :
    CheckedScopedStateTyping frozenPrivateSuccessfulConstructor.signature
      frozenPrivateSuccessfulConstructor.definitions
      privateSuccessfulConstructorInitialState [] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfCheckedPrivateBodyExecution
    frozenPrivateSuccessfulConstructor.agreement
    frozenPrivateSuccessfulConstructor_lookup rfl
    privateSuccessfulConstructorBodyExecution .nil

def successfulConstructorReduction : AtomReduction :=
  ⟨[[⟨.var, .something, .int 7⟩]], []⟩

/-- The certified constructor shape is reduced successfully.  This helper is
slightly broader than the concrete regression atom because it ignores the
runtime environment and the matcher's unused `original` cursor; agreement
with the real evaluator is proved below only for the concrete atom in the
empty environment.  Other user atoms retain the built-in-miss-to-timeout
behavior. -/
def successfulConstructorReducer (environment : ValueEnvironment)
    (atom : MatchingAtom) : FuelResult (DispatchResult AtomReduction) :=
  match atom with
  | ⟨.ctor ⟨"cons"⟩ [.var, .wild],
      .matcherV [] _
        [⟨.ctor ⟨"cons"⟩ [.hole, .wild], .something,
            [⟨.ctor ⟨"cons"⟩ [.var, .wild],
              .ctor ⟨"cons"⟩ [.var 0, .ctor ⟨"nil"⟩ []]⟩]⟩,
          ⟨.hole, .something, [⟨.var, .ctor ⟨"nil"⟩ []⟩]⟩],
      .data ⟨"cons"⟩ [.int 7, .data ⟨"nil"⟩ []]⟩ =>
        .ok (.hit successfulConstructorReduction)
  | _ => privateBuiltinReducer environment atom

private theorem checkedVariableSevenBranch_of_total
    (typed : TotalMatchingAtomsTyping environmentTypes bindingTypes
      [⟨.var, .something, .int 7⟩] newBindings) :
    CheckedOrdinaryAtomsTyping environmentTypes bindingTypes
      [⟨.var, .something, .int 7⟩] newBindings := by
  cases typed with
  | cons head tail =>
      cases tail
      cases head with
      | builtin headTyped =>
          exact .cons (CheckedOrdinaryAtomTyping.ofBuiltin headTyped) .nil

theorem successfulConstructorReducer_checkedSafe :
    CheckedScopedAtomReducerTypedSafe successfulConstructorReducer := by
  intro environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern <;>
    try simpa [successfulConstructorReducer] using
      (privateBuiltinReducer_checkedSafe environmentTyped bindingsTyped atomTyped)
  case ctor constructor fields =>
    unfold successfulConstructorReducer
    split
    next original =>
      cases original
      cases atomTyped.typed with
      | builtin typed => cases typed
      | user builtinMiss matcherEnvironmentTyped targetTyped clausesTyped
          finalCatchAll branches =>
          have dispatched :
              dispatchMatcherClauses (evalFuel 4) (bindings ++ environment) []
                  [successfulConstructorClause,
                    successfulConstructorFallbackClause]
                  privateSuccessfulConstructorBody
                  successfulConstructorTarget =
                .ok (.hit [[⟨.var, .something, .int 7⟩]]) := by
            exact successfulConstructor_dispatch_from_two 2 _
          have delegated : DelegatedMatchingBranchesTyping
              [⟨.any, .int⟩] [[⟨.var, .something, .int 7⟩]] :=
            .cons
              (.cons (.checked (.something .int) (.matcherToSlot .equal))
                (.int 7) .nil)
              .nil
          have totalBranch := branches 4 (bindings ++ environment) dispatched
            delegated [⟨.var, .something, .int 7⟩] (by simp)
          exact .inr ⟨successfulConstructorReduction, rfl,
            .intro [] .nil (by
              intro branch member
              simp [successfulConstructorReduction] at member
              subst branch
              exact ⟨newBindings,
                by simpa using
                  (checkedVariableSevenBranch_of_total totalBranch), rfl⟩)⟩
    next =>
      simpa using
        (privateBuiltinReducer_checkedSafe environmentTyped bindingsTyped
          atomTyped)

theorem successfulConstructorReducer_structuralSafe :
    CheckedBodyReducerSafe successfulConstructorReducer := by
  intro environment atom atoms expansion
  cases expansion with
  | and => rfl
  | tuple zipped =>
      simp [successfulConstructorReducer, privateBuiltinReducer,
        reduceBuiltinAtom, zipped]

/-- The successful bespoke branch is exactly the branch returned by the
actual user-matcher dispatcher at evaluator fuel four. -/
theorem successfulConstructorReducer_agrees_with_actual_dispatch :
    successfulConstructorReducer []
        ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
          successfulConstructorTarget⟩ =
      evaluationAtomReducer (evalFuel 4) []
        ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
          successfulConstructorTarget⟩ := by
  have dispatched := successfulConstructor_dispatch_from_two 2 []
  have builtinMiss :
      reduceBuiltinAtom (evalFuel 4) []
          ⟨privateSuccessfulConstructorBody, successfulConstructorMatcher,
            successfulConstructorTarget⟩ =
        FuelResult.ok DispatchResult.miss := by
    rfl
  change FuelResult.ok (DispatchResult.hit successfulConstructorReduction) = _
  unfold evaluationAtomReducer combineAtomReducers
  rw [builtinMiss]
  simp only [FuelResult.bind]
  unfold reduceMatcherAtom
  change FuelResult.ok (DispatchResult.hit successfulConstructorReduction) =
    FuelResult.map clauseResultToAtomReduction
      (dispatchMatcherClauses (evalFuel 4) [] []
        [successfulConstructorClause, successfulConstructorFallbackClause]
        privateSuccessfulConstructorBody successfulConstructorTarget)
  rw [show dispatchMatcherClauses (evalFuel 4) [] []
      [successfulConstructorClause, successfulConstructorFallbackClause]
      privateSuccessfulConstructorBody successfulConstructorTarget =
        .ok (.hit [[⟨.var, .something, .int 7⟩]]) by
    simpa using dispatched]
  rfl

set_option maxRecDepth 100000 in
theorem public_frozen_private_successful_constructor_exact :
    depthFirstFuel
      (stepPatternFunctionState
        frozenPrivateSuccessfulConstructor.definitions
        successfulConstructorReducer)
      20 [privateSuccessfulConstructorInitialState] = .ok [[]] := by
  rw [frozenPrivateSuccessfulConstructor_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_private_successful_constructor_typed (fuel : Nat) :
    TypedMatchingSearchResult []
      (depthFirstFuel
        (stepPatternFunctionState
          frozenPrivateSuccessfulConstructor.definitions
          successfulConstructorReducer)
        fuel [privateSuccessfulConstructorInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    successfulConstructorReducer_checkedSafe
    successfulConstructorReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact privateSuccessfulConstructorInitialState_checked_automatic

theorem public_frozen_private_successful_constructor_never_stuck
    (fuel : Nat) :
    (depthFirstFuel
      (stepPatternFunctionState
        frozenPrivateSuccessfulConstructor.definitions
        successfulConstructorReducer)
      fuel [privateSuccessfulConstructorInitialState]).NotStuck := by
  rcases public_frozen_private_successful_constructor_typed fuel with timeout |
    ⟨answers, success, _answersTyped⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TypePM.PatternFunctionPrivateBodyPlanAutomationRegression
