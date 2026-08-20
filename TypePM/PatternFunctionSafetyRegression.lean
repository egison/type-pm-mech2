import TypePM.PatternFunctionSafety
import TypePM.Source.ElaborationCompleteness

/-!
# Focused scoped-node safety regressions

The frozen nullary `discard` definition has an `any`/`Int` result interface
and a wildcard body.  It is small enough that the public freeze checker and
all three MNode-specific typed steps can be pinned without relying on the
larger Paper 2 fixture.
-/

namespace TypePM.PatternFunctionSafetyRegression

open Source Runtime
open Source.PatternFunctionFreeze

def discardName : PatternFunName := ⟨"discard"⟩

def discardScheme : DualScheme :=
  { tyArity := 0
    capArity := 0
    fields := []
    result := ⟨.any, .int⟩
    fieldsWellScoped := by simp
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped] }

def discardDefinition : PatternFunctionDefinition :=
  { name := discardName, parameterCount := 0, body := .wild }

def discardSource : PatternFunctionSourceDefinition :=
  { name := discardName, scheme := discardScheme, body := .wild }

def discardSignature : FrozenSignature :=
  PatternFunctionFreeze.signature Paper1Signature.signature [discardSource]

def discardDefinitions : PatternFunctionDefinitions := [discardDefinition]

def discardGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := []
    hard := []
    pending := [] }

def discardSolution : Subst :=
  { cap := fun _ => .any, ty := fun _ => .int }

def discardChecked : discardDefinition.Checked discardSignature where
  scheme := discardScheme
  lookup := by rfl
  arity := by rfl
  generated := discardGenerated
  next := ⟨1, 1⟩
  bodyElaboration := .wild
  solution := discardSolution
  semanticSolution := by
    simp [GeneratedPattern.SemanticSolution, discardGenerated, Solves]
  resultCapability_eq := by
    simp [discardGenerated, discardScheme, discardSolution,
      DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
      Scheme.boundCapInstance, Cap.apply]
  resultTarget_eq := by
    simp [discardGenerated, discardScheme, discardSolution,
      DualScheme.instantiate, PolyDual.openBound, PolyTy.openBound,
      Scheme.boundTyInstance, Ty.apply]

theorem discardSignature_wellFormed : discardSignature.WellFormed := by
  refine
    { baseWellFormed := Paper1Signature.wellFormed
      patternFunctionNodup := by decide
      patternFunctionClosed := ?_
      patternFunctionWellFormed := ?_ }
  · intro declaration member
    simp [discardSignature, PatternFunctionFreeze.signature, discardSource]
      at member
    subst declaration
    change discardScheme.Closed
    simp [DualScheme.Closed, DualScheme.freeTyVars,
      DualScheme.freeCapVars, discardScheme, PolyTy.freeTyVars,
      PolyTy.freeCapVars, PolyCap.freeCapVars, dedupFirst, dedup]
  · intro declaration member
    simp [discardSignature, PatternFunctionFreeze.signature, discardSource]
      at member
    subst declaration
    exact discardScheme.wellFormed

theorem discardDefinitions_agree :
    discardDefinitions.Agree discardSignature := by
  refine
    { signatureWellFormed := discardSignature_wellFormed
      namesNodup := by decide
      runtimeChecked := ?_
      sourceImplemented := ?_ }
  · intro definition member
    simp [discardDefinitions] at member
    subst definition
    exact ⟨discardChecked⟩
  · intro declaration member
    simp [discardSignature, PatternFunctionFreeze.signature, discardSource]
      at member
    subst declaration
    exact ⟨discardDefinition, by simp [discardDefinitions], rfl⟩

theorem discard_elaboration_exact :
    elaboratePattern discardSignature []
        (discardScheme.instantiate ⟨0, 0⟩).1.fields .wild []
        (discardScheme.instantiate ⟨0, 0⟩).2 =
      some (discardGenerated, ⟨1, 1⟩) := by
  simp [discardSignature, PatternFunctionFreeze.signature, discardScheme,
    discardGenerated, elaboratePattern, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound,
    PolyTy.openBound, Scheme.boundTyInstance,
    Scheme.boundCapInstance]

theorem discard_bodies_checked :
    checkBodies discardSignature [discardSource] = true := by
  have blockSemantic :
      (resultCheckBlock discardGenerated
        (discardScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          discardSolution := by
    constructor
    · simp [resultCheckBlock, discardGenerated, discardScheme,
        discardSolution, Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Ty.apply]
    · simp [resultCheckBlock, discardGenerated]
  have noPending :
      (resultCheckBlock discardGenerated
        (discardScheme.instantiate ⟨0, 0⟩).1.result).pending = [] := rfl
  have accepts :=
    (Generated.blockAccepts_iff_exists_semanticSolution_of_pending_eq_nil
      (resultCheckBlock discardGenerated
        (discardScheme.instantiate ⟨0, 0⟩).1.result) noPending).2
      ⟨discardSolution, blockSemantic⟩
  have succeeds := accepts.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases inferenceEq : inferGeneratedUsing unify
      (resultCheckBlock discardGenerated
        (discardScheme.instantiate ⟨0, 0⟩).1.result) with
  | none => exact False.elim (succeeds inferenceEq)
  | some result =>
      simp only [checkBodies, Bool.and_true]
      change (checkBody discardSignature discardScheme .wild).isSome = true
      simp only [checkBody]
      rw [discard_elaboration_exact]
      simp [inferenceEq]

set_option maxRecDepth 100000 in
/-- The same source definition is accepted by the public executable freeze
checker, rather than only by the hand-written relational certificate. -/
theorem public_discard_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [discardSource]).isSome = true := by
  have names :
      (([discardSource] : List PatternFunctionSourceDefinition).map
        PatternFunctionSourceDefinition.name).Nodup := by decide
  have closed : interfacesClosed [discardSource] = true := by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed]
  have checked : checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature
        [discardSource]) [discardSource] = true := by
    exact discard_bodies_checked
  rw [dif_pos checked]
  rfl

def frozenDiscard : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed [discardSource]).get
      public_discard_freeze_succeeds

theorem public_discard_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [discardSource] = some frozenDiscard := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [discardSource] with
  | none =>
      have success := public_discard_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenDiscard, frozenEq]

/-- A program returned by the public checker inherits preservation and
no-stuck from the ordinary evaluator on the proved simulation fragment. -/
theorem public_frozen_program_preserves_independent_expression :
    TypedResult .int
      (evalCheckedPatternFunctionNodesFuel frozenDiscard.signature
        frozenDiscard.definitions frozenDiscard.agreement 2 [] (.lit 6)) := by
  exact RuntimeTyping.freezeCheckedPatternFunctionNodesSafety
    public_discard_freeze_exact (.lit 6) .lit 2 [] .nil

theorem public_frozen_program_independent_expression_never_stuck :
    (evalCheckedPatternFunctionNodesFuel frozenDiscard.signature
      frozenDiscard.definitions frozenDiscard.agreement 2 [] (.lit 6)).NotStuck :=
  public_frozen_program_preserves_independent_expression.notStuck

theorem frozenDiscard_definitions_exact :
    frozenDiscard.definitions = discardDefinitions := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenDiscard) public_discard_freeze_exact
  simpa [PatternFunctionFreeze.definitions, discardSource,
    PatternFunctionSourceDefinition.runtimeDefinition, discardDefinitions,
    discardDefinition, discardScheme] using definitionsEq

/-- A genuine MNode application of the publicly frozen definition.  The
ordinary arm succeeds, so the explicit fallback is not selected. -/
def frozenDiscardProgram : Source.Expr :=
  .matchFirst (.lit 8) .something
    [.mk (.app discardName []) (.lit 1)] (.lit 0)

set_option maxRecDepth 100000 in
theorem public_frozen_mnode_application_executes_exact :
    evalCheckedPatternFunctionNodesFuel frozenDiscard.signature
      frozenDiscard.definitions frozenDiscard.agreement 20 []
        frozenDiscardProgram = .ok (.int 1) := by
  unfold evalCheckedPatternFunctionNodesFuel
  rw [frozenDiscard_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_mnode_application_preserves_type :
    TypedResult .int
      (evalCheckedPatternFunctionNodesFuel frozenDiscard.signature
        frozenDiscard.definitions frozenDiscard.agreement 20 []
          frozenDiscardProgram) :=
  .inr ⟨.int 1, public_frozen_mnode_application_executes_exact, .int 1⟩

theorem public_frozen_mnode_application_never_stuck :
    (evalCheckedPatternFunctionNodesFuel frozenDiscard.signature
      frozenDiscard.definitions frozenDiscard.agreement 20 []
        frozenDiscardProgram).NotStuck :=
  public_frozen_mnode_application_preserves_type.notStuck

def applicationTyping : MNodeApplicationTyping discardSignature
    discardDefinitions discardName [] .something (.int 8) [] [] [] []
    discardDefinition .any .int where
  agreement := discardDefinitions_agree
  found := by rfl
  arity := by rfl
  checkedResult := ⟨discardChecked, by rfl, by rfl⟩
  matcherTyped := .something .int
  targetTyped := .int 8
  outer := ⟨.nil, .nil⟩

/-- Application enters the checked body and cannot take the unknown-name or
wrong-arity stuck branches. -/
theorem typed_application_starts_checked_node :
    stepPatternFunctionHead discardDefinitions
        (evaluationAtomReducer (evalFuel 2))
        (.atom ⟨.app discardName [], .something, .int 8⟩) [] [] [] =
      .ok [⟨[.node [.atom ⟨.wild, .something, .int 8⟩] [] [] []], [], []⟩] ∧
      Nonempty (discardDefinition.Checked discardSignature) ∧
      PatternFunctionOuterFrameTyping [] [] [] [] :=
  applicationTyping.step _ []

def parameterTyping : MNodeParameterTyping [.var] 0 .var .something (.int 7)
    [] [] [] [.int 99] [] [] [] [.int] [.int] where
  argumentLookup := rfl
  outer := ⟨.nil, .nil⟩
  privateEnvironmentTyped := .nil
  privateBindingsTyped := .cons (.int 99) .nil
  exportedAtomTyped := .builtin (.somethingVar (.int 7))

/-- Parameter export preserves the typed private frame and exposes a typed
ordinary atom whose binding belongs to the outer frame. -/
theorem typed_parameter_exports_outer_atom :
    stepPatternFunctionHead discardDefinitions
        (evaluationAtomReducer (evalFuel 2))
        (.node [.atom ⟨.embed 0, .something, .int 7⟩]
          [] [.int 99] [.var]) [] [] [] =
      .ok [⟨[.atom ⟨.var, .something, .int 7⟩,
          .node [] [] [.int 99] [.var]], [], []⟩] ∧
      TotalMatchingAtomTyping [] [] ⟨.var, .something, .int 7⟩ [.int] ∧
      PatternFunctionOuterFrameTyping [] [] [] [] ∧
      EnvironmentTyping [] [] ∧ ValueTypings [.int 99] [.int] :=
  parameterTyping.step _ _ [] []

def doneTyping : MNodeDoneTyping [] [.int 4] [] [.int] :=
  ⟨⟨.nil, .cons (.int 4) .nil⟩⟩

/-- Node completion discards the private value but returns the unchanged
typed outer binding. -/
theorem typed_node_done_preserves_outer_frame :
    stepPatternFunctionHead discardDefinitions
        (evaluationAtomReducer (evalFuel 2))
        (.node [] [] [.int 99] []) [] [] [.int 4] =
      .ok [⟨[], [], [.int 4]⟩] ∧
      PatternFunctionOuterFrameTyping [] [.int 4] [] [.int] :=
  doneTyping.step _ _ [] [.int 99] [] []

/-! ## Complete checked scoped-search regression

`identity` is frozen by the public checker.  Its checked body is one embedded
parameter, while the actual argument is a variable handled in the outer
frame.  The small reducer below implements the variable, wildcard, and
conjunction cases used by these scoped regressions and times out otherwise.
It is globally safe for the structural fragment and lets the finite DFS
complete with the exported binding.
-/

def identityName : PatternFunName := ⟨"identity"⟩

def identityScheme : DualScheme :=
  { tyArity := 0
    capArity := 0
    fields := [⟨.any, .int⟩]
    result := ⟨.any, .int⟩
    fieldsWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped]
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped] }

def identitySource : PatternFunctionSourceDefinition :=
  { name := identityName, scheme := identityScheme, body := .embed 0 }

def identityGenerated : GeneratedPattern :=
  { dual := ⟨.any, .int⟩, bindings := [], hard := [], pending := [] }

def identitySolution : Subst :=
  { cap := fun _ => .any, ty := fun _ => .int }

theorem identity_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          [identitySource]) []
        (identityScheme.instantiate ⟨0, 0⟩).1.fields (.embed 0) []
        (identityScheme.instantiate ⟨0, 0⟩).2 =
      some (identityGenerated, ⟨0, 0⟩) := by
  simp [identityScheme, identitySource, identityGenerated, elaboratePattern,
    DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
    PolyTy.openBound, Scheme.boundTyInstance,
    Scheme.boundCapInstance]

theorem identity_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature
        [identitySource]) [identitySource] = true := by
  have blockSemantic :
      (resultCheckBlock identityGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          identitySolution := by
    constructor
    · simp [resultCheckBlock, identityGenerated, identityScheme,
        identitySolution, Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Ty.apply]
    · simp [resultCheckBlock, identityGenerated]
  have noPending :
      (resultCheckBlock identityGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result).pending = [] := rfl
  have accepts :=
    (Generated.blockAccepts_iff_exists_semanticSolution_of_pending_eq_nil
      (resultCheckBlock identityGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result) noPending).2
      ⟨identitySolution, blockSemantic⟩
  have succeeds := accepts.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases inferenceEq : inferGeneratedUsing unify
      (resultCheckBlock identityGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result) with
  | none => exact False.elim (succeeds inferenceEq)
  | some result =>
      simp only [identitySource, checkBodies, Bool.and_true]
      change (checkBody
        (PatternFunctionFreeze.signature Paper1Signature.signature
          [identitySource]) identityScheme (.embed 0)).isSome = true
      simp only [checkBody]
      rw [identity_elaboration_exact]
      simp [inferenceEq]

set_option maxRecDepth 100000 in
theorem public_identity_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [identitySource]).isSome = true := by
  have names :
      (([identitySource] : List PatternFunctionSourceDefinition).map
        PatternFunctionSourceDefinition.name).Nodup := by decide
  have closed : interfacesClosed [identitySource] = true := by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed,
    dif_pos identity_bodies_checked]
  rfl

def frozenIdentity : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed [identitySource]).get
      public_identity_freeze_succeeds

theorem public_identity_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [identitySource] = some frozenIdentity := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [identitySource] with
  | none =>
      have success := public_identity_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenIdentity, frozenEq]

def identityDefinition : PatternFunctionDefinition :=
  { name := identityName, parameterCount := 1, body := .embed 0 }

theorem frozenIdentity_definitions_exact :
    frozenIdentity.definitions = [identityDefinition] := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenIdentity) public_identity_freeze_exact
  simpa [PatternFunctionFreeze.definitions, identitySource,
    PatternFunctionSourceDefinition.runtimeDefinition, identityDefinition,
    identityScheme] using definitionsEq

theorem frozenIdentity_lookup :
    frozenIdentity.definitions.lookup identityName = some identityDefinition := by
  rw [frozenIdentity_definitions_exact]
  rfl

def variableOnlyReducer (_environment : ValueEnvironment)
    (atom : MatchingAtom) : FuelResult (DispatchResult AtomReduction) :=
  match atom.pattern, atom.matcher with
  | .var, .something => .ok (.hit ⟨[[]], [atom.target]⟩)
  | .wild, .something => .ok (.hit ⟨[[]], []⟩)
  | .and left right, .something =>
      .ok (.hit ⟨[[⟨left, .something, atom.target⟩,
        ⟨right, .something, atom.target⟩]], []⟩)
  | .tuple patterns, .tuple matchers =>
      match atom.target with
      | .tuple targets =>
          match zipMatchingAtoms patterns matchers targets with
          | some atoms => .ok (.hit ⟨[atoms], []⟩)
          | none => .timeout
      | _ => .timeout
  | _, _ => .timeout

theorem variableOnlyReducer_andSafe :
    CheckedAndReducerSafe variableOnlyReducer := by
  intro environment left right target
  rfl

theorem variableOnlyReducer_structuralSafe :
    CheckedBodyReducerSafe variableOnlyReducer := by
  exact checkedBodyReducerSafe_of_and_tuple variableOnlyReducer_andSafe (by
    intro environment patterns matchers targets atoms zipped
    simp [variableOnlyReducer, zipped])

theorem variableOnlyReducer_checkedSafe :
    CheckedScopedAtomReducerTypedSafe variableOnlyReducer := by
  intro environmentTypes bindingTypes environment bindings atom newBindings
    environmentTyped bindingsTyped atomTyped
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern <;> cases matcher <;>
    simp [variableOnlyReducer]
  case var.something =>
    cases atomTyped.typed with
    | builtin typed =>
        cases typed with
        | somethingVar targetTyped =>
            exact .intro _ (.cons targetTyped .nil) (by
              intro branch member
              simp only [List.mem_singleton] at member
              subst branch
              exact ⟨[], .nil, rfl⟩)
  case wild.something =>
    cases atomTyped.typed with
    | builtin typed =>
        cases typed with
        | somethingWild targetTyped =>
            exact .intro [] .nil (by
              intro branch member
              simp only [List.mem_singleton] at member
              subst branch
              exact ⟨[], .nil, rfl⟩)
  case and.something left right =>
    cases atomTyped.typed with
    | builtin typed =>
        cases typed with
        | and leftTyped rightTyped =>
            exact .intro [] .nil (by
              intro branch member
              simp only [List.mem_singleton] at member
              subst branch
              exact ⟨_,
                .cons (by simpa using
                    CheckedOrdinaryAtomTyping.ofBuiltin leftTyped)
                  (.cons (by simpa using
                      CheckedOrdinaryAtomTyping.ofBuiltin rightTyped) .nil),
                by simp⟩)
  case tuple.tuple patterns matchers =>
    cases atomTyped.typed with
    | builtin typed =>
        cases typed with
        | tuple atoms zipped atomsTyped =>
            simp only
            rw [zipped.complete]
            exact .inr ⟨_, rfl, .intro [] .nil (by
                intro branch member
                simp only [List.mem_singleton] at member
                subst branch
                exact ⟨newBindings, by
                    simpa using CheckedOrdinaryAtomsTyping.ofBuiltin atomsTyped,
                  by simp⟩)⟩

def identityInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app identityName [.var], .something, .int 11⟩], [], []⟩

def identityBodyPlan :
    CheckedBodyAtomPlan frozenIdentity.signature frozenIdentity.definitions
      [] [.var] [] ⟨.embed 0, .something, .int 11⟩ [.int] :=
  CheckedBodyAtomPlan.parameter rfl
    (.ordinary
      ⟨.builtin (.somethingVar (.int 11)), by intros; simp, by intros; simp⟩
      .nil)

theorem identityInitialState_checked :
    CheckedScopedStateTyping frozenIdentity.signature
      frozenIdentity.definitions identityInitialState [.int] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfBodyPlan frozenIdentity.agreement
    frozenIdentity_lookup rfl identityBodyPlan .nil

theorem public_frozen_identity_scoped_dfs_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenIdentity.definitions variableOnlyReducer)
      8 [identityInitialState] = .ok [[.int 11]] := by
  rw [frozenIdentity_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_identity_scoped_dfs_typed :
    TypedMatchingSearchResult [.int]
      (depthFirstFuel
        (stepPatternFunctionState frozenIdentity.definitions variableOnlyReducer)
        8 [identityInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    variableOnlyReducer_checkedSafe variableOnlyReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact identityInitialState_checked

theorem public_frozen_identity_scoped_dfs_never_stuck :
    (depthFirstFuel
      (stepPatternFunctionState frozenIdentity.definitions variableOnlyReducer)
      8 [identityInitialState]).NotStuck := by
  rw [public_frozen_identity_scoped_dfs_exact]
  simp [FuelResult.NotStuck]

/-! ## A checked private-body call to another checked definition -/

def callerName : PatternFunName := ⟨"caller"⟩

def callerSource : PatternFunctionSourceDefinition :=
  { name := callerName
    scheme := identityScheme
    body := .app identityName [.embed 0] }

def nestedSources : List PatternFunctionSourceDefinition :=
  [identitySource, callerSource]

def callerGenerated : GeneratedPattern :=
  { dual := ⟨.any, .int⟩
    bindings := []
    hard := [.ty .int .int, .cap .any .any]
    pending := [] }

theorem nested_identity_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          nestedSources) []
        (identityScheme.instantiate ⟨0, 0⟩).1.fields (.embed 0) []
        (identityScheme.instantiate ⟨0, 0⟩).2 =
      some (identityGenerated, ⟨0, 0⟩) := by
  simp [nestedSources, identityScheme, identitySource, callerSource,
    identityGenerated, elaboratePattern, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound, PolyTy.openBound,
    Scheme.boundTyInstance, Scheme.boundCapInstance]

theorem nested_caller_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          nestedSources) []
        (identityScheme.instantiate ⟨0, 0⟩).1.fields callerSource.body []
        (identityScheme.instantiate ⟨0, 0⟩).2 =
      some (callerGenerated, ⟨0, 0⟩) := by
  simp [nestedSources, callerSource, identitySource, identityScheme,
    identityName, callerName, callerGenerated, elaboratePattern,
    elaboratePatterns,
    PatternFunctionFreeze.signature, FrozenSignature.lookupPatternFunction,
    PatternFunctionSourceDefinition.declaration, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound, PolyTy.openBound,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    Pattern.fieldEquations]

private theorem checked_body_isSome
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
  | some result =>
      simp [checkBody, elaboration, inferenceEq]

theorem nested_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature nestedSources)
      nestedSources = true := by
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
  have callerSemantic :
      (resultCheckBlock callerGenerated
        (identityScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          identitySolution := by
    constructor <;>
      simp [resultCheckBlock, callerGenerated, identityScheme,
        identitySolution, Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Ty.apply]
  have identityChecked := checked_body_isSome nested_identity_elaboration_exact
    (solution := identitySolution) (by rfl) identitySemantic
  have callerChecked := checked_body_isSome nested_caller_elaboration_exact
    (solution := identitySolution) (by rfl) callerSemantic
  simpa [nestedSources, identitySource, callerSource, identityScheme,
    checkBodies] using And.intro identityChecked callerChecked

set_option maxRecDepth 100000 in
theorem public_nested_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed nestedSources).isSome = true := by
  have names :
      (nestedSources.map PatternFunctionSourceDefinition.name).Nodup := by
    decide
  have closed : interfacesClosed nestedSources = true := by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed,
    dif_pos nested_bodies_checked]
  rfl

def frozenNested : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed nestedSources).get
      public_nested_freeze_succeeds

theorem public_nested_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed nestedSources = some frozenNested := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed nestedSources with
  | none =>
      have success := public_nested_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenNested, frozenEq]

def callerDefinition : PatternFunctionDefinition :=
  { name := callerName
    parameterCount := 1
    body := .app identityName [.embed 0] }

theorem frozenNested_definitions_exact :
    frozenNested.definitions = [identityDefinition, callerDefinition] := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenNested) public_nested_freeze_exact
  simpa [PatternFunctionFreeze.definitions, nestedSources, identitySource,
    callerSource, PatternFunctionSourceDefinition.runtimeDefinition,
    identityDefinition, callerDefinition, identityScheme] using definitionsEq

theorem frozenNested_identity_lookup :
    frozenNested.definitions.lookup identityName = some identityDefinition := by
  rw [frozenNested_definitions_exact]
  rfl

theorem frozenNested_caller_lookup :
    frozenNested.definitions.lookup callerName = some callerDefinition := by
  rw [frozenNested_definitions_exact]
  rfl

def nestedInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app callerName [.var], .something, .int 23⟩], [], []⟩

theorem nestedInitialState_checked :
    CheckedScopedStateTyping frozenNested.signature frozenNested.definitions
      nestedInitialState [.int] := by
  refine .mk .nil .nil ?_
  apply CheckedScopedWorkTyping.applicationOfAgreement frozenNested.agreement
    frozenNested_caller_lookup rfl
  · apply CheckedMNodeWorkTyping.applicationParameter
      frozenNested_identity_lookup
      (frozenNested.agreement.lookup_checked frozenNested_identity_lookup)
      rfl rfl rfl rfl
    · exact .ordinary
        ⟨.builtin (.somethingVar (.int 23)), by intros; simp, by intros; simp⟩
        .nil
    · exact .nil
  · exact .nil

theorem public_frozen_nested_scoped_dfs_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenNested.definitions variableOnlyReducer)
      12 [nestedInitialState] = .ok [[.int 23]] := by
  rw [frozenNested_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_nested_scoped_dfs_typed :
    TypedMatchingSearchResult [.int]
      (depthFirstFuel
        (stepPatternFunctionState frozenNested.definitions variableOnlyReducer)
        12 [nestedInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    variableOnlyReducer_checkedSafe variableOnlyReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact nestedInitialState_checked

theorem public_frozen_nested_scoped_dfs_never_stuck :
    (depthFirstFuel
      (stepPatternFunctionState frozenNested.definitions variableOnlyReducer)
      12 [nestedInitialState]).NotStuck := by
  rw [public_frozen_nested_scoped_dfs_exact]
  simp [FuelResult.NotStuck]

/-! ## Compound checked callee body -/

def conjoinName : PatternFunName := ⟨"conjoin"⟩
def binaryCallerName : PatternFunName := ⟨"binaryCaller"⟩

def binaryScheme : DualScheme :=
  { tyArity := 0
    capArity := 0
    fields := [⟨.any, .int⟩, ⟨.any, .int⟩]
    result := ⟨.any, .int⟩
    fieldsWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped]
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped] }

def conjoinSource : PatternFunctionSourceDefinition :=
  { name := conjoinName
    scheme := binaryScheme
    body := .and (.embed 0) (.embed 1) }

def binaryCallerSource : PatternFunctionSourceDefinition :=
  { name := binaryCallerName
    scheme := binaryScheme
    body := .app conjoinName [.embed 0, .embed 1] }

def compoundSources : List PatternFunctionSourceDefinition :=
  [conjoinSource, binaryCallerSource]

def binaryCallerGenerated : GeneratedPattern :=
  { dual := ⟨.any, .int⟩
    bindings := []
    hard := [
      .ty .int .int, .cap .any .any,
      .ty .int .int, .cap .any .any]
    pending := [] }

theorem conjoin_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          compoundSources) []
        (binaryScheme.instantiate ⟨0, 0⟩).1.fields conjoinSource.body []
        (binaryScheme.instantiate ⟨0, 0⟩).2 =
      some (callerGenerated, ⟨0, 0⟩) := by
  simp [compoundSources, conjoinSource, binaryCallerSource, binaryScheme,
    callerGenerated, elaboratePattern, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound, PolyTy.openBound,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    Pattern.dualEquations]

theorem binaryCaller_elaboration_exact :
    elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          compoundSources) []
        (binaryScheme.instantiate ⟨0, 0⟩).1.fields
        binaryCallerSource.body [] (binaryScheme.instantiate ⟨0, 0⟩).2 =
      some (binaryCallerGenerated, ⟨0, 0⟩) := by
  simp [compoundSources, conjoinSource, binaryCallerSource, binaryScheme,
    conjoinName, binaryCallerName, binaryCallerGenerated, elaboratePattern,
    elaboratePatterns, PatternFunctionFreeze.signature,
    FrozenSignature.lookupPatternFunction,
    PatternFunctionSourceDefinition.declaration, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound, PolyTy.openBound,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    Pattern.fieldEquations]

theorem compound_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature
        compoundSources) compoundSources = true := by
  have conjoinSemantic :
      (resultCheckBlock callerGenerated
        (binaryScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          identitySolution := by
    constructor <;>
      simp [resultCheckBlock, callerGenerated, binaryScheme,
        identitySolution, Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Ty.apply]
  have callerSemantic :
      (resultCheckBlock binaryCallerGenerated
        (binaryScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          identitySolution := by
    constructor <;>
      simp [resultCheckBlock, binaryCallerGenerated, binaryScheme,
        identitySolution, Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Ty.apply]
  have conjoinChecked := checked_body_isSome conjoin_elaboration_exact
    (solution := identitySolution) (by rfl) conjoinSemantic
  have callerChecked := checked_body_isSome binaryCaller_elaboration_exact
    (solution := identitySolution) (by rfl) callerSemantic
  simpa [compoundSources, conjoinSource, binaryCallerSource, binaryScheme,
    checkBodies] using And.intro conjoinChecked callerChecked

set_option maxRecDepth 100000 in
theorem public_compound_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed compoundSources).isSome = true := by
  have names :
      (compoundSources.map PatternFunctionSourceDefinition.name).Nodup := by
    decide
  have closed : interfacesClosed compoundSources = true := by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed,
    dif_pos compound_bodies_checked]
  rfl

def frozenCompound : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed compoundSources).get
      public_compound_freeze_succeeds

theorem public_compound_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed compoundSources = some frozenCompound := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed compoundSources with
  | none =>
      have success := public_compound_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenCompound, frozenEq]

def conjoinDefinition : PatternFunctionDefinition :=
  { name := conjoinName
    parameterCount := 2
    body := .and (.embed 0) (.embed 1) }

def binaryCallerDefinition : PatternFunctionDefinition :=
  { name := binaryCallerName
    parameterCount := 2
    body := .app conjoinName [.embed 0, .embed 1] }

theorem frozenCompound_definitions_exact :
    frozenCompound.definitions =
      [conjoinDefinition, binaryCallerDefinition] := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenCompound) public_compound_freeze_exact
  simpa [PatternFunctionFreeze.definitions, compoundSources, conjoinSource,
    binaryCallerSource, PatternFunctionSourceDefinition.runtimeDefinition,
    conjoinDefinition, binaryCallerDefinition, binaryScheme] using definitionsEq

theorem frozenCompound_conjoin_lookup :
    frozenCompound.definitions.lookup conjoinName = some conjoinDefinition := by
  rw [frozenCompound_definitions_exact]
  rfl

theorem frozenCompound_caller_lookup :
    frozenCompound.definitions.lookup binaryCallerName =
      some binaryCallerDefinition := by
  rw [frozenCompound_definitions_exact]
  rfl

def compoundInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app conjoinName [.var, .wild], .something, .int 31⟩],
    [], []⟩

def compoundConjoinPlan :
    CheckedBodyAtomPlan frozenCompound.signature frozenCompound.definitions
      [] [.var, .wild] []
      ⟨.and (.embed 0) (.embed 1), .something, .int 31⟩ [.int] :=
  CheckedBodyAtomPlan.expand CheckedBodyAtomExpansion.and
    (CheckedBodyAtomsPlan.cons
      (CheckedBodyAtomPlan.parameter rfl
        (.ordinary
          (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 31)))
          .nil))
      (CheckedBodyAtomsPlan.cons
        (CheckedBodyAtomPlan.parameter rfl
          (.ordinary
            (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingWild (.int 31)))
            .nil))
        CheckedBodyAtomsPlan.nil))

theorem compoundInitialState_checked :
    CheckedScopedStateTyping frozenCompound.signature
      frozenCompound.definitions compoundInitialState [.int] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfBodyPlan frozenCompound.agreement
    frozenCompound_conjoin_lookup rfl compoundConjoinPlan .nil

theorem public_frozen_compound_scoped_dfs_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenCompound.definitions variableOnlyReducer)
      20 [compoundInitialState] = .ok [[.int 31]] := by
  rw [frozenCompound_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_compound_scoped_dfs_typed :
    TypedMatchingSearchResult [.int]
      (depthFirstFuel
        (stepPatternFunctionState frozenCompound.definitions variableOnlyReducer)
        20 [compoundInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    variableOnlyReducer_checkedSafe variableOnlyReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact compoundInitialState_checked

theorem public_frozen_compound_scoped_dfs_never_stuck :
    (depthFirstFuel
      (stepPatternFunctionState frozenCompound.definitions variableOnlyReducer)
      20 [compoundInitialState]).NotStuck := by
  rw [public_frozen_compound_scoped_dfs_exact]
  simp [FuelResult.NotStuck]

/-! ## Three parameters through tuple and nested conjunction -/

def tripleName : PatternFunName := ⟨"tripleBody"⟩

def tripleScheme : DualScheme :=
  { tyArity := 0
    capArity := 0
    fields := [⟨.any, .int⟩, ⟨.any, .int⟩, ⟨.any, .int⟩]
    result := ⟨.prod [.any, .any], .prod [.int, .int]⟩
    fieldsWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped]
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped] }

def tripleBody : Pattern :=
  .tuple [.and (.embed 0) (.embed 1), .embed 2]

def tripleSource : PatternFunctionSourceDefinition :=
  { name := tripleName, scheme := tripleScheme, body := tripleBody }

def tripleSources : List PatternFunctionSourceDefinition := [tripleSource]

def tripleGenerated : GeneratedPattern :=
  { dual := ⟨.prod [.any, .any], .prod [.int, .int]⟩
    bindings := []
    hard := [.ty .int .int, .cap .any .any]
    pending := [] }

theorem triple_elaboration_exact :
    elaboratePattern
      (PatternFunctionFreeze.signature Paper1Signature.signature tripleSources)
      [] (tripleScheme.instantiate ⟨0, 0⟩).1.fields tripleBody []
      (tripleScheme.instantiate ⟨0, 0⟩).2 =
        some (tripleGenerated, ⟨0, 0⟩) := by
  simp [tripleSources, tripleSource, tripleScheme, tripleBody, tripleGenerated,
    elaboratePattern, elaboratePatterns, DualScheme.instantiate,
    PolyDual.openBound, PolyCap.openBound, PolyTy.openBound,
    Scheme.boundTyInstance, Scheme.boundCapInstance,
    Pattern.dualEquations, Dual.capabilities, Dual.targets]

theorem triple_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature tripleSources)
      tripleSources = true := by
  have semantic :
      (resultCheckBlock tripleGenerated
        (tripleScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          identitySolution := by
    constructor <;>
      simp [resultCheckBlock, tripleGenerated, tripleScheme, identitySolution,
        Pattern.dualEquations, Solves, Equation.Holds,
        DualScheme.instantiate, PolyDual.openBound, PolyCap.openBound,
        PolyTy.openBound, PolyTy.openBoundList, PolyCap.openBoundList,
        Scheme.boundTyInstance, Scheme.boundCapInstance,
        Cap.apply, Cap.applyList, Ty.apply, Ty.applyList]
  have checked := checked_body_isSome triple_elaboration_exact
    (solution := identitySolution) (by rfl) semantic
  simpa [tripleSources, tripleSource, checkBodies] using checked

set_option maxRecDepth 100000 in
theorem public_triple_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed tripleSources).isSome = true := by
  have names : (tripleSources.map PatternFunctionSourceDefinition.name).Nodup :=
    by decide
  have closed : interfacesClosed tripleSources = true := by rfl
  rw [freezePatternFunctions, dif_pos names, dif_pos closed,
    dif_pos triple_bodies_checked]
  rfl

def frozenTriple : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed tripleSources).get public_triple_freeze_succeeds

theorem public_triple_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed tripleSources = some frozenTriple := by
  cases frozenEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed tripleSources with
  | none =>
      have success := public_triple_freeze_succeeds
      rw [frozenEq] at success
      contradiction
  | some program => simp [frozenTriple, frozenEq]

def tripleDefinition : PatternFunctionDefinition :=
  { name := tripleName, parameterCount := 3, body := tripleBody }

theorem frozenTriple_definitions_exact :
    frozenTriple.definitions = [tripleDefinition] := by
  have definitionsEq := freezePatternFunctions_definitions
    (program := frozenTriple) public_triple_freeze_exact
  simpa [PatternFunctionFreeze.definitions, tripleSources, tripleSource,
    PatternFunctionSourceDefinition.runtimeDefinition, tripleDefinition,
    tripleScheme] using definitionsEq

theorem frozenTriple_lookup :
    frozenTriple.definitions.lookup tripleName = some tripleDefinition := by
  rw [frozenTriple_definitions_exact]
  rfl

def tripleBodyPlan :
    CheckedBodyAtomPlan frozenTriple.signature frozenTriple.definitions
      [] [.var, .wild, .var] []
      ⟨tripleBody, .tuple [.something, .something],
        .tuple [.int 41, .int 42]⟩ [.int, .int] :=
  CheckedBodyAtomPlan.expand
    (CheckedBodyAtomExpansion.tuple (atoms := [
      ⟨.and (.embed 0) (.embed 1), .something, .int 41⟩,
      ⟨.embed 2, .something, .int 42⟩]) rfl)
    (CheckedBodyAtomsPlan.cons
      (CheckedBodyAtomPlan.expand CheckedBodyAtomExpansion.and
        (CheckedBodyAtomsPlan.cons
          (CheckedBodyAtomPlan.parameter rfl
            (.ordinary
              (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 41)))
              .nil))
          (CheckedBodyAtomsPlan.cons
            (CheckedBodyAtomPlan.parameter rfl
              (.ordinary
                (CheckedOrdinaryAtomTyping.ofBuiltin
                  (.somethingWild (.int 41))) .nil))
            CheckedBodyAtomsPlan.nil)))
      (CheckedBodyAtomsPlan.cons
        (CheckedBodyAtomPlan.parameter rfl
          (.ordinary
            (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 42)))
            .nil))
        CheckedBodyAtomsPlan.nil))

def tripleInitialState : PatternFunctionState :=
  ⟨[.atom ⟨.app tripleName [.var, .wild, .var],
      .tuple [.something, .something], .tuple [.int 41, .int 42]⟩], [], []⟩

theorem tripleInitialState_checked :
    CheckedScopedStateTyping frozenTriple.signature frozenTriple.definitions
      tripleInitialState [.int, .int] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfBodyPlan frozenTriple.agreement
    frozenTriple_lookup rfl tripleBodyPlan .nil

theorem public_frozen_triple_scoped_dfs_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenTriple.definitions variableOnlyReducer)
      20 [tripleInitialState] = .ok [[.int 41, .int 42]] := by
  rw [frozenTriple_definitions_exact]
  with_unfolding_all rfl

theorem public_frozen_triple_scoped_dfs_typed :
    TypedMatchingSearchResult [.int, .int]
      (depthFirstFuel
        (stepPatternFunctionState frozenTriple.definitions variableOnlyReducer)
        20 [tripleInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    variableOnlyReducer_checkedSafe variableOnlyReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact tripleInitialState_checked

theorem public_frozen_triple_scoped_dfs_never_stuck :
    (depthFirstFuel
      (stepPatternFunctionState frozenTriple.definitions variableOnlyReducer)
      20 [tripleInitialState]).NotStuck := by
  rw [public_frozen_triple_scoped_dfs_exact]
  trivial

end TypePM.PatternFunctionSafetyRegression
