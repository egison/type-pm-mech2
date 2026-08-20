import TypePM.BlockClosure
import TypePM.Source.PatternFunctionDefinition

/-!
# Executable freezing of source-defined pattern functions

This module is the public boundary promised by PF5.  A caller supplies a
well-formed base signature and source entries containing both the declared
dual scheme and the pattern body.  `freezePatternFunctions` first builds the
complete interface table, then checks every body at the scheme's canonical
bound-index instance.  On success it returns the frozen source signature, the
runtime body table, and their `PatternFunctionDefinitions.Agree` certificate.

The check is deliberately limited to the canonical instance used by
`PatternFunctionDefinition.Checked`; it does not claim all-instance agreement
or pattern-function principality.
-/

namespace TypePM.Source

/-- One source-level input to the freeze checker.  The parameter count exposed
to the runtime is determined by the declared interface. -/
structure PatternFunctionSourceDefinition where
  name : PatternFunName
  scheme : DualScheme
  body : Pattern
deriving Repr

namespace PatternFunctionSourceDefinition

def declaration (source : PatternFunctionSourceDefinition) :
    PatternFunctionDeclaration :=
  ⟨source.name, source.scheme⟩

def runtimeDefinition (source : PatternFunctionSourceDefinition) :
    PatternFunctionDefinition :=
  { name := source.name
    parameterCount := source.scheme.fields.length
    body := source.body }

end PatternFunctionSourceDefinition

/-- The two tables and their proof of source/runtime agreement.  This package
can be passed directly to the checked MNode evaluator. -/
structure FrozenPatternFunctionProgram where
  signature : FrozenSignature
  definitions : PatternFunctionDefinitions
  agreement : definitions.Agree signature

namespace PatternFunctionFreeze

def signature (base : Signature)
    (sources : List PatternFunctionSourceDefinition) : FrozenSignature :=
  { base := base
    patternFunctions := sources.map
      PatternFunctionSourceDefinition.declaration }

def definitions (sources : List PatternFunctionSourceDefinition) :
    PatternFunctionDefinitions :=
  sources.map PatternFunctionSourceDefinition.runtimeDefinition

/-- Constraint block used to compare a generated body with its declared
result. -/
def resultCheckBlock (generated : GeneratedPattern)
    (expected : Dual) : Generated :=
  { target := generated.dual.target
    hard := generated.hard ++ Pattern.dualEquations generated.dual expected
    pending := generated.pending }

/-- Computational evidence retained from one successful body check. -/
structure BodyCheckResult where
  generated : GeneratedPattern
  next : Supply
  solution : Subst

/-- Check one body at the declaration's canonical bound-index instance. -/
def checkBody (signature : FrozenSignature) (scheme : DualScheme)
    (body : Pattern) : Option BodyCheckResult := do
  let instantiated := scheme.instantiate ⟨0, 0⟩
  let (generated, next) ← elaboratePattern signature [] instantiated.1.fields
    body [] instantiated.2
  let closed ← inferGeneratedUsing unify
    (resultCheckBlock generated instantiated.1.result)
  pure ⟨generated, next, closed.substitution⟩

/-- Check every source body against the already frozen complete interface
table. -/
def checkBodies (signature : FrozenSignature) :
    List PatternFunctionSourceDefinition → Bool
  | [] => true
  | source :: sources =>
      (checkBody signature source.scheme source.body).isSome &&
        checkBodies signature sources

private theorem principalBlockClosure_semanticSolution
    {generated : Generated} (closure : PrincipalBlockClosure generated) :
    generated.SemanticSolution closure.substitution := by
  have finalHardSolved : Solves closure.substitution closure.finalHard :=
    closure.finalHard_solved
  constructor
  · intro equation membership
    exact finalHardSolved equation
      (closure.saturation.closure.hard_mem_final equation membership)
  · intro obligation membership
    rcases closure.saturation.closure.pending_covered obligation membership with
      retained | promoted
    · exact closure.remaining_checkConversion obligation retained
    · have equality := finalHardSolved
        (.ty obligation.source obligation.expected) promoted
      simp only [Equation.Holds] at equality
      rw [equality]
      exact ⟨.ordinary, .ordinary⟩

private theorem inferGeneratedUsing_semanticSolution
    {generated : Generated} {result : InferenceResult}
    (success : inferGeneratedUsing unify generated = some result) :
    generated.SemanticSolution result.substitution := by
  obtain ⟨closure, substitutionEq, _targetEq⟩ :=
    inferGeneratedUsing_principalBlockClosure
      (fun _ _ solverSuccess => unify_mostGeneral solverSuccess) success
  rw [substitutionEq]
  exact principalBlockClosure_semanticSolution closure

theorem checkBody_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {scheme : DualScheme} {body : Pattern} {result : BodyCheckResult}
    (success : checkBody signature scheme body = some result) :
    ∃ generated next solution,
      result = ⟨generated, next, solution⟩ ∧
      PatternElaborates signature [] (scheme.instantiate ⟨0, 0⟩).1.fields
        body [] (scheme.instantiate ⟨0, 0⟩).2 generated next ∧
      generated.SemanticSolution solution ∧
      generated.dual.capability.apply solution.cap =
        (scheme.instantiate ⟨0, 0⟩).1.result.capability.apply solution.cap ∧
      generated.dual.target.apply solution =
        (scheme.instantiate ⟨0, 0⟩).1.result.target.apply solution := by
  unfold checkBody at success
  generalize instantiatedEq : scheme.instantiate ⟨0, 0⟩ = instantiated at success
  cases elaborationEq : elaboratePattern signature [] instantiated.1.fields body []
      instantiated.2 with
  | none => simp [elaborationEq] at success
  | some output =>
      rcases output with ⟨generated, next⟩
      cases closureEq : inferGeneratedUsing unify
          (resultCheckBlock generated instantiated.1.result) with
      | none => simp [elaborationEq, closureEq] at success
      | some closed =>
          simp [elaborationEq, closureEq] at success
          subst result
          have elaborates : PatternElaborates signature [] instantiated.1.fields
              body [] instantiated.2 generated next :=
            elaboratePattern_sound wellFormed elaborationEq
          have semantic := inferGeneratedUsing_semanticSolution closureEq
          have hardSolved := semantic.1
          have split := (solves_append closed.substitution generated.hard
            (Pattern.dualEquations generated.dual instantiated.1.result)).mp
              hardSolved
          have generatedSemantic : generated.SemanticSolution
              closed.substitution := ⟨split.1, semantic.2⟩
          have resultEqualities := split.2
          simp only [Pattern.dualEquations, solves_cons, solves_nil,
            Equation.Holds, and_true] at resultEqualities
          subst instantiated
          exact ⟨generated, next, closed.substitution, rfl, elaborates,
            generatedSemantic, resultEqualities.2, resultEqualities.1⟩

private theorem lookup_source
    {base : Signature} {sources : List PatternFunctionSourceDefinition}
    (namesNodup : (sources.map PatternFunctionSourceDefinition.name).Nodup)
    {source : PatternFunctionSourceDefinition} (member : source ∈ sources) :
    (signature base sources).lookupPatternFunction source.name =
      some source.scheme := by
  induction sources with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at namesNodup
      rcases namesNodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [signature, FrozenSignature.lookupPatternFunction,
          PatternFunctionSourceDefinition.declaration]
      · have different : head.name ≠ source.name := by
          intro equality
          apply headFresh
          rw [equality]
          exact List.mem_map.mpr ⟨source, member, rfl⟩
        simpa [signature, FrozenSignature.lookupPatternFunction,
          PatternFunctionSourceDefinition.declaration, different] using
          induction tailNodup member

private theorem checkBodies_member
    {signature : FrozenSignature}
    {sources : List PatternFunctionSourceDefinition}
    (checked : checkBodies signature sources = true)
    {source : PatternFunctionSourceDefinition} (member : source ∈ sources) :
    ∃ result, checkBody signature source.scheme source.body = some result := by
  induction sources with
  | nil => simp at member
  | cons head tail induction =>
      simp only [checkBodies, Bool.and_eq_true] at checked
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Option.isSome_iff_exists.mp checked.1
      · exact induction checked.2 member

private theorem checkBodies_checked
    {base : Signature} {sources : List PatternFunctionSourceDefinition}
    (wellFormed : (signature base sources).WellFormed)
    (namesNodup : (sources.map PatternFunctionSourceDefinition.name).Nodup)
    (checked : checkBodies (signature base sources) sources = true)
    {source : PatternFunctionSourceDefinition} (member : source ∈ sources) :
    Nonempty
      ((PatternFunctionSourceDefinition.runtimeDefinition source).Checked
        (signature base sources)) := by
  obtain ⟨bodyResult, bodySuccess⟩ := checkBodies_member checked member
  obtain ⟨generated, next, solution, rfl, elaborates, semantic,
      capabilityEq, targetEq⟩ := checkBody_sound wellFormed bodySuccess
  exact ⟨
    { scheme := source.scheme
      lookup := lookup_source namesNodup member
      arity := rfl
      generated := generated
      next := next
      bodyElaboration := elaborates
      solution := solution
      semanticSolution := semantic
      resultCapability_eq := capabilityEq
      resultTarget_eq := targetEq }⟩

/-- Executable closedness check for the finite interface list. -/
def interfaceClosed (source : PatternFunctionSourceDefinition) : Bool :=
  source.scheme.freeTyVars == [] && source.scheme.freeCapVars == []

def interfacesClosed (sources : List PatternFunctionSourceDefinition) : Bool :=
  sources.all interfaceClosed

private theorem interfacesClosed_sound
    {sources : List PatternFunctionSourceDefinition}
    (success : interfacesClosed sources = true) :
    ∀ source ∈ sources, source.scheme.Closed := by
  intro source member
  have all := (List.all_eq_true.mp success) source member
  simpa [interfaceClosed, DualScheme.Closed] using all

private theorem signature_wellFormed
    {base : Signature} (baseWellFormed : base.WellFormed)
    {sources : List PatternFunctionSourceDefinition}
    (namesNodup : (sources.map PatternFunctionSourceDefinition.name).Nodup)
    (closed : ∀ source ∈ sources, source.scheme.Closed) :
    (signature base sources).WellFormed := by
  refine
    { baseWellFormed := baseWellFormed
      patternFunctionNodup := ?_
      patternFunctionClosed := ?_
      patternFunctionWellFormed := ?_ }
  · simpa [signature, PatternFunctionSourceDefinition.declaration,
      Function.comp_def] using namesNodup
  · intro declaration member
    simp only [signature, List.mem_map] at member
    obtain ⟨source, sourceMember, rfl⟩ := member
    exact closed source sourceMember
  · intro declaration member
    simp only [signature, List.mem_map] at member
    obtain ⟨source, _sourceMember, rfl⟩ := member
    exact source.scheme.wellFormed

private theorem definitions_agree
    {base : Signature} (baseWellFormed : base.WellFormed)
    {sources : List PatternFunctionSourceDefinition}
    (namesNodup : (sources.map PatternFunctionSourceDefinition.name).Nodup)
    (closed : ∀ source ∈ sources, source.scheme.Closed)
    (checked : checkBodies (signature base sources) sources = true) :
    (definitions sources).Agree (signature base sources) := by
  have signatureWellFormed := signature_wellFormed baseWellFormed namesNodup closed
  refine
    { signatureWellFormed := signatureWellFormed
      namesNodup := ?_
      runtimeChecked := ?_
      sourceImplemented := ?_ }
  · simpa [definitions, PatternFunctionSourceDefinition.runtimeDefinition,
      Function.comp_def] using namesNodup
  · intro definition member
    simp only [definitions, List.mem_map] at member
    obtain ⟨source, sourceMember, rfl⟩ := member
    exact checkBodies_checked signatureWellFormed namesNodup checked sourceMember
  · intro declaration member
    simp only [signature, List.mem_map] at member
    obtain ⟨source, sourceMember, rfl⟩ := member
    exact ⟨source.runtimeDefinition, by
      exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩, rfl⟩

/-- Public executable freeze checker.  `none` reports a duplicate name, an
open interface, or a body that fails canonical-instance generation or
constraint solving.  A successful package is ready for
`Runtime.evalCheckedPatternFunctionNodesFuel`. -/
def freezePatternFunctions
    (base : Signature) (baseWellFormed : base.WellFormed)
    (sources : List PatternFunctionSourceDefinition) :
    Option FrozenPatternFunctionProgram :=
  if namesNodup :
      (sources.map PatternFunctionSourceDefinition.name).Nodup then
    if closedCheck : interfacesClosed sources = true then
      if checked : checkBodies (signature base sources) sources = true then
        some
          { signature := signature base sources
            definitions := definitions sources
            agreement := definitions_agree baseWellFormed namesNodup
              (interfacesClosed_sound closedCheck) checked }
      else none
    else none
  else none

/-- A successful freeze exposes exactly the interface table constructed from
the supplied source entries. -/
theorem freezePatternFunctions_signature
    {base : Signature} {baseWellFormed : base.WellFormed}
    {sources : List PatternFunctionSourceDefinition}
    {program : FrozenPatternFunctionProgram}
    (success : freezePatternFunctions base baseWellFormed sources =
      some program) :
    program.signature = signature base sources := by
  unfold freezePatternFunctions at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases Option.some.inj success
  rfl

/-- A successful freeze exposes exactly the runtime body table constructed
from the supplied source entries. -/
theorem freezePatternFunctions_definitions
    {base : Signature} {baseWellFormed : base.WellFormed}
    {sources : List PatternFunctionSourceDefinition}
    {program : FrozenPatternFunctionProgram}
    (success : freezePatternFunctions base baseWellFormed sources =
      some program) :
    program.definitions = definitions sources := by
  unfold freezePatternFunctions at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases Option.some.inj success
  rfl

end PatternFunctionFreeze
end TypePM.Source
