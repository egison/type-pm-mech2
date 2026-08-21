import TypePM.Source.M4RecursiveElaboration
import TypePM.Source.PolymorphicLetRuntimeBridge

/-!
# The M4 `letE` source/runtime-world step

This module isolates the first genuinely context-changing constructor needed by
a future class-wide Paper 1 runtime-certificate induction.  It decomposes the
exact fuel-indexed M4 `letE` rule, retains the right-hand-side principal block
closure chosen by that rule, and constructs the source/runtime context world in
which the body must be certified.

The `fuel` parameter below is only the structural fuel of
`M4.ElaboratesFuel`.  No evaluator fuel, search fuel, logical result index,
completed evaluation, or completed search result is stored in this world.
-/

namespace TypePM.Source.M4

open TypePM.Runtime

/-- The nonempty body world exposed by one exact M4 `letE` elaboration.

The source body context is closed by the right-hand-side principal
substitution and extended by its generalized scheme.  The runtime context is
extended by one canonical monotype for that scheme; the `true` provenance bit
records that later occurrences may instantiate this protected binding.

This structure contains only static elaboration and context evidence.  Future
runtime-preservation induction hypotheses can consume `valueElaboration` and
`bodyElaboration` without assuming either subexpression's evaluation result. -/
structure LetRuntimeWorld
    {signature : FrozenSignature} {context : Context}
    {value body : Expr} {supply : Supply} {generated : Generated}
    {next : Supply} (fuel : Nat) (solution : Subst)
    (runtimeContext : List Ty) (provenance : List Bool) : Type where
  valueGenerated : Generated
  afterValue : Supply
  valueElaboration :
    ElaboratesFuel signature fuel context value supply valueGenerated afterValue
  valueClosure : PrincipalBlockClosure valueGenerated
  valueAbsorbing : valueClosure.Absorbing
  bodyGenerated : Generated
  bodyElaboration :
    ElaboratesFuel signature fuel
      ((context.applyFree valueClosure.substitution).generalize
          valueClosure.target :: context.applyFree valueClosure.substitution)
      body
      (afterValue.join
        (context.applyFree valueClosure.substitution).initialSupply)
      bodyGenerated next
  generated_eq :
    generated = Generated.fromLet
      (context.interfaceEquations valueClosure.substitution) bodyGenerated
  interfaceSolved :
    Solves solution (context.interfaceEquations valueClosure.substitution)
  bodySemantic : bodyGenerated.SemanticSolution solution
  outerContextCompatible :
    ProtectedContextCompatible context runtimeContext provenance solution
  outerSourceRuntimeLength : context.length = runtimeContext.length
  outerRuntimeProvenanceLength : runtimeContext.length = provenance.length
  closedContextCompatible :
    ProtectedContextCompatible
      (context.applyFree valueClosure.substitution)
      runtimeContext provenance solution
  bodyContextCompatible :
    ProtectedContextCompatible
      ((context.applyFree valueClosure.substitution).generalize
          valueClosure.target :: context.applyFree valueClosure.substitution)
      ((((context.applyFree valueClosure.substitution).generalize
          valueClosure.target).instantiate
            (context.applyFree valueClosure.substitution).initialSupply).1 ::
        runtimeContext)
      (true :: provenance) solution
  bodySourceRuntimeLength :
    (((context.applyFree valueClosure.substitution).generalize
          valueClosure.target :: context.applyFree valueClosure.substitution).length) =
      (((((context.applyFree valueClosure.substitution).generalize
          valueClosure.target).instantiate
            (context.applyFree valueClosure.substitution).initialSupply).1 ::
        runtimeContext).length)
  bodyRuntimeProvenanceLength :
    (((((context.applyFree valueClosure.substitution).generalize
          valueClosure.target).instantiate
            (context.applyFree valueClosure.substitution).initialSupply).1 ::
        runtimeContext).length) =
      (true :: provenance).length

private theorem semanticSolution_fromLet_interface
    {effects : List Equation} {bodyGenerated : Generated}
    (semantic : (Generated.fromLet effects bodyGenerated).SemanticSolution
      solution) :
    Solves solution effects := by
  intro equation membership
  exact semantic.1 equation (by
    simp [Generated.fromLet, membership])

private theorem semanticSolution_fromLet_body
    {effects : List Equation} {bodyGenerated : Generated}
    (semantic : (Generated.fromLet effects bodyGenerated).SemanticSolution
      solution) :
    bodyGenerated.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [Generated.fromLet, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simpa [Generated.fromLet] using membership)

/-- Decompose one exact positive-fuel M4 `letE` rule and extend its compatible
source/runtime context world for the body.

The three substitutions have distinct roles: `valueClosure.substitution`
closes the right-hand-side block, `solution` solves the enclosing block, and
the canonical scheme instantiation selects the single monotype stored in the
runtime context. -/
theorem ElaboratesFuel.letE_runtimeWorld
    (elaboration : ElaboratesFuel signature (fuel + 1) context
      (.letE value body) supply generated next)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : ProtectedContextCompatible context runtimeContext
      provenance solution)
    (sourceRuntimeLength : context.length = runtimeContext.length)
    (runtimeProvenanceLength : runtimeContext.length = provenance.length) :
    Nonempty
      (LetRuntimeWorld (signature := signature) (context := context)
        (value := value) (body := body) (supply := supply)
        (generated := generated) (next := next) fuel solution runtimeContext
        provenance) := by
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨valueGenerated, afterValue, valueElaboration, valueClosure,
    bodyGenerated, valueAbsorbing, bodyElaboration, generatedEq⟩ := elaboration
  have parentSemantic :
      (Generated.fromLet
        (context.interfaceEquations valueClosure.substitution)
        bodyGenerated).SemanticSolution solution := by
    simpa [generatedEq] using semantic
  have interfaceSolved :
      Solves solution
        (context.interfaceEquations valueClosure.substitution) :=
    semanticSolution_fromLet_interface parentSemantic
  have bodySemantic : bodyGenerated.SemanticSolution solution :=
    semanticSolution_fromLet_body parentSemantic
  have closedSourceRuntimeLength :
      (context.applyFree valueClosure.substitution).length =
        runtimeContext.length := by
    simpa [Context.applyFree] using sourceRuntimeLength
  have closedContextCompatible :
      ProtectedContextCompatible
        (context.applyFree valueClosure.substitution)
        runtimeContext provenance solution :=
    contextCompatible.ofApplyFreeInterface interfaceSolved
  have bodyContextCompatible :
      ProtectedContextCompatible
        ((context.applyFree valueClosure.substitution).generalize
            valueClosure.target :: context.applyFree valueClosure.substitution)
        ((((context.applyFree valueClosure.substitution).generalize
            valueClosure.target).instantiate
              (context.applyFree valueClosure.substitution).initialSupply).1 ::
          runtimeContext)
        (true :: provenance) solution := by
    apply ProtectedContextCompatible.pushCanonical
      (canonicalSupply :=
        (context.applyFree valueClosure.substitution).initialSupply)
    · intro index membership
      exact Context.freeTyVar_lt_initialSupply
        ((Context.mem_generalize_freeTyVars.mp membership).2)
    · intro index membership
      exact Context.freeCapVar_lt_initialSupply
        ((Context.mem_generalize_freeCapVars.mp membership).2)
    · exact closedContextCompatible
  have bodySourceRuntimeLength :
      (((context.applyFree valueClosure.substitution).generalize
            valueClosure.target :: context.applyFree valueClosure.substitution).length) =
        (((((context.applyFree valueClosure.substitution).generalize
            valueClosure.target).instantiate
              (context.applyFree valueClosure.substitution).initialSupply).1 ::
          runtimeContext).length) := by
    simpa only [List.length_cons] using
      congrArg Nat.succ closedSourceRuntimeLength
  have bodyRuntimeProvenanceLength :
      (((((context.applyFree valueClosure.substitution).generalize
            valueClosure.target).instantiate
              (context.applyFree valueClosure.substitution).initialSupply).1 ::
          runtimeContext).length) =
        (true :: provenance).length := by
    simpa only [List.length_cons] using
      congrArg Nat.succ runtimeProvenanceLength
  exact ⟨
    { valueGenerated := valueGenerated
      afterValue := afterValue
      valueElaboration := valueElaboration
      valueClosure := valueClosure
      valueAbsorbing := valueAbsorbing
      bodyGenerated := bodyGenerated
      bodyElaboration := bodyElaboration
      generated_eq := generatedEq
      interfaceSolved := interfaceSolved
      bodySemantic := bodySemantic
      outerContextCompatible := contextCompatible
      outerSourceRuntimeLength := sourceRuntimeLength
      outerRuntimeProvenanceLength := runtimeProvenanceLength
      closedContextCompatible := closedContextCompatible
      bodyContextCompatible := bodyContextCompatible
      bodySourceRuntimeLength := bodySourceRuntimeLength
      bodyRuntimeProvenanceLength := bodyRuntimeProvenanceLength }⟩

/-- Existential packaging for an exact principal M4 `letE` derivation.

This is the entry point expected by a future certificate induction: it opens
the hidden static-fuel witness, uses the enclosing principal closure as the
semantic solution, and returns a body world whose runtime context is genuinely
one element longer. -/
theorem PrincipalTypingDerivation.letE_runtimeWorld
    (derivation : PrincipalTypingDerivation signature context
      (.letE value body) principal)
    (contextCompatible : ProtectedContextCompatible context runtimeContext
      provenance derivation.closure.substitution)
    (sourceRuntimeLength : context.length = runtimeContext.length)
    (runtimeProvenanceLength : runtimeContext.length = provenance.length) :
    ∃ fuel,
      Nonempty
        (LetRuntimeWorld (signature := signature) (context := context)
          (value := value) (body := body) (supply := context.initialSupply)
          (generated := derivation.generated) (next := derivation.next)
          fuel derivation.closure.substitution runtimeContext provenance) := by
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  cases staticFuel with
  | zero => simp [ElaboratesFuel] at elaboration
  | succ fuel =>
      exact ⟨fuel,
        elaboration.letE_runtimeWorld
          (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
            derivation.closure)
          contextCompatible sourceRuntimeLength runtimeProvenanceLength⟩

end TypePM.Source.M4
