import TypePM.Source.SupplyWellFormed

/-!
# Freshness-scoped full-M2 principality

Acceptance completeness only says that executable elaboration produces a
solvable block.  Global principality additionally needs to compare the
principal target of that block with the principal target selected by the
relational elaboration.  This file states that per-derivation correspondence
directly and derives all public principality consequences from its
freshness-safe form.  Arbitrary starting supplies are intentionally excluded:
they may collide with free context variables.
-/

namespace TypePM.Source

/-- The executable representative corresponding to one relational
elaboration and one selected principal closure.  This is acceptance
completeness strengthened by exactly the two target-instance maps needed for
global principality; it does not require the two generated blocks or their
closure substitutions to be equal. -/
def PrincipalElaborationCorrespondence
    {signature : Signature} {context : Context} {expression : Expr} {supply next : Supply}
    {generated : TypePM.Generated}
    (_derivation : Elaborates signature context expression supply generated next)
    (closure : PrincipalBlockClosure generated) : Prop :=
  ∃ (computed : TypePM.Generated) (computedNext : Supply),
    elaborate signature context expression supply = some (computed, computedNext) ∧
      ∃ computedClosure : PrincipalBlockClosure computed,
        IsInstance computedClosure.target closure.target ∧
          IsInstance closure.target computedClosure.target

private theorem isInstance_trans
    {first second third : Ty}
    (firstToSecond : IsInstance first second)
    (secondToThird : IsInstance second third) :
    IsInstance first third := by
  obtain ⟨firstSubstitution, firstEquality⟩ := firstToSecond
  obtain ⟨secondSubstitution, secondEquality⟩ := secondToThird
  refine ⟨Subst.compose secondSubstitution firstSubstitution, ?_⟩
  rw [← Ty.apply_compose, firstEquality, secondEquality]

namespace PrincipalElaborationCorrespondence

/-- Literal replay is the trivial correspondence case.  Thus ordinary
constructors add no target-level obligation when their recursive
elaborations replay literally; only a representative-changing `letE` can
force use of the general premise. -/
theorem of_replay
    {signature : Signature} {context : Context} {expression : Expr} {supply next : Supply}
    {generated : TypePM.Generated}
    (derivation : Elaborates signature context expression supply generated next)
    (closure : PrincipalBlockClosure generated)
    (replay : elaborate signature context expression supply = some (generated, next)) :
    PrincipalElaborationCorrespondence derivation closure := by
  exact ⟨generated, next, replay, closure,
    ⟨Subst.id, by simp⟩, ⟨Subst.id, by simp⟩⟩

/-- In particular, every let-free derivation has the required target
correspondence without any additional premise. -/
theorem of_letFree
    {signature : Signature} {context : Context} {expression : Expr} {supply next : Supply}
    {generated : TypePM.Generated}
    (derivation : Elaborates signature context expression supply generated next)
    (closure : PrincipalBlockClosure generated)
    (letFree : LetFree expression) :
    PrincipalElaborationCorrespondence derivation closure :=
  of_replay derivation closure (derivation.replay_of_letFree letFree)

end PrincipalElaborationCorrespondence

namespace PrincipalTyping

/-- Per-derivation target correspondence makes every blockwise-principal
typing agree in both directions with the deterministic inference result. -/
theorem agreesWithInference_of_wellFormedElaborationPrincipalityComplete
    (complete : WellFormedElaborationPrincipalityComplete)
    {signature : Signature} {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping signature context expression target) :
    AgreesWithInference principal := by
  rcases principal with ⟨derivation⟩
  obtain ⟨computed, computedNext, replay, computedClosure,
      targetInstances⟩ :=
    complete derivation.elaboration derivation.closure
      (Supply.wellFormedFor_initialSupply context) derivation.absorbing
  have closes :
      inferGeneratedUsing unify computed ≠ none :=
    computedClosure.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases closureResult : inferGeneratedUsing unify computed with
  | none => exact (closes closureResult).elim
  | some result =>
      obtain ⟨inferredClosure, _, inferredTargetEquality⟩ :=
        inferGeneratedUsing_principalBlockClosure
          (fun _ _ success => unify_mostGeneral success) closureResult
      have inferredInstances :=
        computedClosure.targets_mutualInstances inferredClosure
      have success : infer signature context expression = some result.target := by
        simp [infer, elaborateRoot, replay, closureResult]
      refine ⟨result.target, success, ?_, ?_⟩
      · rw [inferredTargetEquality, derivation.target_eq]
        exact isInstance_trans inferredInstances.2
          targetInstances.1
      · rw [inferredTargetEquality, derivation.target_eq]
        exact isInstance_trans targetInstances.2
          inferredInstances.1

end PrincipalTyping

/-- Freshness-safe principality correspondence also accepts every
declaratively typable program at the public `context.initialSupply`. -/
theorem Typing.infer_isSome_of_wellFormedElaborationPrincipalityComplete
    (complete : WellFormedElaborationPrincipalityComplete)
    {signature : Signature} {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing signature context expression target) :
    infer signature context expression ≠ none :=
  typing.infer_isSome_of_wellFormedElaborationAcceptanceComplete
    complete.toAcceptance

/-- The completed per-derivation correspondence gives full source
coherence. -/
theorem principalCoherence_of_wellFormedElaborationPrincipalityComplete
    (complete : WellFormedElaborationPrincipalityComplete)
    (signature : Signature) (context : Context) (expression : Expr) :
    PrincipalCoherence signature context expression :=
  principalCoherence_of_inferenceAgreement
    (fun principal =>
      principal.agreesWithInference_of_wellFormedElaborationPrincipalityComplete
        complete)

namespace Inference

/-- Under freshness-safe principality correspondence, public source
typability is equivalent to success of inference from
`context.initialSupply`. -/
theorem typable_iff_infer_isSome_of_wellFormedElaborationPrincipalityComplete
    (complete : WellFormedElaborationPrincipalityComplete)
    (signature : Signature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Typable signature context expression ↔ infer signature context expression ≠ none :=
  typable_iff_infer_isSome_of_wellFormedElaborationAcceptanceComplete
    complete.toAcceptance signature wellFormed context expression

/-- Public source typability is decidable under freshness-safe
principality correspondence. -/
def typableDecidable_of_wellFormedElaborationPrincipalityComplete
    (complete : WellFormedElaborationPrincipalityComplete)
    (signature : Signature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Decidable (Typable signature context expression) :=
  typableDecidable_of_wellFormedElaborationAcceptanceComplete
    complete.toAcceptance signature wellFormed context expression

/-- Under the single elaboration correspondence premise, every successful
full-M2 inference run is a globally principal source result. -/
theorem infer_success_principalResult_of_wellFormedElaborationPrincipalityComplete
    (complete : WellFormedElaborationPrincipalityComplete)
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer signature context expression = some target) :
    PrincipalResult signature context expression target :=
  infer_success_principalResult_of_coherence
    wellFormed
    (principalCoherence_of_wellFormedElaborationPrincipalityComplete
      complete signature context expression)
    success

/-- A blockwise-principal declarative witness is enough to run inference and
obtain its globally principal representative under the correspondence
premise. -/
theorem infer_principalResult_of_wellFormedElaborationPrincipalityComplete
    (complete : WellFormedElaborationPrincipalityComplete)
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {principal : Ty}
    (principalTyping : PrincipalTyping signature context expression principal) :
    ∃ inferred,
      infer signature context expression = some inferred ∧
        PrincipalResult signature context expression inferred := by
  obtain ⟨inferred, success, _, _⟩ :=
    principalTyping.agreesWithInference_of_wellFormedElaborationPrincipalityComplete
      complete
  exact ⟨inferred, success,
    infer_success_principalResult_of_wellFormedElaborationPrincipalityComplete
      complete wellFormed success⟩

end Inference

namespace PrincipalTyping

/-- Conditional full-M2 uniqueness: any two blockwise-principal results
differ only by a finite renaming on variables occurring in their targets. -/
theorem finiteRenamingEq_of_wellFormedElaborationPrincipalityComplete
    (complete : WellFormedElaborationPrincipalityComplete)
    {signature : Signature} {context : Context} {expression : Expr} {left right : Ty}
    (leftPrincipal : PrincipalTyping signature context expression left)
    (rightPrincipal : PrincipalTyping signature context expression right) :
    FiniteRenamingEq left right :=
  finiteRenamingEq_of_coherence
    (principalCoherence_of_wellFormedElaborationPrincipalityComplete
      complete signature context expression)
    leftPrincipal rightPrincipal

end PrincipalTyping

end TypePM.Source
