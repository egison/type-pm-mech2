import TypePM.Source.Principality

/-!
# Conditional full-M2 principality

Acceptance completeness only says that executable elaboration produces a
solvable block.  Global principality additionally needs to compare the
principal target of that block with the principal target selected by the
relational elaboration.  This file states that per-derivation correspondence
directly and derives all public principality consequences from it.
-/

namespace TypePM.Source

/-- The executable representative corresponding to one relational
elaboration and one selected principal closure.  This is acceptance
completeness strengthened by exactly the two target-instance maps needed for
global principality; it does not require the two generated blocks or their
closure substitutions to be equal. -/
def PrincipalElaborationCorrespondence
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : TypePM.Generated}
    (_derivation : Elaborates context expression supply generated next)
    (closure : PrincipalBlockClosure generated) : Prop :=
  ∃ (computed : TypePM.Generated) (computedNext : Supply),
    elaborate context expression supply = some (computed, computedNext) ∧
      ∃ computedClosure : PrincipalBlockClosure computed,
        IsInstance computedClosure.target closure.target ∧
          IsInstance closure.target computedClosure.target

/-- The sole conditional premise for full M2 principality: every absorbing
principal relational derivation has a corresponding executable principal
closure with a mutually instantiable target. -/
def ElaborationPrincipalityComplete : Prop :=
  ∀ {context : Context} {expression : Expr} {supply next : Supply}
      {generated : TypePM.Generated}
      (derivation : Elaborates context expression supply generated next)
      (closure : PrincipalBlockClosure generated),
    closure.Absorbing →
      PrincipalElaborationCorrespondence derivation closure

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
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : TypePM.Generated}
    (derivation : Elaborates context expression supply generated next)
    (closure : PrincipalBlockClosure generated)
    (replay : elaborate context expression supply = some (generated, next)) :
    PrincipalElaborationCorrespondence derivation closure := by
  exact ⟨generated, next, replay, closure,
    ⟨Subst.id, by simp⟩, ⟨Subst.id, by simp⟩⟩

/-- In particular, every let-free derivation has the required target
correspondence without any additional premise. -/
theorem of_letFree
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : TypePM.Generated}
    (derivation : Elaborates context expression supply generated next)
    (closure : PrincipalBlockClosure generated)
    (letFree : LetFree expression) :
    PrincipalElaborationCorrespondence derivation closure :=
  of_replay derivation closure (derivation.replay_of_letFree letFree)

end PrincipalElaborationCorrespondence

/-- The principality correspondence strictly contains the information needed
by acceptance completeness. -/
theorem ElaborationPrincipalityComplete.toAcceptanceComplete
    (complete : ElaborationPrincipalityComplete) :
    ElaborationAcceptanceComplete := by
  intro context expression supply next generated derivation closure absorbing
  obtain ⟨computed, computedNext, replay, computedClosure, _⟩ :=
    complete derivation closure absorbing
  exact ⟨computed, computedNext, replay,
    computedClosure.finalHard,
    computedClosure.finalPending,
    computedClosure.hardSubstitution,
    computedClosure.residualSubstitution,
    computedClosure.saturation,
    computedClosure.residualPrincipal.1⟩

namespace PrincipalTyping

/-- Per-derivation target correspondence makes every blockwise-principal
typing agree in both directions with the deterministic inference result. -/
theorem agreesWithInference_of_elaborationPrincipalityComplete
    (complete : ElaborationPrincipalityComplete)
    {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping context expression target) :
    AgreesWithInference principal := by
  rcases principal with ⟨derivation⟩
  obtain ⟨computed, computedNext, replay, computedClosure,
      targetInstances⟩ :=
    complete derivation.elaboration derivation.closure derivation.absorbing
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
      have success : infer context expression = some result.target := by
        simp [infer, elaborateRoot, replay, closureResult]
      refine ⟨result.target, success, ?_, ?_⟩
      · rw [inferredTargetEquality, derivation.target_eq]
        exact isInstance_trans inferredInstances.2
          targetInstances.1
      · rw [inferredTargetEquality, derivation.target_eq]
        exact isInstance_trans targetInstances.2
          inferredInstances.1

end PrincipalTyping

/-- The per-derivation correspondence premise closes the full source
coherence gap. -/
theorem principalCoherence_of_elaborationPrincipalityComplete
    (complete : ElaborationPrincipalityComplete)
    (context : Context) (expression : Expr) :
    PrincipalCoherence context expression :=
  principalCoherence_of_inferenceAgreement
    (fun principal =>
      principal.agreesWithInference_of_elaborationPrincipalityComplete
        complete)

namespace Inference

/-- Under the single elaboration correspondence premise, every successful
full-M2 inference run is a globally principal source result. -/
theorem infer_success_principalResult_of_elaborationPrincipalityComplete
    (complete : ElaborationPrincipalityComplete)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer context expression = some target) :
    PrincipalResult context expression target :=
  infer_success_principalResult_of_coherence
    (principalCoherence_of_elaborationPrincipalityComplete
      complete context expression)
    success

/-- A blockwise-principal declarative witness is enough to run inference and
obtain its globally principal representative under the correspondence
premise. -/
theorem infer_principalResult_of_elaborationPrincipalityComplete
    (complete : ElaborationPrincipalityComplete)
    {context : Context} {expression : Expr} {principal : Ty}
    (principalTyping : PrincipalTyping context expression principal) :
    ∃ inferred,
      infer context expression = some inferred ∧
        PrincipalResult context expression inferred := by
  obtain ⟨inferred, success, _, _⟩ :=
    principalTyping.agreesWithInference_of_elaborationPrincipalityComplete
      complete
  exact ⟨inferred, success,
    infer_success_principalResult_of_elaborationPrincipalityComplete
      complete success⟩

end Inference

namespace PrincipalTyping

/-- Conditional full-M2 uniqueness: any two blockwise-principal results
differ only by a finite renaming on variables occurring in their targets. -/
theorem finiteRenamingEq_of_elaborationPrincipalityComplete
    (complete : ElaborationPrincipalityComplete)
    {context : Context} {expression : Expr} {left right : Ty}
    (leftPrincipal : PrincipalTyping context expression left)
    (rightPrincipal : PrincipalTyping context expression right) :
    FiniteRenamingEq left right :=
  finiteRenamingEq_of_coherence
    (principalCoherence_of_elaborationPrincipalityComplete
      complete context expression)
    leftPrincipal rightPrincipal

end PrincipalTyping

end TypePM.Source
