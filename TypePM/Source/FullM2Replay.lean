import TypePM.Source.FullM2Coherence
import TypePM.Source.ConditionalPrincipality

/-!
# Executable replay from full M2 coherence

This module closes the gap between relational source elaboration and the
executable elaborator without assuming that the signature is well formed.
The executable run is replayed together with a fresh relational derivation;
constructor lookup facts and closedness evidence are inherited from the
given derivation rather than reconstructed from a signature invariant.
-/

namespace TypePM.Source

/-- A successful executable run, paired with a relational derivation of the
exact block and supply returned by that run. -/
def ExecutableElaborationReplay
    (signature : Signature) (context : Context) (expression : Expr)
    (supply : Supply) : Prop :=
  ∃ generated next,
    elaborate signature context expression supply = some (generated, next) ∧
      Elaborates signature context expression supply generated next

/-- List-valued counterpart of `ExecutableElaborationReplay`. -/
def ExecutableItemsReplay
    (signature : Signature) (context : Context) (expressions : List Expr)
    (supply : Supply) : Prop :=
  ∃ generated next,
    elaborateItems signature context expressions supply = some (generated, next) ∧
      ElaboratesItems signature context expressions supply generated next

/-- Call-fold counterpart of `ExecutableElaborationReplay`. -/
def ExecutableCallReplay
    (signature : Signature) (context : Context) (accumulated : Generated)
    (arguments : List Expr) (supply : Supply) : Prop :=
  ∃ generated next,
    elaborateCall signature context accumulated arguments supply =
        some (generated, next) ∧
      ElaboratesCall signature context accumulated arguments supply generated next

private theorem blockAccepts_of_principal
    {generated : Generated} (closure : PrincipalBlockClosure generated) :
    BlockAccepts generated :=
  ⟨closure.finalHard, closure.finalPending, closure.hardSubstitution,
    closure.residualSubstitution, closure.saturation,
    closure.residualPrincipal.1⟩

mutual

/-- Full M2 coherence makes every well-scoped relational elaboration
executable.  The returned derivation describes the executable result itself,
which is essential at an enclosing `letE`. -/
theorem Elaborates.executableReplay_of_fullM2
    (coherent : FullM2Coherence)
    {signature : Signature} {context : Context} {expression : Expr}
    {supply generated next}
    (derivation : Elaborates signature context expression supply generated next)
    (wellFormed : supply.WellFormedFor context) :
    ExecutableElaborationReplay signature context expression supply := by
  cases derivation with
  | var lookup =>
      exact ⟨_, _, by simp [elaborate, lookup], .var lookup⟩
  | lit =>
      exact ⟨_, _, by simp [elaborate], .lit⟩
  | something =>
      exact ⟨_, _, by simp [elaborate], .something⟩
  | lam bodyElaboration =>
      obtain ⟨computedBody, computedNext, bodyReplay, computedBodyElaboration⟩ :=
        bodyElaboration.executableReplay_of_fullM2 coherent
          wellFormed.monomorphic_cons_nextTy
      exact ⟨_, computedNext, by simp [elaborate, bodyReplay],
        .lam computedBodyElaboration⟩
  | app functionElaboration argumentElaboration =>
      obtain ⟨computedFunction, afterFunction, functionReplay,
          computedFunctionElaboration⟩ :=
        functionElaboration.executableReplay_of_fullM2 coherent wellFormed
      obtain ⟨functionCoherence⟩ := coherent _ wellFormed
        functionElaboration computedFunctionElaboration
      rw [functionCoherence.next_eq] at argumentElaboration
      obtain ⟨computedArgument, afterArgument, argumentReplay,
          computedArgumentElaboration⟩ :=
        argumentElaboration.executableReplay_of_fullM2 coherent
          (wellFormed.mono computedFunctionElaboration.supply_le_next)
      exact ⟨_, afterArgument.nextTy 2,
        by simp [elaborate, functionReplay, argumentReplay],
        .app computedFunctionElaboration computedArgumentElaboration⟩
  | tuple itemsElaboration =>
      obtain ⟨computedItems, computedNext, itemsReplay,
          computedItemsElaboration⟩ :=
        itemsElaboration.executableReplay_of_fullM2 coherent wellFormed
      exact ⟨_, computedNext, by simp [elaborate, itemsReplay],
        .tuple computedItemsElaboration⟩
  | letE valueElaboration closure absorbing bodyElaboration =>
      obtain ⟨computedValue, computedAfterValue, valueReplay,
          computedValueElaboration⟩ :=
        valueElaboration.executableReplay_of_fullM2 coherent wellFormed
      obtain ⟨valueCoherence⟩ := coherent _ wellFormed valueElaboration
        computedValueElaboration
      rw [valueCoherence.next_eq] at bodyElaboration
      have computedAccepts : BlockAccepts computedValue := by
        have transferred :=
          (valueCoherence.blockAccepts_iff .hole trivial).mp
            (blockAccepts_of_principal closure)
        change BlockAccepts computedValue at transferred
        exact transferred
      have closureIsSome :=
        computedAccepts.inferGeneratedUsing_isSome unify_completeMGUSolver
      cases closureResult : inferGeneratedUsing unify computedValue with
      | none => exact (closureIsSome closureResult).elim
      | some closedValue =>
          obtain ⟨computedClosure, substitutionEquality, targetEquality,
              computedAbsorbing⟩ :=
            inferGeneratedUsing_absorbingPrincipalBlockClosure
              unify_absorbingMGUSolver closureResult
          obtain ⟨alignment⟩ := valueCoherence.closureAlignment closure
            computedClosure absorbing computedAbsorbing
          have originalBodyStart := valueElaboration.letBodySupply_eq
            closure absorbing wellFormed
          rw [valueCoherence.next_eq] at originalBodyStart
          have computedBodyStart := computedValueElaboration.letBodySupply_eq
            computedClosure computedAbsorbing wellFormed
          have originalBodyAtFinish := bodyElaboration
          rw [originalBodyStart] at originalBodyAtFinish
          have originalClosedWellFormed : computedAfterValue.WellFormedFor
              (context.applyFree closure.substitution) := by
            rw [← valueCoherence.next_eq]
            exact valueElaboration.closedContext_initialSupply_le closure absorbing
              wellFormed
          have originalBodyWellFormed : computedAfterValue.WellFormedFor
              ((context.applyFree closure.substitution).generalize closure.target ::
                context.applyFree closure.substitution) :=
            originalClosedWellFormed.generalized_cons closure.target
          have alignmentAtComputed :
              alignment.alignment.alignment.rho.FixesAtOrAbove
                computedAfterValue := by
            rw [← valueCoherence.next_eq]
            exact alignment.alignment.fixesAtOrAbove
          have transported := originalBodyAtFinish.transport_of_fixesAtOrAbove
            originalBodyWellFormed alignmentAtComputed
          have bodyContextExact :
              ElaborationRenaming.renameContext alignment.alignment.alignment.rho
                  ((context.applyFree closure.substitution).generalize
                      closure.target :: context.applyFree closure.substitution) =
                ((context.applyFree computedClosure.substitution).generalize
                    computedClosure.target ::
                context.applyFree computedClosure.substitution) := by
            change
              (((context.applyFree closure.substitution).generalize closure.target ::
                  context.applyFree closure.substitution).map
                (Scheme.applyFree
                  alignment.alignment.alignment.rho.substitution)) = _
            exact alignment.alignment.bodyContext_exact
          rw [bodyContextExact] at transported
          have computedClosedWellFormed : computedAfterValue.WellFormedFor
              (context.applyFree computedClosure.substitution) := by
            exact computedValueElaboration.closedContext_initialSupply_le
              computedClosure computedAbsorbing wellFormed
          have computedBodyWellFormed : computedAfterValue.WellFormedFor
              ((context.applyFree computedClosure.substitution).generalize
                  computedClosure.target ::
                context.applyFree computedClosure.substitution) :=
            computedClosedWellFormed.generalized_cons computedClosure.target
          obtain ⟨computedBody, computedNext, bodyReplay,
              computedBodyElaborationAtFinish⟩ :=
            transported.executableReplay_of_fullM2 coherent
              computedBodyWellFormed
          have computedBodyElaboration := computedBodyElaborationAtFinish
          rw [← computedBodyStart] at computedBodyElaboration
          refine ⟨Generated.fromLet
              (context.interfaceEquations computedClosure.substitution)
              computedBody,
            computedNext, ?_, ?_⟩
          · simp [elaborate, valueReplay, closureResult,
              substitutionEquality, targetEquality, computedBodyStart,
              bodyReplay]
          · simpa [substitutionEquality] using
              (Elaborates.letE computedValueElaboration computedClosure
                computedAbsorbing computedBodyElaboration)
  | ctor lookup arity closed call =>
      obtain ⟨computed, computedNext, callReplay, computedCall⟩ :=
        call.executableReplayFrom_of_fullM2 coherent
          _
          (wellFormed.mono (by simp [Supply.Le, Scheme.instantiate]))
      exact ⟨computed, computedNext,
        by simp [elaborate, lookup, arity, callReplay],
        .ctor lookup arity closed computedCall⟩
  | prim lookup arity closed call =>
      obtain ⟨computed, computedNext, callReplay, computedCall⟩ :=
        call.executableReplayFrom_of_fullM2 coherent
          _
          (wellFormed.mono (by simp [Supply.Le, Scheme.instantiate]))
      exact ⟨computed, computedNext,
        by simp [elaborate, lookup, arity, callReplay],
        .prim lookup arity closed computedCall⟩
  | ifE call =>
      obtain ⟨computed, computedNext, callReplay, computedCall⟩ :=
        call.executableReplayFrom_of_fullM2 coherent
          ⟨(conditionalScheme.instantiate supply).1, [], []⟩
          (wellFormed.mono (by simp [Supply.Le, Scheme.instantiate]))
      exact ⟨computed, computedNext,
        by simpa [elaborate] using callReplay,
        .ifE computedCall⟩
termination_by expression.complexity * 3 + 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals try simp
  all_goals omega

/-- Sibling expressions replay in evaluation order. -/
theorem ElaboratesItems.executableReplay_of_fullM2
    (coherent : FullM2Coherence)
    {signature : Signature} {context : Context} {expressions : List Expr}
    {supply generated next}
    (derivation : ElaboratesItems signature context expressions supply generated next)
    (wellFormed : supply.WellFormedFor context) :
    ExecutableItemsReplay signature context expressions supply := by
  cases derivation with
  | nil => exact ⟨_, _, by simp [elaborateItems], .nil⟩
  | cons itemElaboration itemsElaboration =>
      obtain ⟨computedItem, afterItem, itemReplay, computedItemElaboration⟩ :=
        itemElaboration.executableReplay_of_fullM2 coherent wellFormed
      obtain ⟨itemCoherence⟩ := coherent _ wellFormed itemElaboration
        computedItemElaboration
      rw [itemCoherence.next_eq] at itemsElaboration
      obtain ⟨computedItems, computedNext, itemsReplay,
          computedItemsElaboration⟩ :=
        itemsElaboration.executableReplay_of_fullM2 coherent
          (wellFormed.mono computedItemElaboration.supply_le_next)
      exact ⟨_, computedNext, by simp [elaborateItems, itemReplay, itemsReplay],
        .cons computedItemElaboration computedItemsElaboration⟩
termination_by Expr.listComplexity expressions * 3 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals try simp
  all_goals omega

/-- Call arguments replay in evaluation order. -/
theorem ElaboratesCall.executableReplayFrom_of_fullM2
    (coherent : FullM2Coherence)
    {signature : Signature} {context : Context} {accumulated : Generated}
    {arguments : List Expr} {supply generated next}
    (derivation : ElaboratesCall signature context accumulated arguments
      supply generated next)
    (replayAccumulated : Generated)
    (wellFormed : supply.WellFormedFor context) :
    ExecutableCallReplay signature context replayAccumulated arguments supply := by
  cases derivation with
  | nil => exact ⟨_, _, by simp [elaborateCall], .nil⟩
  | cons argumentElaboration restElaboration =>
      obtain ⟨computedArgument, afterArgument, argumentReplay,
          computedArgumentElaboration⟩ :=
        argumentElaboration.executableReplay_of_fullM2 coherent wellFormed
      obtain ⟨argumentCoherence⟩ := coherent _ wellFormed
        argumentElaboration computedArgumentElaboration
      rw [argumentCoherence.next_eq] at restElaboration
      obtain ⟨computed, computedNext, restReplay, computedRest⟩ :=
        restElaboration.executableReplayFrom_of_fullM2 coherent
          (Generated.fromApp replayAccumulated computedArgument
            (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
          ((wellFormed.mono computedArgumentElaboration.supply_le_next).nextTy 2)
      exact ⟨computed, computedNext,
        by simp [elaborateCall, argumentReplay, restReplay],
        .cons computedArgumentElaboration computedRest⟩
termination_by Expr.listComplexity arguments * 3
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals try simp
  all_goals omega

end

/-- Replay a call from its original accumulated block. -/
theorem ElaboratesCall.executableReplay_of_fullM2
    (coherent : FullM2Coherence)
    {signature : Signature} {context : Context} {accumulated : Generated}
    {arguments : List Expr} {supply generated next}
    (derivation : ElaboratesCall signature context accumulated arguments
      supply generated next)
    (wellFormed : supply.WellFormedFor context) :
    ExecutableCallReplay signature context accumulated arguments supply :=
  derivation.executableReplayFrom_of_fullM2 coherent accumulated wellFormed

/-- Full M2 coherence implies principality completeness for every
well-formed source supply, with no signature well-formedness premise. -/
theorem wellFormedElaborationPrincipalityComplete_of_fullM2
    (coherent : FullM2Coherence) :
    WellFormedElaborationPrincipalityComplete := by
  intro signature context expression supply next generated derivation closure
    wellFormed absorbing
  obtain ⟨computed, computedNext, replay, computedElaboration⟩ :=
    derivation.executableReplay_of_fullM2 coherent wellFormed
  obtain ⟨pair⟩ := coherent expression wellFormed derivation
    computedElaboration
  have computedAccepts : BlockAccepts computed := by
    have transferred := (pair.blockAccepts_iff .hole trivial).mp
      (blockAccepts_of_principal closure)
    change BlockAccepts computed at transferred
    exact transferred
  have closureIsSome :=
    computedAccepts.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases closureResult : inferGeneratedUsing unify computed with
  | none => exact (closureIsSome closureResult).elim
  | some result =>
      obtain ⟨computedClosure, _, _, computedAbsorbing⟩ :=
        inferGeneratedUsing_absorbingPrincipalBlockClosure
          unify_absorbingMGUSolver closureResult
      obtain ⟨computedToOriginal, originalToComputed⟩ :=
        pair.closureTargets_mutualInstances closure computedClosure absorbing
          computedAbsorbing
      exact ⟨computed, computedNext, replay, computedClosure,
        originalToComputed, computedToOriginal⟩

end TypePM.Source
