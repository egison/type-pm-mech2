import TypePM.Source.InterfaceClosureTransport
import TypePM.BlockOrderInvariance

/-!
# Replay and acceptance completeness for M2 source elaboration

The executable and relational elaborators choose exactly the same fresh names
until a `letE` boundary.  At such a boundary the relation may carry a
different absorbing principal closure from the concrete unifier, so a later
renaming/coherence theorem is required.  This module records the completeness
facts that do not depend on that theorem: exact-representative replay and full
acceptance completeness for the let-free fragment.
-/

namespace TypePM

namespace BlockAccepts

/-- A declaratively acceptable block is accepted by every complete
most-general-unifier implementation.  Unlike the corresponding theorem for
`PrincipalBlockClosure`, the input only carries a residual solution, not a
principal residual representative. -/
theorem inferGeneratedUsing_isSome
    {solve : List Equation → Option Subst}
    (solver : CompleteMGUSolver solve)
    {generated : Generated}
    (accepts : BlockAccepts generated) :
    inferGeneratedUsing solve generated ≠ none := by
  rcases accepts with ⟨finalHard, finalPending, hardSubstitution,
    residualSubstitution, saturation, residualSolved⟩
  obtain ⟨computed, saturationResult⟩ :=
    solver.saturateUsing_complete saturation
  have computedSaturation :
      Saturated generated.hard generated.pending
        computed.hard computed.pending computed.substitution :=
    saturateUsing_sound solve solver.principal saturationResult
  obtain ⟨_, pendingEquality⟩ :=
    saturation.finalState_unique computedSaturation
  obtain ⟨declarativeToComputed, computedToDeclarative⟩ :=
    saturation.finalSubstitutions_mutualFactors computedSaturation
  have computedResidualSolvable :
      ∃ substitution,
        Solves substitution
          (residualEquations computed.substitution computed.pending) := by
    rw [← pendingEquality]
    obtain ⟨post, _, transported⟩ :=
      ResolutionTransport.residualEquations_transport_of_mutualFactors
        computedToDeclarative declarativeToComputed residualSolved
    exact ⟨Subst.compose residualSubstitution post, transported⟩
  obtain ⟨residual, residualResult⟩ :=
    solver.complete _ computedResidualSolvable
  simp [inferGeneratedUsing, saturationResult, residualResult]

end BlockAccepts

namespace Source

mutual

/-- Evidence that a source expression contains no `letE`. -/
inductive LetFree : Expr → Prop where
  | var (index : Nat) : LetFree (.var index)
  | lit (value : Int) : LetFree (.lit value)
  | something : LetFree .something
  | lam {body : Expr} : LetFree body → LetFree (.lam body)
  | app {function argument : Expr} :
      LetFree function → LetFree argument → LetFree (.app function argument)
  | tuple {items : List Expr} : LetFreeItems items → LetFree (.tuple items)

/-- Pointwise let-freedom for tuple items. -/
inductive LetFreeItems : List Expr → Prop where
  | nil : LetFreeItems []
  | cons {item : Expr} {items : List Expr} :
      LetFree item → LetFreeItems items → LetFreeItems (item :: items)

end

mutual

/-- Every let-free relational elaboration is replayed literally by the
executable elaborator. -/
theorem Elaborates.replay_of_letFree
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (derivation : Elaborates context expression supply generated next)
    (letFree : LetFree expression) :
    elaborate context expression supply = some (generated, next) := by
  cases derivation with
  | var lookup => simp [elaborate, lookup]
  | lit => simp [elaborate]
  | something => simp [elaborate]
  | lam bodyElaboration =>
      cases letFree with
      | lam bodyLetFree =>
          simp [elaborate,
            Elaborates.replay_of_letFree bodyElaboration bodyLetFree]
  | app functionElaboration argumentElaboration =>
      cases letFree with
      | app functionLetFree argumentLetFree =>
          simp [elaborate,
            Elaborates.replay_of_letFree functionElaboration functionLetFree,
            Elaborates.replay_of_letFree argumentElaboration argumentLetFree]
  | tuple itemsElaboration =>
      cases letFree with
      | tuple itemsLetFree =>
          simp [elaborate,
            ElaboratesItems.replay_of_letFree itemsElaboration itemsLetFree]
  | letE => cases letFree

/-- List counterpart of `Elaborates.replay_of_letFree`. -/
theorem ElaboratesItems.replay_of_letFree
    {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (derivation :
      ElaboratesItems context expressions supply generated next)
    (letFree : LetFreeItems expressions) :
    elaborateItems context expressions supply = some (generated, next) := by
  cases derivation with
  | nil => simp [elaborateItems]
  | cons itemElaboration itemsElaboration =>
      cases letFree with
      | cons itemLetFree itemsLetFree =>
          simp [elaborateItems,
            Elaborates.replay_of_letFree itemElaboration itemLetFree,
            ElaboratesItems.replay_of_letFree itemsElaboration itemsLetFree]

end


/-- An executable elaboration result together with independent evidence that
its generated constraint block has a principal closure.  This is the exact
intermediate fact needed for acceptance completeness. -/
structure ExecutableClosure (context : Context) (expression : Expr) where
  generated : Generated
  next : Supply
  replay : elaborate context expression context.initialSupply =
    some (generated, next)
  closure : PrincipalBlockClosure generated

/-- Declarative acceptance of the block actually produced by elaboration is
enough to construct an `ExecutableClosure`; no particular principal
representative has to be supplied. -/
theorem executableClosure_of_blockAccepts
    {context : Context} {expression : Expr} {generated : Generated}
    {next : Supply}
    (replay : elaborate context expression context.initialSupply =
      some (generated, next))
    (accepts : BlockAccepts generated) :
    Nonempty (ExecutableClosure context expression) := by
  have succeeds :=
    TypePM.BlockAccepts.inferGeneratedUsing_isSome
      unify_completeMGUSolver accepts
  cases computed : inferGeneratedUsing unify generated with
  | none => exact (succeeds computed).elim
  | some result =>
      obtain ⟨closure, _, _⟩ :=
        inferGeneratedUsing_principalBlockClosure
          (fun _ _ success => unify_mostGeneral success) computed
      exact ⟨
        { generated := generated
          next := next
          replay := replay
          closure := closure }⟩

/-- Once the block selected by executable elaboration has a declarative
principal closure, completeness of the block solver suffices for source
inference acceptance. -/
theorem infer_isSome_of_elaboratedClosure
    {context : Context} {expression : Expr} {generated : Generated}
    {next : Supply}
    (replay : elaborate context expression context.initialSupply =
      some (generated, next))
    (closure : PrincipalBlockClosure generated) :
    infer context expression ≠ none := by
  have closed : inferGeneratedUsing unify generated ≠ none :=
    closure.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases closureResult : inferGeneratedUsing unify generated with
  | none => exact (closed closureResult).elim
  | some result => simp [infer, elaborateRoot, replay, closureResult]

/-- Exact-representative specialization of
`infer_isSome_of_elaboratedClosure`. -/
theorem infer_isSome_of_exactRepresentative
    {context : Context} {expression : Expr} {generated : Generated}
    {next : Supply}
    (replay : elaborate context expression context.initialSupply =
      some (generated, next))
    (closure : PrincipalBlockClosure generated) :
    infer context expression ≠ none :=
  infer_isSome_of_elaboratedClosure replay closure

/-- An executable elaboration result with a principal block closure is
accepted by source inference. -/
theorem ExecutableClosure.infer_isSome
    {context : Context} {expression : Expr}
    (witness : ExecutableClosure context expression) :
    infer context expression ≠ none :=
  infer_isSome_of_elaboratedClosure witness.replay witness.closure

/-- A let-free blockwise-principal typing is accepted by executable source
inference. -/
theorem PrincipalTyping.infer_isSome_of_letFree
    {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping context expression target)
    (letFree : LetFree expression) :
    infer context expression ≠ none := by
  rcases principal with ⟨derivation⟩
  let witness : ExecutableClosure context expression :=
    { generated := derivation.generated
      next := derivation.next
      replay := derivation.elaboration.replay_of_letFree letFree
      closure := derivation.closure }
  exact witness.infer_isSome

/-- Every declaratively typable let-free source expression is accepted.
The requested result type may be any substitution instance of the stored
blockwise-principal result. -/
theorem Typing.infer_isSome_of_letFree
    {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing context expression target)
    (letFree : LetFree expression) :
    infer context expression ≠ none := by
  rcases typing with ⟨_, principal, _⟩
  exact principal.infer_isSome_of_letFree letFree

/-- The remaining interface-aware transport statement for full M2
completeness.  It says that an acceptable relational representative can be
replayed by executable elaboration with an acceptable (not necessarily
identical) generated block.  `InterfaceClosureTransport` supplies the
representative-insensitive interface equations needed in the `letE` case;
finite fresh-name transport supplies the body comparison. -/
def ElaborationAcceptanceComplete : Prop :=
  ∀ {context : Context} {expression : Expr} {supply next : Supply}
      {generated : Generated},
    Elaborates context expression supply generated next →
      ∀ (closure : PrincipalBlockClosure generated), closure.Absorbing →
        ∃ computed computedNext,
          elaborate context expression supply =
              some (computed, computedNext) ∧
            BlockAccepts computed

/-- The precise remaining transport statement implies acceptance
completeness for every blockwise-principal source typing. -/
theorem PrincipalTyping.infer_isSome_of_elaborationAcceptanceComplete
    (complete : ElaborationAcceptanceComplete)
    {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping context expression target) :
    infer context expression ≠ none := by
  rcases principal with ⟨derivation⟩
  obtain ⟨computed, computedNext, replay, accepts⟩ :=
    complete derivation.elaboration derivation.closure
      derivation.absorbing
  obtain ⟨witness⟩ := executableClosure_of_blockAccepts replay accepts
  exact witness.infer_isSome

/-- Instance closure does not add any further obligation to acceptance
completeness once the principal representative is accepted. -/
theorem Typing.infer_isSome_of_elaborationAcceptanceComplete
    (complete : ElaborationAcceptanceComplete)
    {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing context expression target) :
    infer context expression ≠ none := by
  rcases typing with ⟨_, principal, _⟩
  exact principal.infer_isSome_of_elaborationAcceptanceComplete complete

/-- A source expression is typable when it has at least one declarative
result type. -/
def Typable (context : Context) (expression : Expr) : Prop :=
  ∃ target, Typing context expression target

namespace Inference

/-- On the let-free fragment, public source inference succeeds exactly for
declaratively typable expressions. -/
theorem typable_iff_infer_isSome_of_letFree
    (context : Context) (expression : Expr)
    (letFree : LetFree expression) :
    Typable context expression ↔ infer context expression ≠ none := by
  constructor
  · rintro ⟨_, typing⟩
    exact typing.infer_isSome_of_letFree letFree
  · intro succeeds
    cases computed : infer context expression with
    | none => exact False.elim (succeeds computed)
    | some target => exact ⟨target, infer_success_typing computed⟩

/-- Let-free source typability is decidable by running public inference. -/
def typableDecidable_of_letFree
    (context : Context) (expression : Expr)
    (letFree : LetFree expression) :
    Decidable (Typable context expression) :=
  match computed : infer context expression with
  | none => isFalse (by
      rintro ⟨_, typing⟩
      exact typing.infer_isSome_of_letFree letFree computed)
  | some target => isTrue ⟨target, infer_success_typing computed⟩

/-- Conditional full-M2 exactness, reduced solely to the explicit
interface-aware elaboration transport statement above. -/
theorem typable_iff_infer_isSome_of_elaborationAcceptanceComplete
    (complete : ElaborationAcceptanceComplete)
    (context : Context) (expression : Expr) :
    Typable context expression ↔ infer context expression ≠ none := by
  constructor
  · rintro ⟨_, typing⟩
    exact typing.infer_isSome_of_elaborationAcceptanceComplete complete
  · intro succeeds
    cases computed : infer context expression with
    | none => exact False.elim (succeeds computed)
    | some target => exact ⟨target, infer_success_typing computed⟩

/-- Conditional full-M2 decision procedure.  Supplying the remaining
transport proof removes the condition without changing the algorithm. -/
def typableDecidable_of_elaborationAcceptanceComplete
    (complete : ElaborationAcceptanceComplete)
    (context : Context) (expression : Expr) :
    Decidable (Typable context expression) :=
  match computed : infer context expression with
  | none => isFalse (by
      rintro ⟨_, typing⟩
      exact typing.infer_isSome_of_elaborationAcceptanceComplete
        complete computed)
  | some target => isTrue ⟨target, infer_success_typing computed⟩

end Inference

end Source

end TypePM
