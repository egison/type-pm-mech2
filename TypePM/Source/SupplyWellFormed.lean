import TypePM.Source.ElaborationCompleteness
import TypePM.Source.Principality

/-!
# Well-formed fresh supplies for source elaboration

Public source inference always starts at `Context.initialSupply`.  The more
general elaboration relations expose an arbitrary starting supply, but the
usual freshness and renaming arguments only apply when both components of
that supply lie above all free names in the source context.  This module
records that precondition and the elementary preservation facts used by the
completed completeness proof.
-/

namespace TypePM.Source

namespace Supply

/-- Componentwise order on the independent ordinary-variable and
capability-variable supplies. -/
def Le (left right : Supply) : Prop :=
  left.ty ≤ right.ty ∧ left.cap ≤ right.cap

/-- A source supply is well formed for a context when allocation starts
above every free name in that context. -/
def WellFormedFor (context : Context) (supply : Supply) : Prop :=
  context.initialSupply.Le supply

theorem le_refl (supply : Supply) : supply.Le supply := by
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem le_trans {first second third : Supply}
    (firstSecond : first.Le second) (secondThird : second.Le third) :
    first.Le third := by
  exact ⟨Nat.le_trans firstSecond.1 secondThird.1,
    Nat.le_trans firstSecond.2 secondThird.2⟩

theorem le_nextTy (supply : Supply) (count : Nat) :
    supply.Le (supply.nextTy count) := by
  simp [Le, Supply.nextTy]

theorem le_join_left (left right : Supply) : left.Le (left.join right) := by
  simp only [Le, Supply.join]
  exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem le_join_right (left right : Supply) : right.Le (left.join right) := by
  simp only [Le, Supply.join]
  exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-- The defensive `letE` join is redundant once the closed context's names
are known to remain below the supply returned by the value elaboration. -/
theorem join_eq_left_of_right_le {left right : Supply}
    (bounded : right.Le left) :
    left.join right = left := by
  cases left with
  | mk leftTy leftCap =>
      cases right with
      | mk rightTy rightCap =>
          simp only [Le] at bounded
          simp only [Supply.join, Supply.mk.injEq]
          omega

theorem wellFormedFor_initialSupply (context : Context) :
    context.initialSupply.WellFormedFor context :=
  le_refl _

theorem WellFormedFor.mono {context : Context} {source target : Supply}
    (wellFormed : source.WellFormedFor context)
    (increases : source.Le target) :
    target.WellFormedFor context :=
  le_trans wellFormed increases

theorem WellFormedFor.nextTy {context : Context} {supply : Supply}
    (wellFormed : supply.WellFormedFor context) (count : Nat) :
    (supply.nextTy count).WellFormedFor context :=
  wellFormed.mono (le_nextTy supply count)

theorem wellFormedFor_join_initialSupply
    (context : Context) (supply : Supply) :
    (supply.join context.initialSupply).WellFormedFor context :=
  le_join_right supply context.initialSupply

/-- Exact `letE` body-supply simplification, separated from the substantive
closure-range theorem that must establish `closedAbove`. -/
theorem letBodySupply_eq
    (closedContext : Context) (afterValue : Supply)
    (closedAbove : closedContext.initialSupply.Le afterValue) :
    afterValue.join closedContext.initialSupply = afterValue :=
  join_eq_left_of_right_le closedAbove

end Supply

mutual

/-- Relational elaboration never moves either supply component backwards. -/
theorem Elaborates.supply_le_next
    {signature : Signature} {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (derivation : Elaborates signature context expression supply generated next) :
    supply.Le next := by
  cases derivation with
  | var lookup =>
      simp [Supply.Le, Scheme.instantiate]
  | lit => exact Supply.le_refl _
  | something => exact Supply.le_nextTy _ _
  | lam bodyElaboration =>
      exact Supply.le_trans (Supply.le_nextTy _ _) bodyElaboration.supply_le_next
  | app functionElaboration argumentElaboration =>
      exact Supply.le_trans functionElaboration.supply_le_next
        (Supply.le_trans argumentElaboration.supply_le_next
          (Supply.le_nextTy _ _))
  | tuple itemsElaboration => exact itemsElaboration.supply_le_next
  | letE valueElaboration closure absorbing bodyElaboration =>
      exact Supply.le_trans valueElaboration.supply_le_next
        (Supply.le_trans (Supply.le_join_left _ _)
          bodyElaboration.supply_le_next)
  | ctor lookup arity closed call =>
      exact Supply.le_trans (by simp [Supply.Le, Scheme.instantiate])
        call.supply_le_next
  | prim lookup arity closed call =>
      exact Supply.le_trans (by simp [Supply.Le, Scheme.instantiate])
        call.supply_le_next
  | ifE call =>
      exact Supply.le_trans (by simp [Supply.Le, Scheme.instantiate])
        call.supply_le_next
termination_by expression.complexity * 3 + 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals try simp
  all_goals omega

/-- List elaboration has the same componentwise monotonicity property. -/
theorem ElaboratesItems.supply_le_next
    {signature : Signature} {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (derivation : ElaboratesItems signature context expressions supply generated next) :
    supply.Le next := by
  cases derivation with
  | nil => exact Supply.le_refl _
  | cons itemElaboration itemsElaboration =>
      exact Supply.le_trans itemElaboration.supply_le_next
        itemsElaboration.supply_le_next
termination_by Expr.listComplexity expressions * 3 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals try simp
  all_goals omega

theorem ElaboratesCall.supply_le_next
    {signature : Signature} {context : Context}
    {accumulated generated : Generated} {expressions : List Expr}
    {supply next : Supply}
    (derivation : ElaboratesCall signature context accumulated expressions
      supply generated next) : supply.Le next := by
  cases derivation with
  | nil => exact Supply.le_refl _
  | cons argumentElaboration restElaboration =>
      exact Supply.le_trans argumentElaboration.supply_le_next
        (Supply.le_trans (Supply.le_nextTy _ _)
          restElaboration.supply_le_next)
termination_by Expr.listComplexity expressions * 3
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals try simp
  all_goals omega

end

/-- A well-formed starting supply remains well formed for the outer context
after relational elaboration, including across `letE`'s supply join. -/
theorem Elaborates.wellFormedFor_next
    {signature : Signature} {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (derivation : Elaborates signature context expression supply generated next)
    (wellFormed : supply.WellFormedFor context) :
    next.WellFormedFor context :=
  wellFormed.mono derivation.supply_le_next

/-- Executable elaboration preserves the same outer-context supply
invariant. -/
theorem elaborate_wellFormedFor_next
    {signature : Signature} (signatureWellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (success : elaborate signature context expression supply = some (generated, next))
    (wellFormed : supply.WellFormedFor context) :
    next.WellFormedFor context :=
  (elaborate_sound signatureWellFormed success).wellFormedFor_next wellFormed

/-- Acceptance completeness at exactly the supply scope used by public root
inference and by freshness transport. -/
def WellFormedElaborationAcceptanceComplete : Prop :=
  ∀ {signature : Signature} {context : Context} {expression : Expr} {supply next : Supply}
      {generated : Generated},
    supply.WellFormedFor context →
      Elaborates signature context expression supply generated next →
        ∀ (closure : PrincipalBlockClosure generated), closure.Absorbing →
          ∃ computed computedNext,
            elaborate signature context expression supply = some (computed, computedNext) ∧
              BlockAccepts computed

/-- The older arbitrary-supply premise is strictly stronger syntactically
than the well-formed-supply statement. -/
theorem ElaborationAcceptanceComplete.toWellFormed
    (complete : ElaborationAcceptanceComplete) :
    WellFormedElaborationAcceptanceComplete := by
  intro signature context expression supply next generated _ derivation closure absorbing
  exact complete derivation closure absorbing

/-- The well-formed statement is sufficient for the public root inference
API, whose relational witness starts at `Context.initialSupply`. -/
theorem PrincipalTyping.infer_isSome_of_wellFormedElaborationAcceptanceComplete
    (complete : WellFormedElaborationAcceptanceComplete)
    {signature : Signature} {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping signature context expression target) :
    infer signature context expression ≠ none := by
  rcases principal with ⟨derivation⟩
  obtain ⟨computed, computedNext, replay, accepts⟩ :=
    complete (Supply.wellFormedFor_initialSupply context)
      derivation.elaboration derivation.closure derivation.absorbing
  obtain ⟨witness⟩ := executableClosure_of_blockAccepts replay accepts
  exact witness.infer_isSome

/-- Instance closure adds no new acceptance obligation at the public root
supply once its blockwise-principal representative is accepted. -/
theorem Typing.infer_isSome_of_wellFormedElaborationAcceptanceComplete
    (complete : WellFormedElaborationAcceptanceComplete)
    {signature : Signature} {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing signature context expression target) :
    infer signature context expression ≠ none := by
  rcases typing with ⟨_, principal, _⟩
  exact principal.infer_isSome_of_wellFormedElaborationAcceptanceComplete
    complete

namespace Inference

/-- At the public `context.initialSupply`, freshness-safe elaboration
acceptance gives exact agreement between declarative typability and
executable inference success. -/
theorem typable_iff_infer_isSome_of_wellFormedElaborationAcceptanceComplete
    (complete : WellFormedElaborationAcceptanceComplete)
    (signature : Signature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Typable signature context expression ↔
      infer signature context expression ≠ none := by
  constructor
  · rintro ⟨_, typing⟩
    exact typing.infer_isSome_of_wellFormedElaborationAcceptanceComplete
      complete
  · intro succeeds
    cases computed : infer signature context expression with
    | none => exact False.elim (succeeds computed)
    | some target => exact ⟨target, infer_success_typing wellFormed computed⟩

/-- Public source typability is decidable from the executable inference
result under freshness-safe elaboration acceptance. -/
def typableDecidable_of_wellFormedElaborationAcceptanceComplete
    (complete : WellFormedElaborationAcceptanceComplete)
    (signature : Signature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Decidable (Typable signature context expression) :=
  match computed : infer signature context expression with
  | none => isFalse (by
      rintro ⟨_, typing⟩
      exact typing.infer_isSome_of_wellFormedElaborationAcceptanceComplete
        complete computed)
  | some target => isTrue ⟨target, infer_success_typing wellFormed computed⟩

end Inference

/-- Principality correspondence restricted to freshness-safe supplies. -/
def WellFormedElaborationPrincipalityComplete : Prop :=
  ∀ {signature : Signature} {context : Context} {expression : Expr} {supply next : Supply}
      {generated : Generated}
      (_derivation : Elaborates signature context expression supply generated next)
      (closure : PrincipalBlockClosure generated),
    supply.WellFormedFor context → closure.Absorbing →
      ∃ (computed : Generated) (computedNext : Supply),
        elaborate signature context expression supply = some (computed, computedNext) ∧
          ∃ computedClosure : PrincipalBlockClosure computed,
            IsInstance computedClosure.target closure.target ∧
              IsInstance closure.target computedClosure.target

/-- Freshness-safe principality correspondence contains the corresponding
acceptance result. -/
theorem WellFormedElaborationPrincipalityComplete.toAcceptance
    (complete : WellFormedElaborationPrincipalityComplete) :
    WellFormedElaborationAcceptanceComplete := by
  intro signature context expression supply next generated wellFormed derivation closure
    absorbing
  obtain ⟨computed, computedNext, replay, computedClosure, _⟩ :=
    complete derivation closure wellFormed absorbing
  exact ⟨computed, computedNext, replay,
    ⟨computedClosure.finalHard,
      computedClosure.finalPending,
      computedClosure.hardSubstitution,
      computedClosure.residualSubstitution,
      computedClosure.saturation,
      computedClosure.residualPrincipal.1⟩⟩

namespace SupplyCollision

private def freeZero : TyVar := ⟨0⟩

/-- A scheme with one quantified variable and one genuinely free context
variable. -/
def polymorphicScheme : Scheme :=
  ⟨1, 0, .fn (.bound 0) (.free freeZero), by
    simp [PolyTy.WellScoped]⟩

def context : Context := [polymorphicScheme]

theorem initialSupply_eq : context.initialSupply = ⟨1, 0⟩ := by
  decide

/-- Starting below the context supply aliases the quantified variable with
the free variable, changing `∀a. a → β0` into `β0 → β0`. -/
theorem instantiate_below_aliases :
    polymorphicScheme.instantiate ⟨0, 0⟩ =
      (.fn (.var freeZero) (.var freeZero), ⟨1, 0⟩) := by
  rfl

/-- The public root supply keeps the quantified and free variables distinct. -/
theorem instantiate_at_root_is_fresh :
    polymorphicScheme.instantiate context.initialSupply =
      (.fn (.var ⟨1⟩) (.var freeZero), ⟨2, 0⟩) := by
  rw [initialSupply_eq]
  rfl

theorem below_not_wellFormed :
    ¬ (Supply.mk 0 0).WellFormedFor context := by
  simp [Supply.WellFormedFor, Supply.Le, initialSupply_eq]

private def freeCapZero : CapVar := ⟨0⟩

/-- Capability variables have the same collision mode independently of
ordinary type variables. -/
def capabilityPolymorphicScheme : Scheme :=
  ⟨0, 1,
    .matcher (.bound 0) (.slot (.free freeCapZero) .int), by
      simp [PolyTy.WellScoped, PolyCap.WellScoped]⟩

def capabilityContext : Context := [capabilityPolymorphicScheme]

theorem capabilityInitialSupply_eq :
    capabilityContext.initialSupply = ⟨0, 1⟩ := by
  decide

theorem capabilityInstantiate_below_aliases :
    capabilityPolymorphicScheme.instantiate ⟨0, 0⟩ =
      (.matcher (.var freeCapZero) (.slot (.var freeCapZero) .int),
        ⟨0, 1⟩) := by
  rfl

theorem capabilityInstantiate_at_root_is_fresh :
    capabilityPolymorphicScheme.instantiate
        capabilityContext.initialSupply =
      (.matcher (.var ⟨1⟩) (.slot (.var freeCapZero) .int),
        ⟨0, 2⟩) := by
  rw [capabilityInitialSupply_eq]
  rfl

private def alpha : TyVar := ⟨0⟩
private def beta : TyVar := ⟨1⟩
private def high : TyVar := ⟨100⟩

private def highRepresentative : Subst :=
  { cap := Cap.var
    ty := fun index =>
      if index = alpha ∨ index = beta then .var high else .var index }

private def groundSolution : Subst :=
  { cap := Cap.var
    ty := fun index =>
      if index = alpha ∨ index = beta then .int else .var index }

/-- Mapping both sides of `α = β` to an arbitrary high `γ` does unify the
equation, but it is *not* absorbing: a ground solution of the original
equality does not absorb that fresh representative.  Thus the existing
`Absorbing` premise already rules out this tempting counterexample. -/
theorem highRepresentative_not_absorbing :
    ¬ AbsorbingPrincipal
      [.ty (.var alpha) (.var beta)] highRepresentative := by
  intro absorbing
  have groundSolves :
      Solves groundSolution [.ty (.var alpha) (.var beta)] := by
    intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    change groundSolution.ty alpha = groundSolution.ty beta
    rfl
  have absorbed := absorbing.absorbs groundSolves
  have atAlpha := congrArg (fun substitution => substitution.ty alpha) absorbed
  simp [Subst.compose, highRepresentative, groundSolution,
    Ty.apply, alpha, beta, high] at atAlpha

end SupplyCollision

end TypePM.Source
