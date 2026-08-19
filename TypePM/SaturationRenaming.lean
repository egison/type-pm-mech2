import TypePM.Declarative
import TypePM.Permutation
import TypePM.SourcePermutation

/-!
# Renaming invariance of declarative saturation

Fresh ordinary type-variable names are operational bookkeeping.  This module
shows that changing them bijectively preserves the branch decisions, hard
saturation, and residual equations used by declarative M1 typing.
-/

namespace TypePM

/-- The substitution whose action is exactly an ordinary-variable renaming. -/
def Subst.ofTyRenaming (rho : TyRenaming) : Subst :=
  { cap := Cap.var
    ty := fun index => .var (rho index) }

mutual

@[simp] theorem Ty.apply_ofTyRenaming
    (rho : TyRenaming) (target : Ty) :
    target.apply (Subst.ofTyRenaming rho) = target.rename rho := by
  cases target with
  | var => rfl
  | int => rfl
  | fn domain codomain =>
      simp [Ty.apply, Ty.rename, Ty.apply_ofTyRenaming]
  | prod items =>
      simp [Ty.apply, Ty.rename, Ty.applyList_ofTyRenaming]
  | data former arguments =>
      simp [Ty.apply, Ty.rename, Ty.applyList_ofTyRenaming]
  | matcher capability target =>
      simp only [Ty.apply, Ty.rename]
      rw [show (Subst.ofTyRenaming rho).cap = Subst.id.cap by rfl,
        Cap.apply_id, Ty.apply_ofTyRenaming]
  | slot capability target =>
      simp only [Ty.apply, Ty.rename]
      rw [show (Subst.ofTyRenaming rho).cap = Subst.id.cap by rfl,
        Cap.apply_id, Ty.apply_ofTyRenaming]

@[simp] theorem Ty.applyList_ofTyRenaming
    (rho : TyRenaming) (targets : List Ty) :
    Ty.applyList (Subst.ofTyRenaming rho) targets =
      Ty.renameList rho targets := by
  cases targets with
  | nil => rfl
  | cons target targets =>
      simp [Ty.applyList, Ty.renameList, Ty.apply_ofTyRenaming,
        Ty.applyList_ofTyRenaming]

end

@[simp] theorem Equation.apply_ofTyRenaming
    (rho : TyRenaming) (equation : Equation) :
    equation.apply (Subst.ofTyRenaming rho) = equation.rename rho := by
  cases equation with
  | cap left right =>
      simp only [Equation.apply, Equation.rename]
      have leftEquality :
          left.apply (Subst.ofTyRenaming rho).cap = left := by
        change left.apply Subst.id.cap = left
        exact Cap.apply_id left
      have rightEquality :
          right.apply (Subst.ofTyRenaming rho).cap = right := by
        change right.apply Subst.id.cap = right
        exact Cap.apply_id right
      rw [leftEquality, rightEquality]
  | ty left right =>
      simp [Equation.apply, Equation.rename, Ty.apply_ofTyRenaming]

@[simp] theorem Subst.renameSolution_symm_apply
    (rho : TyRenaming) (substitution : Subst) :
    Subst.renameSolution rho.symm
      (Subst.renameSolution rho substitution) = substitution := by
  apply Subst.eq_of_components
  · intro index
    rfl
  · intro index
    simp [Subst.renameSolution]

@[simp] theorem Subst.renameSolution_apply_symm
    (rho : TyRenaming) (substitution : Subst) :
    Subst.renameSolution rho
      (Subst.renameSolution rho.symm substitution) = substitution := by
  apply Subst.eq_of_components
  · intro index
    rfl
  · intro index
    simp [Subst.renameSolution]

theorem Subst.renameSolution_compose
    (rho : TyRenaming) (later earlier : Subst) :
    Subst.renameSolution rho (Subst.compose later earlier) =
      Subst.compose (Subst.renameSolution rho later)
        (Subst.renameSolution rho earlier) := by
  apply Subst.eq_of_components
  · intro index
    rfl
  · intro index
    simp only [Subst.renameSolution, Subst.compose]
    exact (Ty.rename_apply_renameSolution rho later
      (earlier.ty (rho.symm index))).symm

namespace Ty

@[simp] theorem mayBecomeMatcher_rename
    (rho : TyRenaming) (target : Ty) :
    (target.rename rho).mayBecomeMatcher = target.mayBecomeMatcher := by
  cases target <;> rfl

@[simp] theorem mayBecomeMatcherItems_rename
    (rho : TyRenaming) (targets : List Ty) :
    mayBecomeMatcherItems (Ty.renameList rho targets) =
      mayBecomeMatcherItems targets := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp only [Ty.renameList, mayBecomeMatcherItems]
      rw [mayBecomeMatcher_rename, induction]

@[simp] theorem mayBecomeMatcherProduct_rename
    (rho : TyRenaming) (target : Ty) :
    (target.rename rho).mayBecomeMatcherProduct =
      target.mayBecomeMatcherProduct := by
  cases target with
  | prod items =>
      cases items with
      | nil => rfl
      | cons item items =>
          simp only [Ty.rename, Ty.renameList, mayBecomeMatcherProduct]
          rw [mayBecomeMatcher_rename,
            mayBecomeMatcherItems_rename]
  | _ => rfl

@[simp] theorem mayBecomeExpectedMatcher_rename
    (rho : TyRenaming) (target : Ty) :
    (target.rename rho).mayBecomeExpectedMatcher =
      target.mayBecomeExpectedMatcher := by
  cases target <;> rfl

@[simp] theorem mayBecomeExpectedSlot_rename
    (rho : TyRenaming) (target : Ty) :
    (target.rename rho).mayBecomeExpectedSlot =
      target.mayBecomeExpectedSlot := by
  cases target <;> rfl

@[simp] theorem couldSpecial_rename
    (rho : TyRenaming) (source expected : Ty) :
    (source.rename rho).couldSpecial (expected.rename rho) =
      source.couldSpecial expected := by
  simp [Ty.couldSpecial]

end Ty

theorem Resolution.resolve_branch_rename
    (rho : TyRenaming) (source expected : Ty) :
    (resolve (source.rename rho) (expected.rename rho)).branch =
      (resolve source expected).branch := by
  let post := Subst.ofTyRenaming rho
  let retract := Subst.ofTyRenaming rho.symm
  have sourceRetract :
      (source.apply post).apply retract = source := by
    simp [post, retract]
  have expectedRetract :
      (expected.apply post).apply retract = expected := by
    simp [post, retract]
  have canonical := Resolution.resolve_apply_canonical_of_retract
    post retract source expected sourceRetract expectedRetract
  rw [← Ty.apply_ofTyRenaming rho source,
    ← Ty.apply_ofTyRenaming rho expected]
  exact canonical.1.symm

theorem Resolution.resolve_equations_rename
    (rho : TyRenaming) (source expected : Ty) :
    (resolve (source.rename rho) (expected.rename rho)).equations =
      (resolve source expected).equations.map (Equation.rename rho) := by
  let post := Subst.ofTyRenaming rho
  let retract := Subst.ofTyRenaming rho.symm
  have sourceRetract :
      (source.apply post).apply retract = source := by
    simp [post, retract]
  have expectedRetract :
      (expected.apply post).apply retract = expected := by
    simp [post, retract]
  have canonical := Resolution.resolve_apply_canonical_of_retract
    post retract source expected sourceRetract expectedRetract
  rw [← Ty.apply_ofTyRenaming rho source,
    ← Ty.apply_ofTyRenaming rho expected]
  have functionEquality :
      Equation.apply post = Equation.rename rho := by
    funext equation
    simpa only [post] using Equation.apply_ofTyRenaming rho equation
  rw [functionEquality] at canonical
  exact canonical.2

namespace CheckObligation

@[simp] theorem apply_renameSolution
    (rho : TyRenaming) (substitution : Subst)
    (obligation : CheckObligation) :
    (obligation.rename rho).apply
        (Subst.renameSolution rho substitution) =
      (obligation.apply substitution).rename rho := by
  cases obligation
  simp [CheckObligation.apply, CheckObligation.rename,
    Ty.rename_apply_renameSolution]

@[simp] theorem forcedOrdinaryUnder_rename
    (rho : TyRenaming) (substitution : Subst)
    (obligation : CheckObligation) :
    (obligation.rename rho).forcedOrdinaryUnder
        (Subst.renameSolution rho substitution) ↔
      obligation.forcedOrdinaryUnder substitution := by
  change
    ((obligation.source.rename rho).apply
        (Subst.renameSolution rho substitution)).couldSpecial
      ((obligation.expected.rename rho).apply
        (Subst.renameSolution rho substitution)) = false ↔ _
  rw [Ty.rename_apply_renameSolution,
    Ty.rename_apply_renameSolution, Ty.couldSpecial_rename]
  rfl

@[simp] theorem residualEquations_rename
    (rho : TyRenaming) (substitution : Subst)
    (obligation : CheckObligation) :
    (obligation.rename rho).residualEquations
        (Subst.renameSolution rho substitution) =
      (obligation.residualEquations substitution).map
        (Equation.rename rho) := by
  change
    (resolve
      ((obligation.source.rename rho).apply
        (Subst.renameSolution rho substitution))
      ((obligation.expected.rename rho).apply
        (Subst.renameSolution rho substitution))).equations = _
  rw [Ty.rename_apply_renameSolution,
    Ty.rename_apply_renameSolution,
    Resolution.resolve_equations_rename]
  rfl

end CheckObligation

/-- Rename both components of a simultaneous promotion result. -/
def Promotion.rename (rho : TyRenaming) (promotion : Promotion) : Promotion :=
  { equations := promotion.equations.map (Equation.rename rho)
    pending := promotion.pending.map (CheckObligation.rename rho) }

@[simp] theorem promoteUnder_rename
    (rho : TyRenaming) (substitution : Subst)
    (obligations : List CheckObligation) :
    promoteUnder (Subst.renameSolution rho substitution)
        (obligations.map (CheckObligation.rename rho)) =
      (promoteUnder substitution obligations).rename rho := by
  induction obligations with
  | nil => rfl
  | cons obligation obligations induction =>
      simp only [List.map_cons, promoteUnder]
      change
        (if
          ((obligation.source.rename rho).apply
              (Subst.renameSolution rho substitution)).couldSpecial
            ((obligation.expected.rename rho).apply
              (Subst.renameSolution rho substitution)) then _ else _) = _
      rw [Ty.rename_apply_renameSolution,
        Ty.rename_apply_renameSolution, Ty.couldSpecial_rename]
      split <;> simp [Promotion.rename, induction,
        CheckObligation.rename, Equation.rename]

/-- Forward transport of a most-general solution through a bijective
ordinary-variable renaming. -/
theorem mostGeneral_rename_forward
    (rho : TyRenaming) (equations : List Equation)
    (substitution : Subst)
    (principal : MostGeneral equations substitution) :
      MostGeneral (equations.map (Equation.rename rho))
        (Subst.renameSolution rho substitution) := by
  refine ⟨?_, ?_⟩
  · exact (solves_rename_perm rho substitution (List.Perm.refl _)).mp
      principal.1
  · intro specific solved
    have unrenamedSolved :
        Solves (Subst.renameSolution rho.symm specific) equations := by
      intro equation membership
      have renamedMembership :
          equation.rename rho ∈
            equations.map (Equation.rename rho) :=
        List.mem_map.mpr ⟨equation, membership, rfl⟩
      have held := solved _ renamedMembership
      exact (Equation.holds_rename rho
        (Subst.renameSolution rho.symm specific) equation).mp
        (by simpa using held)
    obtain ⟨later, factor⟩ := principal.2 _ unrenamedSolved
    refine ⟨Subst.renameSolution rho later, ?_⟩
    have renamed := congrArg (Subst.renameSolution rho) factor
    simpa [Subst.renameSolution_compose] using renamed

/-- Most-generality is invariant under a bijective ordinary-variable
renaming. -/
theorem mostGeneral_rename
    (rho : TyRenaming) (equations : List Equation)
    (substitution : Subst) :
    MostGeneral equations substitution ↔
      MostGeneral (equations.map (Equation.rename rho))
        (Subst.renameSolution rho substitution) := by
  constructor
  · exact mostGeneral_rename_forward rho equations substitution
  · intro principal
    have restored := mostGeneral_rename_forward rho.symm
      (equations.map (Equation.rename rho))
      (Subst.renameSolution rho substitution) principal
    simpa [List.map_map, Function.comp_def,
      Equation.rename_symm_apply] using restored

namespace PromotionClosure

/-- Rename every state and every principal solution in a promotion closure. -/
theorem rename
    (rho : TyRenaming)
    {hard pendingHard : List Equation}
    {pending finalPending : List CheckObligation}
    (closure : PromotionClosure hard pending pendingHard finalPending) :
    PromotionClosure
      (hard.map (Equation.rename rho))
      (pending.map (CheckObligation.rename rho))
      (pendingHard.map (Equation.rename rho))
      (finalPending.map (CheckObligation.rename rho)) := by
  induction closure with
  | refl => exact .refl
  | @step hard pending substitution promoted finalHard finalPending
      principal promoted_eq progress remaining induction =>
      let renamedPromotion := promoted.rename rho
      have promotionEquality :
          promoteUnder (Subst.renameSolution rho substitution)
              (pending.map (CheckObligation.rename rho)) =
            renamedPromotion := by
        rw [promoteUnder_rename, promoted_eq]
      have renamedProgress : renamedPromotion.equations ≠ [] := by
        intro empty
        have mappedEmpty :
            promoted.equations.map (Equation.rename rho) = [] := by
          simpa [renamedPromotion, Promotion.rename] using empty
        have : promoted.equations = [] := by simpa using mappedEmpty
        exact progress this
      have appended :
          (hard ++ promoted.equations).map (Equation.rename rho) =
            hard.map (Equation.rename rho) ++ renamedPromotion.equations := by
        simp [renamedPromotion, Promotion.rename]
      rw [appended] at induction
      exact .step
        ((mostGeneral_rename rho hard substitution).mp principal)
        promotionEquality renamedProgress induction

/-- Transport a promotion closure when both input worklists are reordered.
The endpoint worklists are correspondingly permuted. -/
theorem permuteInitial
    {leftHard rightHard : List Equation}
    {leftPending rightPending : List CheckObligation}
    {finalHard : List Equation}
    {finalPending : List CheckObligation}
    (hardPermutation : leftHard.Perm rightHard)
    (pendingPermutation : leftPending.Perm rightPending)
    (closure : PromotionClosure leftHard leftPending
      finalHard finalPending) :
    ∃ transportedHard transportedPending,
      finalHard.Perm transportedHard ∧
        finalPending.Perm transportedPending ∧
        PromotionClosure rightHard rightPending
          transportedHard transportedPending := by
  induction closure generalizing rightHard rightPending with
  | @refl hard pending =>
      exact ⟨rightHard, rightPending, hardPermutation,
        pendingPermutation, .refl⟩
  | @step hard pending substitution promoted finalHard finalPending
      principal promotion progress remaining induction =>
      let transportedPromotion := promoteUnder substitution rightPending
      have promotionPermutations :=
        promoteUnder_perm substitution pendingPermutation
      rw [promotion] at promotionPermutations
      have transportedProgress :
          transportedPromotion.equations ≠ [] := by
        intro empty
        have lengthZero : promoted.equations.length = 0 := by
          rw [promotionPermutations.1.length_eq]
          simp [transportedPromotion, empty]
        have promotedEmpty : promoted.equations = [] := by
          cases equationList : promoted.equations with
          | nil => rfl
          | cons equation equations =>
              simp [equationList] at lengthZero
        exact progress promotedEmpty
      have appendedPermutation :
          (hard ++ promoted.equations).Perm
            (rightHard ++ transportedPromotion.equations) :=
        hardPermutation.append promotionPermutations.1
      obtain ⟨transportedHard, transportedPending,
          finalHardPermutation, finalPendingPermutation,
          transportedRemaining⟩ :=
        induction appendedPermutation promotionPermutations.2
      exact ⟨transportedHard, transportedPending,
        finalHardPermutation, finalPendingPermutation,
        .step
          ((mostGeneral_iff_of_perm hardPermutation substitution).mp
            principal)
          (by rfl) transportedProgress transportedRemaining⟩

end PromotionClosure

namespace Saturated

/-- Rename a complete saturated hard block. -/
theorem rename
    (rho : TyRenaming)
    {hard finalHard : List Equation}
    {pending finalPending : List CheckObligation}
    {substitution : Subst}
    (saturated : Saturated hard pending finalHard finalPending substitution) :
    Saturated
      (hard.map (Equation.rename rho))
      (pending.map (CheckObligation.rename rho))
      (finalHard.map (Equation.rename rho))
      (finalPending.map (CheckObligation.rename rho))
      (Subst.renameSolution rho substitution) := by
  refine
    { closure := saturated.closure.rename rho
      principal := (mostGeneral_rename rho _ _).mp saturated.principal
      stable := ?_ }
  have renamed := promoteUnder_rename rho substitution finalPending
  have equationEquality := congrArg Promotion.equations renamed
  change _ =
    (promoteUnder substitution finalPending).equations.map
      (Equation.rename rho) at equationEquality
  rw [saturated.stable] at equationEquality
  simpa [Promotion.rename] using equationEquality

/-- Saturation is insensitive to the order of both initial worklists. -/
theorem permuteInitial
    {leftHard rightHard : List Equation}
    {leftPending rightPending : List CheckObligation}
    {finalHard : List Equation}
    {finalPending : List CheckObligation}
    {substitution : Subst}
    (hardPermutation : leftHard.Perm rightHard)
    (pendingPermutation : leftPending.Perm rightPending)
    (saturated : Saturated leftHard leftPending
      finalHard finalPending substitution) :
    ∃ transportedHard transportedPending,
      finalHard.Perm transportedHard ∧
        finalPending.Perm transportedPending ∧
        Saturated rightHard rightPending transportedHard
          transportedPending substitution := by
  obtain ⟨transportedHard, transportedPending,
      finalHardPermutation, finalPendingPermutation,
      transportedClosure⟩ :=
    saturated.closure.permuteInitial hardPermutation pendingPermutation
  have transportedStable :
      (promoteUnder substitution transportedPending).equations = [] := by
    have promotedPermutation :=
      (promoteUnder_perm substitution finalPendingPermutation).1
    have transportedLength :
        (promoteUnder substitution transportedPending).equations.length = 0 := by
      rw [← promotedPermutation.length_eq, saturated.stable]
      rfl
    cases equationList :
        (promoteUnder substitution transportedPending).equations with
    | nil => rfl
    | cons equation equations =>
        simp [equationList] at transportedLength
  exact ⟨transportedHard, transportedPending,
    finalHardPermutation, finalPendingPermutation,
    { closure := transportedClosure
      principal :=
        (mostGeneral_iff_of_perm finalHardPermutation substitution).mp
          saturated.principal
      stable := transportedStable }⟩

end Saturated

@[simp] theorem residualEquations_rename
    (rho : TyRenaming) (substitution : Subst)
    (obligations : List CheckObligation) :
    residualEquations (Subst.renameSolution rho substitution)
        (obligations.map (CheckObligation.rename rho)) =
      (residualEquations substitution obligations).map
        (Equation.rename rho) := by
  induction obligations with
  | nil => rfl
  | cons obligation obligations induction =>
      simp [residualEquations, CheckObligation.residualEquations_rename,
        induction]

/-- Solving a residual worklist is invariant under fresh-variable renaming. -/
theorem solves_residualEquations_rename
    (rho : TyRenaming) (hardSubstitution residualSubstitution : Subst)
    (obligations : List CheckObligation) :
    Solves residualSubstitution
        (residualEquations hardSubstitution obligations) ↔
      Solves (Subst.renameSolution rho residualSubstitution)
        (residualEquations
          (Subst.renameSolution rho hardSubstitution)
          (obligations.map (CheckObligation.rename rho))) := by
  rw [residualEquations_rename]
  exact solves_rename_perm rho residualSubstitution (List.Perm.refl _)

/-- Solving residual equations depends only on the order-independent pending
worklist. -/
theorem solves_residualEquations_iff_of_perm
    (hardSubstitution residualSubstitution : Subst)
    {left right : List CheckObligation}
    (permutation : left.Perm right) :
    Solves residualSubstitution
        (residualEquations hardSubstitution left) ↔
      Solves residualSubstitution
        (residualEquations hardSubstitution right) := by
  exact solves_iff_of_perm
    (residualEquations_perm hardSubstitution permutation)
    residualSubstitution

namespace TypingDerivation

/-- Transport a complete typing witness to an explicitly alpha-renamed and
reordered generated problem.  A relational generation derivation for the
transported problem is supplied independently; the theorem below transforms
all declarative solving evidence. -/
theorem transportGenerated
    {context : Context} {expression : Expr} {target : Ty}
    (derivation : TypingDerivation context expression target)
    (rho : TyRenaming)
    {generated : Generated} {next : Nat}
    (generation : Generates context expression context.nextVar generated next)
    (targetEquality :
      derivation.generated.target.rename rho = generated.target)
    (hardPermutation :
      (derivation.generated.hard.map (Equation.rename rho)).Perm
        generated.hard)
    (pendingPermutation :
      (derivation.generated.pending.map (CheckObligation.rename rho)).Perm
        generated.pending) :
    Nonempty (TypingDerivation context expression (target.rename rho)) := by
  have renamedSaturation := derivation.saturation.rename rho
  obtain ⟨transportedHard, transportedPending,
      finalHardPermutation, finalPendingPermutation,
      transportedSaturation⟩ :=
    renamedSaturation.permuteInitial hardPermutation pendingPermutation
  have renamedResidualSolved :
      Solves (Subst.renameSolution rho derivation.residualSubstitution)
        (residualEquations
          (Subst.renameSolution rho derivation.hardSubstitution)
          (derivation.finalPending.map (CheckObligation.rename rho))) :=
    (solves_residualEquations_rename rho
      derivation.hardSubstitution derivation.residualSubstitution
      derivation.finalPending).mp derivation.residualSolved
  have transportedResidualSolved :
      Solves (Subst.renameSolution rho derivation.residualSubstitution)
        (residualEquations
          (Subst.renameSolution rho derivation.hardSubstitution)
          transportedPending) :=
    (solves_residualEquations_iff_of_perm
      (Subst.renameSolution rho derivation.hardSubstitution)
      (Subst.renameSolution rho derivation.residualSubstitution)
      finalPendingPermutation).mp renamedResidualSolved
  refine ⟨
    { generated := generated
      next := next
      finalHard := transportedHard
      finalPending := transportedPending
      hardSubstitution :=
        Subst.renameSolution rho derivation.hardSubstitution
      residualSubstitution :=
        Subst.renameSolution rho derivation.residualSubstitution
      generation := generation
      saturation := transportedSaturation
      residualSolved := transportedResidualSolved
      target_eq := ?_ }⟩
  calc
    target.rename rho =
        (derivation.generated.target.apply
          (Subst.compose derivation.residualSubstitution
            derivation.hardSubstitution)).rename rho := by
      exact congrArg (Ty.rename rho) derivation.target_eq
    _ = (derivation.generated.target.rename rho).apply
          (Subst.renameSolution rho
            (Subst.compose derivation.residualSubstitution
              derivation.hardSubstitution)) := by
      exact (Ty.rename_apply_renameSolution rho
        (Subst.compose derivation.residualSubstitution
          derivation.hardSubstitution)
        derivation.generated.target).symm
    _ = generated.target.apply
          (Subst.compose
            (Subst.renameSolution rho derivation.residualSubstitution)
            (Subst.renameSolution rho derivation.hardSubstitution)) := by
      rw [targetEquality, Subst.renameSolution_compose]

/-- Alpha-equivalent generated problems carry the same typing evidence up to
the witnessing fresh-variable renaming, once relational generation of the
second problem is available. -/
theorem transportAlphaEq
    {context : Context} {expression : Expr} {target : Ty}
    (derivation : TypingDerivation context expression target)
    {generated : Generated} {next : Nat}
    (generation : Generates context expression context.nextVar generated next)
    (equivalence : derivation.generated.AlphaEq generated) :
    ∃ rho : TyRenaming,
      rho.FiniteSupport ∧
        Nonempty
          (TypingDerivation context expression (target.rename rho)) := by
  rcases equivalence with
    ⟨rho, finite, targetEquality, hardPermutation, pendingPermutation⟩
  exact ⟨rho, finite,
    derivation.transportGenerated rho generation targetEquality
      hardPermutation pendingPermutation⟩

end TypingDerivation

end TypePM
