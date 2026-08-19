import TypePM.GeneralizationTransport
import TypePM.Source.Elaboration
import TypePM.Source.ElaborationTransport
import TypePM.BlockOrderInvariance

/-!
# Two-sort renaming transport for source elaboration

Source elaboration allocates ordinary and capability variables from separate
numeric supplies.  This module first develops the global, bijective renaming
algebra needed at a nested `let` boundary.  Fresh-supply transport is stated
separately, because a bijection must map each actually allocated finite
interval in order; bijectivity alone says nothing about numeric allocation
order.
-/

namespace TypePM.Source

namespace VariableRenaming

def symm (rho : VariableRenaming) : VariableRenaming :=
  { tyForward := rho.tyBackward
    tyBackward := rho.tyForward
    capForward := rho.capBackward
    capBackward := rho.capForward
    ty_backward_forward := rho.ty_forward_backward
    ty_forward_backward := rho.ty_backward_forward
    cap_backward_forward := rho.cap_forward_backward
    cap_forward_backward := rho.cap_backward_forward }

@[simp] theorem symm_tyForward (rho : VariableRenaming) (index : TyVar) :
    rho.symm.tyForward index = rho.tyBackward index := rfl

@[simp] theorem symm_capForward (rho : VariableRenaming) (index : CapVar) :
    rho.symm.capForward index = rho.capBackward index := rfl

@[simp] theorem symm_tyBackward (rho : VariableRenaming) (index : TyVar) :
    rho.symm.tyBackward index = rho.tyForward index := rfl

@[simp] theorem symm_capBackward (rho : VariableRenaming) (index : CapVar) :
    rho.symm.capBackward index = rho.capForward index := rfl

@[simp] theorem backward_forward_ty (rho : VariableRenaming) (index : TyVar) :
    rho.tyBackward (rho.tyForward index) = index :=
  rho.ty_backward_forward index

@[simp] theorem forward_backward_ty (rho : VariableRenaming) (index : TyVar) :
    rho.tyForward (rho.tyBackward index) = index :=
  rho.ty_forward_backward index

@[simp] theorem backward_forward_cap
    (rho : VariableRenaming) (index : CapVar) :
    rho.capBackward (rho.capForward index) = index :=
  rho.cap_backward_forward index

@[simp] theorem forward_backward_cap
    (rho : VariableRenaming) (index : CapVar) :
    rho.capForward (rho.capBackward index) = index :=
  rho.cap_forward_backward index

@[simp] theorem substitution_symm_compose (rho : VariableRenaming) :
    Subst.compose rho.symm.substitution rho.substitution = Subst.id := by
  apply Subst.eq_of_components
  · intro index
    simp [VariableRenaming.substitution, Subst.compose, Subst.id, Cap.apply]
  · intro index
    simp [VariableRenaming.substitution, Subst.compose, Subst.id, Ty.apply]

@[simp] theorem substitution_compose_symm (rho : VariableRenaming) :
    Subst.compose rho.substitution rho.symm.substitution = Subst.id := by
  apply Subst.eq_of_components
  · intro index
    simp [VariableRenaming.substitution, Subst.compose, Subst.id, Cap.apply]
  · intro index
    simp [VariableRenaming.substitution, Subst.compose, Subst.id, Ty.apply]

end VariableRenaming


namespace ElaborationRenaming

def renameCap (rho : VariableRenaming) (capability : Cap) : Cap :=
  capability.apply rho.substitution.cap

def renameTy (rho : VariableRenaming) (target : Ty) : Ty :=
  target.apply rho.substitution

def renameEquation (rho : VariableRenaming) : Equation → Equation :=
  Equation.apply rho.substitution

def renameObligation (rho : VariableRenaming)
    (obligation : CheckObligation) : CheckObligation :=
  obligation.apply rho.substitution

def renameGenerated (rho : VariableRenaming) (generated : Generated) :
    Generated :=
  { target := renameTy rho generated.target
    hard := generated.hard.map (renameEquation rho)
    pending := generated.pending.map (renameObligation rho) }

def renameGeneratedItems (rho : VariableRenaming)
    (generated : GeneratedItems) : GeneratedItems :=
  { targets := Ty.applyList rho.substitution generated.targets
    hard := generated.hard.map (renameEquation rho)
    pending := generated.pending.map (renameObligation rho) }

def renameContext (rho : VariableRenaming) (context : Context) : Context :=
  context.applyFree rho.substitution

/-- Conjugate a solution by the global two-sort change of names. -/
def renameSubstitution (rho : VariableRenaming)
    (substitution : Subst) : Subst :=
  { ty := fun index =>
      (substitution.ty (rho.tyBackward index)).apply rho.substitution
    cap := fun index =>
      (substitution.cap (rho.capBackward index)).apply
        rho.substitution.cap }

theorem compose_renameSubstitution_forward
    (rho : VariableRenaming) (substitution : Subst) :
    Subst.compose (renameSubstitution rho substitution) rho.substitution =
      Subst.compose rho.substitution substitution := by
  apply Subst.eq_of_components
  · intro index
    simp [renameSubstitution, VariableRenaming.substitution,
      Subst.compose, Cap.apply]
  · intro index
    simp [renameSubstitution, VariableRenaming.substitution,
      Subst.compose, Ty.apply]

@[simp] theorem renameTy_apply_renameSubstitution
    (rho : VariableRenaming) (substitution : Subst) (target : Ty) :
    (renameTy rho target).apply (renameSubstitution rho substitution) =
      renameTy rho (target.apply substitution) := by
  simp only [renameTy, Ty.apply_compose]
  rw [compose_renameSubstitution_forward]

@[simp] theorem renameCap_apply_renameSubstitution
    (rho : VariableRenaming) (substitution : Subst) (capability : Cap) :
    (renameCap rho capability).apply
        (renameSubstitution rho substitution).cap =
      renameCap rho (capability.apply substitution.cap) := by
  simp only [renameCap, Cap.apply_compose]
  rw [compose_renameSubstitution_forward]

@[simp] theorem renameTy_symm_apply
    (rho : VariableRenaming) (target : Ty) :
    renameTy rho.symm (renameTy rho target) = target := by
  simp [renameTy, Ty.apply_compose]

@[simp] theorem renameCap_symm_apply
    (rho : VariableRenaming) (capability : Cap) :
    renameCap rho.symm (renameCap rho capability) = capability := by
  simp [renameCap, Cap.apply_compose]

@[simp] theorem renameEquation_symm_apply
    (rho : VariableRenaming) (equation : Equation) :
    renameEquation rho.symm (renameEquation rho equation) = equation := by
  cases equation <;>
    simp [renameEquation, Equation.apply,
      Ty.apply_compose, Cap.apply_compose]

@[simp] theorem renameObligation_symm_apply
    (rho : VariableRenaming) (obligation : CheckObligation) :
    renameObligation rho.symm (renameObligation rho obligation) = obligation := by
  cases obligation
  simp [renameObligation, CheckObligation.apply]

@[simp] theorem renameGenerated_symm_apply
    (rho : VariableRenaming) (generated : Generated) :
    renameGenerated rho.symm (renameGenerated rho generated) = generated := by
  cases generated
  simp [renameGenerated, List.map_map, Function.comp_def]

@[simp] theorem renameSubstitution_symm_apply
    (rho : VariableRenaming) (substitution : Subst) :
    renameSubstitution rho.symm (renameSubstitution rho substitution) =
      substitution := by
  apply Subst.eq_of_components
  · intro index
    simp [renameSubstitution, Cap.apply_compose]
  · intro index
    simp [renameSubstitution, Ty.apply_compose]

@[simp] theorem renameSubstitution_apply_symm
    (rho : VariableRenaming) (substitution : Subst) :
    renameSubstitution rho (renameSubstitution rho.symm substitution) =
      substitution := by
  apply Subst.eq_of_components
  · intro index
    simp [renameSubstitution, Cap.apply_compose]
  · intro index
    simp [renameSubstitution, Ty.apply_compose]

theorem renameSubstitution_compose
    (rho : VariableRenaming) (later earlier : Subst) :
    renameSubstitution rho (Subst.compose later earlier) =
      Subst.compose (renameSubstitution rho later)
        (renameSubstitution rho earlier) := by
  apply Subst.eq_of_components
  · intro index
    simpa [renameSubstitution, Subst.compose, renameCap] using
      (renameCap_apply_renameSubstitution rho later
        (earlier.cap (rho.capBackward index))).symm
  · intro index
    simpa [renameSubstitution, Subst.compose, renameTy] using
      (renameTy_apply_renameSubstitution rho later
        (earlier.ty (rho.tyBackward index))).symm

theorem Equation.holds_renameVariables
    (rho : VariableRenaming) (substitution : Subst)
    (equation : Equation) :
    Equation.Holds (renameSubstitution rho substitution)
        (renameEquation rho equation) ↔
      Equation.Holds substitution equation := by
  cases equation with
  | cap left right =>
      change
        (renameCap rho left).apply (renameSubstitution rho substitution).cap =
            (renameCap rho right).apply
              (renameSubstitution rho substitution).cap ↔ _
      rw [renameCap_apply_renameSubstitution,
        renameCap_apply_renameSubstitution]
      constructor
      · intro equality
        have restored := congrArg (renameCap rho.symm) equality
        change left.apply substitution.cap = right.apply substitution.cap
        simpa using restored
      · change left.apply substitution.cap = right.apply substitution.cap → _
        exact congrArg (renameCap rho)
  | ty left right =>
      change
        (renameTy rho left).apply (renameSubstitution rho substitution) =
            (renameTy rho right).apply
              (renameSubstitution rho substitution) ↔ _
      rw [renameTy_apply_renameSubstitution,
        renameTy_apply_renameSubstitution]
      constructor
      · intro equality
        have restored := congrArg (renameTy rho.symm) equality
        change left.apply substitution = right.apply substitution
        simpa using restored
      · change left.apply substitution = right.apply substitution → _
        exact congrArg (renameTy rho)

theorem solves_renameVariables
    (rho : VariableRenaming) (substitution : Subst)
    (equations : List Equation) :
    Solves (renameSubstitution rho substitution)
        (equations.map (renameEquation rho)) ↔
      Solves substitution equations := by
  constructor
  · intro solved equation membership
    exact (Equation.holds_renameVariables rho substitution equation).mp
      (solved _ (List.mem_map.mpr ⟨equation, membership, rfl⟩))
  · intro solved equation membership
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp membership
    exact (Equation.holds_renameVariables rho substitution source).mpr
      (solved source sourceMember)

theorem mostGeneral_renameVariables_forward
    (rho : VariableRenaming) (equations : List Equation)
    (substitution : Subst) (principal : MostGeneral equations substitution) :
    MostGeneral (equations.map (renameEquation rho))
      (renameSubstitution rho substitution) := by
  refine ⟨(solves_renameVariables rho substitution equations).mpr
    principal.1, ?_⟩
  intro specific solved
  have restoredSolved :
      Solves (renameSubstitution rho.symm specific) equations := by
    intro equation membership
    apply (Equation.holds_renameVariables rho
      (renameSubstitution rho.symm specific) equation).mp
    simpa using solved (renameEquation rho equation)
      (List.mem_map.mpr ⟨equation, membership, rfl⟩)
  obtain ⟨later, factor⟩ := principal.2 _ restoredSolved
  refine ⟨renameSubstitution rho later, ?_⟩
  have renamed := congrArg (renameSubstitution rho) factor
  simpa [renameSubstitution_compose] using renamed

theorem mostGeneral_renameVariables
    (rho : VariableRenaming) (equations : List Equation)
    (substitution : Subst) :
    MostGeneral equations substitution ↔
      MostGeneral (equations.map (renameEquation rho))
        (renameSubstitution rho substitution) := by
  constructor
  · exact mostGeneral_renameVariables_forward rho equations substitution
  · intro principal
    have restored := mostGeneral_renameVariables_forward rho.symm
      (equations.map (renameEquation rho))
      (renameSubstitution rho substitution) principal
    simpa [List.map_map, Function.comp_def] using restored

theorem absorbingPrincipal_renameVariables
    (rho : VariableRenaming) (equations : List Equation)
    (substitution : Subst)
    (absorbing : AbsorbingPrincipal equations substitution) :
    AbsorbingPrincipal (equations.map (renameEquation rho))
      (renameSubstitution rho substitution) := by
  refine ⟨(mostGeneral_renameVariables rho equations substitution).mp
    absorbing.1, ?_⟩
  intro solution solved
  have restoredSolved :
      Solves (renameSubstitution rho.symm solution) equations := by
    intro equation membership
    apply (Equation.holds_renameVariables rho
      (renameSubstitution rho.symm solution) equation).mp
    simpa using solved (renameEquation rho equation)
      (List.mem_map.mpr ⟨equation, membership, rfl⟩)
  have absorbed := absorbing.2 _ restoredSolved
  have renamed := congrArg (renameSubstitution rho) absorbed
  simpa [renameSubstitution_compose] using renamed


namespace Ty

@[simp] theorem mayBecomeMatcher_renameVariables
    (rho : VariableRenaming) (target : TypePM.Ty) :
    (renameTy rho target).mayBecomeMatcher = target.mayBecomeMatcher := by
  cases target <;> rfl

@[simp] theorem mayBecomeMatcherItems_renameVariables
    (rho : VariableRenaming) (targets : List TypePM.Ty) :
    TypePM.Ty.mayBecomeMatcherItems
        (TypePM.Ty.applyList rho.substitution targets) =
      TypePM.Ty.mayBecomeMatcherItems targets := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp only [TypePM.Ty.applyList, TypePM.Ty.mayBecomeMatcherItems]
      rw [show (target.apply rho.substitution).mayBecomeMatcher =
          target.mayBecomeMatcher by
        exact mayBecomeMatcher_renameVariables rho target,
        induction]

@[simp] theorem mayBecomeMatcherProduct_renameVariables
    (rho : VariableRenaming) (target : TypePM.Ty) :
    (renameTy rho target).mayBecomeMatcherProduct =
      target.mayBecomeMatcherProduct := by
  cases target with
  | prod items =>
      cases items with
      | nil => rfl
      | cons item items =>
          simp only [renameTy, TypePM.Ty.apply, TypePM.Ty.applyList,
            TypePM.Ty.mayBecomeMatcherProduct]
          rw [show (item.apply rho.substitution).mayBecomeMatcher =
              item.mayBecomeMatcher by
            exact mayBecomeMatcher_renameVariables rho item,
            mayBecomeMatcherItems_renameVariables]
  | _ => rfl

@[simp] theorem mayBecomeExpectedMatcher_renameVariables
    (rho : VariableRenaming) (target : TypePM.Ty) :
    (renameTy rho target).mayBecomeExpectedMatcher =
      target.mayBecomeExpectedMatcher := by
  cases target <;> rfl

@[simp] theorem mayBecomeExpectedSlot_renameVariables
    (rho : VariableRenaming) (target : TypePM.Ty) :
    (renameTy rho target).mayBecomeExpectedSlot =
      target.mayBecomeExpectedSlot := by
  cases target <;> rfl

@[simp] theorem couldSpecial_renameVariables
    (rho : VariableRenaming) (source expected : TypePM.Ty) :
    (renameTy rho source).couldSpecial (renameTy rho expected) =
      source.couldSpecial expected := by
  simp [TypePM.Ty.couldSpecial]

end Ty


theorem Resolution.resolve_equations_renameVariables
    (rho : VariableRenaming) (source expected : Ty) :
    (resolve (renameTy rho source) (renameTy rho expected)).equations =
      (resolve source expected).equations.map (renameEquation rho) := by
  have sourceRetract :
      (source.apply rho.substitution).apply rho.symm.substitution = source := by
    simp [Ty.apply_compose]
  have expectedRetract :
      (expected.apply rho.substitution).apply rho.symm.substitution =
        expected := by
    simp [Ty.apply_compose]
  have canonical := Resolution.resolve_apply_canonical_of_retract
    rho.substitution rho.symm.substitution source expected
    sourceRetract expectedRetract
  simpa [renameTy, renameEquation] using canonical.2

@[simp] theorem CheckObligation.apply_renameSubstitution
    (rho : VariableRenaming) (substitution : Subst)
    (obligation : CheckObligation) :
    (renameObligation rho obligation).apply
        (renameSubstitution rho substitution) =
      renameObligation rho (obligation.apply substitution) := by
  cases obligation with
  | mk source expected =>
      simp only [renameObligation, CheckObligation.apply]
      have sourceEquality :=
        renameTy_apply_renameSubstitution rho substitution source
      have expectedEquality :=
        renameTy_apply_renameSubstitution rho substitution expected
      change
        CheckObligation.mk
          ((renameTy rho source).apply
            (renameSubstitution rho substitution))
          ((renameTy rho expected).apply
            (renameSubstitution rho substitution)) = _
      rw [sourceEquality, expectedEquality]
      rfl

@[simp] theorem CheckObligation.residualEquations_renameVariables
    (rho : VariableRenaming) (substitution : Subst)
    (obligation : CheckObligation) :
    (renameObligation rho obligation).residualEquations
        (renameSubstitution rho substitution) =
      (obligation.residualEquations substitution).map
        (renameEquation rho) := by
  change
    (resolve
      ((renameObligation rho obligation).source.apply
        (renameSubstitution rho substitution))
      ((renameObligation rho obligation).expected.apply
        (renameSubstitution rho substitution))).equations = _
  rw [show (renameObligation rho obligation).source =
      renameTy rho obligation.source by rfl,
    show (renameObligation rho obligation).expected =
      renameTy rho obligation.expected by rfl,
    renameTy_apply_renameSubstitution,
    renameTy_apply_renameSubstitution,
    Resolution.resolve_equations_renameVariables]
  rfl

def renamePromotion (rho : VariableRenaming)
    (promotion : Promotion) : Promotion :=
  { equations := promotion.equations.map (renameEquation rho)
    pending := promotion.pending.map (renameObligation rho) }

@[simp] theorem promoteUnder_renameVariables
    (rho : VariableRenaming) (substitution : Subst)
    (obligations : List CheckObligation) :
    promoteUnder (renameSubstitution rho substitution)
        (obligations.map (renameObligation rho)) =
      renamePromotion rho (promoteUnder substitution obligations) := by
  induction obligations with
  | nil => rfl
  | cons obligation obligations induction =>
      simp only [List.map_cons, promoteUnder]
      change
        (if
          ((renameTy rho obligation.source).apply
              (renameSubstitution rho substitution)).couldSpecial
            ((renameTy rho obligation.expected).apply
              (renameSubstitution rho substitution)) then _ else _) = _
      rw [renameTy_apply_renameSubstitution,
        renameTy_apply_renameSubstitution,
        Ty.couldSpecial_renameVariables]
      split <;>
        simp [renamePromotion, induction, renameObligation,
          renameEquation, CheckObligation.apply, Equation.apply]

namespace PromotionClosure

theorem renameVariables
    (rho : VariableRenaming)
    {hard finalHard : List Equation}
    {pending finalPending : List CheckObligation}
    (closure : PromotionClosure hard pending finalHard finalPending) :
    PromotionClosure
      (hard.map (renameEquation rho))
      (pending.map (renameObligation rho))
      (finalHard.map (renameEquation rho))
      (finalPending.map (renameObligation rho)) := by
  induction closure with
  | refl => exact .refl
  | @step hard pending substitution promoted finalHard finalPending
      principal promotedEquality progress remaining induction =>
      let renamedPromotion := renamePromotion rho promoted
      have promotionEquality :
          promoteUnder (renameSubstitution rho substitution)
              (pending.map (renameObligation rho)) =
            renamedPromotion := by
        rw [promoteUnder_renameVariables, promotedEquality]
      have renamedProgress : renamedPromotion.equations ≠ [] := by
        intro empty
        have mappedEmpty :
            promoted.equations.map (renameEquation rho) = [] := by
          simpa [renamedPromotion, renamePromotion] using empty
        exact progress (by simpa using mappedEmpty)
      have appended :
          (hard ++ promoted.equations).map (renameEquation rho) =
            hard.map (renameEquation rho) ++ renamedPromotion.equations := by
        simp [renamedPromotion, renamePromotion]
      rw [appended] at induction
      exact .step
        ((mostGeneral_renameVariables rho hard substitution).mp principal)
        promotionEquality renamedProgress induction

end PromotionClosure


namespace Saturated

theorem renameVariables
    (rho : VariableRenaming)
    {hard finalHard : List Equation}
    {pending finalPending : List CheckObligation}
    {substitution : Subst}
    (saturated : Saturated hard pending finalHard finalPending substitution) :
    Saturated
      (hard.map (renameEquation rho))
      (pending.map (renameObligation rho))
      (finalHard.map (renameEquation rho))
      (finalPending.map (renameObligation rho))
      (renameSubstitution rho substitution) := by
  refine
    { closure :=
        ElaborationRenaming.PromotionClosure.renameVariables rho
          saturated.closure
      principal :=
        (mostGeneral_renameVariables rho _ _).mp saturated.principal
      stable := ?_ }
  have renamed := promoteUnder_renameVariables rho substitution finalPending
  have equationsEquality := congrArg Promotion.equations renamed
  change _ =
    (promoteUnder substitution finalPending).equations.map
      (renameEquation rho) at equationsEquality
  rw [saturated.stable] at equationsEquality
  simpa [renamePromotion] using equationsEquality

end Saturated


@[simp] theorem residualEquations_renameVariables
    (rho : VariableRenaming) (substitution : Subst)
    (obligations : List CheckObligation) :
    residualEquations (renameSubstitution rho substitution)
        (obligations.map (renameObligation rho)) =
      (residualEquations substitution obligations).map
        (renameEquation rho) := by
  induction obligations with
  | nil => rfl
  | cons obligation obligations induction =>
      simp [residualEquations,
        CheckObligation.residualEquations_renameVariables,
        List.map_append, induction]


def renameClosure {generated : Generated}
    (rho : VariableRenaming) (closure : PrincipalBlockClosure generated) :
    PrincipalBlockClosure (renameGenerated rho generated) :=
  { finalHard := closure.finalHard.map (renameEquation rho)
    finalPending := closure.finalPending.map (renameObligation rho)
    hardSubstitution := renameSubstitution rho closure.hardSubstitution
    residualSubstitution :=
      renameSubstitution rho closure.residualSubstitution
    saturation :=
      ElaborationRenaming.Saturated.renameVariables rho closure.saturation
    residualPrincipal := by
      rw [residualEquations_renameVariables]
      exact (mostGeneral_renameVariables rho _ _).mp
        closure.residualPrincipal }

@[simp] theorem renameClosure_substitution {generated : Generated}
    (rho : VariableRenaming) (closure : PrincipalBlockClosure generated) :
    (renameClosure rho closure).substitution =
      renameSubstitution rho closure.substitution := by
  change
    Subst.compose
        (renameSubstitution rho closure.residualSubstitution)
        (renameSubstitution rho closure.hardSubstitution) =
      renameSubstitution rho
        (Subst.compose closure.residualSubstitution
          closure.hardSubstitution)
  exact (renameSubstitution_compose rho closure.residualSubstitution
    closure.hardSubstitution).symm

@[simp] theorem renameClosure_target {generated : Generated}
    (rho : VariableRenaming) (closure : PrincipalBlockClosure generated) :
    (renameClosure rho closure).target = renameTy rho closure.target := by
  change
    (renameTy rho generated.target).apply
        (renameClosure rho closure).substitution =
      renameTy rho (generated.target.apply closure.substitution)
  rw [renameClosure_substitution]
  exact renameTy_apply_renameSubstitution rho closure.substitution
    generated.target

theorem renameClosure_absorbing {generated : Generated}
    (rho : VariableRenaming) (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) :
    (renameClosure rho closure).Absorbing := by
  change
    AbsorbingPrincipal
        (closure.finalHard.map (renameEquation rho))
        (renameSubstitution rho closure.hardSubstitution) ∧
      AbsorbingPrincipal
        (residualEquations
          (renameSubstitution rho closure.hardSubstitution)
          (closure.finalPending.map (renameObligation rho)))
        (renameSubstitution rho closure.residualSubstitution)
  constructor
  · exact absorbingPrincipal_renameVariables rho _ _ absorbing.1
  · rw [show residualEquations
      (renameSubstitution rho closure.hardSubstitution)
      (closure.finalPending.map (renameObligation rho)) =
        (residualEquations closure.hardSubstitution
          closure.finalPending).map (renameEquation rho) by
        exact residualEquations_renameVariables rho
          closure.hardSubstitution closure.finalPending]
    exact absorbingPrincipal_renameVariables rho _ _ absorbing.2

/-- Acceptance of a generated block is preserved by a bijective two-sort
change of names. -/
theorem blockAccepts_renameVariables_forward
    (rho : VariableRenaming) {generated : Generated}
    (accepts : BlockAccepts generated) :
    BlockAccepts (renameGenerated rho generated) := by
  rcases accepts with
    ⟨finalHard, finalPending, hardSubstitution, residualSubstitution,
      saturation, residualSolved⟩
  refine ⟨finalHard.map (renameEquation rho),
    finalPending.map (renameObligation rho),
    renameSubstitution rho hardSubstitution,
    renameSubstitution rho residualSubstitution,
    Saturated.renameVariables rho saturation, ?_⟩
  rw [residualEquations_renameVariables]
  exact (solves_renameVariables rho residualSubstitution _).mpr
    residualSolved

/-- Two-sort renaming preserves and reflects block acceptance. -/
theorem blockAccepts_renameVariables
    (rho : VariableRenaming) (generated : Generated) :
    BlockAccepts (renameGenerated rho generated) ↔
      BlockAccepts generated := by
  constructor
  · intro accepts
    have restored := blockAccepts_renameVariables_forward rho.symm accepts
    simpa using restored
  · exact blockAccepts_renameVariables_forward rho

theorem blockAccepts_renameVariables_iff
    (rho : VariableRenaming) (generated : Generated) :
    BlockAccepts generated ↔
      BlockAccepts (renameGenerated rho generated) :=
  (blockAccepts_renameVariables rho generated).symm


mutual

@[simp] theorem PolyCap.freeCapVars_applyFree_renaming
    (rho : VariableRenaming) (capability : PolyCap) :
    (capability.applyFree rho.substitution.cap).freeCapVars =
      capability.freeCapVars.map rho.capForward := by
  cases capability with
  | any => rfl
  | free index => rfl
  | bound index => rfl
  | prod items =>
      simp [PolyCap.applyFree, PolyCap.freeCapVars,
        PolyCap.freeCapVarsList_applyFree_renaming]
  | con former arguments =>
      simp [PolyCap.applyFree, PolyCap.freeCapVars,
        PolyCap.freeCapVarsList_applyFree_renaming]

@[simp] theorem PolyCap.freeCapVarsList_applyFree_renaming
    (rho : VariableRenaming) (items : List PolyCap) :
    PolyCap.freeCapVarsList
        (PolyCap.applyFreeList rho.substitution.cap items) =
      (PolyCap.freeCapVarsList items).map rho.capForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.applyFreeList, PolyCap.freeCapVarsList,
        PolyCap.freeCapVars_applyFree_renaming,
        PolyCap.freeCapVarsList_applyFree_renaming, List.map_append]

end


mutual

@[simp] theorem PolyTy.freeTyVars_applyFree_renaming
    (rho : VariableRenaming) (target : PolyTy) :
    (target.applyFree rho.substitution).freeTyVars =
      target.freeTyVars.map rho.tyForward := by
  cases target with
  | free index => rfl
  | bound index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVars_applyFree_renaming, List.map_append]
  | prod items =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVarsList_applyFree_renaming]
  | data former arguments =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVarsList_applyFree_renaming]
  | matcher capability target =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVars_applyFree_renaming]
  | slot capability target =>
      simp [PolyTy.applyFree, PolyTy.freeTyVars,
        PolyTy.freeTyVars_applyFree_renaming]

@[simp] theorem PolyTy.freeTyVarsList_applyFree_renaming
    (rho : VariableRenaming) (items : List PolyTy) :
    PolyTy.freeTyVarsList
        (PolyTy.applyFreeList rho.substitution items) =
      (PolyTy.freeTyVarsList items).map rho.tyForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.applyFreeList, PolyTy.freeTyVarsList,
        PolyTy.freeTyVars_applyFree_renaming,
        PolyTy.freeTyVarsList_applyFree_renaming, List.map_append]

end


mutual

@[simp] theorem PolyTy.freeCapVars_applyFree_renaming
    (rho : VariableRenaming) (target : PolyTy) :
    (target.applyFree rho.substitution).freeCapVars =
      target.freeCapVars.map rho.capForward := by
  cases target with
  | free index => rfl
  | bound index => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVars_applyFree_renaming, List.map_append]
  | prod items =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVarsList_applyFree_renaming]
  | data former arguments =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVarsList_applyFree_renaming]
  | matcher capability target =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVars_applyFree_renaming,
        List.map_append]
  | slot capability target =>
      simp [PolyTy.applyFree, PolyTy.freeCapVars,
        PolyTy.freeCapVars_applyFree_renaming,
        List.map_append]

@[simp] theorem PolyTy.freeCapVarsList_applyFree_renaming
    (rho : VariableRenaming) (items : List PolyTy) :
    PolyTy.freeCapVarsList
        (PolyTy.applyFreeList rho.substitution items) =
      (PolyTy.freeCapVarsList items).map rho.capForward := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.applyFreeList, PolyTy.freeCapVarsList,
        PolyTy.freeCapVars_applyFree_renaming,
        PolyTy.freeCapVarsList_applyFree_renaming, List.map_append]

end


@[simp] theorem Scheme.freeTyVars_applyFree_renaming
    (rho : VariableRenaming) (scheme : Scheme) :
    (scheme.applyFree rho.substitution).freeTyVars =
      scheme.freeTyVars.map rho.tyForward := by
  simp [Scheme.freeTyVars, Scheme.applyFree,
    dedupFirst_map_of_injective rho.tyForward rho.tyForward_injective]

@[simp] theorem Scheme.freeCapVars_applyFree_renaming
    (rho : VariableRenaming) (scheme : Scheme) :
    (scheme.applyFree rho.substitution).freeCapVars =
      scheme.freeCapVars.map rho.capForward := by
  simp [Scheme.freeCapVars, Scheme.applyFree,
    dedupFirst_map_of_injective rho.capForward rho.capForward_injective]


theorem flatMap_schemeFreeTyVars_renaming
    (rho : VariableRenaming) (context : Context) :
    (context.map (Scheme.applyFree rho.substitution)).flatMap
        Scheme.freeTyVars =
      (context.flatMap Scheme.freeTyVars).map rho.tyForward := by
  induction context with
  | nil => rfl
  | cons scheme context induction =>
      simp [induction, List.map_append]

theorem flatMap_schemeFreeCapVars_renaming
    (rho : VariableRenaming) (context : Context) :
    (context.map (Scheme.applyFree rho.substitution)).flatMap
        Scheme.freeCapVars =
      (context.flatMap Scheme.freeCapVars).map rho.capForward := by
  induction context with
  | nil => rfl
  | cons scheme context induction =>
      simp [induction, List.map_append]


@[simp] theorem Context.freeTyVars_renameContext
    (rho : VariableRenaming) (context : Context) :
    (renameContext rho context).freeTyVars =
      context.freeTyVars.map rho.tyForward := by
  simp [renameContext, Context.applyFree, Context.freeTyVars,
    flatMap_schemeFreeTyVars_renaming,
    dedupFirst_map_of_injective rho.tyForward rho.tyForward_injective]

@[simp] theorem Context.freeCapVars_renameContext
    (rho : VariableRenaming) (context : Context) :
    (renameContext rho context).freeCapVars =
      context.freeCapVars.map rho.capForward := by
  simp [renameContext, Context.applyFree, Context.freeCapVars,
    flatMap_schemeFreeCapVars_renaming,
    dedupFirst_map_of_injective rho.capForward rho.capForward_injective]

@[simp] theorem renameSubstitution_tyForward
    (rho : VariableRenaming) (substitution : Subst) (index : TyVar) :
    (renameSubstitution rho substitution).ty (rho.tyForward index) =
      renameTy rho (substitution.ty index) := by
  simp [renameSubstitution, renameTy]

@[simp] theorem renameSubstitution_capForward
    (rho : VariableRenaming) (substitution : Subst) (index : CapVar) :
    (renameSubstitution rho substitution).cap (rho.capForward index) =
      renameCap rho (substitution.cap index) := by
  simp [renameSubstitution, renameCap]

/-- Renaming a context after closing a block agrees literally with closing
the renamed context by the conjugated block solution. -/
theorem renameContext_applyClosure {generated : Generated}
    (rho : VariableRenaming) (context : Context)
    (closure : PrincipalBlockClosure generated) :
    renameContext rho (context.applyFree closure.substitution) =
      (renameContext rho context).applyFree
        (renameClosure rho closure).substitution := by
  simp only [renameContext, Context.applyFree_compose,
    renameClosure_substitution]
  rw [compose_renameSubstitution_forward]

/-- The finite interface exposed by a closed `let` block commutes with a
bijective change of both variable sorts. -/
theorem Context.interfaceEquations_renameVariables
    (rho : VariableRenaming) (context : Context) (substitution : Subst) :
    (context.interfaceEquations substitution).map (renameEquation rho) =
      (renameContext rho context).interfaceEquations
        (renameSubstitution rho substitution) := by
  simp only [Context.interfaceEquations, List.map_append,
    Context.freeTyVars_renameContext, Context.freeCapVars_renameContext,
    List.map_map]
  congr 1
  · apply List.map_congr_left
    intro index _
    simp [renameEquation, Equation.apply,
      renameTy, VariableRenaming.substitution, Ty.apply]
  · apply List.map_congr_left
    intro index _
    simp [renameEquation, Equation.apply,
      renameCap, VariableRenaming.substitution, Cap.apply]

@[simp] theorem renameGenerated_fromLet
    (rho : VariableRenaming) (effects : List Equation) (body : Generated) :
    renameGenerated rho (Generated.fromLet effects body) =
      Generated.fromLet (effects.map (renameEquation rho))
        (renameGenerated rho body) := by
  simp [renameGenerated, Generated.fromLet]

mutual

/-- A finite allocation certificate for one relational elaboration. It
records only the names actually allocated by the derivation. At `let`, the
certificate restarts at the two concrete numeric `join` results, so no claim
that a permutation preserves `max` is hidden in the definition. -/
inductive Alignment (rho : VariableRenaming) :
    {context : Context} → {expression : Expr} → {source : Supply} →
      {generated : Generated} → {next : Supply} →
      Elaborates context expression source generated next →
      Supply → Supply → Prop where
  | var {context : Context} {index : Nat} {source : Supply} {scheme : Scheme}
      (lookup : context[index]? = some scheme)
      {target : Supply}
      (names : source.MapsPrefix rho target
        scheme.tyArity scheme.capArity) :
      Alignment rho (Elaborates.var (supply := source) lookup) target
        ((scheme.applyFree rho.substitution).instantiate target).2
  | lit {context : Context} {value : Int} {source : Supply} {target : Supply} :
      Alignment rho
        (Elaborates.lit (context := context) (value := value) (supply := source))
        target target
  | something {context : Context} {source : Supply} {target : Supply}
      (name : rho.tyForward ⟨source.ty⟩ = ⟨target.ty⟩) :
      Alignment rho
        (Elaborates.something (context := context) (supply := source))
        target (target.nextTy 1)
  | lam {context : Context} {body : Expr} {source : Supply}
      {generatedBody : Generated} {next : Supply}
      {bodyDerivation : Elaborates
        (.mono (.var ⟨source.ty⟩) :: context) body
        (source.nextTy 1) generatedBody next}
      {target targetNext : Supply}
      (domain : rho.tyForward ⟨source.ty⟩ = ⟨target.ty⟩)
      (bodyAlignment : Alignment rho bodyDerivation
        (target.nextTy 1) targetNext) :
      Alignment rho (Elaborates.lam bodyDerivation) target targetNext
  | app {context : Context} {function argument : Expr} {source : Supply}
      {generatedFunction : Generated} {afterFunction : Supply}
      {generatedArgument : Generated} {afterArgument : Supply}
      {functionDerivation : Elaborates context function source
        generatedFunction afterFunction}
      {argumentDerivation : Elaborates context argument afterFunction
        generatedArgument afterArgument}
      {target targetAfterFunction targetAfterArgument : Supply}
      (functionAlignment : Alignment rho functionDerivation target
        targetAfterFunction)
      (argumentAlignment : Alignment rho argumentDerivation
        targetAfterFunction targetAfterArgument)
      (domain : rho.tyForward ⟨afterArgument.ty⟩ =
        ⟨targetAfterArgument.ty⟩)
      (result : rho.tyForward ⟨afterArgument.ty + 1⟩ =
        ⟨targetAfterArgument.ty + 1⟩) :
      Alignment rho (Elaborates.app functionDerivation argumentDerivation)
        target (targetAfterArgument.nextTy 2)
  | tuple {context : Context} {items : List Expr} {source : Supply}
      {generatedItems : GeneratedItems} {next : Supply}
      {itemsDerivation : ElaboratesItems context items source
        generatedItems next}
      {target targetNext : Supply}
      (itemsAlignment : ItemsAlignment rho itemsDerivation target targetNext) :
      Alignment rho (Elaborates.tuple itemsDerivation) target targetNext
  | letE {context : Context} {value body : Expr} {source : Supply}
      {generatedValue : Generated} {afterValue : Supply}
      {generatedBody : Generated} {next : Supply}
      {valueDerivation : Elaborates context value source
        generatedValue afterValue}
      {closure : PrincipalBlockClosure generatedValue}
      {absorbing : closure.Absorbing}
      {bodyDerivation : Elaborates
        ((context.applyFree closure.substitution).generalize closure.target ::
          context.applyFree closure.substitution)
        body
        (afterValue.join
          (context.applyFree closure.substitution).initialSupply)
        generatedBody next}
      {target targetAfterValue targetNext : Supply}
      (valueAlignment : Alignment rho valueDerivation target targetAfterValue)
      (bodyAlignment : Alignment rho bodyDerivation
        (targetAfterValue.join
          ((renameContext rho context).applyFree
            (renameClosure rho closure).substitution).initialSupply)
        targetNext) :
      Alignment rho
        (Elaborates.letE valueDerivation closure absorbing bodyDerivation)
        target targetNext

/-- Finite allocation certificate for sibling elaboration. -/
inductive ItemsAlignment (rho : VariableRenaming) :
    {context : Context} → {expressions : List Expr} → {source : Supply} →
      {generated : GeneratedItems} → {next : Supply} →
      ElaboratesItems context expressions source generated next →
      Supply → Supply → Prop where
  | nil {context : Context} {source : Supply} {target : Supply} :
      ItemsAlignment rho
        (ElaboratesItems.nil (context := context) (supply := source))
        target target
  | cons {context : Context} {item : Expr} {items : List Expr}
      {source : Supply} {generatedItem : Generated} {afterItem : Supply}
      {generatedItems : GeneratedItems} {next : Supply}
      {itemDerivation : Elaborates context item source generatedItem afterItem}
      {itemsDerivation : ElaboratesItems context items afterItem
        generatedItems next}
      {target targetAfterItem targetNext : Supply}
      (itemAlignment : Alignment rho itemDerivation target targetAfterItem)
      (itemsAlignment : ItemsAlignment rho itemsDerivation
        targetAfterItem targetNext) :
      ItemsAlignment rho
        (ElaboratesItems.cons itemDerivation itemsDerivation)
        target targetNext

end

mutual

/-- Transport an elaboration using only its finite allocation certificate. -/
theorem Alignment.transport
    {rho : VariableRenaming}
    {context : Context} {expression : Expr} {source next : Supply}
    {generated : Generated}
    {derivation : Elaborates context expression source generated next}
    {target targetNext : Supply}
    (certificate : Alignment rho derivation target targetNext) :
    Elaborates (renameContext rho context) expression target
      (renameGenerated rho generated) targetNext := by
  cases certificate with
  | var lookup names =>
      rename_i index scheme
      have renamedLookup :
          (renameContext rho context)[index]? =
            some (scheme.applyFree rho.substitution) := by
        simpa [renameContext, Context.applyFree] using
          congrArg (Option.map (Scheme.applyFree rho.substitution)) lookup
      have instantiated := Scheme.instantiate_variableRenaming_prefix
        rho scheme names
      simpa [renameGenerated, renameTy, instantiated] using
        (Elaborates.var (supply := target) renamedLookup)
  | @lit context value source target =>
      simpa [renameGenerated, renameTy, Ty.apply] using
        (Elaborates.lit (context := renameContext rho context)
          (value := value) (supply := target))
  | @something context source target name =>
      simpa [renameGenerated, renameTy, VariableRenaming.substitution,
        Ty.apply, Cap.apply, name] using
        (Elaborates.something (context := renameContext rho context)
          (supply := target))
  | @lam context body source generatedBody next bodyDerivation target
      targetNext domain bodyAlignment =>
      have bodyTransport := Alignment.transport bodyAlignment
      have contextEquality :
          renameContext rho
              (.mono (.var ⟨source.ty⟩) :: context) =
            .mono (.var ⟨target.ty⟩) :: renameContext rho context := by
        simp [renameContext, Context.applyFree, Scheme.mono,
          Scheme.applyFree,
          VariableRenaming.substitution, Ty.apply, domain]
      rw [contextEquality] at bodyTransport
      simpa [renameGenerated, renameTy,
        VariableRenaming.substitution, Ty.apply, domain] using
        (Elaborates.lam bodyTransport)
  | @app context function argument source generatedFunction afterFunction
      generatedArgument afterArgument functionDerivation argumentDerivation
      target targetAfterFunction targetAfterArgument functionAlignment
      argumentAlignment domain result =>
      have functionTransport := Alignment.transport functionAlignment
      have argumentTransport := Alignment.transport argumentAlignment
      simpa [renameGenerated, renameTy, renameEquation,
        renameObligation, Equation.apply, CheckObligation.apply,
        VariableRenaming.substitution, Ty.apply, List.map_append,
        domain, result] using
        (Elaborates.app functionTransport argumentTransport)
  | @tuple context items source generatedItems next itemsDerivation target
      targetNext itemsAlignment =>
      have itemsTransport := ItemsAlignment.transport itemsAlignment
      simpa [renameGenerated, renameGeneratedItems, renameTy,
        Ty.apply, Ty.applyList] using
        (Elaborates.tuple itemsTransport)
  | @letE context value body source generatedValue afterValue generatedBody
      next valueDerivation closure absorbing bodyDerivation target
      targetAfterValue targetNext valueAlignment bodyAlignment
      =>
      have valueTransport := Alignment.transport valueAlignment
      have bodyTransport := Alignment.transport bodyAlignment
      let renamedClosure := renameClosure rho closure
      have renamedAbsorbing : renamedClosure.Absorbing :=
        renameClosure_absorbing rho closure absorbing
      have closedContextEquality :
          renameContext rho (context.applyFree closure.substitution) =
            (renameContext rho context).applyFree
              renamedClosure.substitution :=
        renameContext_applyClosure rho context closure
      have generalizedEquality :
          ((context.applyFree closure.substitution).generalize
              closure.target).applyFree rho.substitution =
            ((renameContext rho context).applyFree
                renamedClosure.substitution).generalize
              renamedClosure.target := by
        calc
          _ = (renameContext rho
                (context.applyFree closure.substitution)).generalize
              (renameTy rho closure.target) :=
            Context.generalize_variableRenaming_exact rho
              (context.applyFree closure.substitution) closure.target
          _ = ((renameContext rho context).applyFree
                  renamedClosure.substitution).generalize
                renamedClosure.target := by
            rw [closedContextEquality, renameClosure_target]
      have bodyContextEquality :
          renameContext rho
              ((context.applyFree closure.substitution).generalize
                  closure.target ::
                context.applyFree closure.substitution) =
            ((renameContext rho context).applyFree
                  renamedClosure.substitution).generalize
                renamedClosure.target ::
              (renameContext rho context).applyFree
                renamedClosure.substitution := by
        change
          ((context.applyFree closure.substitution).generalize
              closure.target).applyFree rho.substitution ::
            renameContext rho
              (context.applyFree closure.substitution) = _
        rw [generalizedEquality, closedContextEquality]
      rw [bodyContextEquality] at bodyTransport
      have interfaceEquality :=
        Context.interfaceEquations_renameVariables rho context
          closure.substitution
      simpa [renamedClosure, interfaceEquality] using
        (Elaborates.letE valueTransport renamedClosure renamedAbsorbing
          bodyTransport)

/-- Transport sibling elaboration using its finite allocation certificate. -/
theorem ItemsAlignment.transport
    {rho : VariableRenaming}
    {context : Context} {expressions : List Expr} {source next : Supply}
    {generated : GeneratedItems}
    {derivation : ElaboratesItems context expressions source generated next}
    {target targetNext : Supply}
    (certificate : ItemsAlignment rho derivation target targetNext) :
    ElaboratesItems (renameContext rho context) expressions target
      (renameGeneratedItems rho generated) targetNext := by
  cases certificate with
  | @nil context source target =>
      simpa [renameGeneratedItems, Ty.applyList] using
        (ElaboratesItems.nil (context := renameContext rho context)
          (supply := target))
  | @cons context item items source generatedItem afterItem generatedItems
      next itemDerivation itemsDerivation target targetAfterItem targetNext
      itemAlignment itemsAlignment =>
      have itemTransport := Alignment.transport itemAlignment
      have itemsTransport := ItemsAlignment.transport itemsAlignment
      simpa [renameGeneratedItems, renameGenerated, renameTy,
        Ty.apply, Ty.applyList,
        List.map_append] using
        (ElaboratesItems.cons itemTransport itemsTransport)

end

end ElaborationRenaming

end TypePM.Source
