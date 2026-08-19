import TypePM.Source.ElaborationRenaming

/-!
# Composition of source-elaboration renamings

This module combines a support renaming with a later finite fresh-interval
renaming.  Composition is ordered: `comp later earlier` first applies
`earlier`, then `later`.
-/

namespace TypePM.Source

namespace VariableRenaming

/-- The identity change of names in both variable sorts. -/
def id : VariableRenaming :=
  { tyForward := fun index => index
    tyBackward := fun index => index
    capForward := fun index => index
    capBackward := fun index => index
    ty_backward_forward := fun _ => rfl
    ty_forward_backward := fun _ => rfl
    cap_backward_forward := fun _ => rfl
    cap_forward_backward := fun _ => rfl }

/-- Composition, with the earlier change of names on the right. -/
def comp (later earlier : VariableRenaming) : VariableRenaming :=
  { tyForward := later.tyForward ∘ earlier.tyForward
    tyBackward := earlier.tyBackward ∘ later.tyBackward
    capForward := later.capForward ∘ earlier.capForward
    capBackward := earlier.capBackward ∘ later.capBackward
    ty_backward_forward := fun index => by
      simp
    ty_forward_backward := fun index => by
      simp
    cap_backward_forward := fun index => by
      simp
    cap_forward_backward := fun index => by
      simp }

@[simp] theorem id_tyForward (index : TyVar) :
    id.tyForward index = index := rfl

@[simp] theorem id_capForward (index : CapVar) :
    id.capForward index = index := rfl

@[simp] theorem comp_tyForward
    (later earlier : VariableRenaming) (index : TyVar) :
    (comp later earlier).tyForward index =
      later.tyForward (earlier.tyForward index) := rfl

@[simp] theorem comp_capForward
    (later earlier : VariableRenaming) (index : CapVar) :
    (comp later earlier).capForward index =
      later.capForward (earlier.capForward index) := rfl

@[simp] theorem comp_tyBackward
    (later earlier : VariableRenaming) (index : TyVar) :
    (comp later earlier).tyBackward index =
      earlier.tyBackward (later.tyBackward index) := rfl

@[simp] theorem comp_capBackward
    (later earlier : VariableRenaming) (index : CapVar) :
    (comp later earlier).capBackward index =
      earlier.capBackward (later.capBackward index) := rfl

@[simp] theorem substitution_id : id.substitution = Subst.id := by
  apply Subst.eq_of_components <;> intro index <;>
    simp [id, substitution, Subst.id]

@[simp] theorem substitution_comp
    (later earlier : VariableRenaming) :
    (comp later earlier).substitution =
      Subst.compose later.substitution earlier.substitution := by
  apply Subst.eq_of_components
  · intro index
    simp [comp, substitution, Subst.compose, Cap.apply]
  · intro index
    simp [comp, substitution, Subst.compose, Ty.apply]

end VariableRenaming


namespace Supply

/-- Finite allocated prefixes compose without imposing any condition on the
unused tails. -/
theorem MapsPrefix.comp
    {earlier later : VariableRenaming}
    {source middle target : Supply} {tyCount capCount : Nat}
    (first : source.MapsPrefix earlier middle tyCount capCount)
    (second : middle.MapsPrefix later target tyCount capCount) :
    source.MapsPrefix (VariableRenaming.comp later earlier) target
      tyCount capCount := by
  constructor
  · intro offset inside
    rw [VariableRenaming.comp_tyForward, first.1 offset inside]
    exact second.1 offset inside
  · intro offset inside
    rw [VariableRenaming.comp_capForward, first.2 offset inside]
    exact second.2 offset inside

theorem MapsPrefix.id
    (source : Supply) (tyCount capCount : Nat) :
    source.MapsPrefix VariableRenaming.id source tyCount capCount := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end Supply


namespace ElaborationRenaming

@[simp] theorem renameTy_id (target : Ty) :
    renameTy VariableRenaming.id target = target := by
  simp [renameTy]

@[simp] theorem renameCap_id (capability : Cap) :
    renameCap VariableRenaming.id capability = capability := by
  simp [renameCap]

@[simp] theorem renameTy_comp
    (later earlier : VariableRenaming) (target : Ty) :
    renameTy (VariableRenaming.comp later earlier) target =
      renameTy later (renameTy earlier target) := by
  simp [renameTy, Ty.apply_compose]

@[simp] theorem renameCap_comp
    (later earlier : VariableRenaming) (capability : Cap) :
    renameCap (VariableRenaming.comp later earlier) capability =
      renameCap later (renameCap earlier capability) := by
  simp [renameCap, Cap.apply_compose]

@[simp] theorem renameEquation_comp
    (later earlier : VariableRenaming) (equation : Equation) :
    renameEquation (VariableRenaming.comp later earlier) equation =
      renameEquation later (renameEquation earlier equation) := by
  cases equation <;>
    simp [renameEquation, Equation.apply]

@[simp] theorem renameObligation_comp
    (later earlier : VariableRenaming) (obligation : CheckObligation) :
    renameObligation (VariableRenaming.comp later earlier) obligation =
      renameObligation later (renameObligation earlier obligation) := by
  cases obligation
  simp [renameObligation, CheckObligation.apply]

@[simp] theorem renameGenerated_comp
    (later earlier : VariableRenaming) (generated : Generated) :
    renameGenerated (VariableRenaming.comp later earlier) generated =
      renameGenerated later (renameGenerated earlier generated) := by
  cases generated
  simp [renameGenerated, List.map_map, Function.comp_def]

@[simp] theorem renameGeneratedItems_comp
    (later earlier : VariableRenaming) (generated : GeneratedItems) :
    renameGeneratedItems (VariableRenaming.comp later earlier) generated =
      renameGeneratedItems later (renameGeneratedItems earlier generated) := by
  cases generated
  simp [renameGeneratedItems, List.map_map,
    Function.comp_def]

@[simp] theorem renameContext_comp
    (later earlier : VariableRenaming) (context : Context) :
    renameContext (VariableRenaming.comp later earlier) context =
      renameContext later (renameContext earlier context) := by
  simp [renameContext, Context.applyFree_compose]

@[simp] theorem renameSubstitution_compRenaming
    (later earlier : VariableRenaming) (substitution : Subst) :
    renameSubstitution (VariableRenaming.comp later earlier) substitution =
      renameSubstitution later
        (renameSubstitution earlier substitution) := by
  apply Subst.eq_of_components
  · intro index
    change
      (substitution.cap
          (earlier.capBackward (later.capBackward index))).apply
          (VariableRenaming.comp later earlier).substitution.cap =
        ((substitution.cap
            (earlier.capBackward (later.capBackward index))).apply
            earlier.substitution.cap).apply later.substitution.cap
    rw [VariableRenaming.substitution_comp]
    exact (Cap.apply_compose later.substitution earlier.substitution
      (substitution.cap
        (earlier.capBackward (later.capBackward index)))).symm
  · intro index
    change
      (substitution.ty
          (earlier.tyBackward (later.tyBackward index))).apply
          (VariableRenaming.comp later earlier).substitution =
        ((substitution.ty
            (earlier.tyBackward (later.tyBackward index))).apply
            earlier.substitution).apply later.substitution
    rw [VariableRenaming.substitution_comp]
    exact (Ty.apply_compose later.substitution earlier.substitution
      (substitution.ty
        (earlier.tyBackward (later.tyBackward index)))).symm

/-- The simultaneous solution selected by closure renaming composes exactly.
This projection-level law avoids hiding a dependent cast between the two
propositionally equal generated-block indices. -/
@[simp] theorem renameClosure_comp_substitution
    {generated : Generated} (later earlier : VariableRenaming)
    (closure : PrincipalBlockClosure generated) :
    (renameClosure (VariableRenaming.comp later earlier) closure).substitution =
      (renameClosure later (renameClosure earlier closure)).substitution := by
  simp [renameSubstitution_compRenaming]

/-- Principal closure targets obey the same composition law. -/
@[simp] theorem renameClosure_comp_target
    {generated : Generated} (later earlier : VariableRenaming)
    (closure : PrincipalBlockClosure generated) :
    (renameClosure (VariableRenaming.comp later earlier) closure).target =
      (renameClosure later (renameClosure earlier closure)).target := by
  simp

end ElaborationRenaming

end TypePM.Source
