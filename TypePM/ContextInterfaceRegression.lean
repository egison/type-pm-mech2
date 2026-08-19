import TypePM.AbsorbingUnification
import TypePM.ContextInterface

/-!
# Context-interface normalization regressions

These small kernel-checked examples isolate why a closed source block uses an
absorbing principal substitution, rather than an arbitrary representative of
a most general solution.  An unconstrained swap is a most general solution of
the empty worklist, but exporting that swap through a context interface would
introduce equalities which the source block never required.
-/

namespace TypePM.Source.ContextInterfaceRegression

private def ty0 : TyVar := ⟨0⟩
private def ty1 : TyVar := ⟨1⟩
private def ty2 : TyVar := ⟨2⟩
private def cap0 : CapVar := ⟨0⟩
private def cap1 : CapVar := ⟨1⟩
private def cap2 : CapVar := ⟨2⟩

/-- Simultaneously swap names zero and one in each variable sort. -/
private def swapBoth : Subst :=
  { ty := fun index =>
      if index = ty0 then .var ty1
      else if index = ty1 then .var ty0
      else .var index
    cap := fun index =>
      if index = cap0 then .var cap1
      else if index = cap1 then .var cap0
      else .var index }

private theorem swapBoth_involutive :
    Subst.compose swapBoth swapBoth = Subst.id := by
  apply Subst.eq_of_components
  · intro index
    by_cases zero : index = cap0
    · subst index
      simp [swapBoth, cap0, cap1, Subst.compose, Subst.id, Cap.apply]
    · by_cases one : index = cap1
      · subst index
        simp [swapBoth, cap0, cap1, Subst.compose, Subst.id, Cap.apply]
      · simp [swapBoth, zero, one, Subst.compose, Subst.id, Cap.apply]
  · intro index
    by_cases zero : index = ty0
    · subst index
      simp [swapBoth, ty0, ty1, Subst.compose, Subst.id, Ty.apply]
    · by_cases one : index = ty1
      · subst index
        simp [swapBoth, ty0, ty1, Subst.compose, Subst.id, Ty.apply]
      · simp [swapBoth, zero, one, Subst.compose, Subst.id, Ty.apply]

/-- The factorization-only definition permits an arbitrary involutive rename
as a representative of the empty worklist. -/
theorem swapBoth_plainMostGeneral : MostGeneral [] swapBoth := by
  constructor
  · exact solves_nil _
  · intro specific _
    refine ⟨Subst.compose specific swapBoth, ?_⟩
    calc
      specific = Subst.compose specific Subst.id :=
        (Subst.compose_id_right specific).symm
      _ = Subst.compose specific (Subst.compose swapBoth swapBoth) := by
        rw [swapBoth_involutive]
      _ = Subst.compose (Subst.compose specific swapBoth) swapBoth :=
        Subst.compose_assoc specific swapBoth swapBoth

/-- The same representative is rejected by absorbing normalization. -/
theorem swapBoth_notAbsorbing :
    ¬ AbsorbingPrincipal [] swapBoth := by
  intro absorbing
  have identity := AbsorbingPrincipal.eq_id_of_empty absorbing
  have component := congrArg (fun substitution => substitution.ty ty0) identity
  simp [swapBoth, ty0, ty1, Subst.id] at component

/-- This is the boundary used by an empty closed block: absorption makes its
principal substitution literally the identity. -/
theorem empty_closure_is_identity {principal : Subst}
    (normalized : AbsorbingPrincipal [] principal) :
    principal = Subst.id :=
  AbsorbingPrincipal.eq_id_of_empty normalized

/-- With the identity block substitution, every later substitution solves
the finite context interface. -/
theorem every_later_solves_identity_interface
    (context : Context) (later : Subst) :
    Solves later (context.interfaceEquations Subst.id) := by
  rw [Context.solves_interfaceEquations_iff]
  unfold Context.SubstitutionsAgree
  simp

/-- An absent ordinary variable is never selected as the left-hand domain of
an interface equation.  A block image may still mention a new name on the
right, so this is the strongest unconditional statement. -/
theorem absent_ty_not_interface_domain
    (context : Context) (block : Subst) (index : TyVar)
    (absent : index ∉ context.freeTyVars) (right : Ty) :
    Equation.ty (.var index) right ∉ context.interfaceEquations block := by
  simp only [Context.interfaceEquations, List.mem_append, List.mem_map]
  intro membership
  rcases membership with membership | membership
  · obtain ⟨candidate, candidateMember, equality⟩ := membership
    injection equality with leftEquality
    have indexEquality : candidate = index := Ty.var.inj leftEquality
    exact absent (indexEquality ▸ candidateMember)
  · obtain ⟨_, _, equality⟩ := membership
    cases equality

/-- The analogous domain property for capability variables. -/
theorem absent_cap_not_interface_domain
    (context : Context) (block : Subst) (index : CapVar)
    (absent : index ∉ context.freeCapVars) (right : Cap) :
    Equation.cap (.var index) right ∉ context.interfaceEquations block := by
  simp only [Context.interfaceEquations, List.mem_append, List.mem_map]
  intro membership
  rcases membership with membership | membership
  · obtain ⟨_, _, equality⟩ := membership
    cases equality
  · obtain ⟨candidate, candidateMember, equality⟩ := membership
    injection equality with leftEquality
    have indexEquality : candidate = index := Cap.var.inj leftEquality
    exact absent (indexEquality ▸ candidateMember)

/-- A monomorphic context mentioning both swapped names in both sorts.  The
public smart constructor keeps the scheme's scoping proof bundled.
-/
private def bothSortContext : Context :=
  [.mono (.prod [
    .var ty0,
    .var ty1,
    .matcher (.prod [.var cap0, .var cap1]) .int])]

/-- Exporting the unconstrained swap turns it into four context equalities,
two for ordinary types and two for capabilities. -/
theorem swapBoth_interface_equations :
    bothSortContext.interfaceEquations swapBoth = [
      .ty (.var ty0) (.var ty1),
      .ty (.var ty1) (.var ty0),
      .cap (.var cap0) (.var cap1),
      .cap (.var cap1) (.var cap0)] := by
  rfl

/-- In this concrete closed-block boundary, names absent from the context are
absent from the complete interface worklist in both sorts.  The preceding
domain theorems state the unconditional general fact; this stronger occurrence
statement additionally relies on the concrete block not introducing the
unrelated names in its images. -/
theorem unrelated_names_absent_from_interface :
    ty2 ∉ bothSortContext.freeTyVars ∧
      cap2 ∉ bothSortContext.freeCapVars ∧
      .ty ty2 ∉ unificationVars
        (bothSortContext.interfaceEquations swapBoth) ∧
      .cap cap2 ∉ unificationVars
        (bothSortContext.interfaceEquations swapBoth) := by
  decide

/-- The ordinary-type equality introduced by the swap is not satisfied by
the identity substitution. -/
theorem swapBoth_ty_equality_is_spurious :
    ¬ Equation.Holds Subst.id (.ty (.var ty0) (.var ty1)) := by
  simp [Equation.Holds, Ty.apply, Subst.id, ty0, ty1]

/-- The capability equality introduced by the swap is independently not
satisfied by the identity substitution. -/
theorem swapBoth_cap_equality_is_spurious :
    ¬ Equation.Holds Subst.id (.cap (.var cap0) (.var cap1)) := by
  simp [Equation.Holds, Cap.apply, Subst.id, cap0, cap1]

/-- Hence plain most-generality alone can make an empty block reject a later
identity solution through its interface, although the normalized identity
representative accepts it. -/
theorem plainMostGeneral_can_create_spurious_interface_failure :
    MostGeneral [] swapBoth ∧
      ¬ Solves Subst.id (bothSortContext.interfaceEquations swapBoth) ∧
      Solves Subst.id (bothSortContext.interfaceEquations Subst.id) := by
  refine ⟨swapBoth_plainMostGeneral, ?_,
    every_later_solves_identity_interface bothSortContext Subst.id⟩
  rw [swapBoth_interface_equations]
  intro solved
  exact swapBoth_ty_equality_is_spurious
    (solved _ (by simp))

end TypePM.Source.ContextInterfaceRegression
