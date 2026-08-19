import TypePM.Source.ClosureSupportRenaming
import TypePM.Source.ElaborationRenaming
import TypePM.FreshAliasSequence
import TypePM.HardWorklistEquivalence

/-!
# A directional counterexample for interface alias decomposition

Two absorbing principal closures can eliminate the same variable equality in
opposite directions.  After swapping the two representatives so that their
closed contexts and targets agree, the renamed first interface is a genuine
alias while the second interface is tautological.  Consequently, adding more
equations to the renamed first interface cannot make it semantically
equivalent to the second one.

This does not rule out a symmetric decomposition through a common refinement:
the alias can instead be added to the tautological side.
-/

namespace TypePM.Source.InterfaceAliasCounterexample

set_option linter.unusedSimpArgs false

private def alpha : TyVar := ⟨0⟩
private def beta : TyVar := ⟨1⟩

private def generated : TypePM.Generated :=
  { target := .var alpha
    hard := [.ty (.var alpha) (.var beta)]
    pending := [] }

private def leftSubstitution : Subst :=
  Subst.singleTy alpha (.var beta)

private def rightSubstitution : Subst :=
  Subst.singleTy beta (.var alpha)

private theorem alpha_ne_beta : alpha ≠ beta := by decide
private theorem beta_ne_alpha : beta ≠ alpha := by decide

private def leftReduction :
    Reduces generated.hard leftSubstitution [] := by
  apply Reduces.tyVarLeft
  simp [alpha, beta, Ty.occursTy]

private def rightReduction :
    Reduces generated.hard rightSubstitution [] := by
  apply Reduces.tyVarRight
  simp [alpha, beta, Ty.occursTy]

private theorem leftAbsorbingPrincipal :
    AbsorbingPrincipal generated.hard leftSubstitution := by
  constructor
  · constructor
    · simp [generated, leftSubstitution, Equation.Holds,
        Subst.singleTy, Ty.apply, alpha, beta]
    · intro solution solved
      exact leftReduction.factors_first solved
  · intro solution solved
    exact leftReduction.absorbed solved

private theorem rightAbsorbingPrincipal :
    AbsorbingPrincipal generated.hard rightSubstitution := by
  constructor
  · constructor
    · simp [generated, rightSubstitution, Equation.Holds,
        Subst.singleTy, Ty.apply, alpha, beta]
    · intro solution solved
      exact rightReduction.factors_first solved
  · intro solution solved
    exact rightReduction.absorbed solved

private theorem idAbsorbingPrincipal :
    AbsorbingPrincipal [] Subst.id := by
  constructor
  · constructor
    · exact solves_nil _
    · intro solution _
      exact ⟨solution, by simp⟩
  · intro solution _
    simp

private def leftClosure : PrincipalBlockClosure generated :=
  { finalHard := generated.hard
    finalPending := []
    hardSubstitution := leftSubstitution
    residualSubstitution := Subst.id
    saturation :=
      { closure := .refl
        principal := leftAbsorbingPrincipal.mostGeneral
        stable := by simp [promoteUnder] }
    residualPrincipal := by
      simpa [residualEquations] using idAbsorbingPrincipal.mostGeneral }

private def rightClosure : PrincipalBlockClosure generated :=
  { finalHard := generated.hard
    finalPending := []
    hardSubstitution := rightSubstitution
    residualSubstitution := Subst.id
    saturation :=
      { closure := .refl
        principal := rightAbsorbingPrincipal.mostGeneral
        stable := by simp [promoteUnder] }
    residualPrincipal := by
      simpa [residualEquations] using idAbsorbingPrincipal.mostGeneral }

@[simp] private theorem leftClosure_substitution :
    leftClosure.substitution = leftSubstitution := by
  simp [PrincipalBlockClosure.substitution, leftClosure]

@[simp] private theorem rightClosure_substitution :
    rightClosure.substitution = rightSubstitution := by
  simp [PrincipalBlockClosure.substitution, rightClosure]

theorem leftClosure_absorbing : leftClosure.Absorbing := by
  exact ⟨leftAbsorbingPrincipal, by
    simpa [leftClosure, residualEquations] using idAbsorbingPrincipal⟩

theorem rightClosure_absorbing : rightClosure.Absorbing := by
  exact ⟨rightAbsorbingPrincipal, by
    simpa [rightClosure, residualEquations] using idAbsorbingPrincipal⟩

private def swap : VariableRenaming :=
  let permutation := FinitePermutation.swap alpha beta
  { tyForward := permutation.forward
    tyBackward := permutation.backward
    capForward := id
    capBackward := id
    ty_backward_forward := permutation.backward_forward
    ty_forward_backward := permutation.forward_backward
    cap_backward_forward := fun _ => rfl
    cap_forward_backward := fun _ => rfl }

private def context : Context := [.mono (.var alpha)]

theorem swap_finiteSupport :
    FinitePermutation.Permutation.FiniteSupport
      { forward := swap.tyForward
        backward := swap.tyBackward
        backward_forward := swap.ty_backward_forward
        forward_backward := swap.ty_forward_backward } := by
  exact FinitePermutation.finiteSupport_swap alpha beta

theorem closedContext_exact :
    (context.applyFree leftClosure.substitution).applyFree
        swap.substitution =
      context.applyFree rightClosure.substitution := by
  rw [leftClosure_substitution, rightClosure_substitution]
  simp [context, leftSubstitution,
    rightSubstitution, swap, alpha, beta, VariableRenaming.substitution,
    FinitePermutation.swap, FinitePermutation.swapIndex,
    Context.applyFree, Scheme.mono, Scheme.applyFree, PolyTy.applyFree,
    PolyTy.ofTy, Subst.singleTy, Subst.compose, Subst.id, Ty.apply]

theorem target_exact :
    leftClosure.target.apply swap.substitution = rightClosure.target := by
  rw [PrincipalBlockClosure.target, PrincipalBlockClosure.target,
    leftClosure_substitution, rightClosure_substitution]
  simp [PrincipalBlockClosure.target, generated,
    leftSubstitution, rightSubstitution, swap, alpha, beta,
    VariableRenaming.substitution, FinitePermutation.swap,
    FinitePermutation.swapIndex, Subst.singleTy, Subst.compose,
    Subst.id, Ty.apply]

private def renamedLeftInterface : List Equation :=
  (context.interfaceEquations leftClosure.substitution).map
    (ElaborationRenaming.renameEquation swap)

private def rightInterface : List Equation :=
  context.interfaceEquations rightClosure.substitution

theorem renamedLeftInterface_eq :
    renamedLeftInterface = [.ty (.var beta) (.var alpha)] := by
  unfold renamedLeftInterface
  rw [leftClosure_substitution]
  simp [context, leftSubstitution,
    swap, alpha, beta, ElaborationRenaming.renameEquation,
    VariableRenaming.substitution, FinitePermutation.swap,
    FinitePermutation.swapIndex, Context.interfaceEquations,
    Context.freeTyVars, Context.freeCapVars, Scheme.freeTyVars,
    Scheme.freeCapVars, Scheme.mono, PolyTy.ofTy, PolyTy.freeTyVars,
    PolyTy.freeCapVars, dedupFirst, dedup, List.idxOf, List.findIdx,
    List.findIdx.go, Subst.singleTy, Subst.compose, Subst.id,
    Equation.apply, Ty.apply]

theorem rightInterface_eq :
    rightInterface = [.ty (.var alpha) (.var alpha)] := by
  unfold rightInterface
  rw [rightClosure_substitution]
  simp [context, rightSubstitution,
    alpha, beta, Context.interfaceEquations, Context.freeTyVars,
    Context.freeCapVars, Scheme.freeTyVars, Scheme.freeCapVars,
    Scheme.mono, PolyTy.ofTy, PolyTy.freeTyVars, PolyTy.freeCapVars,
    dedupFirst, dedup, List.idxOf, List.findIdx, List.findIdx.go,
    Subst.singleTy, Subst.compose, Subst.id]

/-- No list of extra hard equations can repair the decomposition when the
extra aliases are required to be added to the renamed-left side. -/
theorem no_left_addition_decomposition (extra : List Equation) :
    ¬ HardEquivalent (extra ++ renamedLeftInterface) rightInterface := by
  intro equivalent
  have rightSolved : Solves Subst.id rightInterface := by
    rw [rightInterface_eq]
    simp [Equation.Holds]
  have leftSolved := (equivalent Subst.id).mpr rightSolved
  have aliasSolved :
      (Equation.ty (.var beta) (.var alpha)).Holds Subst.id := by
    have all := (solves_append Subst.id extra renamedLeftInterface).mp leftSolved
    rw [renamedLeftInterface_eq] at all
    exact (solves_cons Subst.id _ []).mp all.2 |>.1
  simp [Equation.Holds, Subst.id, Ty.apply, alpha, beta] at aliasSolved

/-- The correct direction in this example is to add the missing alias to the
tautological side. -/
theorem common_refinement_direction :
    HardEquivalent renamedLeftInterface
      (.ty (.var beta) (.var alpha) :: rightInterface) := by
  rw [renamedLeftInterface_eq, rightInterface_eq]
  intro substitution
  simp [Equation.Holds]

private def emptyBody : TypePM.Generated :=
  { target := .int, hard := [], pending := [] }

private def renamedLeftBlock : TypePM.Generated :=
  Generated.fromLet renamedLeftInterface emptyBody

private def rightBlock : TypePM.Generated :=
  Generated.fromLet rightInterface emptyBody

/-- The symmetric API repairs the failed one-sided statement: both concrete
interfaces are presentations of the empty body, with the nontrivial alias
appearing only on the renamed-left side. -/
theorem commonCoreEquivalent_positive :
    FreshAliasSequence.CommonCoreEquivalent renamedLeftBlock rightBlock := by
  have invariant : FreshAliasSaturation.TyInvariant
      beta alpha emptyBody.hard emptyBody.pending := by
    simp [FreshAliasSaturation.TyInvariant,
      FreshAliasSaturation.PendingFixed, emptyBody]
  have certificate := FreshAliasSequence.CommonCoreEquivalent.tyAlias_refl
    emptyBody beta alpha beta_ne_alpha invariant
  simpa [renamedLeftBlock, rightBlock, Generated.fromLet,
    renamedLeftInterface_eq, rightInterface_eq,
    FreshAliasElimination.addTyAlias] using certificate

end TypePM.Source.InterfaceAliasCounterexample
