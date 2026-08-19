import TypePM.Source.RecursiveLetInvariant
import TypePM.Source.GeneratedAcceptanceTransport

/-!
# Whole-let normalization across different generated value blocks

`CrossGeneratedClosureAlignment` compares the interfaces exposed by
principal closures of two possibly different generated value blocks.  Its
equation component starts after the left interface has been renamed.  This
module lifts that component to the complete `Generated.fromLet` blocks,
including the result type and every delayed checking obligation.

The theorem is deliberately phrased at the post-renaming boundary.  Moving
an isolated child block through a fixed surrounding frame is not a general
property of variable renaming: the frame can share variables with the child.
Consequently the later recursive proof must justify that preceding step from
source support, rather than silently treating it as definitional equality.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition

namespace CrossGeneratedClosureAlignment

/-- After renaming the complete left `let` block, the two closure interfaces
have a common hard-equation core.  Both blocks contain the same renamed body,
so their result types and delayed obligations agree exactly. -/
noncomputable def renamedFromLetCommonCore
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context)
    (body : Generated) :
    GeneratedEquationCommonCore
      (ElaborationRenaming.renameGenerated alignment.rho
        (Generated.fromLet
          (context.interfaceEquations left.substitution) body))
      (Generated.fromLet
        (context.interfaceEquations right.substitution)
        (ElaborationRenaming.renameGenerated alignment.rho body)) := by
  rw [ElaborationRenaming.renameGenerated_fromLet]
  exact
    { equations := by
        simpa [Generated.fromLet] using
          alignment.equations.appendSame
            (ElaborationRenaming.renameGenerated alignment.rho body).hard
      target_eq := rfl
      pending_eq := rfl }

/-- Frame-wise admissibility of the finite interface aliases upgrades the
whole-let common core to scoped contextual acceptance equivalence.  Unlike a
hard-worklist-only statement, this result remains valid when the body has
delayed checking obligations. -/
theorem renamedFromLet_scopedContextualEquivalent
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context)
    (body : Generated)
    {hidden : List UnificationVar}
    (admissible :
      (alignment.renamedFromLetCommonCore body).FrameAdmissible hidden) :
    Generated.ScopedContextualEquivalent hidden
      (ElaborationRenaming.renameGenerated alignment.rho
        (Generated.fromLet
          (context.interfaceEquations left.substitution) body))
      (Generated.fromLet
        (context.interfaceEquations right.substitution)
        (ElaborationRenaming.renameGenerated alignment.rho body)) :=
  GeneratedEquationCommonCore.scopedContextualEquivalent_of_frameAdmissible
    (alignment.renamedFromLetCommonCore body) admissible

/-- Root-block acceptance is the empty-frame consequence of whole-let
normalization. -/
theorem renamedFromLet_blockAccepts_iff
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context)
    (body : Generated)
    {hidden : List UnificationVar}
    (admissible :
      (alignment.renamedFromLetCommonCore body).FrameAdmissible hidden) :
    BlockAccepts
        (ElaborationRenaming.renameGenerated alignment.rho
          (Generated.fromLet
            (context.interfaceEquations left.substitution) body)) ↔
      BlockAccepts
        (Generated.fromLet
          (context.interfaceEquations right.substitution)
          (ElaborationRenaming.renameGenerated alignment.rho body)) :=
  (alignment.renamedFromLet_scopedContextualEquivalent
    body admissible).blockAccepts_iff

/-- At the empty frame, the initial whole-block renaming is always safe.
Combining global renaming invariance with the interface normalization gives
acceptance equivalence directly from the original left `let` block to the
right block with the transported body. -/
theorem fromLet_blockAccepts_iff
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context)
    (body : Generated)
    {hidden : List UnificationVar}
    (admissible :
      (alignment.renamedFromLetCommonCore body).FrameAdmissible hidden) :
    BlockAccepts
        (Generated.fromLet
          (context.interfaceEquations left.substitution) body) ↔
      BlockAccepts
        (Generated.fromLet
          (context.interfaceEquations right.substitution)
          (ElaborationRenaming.renameGenerated alignment.rho body)) := by
  let leftBlock := Generated.fromLet
    (context.interfaceEquations left.substitution) body
  have renameStep :
      BlockAccepts leftBlock ↔
        BlockAccepts
          (ElaborationRenaming.renameGenerated alignment.rho leftBlock) :=
    ElaborationRenaming.blockAccepts_renameVariables_iff
      alignment.rho leftBlock
  exact renameStep.trans (alignment.renamedFromLet_blockAccepts_iff
    body admissible)

/-- For nested use, the only additional premise is precisely that renaming
the isolated left child is safe in every admissible fixed frame.  This
statement exposes, rather than hides, the remaining source-support lemma. -/
theorem fromLet_scopedContextualEquivalent_of_isolatedRenaming
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context)
    (body : Generated)
    {hidden : List UnificationVar}
    (isolatedRenaming : Generated.ScopedContextualEquivalent hidden
      (Generated.fromLet
        (context.interfaceEquations left.substitution) body)
      (ElaborationRenaming.renameGenerated alignment.rho
        (Generated.fromLet
          (context.interfaceEquations left.substitution) body)))
    (admissible :
      (alignment.renamedFromLetCommonCore body).FrameAdmissible hidden) :
    Generated.ScopedContextualEquivalent hidden
      (Generated.fromLet
        (context.interfaceEquations left.substitution) body)
      (Generated.fromLet
        (context.interfaceEquations right.substitution)
        (ElaborationRenaming.renameGenerated alignment.rho body)) :=
  isolatedRenaming.trans
    (alignment.renamedFromLet_scopedContextualEquivalent body admissible)

/-- The normalized right block has exactly the renamed result type of the
original left block.  This is the target-level half needed by principality. -/
theorem renamedFromLet_target_exact
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context)
    (body : Generated) :
    (Generated.fromLet
      (context.interfaceEquations right.substitution)
      (ElaborationRenaming.renameGenerated alignment.rho body)).target =
        ElaborationRenaming.renameTy alignment.rho
          (Generated.fromLet
            (context.interfaceEquations left.substitution) body).target := by
  rfl

/-- The original left and normalized right result types are mutual
substitution instances.  This is the representative-independent target
consequence needed by source principality. -/
theorem fromLet_targets_mutualInstances
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context)
    (body : Generated) :
    IsInstance
        (Generated.fromLet
          (context.interfaceEquations left.substitution) body).target
        (Generated.fromLet
          (context.interfaceEquations right.substitution)
          (ElaborationRenaming.renameGenerated alignment.rho body)).target ∧
      IsInstance
        (Generated.fromLet
          (context.interfaceEquations right.substitution)
          (ElaborationRenaming.renameGenerated alignment.rho body)).target
        (Generated.fromLet
          (context.interfaceEquations left.substitution) body).target := by
  simpa [Generated.fromLet, ElaborationRenaming.renameGenerated,
    ElaborationRenaming.renameTy] using
      ClosureInterfaceDecomposition.renameTy_mutualInstances
        alignment.rho body.target

/-- Delayed checking obligations of the normalized right block are exactly
the renamed obligations of the original left block. -/
theorem renamedFromLet_pending_exact
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context)
    (body : Generated) :
    (Generated.fromLet
      (context.interfaceEquations right.substitution)
      (ElaborationRenaming.renameGenerated alignment.rho body)).pending =
        (Generated.fromLet
          (context.interfaceEquations left.substitution) body).pending.map
            (ElaborationRenaming.renameObligation alignment.rho) := by
  rfl

end CrossGeneratedClosureAlignment

/-! ## Why the nested renaming premise cannot be omitted -/

namespace IsolatedRenamingCounterexample

private def alpha : TyVar := ⟨0⟩
private def beta : TyVar := ⟨1⟩

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

private def child : Generated :=
  { target := .int
    hard := [.ty (.var alpha) .int]
    pending := [] }

private def frame : GeneratedFrame :=
  .letBody [.ty (.var alpha) (.fn .int .int)] .hole

private theorem left_rejected : ¬ BlockAccepts (frame.plug child) := by
  intro accepts
  obtain ⟨solution, solved⟩ :=
    ElaborationRenaming.BlockAccepts.hard_solvable accepts
  have functionConstraint :
      (Ty.var alpha).apply solution = Ty.fn .int .int := by
    have holds := solved
      (.ty (.var alpha) (.fn .int .int)) (by
        simp [frame, child, GeneratedFrame.plug, Generated.fromLet])
    simpa [Equation.Holds, Ty.apply] using holds
  have integerConstraint : (Ty.var alpha).apply solution = Ty.int := by
    have holds := solved (.ty (.var alpha) .int) (by
      simp [frame, child, GeneratedFrame.plug, Generated.fromLet])
    simpa [Equation.Holds, Ty.apply] using holds
  rw [integerConstraint] at functionConstraint
  exact Ty.noConfusion functionConstraint

private theorem right_accepted :
    BlockAccepts
      (frame.plug (ElaborationRenaming.renameGenerated swap child)) := by
  let solution := Subst.compose
    (Subst.singleTy beta .int)
    (Subst.singleTy alpha (.fn .int .int))
  apply ElaborationRenaming.BlockAccepts.of_solvable_noPending
      (solution := solution) (by
    simp [frame, child, GeneratedFrame.plug, Generated.fromLet,
      ElaborationRenaming.renameGenerated])
  intro equation member
  have alternatives :
      equation = .ty (.var alpha) (.fn .int .int) ∨
        equation = .ty (.var beta) .int := by
    simpa [frame, child, GeneratedFrame.plug, Generated.fromLet,
      ElaborationRenaming.renameGenerated, ElaborationRenaming.renameEquation,
      ElaborationRenaming.renameTy, swap, alpha, beta,
      VariableRenaming.substitution, FinitePermutation.swap,
      FinitePermutation.swapIndex, Equation.apply, Ty.apply] using member
  rcases alternatives with rfl | rfl <;>
    simp [solution, alpha, beta, Equation.Holds, Ty.apply,
      Subst.compose, Subst.singleTy]

/-- A global renaming of a child block is not by itself a contextual
equivalence when a fixed frame shares a moved variable with that child. -/
theorem not_scopedContextualEquivalent :
    ¬ Generated.ScopedContextualEquivalent [] child
      (ElaborationRenaming.renameGenerated swap child) := by
  intro related
  have frameAvoids : frame.Avoids [] := by
    constructor
    · intro candidate _ hidden
      simp at hidden
    · trivial
  have atFrame := related frame frameAvoids
  exact left_rejected (atFrame.mpr right_accepted)

end IsolatedRenamingCounterexample

end TypePM.Source
