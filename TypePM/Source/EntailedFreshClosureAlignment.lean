import TypePM.Source.ClosureSupportFutureFixing
import TypePM.Source.EntailedClosureAlignment

/-!
# Future-fixing closure alignment for entailed generated blocks

The semantic transport from the left block produces an absorbing middle
closure on the right generated block.  The bounded-support same-generated
construction then aligns that middle closure with the requested right
representative while fixing the future fresh stream.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition.AliasFreshness

/-- Adding a scoped alias sequence preserves a strict generated-support
bound when every fresh endpoint is itself below the boundary. -/
theorem FreshAliasSequence.addAll_support_below_of_scopedBy
    {support : List UnificationVar} (aliases : List FreshAliasSequence.Alias)
    (body : Generated) (boundary : Supply)
    (scopeProof : ScopedBy support aliases)
    (bodySupported : ∀ candidate, candidate ∈ body.unificationVars →
      candidate ∈ support)
    (supportBelow : ∀ candidate, candidate ∈ support →
      candidate.Below boundary.ty boundary.cap)
    (freshBelow : ∀ alias, alias ∈ aliases →
      (freshVariable alias).Below boundary.ty boundary.cap) :
    ∀ candidate,
      candidate ∈ (FreshAliasSequence.addAll aliases body).unificationVars →
        candidate.Below boundary.ty boundary.cap := by
  induction aliases generalizing support body with
  | nil =>
      intro candidate member
      exact supportBelow candidate (bodySupported candidate member)
  | cons alias aliases induction =>
      have endpoints := scopeProof.2 alias (by simp)
      have tailScope := scopeProof.tail_extended
      apply induction (support := freshVariable alias :: support)
        (body := alias.add body) tailScope
      · exact alias_add_support_subset alias body bodySupported endpoints.2
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with rfl | oldMember
        · exact freshBelow alias (by simp)
        · exact supportBelow candidate oldMember
      · intro later laterMember
        exact freshBelow later (by simp [laterMember])

namespace EntailedGeneratedAlignment

/-- Direct entailed alignment upgraded to the recursive, future-fixing
closure invariant. -/
noncomputable def freshClosureAlignment
    {leftGenerated rightGenerated : Generated}
    (generatedAlignment :
      EntailedGeneratedAlignment leftGenerated rightGenerated)
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (boundary : Supply)
    (contextBelow : context.initialSupply.Le boundary)
    (rightGeneratedBelow : ∀ candidate,
      candidate ∈ rightGenerated.unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    FreshClosureAlignment left right context boundary := by
  let transported :=
    left.transportEntailed_absorbing_target
      generatedAlignment.hardEquivalent
      generatedAlignment.pendingAligned
      leftAbsorbing generatedAlignment.targetEntailed
  let middle := Classical.choose transported
  have middleSpec := Classical.choose_spec transported
  have substitutionEqual : middle.substitution = left.substitution :=
    middleSpec.2.2.1
  have middleAbsorbing : middle.Absorbing := middleSpec.2.2.2.1
  have targetEqual : left.target = middle.target := middleSpec.2.2.2.2
  let middleFresh : FreshClosureAlignment middle right context boundary :=
    FreshClosureAlignment.ofSameGeneratedSupportBelow
      middle right middleAbsorbing rightAbsorbing context boundary
      contextBelow rightGeneratedBelow
  let finalAlignment : CrossGeneratedClosureAlignment left right context :=
    { rho := middleFresh.alignment.rho
      closedContext_exact := by
        rw [← substitutionEqual]
        exact middleFresh.alignment.closedContext_exact
      target_exact := by
        rw [targetEqual]
        exact middleFresh.alignment.target_exact
      generalized_exact := by
        rw [← substitutionEqual, targetEqual]
        exact middleFresh.alignment.generalized_exact
      equations := by
        rw [← substitutionEqual]
        exact middleFresh.alignment.equations }
  exact
    { alignment := finalAlignment
      fixesAtOrAbove := middleFresh.fixesAtOrAbove }

end EntailedGeneratedAlignment

end TypePM.Source
