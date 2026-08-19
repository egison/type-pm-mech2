import TypePM.EntailedPrincipalClosureTransport
import TypePM.Source.EntailedAlignment
import TypePM.Source.RecursiveLetInvariant

/-!
# Closure alignment for directly aligned generated blocks

An entailed alignment transports an absorbing principal closure from the
left generated block to a middle closure on the right block without changing
its substitutions or closed target.  The existing same-generated closure
construction then aligns that middle closure with any absorbing right
closure.  Rewriting the middle endpoints yields the heterogeneous closure
certificate for the original left and right closures.

This is the direct case only: no fresh alias equations are added or removed.
-/

namespace TypePM.Source

namespace EntailedGeneratedAlignment

/-- Direct semantic alignment of generated value blocks induces the full
closure-interface alignment needed at a `let` boundary. -/
noncomputable def closureAlignment
    {leftGenerated rightGenerated : Generated}
    (generatedAlignment :
      EntailedGeneratedAlignment leftGenerated rightGenerated)
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    CrossGeneratedClosureAlignment left right context := by
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
  let middleAlignment : CrossGeneratedClosureAlignment middle right context :=
    CrossGeneratedClosureAlignment.ofSameGenerated
      middleAbsorbing rightAbsorbing context
  exact
    { rho := middleAlignment.rho
      closedContext_exact := by
        rw [← substitutionEqual]
        exact middleAlignment.closedContext_exact
      target_exact := by
        rw [targetEqual]
        exact middleAlignment.target_exact
      generalized_exact := by
        rw [← substitutionEqual, targetEqual]
        exact middleAlignment.generalized_exact
      equations := by
        rw [← substitutionEqual]
        exact middleAlignment.equations }

/-- Target-level principality consequence of direct entailed block
alignment. -/
theorem closureTargets_mutualInstances
    {leftGenerated rightGenerated : Generated}
    (generatedAlignment :
      EntailedGeneratedAlignment leftGenerated rightGenerated)
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    IsInstance left.target right.target ∧
      IsInstance right.target left.target := by
  exact (generatedAlignment.closureAlignment left right leftAbsorbing
    rightAbsorbing context).targets_mutualInstances

end EntailedGeneratedAlignment

end TypePM.Source
