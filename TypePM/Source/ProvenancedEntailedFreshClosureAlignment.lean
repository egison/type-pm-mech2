import TypePM.Source.EntailedFreshClosureAlignment
import TypePM.Source.ProvenancedFreshClosureAlignment

/-!
# Provenance-preserving closure alignment from entailed blocks
-/

namespace TypePM.Source

namespace EntailedGeneratedAlignment

/-- Entailed generated-block alignment upgraded to the future-fixing
closure invariant without discarding the pointwise interface alias shape of
the final same-generated representative comparison. -/
noncomputable def provenancedFreshClosureAlignment
    {leftGenerated rightGenerated : Generated}
    (generatedAlignment : EntailedGeneratedAlignment leftGenerated rightGenerated)
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (boundary : Supply)
    (contextBelow : context.initialSupply.Le boundary)
    (rightGeneratedBelow : ∀ candidate,
      candidate ∈ rightGenerated.unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    ProvenancedFreshClosureAlignment left right context boundary := by
  let transported := left.transportEntailed_absorbing_target
    generatedAlignment.hardEquivalent generatedAlignment.pendingAligned
    leftAbsorbing generatedAlignment.targetEntailed
  let middle := Classical.choose transported
  have middleSpec := Classical.choose_spec transported
  have substitutionEqual : middle.substitution = left.substitution :=
    middleSpec.2.2.1
  have middleAbsorbing : middle.Absorbing := middleSpec.2.2.2.1
  have targetEqual : left.target = middle.target := middleSpec.2.2.2.2
  let middleAlignment :=
    ProvenancedFreshClosureAlignment.ofSameGeneratedSupportBelow
      middle right middleAbsorbing rightAbsorbing context boundary
      contextBelow rightGeneratedBelow
  let finalCross : CrossGeneratedClosureAlignment left right context :=
    { rho := middleAlignment.alignment.alignment.rho
      closedContext_exact := by
        rw [← substitutionEqual]
        exact middleAlignment.alignment.alignment.closedContext_exact
      target_exact := by
        rw [targetEqual]
        exact middleAlignment.alignment.alignment.target_exact
      generalized_exact := by
        rw [← substitutionEqual, targetEqual]
        exact middleAlignment.alignment.alignment.generalized_exact
      equations := by
        rw [← substitutionEqual]
        exact middleAlignment.alignment.alignment.equations }
  let finalFresh : FreshClosureAlignment left right context boundary :=
    { alignment := finalCross
      fixesAtOrAbove := middleAlignment.alignment.fixesAtOrAbove }
  refine
    { alignment := finalFresh
      interfaceShape := ?_ }
  simpa [finalFresh, finalCross, substitutionEqual] using
    middleAlignment.interfaceShape

end EntailedGeneratedAlignment

end TypePM.Source
