import TypePM.Source.AliasedEntailedFreshClosureAlignment
import TypePM.Source.ProvenancedEntailedFreshClosureAlignment

/-!
# Provenance-preserving closure alignment through finite aliases
-/

namespace TypePM.Source

open FreshAliasSequence
open FreshAliasPrincipalClosure

/-- Alias-augmented entailed alignment upgraded without discarding the
pointwise interface shape of the final representative comparison. -/
noncomputable def provenancedAliasedEntailedFreshClosureAlignment
    {leftGenerated rightGenerated : Generated}
    (leftAliases rightAliases : List FreshAliasSequence.Alias)
    (leftAdmissible : FreshAliasSequence.Admissible leftAliases leftGenerated)
    (rightAdmissible : FreshAliasSequence.Admissible rightAliases rightGenerated)
    (leftTargetFixed : SequenceTargetFixed leftAliases leftGenerated)
    (rightTargetFixed : SequenceTargetFixed rightAliases rightGenerated)
    (generatedAlignment : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll leftAliases leftGenerated)
      (FreshAliasSequence.addAll rightAliases rightGenerated))
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (boundary : Supply)
    (leftContextFixed : CumulativeAliasContextFixed leftAliases left context)
    (rightContextFixed : CumulativeAliasContextFixed rightAliases right context)
    (contextBelow : context.initialSupply.Le boundary)
    (rightAugmentedBelow : ∀ candidate,
      candidate ∈ (FreshAliasSequence.addAll
        rightAliases rightGenerated).unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    ProvenancedFreshClosureAlignment left right context boundary := by
  let leftLift := exists_liftAll_absorbing_data leftAliases leftGenerated
    leftAdmissible leftTargetFixed left leftAbsorbing
  let liftedLeft := Classical.choose leftLift
  have liftedLeftSpec := Classical.choose_spec leftLift
  let rightLift := exists_liftAll_absorbing_data rightAliases rightGenerated
    rightAdmissible rightTargetFixed right rightAbsorbing
  let liftedRight := Classical.choose rightLift
  have liftedRightSpec := Classical.choose_spec rightLift
  have liftedLeftAbsorbing : liftedLeft.Absorbing := liftedLeftSpec.1
  have liftedLeftTarget : liftedLeft.target = left.target := liftedLeftSpec.2.1
  have liftedLeftSubstitution : liftedLeft.substitution =
      Subst.compose left.substitution (sequenceSubstitution leftAliases) :=
    liftedLeftSpec.2.2.2.2
  have liftedRightAbsorbing : liftedRight.Absorbing := liftedRightSpec.1
  have liftedRightTarget : liftedRight.target = right.target := liftedRightSpec.2.1
  have liftedRightSubstitution : liftedRight.substitution =
      Subst.compose right.substitution (sequenceSubstitution rightAliases) :=
    liftedRightSpec.2.2.2.2
  let liftedAlignment := generatedAlignment.provenancedFreshClosureAlignment
    liftedLeft liftedRight liftedLeftAbsorbing liftedRightAbsorbing
    context boundary contextBelow rightAugmentedBelow
  let finalCross : CrossGeneratedClosureAlignment left right context :=
    { rho := liftedAlignment.alignment.alignment.rho
      closedContext_exact := by
        have closed := liftedAlignment.alignment.alignment.closedContext_exact
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.closedContext, rightContextFixed.closedContext] at closed
        exact closed
      target_exact := by
        rw [← liftedLeftTarget, ← liftedRightTarget]
        exact liftedAlignment.alignment.alignment.target_exact
      generalized_exact := by
        have generalized := liftedAlignment.alignment.alignment.generalized_exact
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.closedContext, rightContextFixed.closedContext,
          liftedLeftTarget, liftedRightTarget] at generalized
        exact generalized
      equations := by
        have equations := liftedAlignment.alignment.alignment.equations
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.interfaceEquations,
          rightContextFixed.interfaceEquations] at equations
        exact equations }
  let finalFresh : FreshClosureAlignment left right context boundary :=
    { alignment := finalCross
      fixesAtOrAbove := liftedAlignment.alignment.fixesAtOrAbove }
  refine
    { alignment := finalFresh
      interfaceShape := ?_ }
  simpa [finalFresh, finalCross, liftedLeftSubstitution,
    liftedRightSubstitution, leftContextFixed.interfaceEquations,
    rightContextFixed.interfaceEquations] using liftedAlignment.interfaceShape

end TypePM.Source
