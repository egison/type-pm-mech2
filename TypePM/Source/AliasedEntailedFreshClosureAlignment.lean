import TypePM.Source.AliasedEntailedClosureAlignment
import TypePM.Source.EntailedFreshClosureAlignment

/-!
# Future-fixing closure alignment through finite aliases
-/

namespace TypePM.Source

open FreshAliasSequence
open FreshAliasPrincipalClosure

/-- Alias-augmented entailed alignment upgraded to `FreshClosureAlignment`.
The right augmented support bound is exactly what ensures that the finite
closure renaming leaves the future source stream fixed. -/
noncomputable def aliasedEntailedFreshClosureAlignment
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
    (leftContextFixed :
      CumulativeAliasContextFixed leftAliases left context)
    (rightContextFixed :
      CumulativeAliasContextFixed rightAliases right context)
    (contextBelow : context.initialSupply.Le boundary)
    (rightAugmentedBelow : ∀ candidate,
      candidate ∈ (FreshAliasSequence.addAll
        rightAliases rightGenerated).unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    FreshClosureAlignment left right context boundary := by
  let leftLift := exists_liftAll_absorbing_data
    leftAliases leftGenerated leftAdmissible leftTargetFixed
    left leftAbsorbing
  let liftedLeft := Classical.choose leftLift
  have liftedLeftSpec := Classical.choose_spec leftLift
  let rightLift := exists_liftAll_absorbing_data
    rightAliases rightGenerated rightAdmissible rightTargetFixed
    right rightAbsorbing
  let liftedRight := Classical.choose rightLift
  have liftedRightSpec := Classical.choose_spec rightLift
  have liftedLeftAbsorbing : liftedLeft.Absorbing := liftedLeftSpec.1
  have liftedLeftTarget : liftedLeft.target = left.target :=
    liftedLeftSpec.2.1
  have liftedLeftSubstitution :
      liftedLeft.substitution =
        Subst.compose left.substitution
          (sequenceSubstitution leftAliases) :=
    liftedLeftSpec.2.2.2.2
  have liftedRightAbsorbing : liftedRight.Absorbing := liftedRightSpec.1
  have liftedRightTarget : liftedRight.target = right.target :=
    liftedRightSpec.2.1
  have liftedRightSubstitution :
      liftedRight.substitution =
        Subst.compose right.substitution
          (sequenceSubstitution rightAliases) :=
    liftedRightSpec.2.2.2.2
  let liftedFresh := generatedAlignment.freshClosureAlignment
    liftedLeft liftedRight liftedLeftAbsorbing liftedRightAbsorbing
    context boundary contextBelow rightAugmentedBelow
  let finalAlignment : CrossGeneratedClosureAlignment left right context :=
    { rho := liftedFresh.alignment.rho
      closedContext_exact := by
        have closed := liftedFresh.alignment.closedContext_exact
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.closedContext,
          rightContextFixed.closedContext] at closed
        exact closed
      target_exact := by
        rw [← liftedLeftTarget, ← liftedRightTarget]
        exact liftedFresh.alignment.target_exact
      generalized_exact := by
        have generalized := liftedFresh.alignment.generalized_exact
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.closedContext,
          rightContextFixed.closedContext,
          liftedLeftTarget, liftedRightTarget] at generalized
        exact generalized
      equations := by
        have equations := liftedFresh.alignment.equations
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.interfaceEquations,
          rightContextFixed.interfaceEquations] at equations
        exact equations }
  exact
    { alignment := finalAlignment
      fixesAtOrAbove := liftedFresh.fixesAtOrAbove }

end TypePM.Source
