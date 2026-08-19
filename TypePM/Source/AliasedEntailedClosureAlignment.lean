import TypePM.Source.AliasContextFreshness
import TypePM.Source.EntailedClosureAlignment

/-!
# Closure alignment through finite fresh aliases

An entailed generated-block alignment may become visible only after adding
different admissible fresh-alias sequences on its two sides.  This module
lifts absorbing principal closures to those augmented blocks, applies the
direct entailed-closure theorem there, and transports its target and source
context endpoints back to the original closures.
-/

namespace TypePM.Source

open FreshAliasSequence
open FreshAliasPrincipalClosure

/-- Alias-augmented entailed alignment preserves the two original principal
targets up to mutual substitution instance. -/
theorem aliasedEntailedClosureTargets_mutualInstances
    {leftGenerated rightGenerated : Generated}
    (leftAliases rightAliases : List Alias)
    (leftAdmissible : Admissible leftAliases leftGenerated)
    (rightAdmissible : Admissible rightAliases rightGenerated)
    (leftTargetFixed : SequenceTargetFixed leftAliases leftGenerated)
    (rightTargetFixed : SequenceTargetFixed rightAliases rightGenerated)
    (generatedAlignment : EntailedGeneratedAlignment
      (addAll leftAliases leftGenerated)
      (addAll rightAliases rightGenerated))
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    IsInstance left.target right.target ∧
      IsInstance right.target left.target := by
  obtain ⟨liftedLeft, liftedLeftAbsorbing, liftedLeftTarget,
      _leftHard, _leftResidual, _leftSubstitution⟩ :=
    exists_liftAll_absorbing_data leftAliases leftGenerated leftAdmissible
      leftTargetFixed left leftAbsorbing
  obtain ⟨liftedRight, liftedRightAbsorbing, liftedRightTarget,
      _rightHard, _rightResidual, _rightSubstitution⟩ :=
    exists_liftAll_absorbing_data rightAliases rightGenerated rightAdmissible
      rightTargetFixed right rightAbsorbing
  have liftedInstances :=
    generatedAlignment.closureTargets_mutualInstances
      liftedLeft liftedRight liftedLeftAbsorbing liftedRightAbsorbing context
  constructor
  · simpa [liftedLeftTarget, liftedRightTarget] using liftedInstances.1
  · simpa [liftedLeftTarget, liftedRightTarget] using liftedInstances.2

/-- With explicit preservation of the closed contexts and literal interface
equations, the augmented alignment yields the full heterogeneous closure
alignment for the original closures. -/
noncomputable def aliasedEntailedClosureAlignment
    {leftGenerated rightGenerated : Generated}
    (leftAliases rightAliases : List Alias)
    (leftAdmissible : Admissible leftAliases leftGenerated)
    (rightAdmissible : Admissible rightAliases rightGenerated)
    (leftTargetFixed : SequenceTargetFixed leftAliases leftGenerated)
    (rightTargetFixed : SequenceTargetFixed rightAliases rightGenerated)
    (generatedAlignment : EntailedGeneratedAlignment
      (addAll leftAliases leftGenerated)
      (addAll rightAliases rightGenerated))
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context)
    (leftContextFixed :
      CumulativeAliasContextFixed leftAliases left context)
    (rightContextFixed :
      CumulativeAliasContextFixed rightAliases right context) :
    CrossGeneratedClosureAlignment left right context := by
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
  let liftedAlignment := generatedAlignment.closureAlignment
    liftedLeft liftedRight liftedLeftAbsorbing liftedRightAbsorbing context
  exact
    { rho := liftedAlignment.rho
      closedContext_exact := by
        have closed := liftedAlignment.closedContext_exact
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.closedContext,
          rightContextFixed.closedContext] at closed
        exact closed
      target_exact := by
        rw [← liftedLeftTarget, ← liftedRightTarget]
        exact liftedAlignment.target_exact
      generalized_exact := by
        have generalized := liftedAlignment.generalized_exact
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.closedContext,
          rightContextFixed.closedContext,
          liftedLeftTarget, liftedRightTarget] at generalized
        exact generalized
      equations := by
        have equations := liftedAlignment.equations
        rw [liftedLeftSubstitution, liftedRightSubstitution,
          leftContextFixed.interfaceEquations,
          rightContextFixed.interfaceEquations] at equations
        exact equations }

end TypePM.Source
