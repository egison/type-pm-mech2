import TypePM.AbsorbingBlockClosure
import TypePM.FreshAliasSequence

/-!
# Principal closures across fresh aliases

Fresh aliases are auxiliary equations of the form `fresh = existing`.  The
acceptance-level transport is already available in `FreshAliasSaturation`.
This module packages the same construction for principal block closures.

`FreshAliasSequence.Alias.Admissible` only constrains the hard and pending
fields of a block.  It deliberately says nothing about the target.  Target
comparison therefore uses the additional, precise premise `TargetFixed`.
-/

namespace TypePM
namespace FreshAliasPrincipalClosure

open FreshAliasSequence

/-- The elementary substitution represented by one fresh alias. -/
def aliasSubstitution : Alias → Subst
  | .ty fresh existing => Subst.singleTy fresh (.var existing)
  | .cap fresh existing => Subst.singleCap fresh (.var existing)

/-- The endpoint eliminated by an alias. -/
def aliasFreshVariable : Alias → UnificationVar
  | .ty fresh _existing => .ty fresh
  | .cap fresh _existing => .cap fresh

/-- The hard equation contributed by one alias. -/
def aliasEquation : Alias → Equation
  | .ty fresh existing => .ty (.var fresh) (.var existing)
  | .cap fresh existing => .cap (.var fresh) (.var existing)

/-- The extra premise needed when closure targets, rather than acceptance
alone, are transported across an alias. -/
def TargetFixed (alias : Alias) (body : Generated) : Prop :=
  body.target.apply (aliasSubstitution alias) = body.target

/-- Lift a principal closure through one admissible fresh alias. -/
theorem exists_lift
    (alias : Alias) (body : Generated)
    (admissible : alias.Admissible body)
    (closure : PrincipalBlockClosure body) :
    ∃ lifted : PrincipalBlockClosure (alias.add body),
      lifted.finalHard = aliasEquation alias :: closure.finalHard ∧
        lifted.finalPending = closure.finalPending ∧
        lifted.hardSubstitution =
          Subst.compose closure.hardSubstitution (aliasSubstitution alias) ∧
        lifted.residualSubstitution = closure.residualSubstitution := by
  cases alias with
  | ty fresh existing =>
      obtain ⟨finalInvariant, liftedSaturation⟩ :=
        FreshAliasSaturation.Saturated.liftTyAlias
          closure.saturation admissible.1 admissible.2
      refine ⟨
        { finalHard := .ty (.var fresh) (.var existing) :: closure.finalHard
          finalPending := closure.finalPending
          hardSubstitution := Subst.compose closure.hardSubstitution
            (Subst.singleTy fresh (.var existing))
          residualSubstitution := closure.residualSubstitution
          saturation := liftedSaturation
          residualPrincipal := ?_ }, rfl, rfl, rfl, rfl⟩
      have residualEquality :=
        FreshAliasSaturation.residualEquations_compose_of_pendingFixed
          closure.hardSubstitution
          (Subst.singleTy fresh (.var existing)) closure.finalPending
          finalInvariant.2
      rw [residualEquality]
      exact closure.residualPrincipal
  | cap fresh existing =>
      obtain ⟨finalInvariant, liftedSaturation⟩ :=
        FreshAliasSaturation.Saturated.liftCapAlias
          closure.saturation admissible.1 admissible.2
      refine ⟨
        { finalHard := .cap (.var fresh) (.var existing) :: closure.finalHard
          finalPending := closure.finalPending
          hardSubstitution := Subst.compose closure.hardSubstitution
            (Subst.singleCap fresh (.var existing))
          residualSubstitution := closure.residualSubstitution
          saturation := liftedSaturation
          residualPrincipal := ?_ }, rfl, rfl, rfl, rfl⟩
      have residualEquality :=
        FreshAliasSaturation.residualEquations_compose_of_pendingFixed
          closure.hardSubstitution
          (Subst.singleCap fresh (.var existing)) closure.finalPending
          finalInvariant.2
      rw [residualEquality]
      exact closure.residualPrincipal

/-- Under target invariance, lifting does not change the principal target. -/
theorem exists_lift_target_eq
    (alias : Alias) (body : Generated)
    (admissible : alias.Admissible body)
    (targetFixed : TargetFixed alias body)
    (closure : PrincipalBlockClosure body) :
    ∃ lifted : PrincipalBlockClosure (alias.add body),
      lifted.target = closure.target := by
  obtain ⟨lifted, _finalHard, _finalPending,
      hardEquality, residualEquality⟩ :=
    exists_lift alias body admissible closure
  refine ⟨lifted, ?_⟩
  simp only [PrincipalBlockClosure.target,
    PrincipalBlockClosure.substitution]
  rw [hardEquality, residualEquality]
  change (alias.add body).target.apply
      (Subst.compose closure.residualSubstitution
        (Subst.compose closure.hardSubstitution
          (aliasSubstitution alias))) = _
  have addTarget : (alias.add body).target = body.target := by
    cases alias <;> rfl
  rw [addTarget]
  cases alias with
  | ty fresh existing =>
      change body.target.apply
          (Subst.singleTy fresh (.var existing)) = body.target at targetFixed
      simp only [aliasSubstitution]
      rw [Subst.compose_assoc, ← Ty.apply_compose]
      rw [targetFixed]
  | cap fresh existing =>
      change body.target.apply
          (Subst.singleCap fresh (.var existing)) = body.target at targetFixed
      simp only [aliasSubstitution]
      rw [Subst.compose_assoc, ← Ty.apply_compose]
      rw [targetFixed]

/-- Lifting through one admissible alias preserves absorption of both the
hard and residual representatives. -/
theorem exists_lift_absorbing
    (alias : Alias) (body : Generated)
    (admissible : alias.Admissible body)
    (closure : PrincipalBlockClosure body)
    (absorbing : closure.Absorbing) :
    ∃ lifted : PrincipalBlockClosure (alias.add body),
      lifted.Absorbing ∧
        lifted.hardSubstitution =
          Subst.compose closure.hardSubstitution (aliasSubstitution alias) ∧
        lifted.residualSubstitution = closure.residualSubstitution := by
  obtain ⟨lifted, finalHardEquality, finalPendingEquality,
      hardEquality, residualEquality⟩ :=
    exists_lift alias body admissible closure
  refine ⟨lifted, ⟨?_, ?_⟩, hardEquality, residualEquality⟩
  · constructor
    · exact lifted.saturation.principal
    · intro solution solved
      rw [finalHardEquality] at solved
      have bodySolved : Solves solution closure.finalHard :=
        (solves_cons solution _ _).mp solved |>.2
      have bodyAbsorbed := absorbing.1.absorbs bodySolved
      have aliasAbsorbed :
          Subst.compose solution (aliasSubstitution alias) = solution := by
        cases alias with
        | ty fresh existing =>
            let reduction : Reduces
                (.ty (.var fresh) (.var existing) :: closure.finalHard)
                (Subst.singleTy fresh (.var existing))
                (closure.finalHard.map
                  (Equation.apply
                    (Subst.singleTy fresh (.var existing)))) :=
              .tyVarLeft (by
                have different : existing ≠ fresh := Ne.symm admissible.1
                simp [Ty.occursTy, different])
            exact reduction.absorbed solved
        | cap fresh existing =>
            let reduction : Reduces
                (.cap (.var fresh) (.var existing) :: closure.finalHard)
                (Subst.singleCap fresh (.var existing))
                (closure.finalHard.map
                  (Equation.apply
                    (Subst.singleCap fresh (.var existing)))) :=
              .capVarLeft (by
                have different : existing ≠ fresh := Ne.symm admissible.1
                simp [Cap.occurs, different])
            exact reduction.absorbed solved
      calc
        Subst.compose solution lifted.hardSubstitution =
            Subst.compose solution
              (Subst.compose closure.hardSubstitution
                (aliasSubstitution alias)) := by rw [hardEquality]
        _ = Subst.compose
              (Subst.compose solution closure.hardSubstitution)
              (aliasSubstitution alias) :=
            Subst.compose_assoc _ _ _
        _ = Subst.compose solution (aliasSubstitution alias) := by
            rw [bodyAbsorbed]
        _ = solution := aliasAbsorbed
  · rw [finalPendingEquality, hardEquality, residualEquality]
    cases alias with
    | ty fresh existing =>
        have finalInvariant :=
          FreshAliasSaturation.PromotionClosure.tyInvariant_final
            closure.saturation.closure admissible.2
        simp only [aliasSubstitution]
        rw [FreshAliasSaturation.residualEquations_compose_of_pendingFixed
          closure.hardSubstitution
          (Subst.singleTy fresh (.var existing)) closure.finalPending
          finalInvariant.2]
        exact absorbing.2
    | cap fresh existing =>
        have finalInvariant :=
          FreshAliasSaturation.PromotionClosure.capInvariant_final
            closure.saturation.closure admissible.2
        simp only [aliasSubstitution]
        rw [FreshAliasSaturation.residualEquations_compose_of_pendingFixed
          closure.hardSubstitution
          (Subst.singleCap fresh (.var existing)) closure.finalPending
          finalInvariant.2]
        exact absorbing.2

/-- Absorbing lift together with literal target preservation. -/
theorem exists_lift_absorbing_target_eq
    (alias : Alias) (body : Generated)
    (admissible : alias.Admissible body)
    (targetFixed : TargetFixed alias body)
    (closure : PrincipalBlockClosure body)
    (absorbing : closure.Absorbing) :
    ∃ lifted : PrincipalBlockClosure (alias.add body),
      lifted.Absorbing ∧ lifted.target = closure.target ∧
        lifted.hardSubstitution =
          Subst.compose closure.hardSubstitution (aliasSubstitution alias) ∧
        lifted.residualSubstitution = closure.residualSubstitution := by
  obtain ⟨lifted, liftedAbsorbing⟩ :=
    exists_lift_absorbing alias body admissible closure absorbing
  rcases liftedAbsorbing with
    ⟨liftedAbsorbing, hardEquality, residualEquality⟩
  have targetEquality : lifted.target = closure.target := by
    simp only [PrincipalBlockClosure.target,
      PrincipalBlockClosure.substitution]
    rw [hardEquality, residualEquality]
    change (alias.add body).target.apply
        (Subst.compose closure.residualSubstitution
          (Subst.compose closure.hardSubstitution
            (aliasSubstitution alias))) = _
    have addTarget : (alias.add body).target = body.target := by
      cases alias <;> rfl
    rw [addTarget]
    cases alias with
    | ty fresh existing =>
        change body.target.apply
            (Subst.singleTy fresh (.var existing)) = body.target at targetFixed
        simp only [aliasSubstitution]
        rw [Subst.compose_assoc, ← Ty.apply_compose, targetFixed]
    | cap fresh existing =>
        change body.target.apply
            (Subst.singleCap fresh (.var existing)) = body.target at targetFixed
        simp only [aliasSubstitution]
        rw [Subst.compose_assoc, ← Ty.apply_compose, targetFixed]
  exact ⟨lifted, liftedAbsorbing, targetEquality,
    hardEquality, residualEquality⟩

/-- Project an arbitrary principal closure of an aliased block back to a
principal closure of the body.  The projected representatives are allowed to
differ: only existence is intrinsic at this boundary. -/
theorem project
    (alias : Alias) (body : Generated)
    (admissible : alias.Admissible body)
    (closure : PrincipalBlockClosure (alias.add body)) :
    Nonempty (PrincipalBlockClosure body) := by
  cases alias with
  | ty fresh existing =>
      have initialHead :
          ((FreshAliasSequence.Alias.ty fresh existing).add body).hard =
          .ty (.var fresh) (.var existing) :: body.hard := rfl
      have finalShape : ∃ finalHard,
          closure.finalHard =
            .ty (.var fresh) (.var existing) :: finalHard := by
        obtain ⟨extra, equality⟩ :=
          FreshAliasSaturation.PromotionClosure.final_eq_append
            closure.saturation.closure
        exact ⟨body.hard ++ extra, by simpa [initialHead] using equality⟩
      obtain ⟨finalHard, finalEquality⟩ := finalShape
      have aliasedSaturation := closure.saturation
      rw [initialHead, finalEquality] at aliasedSaturation
      obtain ⟨bodyHardSubstitution, bodySaturation, finalInvariant⟩ :=
        FreshAliasSaturation.Saturated.projectTyAlias admissible.1
          aliasedSaturation admissible.2
      obtain ⟨_liftedInvariant, liftedSaturation⟩ :=
        FreshAliasSaturation.Saturated.liftTyAlias
          bodySaturation admissible.1 admissible.2
      let aliasSubstitution := Subst.singleTy fresh (.var existing)
      let liftedHardSubstitution :=
        Subst.compose bodyHardSubstitution aliasSubstitution
      obtain ⟨aliasedToLifted, liftedToAliased⟩ :=
        aliasedSaturation.principal.mutualFactors liftedSaturation.principal
      obtain ⟨post, _factor, transportedSolved⟩ :=
        ResolutionTransport.residualEquations_transport_of_mutualFactors
          liftedToAliased aliasedToLifted closure.residualPrincipal.1
      have residualEquality :
          residualEquations liftedHardSubstitution closure.finalPending =
            residualEquations bodyHardSubstitution closure.finalPending :=
        FreshAliasSaturation.residualEquations_compose_of_pendingFixed
          bodyHardSubstitution aliasSubstitution closure.finalPending
          finalInvariant.2
      have residualSolvable : ∃ solution,
          Solves solution
            (residualEquations bodyHardSubstitution closure.finalPending) := by
        exact ⟨Subst.compose closure.residualSubstitution post, by
          rw [← residualEquality]
          exact transportedSolved⟩
      obtain ⟨bodyResidualSubstitution, residualSuccess⟩ :=
        unify_complete residualSolvable
      let projected : PrincipalBlockClosure body :=
        { finalHard := finalHard
          finalPending := closure.finalPending
          hardSubstitution := bodyHardSubstitution
          residualSubstitution := bodyResidualSubstitution
          saturation := bodySaturation
          residualPrincipal := unify_mostGeneral residualSuccess }
      exact ⟨projected⟩
  | cap fresh existing =>
      have initialHead :
          ((FreshAliasSequence.Alias.cap fresh existing).add body).hard =
          .cap (.var fresh) (.var existing) :: body.hard := rfl
      have finalShape : ∃ finalHard,
          closure.finalHard =
            .cap (.var fresh) (.var existing) :: finalHard := by
        obtain ⟨extra, equality⟩ :=
          FreshAliasSaturation.PromotionClosure.final_eq_append
            closure.saturation.closure
        exact ⟨body.hard ++ extra, by simpa [initialHead] using equality⟩
      obtain ⟨finalHard, finalEquality⟩ := finalShape
      have aliasedSaturation := closure.saturation
      rw [initialHead, finalEquality] at aliasedSaturation
      obtain ⟨bodyHardSubstitution, bodySaturation, finalInvariant⟩ :=
        FreshAliasSaturation.Saturated.projectCapAlias admissible.1
          aliasedSaturation admissible.2
      obtain ⟨_liftedInvariant, liftedSaturation⟩ :=
        FreshAliasSaturation.Saturated.liftCapAlias
          bodySaturation admissible.1 admissible.2
      let aliasSubstitution := Subst.singleCap fresh (.var existing)
      let liftedHardSubstitution :=
        Subst.compose bodyHardSubstitution aliasSubstitution
      obtain ⟨aliasedToLifted, liftedToAliased⟩ :=
        aliasedSaturation.principal.mutualFactors liftedSaturation.principal
      obtain ⟨post, _factor, transportedSolved⟩ :=
        ResolutionTransport.residualEquations_transport_of_mutualFactors
          liftedToAliased aliasedToLifted closure.residualPrincipal.1
      have residualEquality :
          residualEquations liftedHardSubstitution closure.finalPending =
            residualEquations bodyHardSubstitution closure.finalPending :=
        FreshAliasSaturation.residualEquations_compose_of_pendingFixed
          bodyHardSubstitution aliasSubstitution closure.finalPending
          finalInvariant.2
      have residualSolvable : ∃ solution,
          Solves solution
            (residualEquations bodyHardSubstitution closure.finalPending) := by
        exact ⟨Subst.compose closure.residualSubstitution post, by
          rw [← residualEquality]
          exact transportedSolved⟩
      obtain ⟨bodyResidualSubstitution, residualSuccess⟩ :=
        unify_complete residualSolvable
      let projected : PrincipalBlockClosure body :=
        { finalHard := finalHard
          finalPending := closure.finalPending
          hardSubstitution := bodyHardSubstitution
          residualSubstitution := bodyResidualSubstitution
          saturation := bodySaturation
          residualPrincipal := unify_mostGeneral residualSuccess }
      exact ⟨projected⟩

/-- With target invariance, an arbitrary aliased closure has a projected body
closure whose target is mutually substitutable with it. -/
theorem project_targets_mutualInstances
    (alias : Alias) (body : Generated)
    (admissible : alias.Admissible body)
    (targetFixed : TargetFixed alias body)
    (closure : PrincipalBlockClosure (alias.add body)) :
    ∃ projected : PrincipalBlockClosure body,
      IsInstance closure.target projected.target ∧
        IsInstance projected.target closure.target := by
  obtain ⟨projected⟩ := project alias body admissible closure
  obtain ⟨lifted, liftedTarget⟩ :=
    exists_lift_target_eq alias body admissible targetFixed projected
  obtain ⟨forward, backward⟩ := closure.targets_mutualInstances lifted
  exact ⟨projected, by simpa [liftedTarget] using forward,
    by simpa [liftedTarget] using backward⟩

private theorem isInstance_trans
    {first second third : Ty}
    (firstToSecond : IsInstance first second)
    (secondToThird : IsInstance second third) :
    IsInstance first third := by
  obtain ⟨firstSubstitution, firstEquality⟩ := firstToSecond
  obtain ⟨secondSubstitution, secondEquality⟩ := secondToThird
  exact ⟨Subst.compose secondSubstitution firstSubstitution, by
    rw [← Ty.apply_compose, firstEquality, secondEquality]⟩

/-- Every inhabited principal-closure type also has the absorbing
representative computed by the certified executable unifier. -/
theorem exists_absorbingClosure
    {generated : Generated} (closure : PrincipalBlockClosure generated) :
    ∃ absorbingClosure : PrincipalBlockClosure generated,
      absorbingClosure.Absorbing := by
  have succeeds :=
    closure.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases resultEquality : inferGeneratedUsing unify generated with
  | none => exact (succeeds resultEquality).elim
  | some result =>
      obtain ⟨absorbingClosure, _substitution, _target, absorbing⟩ :=
        inferGeneratedUsing_absorbingPrincipalBlockClosure
          unify_absorbingMGUSolver resultEquality
      exact ⟨absorbingClosure, absorbing⟩

/-- Projection may choose a fresh executable representative.  Under target
invariance it can therefore return an absorbing body closure while retaining
mutual target instancehood with the original aliased closure. -/
theorem project_absorbing_targets_mutualInstances
    (alias : Alias) (body : Generated)
    (admissible : alias.Admissible body)
    (targetFixed : TargetFixed alias body)
    (closure : PrincipalBlockClosure (alias.add body)) :
    ∃ projected : PrincipalBlockClosure body,
      projected.Absorbing ∧
        IsInstance closure.target projected.target ∧
        IsInstance projected.target closure.target := by
  obtain ⟨first, closureToFirst, firstToClosure⟩ :=
    project_targets_mutualInstances alias body admissible targetFixed closure
  obtain ⟨projected, absorbing⟩ := exists_absorbingClosure first
  obtain ⟨firstToProjected, projectedToFirst⟩ :=
    first.targets_mutualInstances projected
  exact ⟨projected, absorbing,
    isInstance_trans closureToFirst firstToProjected,
    isInstance_trans projectedToFirst firstToClosure⟩

/-! ## Finite alias sequences -/

/-- Every alias in a sequence leaves the common raw target fixed at the point
where that alias is added. -/
def SequenceTargetFixed : List Alias → Generated → Prop
  | [], _body => True
  | alias :: rest, body =>
      TargetFixed alias body ∧ SequenceTargetFixed rest (alias.add body)

/-- Composite alias substitution in the same step order as `addAll`. -/
def sequenceSubstitution : List Alias → Subst
  | [] => Subst.id
  | alias :: rest =>
      Subst.compose (aliasSubstitution alias) (sequenceSubstitution rest)

/-- Lift a principal closure through a finite admissible alias sequence. -/
theorem exists_liftAll
    (aliases : List Alias) (body : Generated)
    (admissible : FreshAliasSequence.Admissible aliases body)
    (closure : PrincipalBlockClosure body) :
    Nonempty (PrincipalBlockClosure
      (FreshAliasSequence.addAll aliases body)) := by
  induction aliases generalizing body with
  | nil => exact ⟨closure⟩
  | cons alias rest induction =>
      obtain ⟨first, _finalHard, _finalPending, _hard, _residual⟩ :=
        exists_lift alias body admissible.1 closure
      exact induction (body := alias.add body) admissible.2 first

/-- If every alias fixes the target, lifting the whole sequence preserves the
principal target literally. -/
theorem exists_liftAll_target_eq
    (aliases : List Alias) (body : Generated)
    (admissible : FreshAliasSequence.Admissible aliases body)
    (targetFixed : SequenceTargetFixed aliases body)
    (closure : PrincipalBlockClosure body) :
    ∃ lifted : PrincipalBlockClosure
      (FreshAliasSequence.addAll aliases body),
      lifted.target = closure.target := by
  induction aliases generalizing body with
  | nil => exact ⟨closure, rfl⟩
  | cons alias rest induction =>
      obtain ⟨first, firstTarget⟩ :=
        exists_lift_target_eq alias body admissible.1 targetFixed.1 closure
      obtain ⟨lifted, restTarget⟩ :=
        induction (body := alias.add body) admissible.2 targetFixed.2 first
      exact ⟨lifted, restTarget.trans firstTarget⟩

/-- Absorption is preserved while lifting through a finite admissible alias
sequence. -/
theorem exists_liftAll_absorbing
    (aliases : List Alias) (body : Generated)
    (admissible : FreshAliasSequence.Admissible aliases body)
    (closure : PrincipalBlockClosure body)
    (absorbing : closure.Absorbing) :
    ∃ lifted : PrincipalBlockClosure
      (FreshAliasSequence.addAll aliases body),
      lifted.Absorbing := by
  induction aliases generalizing body with
  | nil => exact ⟨closure, absorbing⟩
  | cons alias rest induction =>
      obtain ⟨first, firstAbsorbing, _hard, _residual⟩ :=
        exists_lift_absorbing alias body admissible.1 closure absorbing
      exact induction (body := alias.add body) admissible.2 first
        firstAbsorbing

/-- Finite absorbing lift with literal target preservation. -/
theorem exists_liftAll_absorbing_target_eq
    (aliases : List Alias) (body : Generated)
    (admissible : FreshAliasSequence.Admissible aliases body)
    (targetFixed : SequenceTargetFixed aliases body)
    (closure : PrincipalBlockClosure body)
    (absorbing : closure.Absorbing) :
    ∃ lifted : PrincipalBlockClosure
      (FreshAliasSequence.addAll aliases body),
      lifted.Absorbing ∧ lifted.target = closure.target := by
  induction aliases generalizing body with
  | nil => exact ⟨closure, absorbing, rfl⟩
  | cons alias rest induction =>
      obtain ⟨first, firstAbsorbing, firstTarget,
          _firstHard, _firstResidual⟩ :=
        exists_lift_absorbing_target_eq alias body admissible.1
          targetFixed.1 closure absorbing
      obtain ⟨lifted, liftedAbsorbing, restTarget⟩ :=
        induction (body := alias.add body) admissible.2 targetFixed.2
          first firstAbsorbing
      exact ⟨lifted, liftedAbsorbing, restTarget.trans firstTarget⟩

/-- Data-rich absorbing lift.  It exposes the accumulated alias action on
the hard and composed substitutions for source-context transport. -/
theorem exists_liftAll_absorbing_data
    (aliases : List Alias) (body : Generated)
    (admissible : FreshAliasSequence.Admissible aliases body)
    (targetFixed : SequenceTargetFixed aliases body)
    (closure : PrincipalBlockClosure body)
    (absorbing : closure.Absorbing) :
    ∃ lifted : PrincipalBlockClosure
      (FreshAliasSequence.addAll aliases body),
      lifted.Absorbing ∧
        lifted.target = closure.target ∧
        lifted.hardSubstitution =
          Subst.compose closure.hardSubstitution
            (sequenceSubstitution aliases) ∧
        lifted.residualSubstitution = closure.residualSubstitution ∧
        lifted.substitution =
          Subst.compose closure.substitution (sequenceSubstitution aliases) := by
  induction aliases generalizing body with
  | nil =>
      exact ⟨closure, absorbing, rfl, by simp [sequenceSubstitution], rfl,
        by
          change closure.substitution =
            Subst.compose closure.substitution Subst.id
          exact (Subst.compose_id_right _).symm⟩
  | cons alias rest induction =>
      obtain ⟨first, firstAbsorbing, firstTarget,
          firstHard, firstResidual⟩ :=
        exists_lift_absorbing_target_eq alias body admissible.1
          targetFixed.1 closure absorbing
      obtain ⟨lifted, liftedAbsorbing, restTarget,
          restHard, restResidual, _restSubstitution⟩ :=
        induction (body := alias.add body) admissible.2 targetFixed.2
          first firstAbsorbing
      refine ⟨lifted, liftedAbsorbing, restTarget.trans firstTarget, ?_,
        firstResidual ▸ restResidual, ?_⟩
      · rw [restHard, firstHard]
        exact (Subst.compose_assoc closure.hardSubstitution
          (aliasSubstitution alias) (sequenceSubstitution rest)).symm
      · simp only [PrincipalBlockClosure.substitution]
        rw [restResidual, restHard, firstResidual, firstHard]
        simp only [sequenceSubstitution]
        rw [← Subst.compose_assoc closure.hardSubstitution
          (aliasSubstitution alias) (sequenceSubstitution rest)]
        rw [Subst.compose_assoc closure.residualSubstitution
          closure.hardSubstitution
          (Subst.compose (aliasSubstitution alias)
            (sequenceSubstitution rest))]

/-- Project a principal closure through a finite admissible alias sequence. -/
theorem exists_projectAll
    (aliases : List Alias) (body : Generated)
    (admissible : FreshAliasSequence.Admissible aliases body)
    (closure : PrincipalBlockClosure
      (FreshAliasSequence.addAll aliases body)) :
    Nonempty (PrincipalBlockClosure body) := by
  induction aliases generalizing body with
  | nil => exact ⟨closure⟩
  | cons alias rest induction =>
      obtain ⟨middle⟩ :=
        induction (body := alias.add body) admissible.2 closure
      exact project alias body admissible.1 middle

/-- Under sequence target invariance, projection preserves the principal
target up to mutual substitution instance. -/
theorem projectAll_targets_mutualInstances
    (aliases : List Alias) (body : Generated)
    (admissible : FreshAliasSequence.Admissible aliases body)
    (targetFixed : SequenceTargetFixed aliases body)
    (closure : PrincipalBlockClosure
      (FreshAliasSequence.addAll aliases body)) :
    ∃ projected : PrincipalBlockClosure body,
      IsInstance closure.target projected.target ∧
        IsInstance projected.target closure.target := by
  induction aliases generalizing body with
  | nil =>
      exact ⟨closure, ⟨Subst.id, Ty.apply_id _⟩,
        ⟨Subst.id, Ty.apply_id _⟩⟩
  | cons alias rest induction =>
      obtain ⟨middle, closureToMiddle, middleToClosure⟩ :=
        induction (body := alias.add body) admissible.2 targetFixed.2 closure
      obtain ⟨projected, middleToProjected, projectedToMiddle⟩ :=
        project_targets_mutualInstances alias body admissible.1
          targetFixed.1 middle
      exact ⟨projected,
        isInstance_trans closureToMiddle middleToProjected,
        isInstance_trans projectedToMiddle middleToClosure⟩

/-- Sequence projection with an absorbing representative at the body
endpoint. -/
theorem projectAll_absorbing_targets_mutualInstances
    (aliases : List Alias) (body : Generated)
    (admissible : FreshAliasSequence.Admissible aliases body)
    (targetFixed : SequenceTargetFixed aliases body)
    (closure : PrincipalBlockClosure
      (FreshAliasSequence.addAll aliases body)) :
    ∃ projected : PrincipalBlockClosure body,
      projected.Absorbing ∧
        IsInstance closure.target projected.target ∧
        IsInstance projected.target closure.target := by
  obtain ⟨first, closureToFirst, firstToClosure⟩ :=
    projectAll_targets_mutualInstances aliases body admissible targetFixed
      closure
  obtain ⟨projected, absorbing⟩ := exists_absorbingClosure first
  obtain ⟨firstToProjected, projectedToFirst⟩ :=
    first.targets_mutualInstances projected
  exact ⟨projected, absorbing,
    isInstance_trans closureToFirst firstToProjected,
    isInstance_trans projectedToFirst firstToClosure⟩

/-! ## Why target invariance is necessary -/

private def counterFresh : TyVar := ⟨0⟩
private def counterExisting : TyVar := ⟨1⟩

private def counterBody : Generated :=
  { target := .prod [.var counterFresh, .var counterExisting]
    hard := []
    pending := [] }

private def counterAlias : Alias :=
  .ty counterFresh counterExisting

private theorem counterAlias_admissible :
    counterAlias.Admissible counterBody := by
  exact ⟨by decide, ⟨rfl, rfl⟩⟩

private theorem id_mostGeneral_nil : MostGeneral [] Subst.id := by
  constructor
  · exact solves_nil _
  · intro solution _solved
    exact ⟨solution, by simp⟩

private def counterBodyClosure : PrincipalBlockClosure counterBody :=
  { finalHard := []
    finalPending := []
    hardSubstitution := Subst.id
    residualSubstitution := Subst.id
    saturation :=
      { closure := .refl
        principal := id_mostGeneral_nil
        stable := by simp [promoteUnder] }
    residualPrincipal := by
      simpa [residualEquations] using id_mostGeneral_nil }

private theorem collapsed_not_instance_of_distinct :
    ¬ IsInstance
      (.prod [.var counterExisting, .var counterExisting])
      (.prod [.var counterFresh, .var counterExisting]) := by
  rintro ⟨substitution, equality⟩
  simp only [Ty.apply, Ty.applyList] at equality
  injection equality with itemsEquality
  simp only [List.cons.injEq] at itemsEquality
  have variableEquality :
      Ty.var counterFresh = Ty.var counterExisting :=
    itemsEquality.1.symm.trans itemsEquality.2.1
  injection variableEquality with indexEquality
  exact (by decide : counterFresh ≠ counterExisting) indexEquality

/-- `Alias.Admissible` alone cannot support mutual target instancehood.  In
this minimal block the target contains both the fresh and existing endpoint;
the alias collapses them, losing the information that they were distinct. -/
theorem admissible_not_sufficient_for_target_mutualInstances :
    ∃ aliasedClosure : PrincipalBlockClosure (counterAlias.add counterBody),
      ¬ IsInstance aliasedClosure.target counterBodyClosure.target := by
  obtain ⟨aliasedClosure, _finalHard, _finalPending,
      hardEquality, residualEquality⟩ :=
    exists_lift counterAlias counterBody counterAlias_admissible
      counterBodyClosure
  refine ⟨aliasedClosure, ?_⟩
  have targetEquality : aliasedClosure.target =
      .prod [.var counterExisting, .var counterExisting] := by
    simp [PrincipalBlockClosure.target, PrincipalBlockClosure.substitution,
      hardEquality, residualEquality, counterAlias, counterBodyClosure,
      counterBody, aliasSubstitution, counterFresh, counterExisting,
      FreshAliasSequence.Alias.add, FreshAliasElimination.addTyAlias,
      Subst.compose, Subst.singleTy, Ty.apply, Ty.applyList]
  have bodyTargetEquality : counterBodyClosure.target =
      .prod [.var counterFresh, .var counterExisting] := by
    simp [PrincipalBlockClosure.target, PrincipalBlockClosure.substitution,
      counterBodyClosure, counterBody]
  rw [targetEquality, bodyTargetEquality]
  exact collapsed_not_instance_of_distinct

end FreshAliasPrincipalClosure
end TypePM
