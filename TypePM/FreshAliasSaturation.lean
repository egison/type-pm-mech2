import TypePM.FreshAliasElimination
import TypePM.MGUEquivalence
import TypePM.ResolutionTransport

/-!
# Saturation transport across fresh variable aliases

This file strengthens hard-solvability projection to arbitrary delayed
checking obligations.  A body is fixed by an alias elimination when applying
the corresponding one-variable substitution changes neither its hard
equations nor its pending obligations.
-/

namespace TypePM

namespace FreshAliasSaturation

def PendingFixed (substitution : Subst)
    (pending : List CheckObligation) : Prop :=
  pending.map (CheckObligation.apply substitution) = pending

def TyInvariant (fresh existing : TyVar)
    (hard : List Equation) (pending : List CheckObligation) : Prop :=
  hard.map (Equation.apply (Subst.singleTy fresh (.var existing))) = hard ∧
    PendingFixed (Subst.singleTy fresh (.var existing)) pending

def CapInvariant (fresh existing : CapVar)
    (hard : List Equation) (pending : List CheckObligation) : Prop :=
  hard.map (Equation.apply (Subst.singleCap fresh (.var existing))) = hard ∧
    PendingFixed (Subst.singleCap fresh (.var existing)) pending

private theorem tyAlias_notOccurs
    {fresh existing : TyVar} (different : fresh ≠ existing) :
    (Ty.var existing).occursTy fresh = false := by
  have reverse : existing ≠ fresh := Ne.symm different
  simp [Ty.occursTy, reverse]

private theorem capAlias_notOccurs
    {fresh existing : CapVar} (different : fresh ≠ existing) :
    (Cap.var existing).occurs fresh = false := by
  have reverse : existing ≠ fresh := Ne.symm different
  simp [Cap.occurs, reverse]

theorem tyAlias_mostGeneral_lift
    {hard : List Equation} {solution : Subst}
    {fresh existing : TyVar} (different : fresh ≠ existing)
    (hardFixed :
      hard.map (Equation.apply (Subst.singleTy fresh (.var existing))) = hard)
    (principal : MostGeneral hard solution) :
    MostGeneral
      (.ty (.var fresh) (.var existing) :: hard)
      (Subst.compose solution (Subst.singleTy fresh (.var existing))) := by
  let alias := Subst.singleTy fresh (.var existing)
  let lifted := Subst.compose solution alias
  have aliasSolved :
      (Equation.ty (.var fresh) (.var existing)).Holds lifted := by
    simp [lifted, alias, Equation.Holds, Subst.compose,
      Subst.singleTy, Ty.apply]
  have normalizedSolved :
      Solves solution (hard.map (Equation.apply alias)) := by
    simpa [alias, hardFixed] using principal.1
  have hardSolved : Solves lifted hard :=
    (solves_map_apply solution alias hard).mp normalizedSolved
  refine ⟨(solves_cons lifted _ _).mpr ⟨aliasSolved, hardSolved⟩, ?_⟩
  intro specific specificSolved
  have specificHard : Solves specific hard :=
    (solves_cons specific _ _).mp specificSolved |>.2
  obtain ⟨later, factor⟩ := principal.2 specific specificHard
  let reduction : Reduces
      (Equation.ty (.var fresh) (.var existing) :: hard)
      alias (hard.map (Equation.apply alias)) :=
    .tyVarLeft (tyAlias_notOccurs different)
  have absorbed : Subst.compose specific alias = specific :=
    reduction.absorbed specificSolved
  refine ⟨later, ?_⟩
  calc
    specific = Subst.compose specific alias := absorbed.symm
    _ = Subst.compose (Subst.compose later solution) alias := by rw [factor]
    _ = Subst.compose later (Subst.compose solution alias) :=
      (Subst.compose_assoc later solution alias).symm

/-- Any MGU of an aliased hard list has a body MGU whose canonical alias lift
is another MGU of that same aliased list. -/
theorem tyAlias_mostGeneral_project
    {hard : List Equation} {aliasedSolution : Subst}
    {fresh existing : TyVar} (different : fresh ≠ existing)
    (hardFixed :
      hard.map (Equation.apply (Subst.singleTy fresh (.var existing))) = hard)
    (principal : MostGeneral
      (.ty (.var fresh) (.var existing) :: hard) aliasedSolution) :
    ∃ bodySolution,
      MostGeneral hard bodySolution ∧
        MostGeneral
          (.ty (.var fresh) (.var existing) :: hard)
          (Subst.compose bodySolution
            (Subst.singleTy fresh (.var existing))) := by
  have solvable : ∃ solution, Solves solution hard :=
    ⟨aliasedSolution, (solves_cons aliasedSolution _ _).mp principal.1 |>.2⟩
  obtain ⟨bodySolution, success⟩ := unify_complete solvable
  have bodyPrincipal := unify_mostGeneral success
  exact ⟨bodySolution, bodyPrincipal,
    tyAlias_mostGeneral_lift different hardFixed bodyPrincipal⟩

theorem capAlias_mostGeneral_lift
    {hard : List Equation} {solution : Subst}
    {fresh existing : CapVar} (different : fresh ≠ existing)
    (hardFixed :
      hard.map (Equation.apply (Subst.singleCap fresh (.var existing))) = hard)
    (principal : MostGeneral hard solution) :
    MostGeneral
      (.cap (.var fresh) (.var existing) :: hard)
      (Subst.compose solution (Subst.singleCap fresh (.var existing))) := by
  let alias := Subst.singleCap fresh (.var existing)
  let lifted := Subst.compose solution alias
  have aliasSolved :
      (Equation.cap (.var fresh) (.var existing)).Holds lifted := by
    simp [lifted, alias, Equation.Holds, Subst.compose,
      Subst.singleCap, Cap.apply]
  have normalizedSolved :
      Solves solution (hard.map (Equation.apply alias)) := by
    simpa [alias, hardFixed] using principal.1
  have hardSolved : Solves lifted hard :=
    (solves_map_apply solution alias hard).mp normalizedSolved
  refine ⟨(solves_cons lifted _ _).mpr ⟨aliasSolved, hardSolved⟩, ?_⟩
  intro specific specificSolved
  have specificHard : Solves specific hard :=
    (solves_cons specific _ _).mp specificSolved |>.2
  obtain ⟨later, factor⟩ := principal.2 specific specificHard
  let reduction : Reduces
      (Equation.cap (.var fresh) (.var existing) :: hard)
      alias (hard.map (Equation.apply alias)) :=
    .capVarLeft (capAlias_notOccurs different)
  have absorbed : Subst.compose specific alias = specific :=
    reduction.absorbed specificSolved
  refine ⟨later, ?_⟩
  calc
    specific = Subst.compose specific alias := absorbed.symm
    _ = Subst.compose (Subst.compose later solution) alias := by rw [factor]
    _ = Subst.compose later (Subst.compose solution alias) :=
      (Subst.compose_assoc later solution alias).symm

theorem capAlias_mostGeneral_project
    {hard : List Equation} {aliasedSolution : Subst}
    {fresh existing : CapVar} (different : fresh ≠ existing)
    (hardFixed :
      hard.map (Equation.apply (Subst.singleCap fresh (.var existing))) = hard)
    (principal : MostGeneral
      (.cap (.var fresh) (.var existing) :: hard) aliasedSolution) :
    ∃ bodySolution,
      MostGeneral hard bodySolution ∧
        MostGeneral
          (.cap (.var fresh) (.var existing) :: hard)
          (Subst.compose bodySolution
            (Subst.singleCap fresh (.var existing))) := by
  have solvable : ∃ solution, Solves solution hard :=
    ⟨aliasedSolution, (solves_cons aliasedSolution _ _).mp principal.1 |>.2⟩
  obtain ⟨bodySolution, success⟩ := unify_complete solvable
  have bodyPrincipal := unify_mostGeneral success
  exact ⟨bodySolution, bodyPrincipal,
    capAlias_mostGeneral_lift different hardFixed bodyPrincipal⟩

private theorem pendingFixed_cons
    {substitution : Subst} {head : CheckObligation}
    {tail : List CheckObligation}
    (fixed : PendingFixed substitution (head :: tail)) :
    CheckObligation.apply substitution head = head ∧
      PendingFixed substitution tail := by
  simp only [PendingFixed, List.map_cons, List.cons.injEq] at fixed
  exact fixed

private theorem obligation_apply_components
    {substitution : Subst} {obligation : CheckObligation}
    (fixed : CheckObligation.apply substitution obligation = obligation) :
    obligation.source.apply substitution = obligation.source ∧
      obligation.expected.apply substitution = obligation.expected := by
  cases obligation
  simp only [CheckObligation.apply, CheckObligation.mk.injEq] at fixed
  exact fixed

theorem promoteUnder_compose_of_pendingFixed
    (later alias : Subst) (pending : List CheckObligation)
    (fixed : PendingFixed alias pending) :
    promoteUnder (Subst.compose later alias) pending =
      promoteUnder later pending := by
  induction pending with
  | nil => rfl
  | cons obligation pending induction =>
      obtain ⟨headFixed, tailFixed⟩ := pendingFixed_cons fixed
      obtain ⟨sourceFixed, expectedFixed⟩ :=
        obligation_apply_components headFixed
      have sourceEquality :
          obligation.source.apply (Subst.compose later alias) =
            obligation.source.apply later := by
        rw [← Ty.apply_compose, sourceFixed]
      have expectedEquality :
          obligation.expected.apply (Subst.compose later alias) =
            obligation.expected.apply later := by
        rw [← Ty.apply_compose, expectedFixed]
      simp [promoteUnder, sourceEquality, expectedEquality,
        induction tailFixed]

theorem promoteUnder_preserves_pendingFixed
    (solution alias : Subst) (pending : List CheckObligation)
    (fixed : PendingFixed alias pending) :
    PendingFixed alias (promoteUnder solution pending).pending := by
  induction pending with
  | nil => simp [PendingFixed, promoteUnder]
  | cons obligation pending induction =>
      obtain ⟨headFixed, tailFixed⟩ := pendingFixed_cons fixed
      have tailResult := induction tailFixed
      by_cases possible :
          (obligation.source.apply solution).couldSpecial
            (obligation.expected.apply solution) = true
      · unfold PendingFixed at tailResult ⊢
        simp [promoteUnder, possible, headFixed, tailResult]
      · unfold PendingFixed at tailResult ⊢
        simp [promoteUnder, possible, tailResult]

theorem promoteUnder_equations_fixed
    (solution alias : Subst) (pending : List CheckObligation)
    (fixed : PendingFixed alias pending) :
    (promoteUnder solution pending).equations.map (Equation.apply alias) =
      (promoteUnder solution pending).equations := by
  induction pending with
  | nil => simp [promoteUnder]
  | cons obligation pending induction =>
      obtain ⟨headFixed, tailFixed⟩ := pendingFixed_cons fixed
      obtain ⟨sourceFixed, expectedFixed⟩ :=
        obligation_apply_components headFixed
      by_cases possible :
          (obligation.source.apply solution).couldSpecial
            (obligation.expected.apply solution) = true
      · simp [promoteUnder, possible, induction tailFixed]
      · simp [promoteUnder, possible, Equation.apply,
          sourceFixed, expectedFixed, induction tailFixed]

theorem PromotionClosure.liftTyAlias
    {hard pending finalHard finalPending}
    (closure : PromotionClosure hard pending finalHard finalPending)
    {fresh existing : TyVar} (different : fresh ≠ existing)
    (invariant : TyInvariant fresh existing hard pending) :
    PromotionClosure
      (.ty (.var fresh) (.var existing) :: hard) pending
      (.ty (.var fresh) (.var existing) :: finalHard) finalPending := by
  induction closure with
  | @refl hard pending => exact .refl
  | @step hard pending solution promoted finalHard finalPending
      principal promotion progress tail induction =>
      let alias := Subst.singleTy fresh (.var existing)
      let lifted := Subst.compose solution alias
      have liftedPrincipal :
          MostGeneral (.ty (.var fresh) (.var existing) :: hard) lifted :=
        tyAlias_mostGeneral_lift different invariant.1 principal
      have samePromotion : promoteUnder lifted pending = promoted := by
        calc
          promoteUnder lifted pending = promoteUnder solution pending :=
            promoteUnder_compose_of_pendingFixed solution alias pending
              invariant.2
          _ = promoted := promotion
      have promotedFixed :
          promoted.equations.map (Equation.apply alias) =
            promoted.equations := by
        rw [← promotion]
        exact promoteUnder_equations_fixed solution alias pending invariant.2
      have remainingFixed : PendingFixed alias promoted.pending := by
        rw [← promotion]
        exact promoteUnder_preserves_pendingFixed solution alias pending
          invariant.2
      have nextInvariant :
          TyInvariant fresh existing (hard ++ promoted.equations)
            promoted.pending := by
        constructor
        · simp [alias] at promotedFixed ⊢
          rw [invariant.1, promotedFixed]
        · exact remainingFixed
      have liftedTail := induction nextInvariant
      apply PromotionClosure.step liftedPrincipal samePromotion progress
      simpa using liftedTail

theorem PromotionClosure.tyInvariant_final
    {hard pending finalHard finalPending}
    (closure : PromotionClosure hard pending finalHard finalPending)
    {fresh existing : TyVar}
    (invariant : TyInvariant fresh existing hard pending) :
    TyInvariant fresh existing finalHard finalPending := by
  induction closure with
  | refl => exact invariant
  | @step hard pending solution promoted finalHard finalPending
      principal promotion progress tail induction =>
      let alias := Subst.singleTy fresh (.var existing)
      have promotedFixed :
          promoted.equations.map (Equation.apply alias) =
            promoted.equations := by
        rw [← promotion]
        exact promoteUnder_equations_fixed solution alias pending invariant.2
      have remainingFixed : PendingFixed alias promoted.pending := by
        rw [← promotion]
        exact promoteUnder_preserves_pendingFixed solution alias pending
          invariant.2
      apply induction
      constructor
      · rw [List.map_append, invariant.1, promotedFixed]
      · exact remainingFixed

theorem PromotionClosure.final_eq_append
    {hard pending finalHard finalPending}
    (closure : PromotionClosure hard pending finalHard finalPending) :
    ∃ extra, finalHard = hard ++ extra := by
  induction closure with
  | refl => exact ⟨[], by simp⟩
  | @step hard pending solution promoted finalHard finalPending
      principal promotion progress tail induction =>
      obtain ⟨extra, equality⟩ := induction
      refine ⟨promoted.equations ++ extra, ?_⟩
      rw [equality, List.append_assoc]

theorem PromotionClosure.projectTyAlias
    {hard pending finalHard finalPending}
    {fresh existing : TyVar} (different : fresh ≠ existing)
    (closure : PromotionClosure
      (.ty (.var fresh) (.var existing) :: hard) pending
      (.ty (.var fresh) (.var existing) :: finalHard) finalPending)
    (invariant : TyInvariant fresh existing hard pending) :
    PromotionClosure hard pending finalHard finalPending := by
  generalize initialEquality :
      (.ty (.var fresh) (.var existing) :: hard) = initial at closure
  generalize finalEquality :
      (.ty (.var fresh) (.var existing) :: finalHard) = final at closure
  induction closure generalizing hard finalHard with
  | @refl currentHard currentPending =>
      have listsEqual :
          (.ty (.var fresh) (.var existing) :: hard) =
            (.ty (.var fresh) (.var existing) :: finalHard) :=
        initialEquality.trans finalEquality.symm
      have tailsEqual : hard = finalHard :=
        by
          have := congrArg List.tail listsEqual
          simpa using this
      subst finalHard
      exact .refl
  | @step currentHard currentPending aliasedSolution promoted final currentFinalPending
      aliasedPrincipal promotion progress tail induction =>
      subst currentHard
      subst final
      have projected := tyAlias_mostGeneral_project different invariant.1
        aliasedPrincipal
      obtain ⟨bodySolution, bodyPrincipal, liftedPrincipal⟩ := projected
      let alias := Subst.singleTy fresh (.var existing)
      let lifted := Subst.compose bodySolution alias
      have arbitraryToLifted :
          promoteUnder aliasedSolution currentPending =
            promoteUnder lifted currentPending :=
        promoteUnder_eq_of_mostGeneral aliasedPrincipal liftedPrincipal
          currentPending
      have liftedToBody :
          promoteUnder lifted currentPending =
            promoteUnder bodySolution currentPending :=
        promoteUnder_compose_of_pendingFixed bodySolution alias currentPending
          invariant.2
      have bodyPromotion :
          promoteUnder bodySolution currentPending = promoted := by
        rw [← liftedToBody, ← arbitraryToLifted, promotion]
      have promotedFixed :
          promoted.equations.map (Equation.apply alias) =
            promoted.equations := by
        rw [← bodyPromotion]
        exact promoteUnder_equations_fixed bodySolution alias currentPending
          invariant.2
      have remainingFixed : PendingFixed alias promoted.pending := by
        rw [← bodyPromotion]
        exact promoteUnder_preserves_pendingFixed bodySolution alias currentPending
          invariant.2
      have nextInvariant :
          TyInvariant fresh existing (hard ++ promoted.equations)
            promoted.pending := by
        constructor
        · rw [List.map_append, invariant.1, promotedFixed]
        · exact remainingFixed
      have initialTail :
          (.ty (.var fresh) (.var existing) ::
              (hard ++ promoted.equations)) =
            ((.ty (.var fresh) (.var existing) :: hard) ++
              promoted.equations) := by rfl
      have projectedTail := induction
        (hard := hard ++ promoted.equations)
        (finalHard := finalHard)
        nextInvariant initialTail rfl
      exact .step bodyPrincipal bodyPromotion progress projectedTail

theorem Saturated.liftTyAlias
    {hard pending finalHard finalPending solution}
    (saturated : Saturated hard pending finalHard finalPending solution)
    {fresh existing : TyVar} (different : fresh ≠ existing)
    (invariant : TyInvariant fresh existing hard pending) :
    ∃ _finalInvariant : TyInvariant fresh existing finalHard finalPending,
      Saturated
        (.ty (.var fresh) (.var existing) :: hard) pending
        (.ty (.var fresh) (.var existing) :: finalHard) finalPending
        (Subst.compose solution
          (Subst.singleTy fresh (.var existing))) := by
  let alias := Subst.singleTy fresh (.var existing)
  have liftedClosure :=
    FreshAliasSaturation.PromotionClosure.liftTyAlias
      saturated.closure different invariant
  have finalInvariant : TyInvariant fresh existing finalHard finalPending :=
    FreshAliasSaturation.PromotionClosure.tyInvariant_final
      saturated.closure invariant
  refine ⟨finalInvariant,
    { closure := liftedClosure
      principal :=
        tyAlias_mostGeneral_lift different finalInvariant.1
          saturated.principal
      stable := ?_ }⟩
  rw [promoteUnder_compose_of_pendingFixed solution alias finalPending
    finalInvariant.2]
  exact saturated.stable

/-- Project saturation of a fresh ordinary-variable alias back to the body.
The returned body MGU is chosen canonically by the executable unifier; the
closure itself is independent of that representative. -/
theorem Saturated.projectTyAlias
    {hard pending finalHard finalPending aliasedSolution}
    {fresh existing : TyVar} (different : fresh ≠ existing)
    (saturated : Saturated
      (.ty (.var fresh) (.var existing) :: hard) pending
      (.ty (.var fresh) (.var existing) :: finalHard) finalPending
      aliasedSolution)
    (invariant : TyInvariant fresh existing hard pending) :
    ∃ bodySolution,
      Saturated hard pending finalHard finalPending bodySolution ∧
        TyInvariant fresh existing finalHard finalPending := by
  have bodyClosure :=
    FreshAliasSaturation.PromotionClosure.projectTyAlias different
      saturated.closure invariant
  have finalInvariant : TyInvariant fresh existing finalHard finalPending :=
    FreshAliasSaturation.PromotionClosure.tyInvariant_final
      bodyClosure invariant
  obtain ⟨bodySolution, bodyPrincipal, liftedPrincipal⟩ :=
    tyAlias_mostGeneral_project different finalInvariant.1
      saturated.principal
  let alias := Subst.singleTy fresh (.var existing)
  let lifted := Subst.compose bodySolution alias
  have samePromotion :
      promoteUnder aliasedSolution finalPending =
        promoteUnder lifted finalPending :=
    promoteUnder_eq_of_mostGeneral saturated.principal liftedPrincipal
      finalPending
  have liftedPromotion :
      promoteUnder lifted finalPending =
        promoteUnder bodySolution finalPending :=
    promoteUnder_compose_of_pendingFixed bodySolution alias finalPending
      finalInvariant.2
  refine ⟨bodySolution,
    { closure := bodyClosure
      principal := bodyPrincipal
      stable := ?_ },
    finalInvariant⟩
  rw [← liftedPromotion, ← samePromotion]
  exact saturated.stable

theorem residualEquations_compose_of_pendingFixed
    (solution alias : Subst) (pending : List CheckObligation)
    (fixed : PendingFixed alias pending) :
    residualEquations (Subst.compose solution alias) pending =
      residualEquations solution pending := by
  induction pending with
  | nil => rfl
  | cons obligation pending induction =>
      obtain ⟨headFixed, tailFixed⟩ := pendingFixed_cons fixed
      obtain ⟨sourceFixed, expectedFixed⟩ :=
        obligation_apply_components headFixed
      have sourceEquality :
          obligation.source.apply (Subst.compose solution alias) =
            obligation.source.apply solution := by
        rw [← Ty.apply_compose, sourceFixed]
      have expectedEquality :
          obligation.expected.apply (Subst.compose solution alias) =
            obligation.expected.apply solution := by
        rw [← Ty.apply_compose, expectedFixed]
      simp only [residualEquations]
      rw [show obligation.residualEquations
          (Subst.compose solution alias) =
            obligation.residualEquations solution by
        simp only [CheckObligation.residualEquations,
          CheckObligation.resolutionUnder]
        rw [sourceEquality, expectedEquality],
        induction tailFixed]

/-- One-way general-pending transport: a fresh ordinary alias may be added
to every acceptable alias-fixed body. -/
theorem blockAccepts_addTyAlias
    (body : Generated) (fresh existing : TyVar)
    (different : fresh ≠ existing)
    (invariant : TyInvariant fresh existing body.hard body.pending)
    (accepts : BlockAccepts body) :
    BlockAccepts
      (FreshAliasElimination.addTyAlias fresh existing body) := by
  rcases accepts with ⟨finalHard, finalPending, hardSolution,
    residualSolution, saturated, residualSolved⟩
  obtain ⟨finalInvariant, lifted⟩ :=
    FreshAliasSaturation.Saturated.liftTyAlias
      saturated different invariant
  refine ⟨.ty (.var fresh) (.var existing) :: finalHard,
    finalPending,
    Subst.compose hardSolution (Subst.singleTy fresh (.var existing)),
    residualSolution, lifted, ?_⟩
  rw [residualEquations_compose_of_pendingFixed hardSolution
    (Subst.singleTy fresh (.var existing)) finalPending finalInvariant.2]
  exact residualSolved

/-- General-pending elimination of one fresh ordinary-variable alias. -/
theorem blockAccepts_removeTyAlias
    (body : Generated) (fresh existing : TyVar)
    (different : fresh ≠ existing)
    (invariant : TyInvariant fresh existing body.hard body.pending)
    (accepts : BlockAccepts
      (FreshAliasElimination.addTyAlias fresh existing body)) :
    BlockAccepts body := by
  rcases accepts with ⟨aliasedFinalHard, finalPending, aliasedSolution,
    residualSolution, saturated, residualSolved⟩
  have initialHead :
      (FreshAliasElimination.addTyAlias fresh existing body).hard =
        .ty (.var fresh) (.var existing) :: body.hard := rfl
  rw [initialHead] at saturated
  have finalShape : ∃ finalHard,
      aliasedFinalHard =
        .ty (.var fresh) (.var existing) :: finalHard := by
    obtain ⟨extra, equality⟩ :=
      FreshAliasSaturation.PromotionClosure.final_eq_append
        saturated.closure
    exact ⟨body.hard ++ extra, by simpa using equality⟩
  obtain ⟨finalHard, rfl⟩ := finalShape
  obtain ⟨bodySolution, bodySaturated, finalInvariant⟩ :=
    FreshAliasSaturation.Saturated.projectTyAlias different saturated
      invariant
  obtain ⟨_liftedInvariant, liftedSaturated⟩ :=
    FreshAliasSaturation.Saturated.liftTyAlias bodySaturated different
      invariant
  let alias := Subst.singleTy fresh (.var existing)
  let lifted := Subst.compose bodySolution alias
  obtain ⟨aliasedToLifted, liftedToAliased⟩ :=
    saturated.principal.mutualFactors liftedSaturated.principal
  obtain ⟨post, _factor, transported⟩ :=
    ResolutionTransport.residualEquations_transport_of_mutualFactors
      liftedToAliased aliasedToLifted residualSolved
  have residualEquality :
      residualEquations lifted finalPending =
        residualEquations bodySolution finalPending :=
    residualEquations_compose_of_pendingFixed bodySolution alias finalPending
      finalInvariant.2
  refine ⟨finalHard, finalPending, bodySolution,
    Subst.compose residualSolution post, bodySaturated, ?_⟩
  rw [← residualEquality]
  exact transported

/-- Adding or removing one fresh ordinary-variable alias preserves block
acceptance even when delayed checking obligations remain. -/
theorem blockAccepts_addTyAlias_iff
    (body : Generated) (fresh existing : TyVar)
    (different : fresh ≠ existing)
    (invariant : TyInvariant fresh existing body.hard body.pending) :
    BlockAccepts (FreshAliasElimination.addTyAlias fresh existing body) ↔
      BlockAccepts body := by
  exact ⟨blockAccepts_removeTyAlias body fresh existing different invariant,
    blockAccepts_addTyAlias body fresh existing different invariant⟩

theorem PromotionClosure.liftCapAlias
    {hard pending finalHard finalPending}
    (closure : PromotionClosure hard pending finalHard finalPending)
    {fresh existing : CapVar} (different : fresh ≠ existing)
    (invariant : CapInvariant fresh existing hard pending) :
    PromotionClosure
      (.cap (.var fresh) (.var existing) :: hard) pending
      (.cap (.var fresh) (.var existing) :: finalHard) finalPending := by
  induction closure with
  | @refl hard pending => exact .refl
  | @step hard pending solution promoted finalHard finalPending
      principal promotion progress tail induction =>
      let alias := Subst.singleCap fresh (.var existing)
      let lifted := Subst.compose solution alias
      have liftedPrincipal :
          MostGeneral (.cap (.var fresh) (.var existing) :: hard) lifted :=
        capAlias_mostGeneral_lift different invariant.1 principal
      have samePromotion : promoteUnder lifted pending = promoted := by
        calc
          promoteUnder lifted pending = promoteUnder solution pending :=
            promoteUnder_compose_of_pendingFixed solution alias pending
              invariant.2
          _ = promoted := promotion
      have promotedFixed :
          promoted.equations.map (Equation.apply alias) =
            promoted.equations := by
        rw [← promotion]
        exact promoteUnder_equations_fixed solution alias pending invariant.2
      have remainingFixed : PendingFixed alias promoted.pending := by
        rw [← promotion]
        exact promoteUnder_preserves_pendingFixed solution alias pending
          invariant.2
      have nextInvariant :
          CapInvariant fresh existing (hard ++ promoted.equations)
            promoted.pending := by
        constructor
        · simp [alias] at promotedFixed ⊢
          rw [invariant.1, promotedFixed]
        · exact remainingFixed
      have liftedTail := induction nextInvariant
      apply PromotionClosure.step liftedPrincipal samePromotion progress
      simpa using liftedTail

theorem PromotionClosure.capInvariant_final
    {hard pending finalHard finalPending}
    (closure : PromotionClosure hard pending finalHard finalPending)
    {fresh existing : CapVar}
    (invariant : CapInvariant fresh existing hard pending) :
    CapInvariant fresh existing finalHard finalPending := by
  induction closure with
  | refl => exact invariant
  | @step hard pending solution promoted finalHard finalPending
      principal promotion progress tail induction =>
      let alias := Subst.singleCap fresh (.var existing)
      have promotedFixed :
          promoted.equations.map (Equation.apply alias) =
            promoted.equations := by
        rw [← promotion]
        exact promoteUnder_equations_fixed solution alias pending invariant.2
      have remainingFixed : PendingFixed alias promoted.pending := by
        rw [← promotion]
        exact promoteUnder_preserves_pendingFixed solution alias pending
          invariant.2
      apply induction
      constructor
      · rw [List.map_append, invariant.1, promotedFixed]
      · exact remainingFixed

theorem PromotionClosure.projectCapAlias
    {hard pending finalHard finalPending}
    {fresh existing : CapVar} (different : fresh ≠ existing)
    (closure : PromotionClosure
      (.cap (.var fresh) (.var existing) :: hard) pending
      (.cap (.var fresh) (.var existing) :: finalHard) finalPending)
    (invariant : CapInvariant fresh existing hard pending) :
    PromotionClosure hard pending finalHard finalPending := by
  generalize initialEquality :
      (.cap (.var fresh) (.var existing) :: hard) = initial at closure
  generalize finalEquality :
      (.cap (.var fresh) (.var existing) :: finalHard) = final at closure
  induction closure generalizing hard finalHard with
  | @refl currentHard currentPending =>
      have listsEqual :
          (.cap (.var fresh) (.var existing) :: hard) =
            (.cap (.var fresh) (.var existing) :: finalHard) :=
        initialEquality.trans finalEquality.symm
      have tailsEqual : hard = finalHard := by
        have := congrArg List.tail listsEqual
        simpa using this
      subst finalHard
      exact .refl
  | @step currentHard currentPending aliasedSolution promoted final currentFinalPending
      aliasedPrincipal promotion progress tail induction =>
      subst currentHard
      subst final
      obtain ⟨bodySolution, bodyPrincipal, liftedPrincipal⟩ :=
        capAlias_mostGeneral_project different invariant.1 aliasedPrincipal
      let alias := Subst.singleCap fresh (.var existing)
      let lifted := Subst.compose bodySolution alias
      have arbitraryToLifted :
          promoteUnder aliasedSolution currentPending =
            promoteUnder lifted currentPending :=
        promoteUnder_eq_of_mostGeneral aliasedPrincipal liftedPrincipal
          currentPending
      have liftedToBody :
          promoteUnder lifted currentPending =
            promoteUnder bodySolution currentPending :=
        promoteUnder_compose_of_pendingFixed bodySolution alias currentPending
          invariant.2
      have bodyPromotion :
          promoteUnder bodySolution currentPending = promoted := by
        rw [← liftedToBody, ← arbitraryToLifted, promotion]
      have promotedFixed :
          promoted.equations.map (Equation.apply alias) =
            promoted.equations := by
        rw [← bodyPromotion]
        exact promoteUnder_equations_fixed bodySolution alias currentPending
          invariant.2
      have remainingFixed : PendingFixed alias promoted.pending := by
        rw [← bodyPromotion]
        exact promoteUnder_preserves_pendingFixed bodySolution alias
          currentPending invariant.2
      have nextInvariant :
          CapInvariant fresh existing (hard ++ promoted.equations)
            promoted.pending := by
        constructor
        · rw [List.map_append, invariant.1, promotedFixed]
        · exact remainingFixed
      have initialTail :
          (.cap (.var fresh) (.var existing) ::
              (hard ++ promoted.equations)) =
            ((.cap (.var fresh) (.var existing) :: hard) ++
              promoted.equations) := by rfl
      have projectedTail := induction
        (hard := hard ++ promoted.equations)
        (finalHard := finalHard)
        nextInvariant initialTail rfl
      exact .step bodyPrincipal bodyPromotion progress projectedTail

theorem Saturated.liftCapAlias
    {hard pending finalHard finalPending solution}
    (saturated : Saturated hard pending finalHard finalPending solution)
    {fresh existing : CapVar} (different : fresh ≠ existing)
    (invariant : CapInvariant fresh existing hard pending) :
    ∃ _finalInvariant : CapInvariant fresh existing finalHard finalPending,
      Saturated
        (.cap (.var fresh) (.var existing) :: hard) pending
        (.cap (.var fresh) (.var existing) :: finalHard) finalPending
        (Subst.compose solution
          (Subst.singleCap fresh (.var existing))) := by
  let alias := Subst.singleCap fresh (.var existing)
  have liftedClosure :=
    FreshAliasSaturation.PromotionClosure.liftCapAlias
      saturated.closure different invariant
  have finalInvariant : CapInvariant fresh existing finalHard finalPending :=
    FreshAliasSaturation.PromotionClosure.capInvariant_final
      saturated.closure invariant
  refine ⟨finalInvariant,
    { closure := liftedClosure
      principal :=
        capAlias_mostGeneral_lift different finalInvariant.1
          saturated.principal
      stable := ?_ }⟩
  rw [promoteUnder_compose_of_pendingFixed solution alias finalPending
    finalInvariant.2]
  exact saturated.stable

theorem Saturated.projectCapAlias
    {hard pending finalHard finalPending aliasedSolution}
    {fresh existing : CapVar} (different : fresh ≠ existing)
    (saturated : Saturated
      (.cap (.var fresh) (.var existing) :: hard) pending
      (.cap (.var fresh) (.var existing) :: finalHard) finalPending
      aliasedSolution)
    (invariant : CapInvariant fresh existing hard pending) :
    ∃ bodySolution,
      Saturated hard pending finalHard finalPending bodySolution ∧
        CapInvariant fresh existing finalHard finalPending := by
  have bodyClosure :=
    FreshAliasSaturation.PromotionClosure.projectCapAlias different
      saturated.closure invariant
  have finalInvariant : CapInvariant fresh existing finalHard finalPending :=
    FreshAliasSaturation.PromotionClosure.capInvariant_final
      bodyClosure invariant
  obtain ⟨bodySolution, bodyPrincipal, liftedPrincipal⟩ :=
    capAlias_mostGeneral_project different finalInvariant.1
      saturated.principal
  let alias := Subst.singleCap fresh (.var existing)
  let lifted := Subst.compose bodySolution alias
  have samePromotion :
      promoteUnder aliasedSolution finalPending =
        promoteUnder lifted finalPending :=
    promoteUnder_eq_of_mostGeneral saturated.principal liftedPrincipal
      finalPending
  have liftedPromotion :
      promoteUnder lifted finalPending =
        promoteUnder bodySolution finalPending :=
    promoteUnder_compose_of_pendingFixed bodySolution alias finalPending
      finalInvariant.2
  refine ⟨bodySolution,
    { closure := bodyClosure
      principal := bodyPrincipal
      stable := ?_ },
    finalInvariant⟩
  rw [← liftedPromotion, ← samePromotion]
  exact saturated.stable

theorem blockAccepts_addCapAlias
    (body : Generated) (fresh existing : CapVar)
    (different : fresh ≠ existing)
    (invariant : CapInvariant fresh existing body.hard body.pending)
    (accepts : BlockAccepts body) :
    BlockAccepts
      (FreshAliasElimination.addCapAlias fresh existing body) := by
  rcases accepts with ⟨finalHard, finalPending, hardSolution,
    residualSolution, saturated, residualSolved⟩
  obtain ⟨finalInvariant, lifted⟩ :=
    FreshAliasSaturation.Saturated.liftCapAlias
      saturated different invariant
  refine ⟨.cap (.var fresh) (.var existing) :: finalHard,
    finalPending,
    Subst.compose hardSolution (Subst.singleCap fresh (.var existing)),
    residualSolution, lifted, ?_⟩
  rw [residualEquations_compose_of_pendingFixed hardSolution
    (Subst.singleCap fresh (.var existing)) finalPending finalInvariant.2]
  exact residualSolved

theorem blockAccepts_removeCapAlias
    (body : Generated) (fresh existing : CapVar)
    (different : fresh ≠ existing)
    (invariant : CapInvariant fresh existing body.hard body.pending)
    (accepts : BlockAccepts
      (FreshAliasElimination.addCapAlias fresh existing body)) :
    BlockAccepts body := by
  rcases accepts with ⟨aliasedFinalHard, finalPending, aliasedSolution,
    residualSolution, saturated, residualSolved⟩
  have initialHead :
      (FreshAliasElimination.addCapAlias fresh existing body).hard =
        .cap (.var fresh) (.var existing) :: body.hard := rfl
  rw [initialHead] at saturated
  have finalShape : ∃ finalHard,
      aliasedFinalHard =
        .cap (.var fresh) (.var existing) :: finalHard := by
    obtain ⟨extra, equality⟩ :=
      FreshAliasSaturation.PromotionClosure.final_eq_append
        saturated.closure
    exact ⟨body.hard ++ extra, by simpa using equality⟩
  obtain ⟨finalHard, rfl⟩ := finalShape
  obtain ⟨bodySolution, bodySaturated, finalInvariant⟩ :=
    FreshAliasSaturation.Saturated.projectCapAlias different saturated
      invariant
  obtain ⟨_liftedInvariant, liftedSaturated⟩ :=
    FreshAliasSaturation.Saturated.liftCapAlias bodySaturated different
      invariant
  let alias := Subst.singleCap fresh (.var existing)
  let lifted := Subst.compose bodySolution alias
  obtain ⟨aliasedToLifted, liftedToAliased⟩ :=
    saturated.principal.mutualFactors liftedSaturated.principal
  obtain ⟨post, _factor, transported⟩ :=
    ResolutionTransport.residualEquations_transport_of_mutualFactors
      liftedToAliased aliasedToLifted residualSolved
  have residualEquality :
      residualEquations lifted finalPending =
        residualEquations bodySolution finalPending :=
    residualEquations_compose_of_pendingFixed bodySolution alias finalPending
      finalInvariant.2
  refine ⟨finalHard, finalPending, bodySolution,
    Subst.compose residualSolution post, bodySaturated, ?_⟩
  rw [← residualEquality]
  exact transported

theorem blockAccepts_addCapAlias_iff
    (body : Generated) (fresh existing : CapVar)
    (different : fresh ≠ existing)
    (invariant : CapInvariant fresh existing body.hard body.pending) :
    BlockAccepts (FreshAliasElimination.addCapAlias fresh existing body) ↔
      BlockAccepts body := by
  exact ⟨blockAccepts_removeCapAlias body fresh existing different invariant,
    blockAccepts_addCapAlias body fresh existing different invariant⟩

end FreshAliasSaturation

end TypePM
