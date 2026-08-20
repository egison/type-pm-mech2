import TypePM.Source.M4PatternCoherence

/-!
# Coherence for M4 all-results matching

The four generated children of `matchAll` are compared in source order.  The
pattern block is represented by `patternAsGenerated`; after sibling
certificates have been combined, a small semantic repackaging lemma inserts
the target equation and matcher obligation of `Generated.fromMatchAll`.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source
open InterfaceAliasDecomposition.AliasFreshness

private def matchAllItems (target : Generated) (pattern : GeneratedPattern)
    (matcher body : Generated) : GeneratedItems :=
  GeneratedItems.cons target <|
    GeneratedItems.cons (patternAsGenerated pattern) <|
      GeneratedItems.cons matcher <| GeneratedItems.singleton body

private def singletonItemsCertificate
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right) :
    SupportedItemsAlignmentCertificate start next
      (GeneratedItems.singleton left) (GeneratedItems.singleton right) :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := by simpa using certificate.leftScoped
    rightScoped := by simpa using certificate.rightScoped
    aligned := by
      intro before after
      let frame := GeneratedFrame.tupleItem before after .hole
      exact (EntailedGeneratedAlignment.addAll_frame_reposition
          certificate.leftAliases frame left).trans
        ((certificate.aligned.frame frame).trans
          (EntailedGeneratedAlignment.addAll_frame_reposition
            certificate.rightAliases frame right).symm) }

private def repackageCertificate
    {start next : Supply} {left right left' right' : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (leftScoped : ScopedBy left'.unificationVars certificate.leftAliases)
    (rightScoped : ScopedBy right'.unificationVars certificate.rightAliases)
    (aligned : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll certificate.leftAliases left')
      (FreshAliasSequence.addAll certificate.rightAliases right')) :
    SupportedEntailedAlignmentCertificate start next left' right' :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := leftScoped
    rightScoped := rightScoped
    aligned := aligned }

private def insertAt {α : Type} (item : α) : Nat → List α → List α
  | 0, items => item :: items
  | _ + 1, [] => [item]
  | index + 1, head :: tail => head :: insertAt item index tail

@[simp] private theorem insertAt_zero {α : Type} (item : α)
    (items : List α) : insertAt item 0 items = item :: items := rfl

@[simp] private theorem insertAt_succ_nil {α : Type} (item : α)
    (index : Nat) : insertAt item (index + 1) [] = [item] := rfl

@[simp] private theorem insertAt_succ_cons {α : Type} (item head : α)
    (index : Nat) (tail : List α) :
    insertAt item (index + 1) (head :: tail) =
      head :: insertAt item index tail := rfl

private theorem insertAt_append_length {α : Type} (before suffix : List α)
    (item : α) :
    insertAt item before.length (before ++ suffix) =
      before ++ item :: suffix := by
  induction before with
  | nil => rfl
  | cons head tail induction => simp [induction]

private theorem solves_insertAt_iff (substitution : Subst)
    (equations : List Equation) (index : Nat) (equation : Equation) :
    Solves substitution (insertAt equation index equations) ↔
      equation.Holds substitution ∧ Solves substitution equations := by
  induction equations generalizing index with
  | nil => cases index <;> simp [insertAt, solves_cons, Equation.Holds]
  | cons head tail induction =>
      cases index with
      | zero => simp [insertAt, solves_cons]
      | succ index =>
          simp only [insertAt, solves_cons, induction]
          exact and_left_comm

private theorem entailedPendingEq_weaken
    {weaker stronger : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq weaker left right)
    (entails : ∀ substitution, Solves substitution stronger →
      Solves substitution weaker) :
    EntailedPendingEq stronger left right := by
  induction aligned with
  | nil => exact .nil
  | cons head tail induction => exact .cons (head.weaken entails) induction

private theorem entailedPendingEq_length_eq
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right) :
    left.length = right.length := by
  induction aligned with
  | nil => rfl
  | cons _ _ induction => simp [induction]

private theorem entailedPendingEq_insertAt
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right)
    (index : Nat) {leftItem rightItem : CheckObligation}
    (itemAligned : EntailedObligationEq reference leftItem rightItem) :
    EntailedPendingEq reference
      (insertAt leftItem index left) (insertAt rightItem index right) := by
  induction aligned generalizing index with
  | nil =>
      cases index with
      | zero => exact .cons itemAligned .nil
      | succ _ => exact .cons itemAligned .nil
  | @cons leftHead rightHead leftTail rightTail head tail induction =>
      cases index with
      | zero =>
          simpa [insertAt] using
            (EntailedPendingEq.cons itemAligned (.cons head tail))
      | succ index =>
          simpa [insertAt] using
            (EntailedPendingEq.cons head (induction index))

private theorem encodedDual_components
    {left right : Dual} {substitution : Subst}
    (equality : (encodedPatternDual left).apply substitution =
      (encodedPatternDual right).apply substitution) :
    left.capability.apply substitution.cap =
        right.capability.apply substitution.cap ∧
      left.target.apply substitution = right.target.apply substitution := by
  simp only [encodedPatternDual, Ty.apply] at equality
  injection equality with domains targets
  injection domains with capabilities
  exact ⟨capabilities, targets⟩

private theorem matchAllItems_vars_iff
    (target : Generated) (pattern : GeneratedPattern)
    (matcher body : Generated) :
    ∀ candidate, candidate ∈
        (GeneratedItems.asTuple
          (matchAllItems target pattern matcher body)).unificationVars ↔
      candidate ∈
        (Generated.fromMatchAll target pattern matcher body).unificationVars := by
  intro candidate
  cases candidate <;>
    simp [matchAllItems, GeneratedItems.asTuple, GeneratedItems.cons,
      GeneratedItems.singleton, GeneratedItems.nil, patternAsGenerated,
      encodedPatternDual, Generated.fromMatchAll, Generated.unificationVars,
      Ty.unificationVars, TypePM.unificationVars,
      pendingUnificationVars, Ty.occursTyList, Ty.occursCapList,
      DataTypes.list, Equation.unificationVars,
      CheckObligation.unificationVars, Ty.occursCap, Ty.occursTy,
      or_assoc, or_left_comm, or_comm]

private theorem scopedBy_matchAll
    {target : Generated} {pattern : GeneratedPattern}
    {matcher body : Generated} {aliases : List FreshAliasSequence.Alias}
    (scope : ScopedBy
      (GeneratedItems.asTuple
        (matchAllItems target pattern matcher body)).unificationVars aliases) :
    ScopedBy
      (Generated.fromMatchAll target pattern matcher body).unificationVars
      aliases := by
  refine ⟨scope.1, ?_⟩
  intro alias member
  have endpoints := scope.2 alias member
  constructor
  · intro freshMember
    exact endpoints.1
      ((matchAllItems_vars_iff target pattern matcher body _).mpr freshMember)
  · exact (matchAllItems_vars_iff target pattern matcher body _).mp endpoints.2

private theorem matchAll_hard_as_insert
    (aliases : List FreshAliasSequence.Alias)
    (target : Generated) (pattern : GeneratedPattern)
    (matcher body : Generated) :
    (FreshAliasSequence.addAll aliases
      (Generated.fromMatchAll target pattern matcher body)).hard =
      insertAt (.ty pattern.dual.target target.target)
        (aliases.reverse.map
            InterfaceAliasDecomposition.EquationLists.aliasEquation ++
          target.hard).length
        (FreshAliasSequence.addAll aliases
          (GeneratedItems.asTuple
            (matchAllItems target pattern matcher body))).hard := by
  let before := aliases.reverse.map
    InterfaceAliasDecomposition.EquationLists.aliasEquation ++ target.hard
  let after := pattern.hard ++ matcher.hard ++ body.hard
  have outputShape :
      (FreshAliasSequence.addAll aliases
        (Generated.fromMatchAll target pattern matcher body)).hard =
        before ++ .ty pattern.dual.target target.target :: after := by
    simp [before, after, Generated.fromMatchAll,
      InterfaceAliasDecomposition.EquationLists.addAll_hard,
      InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
      List.append_assoc]
  have baseShape :
      (FreshAliasSequence.addAll aliases
        (GeneratedItems.asTuple
          (matchAllItems target pattern matcher body))).hard =
        before ++ after := by
    simp [before, after, matchAllItems, GeneratedItems.asTuple,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
      patternAsGenerated,
      InterfaceAliasDecomposition.EquationLists.addAll_hard,
      InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
      List.append_assoc]
  rw [outputShape, baseShape]
  exact (insertAt_append_length before after
    (.ty pattern.dual.target target.target)).symm

private theorem matchAll_pending_as_insert
    (target : Generated) (pattern : GeneratedPattern)
    (matcher body : Generated) :
    (Generated.fromMatchAll target pattern matcher body).pending =
      insertAt
        (⟨matcher.target,
          .slot pattern.dual.capability target.target⟩ : CheckObligation)
        (target.pending ++ pattern.pending ++ matcher.pending).length
        (GeneratedItems.asTuple
          (matchAllItems target pattern matcher body)).pending := by
  let before := target.pending ++ pattern.pending ++ matcher.pending
  let after := body.pending
  have outputShape :
      (Generated.fromMatchAll target pattern matcher body).pending =
        before ++
          (⟨matcher.target,
            .slot pattern.dual.capability target.target⟩ : CheckObligation) ::
            after := by
    simp [before, after, Generated.fromMatchAll, List.append_assoc]
  have baseShape :
      (GeneratedItems.asTuple
        (matchAllItems target pattern matcher body)).pending =
        before ++ after := by
    simp [before, after, matchAllItems, GeneratedItems.asTuple,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
      patternAsGenerated, List.append_assoc]
  rw [outputShape, baseShape]
  exact (insertAt_append_length before after
    (⟨matcher.target,
      .slot pattern.dual.capability target.target⟩ : CheckObligation)).symm

private theorem matchAll_component_equalities
    {leftTarget rightTarget : Generated}
    {leftPattern rightPattern : GeneratedPattern}
    {leftMatcher rightMatcher leftBody rightBody : Generated}
    {leftAliases rightAliases : List FreshAliasSequence.Alias}
    (aligned : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll leftAliases
        (GeneratedItems.asTuple
          (matchAllItems leftTarget leftPattern leftMatcher leftBody)))
      (FreshAliasSequence.addAll rightAliases
        (GeneratedItems.asTuple
          (matchAllItems rightTarget rightPattern rightMatcher rightBody))))
    (substitution : Subst)
    (leftSolved : Solves substitution
      (FreshAliasSequence.addAll leftAliases
        (GeneratedItems.asTuple
          (matchAllItems leftTarget leftPattern leftMatcher leftBody))).hard) :
    leftTarget.target.apply substitution =
        rightTarget.target.apply substitution ∧
      leftPattern.dual.capability.apply substitution.cap =
        rightPattern.dual.capability.apply substitution.cap ∧
      leftPattern.dual.target.apply substitution =
        rightPattern.dual.target.apply substitution ∧
      leftMatcher.target.apply substitution =
        rightMatcher.target.apply substitution ∧
      leftBody.target.apply substitution =
        rightBody.target.apply substitution := by
  have targetEquality := aligned.targetEntailed substitution leftSolved
  have listEquality : Ty.applyList substitution
      [leftTarget.target, encodedPatternDual leftPattern.dual,
        leftMatcher.target, leftBody.target] =
      Ty.applyList substitution
      [rightTarget.target, encodedPatternDual rightPattern.dual,
        rightMatcher.target, rightBody.target] := by
    simpa [FreshAliasSequence.addAll_target, matchAllItems,
      GeneratedItems.asTuple, GeneratedItems.cons, GeneratedItems.singleton,
      GeneratedItems.nil, patternAsGenerated, Ty.apply] using targetEquality
  have targetHead := List.cons.inj listEquality
  have patternHead := List.cons.inj targetHead.2
  have matcherHead := List.cons.inj patternHead.2
  have bodyHead := List.cons.inj matcherHead.2
  obtain ⟨capability, patternTarget⟩ :=
    encodedDual_components patternHead.1
  exact ⟨targetHead.1, capability, patternTarget,
    matcherHead.1, bodyHead.1⟩

private def supportedFromMatchAll
    {start next : Supply}
    {leftTarget rightTarget : Generated}
    {leftPattern rightPattern : GeneratedPattern}
    {leftMatcher rightMatcher leftBody rightBody : Generated}
    (targetPendingLength : leftTarget.pending.length =
      rightTarget.pending.length)
    (patternPendingLength : leftPattern.pending.length =
      rightPattern.pending.length)
    (matcherPendingLength : leftMatcher.pending.length =
      rightMatcher.pending.length)
    (certificate : SupportedItemsAlignmentCertificate start next
      (matchAllItems leftTarget leftPattern leftMatcher leftBody)
      (matchAllItems rightTarget rightPattern rightMatcher rightBody)) :
    SupportedEntailedAlignmentCertificate start next
      (Generated.fromMatchAll leftTarget leftPattern leftMatcher leftBody)
      (Generated.fromMatchAll rightTarget rightPattern rightMatcher rightBody) := by
  let base := certificate.itemsTuple
  apply repackageCertificate base
  · exact scopedBy_matchAll base.leftScoped
  · exact scopedBy_matchAll base.rightScoped
  · have aligned := base.aligned
    change EntailedGeneratedAlignment
      (FreshAliasSequence.addAll certificate.leftAliases
        (GeneratedItems.asTuple
          (matchAllItems leftTarget leftPattern leftMatcher leftBody)))
      (FreshAliasSequence.addAll certificate.rightAliases
        (GeneratedItems.asTuple
          (matchAllItems rightTarget rightPattern rightMatcher rightBody)))
      at aligned
    let leftOutput := Generated.fromMatchAll leftTarget leftPattern
      leftMatcher leftBody
    let rightOutput := Generated.fromMatchAll rightTarget rightPattern
      rightMatcher rightBody
    have leftHard := matchAll_hard_as_insert certificate.leftAliases
      leftTarget leftPattern leftMatcher leftBody
    have rightHard := matchAll_hard_as_insert certificate.rightAliases
      rightTarget rightPattern rightMatcher rightBody
    have leftEntailsBase : ∀ substitution,
        Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard →
        Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases
            (GeneratedItems.asTuple
              (matchAllItems leftTarget leftPattern leftMatcher leftBody))).hard := by
      intro substitution solved
      exact (solves_insertAt_iff substitution _ _ _).mp
        (Eq.mp (congrArg (Solves substitution) leftHard) solved) |>.2
    have components (substitution : Subst)
        (solved : Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard) :=
      matchAll_component_equalities aligned substitution
        (leftEntailsBase substitution solved)
    refine ⟨?_, ?_, ?_⟩
    · change HardEquivalent
        (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard
        (FreshAliasSequence.addAll certificate.rightAliases rightOutput).hard
      rw [leftHard, rightHard]
      intro substitution
      rw [solves_insertAt_iff, solves_insertAt_iff]
      constructor
      · rintro ⟨leftEquation, leftBase⟩
        have rightBase := (aligned.hardEquivalent substitution).mp leftBase
        have equalities := matchAll_component_equalities aligned substitution
          leftBase
        exact ⟨by
          simpa [Equation.Holds, equalities.1, equalities.2.2.1] using
            leftEquation, rightBase⟩
      · rintro ⟨rightEquation, rightBase⟩
        have leftBase := (aligned.hardEquivalent substitution).mpr rightBase
        have equalities := matchAll_component_equalities aligned substitution
          leftBase
        exact ⟨by
          simpa [Equation.Holds, equalities.1, equalities.2.2.1] using
            rightEquation, leftBase⟩
    · intro substitution solved
      have equalities := components substitution solved
      simp [FreshAliasSequence.addAll_target,
        Generated.fromMatchAll, DataTypes.list, Ty.apply, Ty.applyList,
        equalities.2.2.2.2]
    · have basePending := entailedPendingEq_weaken
        aligned.pendingAligned leftEntailsBase
      have checkAligned : EntailedObligationEq
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard
          ⟨leftMatcher.target,
            .slot leftPattern.dual.capability leftTarget.target⟩
          ⟨rightMatcher.target,
            .slot rightPattern.dual.capability rightTarget.target⟩ := by
        intro substitution solved
        have equalities := components substitution solved
        simp only [CheckObligation.apply, Ty.apply]
        rw [equalities.2.2.2.1, equalities.2.1, equalities.1]
      have inserted := entailedPendingEq_insertAt basePending
        (leftTarget.pending ++ leftPattern.pending ++
          leftMatcher.pending).length checkAligned
      have prefixLength :
          (leftTarget.pending ++ leftPattern.pending ++
              leftMatcher.pending).length =
            (rightTarget.pending ++ rightPattern.pending ++
              rightMatcher.pending).length := by
        simp [targetPendingLength, patternPendingLength, matcherPendingLength]
      rw [FreshAliasSequence.addAll_pending,
        FreshAliasSequence.addAll_pending]
      rw [matchAll_pending_as_insert, matchAll_pending_as_insert]
      rw [← prefixLength]
      simpa [base, SupportedItemsAlignmentCertificate.itemsTuple,
        FreshAliasSequence.addAll_pending, leftOutput, rightOutput] using inserted

private theorem freshIntervals_disjoint
    {firstStart middle finish : Supply}
    {firstHidden secondHidden : List UnificationVar}
    (firstFresh : VariablesFreshIn firstStart middle firstHidden)
    (secondFresh : VariablesFreshIn middle finish secondHidden) :
    ∀ candidate, candidate ∈ firstHidden → candidate ∉ secondHidden := by
  intro candidate firstMember secondMember
  have firstRange := firstFresh candidate firstMember
  have secondRange := secondFresh candidate secondMember
  cases candidate <;>
    simp only [UnificationVar.FreshIn] at firstRange secondRange <;> omega

private def itemsConsSequential
    {start middle finish : Supply}
    {leftHead rightHead : Generated} {leftTail rightTail : GeneratedItems}
    (head : SupportedEntailedAlignmentCertificate start middle
      leftHead rightHead)
    (tail : SupportedItemsAlignmentCertificate middle finish
      leftTail rightTail)
    (startToMiddle : start.Le middle)
    (middleToFinish : middle.Le finish)
    (leftTailAvoids : GeneratedItemsAvoid head.hidden leftTail)
    (rightTailAvoids : GeneratedItemsAvoid head.hidden rightTail)
    (leftHeadAvoids : GeneratedAvoids tail.hidden leftHead)
    (rightHeadAvoids : GeneratedAvoids tail.hidden rightHead) :
    SupportedItemsAlignmentCertificate start finish
      (GeneratedItems.cons leftHead leftTail)
      (GeneratedItems.cons rightHead rightTail) :=
  SupportedItemsAlignmentCertificate.itemsCons
    (head.rebase (head.hiddenFresh.widen
      (Supply.le_refl start) middleToFinish))
    (tail.rebase (tail.hiddenFresh.widen
      startToMiddle (Supply.le_refl finish)))
    leftTailAvoids rightTailAvoids leftHeadAvoids rightHeadAvoids
    (freshIntervals_disjoint head.hiddenFresh tail.hiddenFresh)

private theorem itemsConsSequential_hidden
    {start middle finish : Supply}
    {leftHead rightHead : Generated} {leftTail rightTail : GeneratedItems}
    (head : SupportedEntailedAlignmentCertificate start middle
      leftHead rightHead)
    (tail : SupportedItemsAlignmentCertificate middle finish
      leftTail rightTail)
    (startToMiddle : start.Le middle) (middleToFinish : middle.Le finish)
    (leftTailAvoids : GeneratedItemsAvoid head.hidden leftTail)
    (rightTailAvoids : GeneratedItemsAvoid head.hidden rightTail)
    (leftHeadAvoids : GeneratedAvoids tail.hidden leftHead)
    (rightHeadAvoids : GeneratedAvoids tail.hidden rightHead) :
    (itemsConsSequential head tail startToMiddle middleToFinish
      leftTailAvoids rightTailAvoids leftHeadAvoids rightHeadAvoids).hidden =
      head.hidden ++ tail.hidden := rfl

private theorem generatedAvoids_append
    {first second : List UnificationVar} {generated : Generated}
    (firstAvoids : GeneratedAvoids first generated)
    (secondAvoids : GeneratedAvoids second generated) :
    GeneratedAvoids (first ++ second) generated := by
  intro candidate member forbidden
  rcases List.mem_append.mp forbidden with first | second
  · exact firstAvoids candidate member first
  · exact secondAvoids candidate member second

private theorem generatedItemsAvoid_cons
    {hidden : List UnificationVar} {head : Generated}
    {tail : GeneratedItems}
    (headAvoids : GeneratedAvoids hidden head)
    (tailAvoids : GeneratedItemsAvoid hidden tail) :
    GeneratedItemsAvoid hidden (GeneratedItems.cons head tail) := by
  simpa using GeneratedItemsAvoid.append
    (GeneratedItemsAvoid.singleton headAvoids) tailAvoids

private theorem freshIn_to_belowFinish
    {start finish : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn start finish hidden) :
    VariablesBelowSupply hidden finish := by
  intro candidate member
  have range := fresh candidate member
  cases candidate <;>
    exact range.2

private theorem context_avoids_laterFresh
    {context : Context} {start phaseStart finish : Supply}
    (wellFormed : start.WellFormedFor context)
    (startToPhase : start.Le phaseStart)
    {hidden : List UnificationVar}
    (fresh : VariablesFreshIn phaseStart finish hidden) :
    VariablesAvoid hidden context.unificationVars := by
  have contextScoped : VariablesScopedBy context.initialSupply start start
      context.unificationVars := by
    intro candidate member
    exact Or.inl (Context.member_unificationVars_below_initialSupply member)
  exact VariablesScopedBy.avoids_later contextScoped fresh wellFormed
    (Supply.le_refl start) startToPhase

private theorem generatedAvoids_of_support
    {context : Context} {start finish : Supply} {generated : Generated}
    {forbidden : List UnificationVar}
    (contextAvoids : VariablesAvoid forbidden context.unificationVars)
    (below : VariablesBelowSupply forbidden start)
    (support : GeneratedSupportProvenance context start finish generated) :
    GeneratedAvoids forbidden generated := by
  intro candidate member forbiddenMember
  rcases support candidate member with contextMember | fresh
  · exact contextAvoids candidate contextMember forbiddenMember
  · have upper := below candidate forbiddenMember
    cases candidate <;>
      simp only [UnificationVar.FreshIn, UnificationVar.Below]
        at fresh upper <;> omega

private theorem extendedContext_avoids
    {context : Context} {bindings : List Ty}
    {forbidden : List UnificationVar}
    (contextAvoids : VariablesAvoid forbidden context.unificationVars)
    (bindingsAvoid : VariablesAvoid forbidden
      (Ty.unificationVarsList bindings)) :
    VariablesAvoid forbidden
      (Pattern.extendContext bindings context).unificationVars := by
  induction bindings with
  | nil => simpa [Pattern.extendContext] using contextAvoids
  | cons binding bindings induction =>
      intro candidate member forbiddenMember
      have origin := Context.mono_cons_unificationVars_origin
        (bindings.map Scheme.mono ++ context) binding member
      rcases origin with bindingMember | tailMember
      · exact bindingsAvoid candidate (by
          simpa [Ty.unificationVarsList] using Or.inl bindingMember)
          forbiddenMember
      · apply induction
        · intro item itemMember hidden
          exact bindingsAvoid item (by
            simpa [Ty.unificationVarsList] using Or.inr itemMember) hidden
        · exact tailMember
        · exact forbiddenMember

private theorem patternAsGenerated_support
    {context : Context} {start finish : Supply}
    {generated : GeneratedPattern}
    (support : GeneratedPatternSupportProvenance context start finish generated) :
    GeneratedSupportProvenance context start finish
      (patternAsGenerated generated) := by
  intro candidate member
  apply support candidate
  cases candidate with
  | cap index =>
      simp [patternAsGenerated, encodedPatternDual,
        Generated.unificationVars, GeneratedPattern.unificationVars,
        dualVariables, Ty.unificationVars] at member ⊢
      rcases member with capability | impossible | target | hard | pending
      · exact Or.inl capability
      · contradiction
      · exact Or.inr (Or.inl target)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hard)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr pending)))
  | ty index =>
      simp [patternAsGenerated, encodedPatternDual,
        Generated.unificationVars, GeneratedPattern.unificationVars,
        dualVariables, Ty.unificationVars] at member ⊢
      rcases member with impossible | target | hard | pending
      · contradiction
      · exact Or.inl target
      · exact Or.inr (Or.inr (Or.inl hard))
      · exact Or.inr (Or.inr (Or.inr pending))

private theorem support_avoids_laterFresh
    {context : Context} {outerStart start finish : Supply}
    (wellFormed : outerStart.WellFormedFor context)
    (outerToStart : outerStart.Le start)
    {observed hidden : List UnificationVar}
    (support : VariablesSupportProvenance context outerStart start observed)
    (fresh : VariablesFreshIn start finish hidden) :
    VariablesAvoid hidden observed := by
  have observedScoped : VariablesScopedBy context.initialSupply outerStart start
      observed := by
    intro candidate member
    rcases support candidate member with inherited | allocated
    · exact Or.inl (Context.member_unificationVars_below_initialSupply inherited)
    · exact Or.inr allocated
  exact VariablesScopedBy.avoids_later observedScoped fresh wellFormed outerToStart
    (Supply.le_refl start)

/-- Supported coherence for the `matchAll` constructor. -/
theorem matchAllSupportedFuelPair
    (target matcher : Expr) (pattern : Pattern) (body : Expr)
    (induction : ∀ smaller : Expr,
      smaller.complexity <
        (Expr.matchAll target matcher pattern body).complexity →
      FullM4FuelPairProperty smaller) :
    SupportedM4FuelPairProperty (.matchAll target matcher pattern body) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftDerivation
    rightDerivation
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftDerivation
  | succ leftFuel =>
    cases rightFuel with
    | zero => simp [ElaboratesFuel] at rightDerivation
    | succ rightFuel =>
      simp only [ElaboratesFuel] at leftDerivation rightDerivation
      cases leftDerivation with
      | @mk leftTarget afterTarget leftPattern afterPattern leftMatcher
          afterMatcher leftBody finish leftTargetDerivation
          leftPatternDerivation leftMatcherDerivation leftBodyDerivation =>
        cases rightDerivation with
        | @mk rightTarget rightAfterTarget rightPattern rightAfterPattern
            rightMatcher rightAfterMatcher rightBody rightFinish
            rightTargetDerivation rightPatternDerivation
            rightMatcherDerivation rightBodyDerivation =>
          have expressionPairBelow : SupportedM4ExpressionPairPropertyBelow
              signature leftFuel rightFuel
              (Expr.matchAll target matcher pattern body).complexity := by
            intro childContext expression childStart left right
              childLeftNext childRightNext complexity childWellFormed
              childLeft childRight
            exact FullM4FuelPairProperty.toSupported
              (induction expression complexity)
              signatureWellFormed childWellFormed childLeft childRight
          obtain ⟨targetResult⟩ :=
            FullM4FuelPairProperty.toSupported (induction target (by
              simp only [Expr.complexity_matchAll]
              omega)) signatureWellFormed wellFormed
              leftTargetDerivation rightTargetDerivation
          cases targetResult.next_eq
          have startToTarget := leftTargetDerivation.supply_le_next
          have targetWellFormed := wellFormed.mono startToTarget
          have emptyArguments : VariablesSupportProvenance context afterTarget
              afterTarget (dualUnificationVars []) := by
            intro candidate member
            simp [dualUnificationVars] at member
          have emptyBindings : VariablesSupportProvenance context afterTarget
              afterTarget (Ty.unificationVarsList []) := by
            intro candidate member
            simp [Ty.unificationVarsList] at member
          obtain ⟨patternResult⟩ :=
            PatternElaboratesUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPairBelow (by
                simp only [Expr.complexity_matchAll]
                omega) targetWellFormed emptyArguments emptyBindings
              (Supply.le_refl afterTarget) leftPatternDerivation
              rightPatternDerivation
          cases patternResult.next_eq
          rw [← patternResult.bindings_eq] at rightBodyDerivation
          have targetToPattern := leftPatternDerivation.supply_le_next
            (fun child => child.supply_le_next)
          obtain ⟨matcherResult⟩ :=
            FullM4FuelPairProperty.toSupported (induction matcher (by
              simp only [Expr.complexity_matchAll]
              omega)) signatureWellFormed
              (targetWellFormed.mono targetToPattern)
              leftMatcherDerivation rightMatcherDerivation
          cases matcherResult.next_eq
          have patternToMatcher := leftMatcherDerivation.supply_le_next
          have patternSupport := leftPatternDerivation.supportProvenance
            signatureWellFormed (fun child => child.supply_le_next)
            (fun child => child.supportProvenance signatureWellFormed)
            emptyArguments emptyBindings (Supply.le_refl afterTarget)
          have bindingsSupport : VariablesSupportProvenance context afterTarget
              afterPattern (Ty.unificationVarsList leftPattern.bindings) := by
            intro candidate member
            exact patternSupport candidate (by
              simp [GeneratedPattern.unificationVars, member])
          have bodyContextSupport :=
            (Pattern.extendContext_support bindingsSupport).extend_finish
              patternToMatcher
          have bodyWellFormed :=
            M4FreshRenaming.Supply.WellFormedFor.of_contextSupport
              targetWellFormed
              (Supply.le_trans targetToPattern patternToMatcher)
              bodyContextSupport
          obtain ⟨bodyResult⟩ :=
            FullM4FuelPairProperty.toSupported (induction body (by
              simp only [Expr.complexity_matchAll]
              omega)) signatureWellFormed bodyWellFormed
              leftBodyDerivation rightBodyDerivation
          cases bodyResult.next_eq
          have matcherToBody := leftBodyDerivation.supply_le_next

          have targetContextAvoid := context_avoids_laterFresh wellFormed
            (Supply.le_refl start) targetResult.certificate.hiddenFresh
          have targetBelow := freshIn_to_belowFinish
            targetResult.certificate.hiddenFresh
          have leftPatternAvoidTarget :=
            PatternElaboratesUsing.avoids_of_inputs signatureWellFormed
              targetContextAvoid
              (by simp [VariablesAvoid, dualUnificationVars])
              (by simp [VariablesAvoid, Ty.unificationVarsList]) targetBelow
              leftPatternDerivation
          have rightPatternAvoidTarget :=
            PatternElaboratesUsing.avoids_of_inputs signatureWellFormed
              targetContextAvoid
              (by simp [VariablesAvoid, dualUnificationVars])
              (by simp [VariablesAvoid, Ty.unificationVarsList]) targetBelow
              rightPatternDerivation

          have matcherSupportLeft := leftMatcherDerivation.supportProvenance
            signatureWellFormed
          have matcherSupportRight := rightMatcherDerivation.supportProvenance
            signatureWellFormed
          have bodySupportLeft := leftBodyDerivation.supportProvenance
            signatureWellFormed
          have bodySupportRight := rightBodyDerivation.supportProvenance
            signatureWellFormed
          have matcherContextAvoidTarget := targetContextAvoid
          have leftMatcherAvoidTarget := generatedAvoids_of_support
            matcherContextAvoidTarget
            (targetBelow.mono targetToPattern) matcherSupportLeft
          have rightMatcherAvoidTarget := generatedAvoids_of_support
            matcherContextAvoidTarget
            (targetBelow.mono targetToPattern) matcherSupportRight
          have leftBodyAvoidTarget := generatedAvoids_of_support
            (extendedContext_avoids targetContextAvoid
              leftPatternAvoidTarget.bindings)
            (targetBelow.mono
              (Supply.le_trans targetToPattern patternToMatcher))
            bodySupportLeft
          have rightBodyAvoidTarget := generatedAvoids_of_support
            (extendedContext_avoids targetContextAvoid
              leftPatternAvoidTarget.bindings)
            (targetBelow.mono
              (Supply.le_trans targetToPattern patternToMatcher))
            bodySupportRight

          have patternContextAvoid := context_avoids_laterFresh wellFormed
            startToTarget patternResult.certificate.hiddenFresh
          have patternBelow := freshIn_to_belowFinish
            patternResult.certificate.hiddenFresh
          have leftMatcherAvoidPattern := generatedAvoids_of_support
            patternContextAvoid patternBelow matcherSupportLeft
          have rightMatcherAvoidPattern := generatedAvoids_of_support
            patternContextAvoid patternBelow matcherSupportRight
          have leftBodyAvoidPattern := generatedAvoids_of_support
            (extendedContext_avoids patternContextAvoid
              patternResult.leftBindingsAvoid)
            (patternBelow.mono patternToMatcher) bodySupportLeft
          have rightBodyAvoidPattern := generatedAvoids_of_support
            (extendedContext_avoids patternContextAvoid
              patternResult.leftBindingsAvoid)
            (patternBelow.mono patternToMatcher) bodySupportRight

          have matcherContextAvoid := context_avoids_laterFresh wellFormed
            (Supply.le_trans startToTarget targetToPattern)
            matcherResult.certificate.hiddenFresh
          have bindingsAvoidMatcher := support_avoids_laterFresh
            targetWellFormed targetToPattern bindingsSupport
            matcherResult.certificate.hiddenFresh
          have matcherBelow := freshIn_to_belowFinish
            matcherResult.certificate.hiddenFresh
          have leftBodyAvoidMatcher := generatedAvoids_of_support
            (extendedContext_avoids matcherContextAvoid bindingsAvoidMatcher)
            matcherBelow bodySupportLeft
          have rightBodyAvoidMatcher := generatedAvoids_of_support
            (extendedContext_avoids matcherContextAvoid bindingsAvoidMatcher)
            matcherBelow bodySupportRight

          have targetSupportLeft := leftTargetDerivation.supportProvenance
            signatureWellFormed
          have targetSupportRight := rightTargetDerivation.supportProvenance
            signatureWellFormed
          have patternBlockSupportLeft := patternAsGenerated_support
            patternSupport
          have patternBlockSupportRight := patternAsGenerated_support
            (rightPatternDerivation.supportProvenance signatureWellFormed
              (fun child => child.supply_le_next)
              (fun child => child.supportProvenance signatureWellFormed)
              emptyArguments emptyBindings (Supply.le_refl afterTarget))
          have leftMatcherAvoidBodyHidden := support_avoids_laterFresh
            (targetWellFormed.mono targetToPattern) patternToMatcher
            matcherSupportLeft bodyResult.certificate.hiddenFresh
          have rightMatcherAvoidBodyHidden := support_avoids_laterFresh
            (targetWellFormed.mono targetToPattern) patternToMatcher
            matcherSupportRight bodyResult.certificate.hiddenFresh
          let matcherBody := itemsConsSequential matcherResult.certificate
            (singletonItemsCertificate bodyResult.certificate)
            patternToMatcher matcherToBody
            (GeneratedItemsAvoid.singleton leftBodyAvoidMatcher)
            (GeneratedItemsAvoid.singleton rightBodyAvoidMatcher)
            leftMatcherAvoidBodyHidden rightMatcherAvoidBodyHidden
          have matcherBodyHidden : matcherBody.hidden =
              matcherResult.certificate.hidden ++
                bodyResult.certificate.hidden := by
            dsimp [matcherBody]
            rw [itemsConsSequential_hidden]
            rfl

          have leftPatternAvoidMatcherHidden := support_avoids_laterFresh
            targetWellFormed targetToPattern patternBlockSupportLeft
            matcherResult.certificate.hiddenFresh
          have rightPatternAvoidMatcherHidden := support_avoids_laterFresh
            targetWellFormed targetToPattern patternBlockSupportRight
            matcherResult.certificate.hiddenFresh
          have leftPatternAvoidBodyHidden := support_avoids_laterFresh
            targetWellFormed targetToPattern patternBlockSupportLeft
            (bodyResult.certificate.hiddenFresh.widen patternToMatcher
              (Supply.le_refl leftNext))
          have rightPatternAvoidBodyHidden := support_avoids_laterFresh
            targetWellFormed targetToPattern patternBlockSupportRight
            (bodyResult.certificate.hiddenFresh.widen patternToMatcher
              (Supply.le_refl leftNext))
          let patternTail := itemsConsSequential patternResult.certificate
            matcherBody targetToPattern
            (Supply.le_trans patternToMatcher matcherToBody)
            (generatedItemsAvoid_cons leftMatcherAvoidPattern
              (GeneratedItemsAvoid.singleton leftBodyAvoidPattern))
            (generatedItemsAvoid_cons rightMatcherAvoidPattern
              (GeneratedItemsAvoid.singleton rightBodyAvoidPattern))
            (by
              rw [matcherBodyHidden]
              exact generatedAvoids_append leftPatternAvoidMatcherHidden
                leftPatternAvoidBodyHidden)
            (by
              rw [matcherBodyHidden]
              exact generatedAvoids_append rightPatternAvoidMatcherHidden
                rightPatternAvoidBodyHidden)
          have patternTailHidden : patternTail.hidden =
              patternResult.certificate.hidden ++
                (matcherResult.certificate.hidden ++
                  bodyResult.certificate.hidden) := by
            dsimp [patternTail]
            rw [itemsConsSequential_hidden, matcherBodyHidden]

          have leftTargetAvoidPatternHidden := support_avoids_laterFresh
            wellFormed startToTarget targetSupportLeft
            patternResult.certificate.hiddenFresh
          have rightTargetAvoidPatternHidden := support_avoids_laterFresh
            wellFormed startToTarget targetSupportRight
            patternResult.certificate.hiddenFresh
          have leftTargetAvoidMatcherHidden := support_avoids_laterFresh
            wellFormed startToTarget targetSupportLeft
            (matcherResult.certificate.hiddenFresh.widen targetToPattern
              (Supply.le_refl afterMatcher))
          have rightTargetAvoidMatcherHidden := support_avoids_laterFresh
            wellFormed startToTarget targetSupportRight
            (matcherResult.certificate.hiddenFresh.widen targetToPattern
              (Supply.le_refl afterMatcher))
          have leftTargetAvoidBodyHidden := support_avoids_laterFresh
            wellFormed startToTarget targetSupportLeft
            (bodyResult.certificate.hiddenFresh.widen
              (Supply.le_trans targetToPattern patternToMatcher)
              (Supply.le_refl leftNext))
          have rightTargetAvoidBodyHidden := support_avoids_laterFresh
            wellFormed startToTarget targetSupportRight
            (bodyResult.certificate.hiddenFresh.widen
              (Supply.le_trans targetToPattern patternToMatcher)
              (Supply.le_refl leftNext))
          let allItems := itemsConsSequential targetResult.certificate
            patternTail startToTarget
            (Supply.le_trans targetToPattern
              (Supply.le_trans patternToMatcher matcherToBody))
            (generatedItemsAvoid_cons leftPatternAvoidTarget.block
              (generatedItemsAvoid_cons leftMatcherAvoidTarget
                (GeneratedItemsAvoid.singleton leftBodyAvoidTarget)))
            (generatedItemsAvoid_cons rightPatternAvoidTarget.block
              (generatedItemsAvoid_cons rightMatcherAvoidTarget
                (GeneratedItemsAvoid.singleton rightBodyAvoidTarget)))
            (by
              rw [patternTailHidden]
              exact generatedAvoids_append leftTargetAvoidPatternHidden
                (generatedAvoids_append leftTargetAvoidMatcherHidden
                  leftTargetAvoidBodyHidden))
            (by
              rw [patternTailHidden]
              exact generatedAvoids_append rightTargetAvoidPatternHidden
                (generatedAvoids_append rightTargetAvoidMatcherHidden
                  rightTargetAvoidBodyHidden))
          have targetPendingLength : leftTarget.pending.length =
              rightTarget.pending.length := by
            simpa [FreshAliasSequence.addAll_pending] using
              entailedPendingEq_length_eq
                targetResult.certificate.aligned.pendingAligned
          have patternPendingLength : leftPattern.pending.length =
              rightPattern.pending.length := by
            simpa [FreshAliasSequence.addAll_pending, patternAsGenerated] using
              entailedPendingEq_length_eq
                patternResult.certificate.aligned.pendingAligned
          have matcherPendingLength : leftMatcher.pending.length =
              rightMatcher.pending.length := by
            simpa [FreshAliasSequence.addAll_pending] using
              entailedPendingEq_length_eq
                matcherResult.certificate.aligned.pendingAligned
          exact ⟨
            { next_eq := rfl
              certificate := supportedFromMatchAll targetPendingLength
                patternPendingLength matcherPendingLength allItems }⟩

/-- The architecture-level semantic step for `matchAll`. -/
theorem matchAllCoherenceStep : MatchAllCoherenceStep := by
  intro target matcher pattern body induction
  exact SupportedM4FuelPairProperty.toFull
    (matchAllSupportedFuelPair target matcher pattern body induction)

end TypePM.Source.M4.CompletenessArchitecture
