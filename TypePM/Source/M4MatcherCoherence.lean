import TypePM.Source.M4FreshRenamingTransport
import TypePM.Source.M4SupportedCoherence

/-!
# Coherence for M4 matcher literals

Matcher headers (`PPat` and `DPat`) are deterministic.  All variation comes
from the expression callbacks in next-matcher positions and arm bodies.  This
module compares those callbacks with the complexity induction hypothesis and
composes their supported certificates in source order.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source
open MatcherTyping
open M4FreshRenaming
open InterfaceAliasDecomposition.AliasFreshness

private def checksGenerated (checks : GeneratedChecks) : Generated :=
  ⟨.int, checks.hard, checks.pending⟩

private def retargetGenerated (target : Ty) (generated : Generated) : Generated :=
  ⟨target, generated.hard, generated.pending⟩

private theorem FreshAliasSequence.addAll_retargetGenerated
    (aliases : List FreshAliasSequence.Alias) (target : Ty)
    (generated : Generated) :
    FreshAliasSequence.addAll aliases (retargetGenerated target generated) =
      retargetGenerated target (FreshAliasSequence.addAll aliases generated) := by
  induction aliases generalizing generated with
  | nil => rfl
  | cons alias aliases induction =>
      rw [FreshAliasSequence.addAll, FreshAliasSequence.addAll]
      have one : alias.add (retargetGenerated target generated) =
          retargetGenerated target (alias.add generated) := by
        cases alias <;> cases generated <;>
          rfl
      rw [one]
      exact induction (alias.add generated)

private theorem scopedBy_retargetGenerated
    {generated : Generated} {aliases : List FreshAliasSequence.Alias}
    {hidden : List UnificationVar} {target : Ty}
    (scopeProof : ScopedBy generated.unificationVars aliases)
    (oldTargetEmpty : generated.target.unificationVars = [])
    (aliasFresh : ∀ alias, alias ∈ aliases → freshVariable alias ∈ hidden)
    (targetAvoids : TypeAvoids hidden target) :
    ScopedBy (retargetGenerated target generated).unificationVars aliases := by
  refine ⟨scopeProof.1, ?_⟩
  intro alias member
  have endpoints := scopeProof.2 alias member
  have hiddenMember := aliasFresh alias member
  constructor
  · intro observed
    simp only [retargetGenerated, Generated.unificationVars,
      List.mem_append] at observed
    rcases observed with (targetMember | hardMember) | pendingMember
    · exact targetAvoids _ targetMember hiddenMember
    · exact endpoints.1 (by
        simp [Generated.unificationVars, oldTargetEmpty, hardMember])
    · exact endpoints.1 (by
        simp [Generated.unificationVars, oldTargetEmpty, pendingMember])
  · have existing := endpoints.2
    simp only [Generated.unificationVars, oldTargetEmpty, List.not_mem_nil,
      false_or, List.mem_append] at existing
    simp only [retargetGenerated, Generated.unificationVars, List.mem_append]
    rcases existing with hardMember | pendingMember
    · exact Or.inl (Or.inr hardMember)
    · exact Or.inr pendingMember

private def supportedCertificateRetarget
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (target : Ty)
    (leftTargetEmpty : left.target.unificationVars = [])
    (rightTargetEmpty : right.target.unificationVars = [])
    (targetAvoids : TypeAvoids certificate.hidden target) :
    SupportedEntailedAlignmentCertificate start next
      (retargetGenerated target left) (retargetGenerated target right) :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := scopedBy_retargetGenerated certificate.leftScoped
      leftTargetEmpty certificate.leftAliasFresh targetAvoids
    rightScoped := scopedBy_retargetGenerated certificate.rightScoped
      rightTargetEmpty certificate.rightAliasFresh targetAvoids
    aligned := by
      rw [FreshAliasSequence.addAll_retargetGenerated,
        FreshAliasSequence.addAll_retargetGenerated]
      exact
        { hardEquivalent := certificate.aligned.hardEquivalent
          targetEntailed := EntailedTypeEq.refl _ target
          pendingAligned := certificate.aligned.pendingAligned } }

private def supportedCertificateTransport
    {start next : Supply} {left right left' right' : Generated}
    (leftEq : left = left') (rightEq : right = right')
    (certificate : SupportedEntailedAlignmentCertificate start next left right) :
    SupportedEntailedAlignmentCertificate start next left' right' := by
  subst left'
  subst right'
  exact certificate

@[simp] private theorem supportedCertificateTransport_hidden
    {start next : Supply} {left right left' right' : Generated}
    (leftEq : left = left') (rightEq : right = right')
    (certificate : SupportedEntailedAlignmentCertificate start next left right) :
    (supportedCertificateTransport leftEq rightEq certificate).hidden =
      certificate.hidden := by
  subst left'
  subst right'
  rfl

private def supportedCertificateSingletonItems
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

private def appendChecksCertificate
    {start next : Supply} {leftFirst rightFirst leftSecond rightSecond : GeneratedChecks}
    (first : SupportedEntailedAlignmentCertificate start next
      (checksGenerated leftFirst) (checksGenerated rightFirst))
    (second : SupportedEntailedAlignmentCertificate start next
      (checksGenerated leftSecond) (checksGenerated rightSecond))
    (leftSecondAvoids : GeneratedAvoids first.hidden
      (checksGenerated leftSecond))
    (rightSecondAvoids : GeneratedAvoids first.hidden
      (checksGenerated rightSecond))
    (leftFirstAvoids : GeneratedAvoids second.hidden
      (checksGenerated leftFirst))
    (rightFirstAvoids : GeneratedAvoids second.hidden
      (checksGenerated rightFirst))
    (hiddenDisjoint : ∀ candidate, candidate ∈ first.hidden →
      candidate ∉ second.hidden) :
    SupportedEntailedAlignmentCertificate start next
      (checksGenerated (leftFirst.append leftSecond))
      (checksGenerated (rightFirst.append rightSecond)) := by
  let combinedItems := SupportedItemsAlignmentCertificate.itemsCons first
    (supportedCertificateSingletonItems second)
    (GeneratedItemsAvoid.singleton leftSecondAvoids)
    (GeneratedItemsAvoid.singleton rightSecondAvoids)
    leftFirstAvoids rightFirstAvoids hiddenDisjoint
  let combined := combinedItems.itemsTuple
  have retargeted := supportedCertificateRetarget combined .int
    (by simp [GeneratedItems.asTuple,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
      checksGenerated, Ty.unificationVars, Ty.unificationVarsList])
    (by simp [GeneratedItems.asTuple,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
      checksGenerated, Ty.unificationVars, Ty.unificationVarsList])
    (by simp [TypeAvoids, VariablesAvoid, Ty.unificationVars])
  exact
    { hidden := retargeted.hidden
      hiddenFresh := retargeted.hiddenFresh
      leftAliases := retargeted.leftAliases
      rightAliases := retargeted.rightAliases
      leftAliasFresh := retargeted.leftAliasFresh
      rightAliasFresh := retargeted.rightAliasFresh
      leftScoped := by
        simpa [combined, combinedItems, checksGenerated,
          GeneratedChecks.append, retargetGenerated, GeneratedItems.asTuple,
          GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil]
          using retargeted.leftScoped
      rightScoped := by
        simpa [combined, combinedItems, checksGenerated,
          GeneratedChecks.append, retargetGenerated, GeneratedItems.asTuple,
          GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil]
          using retargeted.rightScoped
      aligned := by
        simpa [combined, combinedItems, checksGenerated,
          GeneratedChecks.append, retargetGenerated, GeneratedItems.asTuple,
          GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil]
          using retargeted.aligned }

private theorem entailedPendingAppendChecked
    {reference : List Equation} {left right : List CheckObligation}
    {leftTarget rightTarget expected : Ty}
    (pending : EntailedPendingEq reference left right)
    (target : EntailedTypeEq reference leftTarget rightTarget) :
    EntailedPendingEq reference
      (left ++ [⟨leftTarget, expected⟩])
      (right ++ [⟨rightTarget, expected⟩]) := by
  induction pending with
  | nil =>
      exact .cons (by
        intro substitution solved
        simp only [CheckObligation.apply]
        rw [target substitution solved]) .nil
  | cons head tail induction => exact .cons head induction

private theorem entailedGeneratedChecked
    {left right : Generated} (expected : Ty)
    (aligned : EntailedGeneratedAlignment left right) :
    EntailedGeneratedAlignment
      (checksGenerated (GeneratedChecks.checked left expected))
      (checksGenerated (GeneratedChecks.checked right expected)) :=
  { hardEquivalent := aligned.hardEquivalent
    targetEntailed := EntailedTypeEq.refl _ .int
    pendingAligned := by
      simpa [checksGenerated, GeneratedChecks.checked] using
        entailedPendingAppendChecked aligned.pendingAligned
          aligned.targetEntailed }

private theorem FreshAliasSequence.addAll_checked
    (aliases : List FreshAliasSequence.Alias) (generated : Generated)
    (expected : Ty) :
    FreshAliasSequence.addAll aliases
        (checksGenerated (GeneratedChecks.checked generated expected)) =
      checksGenerated (GeneratedChecks.checked
        (FreshAliasSequence.addAll aliases generated) expected) := by
  induction aliases generalizing generated with
  | nil => rfl
  | cons alias aliases induction =>
      rw [FreshAliasSequence.addAll, FreshAliasSequence.addAll]
      have one : alias.add
            (checksGenerated (GeneratedChecks.checked generated expected)) =
          checksGenerated
            (GeneratedChecks.checked (alias.add generated) expected) := by
        cases alias <;> cases generated <;>
          rfl
      rw [one]
      exact induction (alias.add generated)

private theorem scopedBy_checked
    {generated : Generated} {aliases : List FreshAliasSequence.Alias}
    {hidden : List UnificationVar} {expected : Ty}
    (scopeProof : ScopedBy generated.unificationVars aliases)
    (aliasFresh : ∀ alias, alias ∈ aliases → freshVariable alias ∈ hidden)
    (expectedAvoids : TypeAvoids hidden expected) :
    ScopedBy
      (checksGenerated (GeneratedChecks.checked generated expected)).unificationVars
      aliases := by
  refine ⟨scopeProof.1, ?_⟩
  intro alias member
  have endpoints := scopeProof.2 alias member
  have hiddenMember := aliasFresh alias member
  constructor
  · intro observed
    by_cases generatedMember : freshVariable alias ∈ generated.unificationVars
    · exact endpoints.1 generatedMember
    · have expectedMember : freshVariable alias ∈ expected.unificationVars := by
        simp only [checksGenerated, GeneratedChecks.checked,
          Generated.unificationVars,
          pendingUnificationVars_append, pendingUnificationVars,
          CheckObligation.unificationVars, Ty.unificationVars,
          List.mem_append] at observed
        rcases observed with hardMember | pendingMember | sourceMember |
            expectedMember | impossible
        · rcases hardMember with impossible | hardMember
          · simp at impossible
          · exact (generatedMember (by
              simp [Generated.unificationVars, hardMember])).elim
        · exact (generatedMember (by
            simp [Generated.unificationVars, pendingMember])).elim
        · rcases sourceMember with sourceMember | expectedMember
          · exact (generatedMember (by
              simp [Generated.unificationVars, sourceMember])).elim
          · exact expectedMember
      exact expectedAvoids _ expectedMember hiddenMember
  · have existing := endpoints.2
    simp only [Generated.unificationVars, List.mem_append] at existing
    simp only [checksGenerated, GeneratedChecks.checked,
      Generated.unificationVars,
      pendingUnificationVars_append, pendingUnificationVars,
      CheckObligation.unificationVars, Ty.unificationVars,
      List.mem_append]
    rcases existing with (targetMember | hardMember) | pendingMember
    · exact Or.inr (Or.inr (Or.inl (Or.inl targetMember)))
    · exact Or.inl (Or.inr hardMember)
    · exact Or.inr (Or.inl pendingMember)

private def supportedCertificateChecked
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (expected : Ty) (expectedAvoids : TypeAvoids certificate.hidden expected) :
    SupportedEntailedAlignmentCertificate start next
      (checksGenerated (GeneratedChecks.checked left expected))
      (checksGenerated (GeneratedChecks.checked right expected)) :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := scopedBy_checked certificate.leftScoped
      certificate.leftAliasFresh expectedAvoids
    rightScoped := scopedBy_checked certificate.rightScoped
      certificate.rightAliasFresh expectedAvoids
    aligned := by
      rw [FreshAliasSequence.addAll_checked,
        FreshAliasSequence.addAll_checked]
      exact entailedGeneratedChecked expected certificate.aligned }

mutual

theorem ppat_deterministic
    {signature : FrozenSignature} {pattern : PPat} {target : Ty}
    {capability : Option Cap} {start : Supply}
    {left right : GeneratedPPat} {leftNext rightNext : Supply}
    (leftDerivation : PPatElaborates signature pattern target capability start
      left leftNext)
    (rightDerivation : PPatElaborates signature pattern target capability start
      right rightNext) : left = right ∧ leftNext = rightNext := by
  cases leftDerivation with
  | hole => cases rightDerivation; exact ⟨rfl, rfl⟩
  | wild => cases rightDerivation; exact ⟨rfl, rfl⟩
  | capture => cases rightDerivation; exact ⟨rfl, rfl⟩
  | @ctor constructor fields target capability start leftScheme leftFields
      leftNext leftLookup leftArity leftFieldsDerivation =>
      cases rightDerivation with
      | @ctor _ _ _ _ _ rightScheme rightFields rightNext rightLookup
          rightArity rightFieldsDerivation =>
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          obtain ⟨rfl, rfl⟩ := ppats_deterministic leftFieldsDerivation
            rightFieldsDerivation
          exact ⟨rfl, rfl⟩
termination_by PPat.typingSize pattern
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [PPat.typingSize]
  all_goals omega

theorem ppats_deterministic
    {signature : FrozenSignature} {patterns : List PPat} {expected : List Dual}
    {start : Supply} {left right : GeneratedPPats}
    {leftNext rightNext : Supply}
    (leftDerivation : PPatsElaborate signature patterns expected start left leftNext)
    (rightDerivation : PPatsElaborate signature patterns expected start right rightNext) :
    left = right ∧ leftNext = rightNext := by
  cases leftDerivation with
  | nil => cases rightDerivation; exact ⟨rfl, rfl⟩
  | @cons pattern patterns expected expecteds start leftHead leftAfter leftTail
      leftNext leftHeadDerivation leftTailDerivation =>
      cases rightDerivation with
      | @cons _ _ _ _ _ rightHead rightAfter rightTail rightNext
          rightHeadDerivation rightTailDerivation =>
          obtain ⟨rfl, rfl⟩ := ppat_deterministic leftHeadDerivation
            rightHeadDerivation
          obtain ⟨rfl, rfl⟩ := ppats_deterministic leftTailDerivation
            rightTailDerivation
          exact ⟨rfl, rfl⟩
termination_by PPat.listTypingSize patterns
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [PPat.listTypingSize]
  all_goals omega

end

mutual

theorem dpat_deterministic
    {signature : FrozenSignature} {pattern : DPat} {expected : Ty}
    {start : Supply} {left right : GeneratedDPat}
    {leftNext rightNext : Supply}
    (leftDerivation : DPatElaborates signature pattern expected start left leftNext)
    (rightDerivation : DPatElaborates signature pattern expected start right rightNext) :
    left = right ∧ leftNext = rightNext := by
  cases leftDerivation with
  | var => cases rightDerivation; exact ⟨rfl, rfl⟩
  | wild => cases rightDerivation; exact ⟨rfl, rfl⟩
  | @ctor constructor fields expected start leftScheme leftTypes leftResult
      leftFields leftNext leftLookup leftArity leftPeel leftFieldsDerivation =>
      cases rightDerivation with
      | @ctor _ _ _ _ rightScheme rightTypes rightResult rightFields rightNext
          rightLookup rightArity rightPeel rightFieldsDerivation =>
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          have peeledEquality := Option.some.inj (leftPeel.symm.trans rightPeel)
          cases peeledEquality
          obtain ⟨rfl, rfl⟩ := dpats_deterministic leftFieldsDerivation
            rightFieldsDerivation
          exact ⟨rfl, rfl⟩
  | @tuple items expected start leftTypes leftItems leftNext leftTypesEquality
      leftItemsDerivation =>
      cases rightDerivation with
      | @tuple _ _ _ rightTypes rightItems rightNext rightTypesEquality
          rightItemsDerivation =>
          rw [leftTypesEquality] at leftItemsDerivation ⊢
          rw [rightTypesEquality] at rightItemsDerivation ⊢
          obtain ⟨rfl, rfl⟩ := dpats_deterministic leftItemsDerivation
            rightItemsDerivation
          exact ⟨rfl, rfl⟩
termination_by DPat.typingSize pattern
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [DPat.typingSize]
  all_goals omega

theorem dpats_deterministic
    {signature : FrozenSignature} {patterns : List DPat} {expected : List Ty}
    {start : Supply} {left right : GeneratedDPats}
    {leftNext rightNext : Supply}
    (leftDerivation : DPatsElaborate signature patterns expected start left leftNext)
    (rightDerivation : DPatsElaborate signature patterns expected start right rightNext) :
    left = right ∧ leftNext = rightNext := by
  cases leftDerivation with
  | nil => cases rightDerivation; exact ⟨rfl, rfl⟩
  | @cons pattern patterns expected expecteds start leftHead leftAfter leftTail
      leftNext leftHeadDerivation leftTailDerivation =>
      cases rightDerivation with
      | @cons _ _ _ _ _ rightHead rightAfter rightTail rightNext
          rightHeadDerivation rightTailDerivation =>
          obtain ⟨rfl, rfl⟩ := dpat_deterministic leftHeadDerivation
            rightHeadDerivation
          obtain ⟨rfl, rfl⟩ := dpats_deterministic leftTailDerivation
            rightTailDerivation
          exact ⟨rfl, rfl⟩
termination_by DPat.listTypingSize patterns
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [DPat.listTypingSize]
  all_goals omega

end

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
    simp only [UnificationVar.FreshIn] at firstRange secondRange <;>
    omega

private structure SupportedChecksPair
    (start leftNext rightNext : Supply)
    (left right : GeneratedChecks) where
  next_eq : leftNext = rightNext
  certificate : SupportedEntailedAlignmentCertificate start leftNext
    (checksGenerated left) (checksGenerated right)

private def appendSequentialChecks
    {start middle finish : Supply}
    {leftFirst rightFirst leftSecond rightSecond : GeneratedChecks}
    (first : SupportedEntailedAlignmentCertificate start middle
      (checksGenerated leftFirst) (checksGenerated rightFirst))
    (second : SupportedEntailedAlignmentCertificate middle finish
      (checksGenerated leftSecond) (checksGenerated rightSecond))
    (startToMiddle : start.Le middle)
    (middleToFinish : middle.Le finish)
    (leftSecondAvoids : GeneratedAvoids first.hidden
      (checksGenerated leftSecond))
    (rightSecondAvoids : GeneratedAvoids first.hidden
      (checksGenerated rightSecond))
    (leftFirstAvoids : GeneratedAvoids second.hidden
      (checksGenerated leftFirst))
    (rightFirstAvoids : GeneratedAvoids second.hidden
      (checksGenerated rightFirst)) :
    SupportedEntailedAlignmentCertificate start finish
      (checksGenerated (leftFirst.append leftSecond))
      (checksGenerated (rightFirst.append rightSecond)) :=
  appendChecksCertificate
    (first.rebase (first.hiddenFresh.widen (Supply.le_refl start)
      middleToFinish))
    (second.rebase (second.hiddenFresh.widen
      startToMiddle
      (Supply.le_refl finish)))
    leftSecondAvoids rightSecondAvoids leftFirstAvoids rightFirstAvoids
    (freshIntervals_disjoint first.hiddenFresh second.hiddenFresh)

private theorem checksScopedByInitialSupply
    {context : Context} {start finish : Supply} {checks : GeneratedChecks}
    (support : GeneratedChecksSupportProvenance context start finish checks) :
    VariablesScopedBy context.initialSupply start finish
      (checksGenerated checks).unificationVars := by
  intro candidate member
  have checkMember : candidate ∈ checks.unificationVars := by
    simpa [checksGenerated, Generated.unificationVars,
      GeneratedChecks.unificationVars, Ty.unificationVars] using member
  rcases support candidate checkMember with inherited | fresh
  · exact Or.inl (Context.member_unificationVars_below_initialSupply inherited)
  · exact Or.inr fresh

private theorem typeAvoids_of_support_before
    {context : Context} {outerStart start finish : Supply} {target : Ty}
    (wellFormed : outerStart.WellFormedFor context)
    (outerToStart : outerStart.Le start)
    (support : VariablesSupportProvenance context outerStart start
      target.unificationVars)
    {hidden : List UnificationVar}
    (fresh : VariablesFreshIn start finish hidden) :
    TypeAvoids hidden target := by
  intro candidate observed hiddenMember
  have observedScoped : VariablesScopedBy context.initialSupply outerStart start
      target.unificationVars := by
    intro candidate' member
    rcases support candidate' member with inherited | allocated
    · exact Or.inl (Context.member_unificationVars_below_initialSupply inherited)
    · exact Or.inr allocated
  exact VariablesScopedBy.avoids_later observedScoped fresh wellFormed
    outerToStart (Supply.le_refl start) candidate observed hiddenMember

private theorem sequentialChecksAvoidance
    {context : Context} {start middle finish : Supply}
    (wellFormed : start.WellFormedFor context)
    {leftFirst rightFirst leftSecond rightSecond : GeneratedChecks}
    (leftFirstSupport : GeneratedChecksSupportProvenance context start middle
      leftFirst)
    (rightFirstSupport : GeneratedChecksSupportProvenance context start middle
      rightFirst)
    (leftSecondSupport : GeneratedChecksSupportProvenance context middle finish
      leftSecond)
    (rightSecondSupport : GeneratedChecksSupportProvenance context middle finish
      rightSecond)
    {firstHidden secondHidden : List UnificationVar}
    (firstFresh : VariablesFreshIn start middle firstHidden)
    (secondFresh : VariablesFreshIn middle finish secondHidden)
    (startToMiddle : start.Le middle) :
    GeneratedAvoids firstHidden (checksGenerated leftSecond) ∧
    GeneratedAvoids firstHidden (checksGenerated rightSecond) ∧
    GeneratedAvoids secondHidden (checksGenerated leftFirst) ∧
    GeneratedAvoids secondHidden (checksGenerated rightFirst) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact VariablesScopedBy.avoids_earlier firstFresh
      (checksScopedByInitialSupply leftSecondSupport) wellFormed
      (Supply.le_refl middle)
  · exact VariablesScopedBy.avoids_earlier firstFresh
      (checksScopedByInitialSupply rightSecondSupport) wellFormed
      (Supply.le_refl middle)
  · exact VariablesScopedBy.avoids_later
      (checksScopedByInitialSupply leftFirstSupport) secondFresh wellFormed
      startToMiddle (Supply.le_refl middle)
  · exact VariablesScopedBy.avoids_later
      (checksScopedByInitialSupply rightFirstSupport) secondFresh wellFormed
      startToMiddle (Supply.le_refl middle)

private theorem checkedExpression_coherence
    {signature : FrozenSignature} {fuelLeft fuelRight : Nat}
    {context : Context} {expression : Expr} {expected : Ty}
    {start leftNext rightNext : Supply} {left right : GeneratedChecks}
    (property : FullM4FuelPairProperty expression)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : start.WellFormedFor context)
    (leftDerivation : CheckedExpressionElaboratesUsing
      (M4.ElaboratesFuel signature fuelLeft) context expression expected
      start left leftNext)
    (rightDerivation : CheckedExpressionElaboratesUsing
      (M4.ElaboratesFuel signature fuelRight) context expression expected
      start right rightNext)
    (expectedAvoids : ∀ {hidden : List UnificationVar},
      VariablesFreshIn start leftNext hidden → TypeAvoids hidden expected) :
    Nonempty (SupportedChecksPair start leftNext rightNext left right) := by
  cases leftDerivation with
  | @mk leftGenerated _ leftExpression =>
      cases rightDerivation with
      | @mk rightGenerated _ rightExpression =>
          obtain ⟨result⟩ := property.toSupported signatureWellFormed wellFormed
            leftExpression rightExpression
          cases result.next_eq
          exact ⟨
            { next_eq := rfl
              certificate := supportedCertificateChecked result.certificate
                expected (expectedAvoids result.certificate.hiddenFresh) }⟩

private def VariablesBelowSupply (supply : Supply)
    (variables : List UnificationVar) : Prop :=
  ∀ candidate, candidate ∈ variables →
    candidate.Below supply.ty supply.cap

private theorem VariablesBelowSupply.mono
    {start finish : Supply} {variables : List UnificationVar}
    (below : VariablesBelowSupply start variables)
    (increases : start.Le finish) : VariablesBelowSupply finish variables := by
  intro candidate member
  have bound := below candidate member
  cases candidate <;>
    simp only [UnificationVar.Below, Supply.Le] at bound increases ⊢ <;>
    omega

private theorem VariablesBelowSupply.avoidsFresh
    {start finish : Supply} {variables hidden : List UnificationVar}
    (below : VariablesBelowSupply start variables)
    (fresh : VariablesFreshIn start finish hidden) :
    VariablesAvoid hidden variables := by
  intro candidate observed hiddenMember
  have low := below candidate observed
  have high := fresh candidate hiddenMember
  cases candidate <;>
    simp only [UnificationVar.Below, UnificationVar.FreshIn] at low high <;>
    omega

private theorem VariablesSupportProvenance.belowFinish
    {context : Context} {outerStart finish : Supply}
    {variables : List UnificationVar}
    (wellFormed : outerStart.WellFormedFor context)
    (outerToFinish : outerStart.Le finish)
    (support : VariablesSupportProvenance context outerStart finish variables) :
    VariablesBelowSupply finish variables := by
  intro candidate member
  rcases support candidate member with inherited | fresh
  · have contextBound := Context.member_unificationVars_below_initialSupply
      inherited
    change context.initialSupply.Le outerStart at wellFormed
    cases candidate with
    | ty index =>
        change index.index < finish.ty
        simp only [UnificationVar.Below] at contextBound
        exact Nat.lt_of_lt_of_le contextBound
          (Nat.le_trans wellFormed.1 outerToFinish.1)
    | cap index =>
        change index.index < finish.cap
        simp only [UnificationVar.Below] at contextBound
        exact Nat.lt_of_lt_of_le contextBound
          (Nat.le_trans wellFormed.2 outerToFinish.2)
  · cases candidate with
    | ty index =>
        exact (fresh : UnificationVar.FreshIn outerStart finish (.ty index)).2
    | cap index =>
        exact (fresh : UnificationVar.FreshIn outerStart finish (.cap index)).2

private theorem VariablesBelowSupply.scoped
    {start finish : Supply} {variables : List UnificationVar}
    (below : VariablesBelowSupply finish variables)
    (_increases : start.Le finish) :
    VariablesScopedBy start start finish variables := by
  intro candidate member
  have upper := below candidate member
  cases candidate <;>
    simp only [UnificationVar.Below, UnificationVar.FreshIn, Supply.Le]
      at upper _increases ⊢ <;> omega

private theorem VariablesScopedBy.belowFinish
    {boundary start finish : Supply} {variables : List UnificationVar}
    (scopeProof : VariablesScopedBy boundary start finish variables)
    (boundaryToStart : boundary.Le start)
    (startToFinish : start.Le finish) :
    VariablesBelowSupply finish variables := by
  intro candidate member
  rcases scopeProof candidate member with below | fresh
  · have boundaryToFinish := Supply.le_trans boundaryToStart startToFinish
    cases candidate <;>
      simp only [UnificationVar.Below, Supply.Le]
        at below boundaryToFinish ⊢ <;> omega
  · exact fresh.below

private theorem VariablesBelowSupply.asScoped
    {boundary start finish : Supply} {variables : List UnificationVar}
    (below : VariablesBelowSupply boundary variables) :
    VariablesScopedBy boundary start finish variables := by
  intro candidate member
  exact Or.inl (below candidate member)

private theorem VariablesScopedBy.extendFinish
    {boundary originStart start finish : Supply}
    {variables : List UnificationVar}
    (scopeProof : VariablesScopedBy boundary originStart start variables)
    (startToFinish : start.Le finish) :
    VariablesScopedBy boundary originStart finish variables := by
  intro candidate member
  rcases scopeProof candidate member with below | fresh
  · exact Or.inl below
  · exact Or.inr (fresh.extend_finish startToFinish)

private theorem extendContext_scopedByBoundary
    {boundary originStart start : Supply} {context : Context}
    {bindings : List Ty}
    (bindingsScoped : VariablesScopedBy boundary originStart start
      (Ty.unificationVarsList bindings))
    (contextScoped : VariablesScopedBy boundary originStart start
      context.unificationVars) :
    VariablesScopedBy boundary originStart start
      (Pattern.extendContext bindings context).unificationVars := by
  induction bindings with
  | nil => simpa [Pattern.extendContext] using contextScoped
  | cons binding bindings induction =>
      intro candidate member
      have origin := Context.mono_cons_unificationVars_origin
        (bindings.map Scheme.mono ++ context) binding member
      rcases origin with bindingMember | tailMember
      · exact bindingsScoped candidate (by
          simpa [Ty.unificationVarsList] using Or.inl bindingMember)
      · apply induction
        · intro item itemMember
          exact bindingsScoped item (by
            simpa [Ty.unificationVarsList] using Or.inr itemMember)
        · simpa [Pattern.extendContext] using tailMember

private theorem holeProductBelow
    {boundary : Supply} {holes : List Dual}
    (holesBelow : VariablesBelowSupply boundary
      (dualUnificationVars holes)) :
    VariablesBelowSupply boundary
      (DataTypes.list (holeProductTarget holes)).unificationVars := by
  intro candidate member
  simp only [DataTypes.list, Ty.unificationVars,
    Ty.unificationVarsList] at member
  cases holes with
  | nil => simp [holeProductTarget, Ty.unificationVars,
      Ty.unificationVarsList] at member
  | cons first rest =>
      cases rest with
      | nil =>
          apply holesBelow candidate
          have targetMember : candidate ∈ first.target.unificationVars := by
            simpa [holeProductTarget] using member
          simpa [holeProductTarget, dualUnificationVars, dualVariables,
            Ty.unificationVars] using
            (Or.inr targetMember : candidate ∈ first.capability.unificationVars ∨
              candidate ∈ first.target.unificationVars)
      | cons second rest =>
          apply holesBelow candidate
          exact dualTargets_variables (by
            simpa [holeProductTarget, Ty.unificationVars] using member)

private theorem holeProductScoped
    {boundary originStart start : Supply} {holes : List Dual}
    (holesScoped : VariablesScopedBy boundary originStart start
      (dualUnificationVars holes)) :
    VariablesScopedBy boundary originStart start
      (DataTypes.list (holeProductTarget holes)).unificationVars := by
  intro candidate member
  cases holes with
  | nil => simp [DataTypes.list, holeProductTarget, Ty.unificationVars,
      Ty.unificationVarsList] at member
  | cons first rest =>
      cases rest with
      | nil =>
          apply holesScoped candidate
          have targetMember : candidate ∈ first.target.unificationVars := by
            simpa [DataTypes.list, holeProductTarget, Ty.unificationVars,
              Ty.unificationVarsList] using member
          simpa [dualUnificationVars, dualVariables] using
            (Or.inr targetMember : candidate ∈ first.capability.unificationVars ∨
              candidate ∈ first.target.unificationVars)
      | cons second rest =>
          apply holesScoped candidate
          exact dualTargets_variables (by
            simpa [DataTypes.list, holeProductTarget, Ty.unificationVars,
              Ty.unificationVarsList] using member)

private theorem checksSupport_scoped
    {context : Context} {outerStart start finish : Supply}
    {checks : GeneratedChecks}
    (wellFormed : outerStart.WellFormedFor context)
    (outerToFinish : outerStart.Le finish)
    (startToFinish : start.Le finish)
    (support : GeneratedChecksSupportProvenance context outerStart finish checks) :
    VariablesScopedBy start start finish (checksGenerated checks).unificationVars := by
  apply VariablesBelowSupply.scoped _ startToFinish
  apply VariablesSupportProvenance.belowFinish wellFormed outerToFinish
  intro candidate member
  exact support candidate (by
    simpa [checksGenerated, Generated.unificationVars, Ty.unificationVars,
      GeneratedChecks.unificationVars] using member)

private theorem contextBelowSupply
    {context : Context} {supply : Supply}
    (wellFormed : supply.WellFormedFor context) :
    VariablesBelowSupply supply context.unificationVars := by
  intro candidate member
  have belowInitial := Context.member_unificationVars_below_initialSupply member
  change context.initialSupply.Le supply at wellFormed
  cases candidate <;>
    simp only [UnificationVar.Below, Supply.Le] at belowInitial wellFormed ⊢ <;>
    omega

private theorem checkedExpression_scoped
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {expected : Ty} {outerStart start finish : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : outerStart.WellFormedFor context)
    (expectedBelow : VariablesBelowSupply outerStart expected.unificationVars)
    (derivation : CheckedExpressionElaboratesUsing
      (M4.ElaboratesFuel signature fuel) context expression expected start
      generated finish) :
    VariablesScopedBy outerStart start finish
      (checksGenerated generated).unificationVars := by
  cases derivation with
  | @mk inferred _ expressionDerivation =>
      have expressionSupport :=
        expressionDerivation.supportProvenance signatureWellFormed
      have contextBelow := contextBelowSupply wellFormed
      intro candidate member
      simp only [checksGenerated, GeneratedChecks.checked,
        Generated.unificationVars, Ty.unificationVars,
        pendingUnificationVars_append,
        pendingUnificationVars, CheckObligation.unificationVars,
        List.mem_append, List.not_mem_nil, false_or] at member
      rcases member with hardMember | pendingMember | sourceMember |
          expectedMember
      · rcases expressionSupport candidate (by
          simp [Generated.unificationVars, hardMember]) with inherited | fresh
        · exact Or.inl (contextBelow candidate inherited)
        · exact Or.inr fresh
      · rcases expressionSupport candidate (by
          simp [Generated.unificationVars, pendingMember]) with inherited | fresh
        · exact Or.inl (contextBelow candidate inherited)
        · exact Or.inr fresh
      · rcases sourceMember with sourceMember | expectedMember
        · rcases expressionSupport candidate (by
            simp [Generated.unificationVars, sourceMember]) with inherited | fresh
          · exact Or.inl (contextBelow candidate inherited)
          · exact Or.inr fresh
        · exact Or.inl (expectedBelow candidate expectedMember)
      · simp at expectedMember

private theorem member_mono_context
    {target : Ty} {candidate : UnificationVar}
    (member : candidate ∈ target.unificationVars) :
    candidate ∈ Context.unificationVars ([Scheme.mono target] : Context) := by
  cases candidate with
  | ty index =>
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
      apply Or.inl
      refine ⟨index, ?_, rfl⟩
      rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
      refine ⟨Scheme.mono target, by simp, ?_⟩
      rw [Scheme.mem_freeTyVars]
      simpa [Scheme.mono, PolyTy.ofTy] using
        (Ty.mem_tyVars_iff_unificationVars index target).mpr member
  | cap index =>
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
      apply Or.inr
      refine ⟨index, ?_, rfl⟩
      rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap]
      refine ⟨Scheme.mono target, by simp, ?_⟩
      rw [Scheme.mem_freeCapVars]
      simpa [Scheme.mono, PolyTy.ofTy] using
        (Ty.mem_capVars_iff_unificationVars index target).mpr member

private theorem scopedFromMonoContext
    {boundary originStart start finish : Supply} {target : Ty}
    {variables : List UnificationVar}
    (targetScoped : VariablesScopedBy boundary originStart start
      target.unificationVars)
    (originToStart : originStart.Le start)
    (startToFinish : start.Le finish)
    (support : VariablesSupportProvenance ([Scheme.mono target] : Context)
      start finish variables) :
    VariablesScopedBy boundary originStart finish variables := by
  intro candidate member
  rcases support candidate member with inherited | fresh
  · have origin := Context.mono_cons_unificationVars_origin [] target inherited
    rcases origin with targetMember | impossible
    · rcases targetScoped candidate targetMember with below | fresh
      · exact Or.inl below
      · exact Or.inr (fresh.extend_finish startToFinish)
    · simp [Context.unificationVars, Context.freeTyVars,
        Context.freeCapVars, dedupFirst, dedup] at impossible
  · exact Or.inr (fresh.lower_start originToStart)

private theorem dpat_scopedByBoundary
    {signature : FrozenSignature} {pattern : DPat} {expected : Ty}
    {boundary originStart start finish : Supply} {generated : GeneratedDPat}
    (signatureWellFormed : signature.WellFormed)
    (expectedScoped : VariablesScopedBy boundary originStart start
      expected.unificationVars)
    (originToStart : originStart.Le start)
    (derivation : DPatElaborates signature pattern expected start generated
      finish) :
    VariablesScopedBy boundary originStart finish generated.unificationVars := by
  apply scopedFromMonoContext expectedScoped originToStart
    derivation.supply_le_next
  exact derivation.supportProvenance signatureWellFormed
    (fun candidate member => Or.inl (member_mono_context member))
    (Supply.le_refl start)

private theorem ppat_scopedByBoundary
    {signature : FrozenSignature} {pattern : PPat} {target : Ty}
    {capability : Option Cap} {boundary originStart start finish : Supply}
    {generated : GeneratedPPat}
    (signatureWellFormed : signature.WellFormed)
    (targetScoped : VariablesScopedBy boundary originStart start
      target.unificationVars)
    (capabilityScoped : VariablesScopedBy boundary originStart start
      (match capability with
       | none => []
       | some expected => expected.unificationVars))
    (originToStart : originStart.Le start)
    (derivation : PPatElaborates signature pattern target capability start
      generated finish) :
    VariablesScopedBy boundary originStart finish generated.unificationVars := by
  let input : Ty := match capability with
    | none => target
    | some expected => .slot expected target
  have inputScoped : VariablesScopedBy boundary originStart start
      input.unificationVars := by
    intro candidate member
    cases capability with
    | none => exact targetScoped candidate (by simpa [input] using member)
    | some expected =>
        simp only [input, Ty.unificationVars, List.mem_append] at member
        rcases member with capabilityMember | targetMember
        · exact capabilityScoped candidate (by simpa using capabilityMember)
        · exact targetScoped candidate targetMember
  apply scopedFromMonoContext inputScoped originToStart
    derivation.supply_le_next
  apply derivation.supportProvenance signatureWellFormed
  · intro candidate member
    apply Or.inl
    apply member_mono_context
    cases capability with
    | none => simpa [input] using member
    | some expected =>
        simp only [input, Ty.unificationVars, List.mem_append]
        exact Or.inr member
  · intro candidate member
    apply Or.inl
    apply member_mono_context
    cases capability with
    | none => simp at member
    | some expected =>
        simp only [input, Ty.unificationVars, List.mem_append]
        exact Or.inl member
  · exact Supply.le_refl start

private theorem checkedExpression_scopedByBoundary
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {expected : Ty}
    {boundary originStart start finish : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (originToStart : originStart.Le start)
    (contextScoped : VariablesScopedBy boundary originStart start
      context.unificationVars)
    (expectedScoped : VariablesScopedBy boundary originStart start
      expected.unificationVars)
    (derivation : CheckedExpressionElaboratesUsing
      (M4.ElaboratesFuel signature fuel) context expression expected start
      generated finish) :
    VariablesScopedBy boundary originStart finish
      (checksGenerated generated).unificationVars := by
  cases derivation with
  | @mk inferred _ expressionDerivation =>
      have expressionSupport :=
        expressionDerivation.supportProvenance signatureWellFormed
      have startToFinish := expressionDerivation.supply_le_next
      intro candidate member
      simp only [checksGenerated, GeneratedChecks.checked,
        Generated.unificationVars, Ty.unificationVars,
        pendingUnificationVars_append, pendingUnificationVars,
        CheckObligation.unificationVars, List.mem_append,
        List.not_mem_nil, false_or] at member
      rcases member with hardMember | pendingMember | sourceMember |
          expectedMember
      · rcases expressionSupport candidate (by
          simp [Generated.unificationVars, hardMember]) with inherited | fresh
        · rcases contextScoped candidate inherited with below | earlier
          · exact Or.inl below
          · exact Or.inr (earlier.extend_finish startToFinish)
        · exact Or.inr (fresh.lower_start originToStart)
      · rcases expressionSupport candidate (by
          simp [Generated.unificationVars, pendingMember]) with inherited | fresh
        · rcases contextScoped candidate inherited with below | earlier
          · exact Or.inl below
          · exact Or.inr (earlier.extend_finish startToFinish)
        · exact Or.inr (fresh.lower_start originToStart)
      · rcases sourceMember with sourceMember | expectedMember
        · rcases expressionSupport candidate (by
            simp [Generated.unificationVars, sourceMember]) with inherited | fresh
          · rcases contextScoped candidate inherited with below | earlier
            · exact Or.inl below
            · exact Or.inr (earlier.extend_finish startToFinish)
          · exact Or.inr (fresh.lower_start originToStart)
        · rcases expectedScoped candidate expectedMember with below | earlier
          · exact Or.inl below
          · exact Or.inr (earlier.extend_finish startToFinish)
      · simp at expectedMember

private theorem dualHeadBelow
    {supply : Supply} {hole : Dual} {holes : List Dual}
    (below : VariablesBelowSupply supply
      (dualUnificationVars (hole :: holes))) :
    VariablesBelowSupply supply
      (.slot hole.capability hole.target : Ty).unificationVars := by
  intro candidate member
  exact below candidate (by
    simpa [dualUnificationVars, dualVariables, Ty.unificationVars] using
      (List.mem_append_left (dualUnificationVars holes) member))

private theorem dualTailBelow
    {supply : Supply} {hole : Dual} {holes : List Dual}
    (below : VariablesBelowSupply supply
      (dualUnificationVars (hole :: holes))) :
    VariablesBelowSupply supply (dualUnificationVars holes) := by
  intro candidate member
  exact below candidate (by
    simp only [dualUnificationVars, List.flatMap_cons, List.mem_append]
    exact Or.inr member)

private theorem nextItems_scoped
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {items : List Expr} {holes : List Dual} {outerStart start finish : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : outerStart.WellFormedFor context)
    (outerToStart : outerStart.Le start)
    (holesBelow : VariablesBelowSupply outerStart (dualUnificationVars holes))
    (derivation : NextMatcherItemsElaborateUsing
      (M4.ElaboratesFuel signature fuel) context items holes start generated
      finish) :
    VariablesScopedBy outerStart start finish
      (checksGenerated generated).unificationVars := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [checksGenerated, GeneratedChecks.empty, Generated.unificationVars,
        Ty.unificationVars,
        pendingUnificationVars, TypePM.unificationVars] at member
  | @cons item items hole holes start generatedItem afterItem generatedItems
      finish head tail induction =>
      have startToAfter := head.supply_le_next (fun child => child.supply_le_next)
      have afterToFinish := tail.supply_le_next (fun child => child.supply_le_next)
      have headScoped := checkedExpression_scoped signatureWellFormed wellFormed
        (dualHeadBelow holesBelow) head
      have tailBelow := dualTailBelow holesBelow
      have tailScoped := induction
        (Supply.le_trans outerToStart startToAfter) tailBelow
      intro candidate member
      have split : candidate ∈ (checksGenerated generatedItem).unificationVars ∨
          candidate ∈ (checksGenerated generatedItems).unificationVars := by
        simpa [checksGenerated, GeneratedChecks.append,
          Generated.unificationVars, Ty.unificationVars,
          GeneratedChecks.unificationVars, unificationVars_append,
          pendingUnificationVars_append, TypePM.unificationVars,
          or_assoc, or_left_comm, or_comm] using member
      rcases split with headMember | tailMember
      · rcases headScoped candidate headMember with inherited | fresh
        · exact Or.inl inherited
        · exact Or.inr (fresh.extend_finish afterToFinish)
      · rcases tailScoped candidate tailMember with inherited | fresh
        · exact Or.inl inherited
        · exact Or.inr (fresh.lower_start startToAfter)

private theorem dualHeadScoped
    {boundary originStart start : Supply} {hole : Dual} {holes : List Dual}
    (scopeProof : VariablesScopedBy boundary originStart start
      (dualUnificationVars (hole :: holes))) :
    VariablesScopedBy boundary originStart start
      (.slot hole.capability hole.target : Ty).unificationVars := by
  intro candidate member
  apply scopeProof candidate
  simpa [dualUnificationVars, dualVariables, Ty.unificationVars] using
    (List.mem_append_left (dualUnificationVars holes) member)

private theorem dualTailScoped
    {boundary originStart start : Supply} {hole : Dual} {holes : List Dual}
    (scopeProof : VariablesScopedBy boundary originStart start
      (dualUnificationVars (hole :: holes))) :
    VariablesScopedBy boundary originStart start
      (dualUnificationVars holes) := by
  intro candidate member
  apply scopeProof candidate
  simp only [dualUnificationVars, List.flatMap_cons, List.mem_append]
  exact Or.inr member

private theorem nextItems_scopedByBoundary
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {items : List Expr} {holes : List Dual}
    {boundary originStart start finish : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (originToStart : originStart.Le start)
    (contextScoped : VariablesScopedBy boundary originStart start
      context.unificationVars)
    (holesScoped : VariablesScopedBy boundary originStart start
      (dualUnificationVars holes))
    (derivation : NextMatcherItemsElaborateUsing
      (M4.ElaboratesFuel signature fuel) context items holes start generated
      finish) :
    VariablesScopedBy boundary originStart finish
      (checksGenerated generated).unificationVars := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [checksGenerated, GeneratedChecks.empty, Generated.unificationVars,
        Ty.unificationVars,
        pendingUnificationVars, TypePM.unificationVars] at member
  | @cons item items hole holes start generatedItem afterItem generatedItems
      finish head tail induction =>
      have startToAfter := head.supply_le_next
        (fun child => child.supply_le_next)
      have headScoped := checkedExpression_scopedByBoundary signatureWellFormed
        originToStart contextScoped (dualHeadScoped holesScoped) head
      have tailScoped := induction
        (Supply.le_trans originToStart startToAfter)
        (VariablesScopedBy.extendFinish contextScoped startToAfter)
        (VariablesScopedBy.extendFinish (dualTailScoped holesScoped)
          startToAfter)
      have afterToFinish := tail.supply_le_next
        (fun child => child.supply_le_next)
      intro candidate member
      have split : candidate ∈ (checksGenerated generatedItem).unificationVars ∨
          candidate ∈ (checksGenerated generatedItems).unificationVars := by
        simpa [checksGenerated, GeneratedChecks.append,
          Generated.unificationVars, Ty.unificationVars,
          GeneratedChecks.unificationVars, unificationVars_append,
          pendingUnificationVars_append, or_assoc, or_left_comm, or_comm]
          using member
      rcases split with headMember | tailMember
      · rcases headScoped candidate headMember with below | fresh
        · exact Or.inl below
        · exact Or.inr (fresh.extend_finish afterToFinish)
      · exact tailScoped candidate tailMember

private theorem nextMatchers_scopedByBoundary
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {holes : List Dual}
    {boundary originStart start finish : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (originToStart : originStart.Le start)
    (contextScoped : VariablesScopedBy boundary originStart start
      context.unificationVars)
    (holesScoped : VariablesScopedBy boundary originStart start
      (dualUnificationVars holes))
    (derivation : NextMatchersElaborateUsing
      (M4.ElaboratesFuel signature fuel) context expression holes start generated
      finish) :
    VariablesScopedBy boundary originStart finish
      (checksGenerated generated).unificationVars := by
  cases derivation with
  | zero checked =>
      exact checkedExpression_scopedByBoundary signatureWellFormed originToStart
        contextScoped (by
          intro candidate member
          simp [Ty.unificationVars, Ty.unificationVarsList] at member) checked
  | one checked =>
      exact checkedExpression_scopedByBoundary signatureWellFormed originToStart
        contextScoped (dualHeadScoped (holes := []) holesScoped) checked
  | many components =>
      exact nextItems_scopedByBoundary signatureWellFormed originToStart
        contextScoped holesScoped components

private theorem nextItems_coherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    {context : Context} {items : List Expr} {holes : List Dual}
    {start leftNext rightNext : Supply} {left right : GeneratedChecks}
    (properties : ∀ expression, expression ∈ items →
      FullM4FuelPairProperty expression)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : start.WellFormedFor context)
    (holesBelow : VariablesBelowSupply start (dualUnificationVars holes))
    (leftDerivation : NextMatcherItemsElaborateUsing
      (M4.ElaboratesFuel signature leftFuel) context items holes start left
      leftNext)
    (rightDerivation : NextMatcherItemsElaborateUsing
      (M4.ElaboratesFuel signature rightFuel) context items holes start right
    rightNext) : Nonempty (SupportedChecksPair start leftNext rightNext left right) := by
  induction leftDerivation generalizing right rightNext with
  | nil =>
      cases rightDerivation
      exact ⟨
        { next_eq := rfl
          certificate := SupportedEntailedAlignmentCertificate.refl _ _ _ }⟩
  | @cons item items hole holes start leftHead leftAfter leftTail leftNext
      leftHeadDerivation leftTailDerivation induction =>
      cases rightDerivation with
      | @cons _ _ _ _ _ rightHead rightAfter rightTail rightNext
          rightHeadDerivation rightTailDerivation =>
          have slotBelow := dualHeadBelow holesBelow
          obtain ⟨headResult⟩ := checkedExpression_coherence
            (properties item (by simp)) signatureWellFormed wellFormed
            leftHeadDerivation rightHeadDerivation
            (fun fresh => slotBelow.avoidsFresh fresh)
          cases headResult.next_eq
          have startToAfter := leftHeadDerivation.supply_le_next
            (fun child => child.supply_le_next)
          have tailBelow := (dualTailBelow holesBelow).mono startToAfter
          obtain ⟨tailResult⟩ := induction
            (fun expression member => properties expression (by simp [member]))
            (wellFormed.mono startToAfter) tailBelow rightTailDerivation
          cases tailResult.next_eq
          have afterToNext := leftTailDerivation.supply_le_next
            (fun child => child.supply_le_next)
          have leftHeadScoped := checkedExpression_scoped signatureWellFormed
            wellFormed slotBelow leftHeadDerivation
          have rightHeadScoped := checkedExpression_scoped signatureWellFormed
            wellFormed slotBelow rightHeadDerivation
          have leftTailScoped := nextItems_scoped signatureWellFormed
            wellFormed startToAfter (dualTailBelow holesBelow) leftTailDerivation
          have rightTailScoped := nextItems_scoped signatureWellFormed
            wellFormed startToAfter (dualTailBelow holesBelow) rightTailDerivation
          have leftTailAvoids := VariablesScopedBy.avoids_earlier
            headResult.certificate.hiddenFresh leftTailScoped
            (Supply.le_refl start) (Supply.le_refl leftAfter)
          have rightTailAvoids := VariablesScopedBy.avoids_earlier
            headResult.certificate.hiddenFresh rightTailScoped
            (Supply.le_refl start) (Supply.le_refl leftAfter)
          have leftHeadAvoids := VariablesScopedBy.avoids_later leftHeadScoped
            tailResult.certificate.hiddenFresh (Supply.le_refl start)
            startToAfter (Supply.le_refl leftAfter)
          have rightHeadAvoids := VariablesScopedBy.avoids_later rightHeadScoped
            tailResult.certificate.hiddenFresh (Supply.le_refl start)
            startToAfter (Supply.le_refl leftAfter)
          exact ⟨
            { next_eq := rfl
              certificate := appendSequentialChecks headResult.certificate
                tailResult.certificate startToAfter afterToNext
                leftTailAvoids rightTailAvoids leftHeadAvoids
                rightHeadAvoids }⟩

private theorem nextMatchers_coherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    {context : Context} {expression : Expr} {holes : List Dual}
    {start leftNext rightNext : Supply} {left right : GeneratedChecks}
    (expressionProperty : FullM4FuelPairProperty expression)
    (tupleProperties : ∀ items, expression = .tuple items →
      ∀ item, item ∈ items → FullM4FuelPairProperty item)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : start.WellFormedFor context)
    (holesBelow : VariablesBelowSupply start (dualUnificationVars holes))
    (leftDerivation : NextMatchersElaborateUsing
      (M4.ElaboratesFuel signature leftFuel) context expression holes start left
      leftNext)
    (rightDerivation : NextMatchersElaborateUsing
      (M4.ElaboratesFuel signature rightFuel) context expression holes start right
      rightNext) : Nonempty (SupportedChecksPair start leftNext rightNext left right) := by
  cases leftDerivation with
  | zero leftChecked =>
      cases rightDerivation with
      | zero rightChecked =>
          exact checkedExpression_coherence expressionProperty
            signatureWellFormed wellFormed leftChecked rightChecked
            (fun _fresh => by simp [TypeAvoids, Ty.unificationVars,
              Ty.unificationVarsList, VariablesAvoid])
  | @one expression hole start left leftNext leftChecked =>
      cases rightDerivation with
      | one rightChecked =>
          have slotBelow := dualHeadBelow (holes := []) holesBelow
          exact checkedExpression_coherence expressionProperty
            signatureWellFormed wellFormed leftChecked rightChecked
            (fun fresh => slotBelow.avoidsFresh fresh)
  | @many items first second rest start left leftNext leftComponents =>
      cases rightDerivation with
      | many rightComponents =>
          exact nextItems_coherence
            (tupleProperties items rfl) signatureWellFormed wellFormed holesBelow
            leftComponents rightComponents

/-- Generated checks for one matcher arm retain the fixed boundary that
precedes the arm list.  Variables allocated by its header remain in the
arm's own interval instead of being reclassified as inherited by the body. -/
theorem matcherArm_scopedByBoundary
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {captures : List Ty} {matcherTarget : Ty} {holes : List Dual}
    {arm : MatcherArm} {boundary originStart start finish : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (contextScoped : VariablesScopedBy boundary originStart start
      context.unificationVars)
    (capturesScoped : VariablesScopedBy boundary originStart start
      (Ty.unificationVarsList captures))
    (targetScoped : VariablesScopedBy boundary originStart start
      matcherTarget.unificationVars)
    (holesScoped : VariablesScopedBy boundary originStart start
      (dualUnificationVars holes))
    (originToStart : originStart.Le start)
    (derivation : MatcherArmElaboratesUsing
      (M4.ElaboratesFuel signature fuel) DPatElaborates signature context
      captures matcherTarget holes arm start generated finish) :
    VariablesScopedBy boundary originStart finish
      (checksGenerated generated).unificationVars := by
  cases derivation with
  | @mk header body start generatedHeader afterHeader generatedBody finish
      headerElaboration bodyElaboration =>
      have startToHeader := headerElaboration.supply_le_next
      have headerScoped := dpat_scopedByBoundary signatureWellFormed targetScoped
        originToStart headerElaboration
      have bindingsScoped : VariablesScopedBy boundary originStart afterHeader
          (Ty.unificationVarsList generatedHeader.bindings) := by
        intro candidate member
        exact headerScoped candidate (by
          simp [GeneratedDPat.unificationVars, member])
      have bodyContextScoped : VariablesScopedBy boundary originStart afterHeader
          (Pattern.extendContext generatedHeader.bindings
            (Pattern.extendContext captures context)).unificationVars :=
        extendContext_scopedByBoundary bindingsScoped
          (extendContext_scopedByBoundary
            (VariablesScopedBy.extendFinish capturesScoped startToHeader)
            (VariablesScopedBy.extendFinish contextScoped startToHeader))
      have holesAtHeader := VariablesScopedBy.extendFinish holesScoped
        startToHeader
      have expectedScoped := holeProductScoped holesAtHeader
      have bodyScoped := checkedExpression_scopedByBoundary
        signatureWellFormed (Supply.le_trans originToStart startToHeader)
        bodyContextScoped
        expectedScoped bodyElaboration
      intro candidate member
      have split : candidate ∈ TypePM.unificationVars generatedHeader.hard ∨
          candidate ∈ (checksGenerated generatedBody).unificationVars := by
        simpa [checksGenerated, Generated.unificationVars,
          GeneratedChecks.unificationVars, unificationVars_append,
          or_assoc, or_left_comm, or_comm]
          using member
      rcases split with headerMember | bodyMember
      · rcases headerScoped candidate (by
          simp [GeneratedDPat.unificationVars, headerMember]) with below | fresh
        · exact Or.inl below
        · exact Or.inr (fresh.extend_finish
            (bodyElaboration.supply_le_next
              (fun child => child.supply_le_next)))
      · exact bodyScoped candidate bodyMember

/-- List counterpart of `MatcherArmElaboratesUsing.scopedByBoundary`, retaining
the boundary at the beginning of the whole source-ordered arm list. -/
theorem matcherArms_scopedByBoundary
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {captures : List Ty} {matcherTarget : Ty} {holes : List Dual}
    {arms : List MatcherArm} {boundary originStart start finish : Supply}
    {generated : GeneratedArms}
    (signatureWellFormed : signature.WellFormed)
    (contextScoped : VariablesScopedBy boundary originStart start
      context.unificationVars)
    (capturesScoped : VariablesScopedBy boundary originStart start
      (Ty.unificationVarsList captures))
    (targetScoped : VariablesScopedBy boundary originStart start
      matcherTarget.unificationVars)
    (holesScoped : VariablesScopedBy boundary originStart start
      (dualUnificationVars holes))
    (originToStart : originStart.Le start)
    (derivation : MatcherArmsElaborateUsing
      (M4.ElaboratesFuel signature fuel) DPatElaborates signature context
      captures matcherTarget holes arms start generated finish) :
    VariablesScopedBy boundary originStart finish
      (checksGenerated generated.checks).unificationVars := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [checksGenerated, GeneratedChecks.empty, Generated.unificationVars,
        Ty.unificationVars,
        pendingUnificationVars, TypePM.unificationVars] at member
  | @cons arm arms start generatedArm afterArm generatedArms finish head tail
      induction =>
      have startToAfter := head.supply_le_next
        (fun child => child.supply_le_next) DPatElaborates.supply_le_next
      have headScoped := matcherArm_scopedByBoundary signatureWellFormed
        contextScoped capturesScoped targetScoped holesScoped originToStart head
      have tailScoped := induction
        (VariablesScopedBy.extendFinish contextScoped startToAfter)
        (VariablesScopedBy.extendFinish capturesScoped startToAfter)
        (VariablesScopedBy.extendFinish targetScoped startToAfter)
        (VariablesScopedBy.extendFinish holesScoped startToAfter)
        (Supply.le_trans originToStart startToAfter)
      have afterToFinish := tail.supply_le_next
        (fun child => child.supply_le_next) DPatElaborates.supply_le_next
      intro candidate member
      have split : candidate ∈ (checksGenerated generatedArm).unificationVars ∨
          candidate ∈
            (checksGenerated generatedArms.checks).unificationVars := by
        simpa [checksGenerated, GeneratedChecks.append,
          Generated.unificationVars, Ty.unificationVars,
          GeneratedChecks.unificationVars, unificationVars_append,
          pendingUnificationVars_append, or_assoc, or_left_comm, or_comm]
          using member
      rcases split with headMember | tailMember
      · rcases headScoped candidate headMember with below | fresh
        · exact Or.inl below
        · exact Or.inr (fresh.extend_finish afterToFinish)
      · rcases tailScoped candidate tailMember with below | fresh
        · exact Or.inl below
        · exact Or.inr fresh

/-- One complete matcher clause preserves a fixed caller boundary across its
header, next-matcher expression, and data-arm list. -/
theorem matcherClause_scopedByBoundary
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {matcherTarget : Ty} {clause : MatcherClause}
    {boundary originStart start finish : Supply}
    {generated : GeneratedMatcherClause}
    (signatureWellFormed : signature.WellFormed)
    (contextScoped : VariablesScopedBy boundary originStart start
      context.unificationVars)
    (targetScoped : VariablesScopedBy boundary originStart start
      matcherTarget.unificationVars)
    (originToStart : originStart.Le start)
    (derivation : MatcherClauseElaboratesUsing
      (M4.ElaboratesFuel signature fuel) PPatElaborates DPatElaborates
      signature context matcherTarget clause start generated finish) :
    VariablesScopedBy boundary originStart finish generated.unificationVars := by
  cases derivation with
  | @mk header nextMatchers arms start generatedHeader afterHeader generatedNext
      afterNext generatedArms finish shape headerElaboration nextElaboration
      armsElaboration =>
      have startToHeader := headerElaboration.supply_le_next
      have headerToNext := nextElaboration.supply_le_next
        (fun child => child.supply_le_next)
      have nextToFinish := armsElaboration.supply_le_next
        (fun child => child.supply_le_next) DPatElaborates.supply_le_next
      have headerScoped := ppat_scopedByBoundary signatureWellFormed
        targetScoped (by
          intro candidate member
          simp at member)
        originToStart headerElaboration
      have holesScoped : VariablesScopedBy boundary originStart afterHeader
          (dualUnificationVars generatedHeader.holes) := by
        intro candidate member
        exact headerScoped candidate (by
          simp [GeneratedPPat.unificationVars, member])
      have capturesScoped : VariablesScopedBy boundary originStart afterHeader
          (Ty.unificationVarsList generatedHeader.captures) := by
        intro candidate member
        exact headerScoped candidate (by
          simp [GeneratedPPat.unificationVars, member])
      have capturedContextScoped := extendContext_scopedByBoundary
        capturesScoped (VariablesScopedBy.extendFinish contextScoped
          startToHeader)
      have nextScoped := nextMatchers_scopedByBoundary signatureWellFormed
        (Supply.le_trans originToStart startToHeader) capturedContextScoped
        holesScoped nextElaboration
      have armsScoped := matcherArms_scopedByBoundary signatureWellFormed
        (VariablesScopedBy.extendFinish contextScoped
          (Supply.le_trans startToHeader headerToNext))
        (VariablesScopedBy.extendFinish capturesScoped headerToNext)
        (VariablesScopedBy.extendFinish targetScoped
          (Supply.le_trans startToHeader headerToNext))
        (VariablesScopedBy.extendFinish holesScoped headerToNext)
        (Supply.le_trans originToStart
          (Supply.le_trans startToHeader headerToNext)) armsElaboration
      have headerFinal := VariablesScopedBy.extendFinish headerScoped
        (Supply.le_trans headerToNext nextToFinish)
      have nextFinal := VariablesScopedBy.extendFinish nextScoped nextToFinish
      intro candidate member
      rw [GeneratedMatcherClause.unificationVars] at member
      simp only [GeneratedChecks.unificationVars, unificationVars_append,
        pendingUnificationVars_append, List.mem_append] at member
      simp only [or_assoc] at member
      rcases member with holesMember | evidenceMember | headerHardMember |
          nextHardMember | armsHardMember | nextPendingMember |
          armsPendingMember
      · apply headerFinal candidate
        simp only [GeneratedPPat.unificationVars, List.mem_append]
        exact Or.inl (Or.inl (Or.inl holesMember))
      · apply headerFinal candidate
        simp only [GeneratedPPat.unificationVars, List.mem_append]
        exact Or.inl (Or.inr evidenceMember)
      · apply headerFinal candidate
        simp only [GeneratedPPat.unificationVars, List.mem_append]
        exact Or.inr headerHardMember
      · exact nextFinal candidate (by
          simp [checksGenerated, Generated.unificationVars, nextHardMember])
      · exact armsScoped candidate (by
          simp [checksGenerated, Generated.unificationVars, armsHardMember])
      · exact nextFinal candidate (by
          simp [checksGenerated, Generated.unificationVars, nextPendingMember])
      · exact armsScoped candidate (by
          simp [checksGenerated, Generated.unificationVars, armsPendingMember])

/-- Source-ordered matcher clauses preserve the boundary at the start of the
whole clause list, including evidence capabilities and checking blocks. -/
theorem matcherClauses_scopedByBoundary
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {matcherTarget : Ty} {clauses : List MatcherClause}
    {boundary originStart start finish : Supply}
    {generated : GeneratedMatcherClauses}
    (signatureWellFormed : signature.WellFormed)
    (contextScoped : VariablesScopedBy boundary originStart start
      context.unificationVars)
    (targetScoped : VariablesScopedBy boundary originStart start
      matcherTarget.unificationVars)
    (originToStart : originStart.Le start)
    (derivation : MatcherClausesElaborateUsing
      (M4.ElaboratesFuel signature fuel) PPatElaborates DPatElaborates
      signature context matcherTarget clauses start generated finish) :
    VariablesScopedBy boundary originStart finish generated.unificationVars := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [GeneratedMatcherClauses.unificationVars,
        GeneratedChecks.unificationVars, GeneratedChecks.empty,
        Cap.unificationVarsList, TypePM.unificationVars,
        pendingUnificationVars] at member
  | @cons clause clauses start generatedClause afterClause generatedClauses finish
      head tail induction =>
      have startToAfter := head.supply_le_next
        (fun child => child.supply_le_next) PPatElaborates.supply_le_next
        DPatElaborates.supply_le_next
      have headScoped := matcherClause_scopedByBoundary signatureWellFormed
        contextScoped targetScoped originToStart head
      have tailScoped := induction
        (VariablesScopedBy.extendFinish contextScoped startToAfter)
        (VariablesScopedBy.extendFinish targetScoped startToAfter)
        (Supply.le_trans originToStart startToAfter)
      have afterToFinish := tail.supply_le_next
        (fun child => child.supply_le_next) PPatElaborates.supply_le_next
        DPatElaborates.supply_le_next
      have headFinal := VariablesScopedBy.extendFinish headScoped afterToFinish
      intro candidate member
      rw [GeneratedMatcherClauses.unificationVars] at member
      simp only [GeneratedChecks.unificationVars, GeneratedChecks.append,
        unificationVars_append, pendingUnificationVars_append,
        List.mem_append] at member
      simp only [or_assoc] at member
      rcases member with evidenceMember | headHardMember | tailHardMember |
          headPendingMember | tailPendingMember
      · cases evidenceCase : generatedClause.evidence with
        | none =>
            exact tailScoped candidate (by
              apply List.mem_append_left
              simpa [evidenceCase] using evidenceMember)
        | some evidence =>
            simp only [evidenceCase, Cap.unificationVarsList,
              List.mem_append] at evidenceMember
            rcases evidenceMember with headEvidence | tailEvidence
            · exact headFinal candidate (by
                simp [GeneratedMatcherClause.unificationVars, evidenceCase,
                  headEvidence])
            · exact tailScoped candidate (by
                apply List.mem_append_left
                exact tailEvidence)
      · exact headFinal candidate (by
          simp [GeneratedMatcherClause.unificationVars,
            GeneratedChecks.unificationVars, headHardMember])
      · exact tailScoped candidate (by
          simp [GeneratedMatcherClauses.unificationVars,
            GeneratedChecks.unificationVars, tailHardMember])
      · exact headFinal candidate (by
          simp [GeneratedMatcherClause.unificationVars,
            GeneratedChecks.unificationVars, headPendingMember])
      · exact tailScoped candidate (by
          simp [GeneratedMatcherClauses.unificationVars,
            GeneratedChecks.unificationVars, tailPendingMember])

private theorem matcherArm_coherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    {context : Context} {captures : List Ty} {matcherTarget : Ty}
    {holes : List Dual} {arm : MatcherArm}
    {outerStart start leftNext rightNext : Supply}
    {left right : GeneratedChecks}
    (bodyProperty : FullM4FuelPairProperty arm.body)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : outerStart.WellFormedFor context)
    (capturesSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList captures))
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (holesSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars holes))
    (outerToStart : outerStart.Le start)
    (leftDerivation : MatcherArmElaboratesUsing
      (M4.ElaboratesFuel signature leftFuel) DPatElaborates signature context
      captures matcherTarget holes arm start left leftNext)
    (rightDerivation : MatcherArmElaboratesUsing
      (M4.ElaboratesFuel signature rightFuel) DPatElaborates signature context
      captures matcherTarget holes arm start right rightNext) :
    Nonempty (SupportedChecksPair start leftNext rightNext left right) := by
  cases leftDerivation with
  | @mk header body start leftHeader leftAfter leftBody leftNext
      leftHeaderDerivation leftBodyDerivation =>
      cases rightDerivation with
      | @mk _ _ _ rightHeader rightAfter rightBody rightNext
          rightHeaderDerivation rightBodyDerivation =>
          obtain ⟨rfl, rfl⟩ := dpat_deterministic leftHeaderDerivation
            rightHeaderDerivation
          have startToAfter := leftHeaderDerivation.supply_le_next
          have headerSupport := leftHeaderDerivation.supportProvenance
            signatureWellFormed targetSupport outerToStart
          have bindingsSupport : VariablesSupportProvenance context outerStart
              leftAfter (Ty.unificationVarsList leftHeader.bindings) := by
            intro candidate member
            exact headerSupport candidate (by
              simp [GeneratedDPat.unificationVars, member])
          have capturesContextSupport := Pattern.extendContext_support
            capturesSupport
          have bindingsInCaptured :=
            VariablesSupportProvenance.extend_context captures bindingsSupport
          have localContextSupport := Pattern.extendContext_support
            bindingsInCaptured
          have bodyContextSupport : VariablesSupportProvenance context outerStart
              leftAfter
              (Pattern.extendContext leftHeader.bindings
                (Pattern.extendContext captures context)).unificationVars := by
            intro candidate member
            rcases localContextSupport candidate member with inherited | fresh
            · exact (capturesContextSupport.extend_finish startToAfter)
                candidate inherited
            · exact Or.inr fresh
          have outerToAfter := Supply.le_trans outerToStart startToAfter
          have bodyWellFormed := Supply.WellFormedFor.of_contextSupport
            wellFormed outerToAfter bodyContextSupport
          have holesAtAfter := holesSupport.extend_finish startToAfter
          have expectedSupport := holeProductTarget_support holesAtAfter
          have expectedBelow : VariablesBelowSupply leftAfter
              (DataTypes.list (holeProductTarget holes)).unificationVars := by
            apply VariablesSupportProvenance.belowFinish wellFormed outerToAfter
            simpa [DataTypes.list, Ty.unificationVars,
              Ty.unificationVarsList] using expectedSupport
          obtain ⟨bodyResult⟩ := checkedExpression_coherence bodyProperty
            signatureWellFormed bodyWellFormed leftBodyDerivation
            rightBodyDerivation (fun fresh => expectedBelow.avoidsFresh fresh)
          cases bodyResult.next_eq
          have headerHardBelow : VariablesBelowSupply leftAfter
              (TypePM.unificationVars leftHeader.hard) := by
            apply VariablesSupportProvenance.belowFinish wellFormed outerToAfter
            intro candidate member
            exact headerSupport candidate (by
              simp [GeneratedDPat.unificationVars, member])
          have headerAvoids : EquationsAvoid bodyResult.certificate.hidden
              leftHeader.hard :=
            headerHardBelow.avoidsFresh bodyResult.certificate.hiddenFresh
          exact ⟨
            { next_eq := rfl
              certificate := by
                let bodyWide := bodyResult.certificate.rebase
                  (bodyResult.certificate.hiddenFresh.widen startToAfter
                    (Supply.le_refl leftNext))
                simpa [checksGenerated, Generated.fromLet,
                  GeneratedChecks.append, bodyWide,
                  SupportedEntailedAlignmentCertificate.rebase] using
                  bodyWide.letBody leftHeader.hard headerAvoids }⟩

private theorem matcherArms_coherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    {context : Context} {captures : List Ty} {matcherTarget : Ty}
    {holes : List Dual} {arms : List MatcherArm}
    {outerStart start leftNext rightNext : Supply}
    {left right : GeneratedArms}
    (bodyProperties : ∀ arm, arm ∈ arms →
      FullM4FuelPairProperty arm.body)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : outerStart.WellFormedFor context)
    (capturesSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList captures))
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (holesSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars holes))
    (outerToStart : outerStart.Le start)
    (leftDerivation : MatcherArmsElaborateUsing
      (M4.ElaboratesFuel signature leftFuel) DPatElaborates signature context
      captures matcherTarget holes arms start left leftNext)
    (rightDerivation : MatcherArmsElaborateUsing
      (M4.ElaboratesFuel signature rightFuel) DPatElaborates signature context
      captures matcherTarget holes arms start right rightNext) :
    Nonempty (SupportedChecksPair start leftNext rightNext left.checks right.checks) := by
  induction leftDerivation generalizing right rightNext with
  | nil =>
      cases rightDerivation
      exact ⟨SupportedChecksPair.mk rfl
        (SupportedEntailedAlignmentCertificate.refl _ _ _)⟩
  | @cons arm arms start leftHead leftAfter leftTail leftNext head tail induction =>
      cases rightDerivation with
      | @cons _ _ _ rightHead rightAfter rightTail rightNext rightHeadDerivation
          rightTailDerivation =>
          obtain ⟨headResult⟩ := matcherArm_coherence
            (bodyProperties arm (by simp)) signatureWellFormed wellFormed
            capturesSupport targetSupport holesSupport outerToStart head
            rightHeadDerivation
          cases headResult.next_eq
          have startToAfter := head.supply_le_next
            (fun child => child.supply_le_next) DPatElaborates.supply_le_next
          obtain ⟨tailResult⟩ := induction
            (fun tailArm member => bodyProperties tailArm (by simp [member]))
            (capturesSupport.extend_finish startToAfter)
            (targetSupport.extend_finish startToAfter)
            (holesSupport.extend_finish startToAfter)
            (Supply.le_trans outerToStart startToAfter) rightTailDerivation
          cases tailResult.next_eq
          have afterToNext := tail.supply_le_next
            (fun child => child.supply_le_next) DPatElaborates.supply_le_next
          have contextBelow := contextBelowSupply (wellFormed.mono outerToStart)
          have capturesBelow := VariablesSupportProvenance.belowFinish
            wellFormed outerToStart capturesSupport
          have targetBelow := VariablesSupportProvenance.belowFinish
            wellFormed outerToStart targetSupport
          have holesBelow := VariablesSupportProvenance.belowFinish
            wellFormed outerToStart holesSupport
          have leftHeadScoped := matcherArm_scopedByBoundary
            signatureWellFormed contextBelow.asScoped capturesBelow.asScoped
            targetBelow.asScoped holesBelow.asScoped
            (Supply.le_refl start) head
          have rightHeadScoped := matcherArm_scopedByBoundary
            signatureWellFormed contextBelow.asScoped capturesBelow.asScoped
            targetBelow.asScoped holesBelow.asScoped
            (Supply.le_refl start) rightHeadDerivation
          have leftTailScoped := matcherArms_scopedByBoundary
            signatureWellFormed contextBelow.asScoped capturesBelow.asScoped
            targetBelow.asScoped holesBelow.asScoped
            (Supply.le_refl leftAfter) tail
          have rightTailScoped := matcherArms_scopedByBoundary
            signatureWellFormed contextBelow.asScoped capturesBelow.asScoped
            targetBelow.asScoped holesBelow.asScoped
            (Supply.le_refl leftAfter) rightTailDerivation
          exact ⟨
            { next_eq := rfl
              certificate := appendSequentialChecks headResult.certificate
                tailResult.certificate startToAfter afterToNext
                (VariablesScopedBy.avoids_earlier
                  headResult.certificate.hiddenFresh leftTailScoped
                  (Supply.le_refl start) (Supply.le_refl leftAfter))
                (VariablesScopedBy.avoids_earlier
                  headResult.certificate.hiddenFresh rightTailScoped
                  (Supply.le_refl start) (Supply.le_refl leftAfter))
                (VariablesScopedBy.avoids_later leftHeadScoped
                  tailResult.certificate.hiddenFresh (Supply.le_refl start)
                  startToAfter (Supply.le_refl leftAfter))
                (VariablesScopedBy.avoids_later rightHeadScoped
                  tailResult.certificate.hiddenFresh (Supply.le_refl start)
                  startToAfter (Supply.le_refl leftAfter)) }⟩

private structure SupportedClausePair
    (start leftNext rightNext : Supply)
    (left right : GeneratedMatcherClause) where
  next_eq : leftNext = rightNext
  holes_eq : left.holes = right.holes
  evidence_eq : left.evidence = right.evidence
  certificate : SupportedEntailedAlignmentCertificate start leftNext
    (checksGenerated left.checks) (checksGenerated right.checks)
  evidenceAvoid : VariablesAvoid certificate.hidden
    (match left.evidence with
     | none => []
     | some evidence => evidence.unificationVars)

private theorem matcherClause_coherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    {context : Context} {matcherTarget : Ty} {clause : MatcherClause}
    {outerStart start leftNext rightNext : Supply}
    {left right : GeneratedMatcherClause}
    (nextProperty : FullM4FuelPairProperty clause.nextMatchers)
    (tupleProperties : ∀ items, clause.nextMatchers = .tuple items →
      ∀ item, item ∈ items → FullM4FuelPairProperty item)
    (armProperties : ∀ arm, arm ∈ clause.arms →
      FullM4FuelPairProperty arm.body)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : outerStart.WellFormedFor context)
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (outerToStart : outerStart.Le start)
    (leftDerivation : MatcherClauseElaboratesUsing
      (M4.ElaboratesFuel signature leftFuel) PPatElaborates DPatElaborates
      signature context matcherTarget clause start left leftNext)
    (rightDerivation : MatcherClauseElaboratesUsing
      (M4.ElaboratesFuel signature rightFuel) PPatElaborates DPatElaborates
      signature context matcherTarget clause start right rightNext) :
    Nonempty (SupportedClausePair start leftNext rightNext left right) := by
  cases leftDerivation with
  | @mk header nextMatchers arms start leftHeader leftAfterHeader leftNextChecks
      leftAfterNext leftArms leftNext shape leftHeaderDerivation
      leftNextDerivation leftArmsDerivation =>
      cases rightDerivation with
      | @mk _ _ _ _ rightHeader rightAfterHeader rightNextChecks rightAfterNext
          rightArms rightNext rightShape rightHeaderDerivation
          rightNextDerivation rightArmsDerivation =>
          obtain ⟨rfl, rfl⟩ := ppat_deterministic leftHeaderDerivation
            rightHeaderDerivation
          have startToHeader := leftHeaderDerivation.supply_le_next
          have headerSupport := leftHeaderDerivation.supportProvenance
            (expectedCapability := none) signatureWellFormed targetSupport
            (VariablesSupportProvenance.nil context outerStart start)
            outerToStart
          have holesSupport : VariablesSupportProvenance context outerStart
              leftAfterHeader (dualUnificationVars leftHeader.holes) := by
            intro candidate member
            exact headerSupport candidate (by
              simp [GeneratedPPat.unificationVars, member])
          have capturesSupport : VariablesSupportProvenance context outerStart
              leftAfterHeader (Ty.unificationVarsList leftHeader.captures) := by
            intro candidate member
            exact headerSupport candidate (by
              simp [GeneratedPPat.unificationVars, member])
          have capturedContextSupport := Pattern.extendContext_support
            capturesSupport
          have outerToHeader := Supply.le_trans outerToStart startToHeader
          have capturedWellFormed := Supply.WellFormedFor.of_contextSupport
            wellFormed outerToHeader capturedContextSupport
          have holesInCaptured :=
            VariablesSupportProvenance.extend_context leftHeader.captures
              holesSupport
          have holesBelow : VariablesBelowSupply leftAfterHeader
              (dualUnificationVars leftHeader.holes) :=
            VariablesSupportProvenance.belowFinish wellFormed outerToHeader
              holesSupport
          obtain ⟨nextResult⟩ := nextMatchers_coherence nextProperty
            (fun items equality => tupleProperties items (by
              simpa using equality)) signatureWellFormed capturedWellFormed
            holesBelow leftNextDerivation rightNextDerivation
          cases nextResult.next_eq
          have headerToNext := leftNextDerivation.supply_le_next
            (fun child => child.supply_le_next)
          have outerToNext := Supply.le_trans outerToHeader headerToNext
          obtain ⟨armsResult⟩ := matcherArms_coherence armProperties
            signatureWellFormed wellFormed
            (capturesSupport.extend_finish headerToNext)
            (targetSupport.extend_finish
              (Supply.le_trans startToHeader headerToNext))
            (holesSupport.extend_finish headerToNext) outerToNext
            leftArmsDerivation rightArmsDerivation
          cases armsResult.next_eq
          have nextToFinish := leftArmsDerivation.supply_le_next
            (fun child => child.supply_le_next) DPatElaborates.supply_le_next
          have capturedBelow := contextBelowSupply capturedWellFormed
          have leftNextScoped := nextMatchers_scopedByBoundary
            signatureWellFormed (Supply.le_refl leftAfterHeader)
            capturedBelow.asScoped holesBelow.asScoped leftNextDerivation
          have rightNextScoped := nextMatchers_scopedByBoundary
            signatureWellFormed (Supply.le_refl leftAfterHeader)
            capturedBelow.asScoped holesBelow.asScoped rightNextDerivation
          have contextBelow := contextBelowSupply (wellFormed.mono outerToHeader)
          have capturesBelow := VariablesSupportProvenance.belowFinish
            wellFormed outerToHeader capturesSupport
          have targetBelow := VariablesSupportProvenance.belowFinish
            wellFormed outerToHeader
            (targetSupport.extend_finish startToHeader)
          have leftArmsScoped := matcherArms_scopedByBoundary
            signatureWellFormed contextBelow.asScoped capturesBelow.asScoped
            targetBelow.asScoped holesBelow.asScoped
            (Supply.le_refl leftAfterNext) leftArmsDerivation
          have rightArmsScoped := matcherArms_scopedByBoundary
            signatureWellFormed contextBelow.asScoped capturesBelow.asScoped
            targetBelow.asScoped holesBelow.asScoped
            (Supply.le_refl leftAfterNext) rightArmsDerivation
          have combined := appendSequentialChecks nextResult.certificate
            armsResult.certificate headerToNext nextToFinish
            (VariablesScopedBy.avoids_earlier
              nextResult.certificate.hiddenFresh leftArmsScoped
              (Supply.le_refl leftAfterHeader)
              (Supply.le_refl leftAfterNext))
            (VariablesScopedBy.avoids_earlier
              nextResult.certificate.hiddenFresh rightArmsScoped
              (Supply.le_refl leftAfterHeader)
              (Supply.le_refl leftAfterNext))
            (VariablesScopedBy.avoids_later leftNextScoped
              armsResult.certificate.hiddenFresh
              (Supply.le_refl leftAfterHeader) headerToNext
              (Supply.le_refl leftAfterNext))
            (VariablesScopedBy.avoids_later rightNextScoped
              armsResult.certificate.hiddenFresh
              (Supply.le_refl leftAfterHeader) headerToNext
              (Supply.le_refl leftAfterNext))
          have headerScoped := ppat_scopedByBoundary signatureWellFormed
            (VariablesSupportProvenance.belowFinish wellFormed outerToStart
              targetSupport).asScoped
            (by intro candidate member; simp at member)
            (Supply.le_refl start) leftHeaderDerivation
          have headerHardBelow : VariablesBelowSupply leftAfterHeader
              (TypePM.unificationVars leftHeader.hard) := by
            apply VariablesScopedBy.belowFinish _ (Supply.le_refl start)
              startToHeader
            intro candidate member
            exact headerScoped candidate (by
              simp [GeneratedPPat.unificationVars, member])
          have headerAvoids : EquationsAvoid combined.hidden leftHeader.hard :=
            headerHardBelow.avoidsFresh combined.hiddenFresh
          have evidenceBelow : VariablesBelowSupply leftAfterHeader
              (match leftHeader.evidence with
               | none => []
               | some evidence => evidence.unificationVars) := by
            intro candidate member
            apply VariablesScopedBy.belowFinish headerScoped
              (Supply.le_refl start) startToHeader candidate
            simp only [GeneratedPPat.unificationVars, List.mem_append]
            exact Or.inl (Or.inr member)
          have evidenceAvoid : VariablesAvoid combined.hidden
              (match leftHeader.evidence with
               | none => []
               | some evidence => evidence.unificationVars) :=
            evidenceBelow.avoidsFresh combined.hiddenFresh
          let combinedWide := combined.rebase
            (combined.hiddenFresh.widen startToHeader
              (Supply.le_refl leftNext))
          let bodyCertificate :=
            combinedWide.letBody leftHeader.hard headerAvoids
          have leftChecksEq : Generated.fromLet leftHeader.hard
                (checksGenerated (leftNextChecks.append leftArms.checks)) =
              checksGenerated
                ⟨leftHeader.hard ++ leftNextChecks.hard ++ leftArms.checks.hard,
                  leftNextChecks.pending ++ leftArms.checks.pending⟩ := by
            simp [Generated.fromLet, checksGenerated, GeneratedChecks.append,
              List.append_assoc]
          have rightChecksEq : Generated.fromLet leftHeader.hard
                (checksGenerated (rightNextChecks.append rightArms.checks)) =
              checksGenerated
                ⟨leftHeader.hard ++ rightNextChecks.hard ++ rightArms.checks.hard,
                  rightNextChecks.pending ++ rightArms.checks.pending⟩ := by
            simp [Generated.fromLet, checksGenerated, GeneratedChecks.append,
              List.append_assoc]
          let finalCertificate := supportedCertificateTransport leftChecksEq
            rightChecksEq bodyCertificate
          exact ⟨
            { next_eq := rfl
              holes_eq := rfl
              evidence_eq := rfl
              evidenceAvoid := by
                rw [show finalCertificate.hidden = combined.hidden by
                  simp [finalCertificate, bodyCertificate, combinedWide,
                    SupportedEntailedAlignmentCertificate.letBody,
                    SupportedEntailedAlignmentCertificate.underFrame,
                    SupportedEntailedAlignmentCertificate.rebase]]
                exact evidenceAvoid
              certificate := finalCertificate }⟩

private structure SupportedClausesPair
    (start leftNext rightNext : Supply)
    (left right : GeneratedMatcherClauses) where
  next_eq : leftNext = rightNext
  evidences_eq : left.evidences = right.evidences
  certificate : SupportedEntailedAlignmentCertificate start leftNext
    (checksGenerated left.checks) (checksGenerated right.checks)
  evidencesAvoid : VariablesAvoid certificate.hidden
    (Cap.unificationVarsList left.evidences)

private theorem variablesAvoid_append_both
    {firstHidden secondHidden firstObserved secondObserved :
      List UnificationVar}
    (firstOwn : VariablesAvoid firstHidden firstObserved)
    (secondOwn : VariablesAvoid secondHidden secondObserved)
    (secondAvoidsFirst : VariablesAvoid firstHidden secondObserved)
    (firstAvoidsSecond : VariablesAvoid secondHidden firstObserved) :
    VariablesAvoid (firstHidden ++ secondHidden)
      (firstObserved ++ secondObserved) := by
  intro candidate observed forbidden
  rcases List.mem_append.mp observed with firstMember | secondMember
  · rcases List.mem_append.mp forbidden with firstForbidden | secondForbidden
    · exact firstOwn candidate firstMember firstForbidden
    · exact firstAvoidsSecond candidate firstMember secondForbidden
  · rcases List.mem_append.mp forbidden with firstForbidden | secondForbidden
    · exact secondAvoidsFirst candidate secondMember firstForbidden
    · exact secondOwn candidate secondMember secondForbidden

private theorem evidenceMap_member
    {producer : Cap} {evidences : List Cap} {candidate : UnificationVar}
    (member : candidate ∈ TypePM.unificationVars
      (evidences.map (fun evidence => .cap producer evidence))) :
    candidate ∈ producer.unificationVars ∨
      candidate ∈ Cap.unificationVarsList evidences := by
  induction evidences with
  | nil => simp [TypePM.unificationVars] at member
  | cons evidence evidences induction =>
      simp only [List.map_cons, TypePM.unificationVars,
        List.mem_append,
        Equation.unificationVars] at member
      rcases member with headMember | tailMember
      · simp only [Cap.unificationVarsList, List.mem_append]
        rcases headMember with producerMember | evidenceMember
        · exact Or.inl producerMember
        · exact Or.inr (Or.inl evidenceMember)
      · rcases induction tailMember with producerMember | evidenceMember
        · exact Or.inl producerMember
        · exact Or.inr (by
            simp only [Cap.unificationVarsList, List.mem_append]
            exact Or.inr evidenceMember)

private theorem evidenceEquations_avoid
    {hidden : List UnificationVar} {producer : Cap} {evidences : List Cap}
    (producerAvoid : VariablesAvoid hidden producer.unificationVars)
    (evidencesAvoid : VariablesAvoid hidden
      (Cap.unificationVarsList evidences)) :
    EquationsAvoid hidden (evidenceEquations producer evidences) := by
  intro candidate observed forbidden
  cases evidences with
  | nil =>
      apply producerAvoid candidate _ forbidden
      simpa [evidenceEquations, TypePM.unificationVars,
        Equation.unificationVars, Cap.unificationVars] using observed
  | cons evidence evidences =>
      have split : candidate ∈ producer.unificationVars ∨
          candidate ∈ Cap.unificationVarsList (evidence :: evidences) := by
        exact evidenceMap_member (by
          simpa [evidenceEquations] using observed)
      rcases split with producerMember | evidenceMember
      · exact producerAvoid candidate producerMember forbidden
      · exact evidencesAvoid candidate evidenceMember forbidden

private theorem matcherClauses_coherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    {context : Context} {matcherTarget : Ty} {clauses : List MatcherClause}
    {outerStart start leftNext rightNext : Supply}
    {left right : GeneratedMatcherClauses}
    (nextProperties : ∀ clause, clause ∈ clauses →
      FullM4FuelPairProperty clause.nextMatchers)
    (tupleProperties : ∀ clause, clause ∈ clauses →
      ∀ items, clause.nextMatchers = .tuple items →
        ∀ item, item ∈ items → FullM4FuelPairProperty item)
    (armProperties : ∀ clause, clause ∈ clauses →
      ∀ arm, arm ∈ clause.arms → FullM4FuelPairProperty arm.body)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : outerStart.WellFormedFor context)
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (outerToStart : outerStart.Le start)
    (leftDerivation : MatcherClausesElaborateUsing
      (M4.ElaboratesFuel signature leftFuel) PPatElaborates DPatElaborates
      signature context matcherTarget clauses start left leftNext)
    (rightDerivation : MatcherClausesElaborateUsing
      (M4.ElaboratesFuel signature rightFuel) PPatElaborates DPatElaborates
      signature context matcherTarget clauses start right rightNext) :
    Nonempty (SupportedClausesPair start leftNext rightNext left right) := by
  induction leftDerivation generalizing right rightNext with
  | nil =>
      cases rightDerivation
      exact ⟨
        { next_eq := rfl
          evidences_eq := rfl
          certificate := SupportedEntailedAlignmentCertificate.refl _ _ _
          evidencesAvoid := by
            simp [Cap.unificationVarsList, VariablesAvoid] }⟩
  | @cons clause clauses start leftHead leftAfter leftTail leftNext head tail
      induction =>
      cases rightDerivation with
      | @cons _ _ _ rightHead rightAfter rightTail rightNext rightHeadDerivation
          rightTailDerivation =>
          obtain ⟨headResult⟩ := matcherClause_coherence
            (nextProperties clause (by simp))
            (tupleProperties clause (by simp))
            (armProperties clause (by simp)) signatureWellFormed wellFormed
            targetSupport outerToStart head rightHeadDerivation
          cases headResult.next_eq
          have startToAfter := head.supply_le_next
            (fun child => child.supply_le_next) PPatElaborates.supply_le_next
            DPatElaborates.supply_le_next
          obtain ⟨tailResult⟩ := induction
            (fun tailClause member => nextProperties tailClause (by
              simp [member]))
            (fun tailClause member => tupleProperties tailClause (by
              simp [member]))
            (fun tailClause member => armProperties tailClause (by
              simp [member]))
            (targetSupport.extend_finish startToAfter)
            (Supply.le_trans outerToStart startToAfter) rightTailDerivation
          cases tailResult.next_eq
          have afterToNext := tail.supply_le_next
            (fun child => child.supply_le_next) PPatElaborates.supply_le_next
            DPatElaborates.supply_le_next
          have contextBelow := contextBelowSupply (wellFormed.mono outerToStart)
          have targetBelow := VariablesSupportProvenance.belowFinish wellFormed
            outerToStart targetSupport
          have leftHeadAllScoped := matcherClause_scopedByBoundary
            signatureWellFormed contextBelow.asScoped targetBelow.asScoped
            (Supply.le_refl start) head
          have rightHeadAllScoped := matcherClause_scopedByBoundary
            signatureWellFormed contextBelow.asScoped targetBelow.asScoped
            (Supply.le_refl start) rightHeadDerivation
          have leftTailAllScoped := matcherClauses_scopedByBoundary
            signatureWellFormed contextBelow.asScoped targetBelow.asScoped
            (Supply.le_refl leftAfter) tail
          have rightTailAllScoped := matcherClauses_scopedByBoundary
            signatureWellFormed contextBelow.asScoped targetBelow.asScoped
            (Supply.le_refl leftAfter) rightTailDerivation
          have leftHeadEvidenceScoped : VariablesScopedBy start start leftAfter
              (match leftHead.evidence with
               | none => []
               | some evidence => evidence.unificationVars) := by
            intro candidate member
            apply leftHeadAllScoped candidate
            simp only [GeneratedMatcherClause.unificationVars, List.mem_append]
            exact Or.inl (Or.inr member)
          have leftTailEvidenceScoped : VariablesScopedBy start leftAfter leftNext
              (Cap.unificationVarsList leftTail.evidences) := by
            intro candidate member
            exact leftTailAllScoped candidate (by
              simp [GeneratedMatcherClauses.unificationVars, member])
          have leftHeadScoped : VariablesScopedBy start start leftAfter
              (checksGenerated leftHead.checks).unificationVars := by
            intro candidate member
            have checksMember : candidate ∈ leftHead.checks.unificationVars := by
              have observed : candidate ∈ unificationVars leftHead.checks.hard ∨
                  candidate ∈ pendingUnificationVars leftHead.checks.pending := by
                simpa [checksGenerated, Generated.unificationVars,
                  Ty.unificationVars] using member
              simpa only [GeneratedChecks.unificationVars, List.mem_append]
                using observed
            apply leftHeadAllScoped candidate
            simp only [GeneratedMatcherClause.unificationVars, List.mem_append]
            exact Or.inr checksMember
          have rightHeadScoped : VariablesScopedBy start start leftAfter
              (checksGenerated rightHead.checks).unificationVars := by
            intro candidate member
            have checksMember : candidate ∈ rightHead.checks.unificationVars := by
              have observed : candidate ∈ unificationVars rightHead.checks.hard ∨
                  candidate ∈ pendingUnificationVars rightHead.checks.pending := by
                simpa [checksGenerated, Generated.unificationVars,
                  Ty.unificationVars] using member
              simpa only [GeneratedChecks.unificationVars, List.mem_append]
                using observed
            apply rightHeadAllScoped candidate
            simp only [GeneratedMatcherClause.unificationVars, List.mem_append]
            exact Or.inr checksMember
          have leftTailScoped : VariablesScopedBy start leftAfter leftNext
              (checksGenerated leftTail.checks).unificationVars := by
            intro candidate member
            have checksMember : candidate ∈ leftTail.checks.unificationVars := by
              have observed : candidate ∈ unificationVars leftTail.checks.hard ∨
                  candidate ∈ pendingUnificationVars leftTail.checks.pending := by
                simpa [checksGenerated, Generated.unificationVars,
                  Ty.unificationVars] using member
              simpa only [GeneratedChecks.unificationVars, List.mem_append]
                using observed
            apply leftTailAllScoped candidate
            simp only [GeneratedMatcherClauses.unificationVars, List.mem_append]
            exact Or.inr checksMember
          have rightTailScoped : VariablesScopedBy start leftAfter leftNext
              (checksGenerated rightTail.checks).unificationVars := by
            intro candidate member
            have checksMember : candidate ∈ rightTail.checks.unificationVars := by
              have observed : candidate ∈ unificationVars rightTail.checks.hard ∨
                  candidate ∈ pendingUnificationVars rightTail.checks.pending := by
                simpa [checksGenerated, Generated.unificationVars,
                  Ty.unificationVars] using member
              simpa only [GeneratedChecks.unificationVars, List.mem_append]
                using observed
            apply rightTailAllScoped candidate
            simp only [GeneratedMatcherClauses.unificationVars, List.mem_append]
            exact Or.inr checksMember
          let combined := appendSequentialChecks headResult.certificate
            tailResult.certificate startToAfter afterToNext
            (VariablesScopedBy.avoids_earlier
              headResult.certificate.hiddenFresh leftTailScoped
              (Supply.le_refl start) (Supply.le_refl leftAfter))
            (VariablesScopedBy.avoids_earlier
              headResult.certificate.hiddenFresh rightTailScoped
              (Supply.le_refl start) (Supply.le_refl leftAfter))
            (VariablesScopedBy.avoids_later leftHeadScoped
              tailResult.certificate.hiddenFresh (Supply.le_refl start)
              startToAfter (Supply.le_refl leftAfter))
            (VariablesScopedBy.avoids_later rightHeadScoped
              tailResult.certificate.hiddenFresh (Supply.le_refl start)
              startToAfter (Supply.le_refl leftAfter))
          have evidencesEquality :
              (match leftHead.evidence with
               | some evidence => evidence :: leftTail.evidences
               | none => leftTail.evidences) =
              (match rightHead.evidence with
               | some evidence => evidence :: rightTail.evidences
               | none => rightTail.evidences) := by
            rw [headResult.evidence_eq, tailResult.evidences_eq]
          have tailEvidenceAvoidsHead : VariablesAvoid
              headResult.certificate.hidden
              (Cap.unificationVarsList leftTail.evidences) :=
            VariablesScopedBy.avoids_earlier
              headResult.certificate.hiddenFresh leftTailEvidenceScoped
              (Supply.le_refl start) (Supply.le_refl leftAfter)
          have headEvidenceAvoidsTail : VariablesAvoid
              tailResult.certificate.hidden
              (match leftHead.evidence with
               | none => []
               | some evidence => evidence.unificationVars) :=
            VariablesScopedBy.avoids_later leftHeadEvidenceScoped
              tailResult.certificate.hiddenFresh (Supply.le_refl start)
              startToAfter (Supply.le_refl leftAfter)
          have combinedHidden : combined.hidden =
              headResult.certificate.hidden ++
                tailResult.certificate.hidden := by
            simp [combined, appendSequentialChecks, appendChecksCertificate,
              supportedCertificateRetarget, supportedCertificateSingletonItems,
              SupportedItemsAlignmentCertificate.itemsTuple,
              SupportedItemsAlignmentCertificate.itemsCons,
              SupportedEntailedAlignmentCertificate.rebase]
          have evidencesAvoid : VariablesAvoid combined.hidden
              (Cap.unificationVarsList
                (match leftHead.evidence with
                 | some evidence => evidence :: leftTail.evidences
                 | none => leftTail.evidences)) := by
            rw [combinedHidden]
            cases evidenceCase : leftHead.evidence with
            | none =>
                simpa [evidenceCase, Cap.unificationVarsList] using
                  variablesAvoid_append_both headResult.evidenceAvoid
                    tailResult.evidencesAvoid tailEvidenceAvoidsHead
                    headEvidenceAvoidsTail
            | some evidence =>
                simpa [evidenceCase, Cap.unificationVarsList] using
                  variablesAvoid_append_both headResult.evidenceAvoid
                    tailResult.evidencesAvoid tailEvidenceAvoidsHead
                    headEvidenceAvoidsTail
          exact ⟨
            { next_eq := rfl
              evidences_eq := evidencesEquality
              certificate := combined
              evidencesAvoid := evidencesAvoid }⟩

private theorem supportedMatcher
    {clauses : List MatcherClause}
    (nextProperties : ∀ clause, clause ∈ clauses →
      FullM4FuelPairProperty clause.nextMatchers)
    (tupleProperties : ∀ clause, clause ∈ clauses →
      ∀ items, clause.nextMatchers = .tuple items →
        ∀ item, item ∈ items → FullM4FuelPairProperty item)
    (armProperties : ∀ clause, clause ∈ clauses →
      ∀ arm, arm ∈ clause.arms → FullM4FuelPairProperty arm.body) :
    SupportedM4FuelPairProperty (.matcher clauses) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          cases leftElaboration with
          | @mk leftClauses _ leftChecked leftClausesDerivation =>
              cases rightElaboration with
              | @mk rightClauses _ rightChecked
                  rightClausesDerivation =>
                  let afterRoot : Supply :=
                    ⟨start.ty + 1, start.cap + 1⟩
                  have startToRoot : start.Le afterRoot := by
                    simp [afterRoot, Supply.Le]
                  have targetAtRoot : VariablesSupportProvenance context start
                      afterRoot (Ty.unificationVars (.var ⟨start.ty⟩)) :=
                    (freshTy_support context start).extend_finish (by
                      simp [afterRoot, Supply.Le, Supply.nextTy])
                  obtain ⟨clausesResult⟩ := matcherClauses_coherence
                    nextProperties tupleProperties armProperties
                    signatureWellFormed wellFormed targetAtRoot startToRoot
                    leftClausesDerivation rightClausesDerivation
                  cases clausesResult.next_eq
                  have rootToNext := leftClausesDerivation.supply_le_next
                    (fun child => child.supply_le_next)
                    PPatElaborates.supply_le_next DPatElaborates.supply_le_next
                  have producerAtRoot : VariablesSupportProvenance context start
                      afterRoot (Cap.unificationVars (.var ⟨start.cap⟩)) :=
                    (freshCap_support context start).extend_finish (by
                      simp [afterRoot, Supply.Le])
                  have producerBelow : VariablesBelowSupply afterRoot
                      (Cap.unificationVars (.var ⟨start.cap⟩)) :=
                    VariablesSupportProvenance.belowFinish wellFormed
                      startToRoot producerAtRoot
                  have targetBelow : VariablesBelowSupply afterRoot
                      (Ty.unificationVars (.var ⟨start.ty⟩)) :=
                    VariablesSupportProvenance.belowFinish wellFormed
                      startToRoot targetAtRoot
                  have producerAvoid : VariablesAvoid
                      clausesResult.certificate.hidden
                      (Cap.unificationVars (.var ⟨start.cap⟩)) :=
                    producerBelow.avoidsFresh
                      clausesResult.certificate.hiddenFresh
                  have effectsAvoid : EquationsAvoid
                      clausesResult.certificate.hidden
                      (evidenceEquations (.var ⟨start.cap⟩)
                        leftClauses.evidences) :=
                    evidenceEquations_avoid producerAvoid
                      clausesResult.evidencesAvoid
                  have matcherTargetAvoid : TypeAvoids
                      clausesResult.certificate.hidden
                      (.matcher (.var ⟨start.cap⟩) (.var ⟨start.ty⟩)) := by
                    intro candidate observed forbidden
                    have split : candidate ∈
                          Cap.unificationVars (.var ⟨start.cap⟩) ∨
                        candidate ∈ Ty.unificationVars (.var ⟨start.ty⟩) := by
                      simpa [Ty.unificationVars] using observed
                    rcases split with producerMember | targetMember
                    · exact producerAvoid candidate producerMember forbidden
                    · exact targetBelow.avoidsFresh
                        clausesResult.certificate.hiddenFresh candidate
                        targetMember forbidden
                  let withEffects := clausesResult.certificate.letBody
                    (evidenceEquations (.var ⟨start.cap⟩)
                      leftClauses.evidences) effectsAvoid
                  let atRoot := withEffects.rebase
                    (clausesResult.certificate.hiddenFresh.widen startToRoot
                      (Supply.le_refl leftNext))
                  have targetEmpty :
                      (checksGenerated leftClauses.checks).target.unificationVars =
                        [] := by
                    simp [checksGenerated, Ty.unificationVars]
                  have rightTargetEmpty :
                      (checksGenerated rightClauses.checks).target.unificationVars =
                        [] := by
                    simp [checksGenerated, Ty.unificationVars]
                  have atRootTargetAvoid : TypeAvoids atRoot.hidden
                      (.matcher (.var ⟨start.cap⟩) (.var ⟨start.ty⟩)) := by
                    simpa [atRoot, withEffects,
                      SupportedEntailedAlignmentCertificate.rebase,
                      SupportedEntailedAlignmentCertificate.letBody,
                      SupportedEntailedAlignmentCertificate.underFrame] using
                      matcherTargetAvoid
                  let finalCertificate := supportedCertificateRetarget atRoot
                    (.matcher (.var ⟨start.cap⟩) (.var ⟨start.ty⟩))
                    (by simp [Generated.fromLet,
                      checksGenerated, Ty.unificationVars])
                    (by simp [Generated.fromLet,
                      checksGenerated, Ty.unificationVars])
                    atRootTargetAvoid
                  exact ⟨
                    { next_eq := rfl
                      certificate := by
                        simpa [finalCertificate,
                          supportedCertificateRetarget, atRoot, withEffects,
                          retargetGenerated, Generated.fromLet,
                          checksGenerated, clausesResult.evidences_eq] using
                          finalCertificate }⟩

private theorem expr_complexity_lt_list_of_mem
    {expression : Expr} {expressions : List Expr}
    (member : expression ∈ expressions) :
    expression.complexity < Expr.listComplexity expressions := by
  induction expressions with
  | nil => simp at member
  | cons head tail induction =>
      simp only [Expr.listComplexity_cons]
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst expression
        omega
      · have := induction member
        omega

private theorem arm_complexity_lt_list_of_mem
    {arm : MatcherArm} {arms : List MatcherArm} (member : arm ∈ arms) :
    arm.complexity < MatcherArm.listComplexity arms := by
  induction arms with
  | nil => simp at member
  | cons head tail induction =>
      simp only [MatcherArm.listComplexity_cons]
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst arm
        omega
      · have := induction member
        omega

private theorem clause_complexity_lt_list_of_mem
    {clause : MatcherClause} {clauses : List MatcherClause}
    (member : clause ∈ clauses) :
    clause.complexity < MatcherClause.listComplexity clauses := by
  induction clauses with
  | nil => simp at member
  | cons head tail induction =>
      simp only [MatcherClause.listComplexity_cons]
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst clause
        omega
      · have := induction member
        omega

/-- Matcher-literal constructor-local coherence, including all next-matcher
and arm-body expression positions. -/
theorem matcherCoherenceStep : MatcherCoherenceStep := by
  intro clauses induction
  apply SupportedM4FuelPairProperty.toFull
  apply supportedMatcher
  · intro clause clauseMember
    apply induction clause.nextMatchers
    have clauseBound := clause_complexity_lt_list_of_mem clauseMember
    cases clause with
    | mk header nextMatchers arms =>
        simp only [Expr.complexity_matcher, MatcherClause.complexity_mk,
          MatcherClause.nextMatchers] at *
        omega
  · intro clause clauseMember items equality item itemMember
    apply induction item
    have clauseBound := clause_complexity_lt_list_of_mem clauseMember
    have itemBound := expr_complexity_lt_list_of_mem itemMember
    cases clause with
    | mk header nextMatchers arms =>
        simp only [MatcherClause.nextMatchers] at equality
        subst nextMatchers
        simp only [Expr.complexity_matcher, MatcherClause.complexity_mk,
          Expr.complexity_tuple] at *
        omega
  · intro clause clauseMember arm armMember
    apply induction arm.body
    have clauseBound := clause_complexity_lt_list_of_mem clauseMember
    have armBound := arm_complexity_lt_list_of_mem armMember
    cases clause with
    | mk header nextMatchers arms =>
        cases arm with
        | mk armHeader body =>
            simp only [Expr.complexity_matcher, MatcherClause.complexity_mk,
              MatcherClause.arms, MatcherArm.complexity_mk,
              MatcherArm.body] at *
            omega

end TypePM.Source.M4.CompletenessArchitecture
