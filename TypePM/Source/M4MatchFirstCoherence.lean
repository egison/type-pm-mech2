import TypePM.Source.M4PatternCoherence

/-!
# Coherence for M4 ordered single-result matching

The target and matcher are elaborated once.  Each arm then contributes a
pattern block followed by its body block, and later bodies are constrained to
the first body's result type.  This file records the constructor-local
coherence proof in the same supported-certificate form as the other M4
constructors.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source
open MatchFirstTyping
open InterfaceAliasDecomposition.AliasFreshness

private def checksGenerated (hard : List Equation)
    (pending : List CheckObligation) : Generated :=
  ⟨.int, hard, pending⟩

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
        cases alias <;> cases generated <;> rfl
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

private def tailGenerated (tail : GeneratedTail) : Generated :=
  checksGenerated tail.hard tail.pending

private def fixedTypesGenerated (types : List Ty) : Generated :=
  ⟨.prod types, [], []⟩

private def armPatternGenerated (targetType matcherType : Ty)
    (pattern : GeneratedPattern) : Generated :=
  checksGenerated
    ([.ty pattern.dual.target targetType] ++ pattern.hard)
    (pattern.pending ++
      [⟨matcherType, .slot pattern.dual.capability targetType⟩])

private def checkedBodyGenerated (expected : Ty) (body : Generated) : Generated :=
  checksGenerated (body.hard ++ [.ty body.target expected]) body.pending

private def appendChecksGenerated (first second : Generated) : Generated :=
  checksGenerated (first.hard ++ second.hard)
    (first.pending ++ second.pending)

private def firstArmGenerated (targetType matcherType : Ty)
    (pattern : GeneratedPattern) (body : Generated)
    (tail : GeneratedTail) : Generated :=
  ⟨body.target,
    [.ty pattern.dual.target targetType] ++ pattern.hard ++ body.hard ++ tail.hard,
    pattern.pending ++
      [⟨matcherType, .slot pattern.dual.capability targetType⟩] ++
        body.pending ++ tail.pending⟩

private def matchFirstGenerated (target matcher : Generated)
    (arms : GeneratedArms) : Generated :=
  Generated.fromMatchFirst target matcher arms

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

private def itemsPair
    {start next : Supply}
    {leftHead rightHead leftTail rightTail : Generated}
    (head : SupportedEntailedAlignmentCertificate start next
      leftHead rightHead)
    (tail : SupportedEntailedAlignmentCertificate start next
      leftTail rightTail)
    (leftTailAvoids : GeneratedAvoids head.hidden leftTail)
    (rightTailAvoids : GeneratedAvoids head.hidden rightTail)
    (leftHeadAvoids : GeneratedAvoids tail.hidden leftHead)
    (rightHeadAvoids : GeneratedAvoids tail.hidden rightHead)
    (disjoint : ∀ candidate, candidate ∈ head.hidden →
      candidate ∉ tail.hidden) :
    SupportedItemsAlignmentCertificate start next
      (GeneratedItems.cons leftHead (GeneratedItems.singleton leftTail))
      (GeneratedItems.cons rightHead (GeneratedItems.singleton rightTail)) :=
  SupportedItemsAlignmentCertificate.itemsCons head
    (singletonItemsCertificate tail)
    (GeneratedItemsAvoid.singleton leftTailAvoids)
    (GeneratedItemsAvoid.singleton rightTailAvoids)
    leftHeadAvoids rightHeadAvoids disjoint

private def repackageItems
    {start next : Supply} {leftItems rightItems : GeneratedItems}
    {left right : Generated}
    (certificate : SupportedItemsAlignmentCertificate start next
      leftItems rightItems)
    (leftVars : left.unificationVars = leftItems.unificationVars)
    (rightVars : right.unificationVars = rightItems.unificationVars)
    (aligned : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll certificate.leftAliases left)
      (FreshAliasSequence.addAll certificate.rightAliases right)) :
    SupportedEntailedAlignmentCertificate start next left right :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := by simpa [leftVars] using certificate.leftScoped
    rightScoped := by simpa [rightVars] using certificate.rightScoped
    aligned := aligned }

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

private theorem generatedScoped
    {context : Context} {start finish : Supply} {generated : Generated}
    (support : GeneratedSupportProvenance context start finish generated) :
    VariablesScopedBy context.initialSupply start finish
      generated.unificationVars :=
  support.scopedByInitialSupply

private theorem sequentialAvoidance
    {context : Context} {start middle finish : Supply}
    (wellFormed : start.WellFormedFor context)
    {leftFirst rightFirst leftSecond rightSecond : Generated}
    (leftFirstSupport : GeneratedSupportProvenance context start middle leftFirst)
    (rightFirstSupport : GeneratedSupportProvenance context start middle rightFirst)
    (leftSecondSupport : GeneratedSupportProvenance context middle finish leftSecond)
    (rightSecondSupport : GeneratedSupportProvenance context middle finish rightSecond)
    {firstHidden secondHidden : List UnificationVar}
    (firstFresh : VariablesFreshIn start middle firstHidden)
    (secondFresh : VariablesFreshIn middle finish secondHidden)
    (startToMiddle : start.Le middle) :
    GeneratedAvoids firstHidden leftSecond ∧
      GeneratedAvoids firstHidden rightSecond ∧
      GeneratedAvoids secondHidden leftFirst ∧
      GeneratedAvoids secondHidden rightFirst := by
  exact ⟨
    VariablesScopedBy.avoids_earlier firstFresh
      (generatedScoped leftSecondSupport) wellFormed (Supply.le_refl middle),
    VariablesScopedBy.avoids_earlier firstFresh
      (generatedScoped rightSecondSupport) wellFormed (Supply.le_refl middle),
    VariablesScopedBy.avoids_later (generatedScoped leftFirstSupport)
      secondFresh wellFormed startToMiddle (Supply.le_refl middle),
    VariablesScopedBy.avoids_later (generatedScoped rightFirstSupport)
      secondFresh wellFormed startToMiddle (Supply.le_refl middle)⟩

/- The semantic repackaging lemmas below deliberately expose only generated
block structure.  They are shared by first and later arms and keep the list
induction independent of the expression syntax stored in patterns. -/

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

private theorem solves_prepend_patternEquation_iff
    {substitution : Subst} {left right : GeneratedPattern}
    {targetType : Ty}
    (dualEq : left.dual.target.apply substitution =
      right.dual.target.apply substitution)
    (hardEq : Solves substitution left.hard ↔
      Solves substitution right.hard) :
    Solves substitution
        ([.ty left.dual.target targetType] ++ left.hard) ↔
      Solves substitution
        ([.ty right.dual.target targetType] ++ right.hard) := by
  simp only [List.singleton_append, solves_cons, Equation.Holds]
  constructor <;> rintro ⟨equation, hard⟩
  · exact ⟨by simpa [dualEq] using equation, hardEq.mp hard⟩
  · exact ⟨by simpa [dualEq] using equation, hardEq.mpr hard⟩

private theorem pairedPatternTarget_components
    {targetType matcherType : Ty} {left right : GeneratedPattern}
    {substitution : Subst}
    (equality :
      (GeneratedItems.asTuple (GeneratedItems.cons
        (fixedTypesGenerated [targetType, matcherType])
        (GeneratedItems.singleton (patternAsGenerated left)))).target.apply
          substitution =
      (GeneratedItems.asTuple (GeneratedItems.cons
        (fixedTypesGenerated [targetType, matcherType])
        (GeneratedItems.singleton (patternAsGenerated right)))).target.apply
          substitution) :
    left.dual.capability.apply substitution.cap =
        right.dual.capability.apply substitution.cap ∧
      left.dual.target.apply substitution =
        right.dual.target.apply substitution := by
  simp only [GeneratedItems.asTuple, GeneratedItems.cons,
    GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
    patternAsGenerated, Ty.apply] at equality
  injection equality with outer
  injection outer with _fixed encoded
  exact encodedDual_components (List.cons.inj encoded).1

private theorem entailedPending_weaken
    {weaker stronger : List Equation} {left right : List CheckObligation}
    (pending : EntailedPendingEq weaker left right)
    (entails : ∀ substitution, Solves substitution stronger →
      Solves substitution weaker) :
    EntailedPendingEq stronger left right := by
  induction pending with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (head.weaken entails) induction

private theorem pendingAppendPatternSlot
    {reference : List Equation} {left right : List CheckObligation}
    {matcherType targetType : Ty} {leftCap rightCap : Cap}
    (pending : EntailedPendingEq reference left right)
    (capability : ∀ substitution, Solves substitution reference →
      leftCap.apply substitution.cap = rightCap.apply substitution.cap) :
    EntailedPendingEq reference
      (left ++ [⟨matcherType, .slot leftCap targetType⟩])
      (right ++ [⟨matcherType, .slot rightCap targetType⟩]) := by
  induction pending with
  | nil =>
      exact .cons (by
        intro substitution solved
        simp only [CheckObligation.apply, Ty.apply]
        rw [capability substitution solved]) .nil
  | cons head tail induction => exact .cons head induction

private theorem entailedArmPattern
    {targetType matcherType : Ty} {left right : GeneratedPattern}
    (aligned : EntailedGeneratedAlignment
      (GeneratedItems.asTuple (GeneratedItems.cons
        (fixedTypesGenerated [targetType, matcherType])
        (GeneratedItems.singleton (patternAsGenerated left))))
      (GeneratedItems.asTuple (GeneratedItems.cons
        (fixedTypesGenerated [targetType, matcherType])
        (GeneratedItems.singleton (patternAsGenerated right))))) :
    EntailedGeneratedAlignment
      (armPatternGenerated targetType matcherType left)
      (armPatternGenerated targetType matcherType right) := by
  have hard : HardEquivalent
      ([.ty left.dual.target targetType] ++ left.hard)
      ([.ty right.dual.target targetType] ++ right.hard) := by
    intro substitution
    have baseHard : Solves substitution left.hard ↔
        Solves substitution right.hard := by
      simpa [GeneratedItems.asTuple, GeneratedItems.cons,
        GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
        patternAsGenerated] using aligned.hardEquivalent substitution
    have components : Solves substitution left.hard →
        left.dual.target.apply substitution =
          right.dual.target.apply substitution := by
      intro solved
      exact (pairedPatternTarget_components
        (aligned.targetEntailed substitution (by
          simpa [GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil,
            fixedTypesGenerated, patternAsGenerated] using solved))).2
    constructor
    · intro solved
      exact (solves_prepend_patternEquation_iff
        (components ((solves_append substitution
          [.ty left.dual.target targetType] left.hard).mp solved).2)
        baseHard).mp solved
    · intro solved
      have rightHard := (solves_append substitution
        [.ty right.dual.target targetType] right.hard).mp solved |>.2
      have leftHard := baseHard.mpr rightHard
      exact (solves_prepend_patternEquation_iff
        (components leftHard) baseHard).mpr solved
  refine ⟨hard, EntailedTypeEq.refl _ .int, ?_⟩
  have weakened : EntailedPendingEq
      ([.ty left.dual.target targetType] ++ left.hard)
      left.pending right.pending := by
    simpa [GeneratedItems.asTuple, GeneratedItems.cons,
      GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
      patternAsGenerated] using
      entailedPending_weaken aligned.pendingAligned (by
        intro substitution solved
        have tailSolved := (solves_append substitution
          [.ty left.dual.target targetType] left.hard).mp solved |>.2
        simpa [GeneratedItems.asTuple, GeneratedItems.cons,
          GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
          patternAsGenerated] using tailSolved)
  apply pendingAppendPatternSlot weakened
  intro substitution solved
  have tailSolved := (solves_append substitution
    [.ty left.dual.target targetType] left.hard).mp solved |>.2
  exact (pairedPatternTarget_components
    (aligned.targetEntailed substitution (by
      simpa [GeneratedItems.asTuple, GeneratedItems.cons,
        GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
        patternAsGenerated] using tailSolved))).1

private theorem fixedPairAvoids
    {hidden : List UnificationVar} {first second : Ty}
    (firstAvoids : TypeAvoids hidden first)
    (secondAvoids : TypeAvoids hidden second) :
    GeneratedAvoids hidden (fixedTypesGenerated [first, second]) := by
  intro candidate member hiddenMember
  have split : candidate ∈ first.unificationVars ∨
      candidate ∈ second.unificationVars := by
    simpa [fixedTypesGenerated, Generated.unificationVars,
      Ty.unificationVars, Ty.unificationVarsList, TypePM.unificationVars,
      pendingUnificationVars] using member
  rcases split with observed | observed
  · exact firstAvoids candidate observed hiddenMember
  · exact secondAvoids candidate observed hiddenMember

private theorem scopedBy_armPattern
    {targetType matcherType : Ty} {pattern : GeneratedPattern}
    {aliases : List FreshAliasSequence.Alias}
    (scopeProof : ScopedBy
      (GeneratedItems.asTuple (GeneratedItems.cons
        (fixedTypesGenerated [targetType, matcherType])
        (GeneratedItems.singleton (patternAsGenerated pattern)))).unificationVars
      aliases) :
    ScopedBy (armPatternGenerated targetType matcherType pattern).unificationVars
      aliases := by
  have memberIff (candidate : UnificationVar) :
      candidate ∈
          (GeneratedItems.asTuple (GeneratedItems.cons
            (fixedTypesGenerated [targetType, matcherType])
            (GeneratedItems.singleton
              (patternAsGenerated pattern)))).unificationVars ↔
        candidate ∈
          (armPatternGenerated targetType matcherType pattern).unificationVars := by
    simp [armPatternGenerated, checksGenerated, fixedTypesGenerated,
      GeneratedItems.asTuple, GeneratedItems.cons, GeneratedItems.singleton,
      GeneratedItems.nil, patternAsGenerated, encodedPatternDual,
      Generated.unificationVars, Ty.unificationVars,
      Ty.unificationVarsList,
      TypePM.unificationVars, Equation.unificationVars,
      CheckObligation.unificationVars,
      pendingUnificationVars_append, pendingUnificationVars,
      or_assoc, or_left_comm, or_comm]
  refine ⟨scopeProof.1, ?_⟩
  intro alias aliasMember
  have endpoints := scopeProof.2 alias aliasMember
  constructor
  · intro observed
    exact endpoints.1 ((memberIff _).mpr observed)
  · exact (memberIff _).mp endpoints.2

private def supportedArmPattern
    {start next : Supply} {targetType matcherType : Ty}
    {left right : GeneratedPattern}
    (certificate : SupportedEntailedAlignmentCertificate start next
      (patternAsGenerated left) (patternAsGenerated right))
    (targetAvoids : TypeAvoids certificate.hidden targetType)
    (matcherAvoids : TypeAvoids certificate.hidden matcherType) :
    SupportedEntailedAlignmentCertificate start next
      (armPatternGenerated targetType matcherType left)
      (armPatternGenerated targetType matcherType right) := by
  let fixed := fixedTypesGenerated [targetType, matcherType]
  let frame := GeneratedFrame.tupleItem
    (GeneratedItems.singleton fixed) GeneratedItems.nil .hole
  have fixedAvoids : GeneratedAvoids certificate.hidden fixed := by
    exact fixedPairAvoids targetAvoids matcherAvoids
  let base := certificate.underFrame frame
    ⟨GeneratedItemsAvoid.singleton fixedAvoids,
      (by
        intro candidate member
        simp [GeneratedItems.nil, GeneratedItems.unificationVars,
          Ty.unificationVarsList, TypePM.unificationVars,
          pendingUnificationVars] at member),
      trivial⟩
  apply repackageCertificate base
  · apply scopedBy_armPattern
    simpa [base, frame, fixed, GeneratedFrame.plug, GeneratedItems.append,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil] using
      base.leftScoped
  · apply scopedBy_armPattern
    simpa [base, frame, fixed, GeneratedFrame.plug, GeneratedItems.append,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil] using
      base.rightScoped
  · have aligned : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll base.leftAliases
        (GeneratedItems.asTuple (GeneratedItems.cons fixed
          (GeneratedItems.singleton (patternAsGenerated left)))))
      (FreshAliasSequence.addAll base.rightAliases
        (GeneratedItems.asTuple (GeneratedItems.cons fixed
          (GeneratedItems.singleton (patternAsGenerated right))))) := by
      simpa [base, frame, fixed, GeneratedFrame.plug, GeneratedItems.append,
        GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil] using
        base.aligned
    let leftOutput := armPatternGenerated targetType matcherType left
    let rightOutput := armPatternGenerated targetType matcherType right
    have components (substitution : Subst)
        (leftSolved : Solves substitution
          (FreshAliasSequence.addAll base.leftAliases
            (GeneratedItems.asTuple (GeneratedItems.cons fixed
              (GeneratedItems.singleton (patternAsGenerated left))))).hard) :
        left.dual.capability.apply substitution.cap =
            right.dual.capability.apply substitution.cap ∧
          left.dual.target.apply substitution =
            right.dual.target.apply substitution := by
      have targetEquality := aligned.targetEntailed substitution leftSolved
      have rawTargetEquality :
          (GeneratedItems.asTuple (GeneratedItems.cons
            (fixedTypesGenerated [targetType, matcherType])
            (GeneratedItems.singleton (patternAsGenerated left)))).target.apply
              substitution =
          (GeneratedItems.asTuple (GeneratedItems.cons
            (fixedTypesGenerated [targetType, matcherType])
            (GeneratedItems.singleton (patternAsGenerated right)))).target.apply
              substitution := by
        simpa [FreshAliasSequence.addAll_target, fixed] using targetEquality
      exact pairedPatternTarget_components rawTargetEquality
    refine ⟨?_, ?_, ?_⟩
    · intro substitution
      simp only [InterfaceAliasDecomposition.EquationLists.addAll_hard,
        InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
        armPatternGenerated, checksGenerated,
        List.singleton_append, solves_append, solves_cons,
        Equation.Holds]
      constructor
      · rintro ⟨aliasesSolved, equationSolved, leftHard⟩
        have leftBase : Solves substitution
            (FreshAliasSequence.addAll base.leftAliases
              (GeneratedItems.asTuple (GeneratedItems.cons fixed
                (GeneratedItems.singleton (patternAsGenerated left))))).hard := by
          simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
            fixed, GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
            patternAsGenerated] using And.intro aliasesSolved leftHard
        have rightBase := (aligned.hardEquivalent substitution).mp leftBase
        have dualEquality := (components substitution leftBase).2
        have rightSplit : Solves substitution
            (base.rightAliases.reverse.map
              InterfaceAliasDecomposition.EquationLists.aliasEquation ++
              right.hard) := by
          simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
            fixed, GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
            patternAsGenerated] using rightBase
        exact ⟨(solves_append substitution _ _).mp rightSplit |>.1,
          by simpa [dualEquality] using equationSolved,
          (solves_append substitution _ _).mp rightSplit |>.2⟩
      · rintro ⟨aliasesSolved, equationSolved, rightHard⟩
        have rightBase : Solves substitution
            (FreshAliasSequence.addAll base.rightAliases
              (GeneratedItems.asTuple (GeneratedItems.cons fixed
                (GeneratedItems.singleton (patternAsGenerated right))))).hard := by
          simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
            fixed, GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
            patternAsGenerated] using And.intro aliasesSolved rightHard
        have leftBase := (aligned.hardEquivalent substitution).mpr rightBase
        have dualEquality := (components substitution leftBase).2
        have leftSplit : Solves substitution
            (base.leftAliases.reverse.map
              InterfaceAliasDecomposition.EquationLists.aliasEquation ++
              left.hard) := by
          simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
            fixed, GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
            patternAsGenerated] using leftBase
        exact ⟨(solves_append substitution _ _).mp leftSplit |>.1,
          by simpa [dualEquality] using equationSolved,
          (solves_append substitution _ _).mp leftSplit |>.2⟩
    · simpa [FreshAliasSequence.addAll_target, leftOutput, rightOutput,
        armPatternGenerated, checksGenerated] using
        (EntailedTypeEq.refl
          (FreshAliasSequence.addAll base.leftAliases leftOutput).hard
          .int)
    · simp only [FreshAliasSequence.addAll_pending]
      change EntailedPendingEq
        (FreshAliasSequence.addAll base.leftAliases leftOutput).hard
        (left.pending ++
          [⟨matcherType, .slot left.dual.capability targetType⟩])
        (right.pending ++
          [⟨matcherType, .slot right.dual.capability targetType⟩])
      have weakened : EntailedPendingEq
          (FreshAliasSequence.addAll base.leftAliases leftOutput).hard
          left.pending right.pending := by
        have comparison := entailedPending_weaken
          (stronger := (FreshAliasSequence.addAll
            base.leftAliases leftOutput).hard)
          aligned.pendingAligned (by
            intro substitution solved
            have outputSplit := (solves_append substitution
              (base.leftAliases.reverse.map
                InterfaceAliasDecomposition.EquationLists.aliasEquation)
              (.ty left.dual.target targetType :: left.hard)).mp (by
                simpa [leftOutput, armPatternGenerated, checksGenerated,
                  InterfaceAliasDecomposition.EquationLists.addAll_hard,
                  InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append]
                  using solved)
            have baseSolved : Solves substitution
                (base.leftAliases.reverse.map
                  InterfaceAliasDecomposition.EquationLists.aliasEquation ++
                  left.hard) := (solves_append substitution _ _).mpr
              ⟨outputSplit.1,
                (solves_cons substitution _ _).mp outputSplit.2 |>.2⟩
            simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
              InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
              fixed, GeneratedItems.asTuple, GeneratedItems.cons,
              GeneratedItems.singleton, GeneratedItems.nil,
              fixedTypesGenerated, patternAsGenerated] using baseSolved)
        simpa [FreshAliasSequence.addAll_pending, fixed,
          GeneratedItems.asTuple, GeneratedItems.cons,
          GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
          patternAsGenerated] using comparison
      apply pendingAppendPatternSlot weakened
      intro substitution solved
      have outputSplit := (solves_append substitution
        (base.leftAliases.reverse.map
          InterfaceAliasDecomposition.EquationLists.aliasEquation)
        (.ty left.dual.target targetType :: left.hard)).mp (by
          simpa [leftOutput, armPatternGenerated, checksGenerated,
            InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append]
            using solved)
      have baseSolved : Solves substitution
          (FreshAliasSequence.addAll base.leftAliases
            (GeneratedItems.asTuple (GeneratedItems.cons fixed
              (GeneratedItems.singleton (patternAsGenerated left))))).hard := by
        have recombined : Solves substitution
            (base.leftAliases.reverse.map
              InterfaceAliasDecomposition.EquationLists.aliasEquation ++
              left.hard) := (solves_append substitution _ _).mpr
          ⟨outputSplit.1, (solves_cons substitution _ _).mp outputSplit.2 |>.2⟩
        simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
          InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
          fixed, GeneratedItems.asTuple, GeneratedItems.cons,
          GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
          patternAsGenerated] using recombined
      exact (components substitution baseSolved).1

private theorem fixedOneAvoids
    {hidden : List UnificationVar} {expected : Ty}
    (expectedAvoids : TypeAvoids hidden expected) :
    GeneratedAvoids hidden (fixedTypesGenerated [expected]) := by
  intro candidate member hiddenMember
  have observed : candidate ∈ expected.unificationVars := by
    simpa [fixedTypesGenerated, Generated.unificationVars,
      Ty.unificationVars, Ty.unificationVarsList, TypePM.unificationVars,
      pendingUnificationVars] using member
  exact expectedAvoids candidate observed hiddenMember

private theorem scopedBy_checkedBody
    {expected : Ty} {body : Generated}
    {aliases : List FreshAliasSequence.Alias}
    (scopeProof : ScopedBy
      (GeneratedItems.asTuple (GeneratedItems.cons body
        (GeneratedItems.singleton
          (fixedTypesGenerated [expected])))).unificationVars aliases) :
    ScopedBy (checkedBodyGenerated expected body).unificationVars aliases := by
  have memberIff (candidate : UnificationVar) :
      candidate ∈
          (GeneratedItems.asTuple (GeneratedItems.cons body
            (GeneratedItems.singleton
              (fixedTypesGenerated [expected])))).unificationVars ↔
        candidate ∈ (checkedBodyGenerated expected body).unificationVars := by
    simp [checkedBodyGenerated, checksGenerated, fixedTypesGenerated,
      GeneratedItems.asTuple, GeneratedItems.cons, GeneratedItems.singleton,
      GeneratedItems.nil, Generated.unificationVars, Ty.unificationVars,
      Ty.unificationVarsList, TypePM.unificationVars,
      Equation.unificationVars, unificationVars_append,
      or_assoc, or_left_comm, or_comm]
  refine ⟨scopeProof.1, ?_⟩
  intro alias aliasMember
  have endpoints := scopeProof.2 alias aliasMember
  exact ⟨fun observed => endpoints.1 ((memberIff _).mpr observed),
    (memberIff _).mp endpoints.2⟩

private theorem pairedBodyTarget
    {expected : Ty} {left right : Generated} {substitution : Subst}
    (equality :
      (GeneratedItems.asTuple (GeneratedItems.cons left
        (GeneratedItems.singleton
          (fixedTypesGenerated [expected])))).target.apply substitution =
      (GeneratedItems.asTuple (GeneratedItems.cons right
        (GeneratedItems.singleton
          (fixedTypesGenerated [expected])))).target.apply substitution) :
    left.target.apply substitution = right.target.apply substitution := by
  simp only [GeneratedItems.asTuple, GeneratedItems.cons,
    GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated,
    Ty.apply] at equality
  injection equality with targets
  exact (List.cons.inj targets).1

private def supportedCheckedBody
    {start next : Supply} {expected : Ty} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (expectedAvoids : TypeAvoids certificate.hidden expected) :
    SupportedEntailedAlignmentCertificate start next
      (checkedBodyGenerated expected left)
      (checkedBodyGenerated expected right) := by
  let fixed := fixedTypesGenerated [expected]
  let frame := GeneratedFrame.tupleItem GeneratedItems.nil
    (GeneratedItems.singleton fixed) .hole
  have fixedAvoids := fixedOneAvoids expectedAvoids
  let base := certificate.underFrame frame
    ⟨(by
        intro candidate member
        simp [GeneratedItems.nil, GeneratedItems.unificationVars,
          Ty.unificationVarsList, TypePM.unificationVars,
          pendingUnificationVars] at member),
      GeneratedItemsAvoid.singleton fixedAvoids, trivial⟩
  apply repackageCertificate base
  · apply scopedBy_checkedBody
    simpa [base, frame, fixed, GeneratedFrame.plug, GeneratedItems.append,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil] using
      base.leftScoped
  · apply scopedBy_checkedBody
    simpa [base, frame, fixed, GeneratedFrame.plug, GeneratedItems.append,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil] using
      base.rightScoped
  · have aligned : EntailedGeneratedAlignment
        (FreshAliasSequence.addAll base.leftAliases
          (GeneratedItems.asTuple (GeneratedItems.cons left
            (GeneratedItems.singleton fixed))))
        (FreshAliasSequence.addAll base.rightAliases
          (GeneratedItems.asTuple (GeneratedItems.cons right
            (GeneratedItems.singleton fixed)))) := by
      simpa [base, frame, fixed, GeneratedFrame.plug, GeneratedItems.append,
        GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil] using
        base.aligned
    let leftOutput := checkedBodyGenerated expected left
    let rightOutput := checkedBodyGenerated expected right
    have targetEquality (substitution : Subst)
        (leftSolved : Solves substitution
          (FreshAliasSequence.addAll base.leftAliases
            (GeneratedItems.asTuple (GeneratedItems.cons left
              (GeneratedItems.singleton fixed)))).hard) :
        left.target.apply substitution = right.target.apply substitution := by
      have equality := aligned.targetEntailed substitution leftSolved
      have rawEquality :
          (GeneratedItems.asTuple (GeneratedItems.cons left
            (GeneratedItems.singleton
              (fixedTypesGenerated [expected])))).target.apply substitution =
          (GeneratedItems.asTuple (GeneratedItems.cons right
            (GeneratedItems.singleton
              (fixedTypesGenerated [expected])))).target.apply substitution := by
        simpa [FreshAliasSequence.addAll_target, fixed] using equality
      exact pairedBodyTarget rawEquality
    refine ⟨?_, ?_, ?_⟩
    · intro substitution
      simp only [InterfaceAliasDecomposition.EquationLists.addAll_hard,
        InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
        checkedBodyGenerated, checksGenerated,
        solves_append, solves_cons, solves_nil, and_true, Equation.Holds]
      constructor
      · rintro ⟨aliasesLeft, hardLeft, equationLeft⟩
        have baseLeft : Solves substitution
            (base.leftAliases.reverse.map
              InterfaceAliasDecomposition.EquationLists.aliasEquation ++
              left.hard) :=
          (solves_append substitution _ _).mpr ⟨aliasesLeft, hardLeft⟩
        have leftSolved : Solves substitution
            (FreshAliasSequence.addAll base.leftAliases
              (GeneratedItems.asTuple (GeneratedItems.cons left
                (GeneratedItems.singleton fixed)))).hard := by
          simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
            fixed, GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated]
            using baseLeft
        have rightSolved := (aligned.hardEquivalent substitution).mp leftSolved
        have rightBase : Solves substitution
            (base.rightAliases.reverse.map
              InterfaceAliasDecomposition.EquationLists.aliasEquation ++
              right.hard) := by
          simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
            fixed, GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated]
            using rightSolved
        have rightParts := (solves_append substitution _ _).mp rightBase
        exact ⟨rightParts.1, rightParts.2,
          by simpa [targetEquality substitution leftSolved] using equationLeft⟩
      · rintro ⟨aliasesRight, hardRight, equationRight⟩
        have baseRight : Solves substitution
            (base.rightAliases.reverse.map
              InterfaceAliasDecomposition.EquationLists.aliasEquation ++
              right.hard) :=
          (solves_append substitution _ _).mpr ⟨aliasesRight, hardRight⟩
        have rightSolved : Solves substitution
            (FreshAliasSequence.addAll base.rightAliases
              (GeneratedItems.asTuple (GeneratedItems.cons right
                (GeneratedItems.singleton fixed)))).hard := by
          simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
            fixed, GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated]
            using baseRight
        have leftSolved := (aligned.hardEquivalent substitution).mpr rightSolved
        have leftBase : Solves substitution
            (base.leftAliases.reverse.map
              InterfaceAliasDecomposition.EquationLists.aliasEquation ++
              left.hard) := by
          simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
            InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
            fixed, GeneratedItems.asTuple, GeneratedItems.cons,
            GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated]
            using leftSolved
        have leftParts := (solves_append substitution _ _).mp leftBase
        exact ⟨leftParts.1, leftParts.2,
          by simpa [targetEquality substitution leftSolved] using equationRight⟩
    · simpa [FreshAliasSequence.addAll_target, leftOutput, rightOutput,
        checkedBodyGenerated, checksGenerated] using
        (EntailedTypeEq.refl
          (FreshAliasSequence.addAll base.leftAliases leftOutput).hard .int)
    · have comparison := entailedPending_weaken
          (stronger :=
            (FreshAliasSequence.addAll base.leftAliases leftOutput).hard)
          aligned.pendingAligned (by
            intro substitution solved
            have baseSolved := (solves_append substitution
              (base.leftAliases.reverse.map
                InterfaceAliasDecomposition.EquationLists.aliasEquation ++
                left.hard)
              [.ty left.target expected]).mp (by
                simpa [leftOutput, checkedBodyGenerated, checksGenerated,
                  InterfaceAliasDecomposition.EquationLists.addAll_hard,
                  InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
                  List.append_assoc] using solved) |>.1
            simpa [InterfaceAliasDecomposition.EquationLists.addAll_hard,
              InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
              fixed, GeneratedItems.asTuple, GeneratedItems.cons,
              GeneratedItems.singleton, GeneratedItems.nil, fixedTypesGenerated]
              using baseSolved)
      simpa [FreshAliasSequence.addAll_pending, leftOutput, rightOutput,
        checkedBodyGenerated, checksGenerated, fixed, GeneratedItems.asTuple,
        GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
        fixedTypesGenerated] using comparison

private def supportedAppendChecks
    {start next : Supply}
    {leftFirst rightFirst leftSecond rightSecond : Generated}
    (first : SupportedEntailedAlignmentCertificate start next
      leftFirst rightFirst)
    (second : SupportedEntailedAlignmentCertificate start next
      leftSecond rightSecond)
    (leftSecondAvoids : GeneratedAvoids first.hidden leftSecond)
    (rightSecondAvoids : GeneratedAvoids first.hidden rightSecond)
    (leftFirstAvoids : GeneratedAvoids second.hidden leftFirst)
    (rightFirstAvoids : GeneratedAvoids second.hidden rightFirst)
    (leftFirstTargetEmpty : leftFirst.target.unificationVars = [])
    (rightFirstTargetEmpty : rightFirst.target.unificationVars = [])
    (leftSecondTargetEmpty : leftSecond.target.unificationVars = [])
    (rightSecondTargetEmpty : rightSecond.target.unificationVars = [])
    (disjoint : ∀ candidate, candidate ∈ first.hidden →
      candidate ∉ second.hidden) :
    SupportedEntailedAlignmentCertificate start next
      (appendChecksGenerated leftFirst leftSecond)
      (appendChecksGenerated rightFirst rightSecond) := by
  let pair := itemsPair first second leftSecondAvoids rightSecondAvoids
    leftFirstAvoids rightFirstAvoids disjoint
  let base := pair.itemsTuple
  have retargeted := supportedCertificateRetarget base .int
    (by
      simp [GeneratedItems.asTuple,
        GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
        Ty.unificationVars, Ty.unificationVarsList, leftFirstTargetEmpty,
        leftSecondTargetEmpty])
    (by
      simp [GeneratedItems.asTuple,
        GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
        Ty.unificationVars, Ty.unificationVarsList, rightFirstTargetEmpty,
        rightSecondTargetEmpty])
    (by simp [TypeAvoids, VariablesAvoid, Ty.unificationVars])
  simpa [retargetGenerated, appendChecksGenerated, checksGenerated, base, pair,
    itemsPair, GeneratedItems.asTuple, GeneratedItems.cons,
    GeneratedItems.singleton, GeneratedItems.nil, List.append_assoc] using
    retargeted

/-! The coherence proof below keeps the already elaborated prefix in a
single generated block.  Its target stores the result type together with the
target/matcher interface.  Later arms can then be appended without requiring
those three (possibly different) types to be definitionally equal on the two
sides. -/

private def seedItems (target matcher : Generated) : GeneratedItems :=
  GeneratedItems.cons target (GeneratedItems.singleton matcher)

private def seedGenerated (target matcher : Generated) : Generated :=
  GeneratedItems.asTuple (seedItems target matcher)

private def armStateGenerated (interface expected : Ty)
    (hard : List Equation) (pending : List CheckObligation) : Generated :=
  { target := .prod [expected, interface], hard := hard, pending := pending }

private def initialArmState (targetType matcherType : Ty)
    (seed : Generated) (pattern : GeneratedPattern)
    (body : Generated) : Generated :=
  armStateGenerated (.prod [targetType, matcherType]) body.target
    (seed.hard ++ [.ty pattern.dual.target targetType] ++
      pattern.hard ++ body.hard)
    (seed.pending ++ pattern.pending ++
      [⟨matcherType, .slot pattern.dual.capability targetType⟩] ++
        body.pending)

private def extendArmState (targetType matcherType expected : Ty)
    (state : Generated) (pattern : GeneratedPattern)
    (body : Generated) : Generated :=
  { target := state.target
    hard := state.hard ++ [.ty pattern.dual.target targetType] ++
      pattern.hard ++ body.hard ++ [.ty body.target expected]
    pending := state.pending ++ pattern.pending ++
      [⟨matcherType, .slot pattern.dual.capability targetType⟩] ++
        body.pending }

private def finishArmState (expected : Ty) (state : Generated) : Generated :=
  { target := expected, hard := state.hard, pending := state.pending }

private def stateItems (state : Generated) (pattern : GeneratedPattern)
    (body : Generated) : GeneratedItems :=
  GeneratedItems.cons state <|
    GeneratedItems.cons (patternAsGenerated pattern) <|
      GeneratedItems.singleton body

private def insertAtMF {alpha : Type} (item : alpha) : Nat → List alpha → List alpha
  | 0, items => item :: items
  | _ + 1, [] => [item]
  | index + 1, head :: tail => head :: insertAtMF item index tail

private theorem insertAtMF_append_length {alpha : Type}
    (before suffix : List alpha) (item : alpha) :
    insertAtMF item before.length (before ++ suffix) =
      before ++ item :: suffix := by
  induction before with
  | nil => rfl
  | cons head tail induction => simp [insertAtMF, induction]

private theorem solves_insertAtMF_iff (substitution : Subst)
    (equations : List Equation) (index : Nat) (equation : Equation) :
    Solves substitution (insertAtMF equation index equations) ↔
      equation.Holds substitution ∧ Solves substitution equations := by
  induction equations generalizing index with
  | nil => cases index <;> simp [insertAtMF, solves_cons, Equation.Holds]
  | cons head tail induction =>
      cases index with
      | zero => simp [insertAtMF, solves_cons]
      | succ index =>
          simp only [insertAtMF, solves_cons, induction]
          exact and_left_comm

private theorem pendingLength_eq
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right) :
    left.length = right.length := by
  induction aligned with
  | nil => rfl
  | cons _ _ induction => simp [induction]

private theorem pendingInsertAtMF
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right)
    (index : Nat) {leftItem rightItem : CheckObligation}
    (itemAligned : EntailedObligationEq reference leftItem rightItem) :
    EntailedPendingEq reference
      (insertAtMF leftItem index left) (insertAtMF rightItem index right) := by
  induction aligned generalizing index with
  | nil =>
      cases index with
      | zero => exact .cons itemAligned .nil
      | succ _ => exact .cons itemAligned .nil
  | @cons leftHead rightHead leftTail rightTail head tail induction =>
      cases index with
      | zero =>
          simpa [insertAtMF] using
            (EntailedPendingEq.cons itemAligned (.cons head tail))
      | succ index =>
          simpa [insertAtMF] using
            (EntailedPendingEq.cons head (induction index))

private def itemsConsSequentialMF
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

private theorem generatedAvoids_appendMF
    {first second : List UnificationVar} {generated : Generated}
    (firstAvoids : GeneratedAvoids first generated)
    (secondAvoids : GeneratedAvoids second generated) :
    GeneratedAvoids (first ++ second) generated := by
  intro candidate member forbidden
  rcases List.mem_append.mp forbidden with first | second
  · exact firstAvoids candidate member first
  · exact secondAvoids candidate member second

private theorem generatedItemsAvoid_consMF
    {hidden : List UnificationVar} {head : Generated}
    {tail : GeneratedItems}
    (headAvoids : GeneratedAvoids hidden head)
    (tailAvoids : GeneratedItemsAvoid hidden tail) :
    GeneratedItemsAvoid hidden (GeneratedItems.cons head tail) := by
  simpa using GeneratedItemsAvoid.append
    (GeneratedItemsAvoid.singleton headAvoids) tailAvoids

private theorem freshIn_to_belowFinishMF
    {start finish : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn start finish hidden) :
    VariablesBelowSupply hidden finish := by
  intro candidate member
  have range := fresh candidate member
  cases candidate <;> exact range.2

private theorem context_avoids_laterFreshMF
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

private theorem generatedAvoids_of_supportMF
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

private theorem extendedContext_avoidsMF
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

private theorem support_avoids_laterFreshMF
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
  exact VariablesScopedBy.avoids_later observedScoped fresh wellFormed
    outerToStart (Supply.le_refl start)

private theorem patternAsGenerated_supportMF
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

private theorem initialState_vars_iff
    (targetType matcherType : Ty) (seed : Generated)
    (pattern : GeneratedPattern) (body : Generated)
    (seedTarget : seed.target = .prod [targetType, matcherType]) :
    ∀ candidate, candidate ∈
        (GeneratedItems.asTuple (stateItems seed pattern body)).unificationVars ↔
      candidate ∈
        (initialArmState targetType matcherType seed pattern body).unificationVars := by
  intro candidate
  cases candidate <;>
    simp [stateItems, initialArmState, armStateGenerated, seedTarget,
      GeneratedItems.asTuple, GeneratedItems.cons,
      GeneratedItems.singleton, GeneratedItems.nil, patternAsGenerated,
      encodedPatternDual, Generated.unificationVars, Ty.unificationVars,
      TypePM.unificationVars,
      Equation.unificationVars, CheckObligation.unificationVars,
      pendingUnificationVars, Ty.occursTyList, Ty.occursCapList,
      Ty.occursCap, Ty.occursTy,
      or_assoc, or_left_comm, or_comm]

private theorem scopedBy_initialState
    {targetType matcherType : Ty} {seed : Generated}
    {pattern : GeneratedPattern} {body : Generated}
    {aliases : List FreshAliasSequence.Alias}
    (seedTarget : seed.target = .prod [targetType, matcherType])
    (scope : ScopedBy
      (GeneratedItems.asTuple (stateItems seed pattern body)).unificationVars
      aliases) :
    ScopedBy
      (initialArmState targetType matcherType seed pattern body).unificationVars
      aliases := by
  refine ⟨scope.1, ?_⟩
  intro alias member
  have endpoints := scope.2 alias member
  constructor
  · intro freshMember
    exact endpoints.1 ((initialState_vars_iff targetType matcherType seed
      pattern body seedTarget _).mpr freshMember)
  · exact (initialState_vars_iff targetType matcherType seed pattern body
      seedTarget _).mp endpoints.2

private theorem initialState_hard_as_insert
    (aliases : List FreshAliasSequence.Alias)
    (targetType matcherType : Ty) (seed : Generated)
    (pattern : GeneratedPattern) (body : Generated) :
    (FreshAliasSequence.addAll aliases
      (initialArmState targetType matcherType seed pattern body)).hard =
      insertAtMF (.ty pattern.dual.target targetType)
        (aliases.reverse.map
            InterfaceAliasDecomposition.EquationLists.aliasEquation ++
          seed.hard).length
        (FreshAliasSequence.addAll aliases
          (GeneratedItems.asTuple (stateItems seed pattern body))).hard := by
  let before := aliases.reverse.map
    InterfaceAliasDecomposition.EquationLists.aliasEquation ++ seed.hard
  let after := pattern.hard ++ body.hard
  have outputShape :
      (FreshAliasSequence.addAll aliases
        (initialArmState targetType matcherType seed pattern body)).hard =
        before ++ .ty pattern.dual.target targetType :: after := by
    simp [before, after, initialArmState, armStateGenerated,
      InterfaceAliasDecomposition.EquationLists.addAll_hard,
      InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
      List.append_assoc]
  have baseShape :
      (FreshAliasSequence.addAll aliases
        (GeneratedItems.asTuple (stateItems seed pattern body))).hard =
        before ++ after := by
    simp [before, after, stateItems, GeneratedItems.asTuple,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
      patternAsGenerated,
      InterfaceAliasDecomposition.EquationLists.addAll_hard,
      InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
      List.append_assoc]
  rw [outputShape, baseShape]
  exact (insertAtMF_append_length before after
    (.ty pattern.dual.target targetType)).symm

private theorem initialState_pending_as_insert
    (targetType matcherType : Ty) (seed : Generated)
    (pattern : GeneratedPattern) (body : Generated) :
    (initialArmState targetType matcherType seed pattern body).pending =
      insertAtMF
        (⟨matcherType,
          .slot pattern.dual.capability targetType⟩ : CheckObligation)
        (seed.pending ++ pattern.pending).length
        (GeneratedItems.asTuple (stateItems seed pattern body)).pending := by
  let before := seed.pending ++ pattern.pending
  let after := body.pending
  have outputShape :
      (initialArmState targetType matcherType seed pattern body).pending =
        before ++
          (⟨matcherType,
            .slot pattern.dual.capability targetType⟩ : CheckObligation) ::
            after := by
    simp [before, after, initialArmState, armStateGenerated,
      List.append_assoc]
  have baseShape :
      (GeneratedItems.asTuple (stateItems seed pattern body)).pending =
        before ++ after := by
    simp [before, after, stateItems, GeneratedItems.asTuple,
      GeneratedItems.cons, GeneratedItems.singleton, GeneratedItems.nil,
      patternAsGenerated, List.append_assoc]
  rw [outputShape, baseShape]
  exact (insertAtMF_append_length before after
    (⟨matcherType,
      .slot pattern.dual.capability targetType⟩ : CheckObligation)).symm

private theorem initialState_components
    {leftTargetType rightTargetType leftMatcherType rightMatcherType : Ty}
    {leftSeed rightSeed : Generated}
    {leftPattern rightPattern : GeneratedPattern}
    {leftBody rightBody : Generated}
    {leftAliases rightAliases : List FreshAliasSequence.Alias}
    (leftSeedTarget : leftSeed.target =
      .prod [leftTargetType, leftMatcherType])
    (rightSeedTarget : rightSeed.target =
      .prod [rightTargetType, rightMatcherType])
    (aligned : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll leftAliases
        (GeneratedItems.asTuple
          (stateItems leftSeed leftPattern leftBody)))
      (FreshAliasSequence.addAll rightAliases
        (GeneratedItems.asTuple
          (stateItems rightSeed rightPattern rightBody))))
    (substitution : Subst)
    (leftSolved : Solves substitution
      (FreshAliasSequence.addAll leftAliases
        (GeneratedItems.asTuple
          (stateItems leftSeed leftPattern leftBody))).hard) :
    leftTargetType.apply substitution = rightTargetType.apply substitution ∧
      leftMatcherType.apply substitution = rightMatcherType.apply substitution ∧
      leftPattern.dual.capability.apply substitution.cap =
        rightPattern.dual.capability.apply substitution.cap ∧
      leftPattern.dual.target.apply substitution =
        rightPattern.dual.target.apply substitution ∧
      leftBody.target.apply substitution = rightBody.target.apply substitution := by
  have targetEquality := aligned.targetEntailed substitution leftSolved
  have listEquality : Ty.applyList substitution
      [leftSeed.target, encodedPatternDual leftPattern.dual,
        leftBody.target] =
      Ty.applyList substitution
      [rightSeed.target, encodedPatternDual rightPattern.dual,
        rightBody.target] := by
    simpa [FreshAliasSequence.addAll_target, stateItems,
      GeneratedItems.asTuple, GeneratedItems.cons, GeneratedItems.singleton,
      GeneratedItems.nil, patternAsGenerated, Ty.apply] using targetEquality
  have seedHead := List.cons.inj listEquality
  have patternHead := List.cons.inj seedHead.2
  have bodyHead := List.cons.inj patternHead.2
  have seedEquality : Ty.applyList substitution
      [leftTargetType, leftMatcherType] =
      Ty.applyList substitution [rightTargetType, rightMatcherType] := by
    simpa [leftSeedTarget, rightSeedTarget, Ty.apply] using seedHead.1
  have targetHead := List.cons.inj seedEquality
  have matcherHead := List.cons.inj targetHead.2
  obtain ⟨capability, patternTarget⟩ :=
    encodedDual_components patternHead.1
  exact ⟨targetHead.1, matcherHead.1, capability, patternTarget,
    bodyHead.1⟩

private def supportedInitialArmState
    {start next : Supply}
    {leftTargetType rightTargetType leftMatcherType rightMatcherType : Ty}
    {leftSeed rightSeed : Generated}
    {leftPattern rightPattern : GeneratedPattern}
    {leftBody rightBody : Generated}
    (leftSeedTarget : leftSeed.target =
      .prod [leftTargetType, leftMatcherType])
    (rightSeedTarget : rightSeed.target =
      .prod [rightTargetType, rightMatcherType])
    (seedPendingLength : leftSeed.pending.length = rightSeed.pending.length)
    (patternPendingLength : leftPattern.pending.length =
      rightPattern.pending.length)
    (certificate : SupportedItemsAlignmentCertificate start next
      (stateItems leftSeed leftPattern leftBody)
      (stateItems rightSeed rightPattern rightBody)) :
    SupportedEntailedAlignmentCertificate start next
      (initialArmState leftTargetType leftMatcherType leftSeed leftPattern
        leftBody)
      (initialArmState rightTargetType rightMatcherType rightSeed rightPattern
        rightBody) := by
  let base := certificate.itemsTuple
  apply repackageCertificate base
  · exact scopedBy_initialState leftSeedTarget base.leftScoped
  · exact scopedBy_initialState rightSeedTarget base.rightScoped
  · have aligned := base.aligned
    let leftOutput := initialArmState leftTargetType leftMatcherType leftSeed
      leftPattern leftBody
    let rightOutput := initialArmState rightTargetType rightMatcherType rightSeed
      rightPattern rightBody
    have leftHard := initialState_hard_as_insert certificate.leftAliases
      leftTargetType leftMatcherType leftSeed leftPattern leftBody
    have rightHard := initialState_hard_as_insert certificate.rightAliases
      rightTargetType rightMatcherType rightSeed rightPattern rightBody
    have leftEntailsBase : ∀ substitution,
        Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard →
        Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases
            (GeneratedItems.asTuple
              (stateItems leftSeed leftPattern leftBody))).hard := by
      intro substitution solved
      exact (solves_insertAtMF_iff substitution _ _ _).mp
        (Eq.mp (congrArg (Solves substitution) leftHard) solved) |>.2
    have components (substitution : Subst)
        (solved : Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard) :=
      initialState_components leftSeedTarget rightSeedTarget aligned substitution
        (leftEntailsBase substitution solved)
    refine ⟨?_, ?_, ?_⟩
    · change HardEquivalent
        (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard
        (FreshAliasSequence.addAll certificate.rightAliases rightOutput).hard
      rw [leftHard, rightHard]
      intro substitution
      rw [solves_insertAtMF_iff, solves_insertAtMF_iff]
      constructor
      · rintro ⟨leftEquation, leftBase⟩
        have rightBase := (aligned.hardEquivalent substitution).mp leftBase
        have equalities := initialState_components leftSeedTarget
          rightSeedTarget aligned substitution leftBase
        exact ⟨by
          simpa [Equation.Holds, equalities.1, equalities.2.2.2.1] using
            leftEquation, rightBase⟩
      · rintro ⟨rightEquation, rightBase⟩
        have leftBase := (aligned.hardEquivalent substitution).mpr rightBase
        have equalities := initialState_components leftSeedTarget
          rightSeedTarget aligned substitution leftBase
        exact ⟨by
          simpa [Equation.Holds, equalities.1, equalities.2.2.2.1] using
            rightEquation, leftBase⟩
    · intro substitution solved
      have equalities := components substitution solved
      simp [FreshAliasSequence.addAll_target, initialArmState,
        armStateGenerated, Ty.apply, Ty.applyList,
        equalities.1, equalities.2.1, equalities.2.2.2.2]
    · have basePending := entailedPending_weaken aligned.pendingAligned
          leftEntailsBase
      have obligationAligned : EntailedObligationEq
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard
          ⟨leftMatcherType,
            .slot leftPattern.dual.capability leftTargetType⟩
          ⟨rightMatcherType,
            .slot rightPattern.dual.capability rightTargetType⟩ := by
        intro substitution solved
        have equalities := components substitution solved
        simp only [CheckObligation.apply, Ty.apply]
        rw [equalities.2.1, equalities.2.2.1, equalities.1]
      have inserted := pendingInsertAtMF basePending
        (leftSeed.pending ++ leftPattern.pending).length obligationAligned
      have prefixLength :
          (leftSeed.pending ++ leftPattern.pending).length =
            (rightSeed.pending ++ rightPattern.pending).length := by
        simp [seedPendingLength, patternPendingLength]
      rw [FreshAliasSequence.addAll_pending,
        FreshAliasSequence.addAll_pending]
      rw [initialState_pending_as_insert, initialState_pending_as_insert]
      rw [← prefixLength]
      simpa [base, SupportedItemsAlignmentCertificate.itemsTuple,
        FreshAliasSequence.addAll_pending, leftOutput, rightOutput] using inserted

private theorem extendedState_vars_iff
    (targetType matcherType expected : Ty)
    (hard : List Equation) (pending : List CheckObligation)
    (pattern : GeneratedPattern) (body : Generated) :
    ∀ candidate, candidate ∈
        (GeneratedItems.asTuple
          (stateItems
            (armStateGenerated (.prod [targetType, matcherType]) expected
              hard pending)
            pattern body)).unificationVars ↔
      candidate ∈
        (extendArmState targetType matcherType expected
          (armStateGenerated (.prod [targetType, matcherType]) expected
            hard pending)
          pattern body).unificationVars := by
  intro candidate
  cases candidate <;>
    simp [stateItems, extendArmState, armStateGenerated,
      GeneratedItems.asTuple, GeneratedItems.cons,
      GeneratedItems.singleton, GeneratedItems.nil, patternAsGenerated,
      encodedPatternDual, Generated.unificationVars, Ty.unificationVars,
      TypePM.unificationVars,
      Equation.unificationVars, CheckObligation.unificationVars,
      pendingUnificationVars, Ty.occursTyList, Ty.occursCapList,
      Ty.occursCap, Ty.occursTy,
      or_assoc, or_left_comm, or_comm]

private theorem scopedBy_extendedState
    {targetType matcherType expected : Ty}
    {hard : List Equation} {pending : List CheckObligation}
    {pattern : GeneratedPattern} {body : Generated}
    {aliases : List FreshAliasSequence.Alias}
    (scope : ScopedBy
      (GeneratedItems.asTuple
        (stateItems
          (armStateGenerated (.prod [targetType, matcherType]) expected
            hard pending)
          pattern body)).unificationVars aliases) :
    ScopedBy
      (extendArmState targetType matcherType expected
        (armStateGenerated (.prod [targetType, matcherType]) expected
          hard pending)
        pattern body).unificationVars aliases := by
  refine ⟨scope.1, ?_⟩
  intro alias member
  have endpoints := scope.2 alias member
  constructor
  · intro freshMember
    exact endpoints.1 ((extendedState_vars_iff targetType matcherType expected
      hard pending pattern body _).mpr freshMember)
  · exact (extendedState_vars_iff targetType matcherType expected hard pending
      pattern body _).mp endpoints.2

private theorem extendedState_hard_as_inserts
    (aliases : List FreshAliasSequence.Alias)
    (targetType matcherType expected : Ty)
    (hard : List Equation) (pending : List CheckObligation)
    (pattern : GeneratedPattern) (body : Generated) :
    let state := armStateGenerated (.prod [targetType, matcherType]) expected
      hard pending
    let base := (FreshAliasSequence.addAll aliases
      (GeneratedItems.asTuple (stateItems state pattern body))).hard
    let withPattern := insertAtMF (.ty pattern.dual.target targetType)
      (aliases.reverse.map
          InterfaceAliasDecomposition.EquationLists.aliasEquation ++ hard).length
      base
    (FreshAliasSequence.addAll aliases
      (extendArmState targetType matcherType expected state pattern body)).hard =
      insertAtMF (.ty body.target expected) withPattern.length withPattern := by
  dsimp only
  let before := aliases.reverse.map
    InterfaceAliasDecomposition.EquationLists.aliasEquation ++ hard
  let middle := pattern.hard ++ body.hard
  let withPattern := before ++ .ty pattern.dual.target targetType :: middle
  have outputShape :
      (FreshAliasSequence.addAll aliases
        (extendArmState targetType matcherType expected
          (armStateGenerated (.prod [targetType, matcherType]) expected
            hard pending)
          pattern body)).hard =
        withPattern ++ [.ty body.target expected] := by
    simp [before, middle, withPattern, extendArmState, armStateGenerated,
      InterfaceAliasDecomposition.EquationLists.addAll_hard,
      InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
      List.append_assoc]
  have baseShape :
      (FreshAliasSequence.addAll aliases
        (GeneratedItems.asTuple
          (stateItems
            (armStateGenerated (.prod [targetType, matcherType]) expected
              hard pending)
            pattern body))).hard = before ++ middle := by
    simp [before, middle, stateItems, armStateGenerated,
      GeneratedItems.asTuple, GeneratedItems.cons,
      GeneratedItems.singleton, GeneratedItems.nil, patternAsGenerated,
      InterfaceAliasDecomposition.EquationLists.addAll_hard,
      InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
      List.append_assoc]
  rw [outputShape, baseShape]
  have firstInsert :
      insertAtMF (.ty pattern.dual.target targetType) before.length
          (before ++ middle) = withPattern := by
    simpa [withPattern] using insertAtMF_append_length before middle
      (.ty pattern.dual.target targetType)
  rw [firstInsert]
  simpa using
    (insertAtMF_append_length withPattern [] (.ty body.target expected)).symm

private theorem extendedState_pending_as_insert
    (targetType matcherType expected : Ty)
    (hard : List Equation) (pending : List CheckObligation)
    (pattern : GeneratedPattern) (body : Generated) :
    let state := armStateGenerated (.prod [targetType, matcherType]) expected
      hard pending
    (extendArmState targetType matcherType expected state pattern body).pending =
      insertAtMF
        (⟨matcherType,
          .slot pattern.dual.capability targetType⟩ : CheckObligation)
        (pending ++ pattern.pending).length
        (GeneratedItems.asTuple (stateItems state pattern body)).pending := by
  dsimp only
  let before := pending ++ pattern.pending
  let after := body.pending
  have outputShape :
      (extendArmState targetType matcherType expected
        (armStateGenerated (.prod [targetType, matcherType]) expected
          hard pending)
        pattern body).pending =
        before ++
          (⟨matcherType,
            .slot pattern.dual.capability targetType⟩ : CheckObligation) ::
            after := by
    simp [before, after, extendArmState, armStateGenerated, List.append_assoc]
  have baseShape :
      (GeneratedItems.asTuple
        (stateItems
          (armStateGenerated (.prod [targetType, matcherType]) expected
            hard pending)
          pattern body)).pending = before ++ after := by
    simp [before, after, stateItems, armStateGenerated,
      GeneratedItems.asTuple, GeneratedItems.cons,
      GeneratedItems.singleton, GeneratedItems.nil, patternAsGenerated,
      List.append_assoc]
  rw [outputShape, baseShape]
  exact (insertAtMF_append_length before after
    (⟨matcherType,
      .slot pattern.dual.capability targetType⟩ : CheckObligation)).symm

private theorem extendedState_components
    {leftTargetType rightTargetType leftMatcherType rightMatcherType : Ty}
    {leftExpected rightExpected : Ty}
    {leftHard rightHard : List Equation}
    {leftPending rightPending : List CheckObligation}
    {leftPattern rightPattern : GeneratedPattern}
    {leftBody rightBody : Generated}
    {leftAliases rightAliases : List FreshAliasSequence.Alias}
    (aligned : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll leftAliases
        (GeneratedItems.asTuple
          (stateItems
            (armStateGenerated
              (.prod [leftTargetType, leftMatcherType]) leftExpected
              leftHard leftPending)
            leftPattern leftBody)))
      (FreshAliasSequence.addAll rightAliases
        (GeneratedItems.asTuple
          (stateItems
            (armStateGenerated
              (.prod [rightTargetType, rightMatcherType]) rightExpected
              rightHard rightPending)
            rightPattern rightBody))))
    (substitution : Subst)
    (leftSolved : Solves substitution
      (FreshAliasSequence.addAll leftAliases
        (GeneratedItems.asTuple
          (stateItems
            (armStateGenerated
              (.prod [leftTargetType, leftMatcherType]) leftExpected
              leftHard leftPending)
            leftPattern leftBody))).hard) :
    leftExpected.apply substitution = rightExpected.apply substitution ∧
      leftTargetType.apply substitution = rightTargetType.apply substitution ∧
      leftMatcherType.apply substitution = rightMatcherType.apply substitution ∧
      leftPattern.dual.capability.apply substitution.cap =
        rightPattern.dual.capability.apply substitution.cap ∧
      leftPattern.dual.target.apply substitution =
        rightPattern.dual.target.apply substitution ∧
      leftBody.target.apply substitution = rightBody.target.apply substitution := by
  have targetEquality := aligned.targetEntailed substitution leftSolved
  have listEquality : Ty.applyList substitution
      [(armStateGenerated (.prod [leftTargetType, leftMatcherType])
          leftExpected leftHard leftPending).target,
        encodedPatternDual leftPattern.dual, leftBody.target] =
      Ty.applyList substitution
      [(armStateGenerated (.prod [rightTargetType, rightMatcherType])
          rightExpected rightHard rightPending).target,
        encodedPatternDual rightPattern.dual, rightBody.target] := by
    simpa [FreshAliasSequence.addAll_target, stateItems,
      GeneratedItems.asTuple, GeneratedItems.cons, GeneratedItems.singleton,
      GeneratedItems.nil, patternAsGenerated, Ty.apply] using targetEquality
  have stateHead := List.cons.inj listEquality
  have patternHead := List.cons.inj stateHead.2
  have bodyHead := List.cons.inj patternHead.2
  have stateEquality : Ty.applyList substitution
      [leftExpected, .prod [leftTargetType, leftMatcherType]] =
      Ty.applyList substitution
      [rightExpected, .prod [rightTargetType, rightMatcherType]] := by
    simpa [armStateGenerated, Ty.apply] using stateHead.1
  have expectedHead := List.cons.inj stateEquality
  have interfaceHead := List.cons.inj expectedHead.2
  have interfaceEquality : Ty.applyList substitution
      [leftTargetType, leftMatcherType] =
      Ty.applyList substitution [rightTargetType, rightMatcherType] := by
    simpa [Ty.apply] using interfaceHead.1
  have targetHead := List.cons.inj interfaceEquality
  have matcherHead := List.cons.inj targetHead.2
  obtain ⟨capability, patternTarget⟩ :=
    encodedDual_components patternHead.1
  exact ⟨expectedHead.1, targetHead.1, matcherHead.1, capability,
    patternTarget, bodyHead.1⟩

private def supportedExtendArmState
    {start next : Supply}
    {leftTargetType rightTargetType leftMatcherType rightMatcherType : Ty}
    {leftExpected rightExpected : Ty}
    {leftHard rightHard : List Equation}
    {leftPending rightPending : List CheckObligation}
    {leftPattern rightPattern : GeneratedPattern}
    {leftBody rightBody : Generated}
    (statePendingLength : leftPending.length = rightPending.length)
    (patternPendingLength : leftPattern.pending.length =
      rightPattern.pending.length)
    (certificate : SupportedItemsAlignmentCertificate start next
      (stateItems
        (armStateGenerated (.prod [leftTargetType, leftMatcherType])
          leftExpected leftHard leftPending)
        leftPattern leftBody)
      (stateItems
        (armStateGenerated (.prod [rightTargetType, rightMatcherType])
          rightExpected rightHard rightPending)
        rightPattern rightBody)) :
    SupportedEntailedAlignmentCertificate start next
      (extendArmState leftTargetType leftMatcherType leftExpected
        (armStateGenerated (.prod [leftTargetType, leftMatcherType])
          leftExpected leftHard leftPending)
        leftPattern leftBody)
      (extendArmState rightTargetType rightMatcherType rightExpected
        (armStateGenerated (.prod [rightTargetType, rightMatcherType])
          rightExpected rightHard rightPending)
        rightPattern rightBody) := by
  let leftState := armStateGenerated
    (.prod [leftTargetType, leftMatcherType]) leftExpected leftHard leftPending
  let rightState := armStateGenerated
    (.prod [rightTargetType, rightMatcherType]) rightExpected rightHard rightPending
  let base := certificate.itemsTuple
  apply repackageCertificate base
  · exact scopedBy_extendedState base.leftScoped
  · exact scopedBy_extendedState base.rightScoped
  · have aligned := base.aligned
    let leftOutput := extendArmState leftTargetType leftMatcherType leftExpected
      leftState leftPattern leftBody
    let rightOutput := extendArmState rightTargetType rightMatcherType
      rightExpected rightState rightPattern rightBody
    have leftHardShape := extendedState_hard_as_inserts
      certificate.leftAliases leftTargetType leftMatcherType leftExpected
      leftHard leftPending leftPattern leftBody
    have rightHardShape := extendedState_hard_as_inserts
      certificate.rightAliases rightTargetType rightMatcherType rightExpected
      rightHard rightPending rightPattern rightBody
    dsimp only at leftHardShape rightHardShape
    let leftBaseHard := (FreshAliasSequence.addAll certificate.leftAliases
      (GeneratedItems.asTuple
        (stateItems leftState leftPattern leftBody))).hard
    let rightBaseHard := (FreshAliasSequence.addAll certificate.rightAliases
      (GeneratedItems.asTuple
        (stateItems rightState rightPattern rightBody))).hard
    let leftWithPattern := insertAtMF
      (.ty leftPattern.dual.target leftTargetType)
      (certificate.leftAliases.reverse.map
          InterfaceAliasDecomposition.EquationLists.aliasEquation ++
        leftHard).length leftBaseHard
    let rightWithPattern := insertAtMF
      (.ty rightPattern.dual.target rightTargetType)
      (certificate.rightAliases.reverse.map
          InterfaceAliasDecomposition.EquationLists.aliasEquation ++
        rightHard).length rightBaseHard
    have leftEntailsBase : ∀ substitution,
        Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard →
        Solves substitution leftBaseHard := by
      intro substitution solved
      have twice := (solves_insertAtMF_iff substitution _ _ _).mp
        (Eq.mp (congrArg (Solves substitution) leftHardShape) solved)
      exact (solves_insertAtMF_iff substitution _ _ _).mp twice.2 |>.2
    have components (substitution : Subst)
        (solved : Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard) :=
      extendedState_components aligned substitution
        (leftEntailsBase substitution solved)
    refine ⟨?_, ?_, ?_⟩
    · change HardEquivalent
        (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard
        (FreshAliasSequence.addAll certificate.rightAliases rightOutput).hard
      rw [leftHardShape, rightHardShape]
      intro substitution
      rw [solves_insertAtMF_iff, solves_insertAtMF_iff,
        solves_insertAtMF_iff, solves_insertAtMF_iff]
      constructor
      · rintro ⟨leftBodyEquation, leftPatternEquation, leftBase⟩
        have rightBase := (aligned.hardEquivalent substitution).mp leftBase
        have equalities := extendedState_components aligned substitution leftBase
        exact ⟨by
          simpa [Equation.Holds, equalities.1, equalities.2.2.2.2.2] using
            leftBodyEquation,
          by simpa [Equation.Holds, equalities.2.1,
            equalities.2.2.2.2.1] using leftPatternEquation,
          rightBase⟩
      · rintro ⟨rightBodyEquation, rightPatternEquation, rightBase⟩
        have leftBase := (aligned.hardEquivalent substitution).mpr rightBase
        have equalities := extendedState_components aligned substitution leftBase
        exact ⟨by
          simpa [Equation.Holds, equalities.1, equalities.2.2.2.2.2] using
            rightBodyEquation,
          by simpa [Equation.Holds, equalities.2.1,
            equalities.2.2.2.2.1] using rightPatternEquation,
          leftBase⟩
    · intro substitution solved
      have equalities := components substitution solved
      simp [FreshAliasSequence.addAll_target, extendArmState,
        armStateGenerated, Ty.apply,
        Ty.applyList, equalities.1, equalities.2.1, equalities.2.2.1]
    · have basePending := entailedPending_weaken aligned.pendingAligned
          leftEntailsBase
      have obligationAligned : EntailedObligationEq
          (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard
          ⟨leftMatcherType,
            .slot leftPattern.dual.capability leftTargetType⟩
          ⟨rightMatcherType,
            .slot rightPattern.dual.capability rightTargetType⟩ := by
        intro substitution solved
        have equalities := components substitution solved
        simp only [CheckObligation.apply, Ty.apply]
        rw [equalities.2.2.1, equalities.2.2.2.1, equalities.2.1]
      have inserted := pendingInsertAtMF basePending
        (leftPending ++ leftPattern.pending).length obligationAligned
      have prefixLength :
          (leftPending ++ leftPattern.pending).length =
            (rightPending ++ rightPattern.pending).length := by
        simp [statePendingLength, patternPendingLength]
      rw [FreshAliasSequence.addAll_pending,
        FreshAliasSequence.addAll_pending]
      rw [extendedState_pending_as_insert,
        extendedState_pending_as_insert]
      rw [← prefixLength]
      simpa [base, SupportedItemsAlignmentCertificate.itemsTuple,
        FreshAliasSequence.addAll_pending, leftOutput, rightOutput,
        leftState, rightState] using inserted

private def completedArmState (target matcher : Generated)
    (pattern : GeneratedPattern) (body : Generated)
    (tail : GeneratedTail) : Generated :=
  let seed := seedGenerated target matcher
  let initial := initialArmState target.target matcher.target seed pattern body
  armStateGenerated (.prod [target.target, matcher.target]) body.target
    (initial.hard ++ tail.hard) (initial.pending ++ tail.pending)

private theorem completedState_vars_iff
    (target matcher : Generated) (pattern : GeneratedPattern)
    (body : Generated) (tail : GeneratedTail) :
    ∀ candidate,
      candidate ∈
          (completedArmState target matcher pattern body tail).unificationVars ↔
        candidate ∈
          (Generated.fromMatchFirst target matcher
            (GeneratedArms.fromFirst target.target matcher.target pattern body
              tail)).unificationVars := by
  intro candidate
  cases candidate <;>
    simp [completedArmState, seedGenerated, seedItems, initialArmState,
      armStateGenerated, Generated.fromMatchFirst, GeneratedArms.fromFirst,
      GeneratedItems.asTuple, GeneratedItems.cons,
      GeneratedItems.singleton, GeneratedItems.nil, Generated.unificationVars,
      Ty.unificationVars, TypePM.unificationVars, Equation.unificationVars,
      CheckObligation.unificationVars, pendingUnificationVars,
      Ty.occursTyList, Ty.occursCapList, Ty.occursCap,
      Ty.occursTy, or_assoc, or_left_comm, or_comm]

private theorem scopedBy_completedState
    {target matcher : Generated} {pattern : GeneratedPattern}
    {body : Generated} {tail : GeneratedTail}
    {aliases : List FreshAliasSequence.Alias}
    (scope : ScopedBy
      (completedArmState target matcher pattern body tail).unificationVars
      aliases) :
    ScopedBy
      (Generated.fromMatchFirst target matcher
        (GeneratedArms.fromFirst target.target matcher.target pattern body
          tail)).unificationVars aliases := by
  refine ⟨scope.1, ?_⟩
  intro alias member
  have endpoints := scope.2 alias member
  constructor
  · intro freshMember
    exact endpoints.1 ((completedState_vars_iff target matcher pattern body tail
      _).mpr freshMember)
  · exact (completedState_vars_iff target matcher pattern body tail _).mp
      endpoints.2

private def supportedFinishArmState
    {start next : Supply}
    {leftTarget rightTarget leftMatcher rightMatcher : Generated}
    {leftPattern rightPattern : GeneratedPattern}
    {leftBody rightBody : Generated}
    {leftTail rightTail : GeneratedTail}
    (certificate : SupportedEntailedAlignmentCertificate start next
      (completedArmState leftTarget leftMatcher leftPattern leftBody leftTail)
      (completedArmState rightTarget rightMatcher rightPattern rightBody
        rightTail)) :
    SupportedEntailedAlignmentCertificate start next
      (Generated.fromMatchFirst leftTarget leftMatcher
        (GeneratedArms.fromFirst leftTarget.target leftMatcher.target
          leftPattern leftBody leftTail))
      (Generated.fromMatchFirst rightTarget rightMatcher
        (GeneratedArms.fromFirst rightTarget.target rightMatcher.target
          rightPattern rightBody rightTail)) := by
  apply repackageCertificate certificate
  · exact scopedBy_completedState certificate.leftScoped
  · exact scopedBy_completedState certificate.rightScoped
  · let leftOutput := Generated.fromMatchFirst leftTarget leftMatcher
      (GeneratedArms.fromFirst leftTarget.target leftMatcher.target
        leftPattern leftBody leftTail)
    let rightOutput := Generated.fromMatchFirst rightTarget rightMatcher
      (GeneratedArms.fromFirst rightTarget.target rightMatcher.target
        rightPattern rightBody rightTail)
    have hardLeft :
        (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard =
          (FreshAliasSequence.addAll certificate.leftAliases
            (completedArmState leftTarget leftMatcher leftPattern leftBody
              leftTail)).hard := by
      simp [leftOutput, completedArmState, seedGenerated, seedItems,
        initialArmState, armStateGenerated, Generated.fromMatchFirst,
        GeneratedArms.fromFirst,
        GeneratedItems.asTuple, GeneratedItems.cons,
        GeneratedItems.singleton, GeneratedItems.nil,
        InterfaceAliasDecomposition.EquationLists.addAll_hard,
        InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
        List.append_assoc]
    have hardRight :
        (FreshAliasSequence.addAll certificate.rightAliases rightOutput).hard =
          (FreshAliasSequence.addAll certificate.rightAliases
            (completedArmState rightTarget rightMatcher rightPattern rightBody
              rightTail)).hard := by
      simp [rightOutput, completedArmState, seedGenerated, seedItems,
        initialArmState, armStateGenerated, Generated.fromMatchFirst,
        GeneratedArms.fromFirst,
        GeneratedItems.asTuple, GeneratedItems.cons,
        GeneratedItems.singleton, GeneratedItems.nil,
        InterfaceAliasDecomposition.EquationLists.addAll_hard,
        InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
        List.append_assoc]
    refine ⟨?_, ?_, ?_⟩
    · rw [hardLeft, hardRight]
      exact certificate.aligned.hardEquivalent
    · intro substitution solved
      have stateSolved : Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases
            (completedArmState leftTarget leftMatcher leftPattern leftBody
              leftTail)).hard := by
        rwa [← hardLeft]
      have equality := certificate.aligned.targetEntailed substitution stateSolved
      have listEquality : Ty.applyList substitution
          [leftBody.target,
            .prod [leftTarget.target, leftMatcher.target]] =
          Ty.applyList substitution
          [rightBody.target,
            .prod [rightTarget.target, rightMatcher.target]] := by
        simpa [FreshAliasSequence.addAll_target, completedArmState,
          armStateGenerated, Ty.apply] using equality
      have bodyEquality := (List.cons.inj listEquality).1
      simpa [FreshAliasSequence.addAll_target, leftOutput, rightOutput,
        Generated.fromMatchFirst, GeneratedArms.fromFirst] using bodyEquality
    · rw [hardLeft]
      simpa [FreshAliasSequence.addAll_pending, leftOutput, rightOutput,
        completedArmState, seedGenerated, seedItems, initialArmState,
        armStateGenerated, Generated.fromMatchFirst, GeneratedArms.fromFirst,
        GeneratedTail.fromArm, GeneratedItems.asTuple, GeneratedItems.cons,
        GeneratedItems.singleton, GeneratedItems.nil, List.append_assoc] using
        certificate.aligned.pendingAligned

private theorem stateItems_supportMF
    {context : Context} {start finish : Supply}
    {state : Generated} {pattern : GeneratedPattern} {body : Generated}
    (stateSupport : GeneratedSupportProvenance context start finish state)
    (patternSupport : GeneratedSupportProvenance context start finish
      (patternAsGenerated pattern))
    (bodySupport : GeneratedSupportProvenance context start finish body) :
    GeneratedItemsSupportProvenance context start finish
      (stateItems state pattern body) := by
  intro candidate member
  have firstSplit :
      candidate ∈ (GeneratedItems.singleton state).unificationVars ∨
        candidate ∈
          (GeneratedItems.cons (patternAsGenerated pattern)
            (GeneratedItems.singleton body)).unificationVars := by
    apply (GeneratedItems.mem_unificationVars_append candidate
      (GeneratedItems.singleton state)
      (GeneratedItems.cons (patternAsGenerated pattern)
        (GeneratedItems.singleton body))).mp
    simpa [stateItems, GeneratedItems.append, GeneratedItems.singleton,
      GeneratedItems.cons, GeneratedItems.nil, List.append_assoc] using member
  rcases firstSplit with stateMember | tailMember
  · exact stateSupport candidate (by simpa using stateMember)
  · have secondSplit :
        candidate ∈
            (GeneratedItems.singleton
              (patternAsGenerated pattern)).unificationVars ∨
          candidate ∈ (GeneratedItems.singleton body).unificationVars := by
      apply (GeneratedItems.mem_unificationVars_append candidate
        (GeneratedItems.singleton (patternAsGenerated pattern))
        (GeneratedItems.singleton body)).mp
      simpa [GeneratedItems.append, GeneratedItems.singleton,
        GeneratedItems.cons, GeneratedItems.nil, List.append_assoc] using
        tailMember
    rcases secondSplit with patternMember | bodyMember
    · exact patternSupport candidate (by simpa using patternMember)
    · exact bodySupport candidate (by simpa using bodyMember)

private theorem seedGenerated_supportMF
    {context : Context} {start finish : Supply}
    {target matcher : Generated}
    (targetSupport : GeneratedSupportProvenance context start finish target)
    (matcherSupport : GeneratedSupportProvenance context start finish matcher) :
    GeneratedSupportProvenance context start finish
      (seedGenerated target matcher) := by
  intro candidate member
  have itemsMember : candidate ∈ (seedItems target matcher).unificationVars := by
    simpa [seedGenerated, seedItems, GeneratedItems.asTuple,
      Generated.unificationVars, GeneratedItems.unificationVars,
      Ty.unificationVars] using member
  have origin : candidate ∈ target.unificationVars ∨
      candidate ∈ matcher.unificationVars := by
    have split := (GeneratedItems.mem_unificationVars_append candidate
      (GeneratedItems.singleton target)
      (GeneratedItems.singleton matcher)).mp (by
        simpa [seedItems, GeneratedItems.append, GeneratedItems.singleton,
          GeneratedItems.cons, GeneratedItems.nil, List.append_assoc] using
          itemsMember)
    simpa using split
  exact Or.elim origin (targetSupport candidate) (matcherSupport candidate)

private theorem initialArmState_supportMF
    {context : Context} {start finish : Supply}
    {targetType matcherType : Ty} {seed : Generated}
    {pattern : GeneratedPattern} {body : Generated}
    (seedTarget : seed.target = .prod [targetType, matcherType])
    (itemsSupport : GeneratedItemsSupportProvenance context start finish
      (stateItems seed pattern body)) :
    GeneratedSupportProvenance context start finish
      (initialArmState targetType matcherType seed pattern body) := by
  intro candidate member
  exact itemsSupport candidate
    ((initialState_vars_iff targetType matcherType seed pattern body seedTarget
      candidate).mpr member)

private theorem extendArmState_supportMF
    {context : Context} {start finish : Supply}
    {targetType matcherType expected : Ty}
    {hard : List Equation} {pending : List CheckObligation}
    {pattern : GeneratedPattern} {body : Generated}
    (itemsSupport : GeneratedItemsSupportProvenance context start finish
      (stateItems
        (armStateGenerated (.prod [targetType, matcherType]) expected
          hard pending)
        pattern body)) :
    GeneratedSupportProvenance context start finish
      (extendArmState targetType matcherType expected
        (armStateGenerated (.prod [targetType, matcherType]) expected
          hard pending)
        pattern body) := by
  intro candidate member
  exact itemsSupport candidate
    ((extendedState_vars_iff targetType matcherType expected hard pending pattern
      body candidate).mpr member)

set_option maxRecDepth 4096

private theorem foldTailSupported
    {limit : Nat} {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    (signatureWellFormed : signature.WellFormed)
    (expressionPair : SupportedM4ExpressionPairPropertyBelow
      signature leftFuel rightFuel limit)
    {context : Context} {root current : Supply}
    (wellFormed : root.WellFormedFor context)
    (rootToCurrent : root.Le current)
    {leftTargetType rightTargetType leftMatcherType rightMatcherType : Ty}
    {leftExpected rightExpected : Ty}
    {leftHard rightHard : List Equation}
    {leftPending rightPending : List CheckObligation}
    (leftStateSupport : GeneratedSupportProvenance context root current
      (armStateGenerated (.prod [leftTargetType, leftMatcherType])
        leftExpected leftHard leftPending))
    (rightStateSupport : GeneratedSupportProvenance context root current
      (armStateGenerated (.prod [rightTargetType, rightMatcherType])
        rightExpected rightHard rightPending))
    (stateCertificate : SupportedEntailedAlignmentCertificate root current
      (armStateGenerated (.prod [leftTargetType, leftMatcherType])
        leftExpected leftHard leftPending)
      (armStateGenerated (.prod [rightTargetType, rightMatcherType])
        rightExpected rightHard rightPending))
    {arms : List MatchFirstArm}
    {leftTail rightTail : GeneratedTail} {leftNext rightNext : Supply}
    (complexityBound : MatchFirstArm.listComplexity arms < limit)
    (leftDerivation : TailElaboratesUsing
      (ElaboratesFuel signature leftFuel) signature context leftTargetType
      leftMatcherType leftExpected arms current leftTail leftNext)
    (rightDerivation : TailElaboratesUsing
      (ElaboratesFuel signature rightFuel) signature context rightTargetType
      rightMatcherType rightExpected arms current rightTail rightNext) :
    Nonempty (SupportedM2PairCoherence root leftNext rightNext
      (armStateGenerated (.prod [leftTargetType, leftMatcherType]) leftExpected
        (leftHard ++ leftTail.hard) (leftPending ++ leftTail.pending))
      (armStateGenerated (.prod [rightTargetType, rightMatcherType])
        rightExpected (rightHard ++ rightTail.hard)
        (rightPending ++ rightTail.pending))) := by
  cases leftDerivation with
  | nil =>
      cases rightDerivation
      simpa using Nonempty.intro
        ({ next_eq := rfl, certificate := stateCertificate } :
          SupportedM2PairCoherence root current current
            (armStateGenerated (.prod [leftTargetType, leftMatcherType])
              leftExpected leftHard leftPending)
            (armStateGenerated (.prod [rightTargetType, rightMatcherType])
              rightExpected rightHard rightPending))
  | @cons pattern body arms current leftPattern afterPattern leftBody
      afterBody leftRest leftNext leftPatternDerivation leftBodyDerivation
      leftRestDerivation =>
      cases rightDerivation with
      | @cons _ _ _ _ rightPattern rightAfterPattern rightBody rightAfterBody
          rightRest rightNext rightPatternDerivation rightBodyDerivation
          rightRestDerivation =>
          have emptyArguments : VariablesSupportProvenance context root current
              (dualUnificationVars []) := by
            intro candidate member
            simp [dualUnificationVars] at member
          have emptyBindings : VariablesSupportProvenance context root current
              (Ty.unificationVarsList []) := by
            intro candidate member
            simp [Ty.unificationVarsList] at member
          obtain ⟨patternResult⟩ :=
            PatternElaboratesUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp only [MatchFirstArm.listComplexity_cons,
                  MatchFirstArm.complexity_mk] at complexityBound
                omega) wellFormed emptyArguments emptyBindings rootToCurrent
              leftPatternDerivation rightPatternDerivation
          cases patternResult.next_eq
          rw [← patternResult.bindings_eq] at rightBodyDerivation
          have currentToPattern := leftPatternDerivation.supply_le_next
            (fun child => child.supply_le_next)
          have rootToPattern := Supply.le_trans rootToCurrent currentToPattern
          have leftPatternSupport := leftPatternDerivation.supportProvenance
            signatureWellFormed (fun child => child.supply_le_next)
            (fun child => child.supportProvenance signatureWellFormed)
            emptyArguments emptyBindings rootToCurrent
          have rightPatternSupport := rightPatternDerivation.supportProvenance
            signatureWellFormed (fun child => child.supply_le_next)
            (fun child => child.supportProvenance signatureWellFormed)
            emptyArguments emptyBindings rootToCurrent
          have bindingsSupport : VariablesSupportProvenance context root
              afterPattern (Ty.unificationVarsList leftPattern.bindings) := by
            intro candidate member
            exact leftPatternSupport candidate (by
              simp [GeneratedPattern.unificationVars, member])
          have bodyContextSupport := Pattern.extendContext_support
            bindingsSupport
          have bodyWellFormed :=
            M4FreshRenaming.Supply.WellFormedFor.of_contextSupport
              wellFormed rootToPattern bodyContextSupport
          obtain ⟨bodyResult⟩ := expressionPair (by
              simp only [MatchFirstArm.listComplexity_cons,
                MatchFirstArm.complexity_mk] at complexityBound
              omega) bodyWellFormed leftBodyDerivation rightBodyDerivation
          cases bodyResult.next_eq
          have patternToBody := leftBodyDerivation.supply_le_next
          have currentToBody := Supply.le_trans currentToPattern patternToBody
          have rootToBody := Supply.le_trans rootToCurrent currentToBody

          have stateContextAvoid := context_avoids_laterFreshMF wellFormed
            (Supply.le_refl root) stateCertificate.hiddenFresh
          have stateBelow := freshIn_to_belowFinishMF
            stateCertificate.hiddenFresh
          have leftPatternAvoidState :=
            PatternElaboratesUsing.avoids_of_inputs signatureWellFormed
              stateContextAvoid
              (by intro candidate member; simp [dualUnificationVars] at member)
              (by intro candidate member; simp [Ty.unificationVarsList] at member)
              stateBelow
              leftPatternDerivation
          have rightPatternAvoidState :=
            PatternElaboratesUsing.avoids_of_inputs signatureWellFormed
              stateContextAvoid
              (by intro candidate member; simp [dualUnificationVars] at member)
              (by intro candidate member; simp [Ty.unificationVarsList] at member)
              stateBelow
              rightPatternDerivation
          have leftBodySupportLocal := leftBodyDerivation.supportProvenance
            signatureWellFormed
          have rightBodySupportLocal := rightBodyDerivation.supportProvenance
            signatureWellFormed
          have leftBodyAvoidState := generatedAvoids_of_supportMF
            (extendedContext_avoidsMF stateContextAvoid
              leftPatternAvoidState.bindings)
            (stateBelow.mono currentToPattern) leftBodySupportLocal
          have rightBodyAvoidState := generatedAvoids_of_supportMF
            (extendedContext_avoidsMF stateContextAvoid
              leftPatternAvoidState.bindings)
            (stateBelow.mono currentToPattern) rightBodySupportLocal

          have patternContextAvoid := context_avoids_laterFreshMF wellFormed
            rootToCurrent patternResult.certificate.hiddenFresh
          have patternBelow := freshIn_to_belowFinishMF
            patternResult.certificate.hiddenFresh
          have leftBodyAvoidPattern := generatedAvoids_of_supportMF
            (extendedContext_avoidsMF patternContextAvoid
              patternResult.leftBindingsAvoid)
            patternBelow leftBodySupportLocal
          have rightBodyAvoidPattern := generatedAvoids_of_supportMF
            (extendedContext_avoidsMF patternContextAvoid
              patternResult.leftBindingsAvoid)
            patternBelow rightBodySupportLocal

          have leftPatternBlockSupport := patternAsGenerated_supportMF
            leftPatternSupport
          have rightPatternBlockSupport := patternAsGenerated_supportMF
            rightPatternSupport
          have leftStateAvoidPattern := support_avoids_laterFreshMF
            wellFormed rootToCurrent leftStateSupport
            patternResult.certificate.hiddenFresh
          have rightStateAvoidPattern := support_avoids_laterFreshMF
            wellFormed rootToCurrent rightStateSupport
            patternResult.certificate.hiddenFresh
          have leftPatternAvoidBody := support_avoids_laterFreshMF
            wellFormed rootToPattern
            leftPatternBlockSupport bodyResult.certificate.hiddenFresh
          have rightPatternAvoidBody := support_avoids_laterFreshMF
            wellFormed rootToPattern
            rightPatternBlockSupport bodyResult.certificate.hiddenFresh
          have leftStateAvoidBody := support_avoids_laterFreshMF
            wellFormed rootToCurrent leftStateSupport
            (bodyResult.certificate.hiddenFresh.widen currentToPattern
              (Supply.le_refl afterBody))
          have rightStateAvoidBody := support_avoids_laterFreshMF
            wellFormed rootToCurrent rightStateSupport
            (bodyResult.certificate.hiddenFresh.widen currentToPattern
              (Supply.le_refl afterBody))

          let patternBody := itemsConsSequentialMF patternResult.certificate
            (singletonItemsCertificate bodyResult.certificate)
            currentToPattern patternToBody
            (GeneratedItemsAvoid.singleton leftBodyAvoidPattern)
            (GeneratedItemsAvoid.singleton rightBodyAvoidPattern)
            leftPatternAvoidBody rightPatternAvoidBody
          let allItems := itemsConsSequentialMF stateCertificate patternBody
            rootToCurrent currentToBody
            (generatedItemsAvoid_consMF leftPatternAvoidState.block
              (GeneratedItemsAvoid.singleton leftBodyAvoidState))
            (generatedItemsAvoid_consMF rightPatternAvoidState.block
              (GeneratedItemsAvoid.singleton rightBodyAvoidState))
            (by
              change GeneratedAvoids patternBody.hidden _
              rw [show patternBody.hidden =
                patternResult.certificate.hidden ++
                  bodyResult.certificate.hidden by rfl]
              exact generatedAvoids_appendMF leftStateAvoidPattern
                leftStateAvoidBody)
            (by
              change GeneratedAvoids patternBody.hidden _
              rw [show patternBody.hidden =
                patternResult.certificate.hidden ++
                  bodyResult.certificate.hidden by rfl]
              exact generatedAvoids_appendMF rightStateAvoidPattern
                rightStateAvoidBody)
          have statePendingLength : leftPending.length = rightPending.length := by
            simpa [FreshAliasSequence.addAll_pending, armStateGenerated] using
              pendingLength_eq stateCertificate.aligned.pendingAligned
          have patternPendingLength : leftPattern.pending.length =
              rightPattern.pending.length := by
            simpa [FreshAliasSequence.addAll_pending, patternAsGenerated] using
              pendingLength_eq patternResult.certificate.aligned.pendingAligned
          let nextCertificate := supportedExtendArmState statePendingLength
            patternPendingLength allItems

          have leftBodySupport : GeneratedSupportProvenance context root
              afterBody leftBody :=
            leftBodySupportLocal.rebase_context rootToPattern patternToBody
              bodyContextSupport
          have rightBodySupport : GeneratedSupportProvenance context root
              afterBody rightBody :=
            rightBodySupportLocal.rebase_context rootToPattern patternToBody
              bodyContextSupport
          have leftItemsSupport := stateItems_supportMF
            (leftStateSupport.extend_finish currentToBody)
            (leftPatternBlockSupport.extend_finish patternToBody)
            leftBodySupport
          have rightItemsSupport := stateItems_supportMF
            (rightStateSupport.extend_finish currentToBody)
            (rightPatternBlockSupport.extend_finish patternToBody)
            rightBodySupport
          have leftNextStateSupport := extendArmState_supportMF
            leftItemsSupport
          have rightNextStateSupport := extendArmState_supportMF
            rightItemsSupport

          let leftNextHard := leftHard ++
            [.ty leftPattern.dual.target leftTargetType] ++
              leftPattern.hard ++ leftBody.hard ++
                [.ty leftBody.target leftExpected]
          let rightNextHard := rightHard ++
            [.ty rightPattern.dual.target rightTargetType] ++
              rightPattern.hard ++ rightBody.hard ++
                [.ty rightBody.target rightExpected]
          let leftNextPending := leftPending ++ leftPattern.pending ++
            [⟨leftMatcherType,
              .slot leftPattern.dual.capability leftTargetType⟩] ++
              leftBody.pending
          let rightNextPending := rightPending ++ rightPattern.pending ++
            [⟨rightMatcherType,
              .slot rightPattern.dual.capability rightTargetType⟩] ++
              rightBody.pending
          obtain ⟨restResult⟩ := foldTailSupported signatureWellFormed
            expressionPair wellFormed rootToBody
            (leftStateSupport := by
              simpa [leftNextHard, leftNextPending, extendArmState,
                armStateGenerated, List.append_assoc] using leftNextStateSupport)
            (rightStateSupport := by
              simpa [rightNextHard, rightNextPending, extendArmState,
                armStateGenerated, List.append_assoc] using rightNextStateSupport)
            (stateCertificate := by
              simpa [nextCertificate, leftNextHard, rightNextHard,
                leftNextPending, rightNextPending, extendArmState,
                armStateGenerated, List.append_assoc] using nextCertificate)
            (by
              simp only [MatchFirstArm.listComplexity_cons] at complexityBound
              omega)
            leftRestDerivation rightRestDerivation
          exact ⟨
            { next_eq := restResult.next_eq
              certificate := by
                simpa [leftNextHard, rightNextHard, leftNextPending,
                  rightNextPending, GeneratedTail.fromArm,
                  armStateGenerated, List.append_assoc] using
                  restResult.certificate }⟩
termination_by arms.length

/-- Supported coherence for the ordered single-result match constructor. -/
theorem matchFirstSupportedFuelPair
    (target matcher : Expr) (arms : List MatchFirstArm)
    (induction : ∀ smaller : Expr,
      smaller.complexity < (Expr.matchFirst target matcher arms).complexity →
        FullM4FuelPairProperty smaller) :
    SupportedM4FuelPairProperty (.matchFirst target matcher arms) := by
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
          | @matchFirst _ _ _ _ leftTarget afterTarget leftMatcher
              afterMatcher leftArms finish leftExhaustive
              leftTargetDerivation leftMatcherDerivation leftArmsDerivation =>
              cases rightDerivation with
              | @matchFirst _ _ _ _ rightTarget rightAfterTarget rightMatcher
                  rightAfterMatcher rightArms rightFinish rightExhaustive
                  rightTargetDerivation rightMatcherDerivation
                  rightArmsDerivation =>
                  have expressionPairBelow :
                      SupportedM4ExpressionPairPropertyBelow signature
                        leftFuel rightFuel
                        (Expr.matchFirst target matcher arms).complexity := by
                    intro childContext expression childStart left right
                      childLeftNext childRightNext complexity childWellFormed
                      childLeft childRight
                    exact FullM4FuelPairProperty.toSupported
                      (induction expression complexity) signatureWellFormed
                      childWellFormed childLeft childRight
                  obtain ⟨targetResult⟩ :=
                    FullM4FuelPairProperty.toSupported
                      (induction target (by
                        simp only [Expr.complexity_matchFirst]
                        omega)) signatureWellFormed wellFormed
                      leftTargetDerivation rightTargetDerivation
                  cases targetResult.next_eq
                  have startToTarget := leftTargetDerivation.supply_le_next
                  obtain ⟨matcherResult⟩ :=
                    FullM4FuelPairProperty.toSupported
                      (induction matcher (by
                        simp only [Expr.complexity_matchFirst]
                        omega)) signatureWellFormed
                      (wellFormed.mono startToTarget)
                      leftMatcherDerivation rightMatcherDerivation
                  cases matcherResult.next_eq
                  have targetToMatcher := leftMatcherDerivation.supply_le_next
                  have startToMatcher := Supply.le_trans startToTarget
                    targetToMatcher
                  cases leftArmsDerivation with
                  | @cons pattern body tail _ leftPattern afterPattern leftBody
                      afterBody leftTail finish leftPatternDerivation
                      leftBodyDerivation leftTailDerivation =>
                      cases rightArmsDerivation with
                      | @cons _ _ _ _ rightPattern rightAfterPattern rightBody
                          rightAfterBody rightTail rightFinish
                          rightPatternDerivation rightBodyDerivation
                          rightTailDerivation =>
                          have emptyArguments : VariablesSupportProvenance
                              context start afterMatcher
                              (dualUnificationVars []) := by
                            intro candidate member
                            simp [dualUnificationVars] at member
                          have emptyBindings : VariablesSupportProvenance
                              context start afterMatcher
                              (Ty.unificationVarsList []) := by
                            intro candidate member
                            simp [Ty.unificationVarsList] at member
                          obtain ⟨patternResult⟩ :=
                            PatternElaboratesUsing.supportedFuelPairCoherenceBelow
                              signatureWellFormed expressionPairBelow (by
                                simp only [Expr.complexity_matchFirst,
                                  MatchFirstArm.listComplexity_cons,
                                  MatchFirstArm.complexity_mk]
                                omega) wellFormed emptyArguments emptyBindings
                              startToMatcher leftPatternDerivation
                              rightPatternDerivation
                          cases patternResult.next_eq
                          rw [← patternResult.bindings_eq] at rightBodyDerivation
                          have matcherToPattern :=
                            leftPatternDerivation.supply_le_next
                              (fun child => child.supply_le_next)
                          have startToPattern := Supply.le_trans startToMatcher
                            matcherToPattern
                          have leftPatternSupport :=
                            leftPatternDerivation.supportProvenance
                              signatureWellFormed
                              (fun child => child.supply_le_next)
                              (fun child =>
                                child.supportProvenance signatureWellFormed)
                              emptyArguments emptyBindings startToMatcher
                          have rightPatternSupport :=
                            rightPatternDerivation.supportProvenance
                              signatureWellFormed
                              (fun child => child.supply_le_next)
                              (fun child =>
                                child.supportProvenance signatureWellFormed)
                              emptyArguments emptyBindings startToMatcher
                          have bindingsSupport : VariablesSupportProvenance
                              context start afterPattern
                              (Ty.unificationVarsList leftPattern.bindings) := by
                            intro candidate member
                            exact leftPatternSupport candidate (by
                              simp [GeneratedPattern.unificationVars, member])
                          have bodyContextSupport :=
                            Pattern.extendContext_support bindingsSupport
                          have bodyWellFormed :=
                            M4FreshRenaming.Supply.WellFormedFor.of_contextSupport
                              wellFormed startToPattern bodyContextSupport
                          obtain ⟨bodyResult⟩ := expressionPairBelow (by
                              simp only [Expr.complexity_matchFirst,
                                MatchFirstArm.listComplexity_cons,
                                MatchFirstArm.complexity_mk]
                              omega) bodyWellFormed leftBodyDerivation
                            rightBodyDerivation
                          cases bodyResult.next_eq
                          have patternToBody :=
                            leftBodyDerivation.supply_le_next
                          have matcherToBody := Supply.le_trans
                            matcherToPattern patternToBody
                          have startToBody := Supply.le_trans startToMatcher
                            matcherToBody

                          have targetSupportLeft :=
                            leftTargetDerivation.supportProvenance
                              signatureWellFormed
                          have targetSupportRight :=
                            rightTargetDerivation.supportProvenance
                              signatureWellFormed
                          have matcherSupportLeft :=
                            leftMatcherDerivation.supportProvenance
                              signatureWellFormed
                          have matcherSupportRight :=
                            rightMatcherDerivation.supportProvenance
                              signatureWellFormed
                          have targetContextAvoid :=
                            context_avoids_laterFreshMF wellFormed
                              (Supply.le_refl start)
                              targetResult.certificate.hiddenFresh
                          have targetBelow := freshIn_to_belowFinishMF
                            targetResult.certificate.hiddenFresh
                          have leftMatcherAvoidTarget :=
                            generatedAvoids_of_supportMF targetContextAvoid
                              targetBelow matcherSupportLeft
                          have rightMatcherAvoidTarget :=
                            generatedAvoids_of_supportMF targetContextAvoid
                              targetBelow matcherSupportRight
                          have leftTargetAvoidMatcher :=
                            support_avoids_laterFreshMF wellFormed startToTarget
                              targetSupportLeft
                              matcherResult.certificate.hiddenFresh
                          have rightTargetAvoidMatcher :=
                            support_avoids_laterFreshMF wellFormed startToTarget
                              targetSupportRight
                              matcherResult.certificate.hiddenFresh
                          let seedItemsCertificate := itemsConsSequentialMF
                            targetResult.certificate
                            (singletonItemsCertificate
                              matcherResult.certificate)
                            startToTarget targetToMatcher
                            (GeneratedItemsAvoid.singleton
                              leftMatcherAvoidTarget)
                            (GeneratedItemsAvoid.singleton
                              rightMatcherAvoidTarget)
                            leftTargetAvoidMatcher rightTargetAvoidMatcher
                          let seedCertificate :=
                            seedItemsCertificate.itemsTuple
                          have leftSeedSupport := seedGenerated_supportMF
                            (targetSupportLeft.extend_finish targetToMatcher)
                            (matcherSupportLeft.lower_start startToTarget)
                          have rightSeedSupport := seedGenerated_supportMF
                            (targetSupportRight.extend_finish targetToMatcher)
                            (matcherSupportRight.lower_start startToTarget)

                          have seedContextAvoid :=
                            context_avoids_laterFreshMF wellFormed
                              (Supply.le_refl start)
                              seedCertificate.hiddenFresh
                          have seedBelow := freshIn_to_belowFinishMF
                            seedCertificate.hiddenFresh
                          have leftPatternAvoidSeed :=
                            PatternElaboratesUsing.avoids_of_inputs
                              signatureWellFormed seedContextAvoid
                              (by
                                intro candidate member
                                simp [dualUnificationVars] at member)
                              (by
                                intro candidate member
                                simp [Ty.unificationVarsList] at member)
                              seedBelow leftPatternDerivation
                          have rightPatternAvoidSeed :=
                            PatternElaboratesUsing.avoids_of_inputs
                              signatureWellFormed seedContextAvoid
                              (by
                                intro candidate member
                                simp [dualUnificationVars] at member)
                              (by
                                intro candidate member
                                simp [Ty.unificationVarsList] at member)
                              seedBelow rightPatternDerivation
                          have leftBodySupportLocal :=
                            leftBodyDerivation.supportProvenance
                              signatureWellFormed
                          have rightBodySupportLocal :=
                            rightBodyDerivation.supportProvenance
                              signatureWellFormed
                          have leftBodyAvoidSeed := generatedAvoids_of_supportMF
                            (extendedContext_avoidsMF seedContextAvoid
                              leftPatternAvoidSeed.bindings)
                            (seedBelow.mono matcherToPattern)
                            leftBodySupportLocal
                          have rightBodyAvoidSeed :=
                            generatedAvoids_of_supportMF
                              (extendedContext_avoidsMF seedContextAvoid
                                leftPatternAvoidSeed.bindings)
                              (seedBelow.mono matcherToPattern)
                              rightBodySupportLocal
                          have patternContextAvoid :=
                            context_avoids_laterFreshMF wellFormed
                              startToMatcher
                              patternResult.certificate.hiddenFresh
                          have patternBelow := freshIn_to_belowFinishMF
                            patternResult.certificate.hiddenFresh
                          have leftBodyAvoidPattern :=
                            generatedAvoids_of_supportMF
                              (extendedContext_avoidsMF patternContextAvoid
                                patternResult.leftBindingsAvoid)
                              patternBelow leftBodySupportLocal
                          have rightBodyAvoidPattern :=
                            generatedAvoids_of_supportMF
                              (extendedContext_avoidsMF patternContextAvoid
                                patternResult.leftBindingsAvoid)
                              patternBelow rightBodySupportLocal
                          have leftPatternBlockSupport :=
                            patternAsGenerated_supportMF leftPatternSupport
                          have rightPatternBlockSupport :=
                            patternAsGenerated_supportMF rightPatternSupport
                          have leftSeedAvoidPattern :=
                            support_avoids_laterFreshMF wellFormed
                              startToMatcher leftSeedSupport
                              patternResult.certificate.hiddenFresh
                          have rightSeedAvoidPattern :=
                            support_avoids_laterFreshMF wellFormed
                              startToMatcher rightSeedSupport
                              patternResult.certificate.hiddenFresh
                          have leftPatternAvoidBody :=
                            support_avoids_laterFreshMF wellFormed
                              startToPattern leftPatternBlockSupport
                              bodyResult.certificate.hiddenFresh
                          have rightPatternAvoidBody :=
                            support_avoids_laterFreshMF wellFormed
                              startToPattern rightPatternBlockSupport
                              bodyResult.certificate.hiddenFresh
                          have leftSeedAvoidBody :=
                            support_avoids_laterFreshMF wellFormed
                              startToMatcher leftSeedSupport
                              (bodyResult.certificate.hiddenFresh.widen
                                matcherToPattern
                                (Supply.le_refl afterBody))
                          have rightSeedAvoidBody :=
                            support_avoids_laterFreshMF wellFormed
                              startToMatcher rightSeedSupport
                              (bodyResult.certificate.hiddenFresh.widen
                                matcherToPattern
                                (Supply.le_refl afterBody))
                          let patternBody := itemsConsSequentialMF
                            patternResult.certificate
                            (singletonItemsCertificate bodyResult.certificate)
                            matcherToPattern patternToBody
                            (GeneratedItemsAvoid.singleton
                              leftBodyAvoidPattern)
                            (GeneratedItemsAvoid.singleton
                              rightBodyAvoidPattern)
                            leftPatternAvoidBody rightPatternAvoidBody
                          let initialItems := itemsConsSequentialMF
                            seedCertificate patternBody startToMatcher
                            matcherToBody
                            (generatedItemsAvoid_consMF
                              leftPatternAvoidSeed.block
                              (GeneratedItemsAvoid.singleton
                                leftBodyAvoidSeed))
                            (generatedItemsAvoid_consMF
                              rightPatternAvoidSeed.block
                              (GeneratedItemsAvoid.singleton
                                rightBodyAvoidSeed))
                            (by
                              change GeneratedAvoids patternBody.hidden _
                              rw [show patternBody.hidden =
                                patternResult.certificate.hidden ++
                                  bodyResult.certificate.hidden by rfl]
                              exact generatedAvoids_appendMF
                                leftSeedAvoidPattern leftSeedAvoidBody)
                            (by
                              change GeneratedAvoids patternBody.hidden _
                              rw [show patternBody.hidden =
                                patternResult.certificate.hidden ++
                                  bodyResult.certificate.hidden by rfl]
                              exact generatedAvoids_appendMF
                                rightSeedAvoidPattern rightSeedAvoidBody)
                          have seedPendingLength :
                              (seedGenerated leftTarget leftMatcher).pending.length =
                                (seedGenerated rightTarget rightMatcher).pending.length := by
                            simpa [FreshAliasSequence.addAll_pending,
                              seedGenerated, seedItems] using
                              pendingLength_eq
                                seedCertificate.aligned.pendingAligned
                          have patternPendingLength :
                              leftPattern.pending.length =
                                rightPattern.pending.length := by
                            simpa [FreshAliasSequence.addAll_pending,
                              patternAsGenerated] using
                              pendingLength_eq
                                patternResult.certificate.aligned.pendingAligned
                          let initialCertificate := supportedInitialArmState
                            (leftTargetType := leftTarget.target)
                            (rightTargetType := rightTarget.target)
                            (leftMatcherType := leftMatcher.target)
                            (rightMatcherType := rightMatcher.target)
                            (leftSeed := seedGenerated leftTarget leftMatcher)
                            (rightSeed := seedGenerated rightTarget rightMatcher)
                            (leftPattern := leftPattern)
                            (rightPattern := rightPattern)
                            (leftBody := leftBody) (rightBody := rightBody)
                            (leftSeedTarget := by
                              simp [seedGenerated, seedItems,
                                GeneratedItems.asTuple,
                                GeneratedItems.cons, GeneratedItems.singleton,
                                GeneratedItems.nil])
                            (rightSeedTarget := by
                              simp [seedGenerated, seedItems,
                                GeneratedItems.asTuple,
                                GeneratedItems.cons, GeneratedItems.singleton,
                                GeneratedItems.nil])
                            seedPendingLength patternPendingLength initialItems

                          have leftBodySupport : GeneratedSupportProvenance
                              context start afterBody leftBody :=
                            leftBodySupportLocal.rebase_context startToPattern
                              patternToBody bodyContextSupport
                          have rightBodySupport : GeneratedSupportProvenance
                              context start afterBody rightBody :=
                            rightBodySupportLocal.rebase_context startToPattern
                              patternToBody bodyContextSupport
                          have leftInitialItemsSupport := stateItems_supportMF
                            (leftSeedSupport.extend_finish matcherToBody)
                            (leftPatternBlockSupport.extend_finish patternToBody)
                            leftBodySupport
                          have rightInitialItemsSupport := stateItems_supportMF
                            (rightSeedSupport.extend_finish matcherToBody)
                            (rightPatternBlockSupport.extend_finish patternToBody)
                            rightBodySupport
                          have leftInitialSupport := initialArmState_supportMF
                            (targetType := leftTarget.target)
                            (matcherType := leftMatcher.target)
                            (seed := seedGenerated leftTarget leftMatcher)
                            (pattern := leftPattern) (body := leftBody)
                            (seedTarget := by
                              simp [seedGenerated, seedItems,
                                GeneratedItems.asTuple,
                                GeneratedItems.cons, GeneratedItems.singleton,
                                GeneratedItems.nil])
                            leftInitialItemsSupport
                          have rightInitialSupport := initialArmState_supportMF
                            (targetType := rightTarget.target)
                            (matcherType := rightMatcher.target)
                            (seed := seedGenerated rightTarget rightMatcher)
                            (pattern := rightPattern) (body := rightBody)
                            (seedTarget := by
                              simp [seedGenerated, seedItems,
                                GeneratedItems.asTuple,
                                GeneratedItems.cons, GeneratedItems.singleton,
                                GeneratedItems.nil])
                            rightInitialItemsSupport
                          let leftInitial := initialArmState leftTarget.target
                            leftMatcher.target
                            (seedGenerated leftTarget leftMatcher) leftPattern
                            leftBody
                          let rightInitial := initialArmState rightTarget.target
                            rightMatcher.target
                            (seedGenerated rightTarget rightMatcher) rightPattern
                            rightBody
                          obtain ⟨tailResult⟩ := foldTailSupported
                            signatureWellFormed expressionPairBelow wellFormed
                            startToBody
                            (leftStateSupport := by
                              simpa [leftInitial, initialArmState,
                                armStateGenerated] using leftInitialSupport)
                            (rightStateSupport := by
                              simpa [rightInitial, initialArmState,
                                armStateGenerated] using rightInitialSupport)
                            (stateCertificate := by
                              simpa [initialCertificate, leftInitial,
                                rightInitial, initialArmState,
                                armStateGenerated] using initialCertificate)
                            (by
                              simp only [Expr.complexity_matchFirst,
                                MatchFirstArm.listComplexity_cons,
                                MatchFirstArm.complexity_mk]
                              omega)
                            leftTailDerivation rightTailDerivation
                          cases tailResult.next_eq
                          have completedCertificate :
                              SupportedEntailedAlignmentCertificate start leftNext
                                (completedArmState leftTarget leftMatcher
                                  leftPattern leftBody leftTail)
                                (completedArmState rightTarget rightMatcher
                                  rightPattern rightBody rightTail) := by
                            simpa [completedArmState, leftInitial, rightInitial,
                              initialArmState, armStateGenerated] using
                              tailResult.certificate
                          exact ⟨
                            { next_eq := rfl
                              certificate := supportedFinishArmState
                                completedCertificate }⟩

/-- The architecture-level semantic step for ordered single-result matching. -/
theorem matchFirstCoherenceStep : MatchFirstCoherenceStep := by
  intro target matcher arms induction
  exact SupportedM4FuelPairProperty.toFull
    (matchFirstSupportedFuelPair target matcher arms induction)

end TypePM.Source.M4.CompletenessArchitecture
