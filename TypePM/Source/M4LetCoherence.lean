import TypePM.Source.FullM2GraphAliasPresentation
import TypePM.Source.M4FreshRenamingTransport
import TypePM.Source.M4SupportedCoherence

/-!
# Coherence for M4 let roots

The representative-sensitive generated-block assembly used by M2 depends on
source derivations only through supply monotonicity, generated support, and
fresh-renaming transport.  M4 provides those facts for its fuel-indexed
relation.  This module supplies the small support-based adapters and reuses
the completed visible-graph whole-let composition.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source
open FreshAliasSequence
open InterfaceAliasDecomposition
open InterfaceAliasDecomposition.AliasFreshness

private theorem leftAlias_mem_hidden
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    ∀ alias, alias ∈ VisibleSupportGraph.leftAliases data context →
      freshVariable alias ∈ VisibleSupportGraph.leftHidden data context := by
  intro alias member
  rcases List.mem_append.mp member with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩

private theorem rightAlias_mem_hidden
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    ∀ alias, alias ∈ VisibleSupportGraph.rightAliases data context →
      freshVariable alias ∈ VisibleSupportGraph.rightHidden data context := by
  intro alias member
  rcases List.mem_append.mp member with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩

/-- The M2 visible closure graph needs only support provenance from the value
derivation, so it applies unchanged to an M4 value block. -/
private theorem letGraphAliasPresentation_of_support
    {context : Context} {start afterValue : Supply}
    {leftValue rightValue : Generated}
    (wellFormed : start.WellFormedFor context)
    (rightProvenance : GeneratedSupportProvenance context start afterValue
      rightValue)
    (certificate : SupportedEntailedAlignmentCertificate start afterValue
      leftValue rightValue)
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (leftAbsorbing : leftClosure.Absorbing)
    (rightAbsorbing : rightClosure.Absorbing) :
    Nonempty (LetGraphAliasPresentation start afterValue
      (context.interfaceEquations leftClosure.substitution)
      (context.interfaceEquations rightClosure.substitution)
      ((context.applyFree leftClosure.substitution).generalize
          leftClosure.target :: context.applyFree leftClosure.substitution)
      ((context.applyFree rightClosure.substitution).generalize
          rightClosure.target :: context.applyFree rightClosure.substitution)) := by
  have leftFresh : ∀ alias, alias ∈ certificate.leftAliases →
      (freshVariable alias).FreshIn start afterValue := by
    intro alias member
    exact certificate.hiddenFresh _ (certificate.leftAliasFresh alias member)
  have rightFresh : ∀ alias, alias ∈ certificate.rightAliases →
      (freshVariable alias).FreshIn start afterValue := by
    intro alias member
    exact certificate.hiddenFresh _ (certificate.rightAliasFresh alias member)
  have leftContextFixed : CumulativeAliasContextFixed
      certificate.leftAliases leftClosure context :=
    cumulativeAliasContextFixed_of_scopedBy_sourceFresh
      certificate.leftAliases leftClosure leftAbsorbing context
      start afterValue wellFormed certificate.leftScoped leftFresh
  have rightContextFixed : CumulativeAliasContextFixed
      certificate.rightAliases rightClosure context :=
    cumulativeAliasContextFixed_of_scopedBy_sourceFresh
      certificate.rightAliases rightClosure rightAbsorbing context
      start afterValue wellFormed certificate.rightScoped rightFresh
  let graph := canonicalClosureGraphData certificate leftClosure rightClosure
    leftAbsorbing rightAbsorbing context
  have leftClosed : context.applyFree graph.middle.substitution =
      context.applyFree leftClosure.substitution := by
    rw [graph.middleSubstitution, graph.liftedLeftSubstitution,
      leftContextFixed.closedContext]
  have rightClosed : context.applyFree graph.liftedRight.substitution =
      context.applyFree rightClosure.substitution := by
    rw [graph.liftedRightSubstitution, rightContextFixed.closedContext]
  have leftInterface : context.interfaceEquations graph.middle.substitution =
      context.interfaceEquations leftClosure.substitution := by
    rw [graph.middleSubstitution, graph.liftedLeftSubstitution,
      leftContextFixed.interfaceEquations]
  have rightInterface :
      context.interfaceEquations graph.liftedRight.substitution =
        context.interfaceEquations rightClosure.substitution := by
    rw [graph.liftedRightSubstitution, rightContextFixed.interfaceEquations]
  have leftTarget : graph.middle.target = leftClosure.target := by
    rw [← graph.middleTarget, graph.liftedLeftTarget]
  have rightTarget : graph.liftedRight.target = rightClosure.target :=
    graph.liftedRightTarget
  have graphProvenance : GeneratedSupportProvenance context start afterValue
      (FreshAliasSequence.addAll certificate.rightAliases rightValue) :=
    FilteredGraphScopeFreshness.addAll_supportProvenance_of_scopedBy
      rightProvenance certificate.rightScoped rightFresh
  let data := ClosureSupportConstruction.build graph.transport context
  have leftPresentation :=
    SupportGraph.leftVisiblePresentation graph.transport
      graph.middleAbsorbing graph.liftedRightAbsorbing context
  have rightPresentation :=
    SupportGraph.rightVisiblePresentation graph.transport
      graph.middleAbsorbing context
  rw [leftInterface, rightInterface] at leftPresentation rightPresentation
  let interface : GraphAliasPresentation start afterValue
      (context.interfaceEquations leftClosure.substitution)
      (context.interfaceEquations rightClosure.substitution) :=
    { leftHidden := VisibleSupportGraph.leftHidden data context
      rightHidden := VisibleSupportGraph.rightHidden data context
      leftHiddenFresh := by
        simpa [data] using VisibleSupportGraph.leftHiddenFresh graph.transport
          graph.middleAbsorbing graph.liftedRightAbsorbing graphProvenance
      rightHiddenFresh := by
        simpa [data] using VisibleSupportGraph.rightHiddenFresh graph.transport
          graph.middleAbsorbing graph.liftedRightAbsorbing graphProvenance
      leftAliases := VisibleSupportGraph.leftAliases data context
      rightAliases := VisibleSupportGraph.rightAliases data context
      leftPresentation := by simpa [data] using leftPresentation
      rightPresentation := by simpa [data] using rightPresentation
      leftAliasFresh := leftAlias_mem_hidden data
      rightAliasFresh := rightAlias_mem_hidden data
      leftScoped := by
        simpa [data, leftInterface] using
          VisibleSupportGraph.leftInterfaceScoped graph.transport
            graph.middleAbsorbing graph.liftedRightAbsorbing context
      rightScoped := by
        simpa [data, rightInterface] using
          VisibleSupportGraph.rightInterfaceScoped graph.transport
            graph.middleAbsorbing graph.liftedRightAbsorbing context }
  exact ⟨
    { interface := interface
      leftContextAvoids := by
        simpa [interface, data, leftClosed, leftTarget] using
          VisibleSupportGraph.leftContextAvoids graph.transport
            graph.middleAbsorbing graph.liftedRightAbsorbing context
      rightContextAvoids := by
        simpa [interface, data, rightClosed, rightTarget] using
          VisibleSupportGraph.rightContextAvoids graph.transport
            graph.middleAbsorbing graph.liftedRightAbsorbing context }⟩

private theorem generatedAvoids_previousHidden
    {context : Context} {graphStart boundary finish : Supply}
    {generated : Generated} {hidden : List UnificationVar}
    (provenance : GeneratedSupportProvenance context boundary finish generated)
    (hiddenFresh : VariablesFreshIn graphStart boundary hidden)
    (contextAvoids : VariablesAvoid hidden context.unificationVars) :
    GeneratedAvoids hidden generated := by
  intro candidate generatedMember hiddenMember
  rcases provenance candidate generatedMember with contextMember | bodyFresh
  · exact contextAvoids candidate contextMember hiddenMember
  · have graphFresh := hiddenFresh candidate hiddenMember
    cases candidate <;>
      simp only [UnificationVar.FreshIn] at graphFresh bodyFresh <;> omega

private theorem interfaceEquations_avoid_laterHidden
    {context : Context} {start afterValue finish : Supply}
    {generatedValue : Generated}
    (provenance : GeneratedSupportProvenance context start afterValue
      generatedValue)
    (increases : start.Le afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (wellFormed : start.WellFormedFor context)
    {hidden : List UnificationVar}
    (hiddenFresh : VariablesFreshIn afterValue finish hidden) :
    EquationsAvoid hidden
      (context.interfaceEquations closure.substitution) := by
  intro candidate interfaceMember hiddenMember
  have interfaceBelow := Context.interfaceEquations_support_below
    (closure.localized_of_absorbing absorbing) provenance wellFormed increases
    candidate interfaceMember
  have hiddenRange := hiddenFresh candidate hiddenMember
  cases candidate with
  | ty _ => exact (Nat.not_le_of_gt interfaceBelow) hiddenRange.1
  | cap _ => exact (Nat.not_le_of_gt interfaceBelow) hiddenRange.1

/-- Support-local form of the M2 body-renaming semantic lemma. -/
private theorem entailedRenamingFixedOn_of_support
    {outerContext bodyContext : Context} {afterValue bodyFinish : Supply}
    {leftValue rightValue leftBody : Generated}
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (alignment : FreshClosureAlignment leftClosure rightClosure
      outerContext afterValue)
    (bodyContextEq : bodyContext =
      ((outerContext.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        outerContext.applyFree leftClosure.substitution))
    (bodyProvenance : GeneratedSupportProvenance bodyContext afterValue
      bodyFinish leftBody) :
    EntailedRenamingFixedOn
      (closureInterfaceReference outerContext leftClosure rightClosure)
      alignment.alignment.rho leftBody.unificationVars := by
  subst bodyContext
  intro substitution solved
  have solvedParts := solves_append substitution
    (outerContext.interfaceEquations leftClosure.substitution)
    (outerContext.interfaceEquations rightClosure.substitution) |>.mp solved
  have closedAgree :=
    Context.substitutionsAgree_compose_renaming_of_interfaces
      outerContext leftClosure.substitution rightClosure.substitution
      substitution alignment.alignment.rho solvedParts.1 solvedParts.2
      alignment.alignment.closedContext_exact
  constructor
  · intro index member
    rcases bodyProvenance (.ty index) member with contextMember | fresh
    · have closedMember := Context.generalized_cons_support_subset
          (outerContext.applyFree leftClosure.substitution)
          leftClosure.target (.ty index) contextMember
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
        at closedMember
      rcases closedMember with tyMember | capMember
      · obtain ⟨source, sourceMember, equality⟩ := tyMember
        cases equality
        have agreed := closedAgree.1 index sourceMember
        simpa [Subst.compose, VariableRenaming.substitution, Ty.apply] using
          agreed.symm
      · obtain ⟨source, _, impossible⟩ := capMember
        cases impossible
    · have fixed := alignment.fixesAtOrAbove.1 index fresh.1
      simp [fixed]
  · intro index member
    rcases bodyProvenance (.cap index) member with contextMember | fresh
    · have closedMember := Context.generalized_cons_support_subset
          (outerContext.applyFree leftClosure.substitution)
          leftClosure.target (.cap index) contextMember
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
        at closedMember
      rcases closedMember with tyMember | capMember
      · obtain ⟨source, _, impossible⟩ := tyMember
        cases impossible
      · obtain ⟨source, sourceMember, equality⟩ := capMember
        cases equality
        have agreed := closedAgree.2 index sourceMember
        simpa [Subst.compose, VariableRenaming.substitution, Cap.apply] using
          agreed.symm
    · have fixed := alignment.fixesAtOrAbove.2 index fresh.1
      simp [fixed]

/-- Transport the left M4 body derivation across a coherent pair of value
closures and immediately compare it with the right body derivation.  This is
the representative-changing part of `letE`; the remaining outer-block work
is independent of source syntax. -/
theorem FullM4FuelPairProperty.transportLetBody
    {value body : Expr}
    (bodyCoherent : FullM4FuelPairProperty body)
    {signature : FrozenSignature} {context : Context}
    {start afterValue : Supply}
    {leftValue rightValue leftBody rightBody : Generated}
    {leftNext rightNext : Supply}
    {leftValueFuel rightValueFuel leftBodyFuel rightBodyFuel : Nat}
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : start.WellFormedFor context)
    (leftValueElaboration : ElaboratesFuel signature leftValueFuel context
      value start leftValue afterValue)
    (rightValueElaboration : ElaboratesFuel signature rightValueFuel context
      value start rightValue afterValue)
    (valueCoherence : FullM2PairCoherence start afterValue afterValue
      leftValue rightValue context)
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (leftAbsorbing : leftClosure.Absorbing)
    (rightAbsorbing : rightClosure.Absorbing)
    (leftBodyElaboration : ElaboratesFuel signature leftBodyFuel
      ((context.applyFree leftClosure.substitution).generalize
          leftClosure.target :: context.applyFree leftClosure.substitution)
      body
      (afterValue.join
        (context.applyFree leftClosure.substitution).initialSupply)
      leftBody leftNext)
    (rightBodyElaboration : ElaboratesFuel signature rightBodyFuel
      ((context.applyFree rightClosure.substitution).generalize
          rightClosure.target :: context.applyFree rightClosure.substitution)
      body
      (afterValue.join
        (context.applyFree rightClosure.substitution).initialSupply)
      rightBody rightNext) :
    ∃ alignment : ProvenancedFreshClosureAlignment leftClosure rightClosure
        context afterValue,
      ElaboratesFuel signature leftBodyFuel
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target :: context.applyFree rightClosure.substitution)
        body afterValue
        (ElaborationRenaming.renameGenerated
          alignment.alignment.alignment.rho leftBody) leftNext ∧
      Nonempty (FullM2PairCoherence afterValue leftNext rightNext
        (ElaborationRenaming.renameGenerated
          alignment.alignment.alignment.rho leftBody)
        rightBody
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)) := by
  have leftValueProvenance :=
    leftValueElaboration.supportProvenance signatureWellFormed
  have rightValueProvenance :=
    rightValueElaboration.supportProvenance signatureWellFormed
  have leftBodyStart := PrincipalBlockClosure.letBodySupply_eq leftClosure
    leftAbsorbing leftValueProvenance wellFormed
    leftValueElaboration.supply_le_next
  have rightBodyStart := PrincipalBlockClosure.letBodySupply_eq rightClosure
    rightAbsorbing rightValueProvenance wellFormed
    rightValueElaboration.supply_le_next
  have leftBodyAtBoundary := leftBodyElaboration
  rw [leftBodyStart] at leftBodyAtBoundary
  have rightBodyAtBoundary := rightBodyElaboration
  rw [rightBodyStart] at rightBodyAtBoundary
  have leftClosedWellFormed : afterValue.WellFormedFor
      (context.applyFree leftClosure.substitution) :=
    PrincipalBlockClosure.closedContext_initialSupply_le leftClosure
      leftAbsorbing leftValueProvenance wellFormed
      leftValueElaboration.supply_le_next
  have leftBodyWellFormed : afterValue.WellFormedFor
      ((context.applyFree leftClosure.substitution).generalize
          leftClosure.target :: context.applyFree leftClosure.substitution) :=
    leftClosedWellFormed.generalized_cons leftClosure.target
  have rightClosedWellFormed : afterValue.WellFormedFor
      (context.applyFree rightClosure.substitution) :=
    PrincipalBlockClosure.closedContext_initialSupply_le rightClosure
      rightAbsorbing rightValueProvenance wellFormed
      rightValueElaboration.supply_le_next
  have rightBodyWellFormed : afterValue.WellFormedFor
      ((context.applyFree rightClosure.substitution).generalize
          rightClosure.target :: context.applyFree rightClosure.substitution) :=
    rightClosedWellFormed.generalized_cons rightClosure.target
  obtain ⟨alignment⟩ := valueCoherence.closureAlignment leftClosure
    rightClosure leftAbsorbing rightAbsorbing
  have transported := M4FreshRenaming.m4FreshRenamingTransport
    signatureWellFormed leftBodyAtBoundary leftBodyWellFormed
    alignment.alignment.fixesAtOrAbove
  have bodyContextExact :
      ElaborationRenaming.renameContext alignment.alignment.alignment.rho
          ((context.applyFree leftClosure.substitution).generalize
              leftClosure.target ::
            context.applyFree leftClosure.substitution) =
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution) := by
    change
      (((context.applyFree leftClosure.substitution).generalize
          leftClosure.target :: context.applyFree leftClosure.substitution).map
        (Scheme.applyFree
          alignment.alignment.alignment.rho.substitution)) = _
    exact alignment.alignment.bodyContext_exact
  rw [bodyContextExact] at transported
  exact ⟨alignment, transported,
    bodyCoherent signatureWellFormed rightBodyWellFormed transported
      rightBodyAtBoundary⟩

private theorem supportedLet
    {value body : Expr}
    (valueProperty : FullM4FuelPairProperty value)
    (bodyProperty : FullM4FuelPairProperty body) :
    SupportedM4FuelPairProperty (.letE value body) := by
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
          obtain ⟨leftValue, leftAfterValue, leftValueElaboration,
            leftClosure, leftBody, leftAbsorbing, leftBodyElaboration, rfl⟩ :=
            leftElaboration
          obtain ⟨rightValue, rightAfterValue, rightValueElaboration,
            rightClosure, rightBody, rightAbsorbing, rightBodyElaboration, rfl⟩ :=
            rightElaboration
          obtain ⟨valueCoherence⟩ := valueProperty signatureWellFormed
            wellFormed leftValueElaboration rightValueElaboration
          cases valueCoherence.next_eq
          have leftValueProvenance :=
            leftValueElaboration.supportProvenance signatureWellFormed
          have rightValueProvenance :=
            rightValueElaboration.supportProvenance signatureWellFormed
          have leftBodyStart := PrincipalBlockClosure.letBodySupply_eq
            leftClosure leftAbsorbing leftValueProvenance wellFormed
            leftValueElaboration.supply_le_next
          have rightBodyStart := PrincipalBlockClosure.letBodySupply_eq
            rightClosure rightAbsorbing rightValueProvenance wellFormed
            rightValueElaboration.supply_le_next
          have leftBodyAtBoundary := leftBodyElaboration
          rw [leftBodyStart] at leftBodyAtBoundary
          have rightBodyAtBoundary := rightBodyElaboration
          rw [rightBodyStart] at rightBodyAtBoundary
          obtain ⟨alignment, transported, ⟨bodyCoherence⟩⟩ :=
            bodyProperty.transportLetBody signatureWellFormed wellFormed
              leftValueElaboration rightValueElaboration valueCoherence
              leftClosure rightClosure leftAbsorbing rightAbsorbing
              leftBodyElaboration rightBodyElaboration
          cases bodyCoherence.next_eq
          obtain ⟨graph⟩ := letGraphAliasPresentation_of_support
            wellFormed rightValueProvenance valueCoherence.certificate
            leftClosure rightClosure leftAbsorbing rightAbsorbing
          let bodyCertificate := bodyCoherence.certificate
          let rho := alignment.alignment.alignment.rho
          have leftBodyProvenance :=
            leftBodyAtBoundary.supportProvenance signatureWellFormed
          have rightBodyProvenance :=
            rightBodyAtBoundary.supportProvenance signatureWellFormed
          have leftGraphAvoids :
              GeneratedAvoids graph.interface.leftHidden leftBody :=
            generatedAvoids_previousHidden leftBodyProvenance
              graph.interface.leftHiddenFresh graph.leftContextAvoids
          have rightGraphAvoids :
              GeneratedAvoids graph.interface.rightHidden rightBody :=
            generatedAvoids_previousHidden rightBodyProvenance
              graph.interface.rightHiddenFresh graph.rightContextAvoids
          have leftEffectsAvoidBodyHidden :
              EquationsAvoid bodyCertificate.hidden
                (context.interfaceEquations leftClosure.substitution) :=
            interfaceEquations_avoid_laterHidden leftValueProvenance
              leftValueElaboration.supply_le_next leftClosure leftAbsorbing
              wellFormed bodyCertificate.hiddenFresh
          have rightEffectsAvoidBodyHidden :
              EquationsAvoid bodyCertificate.hidden
                (context.interfaceEquations rightClosure.substitution) :=
            interfaceEquations_avoid_laterHidden rightValueProvenance
              rightValueElaboration.supply_le_next rightClosure rightAbsorbing
              wellFormed bodyCertificate.hiddenFresh
          have baseFixed := entailedRenamingFixedOn_of_support
            leftClosure rightClosure alignment.toFreshClosureAlignment rfl
            leftBodyProvenance
          have pulledAliasFresh :=
            AliasRenamingTransport.pulledAliasFresh_hidden_of_certificate
              bodyCertificate alignment.alignment.fixesAtOrAbove
          have leftScoped := graph.interface.leftCombinedScoped leftBody
            leftGraphAvoids
            (AliasRenamingTransport.scopedBy_pullback rho
              bodyCertificate.leftScoped)
            pulledAliasFresh bodyCertificate.hiddenFresh
            leftEffectsAvoidBodyHidden
          have rightScoped := graph.interface.rightCombinedScoped rightBody
            rightGraphAvoids bodyCertificate.rightScoped
            bodyCertificate.rightAliasFresh bodyCertificate.hiddenFresh
            rightEffectsAvoidBodyHidden
          have startToAfterValue := leftValueElaboration.supply_le_next
          have afterValueToFinish := leftBodyAtBoundary.supply_le_next
          have leftGraphFreshToFinish :=
            graph.interface.leftHiddenFresh.widen (Supply.le_refl start)
              afterValueToFinish
          have rightGraphFreshToFinish :=
            graph.interface.rightHiddenFresh.widen (Supply.le_refl start)
              afterValueToFinish
          let certificate :=
            supportedWholeLetEntailedCompositionWithPulledLeftAliases_of_baseFixed
              (graph.interface.leftHidden ++ graph.interface.rightHidden)
              (leftGraphFreshToFinish.append rightGraphFreshToFinish)
              startToAfterValue graph.interface.leftAliases
              graph.interface.rightAliases graph.interface.leftPresentation
              graph.interface.rightPresentation bodyCertificate baseFixed
              alignment.alignment.fixesAtOrAbove
              (fun alias member => List.mem_append_left _
                (graph.interface.leftAliasFresh alias member))
              (fun alias member => List.mem_append_right _
                (graph.interface.rightAliasFresh alias member))
              leftScoped rightScoped
          exact ⟨{ next_eq := rfl, certificate := certificate }⟩

/-- Concrete M4 `letE` transport and whole-block assembly. -/
theorem m4LetTransportAndAssembly : M4LetTransportAndAssembly := by
  intro value body valueProperty bodyProperty
  exact SupportedM4FuelPairProperty.toFull
    (supportedLet valueProperty bodyProperty)

end TypePM.Source.M4.CompletenessArchitecture
