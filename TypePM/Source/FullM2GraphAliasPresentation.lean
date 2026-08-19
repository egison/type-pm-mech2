import TypePM.Source.GraphAliasPresentationConstruction
import TypePM.Source.VisibleGraphSemanticPresentations
import TypePM.Source.VisibleSupportGraphFreshness

/-!
# Complete M2 graph-alias presentation

This module connects the canonical same-generated closure graph back to the
two original value closures used at a source `let` boundary.
-/

namespace TypePM.Source

open FreshAliasSequence
open InterfaceAliasDecomposition
open InterfaceAliasDecomposition.AliasFreshness

private theorem equation_support_mem
    {candidate : UnificationVar} {equation : Equation}
    {equations : List Equation} (equationMember : equation ∈ equations)
    (candidateMember : candidate ∈ equation.unificationVars) :
    candidate ∈ TypePM.unificationVars equations := by
  induction equations with
  | nil => simp at equationMember
  | cons head tail induction =>
      simp only [List.mem_cons] at equationMember
      simp only [TypePM.unificationVars, List.mem_append]
      rcases equationMember with rfl | tailMember
      · exact Or.inl candidateMember
      · exact Or.inr (induction tailMember)

private theorem closedTy_mem_interface
    (context : Context) (block : Subst) {index : TyVar}
    (member : index ∈ (context.applyFree block).freeTyVars) :
    UnificationVar.ty index ∈
      TypePM.unificationVars (context.interfaceEquations block) := by
  obtain ⟨input, inputMember, imageMember⟩ :=
    context.freeTy_applyFree_origin block member
  apply equation_support_mem
    (equation := .ty (.var input) (block.ty input))
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨input, inputMember, rfl⟩
  · simp only [Equation.unificationVars, Ty.unificationVars, List.mem_append]
    exact Or.inr imageMember

private theorem closedCap_mem_interface
    (context : Context) (block : Subst) {index : CapVar}
    (member : index ∈ (context.applyFree block).freeCapVars) :
    UnificationVar.cap index ∈
      TypePM.unificationVars (context.interfaceEquations block) := by
  rcases context.freeCap_applyFree_origin block member with
    ⟨input, inputMember, imageMember⟩ | ⟨input, inputMember, imageMember⟩
  · apply equation_support_mem
      (equation := .ty (.var input) (block.ty input))
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨input, inputMember, rfl⟩
    · simpa [Equation.unificationVars, Ty.unificationVars] using imageMember
  · apply equation_support_mem
      (equation := .cap (.var input) (block.cap input))
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨input, inputMember, rfl⟩
    · simp only [Equation.unificationVars, Cap.unificationVars,
        List.mem_append]
      exact Or.inr imageMember

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

theorem fullM2LetGraphAliasPresentationComplete :
    FullM2LetGraphAliasPresentationComplete := by
  intro signature context value start afterValue leftValue rightValue
    wellFormed leftElaboration rightElaboration certificate
    leftClosure rightClosure leftAbsorbing rightAbsorbing
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
      rightElaboration.supportProvenance certificate.rightScoped rightFresh
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

end TypePM.Source
