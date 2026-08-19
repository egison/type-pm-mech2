import TypePM.Source.FilteredGraphScopeFreshness
import TypePM.Source.GraphAliasPresentationConstruction

/-!
# Scope and freshness of the context-visible closure graph

The representative graph used at a `let` boundary contains only moved
support edges whose existing endpoint occurs in the corresponding closed
context.  This file packages the support facts needed by the semantic graph
presentation while keeping the two sides' fresh endpoints separate.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition
open InterfaceAliasDecomposition.AliasFreshness

namespace VisibleSupportGraph

private theorem nodup_map_of_injectiveOn
    {alpha beta : Type} (function : alpha → beta) (items : List alpha)
    (itemsNodup : items.Nodup)
    (injectiveOn : ∀ {left right}, left ∈ items → right ∈ items →
      function left = function right → left = right) :
    (items.map function).Nodup := by
  induction items with
  | nil => exact .nil
  | cons head tail induction =>
      have split := List.nodup_cons.mp itemsNodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨other, otherMember, equality⟩ := List.mem_map.mp member
        have same := injectiveOn (by simp)
          (List.mem_cons_of_mem _ otherMember) equality.symm
        exact split.1 (same ▸ otherMember)
      · exact induction split.2 (by
          intro left right leftMember rightMember equality
          exact injectiveOn (List.mem_cons_of_mem _ leftMember)
            (List.mem_cons_of_mem _ rightMember) equality)

theorem leftTySource_facts
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    {source : TyVar} (member : source ∈ leftTySources data context) :
    source ∈ data.support.ty.source ∧
      source ∈ (context.applyFree left.substitution).freeTyVars ∧
      data.support.ty.forward source ≠ source ∧
      data.support.ty.forward source ∉ context.freeTyVars := by
  simpa [leftTySources] using member

theorem rightTySource_facts
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    {source : TyVar} (member : source ∈ rightTySources data context) :
    source ∈ data.support.ty.source ∧
      source ∈ (context.applyFree left.substitution).freeTyVars ∧
      data.support.ty.forward source ≠ source ∧
      source ∉ context.freeTyVars := by
  simpa [rightTySources] using member

theorem leftCapSource_facts
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    {source : CapVar} (member : source ∈ leftCapSources data context) :
    source ∈ data.support.cap.source ∧
      source ∈ (context.applyFree left.substitution).freeCapVars ∧
      data.support.cap.forward source ≠ source ∧
      data.support.cap.forward source ∉ context.freeCapVars := by
  simpa [leftCapSources] using member

theorem rightCapSource_facts
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    {source : CapVar} (member : source ∈ rightCapSources data context) :
    source ∈ data.support.cap.source ∧
      source ∈ (context.applyFree left.substitution).freeCapVars ∧
      data.support.cap.forward source ≠ source ∧
      source ∉ context.freeCapVars := by
  simpa [rightCapSources] using member

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

private theorem rightTy_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    {index : TyVar}
    (member : index ∈ (context.applyFree right.substitution).freeTyVars) :
    index ∈ data.support.ty.target := by
  have renamedMember : index ∈
      ((context.applyFree left.substitution).applyFree
        data.globalRenaming.substitution).freeTyVars := by
    rw [data.closedContext_exact]
    exact member
  rw [Context.freeTyVars_apply_variableRenaming] at renamedMember
  obtain ⟨source, sourceMember, imageEquality⟩ :=
    List.mem_map.mp renamedMember
  have sourceSupport := data.leftTy sourceMember
  have targetSupport := data.support.ty.forward_mem sourceSupport
  have agrees : data.globalRenaming.tyForward source =
      data.support.ty.forward source := by
    simpa [ClosureSupportBijection.globalRenaming] using
      data.support.tyForward_agrees sourceSupport
  have equality : data.support.ty.forward source = index :=
    agrees.symm.trans imageEquality
  exact equality ▸ targetSupport

private theorem rightCap_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    {index : CapVar}
    (member : index ∈ (context.applyFree right.substitution).freeCapVars) :
    index ∈ data.support.cap.target := by
  have renamedMember : index ∈
      ((context.applyFree left.substitution).applyFree
        data.globalRenaming.substitution).freeCapVars := by
    rw [data.closedContext_exact]
    exact member
  rw [Context.freeCapVars_apply_variableRenaming] at renamedMember
  obtain ⟨source, sourceMember, imageEquality⟩ :=
    List.mem_map.mp renamedMember
  have sourceSupport := data.leftCap sourceMember
  have targetSupport := data.support.cap.forward_mem sourceSupport
  have agrees : data.globalRenaming.capForward source =
      data.support.cap.forward source := by
    simpa [ClosureSupportBijection.globalRenaming] using
      data.support.capForward_agrees sourceSupport
  have equality : data.support.cap.forward source = index :=
    agrees.symm.trans imageEquality
  exact equality ▸ targetSupport

private theorem leftBodySupport_subset
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    ∀ candidate, candidate ∈ Context.unificationVars
        ((context.applyFree left.substitution).generalize left.target ::
          context.applyFree left.substitution) →
      candidate ∈ SupportGraph.SourceVariables data := by
  intro candidate member
  have closedMember := Context.generalized_cons_support_subset
    (context.applyFree left.substitution) left.target candidate member
  simp only [Context.unificationVars, List.mem_append, List.mem_map] at closedMember
  rcases closedMember with ⟨index, indexMember, rfl⟩ |
      ⟨index, indexMember, rfl⟩
  · exact List.mem_append_left _
      (List.mem_map.mpr ⟨index, data.leftTy indexMember, rfl⟩)
  · exact List.mem_append_right _
      (List.mem_map.mpr ⟨index, data.leftCap indexMember, rfl⟩)

private theorem rightBodySupport_subset
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    ∀ candidate, candidate ∈ Context.unificationVars
        ((context.applyFree right.substitution).generalize right.target ::
          context.applyFree right.substitution) →
      candidate ∈ BuiltSupport.TargetVariables data := by
  intro candidate member
  have closedMember := Context.generalized_cons_support_subset
    (context.applyFree right.substitution) right.target candidate member
  simp only [Context.unificationVars, List.mem_append, List.mem_map] at closedMember
  rcases closedMember with ⟨index, indexMember, rfl⟩ |
      ⟨index, indexMember, rfl⟩
  · exact (BuiltSupport.ty_mem_targetVariables data index).mpr
      (rightTy_covered data indexMember)
  · exact (BuiltSupport.cap_mem_targetVariables data index).mpr
      (rightCap_covered data indexMember)

private theorem rightTyImageTy_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input : TyVar) (inputMember : input ∈ context.freeTyVars)
    {candidate : TyVar}
    (member : candidate ∈ (right.substitution.ty input).tyVars) :
    candidate ∈ (ClosureSupportConstruction.build transport context).support.ty.target := by
  let data := ClosureSupportConstruction.build transport context
  have exact := BuiltSupport.build_tyRhs_exact transport context input inputMember
  rw [← exact, Ty.tyVars_apply_variableRenaming] at member
  obtain ⟨source, sourceMember, imageEquality⟩ := List.mem_map.mp member
  have sourceSupport := BuiltSupport.build_tyImage_ty_covered
    transport context input inputMember sourceMember
  have targetSupport := data.support.ty.forward_mem sourceSupport
  have agrees : data.globalRenaming.tyForward source =
      data.support.ty.forward source := data.support.tyForward_agrees sourceSupport
  have equality : data.support.ty.forward source = candidate :=
    agrees.symm.trans imageEquality
  exact equality ▸ targetSupport

private theorem rightTyImageCap_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input : TyVar) (inputMember : input ∈ context.freeTyVars)
    {candidate : CapVar}
    (member : candidate ∈ (right.substitution.ty input).capVars) :
    candidate ∈ (ClosureSupportConstruction.build transport context).support.cap.target := by
  let data := ClosureSupportConstruction.build transport context
  have exact := BuiltSupport.build_tyRhs_exact transport context input inputMember
  rw [← exact, Ty.capVars_apply_variableRenaming] at member
  obtain ⟨source, sourceMember, imageEquality⟩ := List.mem_map.mp member
  have sourceSupport := BuiltSupport.build_tyImage_cap_covered
    transport context input inputMember sourceMember
  have targetSupport := data.support.cap.forward_mem sourceSupport
  have agrees : data.globalRenaming.capForward source =
      data.support.cap.forward source := data.support.capForward_agrees sourceSupport
  have equality : data.support.cap.forward source = candidate :=
    agrees.symm.trans imageEquality
  exact equality ▸ targetSupport

private theorem rightCapImageCap_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (input : CapVar) (inputMember : input ∈ context.freeCapVars)
    {candidate : CapVar}
    (member : candidate ∈ (right.substitution.cap input).capVars) :
    candidate ∈ (ClosureSupportConstruction.build transport context).support.cap.target := by
  let data := ClosureSupportConstruction.build transport context
  have exact := BuiltSupport.build_capRhs_exact transport context input inputMember
  rw [← exact, Cap.capVars_apply_variableRenaming] at member
  obtain ⟨source, sourceMember, imageEquality⟩ := List.mem_map.mp member
  have sourceSupport := BuiltSupport.build_capImage_cap_covered
    transport context input inputMember sourceMember
  have targetSupport := data.support.cap.forward_mem sourceSupport
  have agrees : data.globalRenaming.capForward source =
      data.support.cap.forward source := data.support.capForward_agrees sourceSupport
  have equality : data.support.cap.forward source = candidate :=
    agrees.symm.trans imageEquality
  exact equality ▸ targetSupport

private theorem leftTyInterface_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {candidate : TyVar}
    (member : .ty candidate ∈
      TypePM.unificationVars (context.interfaceEquations left.substitution))
    (notOuter : candidate ∉ context.freeTyVars) :
    .ty candidate ∈ SupportGraph.SourceVariables
      (ClosureSupportConstruction.build transport context) := by
  let data := ClosureSupportConstruction.build transport context
  rcases Context.interfaceEquations_support_origin context left.substitution member with
    original | tyImage | capImage
  · exact False.elim (notOuter (by
      simpa [Context.unificationVars] using original))
  · obtain ⟨input, inputMember, imageMember⟩ := tyImage
    have typed : candidate ∈ (left.substitution.ty input).tyVars :=
      (Ty.mem_tyVars_iff_unificationVars candidate _).mpr imageMember
    exact List.mem_append_left _ (List.mem_map.mpr
      ⟨candidate, BuiltSupport.build_tyImage_ty_covered
        transport context input inputMember typed, rfl⟩)
  · obtain ⟨input, inputMember, imageMember⟩ := capImage
    simp at imageMember

private theorem leftCapInterface_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {candidate : CapVar}
    (member : .cap candidate ∈
      TypePM.unificationVars (context.interfaceEquations left.substitution))
    (notOuter : candidate ∉ context.freeCapVars) :
    .cap candidate ∈ SupportGraph.SourceVariables
      (ClosureSupportConstruction.build transport context) := by
  rcases Context.interfaceEquations_support_origin context left.substitution member with
    original | tyImage | capImage
  · exact False.elim (notOuter (by
      simpa [Context.unificationVars] using original))
  · obtain ⟨input, inputMember, imageMember⟩ := tyImage
    have typed : candidate ∈ (left.substitution.ty input).capVars :=
      (Ty.mem_capVars_iff_unificationVars candidate _).mpr imageMember
    exact List.mem_append_right _ (List.mem_map.mpr
      ⟨candidate, BuiltSupport.build_tyImage_cap_covered
        transport context input inputMember typed, rfl⟩)
  · obtain ⟨input, inputMember, imageMember⟩ := capImage
    have typed : candidate ∈ (left.substitution.cap input).capVars :=
      (Cap.mem_capVars_iff_unificationVars candidate _).mpr imageMember
    exact List.mem_append_right _ (List.mem_map.mpr
      ⟨candidate, BuiltSupport.build_capImage_cap_covered
        transport context input inputMember typed, rfl⟩)

private theorem rightTyInterface_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {candidate : TyVar}
    (member : .ty candidate ∈
      TypePM.unificationVars (context.interfaceEquations right.substitution))
    (notOuter : candidate ∉ context.freeTyVars) :
    .ty candidate ∈ BuiltSupport.TargetVariables
      (ClosureSupportConstruction.build transport context) := by
  let data := ClosureSupportConstruction.build transport context
  rcases Context.interfaceEquations_support_origin context right.substitution member with
    original | tyImage | capImage
  · exact False.elim (notOuter (by
      simpa [Context.unificationVars] using original))
  · obtain ⟨input, inputMember, imageMember⟩ := tyImage
    have typed : candidate ∈ (right.substitution.ty input).tyVars :=
      (Ty.mem_tyVars_iff_unificationVars candidate _).mpr imageMember
    exact (BuiltSupport.ty_mem_targetVariables data candidate).mpr
      (rightTyImageTy_covered transport context input inputMember typed)
  · obtain ⟨input, inputMember, imageMember⟩ := capImage
    simp at imageMember

private theorem rightCapInterface_covered
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {candidate : CapVar}
    (member : .cap candidate ∈
      TypePM.unificationVars (context.interfaceEquations right.substitution))
    (notOuter : candidate ∉ context.freeCapVars) :
    .cap candidate ∈ BuiltSupport.TargetVariables
      (ClosureSupportConstruction.build transport context) := by
  let data := ClosureSupportConstruction.build transport context
  rcases Context.interfaceEquations_support_origin context right.substitution member with
    original | tyImage | capImage
  · exact False.elim (notOuter (by
      simpa [Context.unificationVars] using original))
  · obtain ⟨input, inputMember, imageMember⟩ := tyImage
    have typed : candidate ∈ (right.substitution.ty input).capVars :=
      (Ty.mem_capVars_iff_unificationVars candidate _).mpr imageMember
    exact (BuiltSupport.cap_mem_targetVariables data candidate).mpr
      (rightTyImageCap_covered transport context input inputMember typed)
  · obtain ⟨input, inputMember, imageMember⟩ := capImage
    have typed : candidate ∈ (right.substitution.cap input).capVars :=
      (Cap.mem_capVars_iff_unificationVars candidate _).mpr imageMember
    exact (BuiltSupport.cap_mem_targetVariables data candidate).mpr
      (rightCapImageCap_covered transport context input inputMember typed)

private theorem leftTyScoped
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (SupportGraph.SourceVariables data)
      ((leftTySources data context).map (fun source =>
        FreshAliasSequence.Alias.ty (data.support.ty.forward source) source)) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (SupportGraph.SourceVariables data)
    ((leftTySources data context).map (fun source =>
      FreshAliasSequence.Alias.ty (data.support.ty.forward source) source))
  constructor
  · rw [List.map_map]
    change ((leftTySources data context).map (fun source =>
      UnificationVar.ty (data.support.ty.forward source))).Nodup
    apply nodup_map_of_injectiveOn _ _
      (data.support.ty.source_nodup.filter _)
    intro first second firstMember secondMember equality
    injection equality with imageEquality
    have firstFacts := leftTySource_facts data firstMember
    have secondFacts := leftTySource_facts data secondMember
    have restored := congrArg data.support.ty.backward imageEquality
    simpa only [data.support.ty.backward_forward firstFacts.1,
      data.support.ty.backward_forward secondFacts.1] using restored
  · intro alias aliasMember
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp aliasMember
    have facts := leftTySource_facts data sourceMember
    constructor
    · change UnificationVar.ty (data.support.ty.forward source) ∉
        SupportGraph.SourceVariables data
      intro combinedMember
      rcases List.mem_append.mp combinedMember with tyMember | capMember
      · obtain ⟨candidate, candidateMember, equality⟩ :=
          List.mem_map.mp tyMember
        have same := UnificationVar.ty.inj equality
        exact SupportGraph.movedTyTarget_not_source transport
          leftAbsorbing rightAbsorbing context facts.1 facts.2.2.1
          (same ▸ candidateMember)
      · obtain ⟨_, _, equality⟩ := List.mem_map.mp capMember
        cases equality
    · exact List.mem_append_left _
        (List.mem_map.mpr ⟨source, facts.1, rfl⟩)

private theorem leftCapScoped
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (SupportGraph.SourceVariables data)
      ((leftCapSources data context).map (fun source =>
        FreshAliasSequence.Alias.cap (data.support.cap.forward source) source)) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (SupportGraph.SourceVariables data)
    ((leftCapSources data context).map (fun source =>
      FreshAliasSequence.Alias.cap (data.support.cap.forward source) source))
  constructor
  · rw [List.map_map]
    change ((leftCapSources data context).map (fun source =>
      UnificationVar.cap (data.support.cap.forward source))).Nodup
    apply nodup_map_of_injectiveOn _ _
      (data.support.cap.source_nodup.filter _)
    intro first second firstMember secondMember equality
    injection equality with imageEquality
    have firstFacts := leftCapSource_facts data firstMember
    have secondFacts := leftCapSource_facts data secondMember
    have restored := congrArg data.support.cap.backward imageEquality
    simpa only [data.support.cap.backward_forward firstFacts.1,
      data.support.cap.backward_forward secondFacts.1] using restored
  · intro alias aliasMember
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp aliasMember
    have facts := leftCapSource_facts data sourceMember
    constructor
    · change UnificationVar.cap (data.support.cap.forward source) ∉
        SupportGraph.SourceVariables data
      intro combinedMember
      rcases List.mem_append.mp combinedMember with tyMember | capMember
      · obtain ⟨_, _, equality⟩ := List.mem_map.mp tyMember
        cases equality
      · obtain ⟨candidate, candidateMember, equality⟩ :=
          List.mem_map.mp capMember
        have same := UnificationVar.cap.inj equality
        exact SupportGraph.movedCapTarget_not_source transport
          leftAbsorbing rightAbsorbing context facts.1 facts.2.2.1
          (same ▸ candidateMember)
    · exact List.mem_append_right _
        (List.mem_map.mpr ⟨source, facts.1, rfl⟩)

/-- The left visible graph is scoped by the complete left observable
support. -/
theorem leftScoped
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (SupportGraph.SourceVariables data) (leftAliases data context) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (SupportGraph.SourceVariables data) (leftAliases data context)
  apply ScopedBy.append (leftTyScoped transport leftAbsorbing rightAbsorbing)
    (leftCapScoped transport leftAbsorbing rightAbsorbing)
  intro candidate tyMember capMember
  simp [AliasFreshness.freshVariable] at tyMember capMember
  obtain ⟨_, _, equality⟩ := tyMember
  obtain ⟨_, _, equality'⟩ := capMember
  rw [← equality] at equality'
  cases equality'

private theorem rightTyScoped
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (BuiltSupport.TargetVariables data)
      ((rightTySources data context).map (fun source =>
        FreshAliasSequence.Alias.ty source
          (data.support.ty.forward source))) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (BuiltSupport.TargetVariables data)
    ((rightTySources data context).map (fun source =>
      FreshAliasSequence.Alias.ty source (data.support.ty.forward source)))
  constructor
  · rw [List.map_map]
    change ((rightTySources data context).map UnificationVar.ty).Nodup
    apply nodup_map_of_injectiveOn _ _
      (data.support.ty.source_nodup.filter _)
    intro first second _ _ equality
    exact UnificationVar.ty.inj equality
  · intro alias aliasMember
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp aliasMember
    have facts := rightTySource_facts data sourceMember
    constructor
    · change UnificationVar.ty source ∉ BuiltSupport.TargetVariables data
      simpa only [BuiltSupport.ty_mem_targetVariables] using
        SupportGraph.movedTySource_not_target transport leftAbsorbing
          rightAbsorbing context facts.1 facts.2.2.1
    · exact (BuiltSupport.ty_mem_targetVariables data _).mpr
        (data.support.ty.forward_mem facts.1)

private theorem rightCapScoped
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (BuiltSupport.TargetVariables data)
      ((rightCapSources data context).map (fun source =>
        FreshAliasSequence.Alias.cap source
          (data.support.cap.forward source))) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (BuiltSupport.TargetVariables data)
    ((rightCapSources data context).map (fun source =>
      FreshAliasSequence.Alias.cap source (data.support.cap.forward source)))
  constructor
  · rw [List.map_map]
    change ((rightCapSources data context).map UnificationVar.cap).Nodup
    apply nodup_map_of_injectiveOn _ _
      (data.support.cap.source_nodup.filter _)
    intro first second _ _ equality
    exact UnificationVar.cap.inj equality
  · intro alias aliasMember
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp aliasMember
    have facts := rightCapSource_facts data sourceMember
    constructor
    · change UnificationVar.cap source ∉ BuiltSupport.TargetVariables data
      simpa only [BuiltSupport.cap_mem_targetVariables] using
        SupportGraph.movedCapSource_not_target transport leftAbsorbing
          rightAbsorbing context facts.1 facts.2.2.1
    · exact (BuiltSupport.cap_mem_targetVariables data _).mpr
        (data.support.cap.forward_mem facts.1)

/-- The right visible graph is scoped by the complete right observable
support. -/
theorem rightScoped
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (BuiltSupport.TargetVariables data) (rightAliases data context) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (BuiltSupport.TargetVariables data) (rightAliases data context)
  apply ScopedBy.append (rightTyScoped transport leftAbsorbing rightAbsorbing)
    (rightCapScoped transport leftAbsorbing rightAbsorbing)
  intro candidate tyMember capMember
  simp [AliasFreshness.freshVariable] at tyMember capMember
  obtain ⟨_, _, equality⟩ := tyMember
  obtain ⟨_, _, equality'⟩ := capMember
  rw [← equality] at equality'
  cases equality'

/-- The left visible aliases are admissibly scoped by the concrete left
interface itself. -/
theorem leftInterfaceScoped
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy
      (TypePM.unificationVars (context.interfaceEquations left.substitution))
      (leftAliases data context) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy
    (TypePM.unificationVars (context.interfaceEquations left.substitution))
    (leftAliases data context)
  refine ⟨(leftScoped transport leftAbsorbing rightAbsorbing).1, ?_⟩
  intro alias aliasMember
  have broad :=
    (leftScoped transport leftAbsorbing rightAbsorbing).2 alias aliasMember
  rcases List.mem_append.mp aliasMember with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    have facts := leftTySource_facts data sourceMember
    constructor
    · intro interfaceMember
      exact broad.1 (leftTyInterface_covered transport context interfaceMember
        facts.2.2.2)
    · exact closedTy_mem_interface context left.substitution facts.2.1
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    have facts := leftCapSource_facts data sourceMember
    constructor
    · intro interfaceMember
      exact broad.1 (leftCapInterface_covered transport context interfaceMember
        facts.2.2.2)
    · exact closedCap_mem_interface context left.substitution facts.2.1

/-- The right visible aliases are admissibly scoped by the concrete right
interface itself. -/
theorem rightInterfaceScoped
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy
      (TypePM.unificationVars (context.interfaceEquations right.substitution))
      (rightAliases data context) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy
    (TypePM.unificationVars (context.interfaceEquations right.substitution))
    (rightAliases data context)
  refine ⟨(rightScoped transport leftAbsorbing rightAbsorbing).1, ?_⟩
  intro alias aliasMember
  have broad :=
    (rightScoped transport leftAbsorbing rightAbsorbing).2 alias aliasMember
  rcases List.mem_append.mp aliasMember with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    have facts := rightTySource_facts data sourceMember
    have agrees : data.globalRenaming.tyForward source =
        data.support.ty.forward source := by
      simpa [ClosureSupportBijection.globalRenaming] using
        data.support.tyForward_agrees facts.1
    have targetClosed : data.support.ty.forward source ∈
        (context.applyFree right.substitution).freeTyVars := by
      rw [← data.closedContext_exact,
        Context.freeTyVars_apply_variableRenaming]
      exact List.mem_map.mpr ⟨source, facts.2.1, agrees⟩
    constructor
    · intro interfaceMember
      exact broad.1 (rightTyInterface_covered transport context interfaceMember
        facts.2.2.2)
    · exact closedTy_mem_interface context right.substitution targetClosed
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    have facts := rightCapSource_facts data sourceMember
    have agrees : data.globalRenaming.capForward source =
        data.support.cap.forward source := by
      simpa [ClosureSupportBijection.globalRenaming] using
        data.support.capForward_agrees facts.1
    have targetClosed : data.support.cap.forward source ∈
        (context.applyFree right.substitution).freeCapVars := by
      rw [← data.closedContext_exact,
        Context.freeCapVars_apply_variableRenaming]
      exact List.mem_map.mpr ⟨source, facts.2.1, agrees⟩
    constructor
    · intro interfaceMember
      exact broad.1 (rightCapInterface_covered transport context interfaceMember
        facts.2.2.2)
    · exact closedCap_mem_interface context right.substitution targetClosed

/-- Every fresh endpoint retained on the left was allocated during the
source value interval. -/
theorem leftAliasFresh
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context} {start finish : Supply}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (_leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated) :
    let data := ClosureSupportConstruction.build transport context
    ∀ alias, alias ∈ leftAliases data context →
      (freshVariable alias).FreshIn start finish := by
  let data := ClosureSupportConstruction.build transport context
  change ∀ alias, alias ∈ leftAliases data context →
    (freshVariable alias).FreshIn start finish
  intro alias member
  rcases List.mem_append.mp member with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    have facts := leftTySource_facts data sourceMember
    exact FilteredGraphScopeFreshness.tyTarget_fresh_of_not_outer
      transport rightAbsorbing provenance
      (data.support.ty.forward_mem facts.1) facts.2.2.2
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    have facts := leftCapSource_facts data sourceMember
    exact FilteredGraphScopeFreshness.capTarget_fresh_of_not_outer
      transport rightAbsorbing provenance
      (data.support.cap.forward_mem facts.1) facts.2.2.2

/-- Every fresh endpoint retained on the right was allocated during the
same source value interval. -/
theorem rightAliasFresh
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context} {start finish : Supply}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (_rightAbsorbing : right.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated) :
    let data := ClosureSupportConstruction.build transport context
    ∀ alias, alias ∈ rightAliases data context →
      (freshVariable alias).FreshIn start finish := by
  let data := ClosureSupportConstruction.build transport context
  change ∀ alias, alias ∈ rightAliases data context →
    (freshVariable alias).FreshIn start finish
  intro alias member
  rcases List.mem_append.mp member with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    have facts := rightTySource_facts data sourceMember
    exact FilteredGraphScopeFreshness.tySource_fresh_of_not_outer
      transport leftAbsorbing provenance facts.1 facts.2.2.2
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    have facts := rightCapSource_facts data sourceMember
    exact FilteredGraphScopeFreshness.capSource_fresh_of_not_outer
      transport leftAbsorbing provenance facts.1 facts.2.2.2

/-- Collected left hidden variables inherit the pointwise interval
freshness. -/
theorem leftHiddenFresh
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context} {start finish : Supply}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (_leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated) :
    let data := ClosureSupportConstruction.build transport context
    VariablesFreshIn start finish (leftHidden data context) := by
  let data := ClosureSupportConstruction.build transport context
  change VariablesFreshIn start finish (leftHidden data context)
  intro candidate member
  rcases List.mem_append.mp member with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    have facts := leftTySource_facts data sourceMember
    exact FilteredGraphScopeFreshness.tyTarget_fresh_of_not_outer
      transport rightAbsorbing provenance
      (data.support.ty.forward_mem facts.1) facts.2.2.2
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    have facts := leftCapSource_facts data sourceMember
    exact FilteredGraphScopeFreshness.capTarget_fresh_of_not_outer
      transport rightAbsorbing provenance
      (data.support.cap.forward_mem facts.1) facts.2.2.2

/-- Right hidden-variable interval freshness. -/
theorem rightHiddenFresh
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context} {start finish : Supply}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (_rightAbsorbing : right.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated) :
    let data := ClosureSupportConstruction.build transport context
    VariablesFreshIn start finish (rightHidden data context) := by
  let data := ClosureSupportConstruction.build transport context
  change VariablesFreshIn start finish (rightHidden data context)
  intro candidate member
  rcases List.mem_append.mp member with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    have facts := rightTySource_facts data sourceMember
    exact FilteredGraphScopeFreshness.tySource_fresh_of_not_outer
      transport leftAbsorbing provenance facts.1 facts.2.2.2
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    have facts := rightCapSource_facts data sourceMember
    exact FilteredGraphScopeFreshness.capSource_fresh_of_not_outer
      transport leftAbsorbing provenance facts.1 facts.2.2.2

private theorem leftHidden_alias
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    {candidate : UnificationVar}
    (member : candidate ∈ leftHidden data context) :
    ∃ alias, alias ∈ leftAliases data context ∧
      freshVariable alias = candidate := by
  rcases List.mem_append.mp member with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    exact ⟨.ty (data.support.ty.forward source) source,
      List.mem_append_left _ (List.mem_map.mpr ⟨source, sourceMember, rfl⟩), rfl⟩
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    exact ⟨.cap (data.support.cap.forward source) source,
      List.mem_append_right _ (List.mem_map.mpr ⟨source, sourceMember, rfl⟩), rfl⟩

private theorem rightHidden_alias
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context)
    {candidate : UnificationVar}
    (member : candidate ∈ rightHidden data context) :
    ∃ alias, alias ∈ rightAliases data context ∧
      freshVariable alias = candidate := by
  rcases List.mem_append.mp member with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    exact ⟨.ty source (data.support.ty.forward source),
      List.mem_append_left _ (List.mem_map.mpr ⟨source, sourceMember, rfl⟩), rfl⟩
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    exact ⟨.cap source (data.support.cap.forward source),
      List.mem_append_right _ (List.mem_map.mpr ⟨source, sourceMember, rfl⟩), rfl⟩

/-- The left-side hidden endpoints do not occur in the generalized left
body context. -/
theorem leftContextAvoids
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    VariablesAvoid (leftHidden data context)
      (Context.unificationVars
        ((context.applyFree left.substitution).generalize left.target ::
          context.applyFree left.substitution)) := by
  let data := ClosureSupportConstruction.build transport context
  change VariablesAvoid (leftHidden data context)
    (Context.unificationVars
      ((context.applyFree left.substitution).generalize left.target ::
        context.applyFree left.substitution))
  intro candidate observed hidden
  obtain ⟨alias, aliasMember, equality⟩ := leftHidden_alias data hidden
  have freshOutside :=
    (leftScoped transport leftAbsorbing rightAbsorbing).2 alias aliasMember |>.1
  apply freshOutside
  rw [equality]
  exact leftBodySupport_subset data candidate observed

/-- The right-side hidden endpoints do not occur in the generalized right
body context. -/
theorem rightContextAvoids
    {generated : Generated} {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    VariablesAvoid (rightHidden data context)
      (Context.unificationVars
        ((context.applyFree right.substitution).generalize right.target ::
          context.applyFree right.substitution)) := by
  let data := ClosureSupportConstruction.build transport context
  change VariablesAvoid (rightHidden data context)
    (Context.unificationVars
      ((context.applyFree right.substitution).generalize right.target ::
        context.applyFree right.substitution))
  intro candidate observed hidden
  obtain ⟨alias, aliasMember, equality⟩ := rightHidden_alias data hidden
  have freshOutside :=
    (rightScoped transport leftAbsorbing rightAbsorbing).2 alias aliasMember |>.1
  apply freshOutside
  rw [equality]
  exact rightBodySupport_subset data candidate observed

end VisibleSupportGraph

end TypePM.Source
