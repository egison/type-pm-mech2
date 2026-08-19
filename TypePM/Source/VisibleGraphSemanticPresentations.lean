import TypePM.Source.FilteredGraphSemanticHelpers
import TypePM.Source.GraphAliasPresentationConstruction
import TypePM.Source.ContextApplyFreeReflection

/-!
# Semantic presentations from the visible closure-support graph

The visible graph contains exactly the moved edges occurring in the closed
left context.  An edge is emitted on one side only when its prospective
fresh endpoint is not already an outer-context variable; otherwise the
corresponding interface equation entails that edge.
-/

namespace TypePM.Source.InterfaceAliasDecomposition.SupportGraph

open EquationLists

private theorem closedContextTy_source
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {index : TyVar}
    (member : index ∈ (context.applyFree left.substitution).freeTyVars) :
    index ∈ (ClosureSupportConstruction.build transport context).support.ty.source := by
  change index ∈ dedupFirst
    (ObservableSupport.closureWitness
      (context.applyFree left.substitution) left.target).tyVars
  apply mem_dedupFirst.mpr
  simp only [ObservableSupport.closureWitness, Ty.tyVars, Ty.tyVarsList,
    List.mem_append]
  exact Or.inl (ObservableSupport.contextWitness_ty _ member)

private theorem closedContextCap_source
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {index : CapVar}
    (member : index ∈ (context.applyFree left.substitution).freeCapVars) :
    index ∈ (ClosureSupportConstruction.build transport context).support.cap.source := by
  change index ∈ dedupFirst
    (ObservableSupport.closureWitness
      (context.applyFree left.substitution) left.target).capVars
  apply mem_dedupFirst.mpr
  simp only [ObservableSupport.closureWitness, Ty.capVars, Ty.capVarsList,
    List.mem_append]
  exact Or.inl (ObservableSupport.contextWitness_cap _ member)

private theorem leftAliases_fix_closedContext
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (context : Context) (substitution : Subst)
    (solved : Solves substitution
      (addAliases
        (VisibleSupportGraph.leftAliases
          (ClosureSupportConstruction.build transport context) context)
        (context.interfaceEquations left.substitution))) :
    (context.applyFree left.substitution).SubstitutionsAgree substitution
      (Subst.compose substitution
        (ClosureSupportConstruction.build transport context).globalRenaming.substitution) := by
  let data := ClosureSupportConstruction.build transport context
  let aliases := VisibleSupportGraph.leftAliases data context
  have leftSolved : Solves substitution
      (context.interfaceEquations left.substitution) := by
    rw [addAliases_eq_reverse_map_append] at solved
    exact (solves_append substitution _ _).mp solved |>.2
  constructor
  · intro source sourceClosed
    have sourceMember := closedContextTy_source transport context sourceClosed
    let target := data.support.ty.forward source
    have globalTarget : data.globalRenaming.tyForward source = target :=
      data.support.tyForward_agrees sourceMember
    have globalTarget' :
        (ClosureSupportConstruction.build transport context).globalRenaming.tyForward
          source = target := by simpa [data] using globalTarget
    by_cases same : target = source
    · change substitution.ty source = substitution.ty
          ((ClosureSupportConstruction.build transport context).globalRenaming.tyForward
            source)
      rw [globalTarget', same]
    · have edge : substitution.ty target = substitution.ty source := by
        by_cases targetContext : target ∈ context.freeTyVars
        · exact leftTyEdge_entailed_of_target_context transport
            leftAbsorbing rightAbsorbing context sourceMember targetContext
            substitution leftSolved
        · have aliasMember : FreshAliasSequence.Alias.ty target source ∈
              VisibleSupportGraph.leftAliases data context := by
            apply List.mem_append_left
            apply List.mem_map.mpr
            refine ⟨source, ?_, rfl⟩
            simp [VisibleSupportGraph.leftTySources, data, sourceMember,
              sourceClosed, same, targetContext, target]
          have held := aliasEquation_holds_of_solves_addAliases solved
            (alias := FreshAliasSequence.Alias.ty target source) (by
              simpa [data] using aliasMember)
          simpa [aliasEquation, Equation.Holds, Ty.apply] using held
      change substitution.ty source = substitution.ty
        ((ClosureSupportConstruction.build transport context).globalRenaming.tyForward
          source)
      rw [globalTarget']
      exact edge.symm
  · intro source sourceClosed
    have sourceMember := closedContextCap_source transport context sourceClosed
    let target := data.support.cap.forward source
    have globalTarget : data.globalRenaming.capForward source = target :=
      data.support.capForward_agrees sourceMember
    have globalTarget' :
        (ClosureSupportConstruction.build transport context).globalRenaming.capForward
          source = target := by simpa [data] using globalTarget
    by_cases same : target = source
    · change substitution.cap source = substitution.cap
          ((ClosureSupportConstruction.build transport context).globalRenaming.capForward
            source)
      rw [globalTarget', same]
    · have edge : substitution.cap target = substitution.cap source := by
        by_cases targetContext : target ∈ context.freeCapVars
        · exact leftCapEdge_entailed_of_target_context transport
            leftAbsorbing rightAbsorbing context sourceMember targetContext
            substitution leftSolved
        · have aliasMember : FreshAliasSequence.Alias.cap target source ∈
              VisibleSupportGraph.leftAliases data context := by
            apply List.mem_append_right
            apply List.mem_map.mpr
            refine ⟨source, ?_, rfl⟩
            simp [VisibleSupportGraph.leftCapSources, data, sourceMember,
              sourceClosed, same, targetContext, target]
          have held := aliasEquation_holds_of_solves_addAliases solved
            (alias := FreshAliasSequence.Alias.cap target source) (by
              simpa [data] using aliasMember)
          simpa [aliasEquation, Equation.Holds, Cap.apply] using held
      change substitution.cap source = substitution.cap
        ((ClosureSupportConstruction.build transport context).globalRenaming.capForward
          source)
      rw [globalTarget']
      exact edge.symm

private theorem rightAliases_fix_closedContext
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (context : Context) (substitution : Subst)
    (solved : Solves substitution
      (addAliases
        (VisibleSupportGraph.rightAliases
          (ClosureSupportConstruction.build transport context) context)
        (context.interfaceEquations right.substitution))) :
    (context.applyFree left.substitution).SubstitutionsAgree substitution
      (Subst.compose substitution
        (ClosureSupportConstruction.build transport context).globalRenaming.substitution) := by
  let data := ClosureSupportConstruction.build transport context
  let aliases := VisibleSupportGraph.rightAliases data context
  have rightSolved : Solves substitution
      (context.interfaceEquations right.substitution) := by
    rw [addAliases_eq_reverse_map_append] at solved
    exact (solves_append substitution _ _).mp solved |>.2
  constructor
  · intro source sourceClosed
    have sourceMember := closedContextTy_source transport context sourceClosed
    let target := data.support.ty.forward source
    have globalTarget : data.globalRenaming.tyForward source = target :=
      data.support.tyForward_agrees sourceMember
    have globalTarget' :
        (ClosureSupportConstruction.build transport context).globalRenaming.tyForward
          source = target := by simpa [data] using globalTarget
    by_cases same : target = source
    · change substitution.ty source = substitution.ty
          ((ClosureSupportConstruction.build transport context).globalRenaming.tyForward
            source)
      rw [globalTarget', same]
    · have edge : substitution.ty source = substitution.ty target := by
        by_cases sourceContext : source ∈ context.freeTyVars
        · exact rightTyEdge_entailed_of_source_context transport
            leftAbsorbing context sourceMember sourceContext
            substitution rightSolved
        · have aliasMember : FreshAliasSequence.Alias.ty source target ∈
              VisibleSupportGraph.rightAliases data context := by
            apply List.mem_append_left
            apply List.mem_map.mpr
            refine ⟨source, ?_, rfl⟩
            simp [VisibleSupportGraph.rightTySources, data, sourceMember,
              sourceClosed, same, sourceContext, target]
          have held := aliasEquation_holds_of_solves_addAliases solved
            (alias := FreshAliasSequence.Alias.ty source target) (by
              simpa [data] using aliasMember)
          simpa [aliasEquation, Equation.Holds, Ty.apply] using held
      change substitution.ty source = substitution.ty
        ((ClosureSupportConstruction.build transport context).globalRenaming.tyForward
          source)
      rw [globalTarget']
      exact edge
  · intro source sourceClosed
    have sourceMember := closedContextCap_source transport context sourceClosed
    let target := data.support.cap.forward source
    have globalTarget : data.globalRenaming.capForward source = target :=
      data.support.capForward_agrees sourceMember
    have globalTarget' :
        (ClosureSupportConstruction.build transport context).globalRenaming.capForward
          source = target := by simpa [data] using globalTarget
    by_cases same : target = source
    · change substitution.cap source = substitution.cap
          ((ClosureSupportConstruction.build transport context).globalRenaming.capForward
            source)
      rw [globalTarget', same]
    · have edge : substitution.cap source = substitution.cap target := by
        by_cases sourceContext : source ∈ context.freeCapVars
        · exact rightCapEdge_entailed_of_source_context transport
            leftAbsorbing context sourceMember sourceContext
            substitution rightSolved
        · have aliasMember : FreshAliasSequence.Alias.cap source target ∈
              VisibleSupportGraph.rightAliases data context := by
            apply List.mem_append_right
            apply List.mem_map.mpr
            refine ⟨source, ?_, rfl⟩
            simp [VisibleSupportGraph.rightCapSources, data, sourceMember,
              sourceClosed, same, sourceContext, target]
          have held := aliasEquation_holds_of_solves_addAliases solved
            (alias := FreshAliasSequence.Alias.cap source target) (by
              simpa [data] using aliasMember)
          simpa [aliasEquation, Equation.Holds, Cap.apply] using held
      change substitution.cap source = substitution.cap
        ((ClosureSupportConstruction.build transport context).globalRenaming.capForward
          source)
      rw [globalTarget']
      exact edge

private theorem solves_interface_of_applyFree_eq
    (context : Context) (block later : Subst)
    (equality : context.applyFree later =
      (context.applyFree block).applyFree later) :
    Solves later (context.interfaceEquations block) := by
  apply (context.solves_interfaceEquations_iff block later).mpr
  apply Context.substitutionsAgree_of_applyFree_eq
  calc
    context.applyFree later =
        (context.applyFree block).applyFree later := equality
    _ = context.applyFree (Subst.compose later block) := by
      rw [Context.applyFree_compose]

/-- Adding the visible left graph aliases to the left interface entails the
right interface. -/
theorem leftVisible_entails_right
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (context : Context) (substitution : Subst)
    (solved : Solves substitution
      (addAliases
        (VisibleSupportGraph.leftAliases
          (ClosureSupportConstruction.build transport context) context)
        (context.interfaceEquations left.substitution))) :
    Solves substitution (context.interfaceEquations right.substitution) := by
  let data := ClosureSupportConstruction.build transport context
  have leftSolved : Solves substitution
      (context.interfaceEquations left.substitution) := by
    rw [addAliases_eq_reverse_map_append] at solved
    exact (solves_append substitution _ _).mp solved |>.2
  have fixedAgree := leftAliases_fix_closedContext transport leftAbsorbing
    rightAbsorbing context substitution solved
  have fixedContext := Context.applyFree_eq_of_substitutionsAgree fixedAgree
  have rightClosed :
      (context.applyFree right.substitution).applyFree substitution =
        (context.applyFree left.substitution).applyFree substitution := by
    calc
      (context.applyFree right.substitution).applyFree substitution =
          ((context.applyFree left.substitution).applyFree
            data.globalRenaming.substitution).applyFree substitution := by
        rw [data.closedContext_exact]
      _ = (context.applyFree left.substitution).applyFree
          (Subst.compose substitution data.globalRenaming.substitution) := by
        rw [Context.applyFree_compose]
      _ = (context.applyFree left.substitution).applyFree substitution :=
        fixedContext.symm
  apply solves_interface_of_applyFree_eq context right.substitution substitution
  calc
    context.applyFree substitution =
        (context.applyFree left.substitution).applyFree substitution :=
      context.applyFree_interface_transport left.substitution substitution
        leftSolved
    _ = (context.applyFree right.substitution).applyFree substitution :=
      rightClosed.symm

/-- Adding the visible right graph aliases to the right interface entails
the left interface. -/
theorem rightVisible_entails_left
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (context : Context) (substitution : Subst)
    (solved : Solves substitution
      (addAliases
        (VisibleSupportGraph.rightAliases
          (ClosureSupportConstruction.build transport context) context)
        (context.interfaceEquations right.substitution))) :
    Solves substitution (context.interfaceEquations left.substitution) := by
  let data := ClosureSupportConstruction.build transport context
  have rightSolved : Solves substitution
      (context.interfaceEquations right.substitution) := by
    rw [addAliases_eq_reverse_map_append] at solved
    exact (solves_append substitution _ _).mp solved |>.2
  have fixedAgree := rightAliases_fix_closedContext transport leftAbsorbing
    context substitution solved
  have fixedContext := Context.applyFree_eq_of_substitutionsAgree fixedAgree
  have rightClosed :
      (context.applyFree right.substitution).applyFree substitution =
        (context.applyFree left.substitution).applyFree substitution := by
    calc
      (context.applyFree right.substitution).applyFree substitution =
          ((context.applyFree left.substitution).applyFree
            data.globalRenaming.substitution).applyFree substitution := by
        rw [data.closedContext_exact]
      _ = (context.applyFree left.substitution).applyFree
          (Subst.compose substitution data.globalRenaming.substitution) := by
        rw [Context.applyFree_compose]
      _ = (context.applyFree left.substitution).applyFree substitution :=
        fixedContext.symm
  apply solves_interface_of_applyFree_eq context left.substitution substitution
  calc
    context.applyFree substitution =
        (context.applyFree right.substitution).applyFree substitution :=
      context.applyFree_interface_transport right.substitution substitution
        rightSolved
    _ = (context.applyFree left.substitution).applyFree substitution :=
      rightClosed

private theorem combined_solves_leftAliases
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (substitution : Subst)
    (leftSolved : Solves substitution
      (context.interfaceEquations left.substitution))
    (rightSolved : Solves substitution
      (context.interfaceEquations right.substitution)) :
    Solves substitution
      (addAliases
        (VisibleSupportGraph.leftAliases
          (ClosureSupportConstruction.build transport context) context)
        (context.interfaceEquations left.substitution)) := by
  let data := ClosureSupportConstruction.build transport context
  let aliases := VisibleSupportGraph.leftAliases data context
  have fixed := Context.substitutionsAgree_compose_renaming_of_interfaces
    context left.substitution right.substitution substitution
    data.globalRenaming leftSolved rightSolved data.closedContext_exact
  rw [addAliases_eq_reverse_map_append]
  apply (solves_append substitution _ _).mpr
  refine ⟨?_, leftSolved⟩
  intro equation equationMember
  obtain ⟨alias, aliasMemberReverse, rfl⟩ := List.mem_map.mp equationMember
  have aliasMember : alias ∈ aliases := by simpa using aliasMemberReverse
  rcases List.mem_append.mp aliasMember with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    have facts : source ∈ data.support.ty.source ∧
        source ∈ (context.applyFree left.substitution).freeTyVars ∧
        data.support.ty.forward source ≠ source ∧
        data.support.ty.forward source ∉ context.freeTyVars := by
      simpa [aliases, VisibleSupportGraph.leftAliases,
        VisibleSupportGraph.leftTySources] using sourceMember
    have agree := fixed.1 source facts.2.1
    have global : data.globalRenaming.tyForward source =
        data.support.ty.forward source :=
      data.support.tyForward_agrees facts.1
    change substitution.ty (data.support.ty.forward source) =
      substitution.ty source
    simpa [Subst.compose, VariableRenaming.substitution, Ty.apply, global]
      using agree.symm
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    have facts : source ∈ data.support.cap.source ∧
        source ∈ (context.applyFree left.substitution).freeCapVars ∧
        data.support.cap.forward source ≠ source ∧
        data.support.cap.forward source ∉ context.freeCapVars := by
      simpa [aliases, VisibleSupportGraph.leftAliases,
        VisibleSupportGraph.leftCapSources] using sourceMember
    have agree := fixed.2 source facts.2.1
    have global : data.globalRenaming.capForward source =
        data.support.cap.forward source :=
      data.support.capForward_agrees facts.1
    change substitution.cap (data.support.cap.forward source) =
      substitution.cap source
    simpa [Subst.compose, VariableRenaming.substitution, Cap.apply, global]
      using agree.symm

private theorem combined_solves_rightAliases
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) (substitution : Subst)
    (leftSolved : Solves substitution
      (context.interfaceEquations left.substitution))
    (rightSolved : Solves substitution
      (context.interfaceEquations right.substitution)) :
    Solves substitution
      (addAliases
        (VisibleSupportGraph.rightAliases
          (ClosureSupportConstruction.build transport context) context)
        (context.interfaceEquations right.substitution)) := by
  let data := ClosureSupportConstruction.build transport context
  let aliases := VisibleSupportGraph.rightAliases data context
  have fixed := Context.substitutionsAgree_compose_renaming_of_interfaces
    context left.substitution right.substitution substitution
    data.globalRenaming leftSolved rightSolved data.closedContext_exact
  rw [addAliases_eq_reverse_map_append]
  apply (solves_append substitution _ _).mpr
  refine ⟨?_, rightSolved⟩
  intro equation equationMember
  obtain ⟨alias, aliasMemberReverse, rfl⟩ := List.mem_map.mp equationMember
  have aliasMember : alias ∈ aliases := by simpa using aliasMemberReverse
  rcases List.mem_append.mp aliasMember with tyMember | capMember
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp tyMember
    have facts : source ∈ data.support.ty.source ∧
        source ∈ (context.applyFree left.substitution).freeTyVars ∧
        data.support.ty.forward source ≠ source ∧
        source ∉ context.freeTyVars := by
      simpa [aliases, VisibleSupportGraph.rightAliases,
        VisibleSupportGraph.rightTySources] using sourceMember
    have agree := fixed.1 source facts.2.1
    have global : data.globalRenaming.tyForward source =
        data.support.ty.forward source :=
      data.support.tyForward_agrees facts.1
    change substitution.ty source =
      substitution.ty (data.support.ty.forward source)
    simpa [Subst.compose, VariableRenaming.substitution, Ty.apply, global]
      using agree
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp capMember
    have facts : source ∈ data.support.cap.source ∧
        source ∈ (context.applyFree left.substitution).freeCapVars ∧
        data.support.cap.forward source ≠ source ∧
        source ∉ context.freeCapVars := by
      simpa [aliases, VisibleSupportGraph.rightAliases,
        VisibleSupportGraph.rightCapSources] using sourceMember
    have agree := fixed.2 source facts.2.1
    have global : data.globalRenaming.capForward source =
        data.support.cap.forward source :=
      data.support.capForward_agrees facts.1
    change substitution.cap source =
      substitution.cap (data.support.cap.forward source)
    simpa [Subst.compose, VariableRenaming.substitution, Cap.apply, global]
      using agree

/-- The visible left graph aliases present the conjunction of the two
concrete interfaces. -/
theorem leftVisiblePresentation
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing) (rightAbsorbing : right.Absorbing)
    (context : Context) :
    HardEquivalent
      (addAliases
        (VisibleSupportGraph.leftAliases
          (ClosureSupportConstruction.build transport context) context)
        (context.interfaceEquations left.substitution))
      (context.interfaceEquations left.substitution ++
        context.interfaceEquations right.substitution) := by
  intro substitution
  constructor
  · intro solved
    have leftSolved : Solves substitution
        (context.interfaceEquations left.substitution) := by
      rw [addAliases_eq_reverse_map_append] at solved
      exact (solves_append substitution _ _).mp solved |>.2
    exact (solves_append substitution _ _).mpr ⟨leftSolved,
      leftVisible_entails_right transport leftAbsorbing rightAbsorbing
        context substitution solved⟩
  · intro solved
    have parts := (solves_append substitution _ _).mp solved
    exact combined_solves_leftAliases transport context substitution
      parts.1 parts.2

/-- Right-hand counterpart of `leftVisiblePresentation`. -/
theorem rightVisiblePresentation
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (context : Context) :
    HardEquivalent
      (addAliases
        (VisibleSupportGraph.rightAliases
          (ClosureSupportConstruction.build transport context) context)
        (context.interfaceEquations right.substitution))
      (context.interfaceEquations left.substitution ++
        context.interfaceEquations right.substitution) := by
  intro substitution
  constructor
  · intro solved
    have rightSolved : Solves substitution
        (context.interfaceEquations right.substitution) := by
      rw [addAliases_eq_reverse_map_append] at solved
      exact (solves_append substitution _ _).mp solved |>.2
    exact (solves_append substitution _ _).mpr ⟨
      rightVisible_entails_left transport leftAbsorbing context substitution
        solved, rightSolved⟩
  · intro solved
    have parts := (solves_append substitution _ _).mp solved
    exact combined_solves_rightAliases transport context substitution
      parts.1 parts.2

end TypePM.Source.InterfaceAliasDecomposition.SupportGraph
