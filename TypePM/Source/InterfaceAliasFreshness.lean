import TypePM.Source.InterfaceAliasDecomposition

namespace TypePM.Source.InterfaceAliasDecomposition.Automatic

open EquationLists AliasFreshness BuiltSupport

noncomputable def tyInterfaceScopedWithTail
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context)
    {tailLeft tailRight : List Equation}
    (base : EndpointScopedShape
      (TargetVariables
        (TypePM.Source.ClosureSupportConstruction.build transport context))
      tailLeft tailRight)
    (indices : List TyVar)
    (covered : ∀ index, index ∈ indices →
      index ∈ context.freeTyVars) :
    EndpointScopedShape
      (TargetVariables
        (TypePM.Source.ClosureSupportConstruction.build transport context))
      (((indices.map fun index =>
          Equation.ty (.var index) (left.substitution.ty index)).map
        (ElaborationRenaming.renameEquation
          (TypePM.Source.ClosureSupportConstruction.build
            transport context).globalRenaming)) ++ tailLeft)
      ((indices.map fun index =>
        Equation.ty (.var index) (right.substitution.ty index)) ++
          tailRight) := by
  induction indices with
  | nil => simpa using base
  | cons index indices induction =>
      have indexMember : index ∈ context.freeTyVars :=
        covered index (by simp)
      have tailCovered : ∀ candidate, candidate ∈ indices →
          candidate ∈ context.freeTyVars := by
        intro candidate member
        exact covered candidate (by simp [member])
      let tail := induction tailCovered
      let data := TypePM.Source.ClosureSupportConstruction.build
        transport context
      have rhsExact := BuiltSupport.build_tyRhs_exact
        transport context index indexMember
      have rhsExactData :
          (left.substitution.ty index).apply
              data.globalRenaming.substitution =
            right.substitution.ty index := by
        simpa only [data] using rhsExact
      have renamedHead :
          ElaborationRenaming.renameEquation data.globalRenaming
              (.ty (.var index) (left.substitution.ty index)) =
            .ty (.var (data.globalRenaming.tyForward index))
              (right.substitution.ty index) := by
        change
          Equation.ty (.var (data.globalRenaming.tyForward index))
              ((left.substitution.ty index).apply
                data.globalRenaming.substitution) =
            Equation.ty (.var (data.globalRenaming.tyForward index))
              (right.substitution.ty index)
        rw [rhsExactData]
      simp only [List.map_cons, List.cons_append]
      rw [renamedHead]
      by_cases sourceMember : index ∈ data.support.ty.source
      · have leftFixed := BuiltSupport.build_tySource_fixed
          transport leftAbsorbing context index sourceMember
        have rightImage : right.substitution.ty index =
            .var (data.globalRenaming.tyForward index) := by
          simpa [leftFixed, VariableRenaming.substitution, Ty.apply] using
            rhsExact.symm
        by_cases same : data.globalRenaming.tyForward index = index
        · simpa [rightImage, same] using
            EndpointScopedShape.same
              (.ty (.var index) (.var index)) tail
        · have freshOutside : .ty index ∉ TargetVariables data := by
            simpa only [ty_mem_targetVariables] using
              BuiltSupport.build_tyMovedSource_not_target transport
                leftAbsorbing rightAbsorbing context index indexMember
                sourceMember same
          have existingInside :
              .ty (data.globalRenaming.tyForward index) ∈
                TargetVariables data := by
            apply (ty_mem_targetVariables data _).mpr
            change data.support.toVariableRenaming.tyForward index ∈
              data.support.ty.target
            rw [data.support.tyForward_agrees sourceMember]
            exact data.support.ty.forward_mem sourceMember
          simpa [rightImage] using
            EndpointScopedShape.tyReflAlias index
              (data.globalRenaming.tyForward index) tail
              freshOutside existingInside
      · by_cases targetMember : index ∈ data.support.ty.target
        · have rightFixed := BuiltSupport.build_tyTarget_fixed
            transport leftAbsorbing rightAbsorbing context index targetMember
          by_cases same : data.globalRenaming.tyForward index = index
          · simpa [rightFixed, same] using
              EndpointScopedShape.same
                (.ty (.var index) (.var index)) tail
          · have freshOutside :
                .ty (data.globalRenaming.tyForward index) ∉
                  TargetVariables data := by
              simpa only [ty_mem_targetVariables] using
                BuiltSupport.build_tyForward_not_target_of_not_source
                  transport context index sourceMember
            have existingInside : .ty index ∈ TargetVariables data :=
              (ty_mem_targetVariables data index).mpr targetMember
            simpa [rightFixed] using
              EndpointScopedShape.tyAliasRefl
                (data.globalRenaming.tyForward index) index tail
                freshOutside existingInside
        · have fixed := BuiltSupport.build_tyForward_fixed_outside
            transport context index sourceMember targetMember
          have fixedData : data.globalRenaming.tyForward index = index := by
            simpa only [data] using fixed
          simpa [fixedData] using
            EndpointScopedShape.same
              (.ty (.var index) (right.substitution.ty index)) tail

noncomputable def capInterfaceScopedWithTail
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context)
    {tailLeft tailRight : List Equation}
    (base : EndpointScopedShape
      (TargetVariables
        (TypePM.Source.ClosureSupportConstruction.build transport context))
      tailLeft tailRight)
    (indices : List CapVar)
    (covered : ∀ index, index ∈ indices →
      index ∈ context.freeCapVars) :
    EndpointScopedShape
      (TargetVariables
        (TypePM.Source.ClosureSupportConstruction.build transport context))
      (((indices.map fun index =>
          Equation.cap (.var index) (left.substitution.cap index)).map
        (ElaborationRenaming.renameEquation
          (TypePM.Source.ClosureSupportConstruction.build
            transport context).globalRenaming)) ++ tailLeft)
      ((indices.map fun index =>
        Equation.cap (.var index) (right.substitution.cap index)) ++
          tailRight) := by
  induction indices with
  | nil => simpa using base
  | cons index indices induction =>
      have indexMember : index ∈ context.freeCapVars :=
        covered index (by simp)
      have tailCovered : ∀ candidate, candidate ∈ indices →
          candidate ∈ context.freeCapVars := by
        intro candidate member
        exact covered candidate (by simp [member])
      let tail := induction tailCovered
      let data := TypePM.Source.ClosureSupportConstruction.build
        transport context
      have rhsExact := BuiltSupport.build_capRhs_exact
        transport context index indexMember
      have rhsExactData :
          (left.substitution.cap index).apply
              data.globalRenaming.substitution.cap =
            right.substitution.cap index := by
        simpa only [data] using rhsExact
      have renamedHead :
          ElaborationRenaming.renameEquation data.globalRenaming
              (.cap (.var index) (left.substitution.cap index)) =
            .cap (.var (data.globalRenaming.capForward index))
              (right.substitution.cap index) := by
        change
          Equation.cap (.var (data.globalRenaming.capForward index))
              ((left.substitution.cap index).apply
                data.globalRenaming.substitution.cap) =
            Equation.cap (.var (data.globalRenaming.capForward index))
              (right.substitution.cap index)
        rw [rhsExactData]
      simp only [List.map_cons, List.cons_append]
      rw [renamedHead]
      by_cases sourceMember : index ∈ data.support.cap.source
      · have leftFixed := BuiltSupport.build_capSource_fixed
          transport leftAbsorbing context index sourceMember
        have rightImage : right.substitution.cap index =
            .var (data.globalRenaming.capForward index) := by
          simpa [leftFixed, VariableRenaming.substitution, Cap.apply] using
            rhsExact.symm
        by_cases same : data.globalRenaming.capForward index = index
        · simpa [rightImage, same] using
            EndpointScopedShape.same
              (.cap (.var index) (.var index)) tail
        · have freshOutside : .cap index ∉ TargetVariables data := by
            simpa only [cap_mem_targetVariables] using
              BuiltSupport.build_capMovedSource_not_target transport
                leftAbsorbing rightAbsorbing context index indexMember
                sourceMember same
          have existingInside :
              .cap (data.globalRenaming.capForward index) ∈
                TargetVariables data := by
            apply (cap_mem_targetVariables data _).mpr
            change data.support.toVariableRenaming.capForward index ∈
              data.support.cap.target
            rw [data.support.capForward_agrees sourceMember]
            exact data.support.cap.forward_mem sourceMember
          simpa [rightImage] using
            EndpointScopedShape.capReflAlias index
              (data.globalRenaming.capForward index) tail
              freshOutside existingInside
      · by_cases targetMember : index ∈ data.support.cap.target
        · have rightFixed := BuiltSupport.build_capTarget_fixed
            transport leftAbsorbing rightAbsorbing context index targetMember
          by_cases same : data.globalRenaming.capForward index = index
          · simpa [rightFixed, same] using
              EndpointScopedShape.same
                (.cap (.var index) (.var index)) tail
          · have freshOutside :
                .cap (data.globalRenaming.capForward index) ∉
                  TargetVariables data := by
              simpa only [cap_mem_targetVariables] using
                BuiltSupport.build_capForward_not_target_of_not_source
                  transport context index sourceMember
            have existingInside : .cap index ∈ TargetVariables data :=
              (cap_mem_targetVariables data index).mpr targetMember
            simpa [rightFixed] using
              EndpointScopedShape.capAliasRefl
                (data.globalRenaming.capForward index) index tail
                freshOutside existingInside
        · have fixed := BuiltSupport.build_capForward_fixed_outside
            transport context index sourceMember targetMember
          have fixedData : data.globalRenaming.capForward index = index := by
            simpa only [data] using fixed
          simpa [fixedData] using
            EndpointScopedShape.same
              (.cap (.var index) (right.substitution.cap index)) tail

noncomputable def interfaceEndpointScopedShape
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    EndpointScopedShape
      (TargetVariables
        (TypePM.Source.ClosureSupportConstruction.build transport context))
      ((context.interfaceEquations left.substitution).map
        (ElaborationRenaming.renameEquation
          (TypePM.Source.ClosureSupportConstruction.build
            transport context).globalRenaming))
      (context.interfaceEquations right.substitution) := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  let empty := EndpointScopedShape.nil (TargetVariables data)
  let capPart := capInterfaceScopedWithTail transport leftAbsorbing
    rightAbsorbing context empty context.freeCapVars
      (fun _ member => member)
  let full := tyInterfaceScopedWithTail transport leftAbsorbing
    rightAbsorbing context capPart context.freeTyVars
      (fun _ member => member)
  simpa [Context.interfaceEquations, List.map_append, data] using full

theorem right_leftVariables
    (context : Context) (substitution : Subst) :
    equationLeftVariables (context.interfaceEquations substitution) =
      context.freeTyVars.map UnificationVar.ty ++
        context.freeCapVars.map UnificationVar.cap := by
  have tyPart : ∀ indices : List TyVar,
      List.filterMap
          (equationLeftVariable? ∘ fun index =>
            Equation.ty (.var index) (substitution.ty index)) indices =
        indices.map UnificationVar.ty := by
    intro indices
    induction indices with
    | nil => rfl
    | cons index indices induction =>
        simp [equationLeftVariable?, induction]
  have capPart : ∀ indices : List CapVar,
      List.filterMap
          (equationLeftVariable? ∘ fun index =>
            Equation.cap (.var index) (substitution.cap index)) indices =
        indices.map UnificationVar.cap := by
    intro indices
    induction indices with
    | nil => rfl
    | cons index indices induction =>
        simp [equationLeftVariable?, induction]
  simp [Context.interfaceEquations, equationLeftVariables,
    List.filterMap_append, tyPart, capPart]

theorem renamed_leftVariables
    (rho : VariableRenaming) (context : Context) (substitution : Subst) :
    equationLeftVariables
        ((context.interfaceEquations substitution).map
          (ElaborationRenaming.renameEquation rho)) =
      context.freeTyVars.map (fun index => .ty (rho.tyForward index)) ++
        context.freeCapVars.map (fun index => .cap (rho.capForward index)) := by
  have tyPart : ∀ indices : List TyVar,
      List.filterMap
          (equationLeftVariable? ∘
            ElaborationRenaming.renameEquation rho ∘ fun index =>
              Equation.ty (.var index) (substitution.ty index)) indices =
        indices.map (fun index => .ty (rho.tyForward index)) := by
    intro indices
    induction indices with
    | nil => rfl
    | cons index indices induction =>
        rw [List.filterMap_cons, List.map_cons, induction]
        simp [equationLeftVariable?, ElaborationRenaming.renameEquation,
          VariableRenaming.substitution, Equation.apply, Ty.apply]
  have capPart : ∀ indices : List CapVar,
      List.filterMap
          (equationLeftVariable? ∘
            ElaborationRenaming.renameEquation rho ∘ fun index =>
              Equation.cap (.var index) (substitution.cap index)) indices =
        indices.map (fun index => .cap (rho.capForward index)) := by
    intro indices
    induction indices with
    | nil => rfl
    | cons index indices induction =>
        rw [List.filterMap_cons, List.map_cons, induction]
        simp [equationLeftVariable?, ElaborationRenaming.renameEquation,
          VariableRenaming.substitution, Equation.apply, Cap.apply]
  simp [Context.interfaceEquations, equationLeftVariables,
    List.filterMap_append, tyPart, capPart]

private theorem nodup_map_of_injective
    {α β : Type} (function : α → β) (items : List α)
    (itemsNodup : items.Nodup) (injective : Function.Injective function) :
    (items.map function).Nodup := by
  induction items with
  | nil => exact .nil
  | cons head tail induction =>
      have split := List.nodup_cons.mp itemsNodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨other, otherMember, equality⟩ := List.mem_map.mp member
        have same := injective equality.symm
        exact split.1 (same ▸ otherMember)
      · exact induction split.2

private theorem nodup_append_of_disjoint
    {α : Type} {left right : List α}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (disjoint : ∀ candidate, candidate ∈ left → candidate ∉ right) :
    (left ++ right).Nodup := by
  induction left with
  | nil => exact rightNodup
  | cons head tail induction =>
      have split := List.nodup_cons.mp leftNodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        rcases List.mem_append.mp member with tailMember | rightMember
        · exact split.1 tailMember
        · exact disjoint head (by simp) rightMember
      · exact induction split.2 (fun candidate member =>
          disjoint candidate (List.mem_cons_of_mem _ member))

theorem right_leftVariables_nodup
    (context : Context) (substitution : Subst) :
    (equationLeftVariables
      (context.interfaceEquations substitution)).Nodup := by
  rw [right_leftVariables]
  apply nodup_append_of_disjoint
  · exact nodup_map_of_injective UnificationVar.ty context.freeTyVars
      context.freeTyVars_nodup (by intro left right equality; injection equality)
  · exact nodup_map_of_injective UnificationVar.cap context.freeCapVars
      context.freeCapVars_nodup (by intro left right equality; injection equality)
  · intro candidate tyMember capMember
    obtain ⟨index, _member, rfl⟩ := List.mem_map.mp tyMember
    simp at capMember

theorem renamed_leftVariables_nodup
    (rho : VariableRenaming) (context : Context) (substitution : Subst) :
    (equationLeftVariables
      ((context.interfaceEquations substitution).map
        (ElaborationRenaming.renameEquation rho))).Nodup := by
  rw [renamed_leftVariables]
  apply nodup_append_of_disjoint
  · apply nodup_map_of_injective _ context.freeTyVars
      context.freeTyVars_nodup
    intro left right equality
    injection equality with imageEquality
    have restored := congrArg rho.tyBackward imageEquality
    simpa using restored
  · apply nodup_map_of_injective _ context.freeCapVars
      context.freeCapVars_nodup
    intro left right equality
    injection equality with imageEquality
    have restored := congrArg rho.capBackward imageEquality
    simpa using restored
  · intro candidate tyMember capMember
    obtain ⟨index, _member, rfl⟩ := List.mem_map.mp tyMember
    simp at capMember

theorem interfaceEndpointScopedBy
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := TypePM.Source.ClosureSupportConstruction.build
      transport context
    let certificate := interfaceEndpointScopedShape transport leftAbsorbing
      rightAbsorbing context
    ScopedBy (TargetVariables data)
        certificate.shape.toEquationCommonCore.leftAliases ∧
      ScopedBy (TargetVariables data)
        certificate.shape.toEquationCommonCore.rightAliases := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  let certificate := interfaceEndpointScopedShape transport leftAbsorbing
    rightAbsorbing context
  exact certificate.scopedBy
    (renamed_leftVariables_nodup data.globalRenaming context
      left.substitution)
    (right_leftVariables_nodup context right.substitution)

/-- The automatic interface decomposition together with the finite support
that separates every fresh alias endpoint from every existing endpoint. -/
structure FreshClosureInterfaceDecomposition
    {generated : Generated}
    (left right : PrincipalBlockClosure generated)
    (context : Context) where
  decomposition : ClosureInterfaceDecomposition left right context
  support : List UnificationVar
  leftScoped : ScopedBy support decomposition.equations.leftAliases
  rightScoped : ScopedBy support decomposition.equations.rightAliases

namespace FreshClosureInterfaceDecomposition

noncomputable def build
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    FreshClosureInterfaceDecomposition left right context := by
  let data := TypePM.Source.ClosureSupportConstruction.build
    transport context
  let certificate := interfaceEndpointScopedShape transport leftAbsorbing
    rightAbsorbing context
  let equations := certificate.shape.toEquationCommonCore
  have scopes := interfaceEndpointScopedBy transport leftAbsorbing
    rightAbsorbing context
  exact
    { decomposition :=
        { rho := data.globalRenaming
          closedContext_exact := data.closedContext_exact
          target_exact := data.target_exact
          generalized_exact := data.generalized_exact
          equations := equations }
      support := TargetVariables data
      leftScoped := scopes.1
      rightScoped := scopes.2 }

private theorem scopedBy_append_support
    {support extra : List UnificationVar}
    {aliases : List FreshAliasSequence.Alias}
    (scopeProof : ScopedBy support aliases)
    (avoids : ∀ alias, alias ∈ aliases →
      freshVariable alias ∉ extra) :
    ScopedBy (support ++ extra) aliases := by
  refine ⟨scopeProof.1, ?_⟩
  intro alias member
  have endpoints := scopeProof.2 alias member
  constructor
  · intro membership
    rcases List.mem_append.mp membership with old | added
    · exact endpoints.1 old
    · exact avoids alias member added
  · exact List.mem_append_left _ endpoints.2

/-- Once the common interface core together with the generated body avoids
the automatically identified fresh endpoints, all stepwise alias
admissibility obligations follow, including those for delayed checking
obligations. -/
theorem admissible_of_avoids
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {context : Context}
    (certificate : FreshClosureInterfaceDecomposition left right context)
    (body : Generated)
    (leftAvoids : ∀ alias,
      alias ∈ certificate.decomposition.equations.leftAliases →
        freshVariable alias ∉
          (Generated.fromLet certificate.decomposition.equations.core
            body).unificationVars)
    (rightAvoids : ∀ alias,
      alias ∈ certificate.decomposition.equations.rightAliases →
        freshVariable alias ∉
          (Generated.fromLet certificate.decomposition.equations.core
            body).unificationVars) :
    FreshAliasSequence.Admissible
        certificate.decomposition.equations.leftAliases
        (Generated.fromLet certificate.decomposition.equations.core body) ∧
      FreshAliasSequence.Admissible
        certificate.decomposition.equations.rightAliases
        (Generated.fromLet certificate.decomposition.equations.core body) := by
  let enlarged := certificate.support ++
    (Generated.fromLet certificate.decomposition.equations.core body).unificationVars
  have bodySupported : ∀ candidate,
      candidate ∈
          (Generated.fromLet certificate.decomposition.equations.core body).unificationVars →
        candidate ∈ enlarged := fun candidate member =>
    List.mem_append_right _ member
  constructor
  · apply admissible_of_scopedBy
      (scopedBy_append_support certificate.leftScoped leftAvoids)
      bodySupported
  · apply admissible_of_scopedBy
      (scopedBy_append_support certificate.rightScoped rightAvoids)
      bodySupported

end FreshClosureInterfaceDecomposition

end TypePM.Source.InterfaceAliasDecomposition.Automatic
