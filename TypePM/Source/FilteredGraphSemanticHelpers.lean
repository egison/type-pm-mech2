import TypePM.Source.InterfaceAliasReallocation

/-!
# Semantic helpers for filtered closure-support graph aliases

Only closure-support edges visible in the closed outer context are relevant
to context interfaces.  If the prospective fresh endpoint is itself an
outer-context variable, the corresponding interface equation already
entails the edge and no alias may be added for it.
-/

namespace TypePM.Source.InterfaceAliasDecomposition.SupportGraph

open EquationLists

/-- On the left, a moved ordinary edge whose target is an outer-context
variable is already entailed by the left interface. -/
theorem leftTyEdge_entailed_of_target_context
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) {source : TyVar}
    (sourceMember : source ∈
      (ClosureSupportConstruction.build transport context).support.ty.source)
    (targetContextMember :
      (ClosureSupportConstruction.build transport context).support.ty.forward
        source ∈ context.freeTyVars) :
    ∀ substitution,
      Solves substitution (context.interfaceEquations left.substitution) →
        (aliasEquation (.ty
          ((ClosureSupportConstruction.build transport context).support.ty.forward
            source) source)).Holds substitution := by
  let data := ClosureSupportConstruction.build transport context
  let target := data.support.ty.forward source
  have targetMember : target ∈ data.support.ty.target :=
    data.support.ty.forward_mem sourceMember
  have rightFixed : right.substitution.ty target = .var target :=
    BuiltSupport.build_tyTarget_fixed transport leftAbsorbing rightAbsorbing
      context target targetMember
  have factor := congrArg (fun current => current.ty target) transport.2
  change (right.substitution.ty target).apply backward =
    left.substitution.ty target at factor
  have backwardImage : backward.ty target = .var source := by
    rw [data.support.ty_backward targetMember,
      data.support.ty.backward_forward sourceMember]
  have leftImage : left.substitution.ty target = .var source := by
    rw [rightFixed, Ty.apply, backwardImage] at factor
    exact factor.symm
  intro substitution solved
  have held := solved (.ty (.var target) (left.substitution.ty target)) (by
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨target, targetContextMember, rfl⟩)
  simpa [aliasEquation, Equation.Holds, leftImage, target] using held

/-- Capability counterpart of `leftTyEdge_entailed_of_target_context`. -/
theorem leftCapEdge_entailed_of_target_context
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) {source : CapVar}
    (sourceMember : source ∈
      (ClosureSupportConstruction.build transport context).support.cap.source)
    (targetContextMember :
      (ClosureSupportConstruction.build transport context).support.cap.forward
        source ∈ context.freeCapVars) :
    ∀ substitution,
      Solves substitution (context.interfaceEquations left.substitution) →
        (aliasEquation (.cap
          ((ClosureSupportConstruction.build transport context).support.cap.forward
            source) source)).Holds substitution := by
  let data := ClosureSupportConstruction.build transport context
  let target := data.support.cap.forward source
  have targetMember : target ∈ data.support.cap.target :=
    data.support.cap.forward_mem sourceMember
  have rightFixed : right.substitution.cap target = .var target :=
    BuiltSupport.build_capTarget_fixed transport leftAbsorbing rightAbsorbing
      context target targetMember
  have factor := congrArg (fun current => current.cap target) transport.2
  change (right.substitution.cap target).apply backward.cap =
    left.substitution.cap target at factor
  have backwardImage : backward.cap target = .var source := by
    rw [data.support.cap_backward targetMember,
      data.support.cap.backward_forward sourceMember]
  have leftImage : left.substitution.cap target = .var source := by
    rw [rightFixed, Cap.apply, backwardImage] at factor
    exact factor.symm
  intro substitution solved
  have held := solved (.cap (.var target) (left.substitution.cap target)) (by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨target, targetContextMember, rfl⟩)
  simpa [aliasEquation, Equation.Holds, leftImage, target] using held

/-- On the right, a moved ordinary edge whose source is an outer-context
variable is already entailed by the right interface. -/
theorem rightTyEdge_entailed_of_source_context
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (context : Context) {source : TyVar}
    (sourceMember : source ∈
      (ClosureSupportConstruction.build transport context).support.ty.source)
    (sourceContextMember : source ∈ context.freeTyVars) :
    ∀ substitution,
      Solves substitution (context.interfaceEquations right.substitution) →
        (aliasEquation (.ty source
          ((ClosureSupportConstruction.build transport context).support.ty.forward
            source))).Holds substitution := by
  let data := ClosureSupportConstruction.build transport context
  let target := data.support.ty.forward source
  have leftFixed : left.substitution.ty source = .var source :=
    BuiltSupport.build_tySource_fixed transport leftAbsorbing context
      source sourceMember
  have factor := congrArg (fun current => current.ty source) transport.1
  change (left.substitution.ty source).apply forward =
    right.substitution.ty source at factor
  have forwardImage : forward.ty source = .var target := by
    simpa [target] using data.support.ty_forward sourceMember
  have rightImage : right.substitution.ty source = .var target := by
    rw [leftFixed, Ty.apply, forwardImage] at factor
    exact factor.symm
  intro substitution solved
  have held := solved (.ty (.var source) (right.substitution.ty source)) (by
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨source, sourceContextMember, rfl⟩)
  simpa [aliasEquation, Equation.Holds, rightImage, target] using held

/-- Capability counterpart of `rightTyEdge_entailed_of_source_context`. -/
theorem rightCapEdge_entailed_of_source_context
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (context : Context) {source : CapVar}
    (sourceMember : source ∈
      (ClosureSupportConstruction.build transport context).support.cap.source)
    (sourceContextMember : source ∈ context.freeCapVars) :
    ∀ substitution,
      Solves substitution (context.interfaceEquations right.substitution) →
        (aliasEquation (.cap source
          ((ClosureSupportConstruction.build transport context).support.cap.forward
            source))).Holds substitution := by
  let data := ClosureSupportConstruction.build transport context
  let target := data.support.cap.forward source
  have leftFixed : left.substitution.cap source = .var source :=
    BuiltSupport.build_capSource_fixed transport leftAbsorbing context
      source sourceMember
  have factor := congrArg (fun current => current.cap source) transport.1
  change (left.substitution.cap source).apply forward.cap =
    right.substitution.cap source at factor
  have forwardImage : forward.cap source = .var target := by
    simpa [target] using data.support.cap_forward sourceMember
  have rightImage : right.substitution.cap source = .var target := by
    rw [leftFixed, Cap.apply, forwardImage] at factor
    exact factor.symm
  intro substitution solved
  have held := solved (.cap (.var source) (right.substitution.cap source)) (by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨source, sourceContextMember, rfl⟩)
  simpa [aliasEquation, Equation.Holds, rightImage, target] using held

end TypePM.Source.InterfaceAliasDecomposition.SupportGraph
