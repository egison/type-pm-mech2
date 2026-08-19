import TypePM.Source.BoundedClosureRenaming

/-!
# Future-fixing closure support renamings

The finite permutation used for closure alignment only moves names in its
finite source and target supports.  Consequently, bounding both supports
strictly below a source supply turns the ordinary closure decomposition into
a `FreshClosureAlignment` suitable for recursive elaboration.
-/

namespace TypePM.Source

namespace ClosureSupportConstruction

private theorem contextWitness_ty_origin
    (context : Context) {index : TyVar}
    (member : index ∈
      (InterfaceAliasDecomposition.ObservableSupport.contextWitness
        context).tyVars) :
    index ∈ Context.freeTyVars context := by
  induction context with
  | nil =>
      simp [InterfaceAliasDecomposition.ObservableSupport.contextWitness,
        Ty.tyVars, Ty.tyVarsList] at member
  | cons scheme context induction =>
      simp only [InterfaceAliasDecomposition.ObservableSupport.contextWitness,
        List.map_cons, Ty.tyVars, Ty.tyVarsList, List.mem_append] at member
      apply mem_dedupFirst.mpr
      rw [List.mem_flatMap]
      rcases member with head | tail
      · refine ⟨scheme, by simp, ?_⟩
        apply Scheme.mem_freeTyVars.mpr
        simpa [InterfaceAliasDecomposition.ObservableSupport.schemeWitness]
          using head
      · have tailMember : index ∈ Context.freeTyVars context := induction tail
        obtain ⟨tailScheme, tailSchemeMember, variableMember⟩ :=
          List.mem_flatMap.mp (mem_dedupFirst.mp tailMember)
        exact ⟨tailScheme, by simp [tailSchemeMember], variableMember⟩

private theorem contextWitness_cap_origin
    (context : Context) {index : CapVar}
    (member : index ∈
      (InterfaceAliasDecomposition.ObservableSupport.contextWitness
        context).capVars) :
    index ∈ Context.freeCapVars context := by
  induction context with
  | nil =>
      simp [InterfaceAliasDecomposition.ObservableSupport.contextWitness,
        Ty.capVars, Ty.capVarsList] at member
  | cons scheme context induction =>
      simp only [InterfaceAliasDecomposition.ObservableSupport.contextWitness,
        List.map_cons, Ty.capVars, Ty.capVarsList, List.mem_append] at member
      apply mem_dedupFirst.mpr
      rw [List.mem_flatMap]
      rcases member with head | tail
      · refine ⟨scheme, by simp, ?_⟩
        apply Scheme.mem_freeCapVars.mpr
        simpa [InterfaceAliasDecomposition.ObservableSupport.schemeWitness]
          using head
      · have tailMember : index ∈ Context.freeCapVars context := induction tail
        obtain ⟨tailScheme, tailSchemeMember, variableMember⟩ :=
          List.mem_flatMap.mp (mem_dedupFirst.mp tailMember)
        exact ⟨tailScheme, by simp [tailSchemeMember], variableMember⟩

/-- Every ordinary source-support name comes from the left closed context or
the left closed target. -/
theorem tySource_origin
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {index : TyVar}
    (member : index ∈ (supportBijection transport context).ty.source) :
    index ∈ (context.applyFree left.substitution).freeTyVars ∨
      index ∈ left.target.tyVars := by
  change index ∈ dedupFirst
    (InterfaceAliasDecomposition.ObservableSupport.closureWitness
      (context.applyFree left.substitution) left.target).tyVars at member
  have raw := mem_dedupFirst.mp member
  simp only [InterfaceAliasDecomposition.ObservableSupport.closureWitness,
    Ty.tyVars, Ty.tyVarsList, List.mem_append] at raw
  rcases raw with contextMember | targetMember
  · left
    exact contextWitness_ty_origin _ contextMember
  · exact Or.inr (by simpa using targetMember)

/-- Capability-variable counterpart of `tySource_origin`. -/
theorem capSource_origin
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {index : CapVar}
    (member : index ∈ (supportBijection transport context).cap.source) :
    index ∈ (context.applyFree left.substitution).freeCapVars ∨
      index ∈ left.target.capVars := by
  change index ∈ dedupFirst
    (InterfaceAliasDecomposition.ObservableSupport.closureWitness
      (context.applyFree left.substitution) left.target).capVars at member
  have raw := mem_dedupFirst.mp member
  simp only [InterfaceAliasDecomposition.ObservableSupport.closureWitness,
    Ty.capVars, Ty.capVarsList, List.mem_append] at raw
  rcases raw with contextMember | targetMember
  · left
    exact contextWitness_cap_origin _ contextMember
  · exact Or.inr (by simpa using targetMember)

/-- Every ordinary target-support name comes from the right closed context
or the right closed target. -/
theorem tyTarget_origin
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {index : TyVar}
    (member : index ∈ (supportBijection transport context).ty.target) :
    index ∈ (context.applyFree right.substitution).freeTyVars ∨
      index ∈ right.target.tyVars := by
  let data := ClosureSupportConstruction.build transport context
  let source := data.support.ty.backward index
  have sourceMember : source ∈ data.support.ty.source :=
    data.support.ty.backward_mem member
  have imageEquality : data.globalRenaming.tyForward source = index := by
    rw [ClosureSupportBijection.globalRenaming,
      data.support.tyForward_agrees sourceMember,
      data.support.ty.forward_backward member]
  rcases tySource_origin transport context sourceMember with
    contextMember | targetMember
  · left
    have renamedMember : data.globalRenaming.tyForward source ∈
        ((context.applyFree left.substitution).applyFree
          data.globalRenaming.substitution).freeTyVars := by
      rw [Context.freeTyVars_apply_variableRenaming]
      exact List.mem_map.mpr ⟨source, contextMember, rfl⟩
    rw [data.closedContext_exact] at renamedMember
    simpa [imageEquality] using renamedMember
  · right
    have renamedMember : data.globalRenaming.tyForward source ∈
        (left.target.apply data.globalRenaming.substitution).tyVars := by
      rw [Ty.tyVars_apply_variableRenaming]
      exact List.mem_map.mpr ⟨source, targetMember, rfl⟩
    rw [data.target_exact] at renamedMember
    simpa [imageEquality] using renamedMember

/-- Capability-variable counterpart of `tyTarget_origin`. -/
theorem capTarget_origin
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (context : Context) {index : CapVar}
    (member : index ∈ (supportBijection transport context).cap.target) :
    index ∈ (context.applyFree right.substitution).freeCapVars ∨
      index ∈ right.target.capVars := by
  let data := ClosureSupportConstruction.build transport context
  let source := data.support.cap.backward index
  have sourceMember : source ∈ data.support.cap.source :=
    data.support.cap.backward_mem member
  have imageEquality : data.globalRenaming.capForward source = index := by
    rw [ClosureSupportBijection.globalRenaming,
      data.support.capForward_agrees sourceMember,
      data.support.cap.forward_backward member]
  rcases capSource_origin transport context sourceMember with
    contextMember | targetMember
  · left
    have renamedMember : data.globalRenaming.capForward source ∈
        ((context.applyFree left.substitution).applyFree
          data.globalRenaming.substitution).freeCapVars := by
      rw [Context.freeCapVars_apply_variableRenaming]
      exact List.mem_map.mpr ⟨source, contextMember, rfl⟩
    rw [data.closedContext_exact] at renamedMember
    simpa [imageEquality] using renamedMember
  · right
    have renamedMember : data.globalRenaming.capForward source ∈
        (left.target.apply data.globalRenaming.substitution).capVars := by
      rw [Ty.capVars_apply_variableRenaming]
      exact List.mem_map.mpr ⟨source, targetMember, rfl⟩
    rw [data.target_exact] at renamedMember
    simpa [imageEquality] using renamedMember

end ClosureSupportConstruction

/-- Same-generated closure alignment with an explicit, checkable finite
support bound.  Source elaboration bounds can be connected to these four
premises without changing the closure-alignment construction. -/
noncomputable def freshClosureAlignment_of_transport_boundedSupport
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (boundary : Supply)
    (tySourceBelow : ∀ index,
      index ∈ (ClosureSupportConstruction.build transport context).support.ty.source →
        index.index < boundary.ty)
    (tyTargetBelow : ∀ index,
      index ∈ (ClosureSupportConstruction.build transport context).support.ty.target →
        index.index < boundary.ty)
    (capSourceBelow : ∀ index,
      index ∈ (ClosureSupportConstruction.build transport context).support.cap.source →
        index.index < boundary.cap)
    (capTargetBelow : ∀ index,
      index ∈ (ClosureSupportConstruction.build transport context).support.cap.target →
        index.index < boundary.cap) :
    FreshClosureAlignment left right context boundary := by
  let data := ClosureSupportConstruction.build transport context
  let decomposition :=
    InterfaceAliasDecomposition.ClosureInterfaceDecomposition.build transport
      leftAbsorbing rightAbsorbing context
  refine
    { alignment :=
        CrossGeneratedClosureAlignment.ofClosureInterfaceDecomposition
          decomposition
      fixesAtOrAbove := ?_ }
  change data.globalRenaming.FixesAtOrAbove boundary
  exact data.globalRenaming_fixesAtOrAbove boundary
    tySourceBelow tyTargetBelow capSourceBelow capTargetBelow

/-- Bounds on the two observable closed contexts and targets imply all four
finite support bounds required by
`freshClosureAlignment_of_transport_boundedSupport`. -/
noncomputable def freshClosureAlignment_of_transport_observablesBelow
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (boundary : Supply)
    (leftContextBelow :
      (context.applyFree left.substitution).initialSupply.Le boundary)
    (rightContextBelow :
      (context.applyFree right.substitution).initialSupply.Le boundary)
    (leftTargetBelow : ∀ candidate,
      candidate ∈ left.target.unificationVars →
        candidate.Below boundary.ty boundary.cap)
    (rightTargetBelow : ∀ candidate,
      candidate ∈ right.target.unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    FreshClosureAlignment left right context boundary := by
  apply freshClosureAlignment_of_transport_boundedSupport transport
    leftAbsorbing rightAbsorbing context boundary
  · intro index member
    rcases ClosureSupportConstruction.tySource_origin transport context member with
      contextMember | targetMember
    · exact Nat.lt_of_lt_of_le
        (Context.freeTy_index_lt_initialSupply contextMember)
        leftContextBelow.1
    · exact leftTargetBelow (.ty index)
        ((Ty.mem_tyVars_iff_unificationVars index left.target).mp targetMember)
  · intro index member
    rcases ClosureSupportConstruction.tyTarget_origin transport context member with
      contextMember | targetMember
    · exact Nat.lt_of_lt_of_le
        (Context.freeTy_index_lt_initialSupply contextMember)
        rightContextBelow.1
    · exact rightTargetBelow (.ty index)
        ((Ty.mem_tyVars_iff_unificationVars index right.target).mp targetMember)
  · intro index member
    rcases ClosureSupportConstruction.capSource_origin transport context member with
      contextMember | targetMember
    · exact Nat.lt_of_lt_of_le
        (Context.freeCap_index_lt_initialSupply contextMember)
        leftContextBelow.2
    · exact leftTargetBelow (.cap index)
        ((Ty.mem_capVars_iff_unificationVars index left.target).mp targetMember)
  · intro index member
    rcases ClosureSupportConstruction.capTarget_origin transport context member with
      contextMember | targetMember
    · exact Nat.lt_of_lt_of_le
        (Context.freeCap_index_lt_initialSupply contextMember)
        rightContextBelow.2
    · exact rightTargetBelow (.cap index)
        ((Ty.mem_capVars_iff_unificationVars index right.target).mp targetMember)

/-- A generated-support bound automatically bounds the target of every
absorbing principal closure of that generated block. -/
theorem PrincipalBlockClosure.target_support_below
    {generated : Generated} (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) (boundary : Supply)
    (generatedBelow : ∀ candidate,
      candidate ∈ generated.unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    ∀ candidate, candidate ∈ closure.target.unificationVars →
      candidate.Below boundary.ty boundary.cap := by
  intro candidate member
  have targetCovered : ∀ input,
      input ∈ generated.target.unificationVars →
        input ∈ generated.unificationVars := by
    intro input variableMember
    simp [Generated.unificationVars, variableMember]
  have supported := Subst.Localized.ty_apply_mem
    (closure.localized_of_absorbing absorbing) generated.target
    targetCovered candidate (by
      simpa [PrincipalBlockClosure.target] using member)
  exact generatedBelow candidate supported

/-- Source-ready same-generated endpoint.  A well-formed context bound and a
bound on the generated block support are sufficient to construct a
future-fixing closure alignment for any two absorbing representatives. -/
noncomputable def freshClosureAlignment_of_transport_generatedSupportBelow
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (boundary : Supply)
    (contextBelow : context.initialSupply.Le boundary)
    (generatedBelow : ∀ candidate,
      candidate ∈ generated.unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    FreshClosureAlignment left right context boundary := by
  apply freshClosureAlignment_of_transport_observablesBelow transport
    leftAbsorbing rightAbsorbing context boundary
  · exact Context.applyFree_initialSupply_le_of_localized
      (left.localized_of_absorbing leftAbsorbing) context boundary
      contextBelow generatedBelow
  · exact Context.applyFree_initialSupply_le_of_localized
      (right.localized_of_absorbing rightAbsorbing) context boundary
      contextBelow generatedBelow
  · exact TypePM.Source.PrincipalBlockClosure.target_support_below
      left leftAbsorbing boundary generatedBelow
  · exact TypePM.Source.PrincipalBlockClosure.target_support_below
      right rightAbsorbing boundary generatedBelow

/-- Fully automatic representative-transport specialization of
`freshClosureAlignment_of_transport_generatedSupportBelow`. -/
noncomputable def FreshClosureAlignment.ofSameGeneratedSupportBelow
    {generated : Generated}
    (left right : PrincipalBlockClosure generated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (boundary : Supply)
    (contextBelow : context.initialSupply.Le boundary)
    (generatedBelow : ∀ candidate,
      candidate ∈ generated.unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    FreshClosureAlignment left right context boundary := by
  let related := left.representativeTransport right
  let forward := Classical.choose related
  let remaining := Classical.choose_spec related
  let backward := Classical.choose remaining
  have transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward := Classical.choose_spec remaining
  exact freshClosureAlignment_of_transport_generatedSupportBelow
    transport leftAbsorbing rightAbsorbing context boundary
    contextBelow generatedBelow

end TypePM.Source
