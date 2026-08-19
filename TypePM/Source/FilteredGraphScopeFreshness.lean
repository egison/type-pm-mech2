import TypePM.Source.InterfaceAliasReallocation
import TypePM.Source.WholeLetEntailedAssembly

/-!
# Scope and freshness for visible representative-graph aliases

A complete closure-support graph can contain edges used only by the closed
value target.  Such edges must not become aliases of the enclosing `let`.
This module keeps precisely the edges whose existing endpoint occurs in the
concrete interface on that side, and discharges the support bookkeeping
independently of the semantic interface-presentation proof.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition

namespace FilteredGraphScopeFreshness

open AliasFreshness

/-- Adding source-fresh aliases to a source-derived block preserves the
context-or-allocation-interval support provenance split. -/
theorem addAll_supportProvenance_of_scopedBy
    {context : Context} {start finish : Supply}
    {body : Generated} {aliases : List FreshAliasSequence.Alias}
    (provenance : GeneratedSupportProvenance context start finish body)
    (scopeProof : ScopedBy body.unificationVars aliases)
    (aliasFresh : ∀ alias, alias ∈ aliases →
      (freshVariable alias).FreshIn start finish) :
    GeneratedSupportProvenance context start finish
      (FreshAliasSequence.addAll aliases body) := by
  induction aliases generalizing body with
  | nil => exact provenance
  | cons alias aliases induction =>
      have endpoints := scopeProof.2 alias (by simp)
      have addedProvenance : GeneratedSupportProvenance context start finish
          (alias.add body) := by
        intro candidate member
        rcases (alias_mem_unificationVars_add_iff alias body candidate).mp
            member with rfl | rfl | original
        · exact Or.inr (aliasFresh alias (by simp))
        · exact provenance _ endpoints.2
        · exact provenance candidate original
      have tailExtended := scopeProof.tail_extended
      have tailScope : ScopedBy (alias.add body).unificationVars aliases := by
        refine ⟨tailExtended.1, ?_⟩
        intro later laterMember
        have laterEndpoints := tailExtended.2 later laterMember
        constructor
        · intro addedMember
          apply laterEndpoints.1
          rcases (alias_mem_unificationVars_add_iff alias body _).mp
              addedMember with sameFresh | sameExisting | original
          · exact List.mem_cons.mpr (Or.inl sameFresh)
          · exact List.mem_cons_of_mem _ (sameExisting ▸ endpoints.2)
          · exact List.mem_cons_of_mem _ original
        · rcases List.mem_cons.mp laterEndpoints.2 with same | original
          · exact (alias_mem_unificationVars_add_iff alias body _).mpr
              (Or.inl same)
          · exact (alias_mem_unificationVars_add_iff alias body _).mpr
              (Or.inr (Or.inr original))
      apply induction addedProvenance tailScope
      intro later laterMember
      exact aliasFresh later (by simp [laterMember])

private theorem closureTarget_supportProvenance
    {generated : Generated} {closure : PrincipalBlockClosure generated}
    {context : Context} {start finish : Supply}
    (absorbing : closure.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated) :
    ∀ candidate, candidate ∈ closure.target.unificationVars →
      candidate ∈ context.unificationVars ∨
        candidate.FreshIn start finish := by
  intro candidate member
  have targetCovered : ∀ input,
      input ∈ generated.target.unificationVars →
        input ∈ generated.unificationVars := by
    intro input inputMember
    exact List.mem_append_left _ (List.mem_append_left _ inputMember)
  have generatedMember := Subst.Localized.ty_apply_mem
    (closure.localized_of_absorbing absorbing) generated.target
    targetCovered candidate (by
      simpa [PrincipalBlockClosure.target] using member)
  exact provenance candidate generatedMember

/-- A non-outer ordinary name in the left observable closure support was
allocated during the value elaboration interval. -/
theorem tySource_fresh_of_not_outer
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    {start finish : Supply}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated)
    {index : TyVar}
    (member : index ∈
      (ClosureSupportConstruction.build transport context).support.ty.source)
    (notOuter : index ∉ context.freeTyVars) :
    (UnificationVar.ty index).FreshIn start finish := by
  rcases ClosureSupportConstruction.tySource_origin transport context member with
    contextMember | targetMember
  · have appliedMember : .ty index ∈
        (context.applyFree left.substitution).unificationVars :=
      List.mem_append_left _ (List.mem_map.mpr ⟨index, contextMember, rfl⟩)
    rcases Context.applyFree_supportProvenance
        (left.localized_of_absorbing leftAbsorbing) provenance
        (.ty index) appliedMember with outerMember | fresh
    · exact False.elim (notOuter (by
        simpa [Context.unificationVars] using outerMember))
    · exact fresh
  · exact closureTarget_supportProvenance leftAbsorbing provenance (.ty index)
      ((Ty.mem_tyVars_iff_unificationVars index left.target).mp targetMember)
      |>.resolve_left (fun outerMember => notOuter (by
        simpa [Context.unificationVars] using outerMember))

/-- Capability-variable counterpart of `tySource_fresh_of_not_outer`. -/
theorem capSource_fresh_of_not_outer
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    {start finish : Supply}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated)
    {index : CapVar}
    (member : index ∈
      (ClosureSupportConstruction.build transport context).support.cap.source)
    (notOuter : index ∉ context.freeCapVars) :
    (UnificationVar.cap index).FreshIn start finish := by
  rcases ClosureSupportConstruction.capSource_origin transport context member with
    contextMember | targetMember
  · have appliedMember : .cap index ∈
        (context.applyFree left.substitution).unificationVars :=
      List.mem_append_right _ (List.mem_map.mpr ⟨index, contextMember, rfl⟩)
    rcases Context.applyFree_supportProvenance
        (left.localized_of_absorbing leftAbsorbing) provenance
        (.cap index) appliedMember with outerMember | fresh
    · exact False.elim (notOuter (by
        simpa [Context.unificationVars] using outerMember))
    · exact fresh
  · exact closureTarget_supportProvenance leftAbsorbing provenance (.cap index)
      ((Ty.mem_capVars_iff_unificationVars index left.target).mp targetMember)
      |>.resolve_left (fun outerMember => notOuter (by
        simpa [Context.unificationVars] using outerMember))

/-- A non-outer ordinary name in the right observable closure support was
allocated during the value elaboration interval. -/
theorem tyTarget_fresh_of_not_outer
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    {start finish : Supply}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (rightAbsorbing : right.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated)
    {index : TyVar}
    (member : index ∈
      (ClosureSupportConstruction.build transport context).support.ty.target)
    (notOuter : index ∉ context.freeTyVars) :
    (UnificationVar.ty index).FreshIn start finish := by
  rcases ClosureSupportConstruction.tyTarget_origin transport context member with
    contextMember | targetMember
  · have appliedMember : .ty index ∈
        (context.applyFree right.substitution).unificationVars :=
      List.mem_append_left _ (List.mem_map.mpr ⟨index, contextMember, rfl⟩)
    rcases Context.applyFree_supportProvenance
        (right.localized_of_absorbing rightAbsorbing) provenance
        (.ty index) appliedMember with outerMember | fresh
    · exact False.elim (notOuter (by
        simpa [Context.unificationVars] using outerMember))
    · exact fresh
  · exact closureTarget_supportProvenance rightAbsorbing provenance (.ty index)
      ((Ty.mem_tyVars_iff_unificationVars index right.target).mp targetMember)
      |>.resolve_left (fun outerMember => notOuter (by
        simpa [Context.unificationVars] using outerMember))

/-- Capability-variable counterpart of `tyTarget_fresh_of_not_outer`. -/
theorem capTarget_fresh_of_not_outer
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    {start finish : Supply}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (rightAbsorbing : right.Absorbing)
    (provenance : GeneratedSupportProvenance context start finish generated)
    {index : CapVar}
    (member : index ∈
      (ClosureSupportConstruction.build transport context).support.cap.target)
    (notOuter : index ∉ context.freeCapVars) :
    (UnificationVar.cap index).FreshIn start finish := by
  rcases ClosureSupportConstruction.capTarget_origin transport context member with
    contextMember | targetMember
  · have appliedMember : .cap index ∈
        (context.applyFree right.substitution).unificationVars :=
      List.mem_append_right _ (List.mem_map.mpr ⟨index, contextMember, rfl⟩)
    rcases Context.applyFree_supportProvenance
        (right.localized_of_absorbing rightAbsorbing) provenance
        (.cap index) appliedMember with outerMember | fresh
    · exact False.elim (notOuter (by
        simpa [Context.unificationVars] using outerMember))
    · exact fresh
  · exact closureTarget_supportProvenance rightAbsorbing provenance (.cap index)
      ((Ty.mem_capVars_iff_unificationVars index right.target).mp targetMember)
      |>.resolve_left (fun outerMember => notOuter (by
        simpa [Context.unificationVars] using outerMember))

/-- Retain graph edges whose existing endpoint is visible in `support`. -/
def visibleAliases (support : List UnificationVar)
    (aliases : List FreshAliasSequence.Alias) :
    List FreshAliasSequence.Alias :=
  aliases.filter fun alias => decide
    (existingVariable alias ∈ support ∧ freshVariable alias ∉ support)

/-- The hidden names of one side are exactly its retained fresh endpoints. -/
def hiddenVariables (support : List UnificationVar)
    (aliases : List FreshAliasSequence.Alias) : List UnificationVar :=
  (visibleAliases support aliases).map freshVariable

@[simp] theorem mem_visibleAliases_iff
    {support : List UnificationVar}
    {aliases : List FreshAliasSequence.Alias}
    {alias : FreshAliasSequence.Alias} :
    alias ∈ visibleAliases support aliases ↔
      alias ∈ aliases ∧ existingVariable alias ∈ support ∧
        freshVariable alias ∉ support := by
  simp [visibleAliases]

/-- Filtering a graph scope to the aliases visible in a smaller concrete
support produces scope over that concrete support. -/
theorem scopedBy_visibleAliases
    {graphSupport concreteSupport : List UnificationVar}
    {aliases : List FreshAliasSequence.Alias}
    (graphScoped : ScopedBy graphSupport aliases) :
    ScopedBy concreteSupport (visibleAliases concreteSupport aliases) := by
  constructor
  · exact List.Nodup.sublist
      (List.Sublist.map freshVariable List.filter_sublist) graphScoped.1
  · intro alias member
    have split := mem_visibleAliases_iff.mp member
    exact ⟨split.2.2, split.2.1⟩

/-- Pointwise source-interval freshness becomes freshness of the collected
hidden endpoint list. -/
theorem hiddenVariables_fresh
    {start boundary : Supply} {support : List UnificationVar}
    {aliases : List FreshAliasSequence.Alias}
    (fresh : ∀ alias, alias ∈ visibleAliases support aliases →
      (freshVariable alias).FreshIn start boundary) :
    VariablesFreshIn start boundary (hiddenVariables support aliases) := by
  intro candidate member
  obtain ⟨alias, aliasMember, equality⟩ := List.mem_map.mp member
  exact equality ▸ fresh alias aliasMember

/-- Every retained alias points to an element of its collected hidden list. -/
theorem freshVariable_mem_hiddenVariables
    (support : List UnificationVar)
    (aliases : List FreshAliasSequence.Alias)
    (alias : FreshAliasSequence.Alias)
    (member : alias ∈ visibleAliases support aliases) :
    freshVariable alias ∈ hiddenVariables support aliases :=
  List.mem_map.mpr ⟨alias, member, rfl⟩

/-- Any context support contained in the graph support avoids every retained
fresh endpoint on that side. -/
theorem contextAvoids_hiddenVariables
    {concreteSupport contextSupport : List UnificationVar}
    {aliases : List FreshAliasSequence.Alias}
    (freshOutside : ∀ alias,
      alias ∈ visibleAliases concreteSupport aliases →
        freshVariable alias ∉ contextSupport) :
    VariablesAvoid (hiddenVariables concreteSupport aliases) contextSupport := by
  intro candidate contextMember hiddenMember
  obtain ⟨alias, aliasMember, equality⟩ := List.mem_map.mp hiddenMember
  exact freshOutside alias aliasMember (equality ▸ contextMember)

/-- Assemble the source-facing graph package once the semantic hard
presentations and the support inclusions have been established. -/
def letGraphAliasPresentation
    {start boundary : Supply}
    {leftInterface rightInterface : List Equation}
    {leftBodyContext rightBodyContext : Context}
    {leftGraphSupport rightGraphSupport : List UnificationVar}
    (leftGraphAliases rightGraphAliases : List FreshAliasSequence.Alias)
    (leftGraphScoped : ScopedBy leftGraphSupport leftGraphAliases)
    (rightGraphScoped : ScopedBy rightGraphSupport rightGraphAliases)
    (leftFreshOutsideContext : ∀ alias,
      alias ∈ visibleAliases (TypePM.unificationVars leftInterface)
          leftGraphAliases →
        freshVariable alias ∉ leftBodyContext.unificationVars)
    (rightFreshOutsideContext : ∀ alias,
      alias ∈ visibleAliases (TypePM.unificationVars rightInterface)
          rightGraphAliases →
        freshVariable alias ∉ rightBodyContext.unificationVars)
    (leftFresh : ∀ alias,
      alias ∈ visibleAliases (TypePM.unificationVars leftInterface)
          leftGraphAliases →
        (freshVariable alias).FreshIn start boundary)
    (rightFresh : ∀ alias,
      alias ∈ visibleAliases (TypePM.unificationVars rightInterface)
          rightGraphAliases →
        (freshVariable alias).FreshIn start boundary)
    (leftPresentation : HardEquivalent
      (EquationLists.addAliases
        (visibleAliases (TypePM.unificationVars leftInterface)
          leftGraphAliases) leftInterface)
      (leftInterface ++ rightInterface))
    (rightPresentation : HardEquivalent
      (EquationLists.addAliases
        (visibleAliases (TypePM.unificationVars rightInterface)
          rightGraphAliases) rightInterface)
      (leftInterface ++ rightInterface)) :
    LetGraphAliasPresentation start boundary leftInterface rightInterface
      leftBodyContext rightBodyContext := by
  let leftAliases := visibleAliases
    (TypePM.unificationVars leftInterface) leftGraphAliases
  let rightAliases := visibleAliases
    (TypePM.unificationVars rightInterface) rightGraphAliases
  let leftHidden := hiddenVariables
    (TypePM.unificationVars leftInterface) leftGraphAliases
  let rightHidden := hiddenVariables
    (TypePM.unificationVars rightInterface) rightGraphAliases
  let interface : GraphAliasPresentation start boundary
      leftInterface rightInterface :=
    { leftHidden := leftHidden
      rightHidden := rightHidden
      leftHiddenFresh := hiddenVariables_fresh leftFresh
      rightHiddenFresh := hiddenVariables_fresh rightFresh
      leftAliases := leftAliases
      rightAliases := rightAliases
      leftPresentation := leftPresentation
      rightPresentation := rightPresentation
      leftAliasFresh := freshVariable_mem_hiddenVariables _ _
      rightAliasFresh := freshVariable_mem_hiddenVariables _ _
      leftScoped := scopedBy_visibleAliases leftGraphScoped
      rightScoped := scopedBy_visibleAliases rightGraphScoped }
  exact
    { interface := interface
      leftContextAvoids := contextAvoids_hiddenVariables
        leftFreshOutsideContext
      rightContextAvoids := contextAvoids_hiddenVariables
        rightFreshOutsideContext }

end FilteredGraphScopeFreshness

end TypePM.Source
