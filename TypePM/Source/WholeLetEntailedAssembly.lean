import TypePM.Source.AliasRenamingTransport
import TypePM.Source.FullM2Coherence
import TypePM.Source.WholeLetPulledAliasComposition

/-!
# Source-specific whole-let entailed assembly

This module develops the support facts used by the
`FullM2LetSupportedAssemblyBridge`: solving both closure interfaces makes the
closure renaming invisible on every variable that can occur in the original
source-derived body.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition

/-- The interface-only data required to present the two concrete closure
interfaces as one common hard theory.  The graph aliases record the finite
part of a closure-representative renaming that is visible at the original
(unrenamed) `let` boundary.  Keeping this package independent of the body
renaming is important: the canonical renaming used to build these aliases
need not be the renaming selected by the transported body derivation. -/
structure GraphAliasPresentation
    (start boundary : Supply)
    (leftInterface rightInterface : List Equation) where
  leftHidden : List UnificationVar
  rightHidden : List UnificationVar
  leftHiddenFresh : VariablesFreshIn start boundary leftHidden
  rightHiddenFresh : VariablesFreshIn start boundary rightHidden
  leftAliases : List FreshAliasSequence.Alias
  rightAliases : List FreshAliasSequence.Alias
  leftPresentation : HardEquivalent
    (EquationLists.addAliases leftAliases leftInterface)
    (leftInterface ++ rightInterface)
  rightPresentation : HardEquivalent
    (EquationLists.addAliases rightAliases rightInterface)
    (leftInterface ++ rightInterface)
  leftAliasFresh : ∀ alias, alias ∈ leftAliases →
    AliasFreshness.freshVariable alias ∈ leftHidden
  rightAliasFresh : ∀ alias, alias ∈ rightAliases →
    AliasFreshness.freshVariable alias ∈ rightHidden
  leftScoped : AliasFreshness.ScopedBy
    (TypePM.unificationVars leftInterface) leftAliases
  rightScoped : AliasFreshness.ScopedBy
    (TypePM.unificationVars rightInterface) rightAliases

/-- A graph presentation together with the inherited-context avoidance
needed to lift its interface scope across the two source-derived bodies. -/
structure LetGraphAliasPresentation
    (start boundary : Supply)
    (leftInterface rightInterface : List Equation)
    (leftBodyContext rightBodyContext : Context) where
  interface : GraphAliasPresentation start boundary
    leftInterface rightInterface
  leftContextAvoids : VariablesAvoid interface.leftHidden
    leftBodyContext.unificationVars
  rightContextAvoids : VariablesAvoid interface.rightHidden
    rightBodyContext.unificationVars

namespace GraphAliasPresentation

/-- Body-level alias scope extends through a fixed interface whose equations
avoid the aliases' hidden fresh endpoints. -/
theorem scopedBodyWhole
    {effects : List Equation} {body : Generated}
    {aliases : List FreshAliasSequence.Alias}
    {hidden : List UnificationVar}
    (scopeProof : AliasFreshness.ScopedBy body.unificationVars aliases)
    (aliasFresh : ∀ alias, alias ∈ aliases →
      AliasFreshness.freshVariable alias ∈ hidden)
    (effectsAvoid : EquationsAvoid hidden effects) :
    AliasFreshness.ScopedBy
      (Generated.fromLet effects body).unificationVars aliases := by
  refine ⟨scopeProof.1, ?_⟩
  intro alias member
  have endpoints := scopeProof.2 alias member
  constructor
  · intro wholeMember
    rcases (Generated.mem_unificationVars_fromLet_iff effects body _).mp
      wholeMember with effectsMember | bodyMember
    · exact effectsAvoid _ effectsMember (aliasFresh alias member)
    · exact endpoints.1 bodyMember
  · exact (Generated.mem_unificationVars_fromLet_iff effects body _).mpr
      (Or.inr endpoints.2)

private theorem earlierLaterFreshDisjoint
    {graphStart boundary finish : Supply}
    {earlierHidden laterHidden : List UnificationVar}
    (earlierFresh : VariablesFreshIn graphStart boundary earlierHidden)
    (laterFresh : VariablesFreshIn boundary finish laterHidden) :
    ∀ candidate, candidate ∈ earlierHidden → candidate ∉ laterHidden := by
  intro candidate earlierMember laterMember
  have before := earlierFresh candidate earlierMember
  have after := laterFresh candidate laterMember
  cases candidate <;> simp only [UnificationVar.FreshIn] at before after
  · omega
  · omega

/-- Interface-level scope extends to the complete left `let` block once the
source-derived body is known not to mention the graph's fresh endpoints. -/
theorem leftScopedWhole
    {start boundary : Supply} {leftInterface rightInterface : List Equation}
    (presentation : GraphAliasPresentation start boundary
      leftInterface rightInterface)
    (body : Generated) (bodyAvoids : GeneratedAvoids presentation.leftHidden body) :
    AliasFreshness.ScopedBy
      (Generated.fromLet leftInterface body).unificationVars
      presentation.leftAliases := by
  refine ⟨presentation.leftScoped.1, ?_⟩
  intro alias member
  have endpoints := presentation.leftScoped.2 alias member
  constructor
  · intro wholeMember
    rcases (Generated.mem_unificationVars_fromLet_iff
      leftInterface body _).mp wholeMember with interfaceMember | bodyMember
    · exact endpoints.1 interfaceMember
    · exact bodyAvoids _ bodyMember
        (presentation.leftAliasFresh alias member)
  · exact (Generated.mem_unificationVars_fromLet_iff
      leftInterface body _).mpr (Or.inl endpoints.2)

/-- Right-hand counterpart of `leftScopedWhole`. -/
theorem rightScopedWhole
    {start boundary : Supply} {leftInterface rightInterface : List Equation}
    (presentation : GraphAliasPresentation start boundary
      leftInterface rightInterface)
    (body : Generated) (bodyAvoids : GeneratedAvoids presentation.rightHidden body) :
    AliasFreshness.ScopedBy
      (Generated.fromLet rightInterface body).unificationVars
      presentation.rightAliases := by
  refine ⟨presentation.rightScoped.1, ?_⟩
  intro alias member
  have endpoints := presentation.rightScoped.2 alias member
  constructor
  · intro wholeMember
    rcases (Generated.mem_unificationVars_fromLet_iff
      rightInterface body _).mp wholeMember with interfaceMember | bodyMember
    · exact endpoints.1 interfaceMember
    · exact bodyAvoids _ bodyMember
        (presentation.rightAliasFresh alias member)
  · exact (Generated.mem_unificationVars_fromLet_iff
      rightInterface body _).mpr (Or.inl endpoints.2)

/-- Append later body aliases to the left graph aliases.  The half-open
source intervals make their fresh endpoints disjoint automatically. -/
theorem leftCombinedScoped
    {start boundary finish : Supply}
    {leftInterface rightInterface : List Equation}
    (presentation : GraphAliasPresentation start boundary
      leftInterface rightInterface)
    (body : Generated) (graphAvoidsBody : GeneratedAvoids presentation.leftHidden body)
    {bodyAliases : List FreshAliasSequence.Alias}
    {bodyHidden : List UnificationVar}
    (bodyScoped : AliasFreshness.ScopedBy body.unificationVars bodyAliases)
    (bodyAliasFresh : ∀ alias, alias ∈ bodyAliases →
      AliasFreshness.freshVariable alias ∈ bodyHidden)
    (bodyHiddenFresh : VariablesFreshIn boundary finish bodyHidden)
    (interfaceAvoidsBodyHidden : EquationsAvoid bodyHidden leftInterface) :
    AliasFreshness.ScopedBy
      (Generated.fromLet leftInterface body).unificationVars
      (presentation.leftAliases ++ bodyAliases) := by
  have graphScoped := presentation.leftScopedWhole body graphAvoidsBody
  have laterScoped := scopedBodyWhole bodyScoped bodyAliasFresh
    interfaceAvoidsBodyHidden
  apply AliasFreshness.ScopedBy.append graphScoped laterScoped
  intro candidate graphMember bodyMember
  obtain ⟨graphAlias, graphAliasMember, graphEquality⟩ :=
    List.mem_map.mp graphMember
  obtain ⟨bodyAlias, bodyAliasMember, bodyEquality⟩ :=
    List.mem_map.mp bodyMember
  have graphHiddenMember := presentation.leftAliasFresh
    graphAlias graphAliasMember
  have bodyHiddenMember := bodyAliasFresh bodyAlias bodyAliasMember
  have sameFresh : AliasFreshness.freshVariable graphAlias =
      AliasFreshness.freshVariable bodyAlias :=
    graphEquality.trans bodyEquality.symm
  exact earlierLaterFreshDisjoint presentation.leftHiddenFresh bodyHiddenFresh
    _ graphHiddenMember (sameFresh ▸ bodyHiddenMember)

/-- Right-hand counterpart of `leftCombinedScoped`. -/
theorem rightCombinedScoped
    {start boundary finish : Supply}
    {leftInterface rightInterface : List Equation}
    (presentation : GraphAliasPresentation start boundary
      leftInterface rightInterface)
    (body : Generated) (graphAvoidsBody : GeneratedAvoids presentation.rightHidden body)
    {bodyAliases : List FreshAliasSequence.Alias}
    {bodyHidden : List UnificationVar}
    (bodyScoped : AliasFreshness.ScopedBy body.unificationVars bodyAliases)
    (bodyAliasFresh : ∀ alias, alias ∈ bodyAliases →
      AliasFreshness.freshVariable alias ∈ bodyHidden)
    (bodyHiddenFresh : VariablesFreshIn boundary finish bodyHidden)
    (interfaceAvoidsBodyHidden : EquationsAvoid bodyHidden rightInterface) :
    AliasFreshness.ScopedBy
      (Generated.fromLet rightInterface body).unificationVars
      (presentation.rightAliases ++ bodyAliases) := by
  have graphScoped := presentation.rightScopedWhole body graphAvoidsBody
  have laterScoped := scopedBodyWhole bodyScoped bodyAliasFresh
    interfaceAvoidsBodyHidden
  apply AliasFreshness.ScopedBy.append graphScoped laterScoped
  intro candidate graphMember bodyMember
  obtain ⟨graphAlias, graphAliasMember, graphEquality⟩ :=
    List.mem_map.mp graphMember
  obtain ⟨bodyAlias, bodyAliasMember, bodyEquality⟩ :=
    List.mem_map.mp bodyMember
  have graphHiddenMember := presentation.rightAliasFresh
    graphAlias graphAliasMember
  have bodyHiddenMember := bodyAliasFresh bodyAlias bodyAliasMember
  have sameFresh : AliasFreshness.freshVariable graphAlias =
      AliasFreshness.freshVariable bodyAlias :=
    graphEquality.trans bodyEquality.symm
  exact earlierLaterFreshDisjoint presentation.rightHiddenFresh bodyHiddenFresh
    _ graphHiddenMember (sameFresh ▸ bodyHiddenMember)

/-- Extend the finishing supply after the body has been elaborated. -/
def widen
    {start boundary finish : Supply}
    {leftInterface rightInterface : List Equation}
    (presentation : GraphAliasPresentation start boundary
      leftInterface rightInterface)
    (boundaryToFinish : boundary.Le finish) :
    GraphAliasPresentation start finish leftInterface rightInterface :=
  { presentation with
    leftHiddenFresh := presentation.leftHiddenFresh.widen
      (Supply.le_refl start) boundaryToFinish
    rightHiddenFresh := presentation.rightHiddenFresh.widen
      (Supply.le_refl start) boundaryToFinish }

end GraphAliasPresentation

namespace Elaborates

/-- A body generated after `boundary` cannot reintroduce graph-alias names
allocated before that boundary, provided its inherited context already
avoids them. -/
theorem generatedAvoids_previousHidden_of_contextAvoids
    {signature : Signature} {context : Context} {expression : Expr}
    {graphStart boundary finish : Supply} {generated : Generated}
    {hidden : List UnificationVar}
    (derivation : Elaborates signature context expression boundary
      generated finish)
    (hiddenFresh : VariablesFreshIn graphStart boundary hidden)
    (contextAvoids : VariablesAvoid hidden context.unificationVars) :
    GeneratedAvoids hidden generated := by
  intro candidate generatedMember hiddenMember
  rcases derivation.supportProvenance candidate generatedMember with
    contextMember | bodyFresh
  · exact contextAvoids candidate contextMember hiddenMember
  · have graphFresh := hiddenFresh candidate hiddenMember
    cases candidate <;> simp only [UnificationVar.FreshIn] at graphFresh bodyFresh
    · omega
    · omega

/-- Handler-facing form.  The standard source `let` supply theorem rewrites
the declarative joined body start to `afterValue`, after which
`entailedRenamingFixedOn_of_interfaces` applies directly. -/
theorem entailedRenamingFixedOn_of_letBody
    {signature : Signature} {context : Context} {value body : Expr}
    {start afterValue finish : Supply}
    {leftValue rightValue leftBody : Generated}
    (wellFormed : start.WellFormedFor context)
    (leftValueElaboration : Elaborates signature context value start
      leftValue afterValue)
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (leftAbsorbing : leftClosure.Absorbing)
    (alignment : ProvenancedFreshClosureAlignment leftClosure rightClosure
      context afterValue)
    (leftBodyElaboration : Elaborates signature
      ((context.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        context.applyFree leftClosure.substitution)
      body
      (afterValue.join
        (context.applyFree leftClosure.substitution).initialSupply)
      leftBody finish) :
    EntailedRenamingFixedOn
      (context.interfaceEquations leftClosure.substitution ++
        context.interfaceEquations rightClosure.substitution)
      alignment.alignment.alignment.rho leftBody.unificationVars := by
  have bodyStart := leftValueElaboration.letBodySupply_eq leftClosure
    leftAbsorbing wellFormed
  have atAfterValue := leftBodyElaboration
  rw [bodyStart] at atAfterValue
  exact atAfterValue.entailedRenamingFixedOn_of_closureInterfaces
    leftClosure rightClosure alignment.toFreshClosureAlignment

end Elaborates

/-- Source construction boundary for the finite representative graph.  It
depends only on the completed value comparison and its two absorbing
closures; in particular, it is independent of whichever future-fixing
renaming was selected to transport the body derivation. -/
def FullM2LetGraphAliasPresentationComplete : Prop :=
  ∀ {signature : Signature} {context : Context} {value : Expr}
      {start afterValue : Supply} {leftValue rightValue : Generated},
    start.WellFormedFor context →
      Elaborates signature context value start leftValue afterValue →
        Elaborates signature context value start rightValue afterValue →
          SupportedEntailedAlignmentCertificate start afterValue
              leftValue rightValue →
            ∀ (leftClosure : PrincipalBlockClosure leftValue)
                (rightClosure : PrincipalBlockClosure rightValue),
              leftClosure.Absorbing → rightClosure.Absorbing →
                Nonempty (LetGraphAliasPresentation start afterValue
                  (context.interfaceEquations leftClosure.substitution)
                  (context.interfaceEquations rightClosure.substitution)
                  ((context.applyFree leftClosure.substitution).generalize
                      leftClosure.target ::
                    context.applyFree leftClosure.substitution)
                  ((context.applyFree rightClosure.substitution).generalize
                      rightClosure.target ::
                    context.applyFree rightClosure.substitution))

/-- The graph presentation, source body support, and pulled body aliases
jointly discharge the exact supported whole-`let` bridge used by the final
M2 induction. -/
theorem fullM2LetSupportedAssemblyBridge_of_graphAliasPresentation
    (graphComplete : FullM2LetGraphAliasPresentationComplete) :
    FullM2LetSupportedAssemblyBridge := by
  intro signature context value body start afterValue
    leftValue rightValue leftBody rightBody leftNext rightNext
    wellFormed leftValueElaboration rightValueElaboration valueCoherence
    leftClosure rightClosure leftAbsorbing rightAbsorbing
    leftBodyElaboration rightBodyElaboration alignment transportedBody
    bodyCoherence
  have nextEquality := bodyCoherence.next_eq
  subst rightNext
  obtain ⟨graph⟩ := graphComplete wellFormed leftValueElaboration
    rightValueElaboration valueCoherence.certificate leftClosure rightClosure
    leftAbsorbing rightAbsorbing
  have leftBodyStart := leftValueElaboration.letBodySupply_eq leftClosure
    leftAbsorbing wellFormed
  have rightBodyStart := rightValueElaboration.letBodySupply_eq rightClosure
    rightAbsorbing wellFormed
  have leftBodyAtBoundary := leftBodyElaboration
  rw [leftBodyStart] at leftBodyAtBoundary
  have rightBodyAtBoundary := rightBodyElaboration
  rw [rightBodyStart] at rightBodyAtBoundary
  let bodyCertificate := bodyCoherence.certificate
  let rho := alignment.alignment.alignment.rho
  have leftGraphAvoids : GeneratedAvoids graph.interface.leftHidden leftBody :=
    leftBodyAtBoundary.generatedAvoids_previousHidden_of_contextAvoids
      graph.interface.leftHiddenFresh graph.leftContextAvoids
  have rightGraphAvoids : GeneratedAvoids graph.interface.rightHidden rightBody :=
    rightBodyAtBoundary.generatedAvoids_previousHidden_of_contextAvoids
      graph.interface.rightHiddenFresh graph.rightContextAvoids
  have leftEffectsAvoidBodyHidden : EquationsAvoid bodyCertificate.hidden
      (context.interfaceEquations leftClosure.substitution) :=
    leftValueElaboration.interfaceEquations_avoid_laterHidden leftClosure
      leftAbsorbing wellFormed bodyCertificate.hiddenFresh
  have rightEffectsAvoidBodyHidden : EquationsAvoid bodyCertificate.hidden
      (context.interfaceEquations rightClosure.substitution) :=
    rightValueElaboration.interfaceEquations_avoid_laterHidden rightClosure
      rightAbsorbing wellFormed bodyCertificate.hiddenFresh
  have baseFixed :=
    leftBodyAtBoundary.entailedRenamingFixedOn_of_closureInterfaces
      leftClosure rightClosure alignment.toFreshClosureAlignment
  have pulledAliasFresh :=
    AliasRenamingTransport.pulledAliasFresh_hidden_of_certificate
      bodyCertificate alignment.alignment.fixesAtOrAbove
  have leftScoped := graph.interface.leftCombinedScoped leftBody
    leftGraphAvoids
    (AliasRenamingTransport.scopedBy_pullback rho bodyCertificate.leftScoped)
    pulledAliasFresh bodyCertificate.hiddenFresh leftEffectsAvoidBodyHidden
  have rightScoped := graph.interface.rightCombinedScoped rightBody
    rightGraphAvoids bodyCertificate.rightScoped
    bodyCertificate.rightAliasFresh bodyCertificate.hiddenFresh
    rightEffectsAvoidBodyHidden
  have startToAfterValue := leftValueElaboration.supply_le_next
  have afterValueToFinish := leftBodyAtBoundary.supply_le_next
  have leftGraphFreshToFinish := graph.interface.leftHiddenFresh.widen
    (Supply.le_refl start) afterValueToFinish
  have rightGraphFreshToFinish := graph.interface.rightHiddenFresh.widen
    (Supply.le_refl start) afterValueToFinish
  let certificate :=
    supportedWholeLetEntailedCompositionWithPulledLeftAliases_of_baseFixed
      (graph.interface.leftHidden ++ graph.interface.rightHidden)
      (leftGraphFreshToFinish.append rightGraphFreshToFinish)
      startToAfterValue
      graph.interface.leftAliases graph.interface.rightAliases
      graph.interface.leftPresentation graph.interface.rightPresentation
      bodyCertificate baseFixed alignment.alignment.fixesAtOrAbove
      (fun alias member => List.mem_append_left _
        (graph.interface.leftAliasFresh alias member))
      (fun alias member => List.mem_append_right _
        (graph.interface.rightAliasFresh alias member))
      leftScoped rightScoped
  exact ⟨
    { next_eq := rfl
      certificate := certificate }⟩

end TypePM.Source
