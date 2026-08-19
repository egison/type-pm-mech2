import TypePM.Source.ClosureSupportFutureFixing
import TypePM.Source.InterfaceAliasFreshness

/-!
# Fresh closure alignment retaining interface-alias provenance

`CrossGeneratedClosureAlignment` intentionally stores only the semantic
`EquationCommonCore`.  Whole-`let` source composition additionally needs to
know which side of each interface position contributed a genuine alias and
which side contributed a reflexive equation.  This module retains that
`PairwiseAliasShape` without changing the existing alignment API.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition

/-- A future-fixing closure alignment together with the pointwise interface
shape from which its equation common core was constructed. -/
structure ProvenancedFreshClosureAlignment
    {leftGenerated rightGenerated : Generated}
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (context : Context) (boundary : Supply) where
  alignment : FreshClosureAlignment left right context boundary
  interfaceShape : EquationLists.PairwiseAliasShape
    ((context.interfaceEquations left.substitution).map
      (ElaborationRenaming.renameEquation alignment.alignment.rho))
    (context.interfaceEquations right.substitution)

namespace ProvenancedFreshClosureAlignment

/-- Forgetting provenance recovers the existing recursive alignment. -/
def toFreshClosureAlignment
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context} {boundary : Supply}
    (alignment : ProvenancedFreshClosureAlignment left right context boundary) :
    FreshClosureAlignment left right context boundary :=
  alignment.alignment

/-- Same-generated absorbing closures have a provenance-preserving
alignment whenever the finite closure support lies below the future source
boundary. -/
noncomputable def ofSameGeneratedBoundedSupport
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
    ProvenancedFreshClosureAlignment left right context boundary := by
  let data := ClosureSupportConstruction.build transport context
  let shape := InterfaceAliasDecomposition.Automatic.interfaceShape
    transport leftAbsorbing rightAbsorbing context
  let cross : CrossGeneratedClosureAlignment left right context :=
    { rho := data.globalRenaming
      closedContext_exact := data.closedContext_exact
      target_exact := data.target_exact
      generalized_exact := data.generalized_exact
      equations := shape.toEquationCommonCore }
  let fresh : FreshClosureAlignment left right context boundary :=
    { alignment := cross
      fixesAtOrAbove := by
        change data.globalRenaming.FixesAtOrAbove boundary
        exact data.globalRenaming_fixesAtOrAbove boundary
          tySourceBelow tyTargetBelow capSourceBelow capTargetBelow }
  exact
    { alignment := fresh
      interfaceShape := shape }

/-- Source-ready specialization: a generated-support bound and a
well-formed context bound imply all four finite closure-support bounds while
retaining the interface shape. -/
noncomputable def ofTransportGeneratedSupportBelow
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
    ProvenancedFreshClosureAlignment left right context boundary := by
  have leftContextBelow := Context.applyFree_initialSupply_le_of_localized
    (left.localized_of_absorbing leftAbsorbing) context boundary
    contextBelow generatedBelow
  have rightContextBelow := Context.applyFree_initialSupply_le_of_localized
    (right.localized_of_absorbing rightAbsorbing) context boundary
    contextBelow generatedBelow
  have leftTargetBelow :=
    TypePM.Source.PrincipalBlockClosure.target_support_below
      left leftAbsorbing boundary generatedBelow
  have rightTargetBelow :=
    TypePM.Source.PrincipalBlockClosure.target_support_below
      right rightAbsorbing boundary generatedBelow
  apply ofSameGeneratedBoundedSupport transport leftAbsorbing rightAbsorbing
    context boundary
  · intro index member
    rcases ClosureSupportConstruction.tySource_origin transport context member with
      contextMember | targetMember
    · exact Nat.lt_of_lt_of_le
        (Context.freeTy_index_lt_initialSupply contextMember) leftContextBelow.1
    · exact leftTargetBelow (.ty index)
        ((Ty.mem_tyVars_iff_unificationVars index left.target).mp targetMember)
  · intro index member
    rcases ClosureSupportConstruction.tyTarget_origin transport context member with
      contextMember | targetMember
    · exact Nat.lt_of_lt_of_le
        (Context.freeTy_index_lt_initialSupply contextMember) rightContextBelow.1
    · exact rightTargetBelow (.ty index)
        ((Ty.mem_tyVars_iff_unificationVars index right.target).mp targetMember)
  · intro index member
    rcases ClosureSupportConstruction.capSource_origin transport context member with
      contextMember | targetMember
    · exact Nat.lt_of_lt_of_le
        (Context.freeCap_index_lt_initialSupply contextMember) leftContextBelow.2
    · exact leftTargetBelow (.cap index)
        ((Ty.mem_capVars_iff_unificationVars index left.target).mp targetMember)
  · intro index member
    rcases ClosureSupportConstruction.capTarget_origin transport context member with
      contextMember | targetMember
    · exact Nat.lt_of_lt_of_le
        (Context.freeCap_index_lt_initialSupply contextMember) rightContextBelow.2
    · exact rightTargetBelow (.cap index)
        ((Ty.mem_capVars_iff_unificationVars index right.target).mp targetMember)

/-- Fully automatic same-generated source endpoint with provenance. -/
noncomputable def ofSameGeneratedSupportBelow
    {generated : Generated}
    (left right : PrincipalBlockClosure generated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (boundary : Supply)
    (contextBelow : context.initialSupply.Le boundary)
    (generatedBelow : ∀ candidate,
      candidate ∈ generated.unificationVars →
        candidate.Below boundary.ty boundary.cap) :
    ProvenancedFreshClosureAlignment left right context boundary := by
  let related := left.representativeTransport right
  let forward := Classical.choose related
  let remaining := Classical.choose_spec related
  let backward := Classical.choose remaining
  have transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward := Classical.choose_spec remaining
  exact ofTransportGeneratedSupportBelow transport leftAbsorbing rightAbsorbing
    context boundary contextBelow generatedBelow

end ProvenancedFreshClosureAlignment

end TypePM.Source
