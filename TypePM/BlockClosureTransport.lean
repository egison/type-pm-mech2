import TypePM.AbsorbingBlockClosure
import TypePM.SchemeTransport

/-!
# Transport between principal block-closure representatives

Two declarative closures of one generated block can choose different names
for the same principal solution.  The witnesses below expose both
factorizations and record their exact action on the result type and a source
context.  They are the algebraic input to nested-`let` completeness.
-/

namespace TypePM

namespace PrincipalBlockClosure

/-- A fixed pair of substitutions relates two closure representatives in
both directions. -/
def RepresentativeTransportUsing {generated : Generated}
    (left right : PrincipalBlockClosure generated)
    (forward backward : Subst) : Prop :=
  Subst.compose forward left.substitution = right.substitution ∧
    Subst.compose backward right.substitution = left.substitution

/-- There are substitutions relating two closure representatives in both
directions. -/
def RepresentativesRelated {generated : Generated}
    (left right : PrincipalBlockClosure generated) : Prop :=
  ∃ forward backward, RepresentativeTransportUsing left right forward backward

theorem representativeTransport {generated : Generated}
    (left right : PrincipalBlockClosure generated) :
    RepresentativesRelated left right := by
  obtain ⟨⟨forward, forwardFactor⟩, ⟨backward, backwardFactor⟩⟩ :=
    left.substitutions_mutualFactors right
  exact ⟨forward, backward, forwardFactor.symm, backwardFactor.symm⟩

namespace RepresentativeTransportUsing

theorem target_forward {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : RepresentativeTransportUsing left right forward backward) :
    left.target.apply forward = right.target := by
  simp only [PrincipalBlockClosure.target, Ty.apply_compose]
  rw [transport.1]

theorem target_backward {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : RepresentativeTransportUsing left right forward backward) :
    right.target.apply backward = left.target := by
  simp only [PrincipalBlockClosure.target, Ty.apply_compose]
  rw [transport.2]

theorem target_roundtrip_left {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : RepresentativeTransportUsing left right forward backward) :
    (left.target.apply forward).apply backward =
      left.target := by
  rw [transport.target_forward, transport.target_backward]

theorem target_roundtrip_right {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : RepresentativeTransportUsing left right forward backward) :
    (right.target.apply backward).apply forward =
      right.target := by
  rw [transport.target_backward, transport.target_forward]

theorem context_forward {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : RepresentativeTransportUsing left right forward backward)
    (context : Source.Context) :
    (context.applyFree left.substitution).applyFree forward =
      context.applyFree right.substitution := by
  rw [Source.Context.applyFree_compose, transport.1]

theorem context_backward {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : RepresentativeTransportUsing left right forward backward)
    (context : Source.Context) :
    (context.applyFree right.substitution).applyFree backward =
      context.applyFree left.substitution := by
  rw [Source.Context.applyFree_compose, transport.2]

theorem schemeInstantiation_forward {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (_transport : RepresentativeTransportUsing left right forward backward)
    {scheme : Source.Scheme} {target : Ty}
    (instantiation : scheme.Instantiates target) :
    (scheme.applyFree forward).Instantiates
      (target.apply forward) :=
  instantiation.applyFree forward

end RepresentativeTransportUsing

end PrincipalBlockClosure

end TypePM
