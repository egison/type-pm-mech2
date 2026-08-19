import TypePM.UnificationSupport
import TypePM.AbsorbingBlockClosure

/-!
# Finite support of generated blocks

The support of a generated block includes its result type, hard equations,
and both sides of every delayed checking obligation.
-/

namespace TypePM

namespace CheckObligation

/-- All two-sorted variables mentioned by a checking obligation. -/
def unificationVars (obligation : CheckObligation) :
    List UnificationVar :=
  obligation.source.unificationVars ++ obligation.expected.unificationVars

end CheckObligation

/-- Variables mentioned by a list of delayed checking obligations. -/
def pendingUnificationVars : List CheckObligation → List UnificationVar
  | [] => []
  | obligation :: obligations =>
      obligation.unificationVars ++ pendingUnificationVars obligations

namespace Generated

/-- The finite semantic support of one generated block. -/
def unificationVars (generated : Generated) : List UnificationVar :=
  generated.target.unificationVars ++
    TypePM.unificationVars generated.hard ++
      pendingUnificationVars generated.pending

end Generated

namespace PrincipalBlockClosure

/-- A principal closure is localized when its composed substitution fixes
variables outside the generated block and its images contain only variables
from that same finite support. -/
def Localized {generated : Generated}
    (closure : PrincipalBlockClosure generated) : Prop :=
  closure.substitution.Localized generated.unificationVars

end PrincipalBlockClosure

@[simp] theorem pendingUnificationVars_append
    (left right : List CheckObligation) :
    pendingUnificationVars (left ++ right) =
      pendingUnificationVars left ++ pendingUnificationVars right := by
  induction left with
  | nil => rfl
  | cons obligation obligations induction =>
      simp [pendingUnificationVars, induction, List.append_assoc]

theorem CheckObligation.mem_unificationVars_source
    (obligation : CheckObligation) {candidate : UnificationVar}
    (member : candidate ∈ obligation.source.unificationVars) :
    candidate ∈ obligation.unificationVars := by
  exact List.mem_append_left _ member

theorem CheckObligation.mem_unificationVars_expected
    (obligation : CheckObligation) {candidate : UnificationVar}
    (member : candidate ∈ obligation.expected.unificationVars) :
    candidate ∈ obligation.unificationVars := by
  exact List.mem_append_right _ member

theorem mem_pendingUnificationVars
    {obligations : List CheckObligation} {obligation : CheckObligation}
    (obligationMember : obligation ∈ obligations)
    {candidate : UnificationVar}
    (candidateMember : candidate ∈ obligation.unificationVars) :
    candidate ∈ pendingUnificationVars obligations := by
  induction obligations with
  | nil => simp at obligationMember
  | cons head tail induction =>
      simp only [List.mem_cons] at obligationMember
      simp only [pendingUnificationVars, List.mem_append]
      rcases obligationMember with rfl | tailMember
      · exact Or.inl candidateMember
      · exact Or.inr (induction tailMember)

end TypePM
