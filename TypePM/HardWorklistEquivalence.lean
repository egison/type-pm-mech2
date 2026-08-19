import TypePM.BlockOrderInvariance

/-!
# Semantic equivalence of hard worklists

Hard-equation lists are compared by their solution sets, rather than by
literal equation orientation or list order.  This is the appropriate boundary
for transporting saturation across representative-sensitive `let` interfaces.
-/

namespace TypePM

/-- Two hard worklists have exactly the same simultaneous solutions. -/
def HardEquivalent (left right : List Equation) : Prop :=
  ∀ substitution, Solves substitution left ↔ Solves substitution right

namespace Equation

/-- Reverse the two sides of one equation. -/
def swapSides : Equation → Equation
  | .cap left right => .cap right left
  | .ty left right => .ty right left

@[simp] theorem holds_swapSides
    (substitution : Subst) (equation : Equation) :
    equation.swapSides.Holds substitution ↔
      equation.Holds substitution := by
  cases equation <;> simp [swapSides, Equation.Holds, eq_comm]

end Equation

namespace HardEquivalent

theorem refl (equations : List Equation) :
    HardEquivalent equations equations :=
  fun _ => Iff.rfl

theorem symm {left right : List Equation}
    (equivalent : HardEquivalent left right) :
    HardEquivalent right left :=
  fun substitution => (equivalent substitution).symm

theorem trans {left middle right : List Equation}
    (first : HardEquivalent left middle)
    (second : HardEquivalent middle right) :
    HardEquivalent left right :=
  fun substitution => (first substitution).trans (second substitution)

/-- A permutation is a semantic hard-worklist equivalence. -/
theorem ofPerm {left right : List Equation}
    (permutation : left.Perm right) :
    HardEquivalent left right :=
  fun substitution => solves_iff_of_perm permutation substitution

/-- Semantic equivalence is a congruence for appending worklists. -/
theorem append {left₁ left₂ right₁ right₂ : List Equation}
    (leftEquivalent : HardEquivalent left₁ left₂)
    (rightEquivalent : HardEquivalent right₁ right₂) :
    HardEquivalent (left₁ ++ right₁) (left₂ ++ right₂) := by
  intro substitution
  simp only [solves_append]
  exact and_congr (leftEquivalent substitution) (rightEquivalent substitution)

theorem appendLeft {left right suffix : List Equation}
    (equivalent : HardEquivalent left right) :
    HardEquivalent (left ++ suffix) (right ++ suffix) :=
  equivalent.append (refl suffix)

theorem appendRight {initial left right : List Equation}
    (equivalent : HardEquivalent left right) :
    HardEquivalent (initial ++ left) (initial ++ right) :=
  (refl initial).append equivalent

/-- Reversing one equation does not change its solution set. -/
theorem singleton_swap (equation : Equation) :
    HardEquivalent [equation] [equation.swapSides] := by
  intro substitution
  simp only [solves_cons, solves_nil, and_true]
  exact (Equation.holds_swapSides substitution equation).symm

/-- Reversing an equation at the head of a worklist is harmless. -/
theorem cons_swap (equation : Equation) (equations : List Equation) :
    HardEquivalent (equation :: equations)
      (equation.swapSides :: equations) := by
  intro substitution
  simp only [solves_cons]
  exact and_congr
    (Equation.holds_swapSides substitution equation).symm Iff.rfl

/-- Most-generality depends only on the semantic solution set. -/
theorem mostGeneral_iff {left right : List Equation}
    (equivalent : HardEquivalent left right) (substitution : Subst) :
    MostGeneral left substitution ↔ MostGeneral right substitution := by
  constructor
  · intro principal
    refine ⟨(equivalent substitution).mp principal.1, ?_⟩
    intro specific solved
    exact principal.2 specific ((equivalent specific).mpr solved)
  · intro principal
    refine ⟨(equivalent substitution).mpr principal.1, ?_⟩
    intro specific solved
    exact principal.2 specific ((equivalent specific).mp solved)

end HardEquivalent


namespace PromotionClosure

/-- Transport a promotion closure after replacing its initial hard worklist
by a semantically equivalent one.  The final worklist may be literally
different, but remains semantically equivalent to the original final list. -/
theorem transportHard
    {left pending finalHard finalPending}
    (closure : PromotionClosure left pending finalHard finalPending)
    {right : List Equation}
    (equivalent : HardEquivalent left right) :
    ∃ transportedFinal,
      PromotionClosure right pending transportedFinal finalPending ∧
        HardEquivalent finalHard transportedFinal := by
  induction closure generalizing right with
  | @refl hard pending =>
      exact ⟨right, .refl, equivalent⟩
  | @step hard pending substitution promoted finalHard finalPending
      principal promotion progress tail induction =>
      have transportedPrincipal : MostGeneral right substitution :=
        (HardEquivalent.mostGeneral_iff equivalent substitution).mp principal
      have appended :
          HardEquivalent (hard ++ promoted.equations)
            (right ++ promoted.equations) :=
        equivalent.appendLeft
      obtain ⟨transportedFinal, transportedTail, finalEquivalent⟩ :=
        induction appended
      exact ⟨transportedFinal,
        .step transportedPrincipal promotion progress transportedTail,
        finalEquivalent⟩

end PromotionClosure


namespace Saturated

/-- Saturation exists across semantic replacement of the initial hard
worklist, using the same most-general substitutions and promotion decisions. -/
theorem transportHard
    {left pending finalHard finalPending substitution}
    (saturated : Saturated left pending finalHard finalPending substitution)
    {right : List Equation}
    (equivalent : HardEquivalent left right) :
    ∃ transportedFinal,
      Saturated right pending transportedFinal finalPending substitution ∧
        HardEquivalent finalHard transportedFinal := by
  obtain ⟨transportedFinal, transportedClosure, finalEquivalent⟩ :=
    saturated.closure.transportHard equivalent
  refine ⟨transportedFinal,
    { closure := transportedClosure
      principal :=
        (HardEquivalent.mostGeneral_iff finalEquivalent substitution).mp
          saturated.principal
      stable := saturated.stable },
    finalEquivalent⟩

end Saturated


namespace BlockAccepts

theorem transportHard
    {left right : Generated}
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingEqual : left.pending = right.pending)
    (accepts : BlockAccepts left) :
    BlockAccepts right := by
  rcases accepts with
    ⟨finalHard, finalPending, hardSubstitution, residualSubstitution,
      saturated, residualSolved⟩
  obtain ⟨transportedFinal, transportedSaturation, _finalEquivalent⟩ :=
    saturated.transportHard hardEquivalent
  change ∃ finalHard finalPending hardSubstitution residualSubstitution,
    Saturated right.hard right.pending finalHard finalPending
        hardSubstitution ∧
      Solves residualSubstitution
        (residualEquations hardSubstitution finalPending)
  rw [← pendingEqual]
  exact ⟨transportedFinal, finalPending, hardSubstitution,
    residualSubstitution, transportedSaturation, residualSolved⟩

/-- Generated blocks with the same delayed obligations and semantically
equivalent hard worklists are accepted simultaneously.  Their target fields
need not agree because `BlockAccepts` deliberately ignores result types. -/
theorem iff_of_hardEquivalent
    {left right : Generated}
    (hardEquivalent : HardEquivalent left.hard right.hard)
    (pendingEqual : left.pending = right.pending) :
    BlockAccepts left ↔ BlockAccepts right := by
  constructor
  · exact transportHard hardEquivalent pendingEqual
  · exact transportHard hardEquivalent.symm pendingEqual.symm

end BlockAccepts

end TypePM
