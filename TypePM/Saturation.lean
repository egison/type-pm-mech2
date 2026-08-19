import TypePM.ConversionPotential
import TypePM.UnificationCorrectness

/-!
# Declarative hard-constraint saturation

An obligation is promoted to an ordinary type equality only when its
hard-normalized source and expected types cannot expose a special matcher
conversion under any later substitution.  Every round classifies all current
obligations using the same most general hard solution.

This module defines the saturation relation independently of an executable
solver.  A later module proves that the executable procedure decides it.
-/

namespace TypePM

namespace CheckObligation

def apply (substitution : Subst) (obligation : CheckObligation) :
    CheckObligation :=
  { source := obligation.source.apply substitution
    expected := obligation.expected.apply substitution }

def forcedOrdinaryUnder (substitution : Subst)
    (obligation : CheckObligation) : Prop :=
  ForcedOrdinary
    (obligation.source.apply substitution)
    (obligation.expected.apply substitution)

def resolutionUnder (substitution : Subst)
    (obligation : CheckObligation) :
    Resolution (obligation.source.apply substitution)
      (obligation.expected.apply substitution) :=
  resolve (obligation.source.apply substitution)
    (obligation.expected.apply substitution)

def residualEquations (substitution : Subst)
    (obligation : CheckObligation) : List Equation :=
  (obligation.resolutionUnder substitution).equations

end CheckObligation

/-- Result of one simultaneous promotion pass. -/
structure Promotion where
  equations : List Equation
  pending : List CheckObligation

/-- Promote exactly the obligations that are already forced to use ordinary
equality.  Potentially special obligations remain pending for the next hard
solution. -/
def promoteUnder (substitution : Subst) :
    List CheckObligation → Promotion
  | [] => ⟨[], []⟩
  | obligation :: obligations =>
      let rest := promoteUnder substitution obligations
      if (obligation.source.apply substitution).couldSpecial
          (obligation.expected.apply substitution) then
        ⟨rest.equations, obligation :: rest.pending⟩
      else
        ⟨.ty obligation.source obligation.expected :: rest.equations,
          rest.pending⟩

theorem promoteUnder_pending_length_le
    (substitution : Subst) (obligations : List CheckObligation) :
    (promoteUnder substitution obligations).pending.length ≤
      obligations.length := by
  induction obligations with
  | nil => simp [promoteUnder]
  | cons obligation obligations induction =>
      by_cases possible :
          (obligation.source.apply substitution).couldSpecial
            (obligation.expected.apply substitution) = true
      · simpa [promoteUnder, possible] using Nat.succ_le_succ induction
      · exact Nat.le_trans
          (by simpa [promoteUnder, possible] using induction)
          (Nat.le_succ _)

/-- A pass that emits an equality strictly decreases the number of delayed
obligations. -/
theorem promoteUnder_pending_length_lt
    (substitution : Subst) (obligations : List CheckObligation)
    (progress : (promoteUnder substitution obligations).equations ≠ []) :
    (promoteUnder substitution obligations).pending.length <
      obligations.length := by
  induction obligations with
  | nil => simp [promoteUnder] at progress
  | cons obligation obligations induction =>
      by_cases possible :
          (obligation.source.apply substitution).couldSpecial
            (obligation.expected.apply substitution) = true
      · have tailProgress :
            (promoteUnder substitution obligations).equations ≠ [] := by
          simpa [promoteUnder, possible] using progress
        exact (by
          simpa [promoteUnder, possible] using
            Nat.succ_lt_succ (induction tailProgress))
      · have bound := promoteUnder_pending_length_le substitution obligations
        simpa [promoteUnder, possible] using Nat.lt_succ_of_le bound

/-- Reflexive-transitive closure of promotion rounds.  Each proper step is
justified by a most general solution of the current hard equations. -/
inductive PromotionClosure :
    List Equation → List CheckObligation →
    List Equation → List CheckObligation → Prop where
  | refl {hard pending} :
      PromotionClosure hard pending hard pending
  | step {hard pending substitution promoted finalHard finalPending} :
      MostGeneral hard substitution →
      promoteUnder substitution pending = promoted →
      promoted.equations ≠ [] →
      PromotionClosure (hard ++ promoted.equations) promoted.pending
        finalHard finalPending →
      PromotionClosure hard pending finalHard finalPending

/-- A saturated block consists of a finite promotion closure and a final most
general hard solution under which no further obligation is forced ordinary. -/
structure Saturated
    (hard : List Equation) (pending : List CheckObligation)
    (finalHard : List Equation) (finalPending : List CheckObligation)
    (substitution : Subst) : Prop where
  closure : PromotionClosure hard pending finalHard finalPending
  principal : MostGeneral finalHard substitution
  stable : (promoteUnder substitution finalPending).equations = []

/-- Residual equalities emitted after every remaining branch has been fixed by
the same saturated hard substitution. -/
def residualEquations (substitution : Subst) :
    List CheckObligation → List Equation
  | [] => []
  | obligation :: obligations =>
      obligation.residualEquations substitution ++
        residualEquations substitution obligations

/-- Solving all residual equations simultaneously gives a checking conversion
for every remaining obligation. -/
theorem residualEquations_sound
    {hardSubstitution residualSubstitution : Subst}
    {obligations : List CheckObligation}
    (solved : Solves residualSubstitution
      (residualEquations hardSubstitution obligations)) :
    ∀ obligation ∈ obligations,
      ∃ conversionClass,
        CheckConversion conversionClass
          ((obligation.source.apply hardSubstitution).apply
            residualSubstitution)
          ((obligation.expected.apply hardSubstitution).apply
            residualSubstitution) := by
  induction obligations with
  | nil => simp
  | cons head tail induction =>
      simp only [residualEquations] at solved
      obtain ⟨headSolved, tailSolved⟩ :=
        (solves_append residualSubstitution _ _).mp solved
      intro obligation membership
      simp only [List.mem_cons] at membership
      rcases membership with rfl | membership
      · let resolution :=
          CheckObligation.resolutionUnder hardSubstitution obligation
        exact ⟨resolution.conversionClass, resolution.sound headSolved⟩
      · exact induction tailSolved obligation membership

end TypePM
