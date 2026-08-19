import TypePM.SaturationProcedureCompleteness

/-!
# Interface for a complete most-general unifier

The declarative typing relation quantifies over solutions.  Executable
inference instead needs one procedure that returns a most general solution
whenever the finite equation worklist is solvable.  `CompleteMGUSolver`
packages exactly those two directions without exposing an implementation.
-/

namespace TypePM

/-- A solver is certified when every returned substitution is most general
and every solvable worklist produces a result. -/
structure CompleteMGUSolver
    (solve : List Equation → Option Subst) : Prop where
  principal : ∀ equations substitution,
    solve equations = some substitution →
      MostGeneral equations substitution
  complete : ∀ equations,
    (∃ substitution, Solves substitution equations) →
      ∃ substitution, solve equations = some substitution

namespace CompleteMGUSolver

/-- Declarative hard saturation can always be replayed by a certified
solver. -/
theorem saturateUsing_complete
    {solve : List Equation → Option Subst}
    (solver : CompleteMGUSolver solve)
    {hard : List Equation} {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    {finalSubstitution : Subst}
    (saturation :
      Saturated hard pending finalHard finalPending finalSubstitution) :
    ∃ output, saturateUsing solve hard pending = some output := by
  apply TypePM.saturateUsing_complete solve solver.principal
  · intro equations hasMostGeneral
    obtain ⟨substitution, principal⟩ := hasMostGeneral
    exact solver.complete equations ⟨substitution, principal.1⟩
  · exact saturation

end CompleteMGUSolver

end TypePM
