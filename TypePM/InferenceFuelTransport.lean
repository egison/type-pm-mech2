import TypePM.UnificationFuelTransport
import TypePM.InferenceProcedure

/-!
# Successful-solver transport for executable inference

The saturation schedule is independent of the implementation of unification.
Consequently, if every successful result of one solver is reproduced exactly
by another solver, every successful inference run is reproduced as well.
-/

namespace TypePM

theorem saturateLoop_success_transport
    {solveFrom solveTo : List Equation → Option Subst}
    (transport : ∀ {equations substitution},
      solveFrom equations = some substitution →
        solveTo equations = some substitution) :
    ∀ {fuel hard pending output},
      saturateLoop solveFrom fuel hard pending = some output →
        saturateLoop solveTo fuel hard pending = some output := by
  intro fuel
  induction fuel with
  | zero =>
      intro hard pending output success
      simp [saturateLoop] at success
  | succ fuel induction =>
      intro hard pending output success
      simp only [saturateLoop] at success ⊢
      cases solved : solveFrom hard with
      | none => simp [solved] at success
      | some substitution =>
          have solvedTo := transport solved
          rw [solved] at success
          rw [solvedTo]
          cases promoted : (promoteUnder substitution pending).equations with
          | nil => simpa [promoted] using success
          | cons equation equations =>
              simpa [promoted] using
                induction (by simpa [promoted] using success)

theorem saturateUsing_success_transport
    {solveFrom solveTo : List Equation → Option Subst}
    (transport : ∀ {equations substitution},
      solveFrom equations = some substitution →
        solveTo equations = some substitution)
    {hard pending output}
    (success : saturateUsing solveFrom hard pending = some output) :
    saturateUsing solveTo hard pending = some output := by
  exact saturateLoop_success_transport transport success

theorem inferGeneratedUsing_success_transport
    {solveFrom solveTo : List Equation → Option Subst}
    (transport : ∀ {equations substitution},
      solveFrom equations = some substitution →
        solveTo equations = some substitution)
    {generated result}
    (success : inferGeneratedUsing solveFrom generated = some result) :
    inferGeneratedUsing solveTo generated = some result := by
  unfold inferGeneratedUsing at success ⊢
  cases saturatedResult : saturateUsing solveFrom generated.hard
      generated.pending with
  | none => simp [saturatedResult] at success
  | some saturated =>
      have saturatedTo := saturateUsing_success_transport transport saturatedResult
      rw [saturatedResult] at success
      rw [saturatedTo]
      cases residualResult : solveFrom
          (residualEquations saturated.substitution saturated.pending) with
      | none => simp [residualResult] at success
      | some residual =>
          have residualTo := transport residualResult
          simpa [residualResult, residualTo] using success

theorem inferGeneratedUsing_unify_of_fuel_success
    {solverFuel : Nat} {generated result}
    (success : inferGeneratedUsing (unifyWithFuel solverFuel) generated =
      some result) :
    inferGeneratedUsing unify generated = some result :=
  inferGeneratedUsing_success_transport unify_eq_of_unifyWithFuel_success
    success

end TypePM
