import TypePM.Saturation

/-!
# Executable saturation skeleton

The procedure is parameterized by a hard-equation solver.  It promotes all
currently forced ordinary checks at once and therefore never lets the result
of one special conversion reclassify a sibling obligation.  The public
inference module later instantiates the parameter with the total MGU solver.
-/

namespace TypePM

/-- Computational output of hard-constraint saturation. -/
structure SaturationOutput where
  hard : List Equation
  pending : List CheckObligation
  substitution : Subst

def saturateLoop
    (solveHard : List Equation → Option Subst) :
    Nat → List Equation → List CheckObligation → Option SaturationOutput
  | 0, _, _ => none
  | fuel + 1, hard, pending => do
      let substitution ← solveHard hard
      let promoted := promoteUnder substitution pending
      match promoted.equations with
      | [] =>
          some ⟨hard, pending, substitution⟩
      | _ :: _ =>
          saturateLoop solveHard fuel
            (hard ++ promoted.equations) promoted.pending

/-- Every proper promotion removes at least one delayed obligation, so one
more round than the original pending length is sufficient independently of
the hard solver's internal implementation. -/
def saturateUsing
    (solveHard : List Equation → Option Subst)
    (hard : List Equation) (pending : List CheckObligation) :
    Option SaturationOutput :=
  saturateLoop solveHard (pending.length + 1) hard pending

theorem saturateLoop_sound
    (solveHard : List Equation → Option Subst)
    (solverPrincipal : ∀ equations substitution,
      solveHard equations = some substitution →
        MostGeneral equations substitution)
    {fuel : Nat} {hard : List Equation}
    {pending : List CheckObligation} {output : SaturationOutput}
    (success : saturateLoop solveHard fuel hard pending = some output) :
    Saturated hard pending output.hard output.pending output.substitution := by
  induction fuel generalizing hard pending output with
  | zero => simp [saturateLoop] at success
  | succ fuel induction =>
      simp only [saturateLoop] at success
      cases solved : solveHard hard with
      | none => simp [solved] at success
      | some substitution =>
          simp only [solved] at success
          let promoted := promoteUnder substitution pending
          change
            (match promoted.equations with
              | [] => some ⟨hard, pending, substitution⟩
              | _ :: _ => saturateLoop solveHard fuel
                  (hard ++ promoted.equations) promoted.pending) =
              some output at success
          cases equationsCase : promoted.equations with
          | nil =>
              rw [equationsCase] at success
              injection success with outputEquality
              subst output
              exact
                { closure := .refl
                  principal := solverPrincipal hard substitution solved
                  stable := by simpa [promoted] using equationsCase }
          | cons equation equations =>
              rw [equationsCase] at success
              have tail := induction success
              exact
                { closure := .step
                    (solverPrincipal hard substitution solved)
                    (by rfl)
                    (by simp [promoted, equationsCase])
                    (by simpa [promoted, equationsCase] using tail.closure)
                  principal := tail.principal
                  stable := tail.stable }

theorem saturateUsing_sound
    (solveHard : List Equation → Option Subst)
    (solverPrincipal : ∀ equations substitution,
      solveHard equations = some substitution →
        MostGeneral equations substitution)
    {hard : List Equation} {pending : List CheckObligation}
    {output : SaturationOutput}
    (success : saturateUsing solveHard hard pending = some output) :
    Saturated hard pending output.hard output.pending output.substitution :=
  saturateLoop_sound solveHard solverPrincipal success

end TypePM
