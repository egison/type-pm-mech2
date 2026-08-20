import TypePM.AbsorbingUnification

/-!
# Transport from the structural unifier to the public unifier

`unifyWithFuel` follows the same deterministic reduction steps as `unify`.
The theorem in this module lets kernel-computed successful runs be reused as
exact facts about the total public unifier.
-/

namespace TypePM

/-- A successful structural-fuel run is reproduced exactly by the two-clock
public unifier whenever its clocks cover the current worklist. -/
theorem unifyLoop_eq_of_unifyWithFuel_success
    {fuel : Nat} {equations : List Equation} {result : Subst}
    (success : unifyWithFuel fuel equations = some result) :
    ∀ {available structuralFuel},
      VariablesCovered available equations →
      rawNodeCount equations ≤ structuralFuel →
      unifyLoop available structuralFuel equations = some result := by
  induction fuel generalizing equations result with
  | zero =>
      cases equations with
      | nil =>
          intro available structuralFuel covered bounded
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst result
          rw [unifyLoop.eq_def]
      | cons equation equations => simp [unifyWithFuel] at success
  | succ fuel induction =>
      cases equations with
      | nil =>
          intro available structuralFuel covered bounded
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst result
          rw [unifyLoop.eq_def]
      | cons equation equations =>
          simp only [unifyWithFuel] at success
          cases computed : reduce (equation :: equations) with
          | none => simp_all
          | some reduction =>
              cases recursive : unifyWithFuel fuel reduction.equations with
              | none => simp_all
              | some later =>
                  simp only [computed, recursive, Option.some.injEq] at success
                  subst result
                  intro available structuralFuel covered bounded
                  cases structuralFuel with
                  | zero =>
                      have positive := Equation.solvedNodeCount_pos Subst.id equation
                      simp only [rawNodeCount, solvedNodeCount] at bounded
                      omega
                  | succ structuralFuel =>
                      rw [unifyLoop.eq_def]
                      dsimp only
                      rw [computed]
                      cases classified : eliminatedVariable?
                          (equation :: equations) with
                      | some eliminated =>
                          have present : eliminated ∈ available :=
                            covered eliminated
                              (eliminatedVariable_mem_unificationVars classified)
                          have remainingCovered :
                              VariablesCovered (available.erase eliminated)
                                reduction.equations :=
                            reduction_variablesCovered_erase computed classified
                              covered
                          have recursivePublic := induction recursive
                            remainingCovered (Nat.le_refl _)
                          simp [present, recursivePublic]
                      | none =>
                          have remainingCovered :
                              VariablesCovered available reduction.equations :=
                            reduction.valid.variablesCovered covered
                          have decreases :
                              rawNodeCount reduction.equations <
                                rawNodeCount (equation :: equations) :=
                            reduction.valid.rawNodeCount_lt_of_no_elimination
                              classified
                          have remainingBounded :
                              rawNodeCount reduction.equations ≤ structuralFuel := by
                            omega
                          have recursivePublic := induction recursive
                            remainingCovered remainingBounded
                          simp [recursivePublic]

/-- Any successful kernel-computable unification run gives the exact result
of the public total unifier. -/
theorem unify_eq_of_unifyWithFuel_success
    {fuel : Nat} {equations : List Equation} {result : Subst}
    (success : unifyWithFuel fuel equations = some result) :
    unify equations = some result := by
  exact unifyLoop_eq_of_unifyWithFuel_success success
    (variablesCovered_initial equations) (Nat.le_refl _)

/-- Fixing a fuel amount gives an absorbing principal solver on every input
where that fuel-bounded solver succeeds. -/
theorem unifyWithFuel_absorbingMGUSolver (fuel : Nat) :
    AbsorbingMGUSolver (unifyWithFuel fuel) := by
  intro equations principal success
  exact unifyWithFuel_absorbingPrincipal success

end TypePM
