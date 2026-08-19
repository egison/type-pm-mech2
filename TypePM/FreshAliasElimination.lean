import TypePM.HardWorklistEquivalence
import TypePM.DeclarativeCoverage
import TypePM.SolverCertified

/-!
# Elimination of fresh alias equations

A fresh alias changes the full solution set because it determines one new
auxiliary variable.  Acceptance nevertheless remains unchanged after that
variable is projected away.  The theorems below establish the variable-to-
variable case needed by representative-sensitive interfaces when there are
no delayed checking obligations.  `bodyFixed` is the precise executable
freshness premise: eliminating the auxiliary variable leaves every body hard
equation literally unchanged.
-/

namespace TypePM

namespace FreshAliasElimination

def addTyAlias (fresh existing : TyVar) (body : Generated) : Generated :=
  { body with hard := .ty (.var fresh) (.var existing) :: body.hard }

def addCapAlias (fresh existing : CapVar) (body : Generated) : Generated :=
  { body with hard := .cap (.var fresh) (.var existing) :: body.hard }

private theorem blockAccepts_hardSolvable
    {generated : Generated} (accepts : BlockAccepts generated) :
    ∃ solution, Solves solution generated.hard := by
  rcases accepts with ⟨finalHard, finalPending, hardSubstitution,
    residualSubstitution, saturation, _residualSolved⟩
  let solution := Subst.compose residualSubstitution hardSubstitution
  have finalSolved : Solves solution finalHard :=
    solves_postcompose saturation.principal.1 residualSubstitution
  exact ⟨solution, fun equation membership =>
    finalSolved equation
      (saturation.closure.hard_mem_final equation membership)⟩

private theorem blockAccepts_of_hardSolvable_noPending
    {generated : Generated} (noPending : generated.pending = [])
    {solution : Subst} (solved : Solves solution generated.hard) :
    BlockAccepts generated := by
  cases generated with
  | mk target hard pending =>
      simp only at noPending
      subst pending
      obtain ⟨principal, success⟩ := unify_complete ⟨solution, solved⟩
      refine ⟨hard, [], principal, Subst.id, ?_, ?_⟩
      · exact
          { closure := .refl
            principal := unify_mostGeneral success
            stable := by simp [promoteUnder] }
      · simp [residualEquations]

theorem tyAlias_hardSolvable_iff
    (body : Generated) (fresh existing : TyVar)
    (bodyFixed :
      body.hard.map (Equation.apply
        (Subst.singleTy fresh (.var existing))) = body.hard) :
    (∃ solution, Solves solution (addTyAlias fresh existing body).hard) ↔
      ∃ solution, Solves solution body.hard := by
  constructor
  · rintro ⟨solution, solved⟩
    exact ⟨solution, (solves_cons solution _ _).mp solved |>.2⟩
  · rintro ⟨solution, solved⟩
    let alias := Subst.singleTy fresh (.var existing)
    let extended := Subst.compose solution alias
    have aliasSolved :
        (Equation.ty (.var fresh) (.var existing)).Holds extended := by
      simp [extended, alias, Equation.Holds, Subst.compose,
        Subst.singleTy, Ty.apply]
    have normalizedSolved :
        Solves solution
          (body.hard.map (Equation.apply alias)) := by
      simpa [alias, bodyFixed] using solved
    have bodySolved : Solves extended body.hard :=
      (solves_map_apply solution alias body.hard).mp normalizedSolved
    exact ⟨extended, by
      change Solves extended
        (Equation.ty (.var fresh) (.var existing) :: body.hard)
      exact (solves_cons extended _ _).mpr ⟨aliasSolved, bodySolved⟩⟩

/-- Adding or removing a fresh ordinary-variable alias preserves acceptance
for a block without delayed checking obligations. -/
theorem blockAccepts_addTyAlias_iff_of_noPending
    (body : Generated) (fresh existing : TyVar)
    (noPending : body.pending = [])
    (bodyFixed :
      body.hard.map (Equation.apply
        (Subst.singleTy fresh (.var existing))) = body.hard) :
    BlockAccepts (addTyAlias fresh existing body) ↔ BlockAccepts body := by
  constructor
  · intro accepts
    obtain ⟨solution, solved⟩ :=
      (tyAlias_hardSolvable_iff body fresh existing bodyFixed).mp
        (blockAccepts_hardSolvable accepts)
    exact blockAccepts_of_hardSolvable_noPending
      (solution := solution) noPending solved
  · intro accepts
    obtain ⟨solution, solved⟩ :=
      (tyAlias_hardSolvable_iff body fresh existing bodyFixed).mpr
        (blockAccepts_hardSolvable accepts)
    exact blockAccepts_of_hardSolvable_noPending
      (solution := solution)
      (by simpa [addTyAlias] using noPending) solved

theorem capAlias_hardSolvable_iff
    (body : Generated) (fresh existing : CapVar)
    (bodyFixed :
      body.hard.map (Equation.apply
        (Subst.singleCap fresh (.var existing))) = body.hard) :
    (∃ solution, Solves solution (addCapAlias fresh existing body).hard) ↔
      ∃ solution, Solves solution body.hard := by
  constructor
  · rintro ⟨solution, solved⟩
    exact ⟨solution, (solves_cons solution _ _).mp solved |>.2⟩
  · rintro ⟨solution, solved⟩
    let alias := Subst.singleCap fresh (.var existing)
    let extended := Subst.compose solution alias
    have aliasSolved :
        (Equation.cap (.var fresh) (.var existing)).Holds extended := by
      simp [extended, alias, Equation.Holds, Subst.compose,
        Subst.singleCap, Cap.apply]
    have normalizedSolved :
        Solves solution
          (body.hard.map (Equation.apply alias)) := by
      simpa [alias, bodyFixed] using solved
    have bodySolved : Solves extended body.hard :=
      (solves_map_apply solution alias body.hard).mp normalizedSolved
    exact ⟨extended, by
      change Solves extended
        (Equation.cap (.var fresh) (.var existing) :: body.hard)
      exact (solves_cons extended _ _).mpr ⟨aliasSolved, bodySolved⟩⟩

/-- Capability-variable counterpart of
`blockAccepts_addTyAlias_iff_of_noPending`. -/
theorem blockAccepts_addCapAlias_iff_of_noPending
    (body : Generated) (fresh existing : CapVar)
    (noPending : body.pending = [])
    (bodyFixed :
      body.hard.map (Equation.apply
        (Subst.singleCap fresh (.var existing))) = body.hard) :
    BlockAccepts (addCapAlias fresh existing body) ↔ BlockAccepts body := by
  constructor
  · intro accepts
    obtain ⟨solution, solved⟩ :=
      (capAlias_hardSolvable_iff body fresh existing bodyFixed).mp
        (blockAccepts_hardSolvable accepts)
    exact blockAccepts_of_hardSolvable_noPending
      (solution := solution) noPending solved
  · intro accepts
    obtain ⟨solution, solved⟩ :=
      (capAlias_hardSolvable_iff body fresh existing bodyFixed).mpr
        (blockAccepts_hardSolvable accepts)
    exact blockAccepts_of_hardSolvable_noPending
      (solution := solution)
      (by simpa [addCapAlias] using noPending) solved

end FreshAliasElimination

end TypePM
