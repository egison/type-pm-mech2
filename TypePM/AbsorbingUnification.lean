import TypePM.UnificationTermination

/-!
# Absorbing principal unifiers

Factorization alone does not require the chosen representative of a most
general unifier to be idempotent.  The executable unifier constructed in this
development satisfies the stronger normalization property below: applying
its result before any solution has no further effect on that solution.

This property is needed at a let-generalization boundary.  It lets the
principal substitution be applied eagerly to the surrounding context without
changing any later solution of the same block.
-/

namespace TypePM

namespace Subst

@[simp] theorem compose_id_left (substitution : Subst) :
    Subst.compose Subst.id substitution = substitution := by
  apply Subst.eq_of_components
  · intro index
    exact Cap.apply_id (substitution.cap index)
  · intro index
    exact Ty.apply_id (substitution.ty index)

end Subst

/-- A principal solution that is absorbed by every solution of the same
equation worklist. -/
def AbsorbingPrincipal (equations : List Equation)
    (principal : Subst) : Prop :=
  MostGeneral equations principal ∧
    ∀ solution, Solves solution equations →
      Subst.compose solution principal = solution

namespace AbsorbingPrincipal

theorem mostGeneral {equations : List Equation} {principal : Subst}
    (absorbing : AbsorbingPrincipal equations principal) :
    MostGeneral equations principal :=
  absorbing.1

theorem solves {equations : List Equation} {principal : Subst}
    (absorbing : AbsorbingPrincipal equations principal) :
    Solves principal equations :=
  absorbing.1.1

theorem absorbs {equations : List Equation} {principal solution : Subst}
    (absorbing : AbsorbingPrincipal equations principal)
    (solved : Solves solution equations) :
    Subst.compose solution principal = solution :=
  absorbing.2 solution solved

/-- An absorbing principal solution is idempotent. -/
theorem idempotent {equations : List Equation} {principal : Subst}
    (absorbing : AbsorbingPrincipal equations principal) :
    Subst.compose principal principal = principal :=
  absorbing.absorbs absorbing.solves

/-- The only absorbing principal representative of the empty worklist is the
identity.  This rules out representative-dependent variable permutations at
an otherwise unconstrained generalization boundary. -/
theorem eq_id_of_empty {principal : Subst}
    (absorbing : AbsorbingPrincipal [] principal) :
    principal = Subst.id := by
  have absorbedIdentity := absorbing.absorbs (solves_nil Subst.id)
  simpa only [Subst.compose_id_left] using absorbedIdentity

end AbsorbingPrincipal

/-- The elementary substitution selected by one reduction fixes every
ordinary variable absent from the input worklist. -/
theorem Reduces.substitution_fixes_ty_of_not_mem
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining) (index : TyVar)
    (absent : .ty index ∉ unificationVars input) :
    first.ty index = .var index := by
  cases reduction <;>
    simp_all [unificationVars, Equation.unificationVars,
      Cap.unificationVars, Ty.unificationVars, Subst.singleCap,
      Subst.singleTy, Subst.id]

/-- The elementary substitution selected by one reduction fixes every
capability variable absent from the input worklist. -/
theorem Reduces.substitution_fixes_cap_of_not_mem
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining) (index : CapVar)
    (absent : .cap index ∉ unificationVars input) :
    first.cap index = .var index := by
  cases reduction <;>
    simp_all [unificationVars, Equation.unificationVars,
      Cap.unificationVars, Ty.unificationVars, Subst.singleCap,
      Subst.singleTy, Subst.id]

/-- A fuel-bounded run changes only variables occurring in its input
worklist.  Both variable sorts are covered by one local frame theorem. -/
theorem unifyWithFuel_fixes_unmentioned
    {fuel : Nat} {equations : List Equation} {principal : Subst}
    (success : unifyWithFuel fuel equations = some principal) :
    (∀ index, .ty index ∉ unificationVars equations →
      principal.ty index = .var index) ∧
    (∀ index, .cap index ∉ unificationVars equations →
      principal.cap index = .var index) := by
  induction fuel generalizing equations principal with
  | zero =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst principal
          exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      | cons equation equations => simp [unifyWithFuel] at success
  | succ fuel induction =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst principal
          exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      | cons equation equations =>
          simp only [unifyWithFuel] at success
          cases reduced : reduce (equation :: equations) with
          | none => simp_all
          | some reduction =>
              cases recursive :
                  unifyWithFuel fuel reduction.equations with
              | none => simp_all
              | some later =>
                  simp_all only [Option.some.injEq]
                  subst principal
                  have recursiveFrame := induction recursive
                  constructor
                  · intro index absent
                    have remainingAbsent :
                        .ty index ∉ unificationVars reduction.equations :=
                      fun member => absent
                        (reduction.valid.unificationVars_subset _ member)
                    have firstFixed :=
                      reduction.valid.substitution_fixes_ty_of_not_mem
                        index absent
                    have laterFixed := recursiveFrame.1 index remainingAbsent
                    simp [Subst.compose, firstFixed, laterFixed, Ty.apply]
                  · intro index absent
                    have remainingAbsent :
                        .cap index ∉ unificationVars reduction.equations :=
                      fun member => absent
                        (reduction.valid.unificationVars_subset _ member)
                    have firstFixed :=
                      reduction.valid.substitution_fixes_cap_of_not_mem
                        index absent
                    have laterFixed := recursiveFrame.2 index remainingAbsent
                    simp [Subst.compose, firstFixed, laterFixed, Cap.apply]

/-- Every solution absorbs the result of a successful fuel-bounded
unification run. -/
theorem unifyWithFuel_absorbed
    {fuel : Nat} {equations : List Equation} {principal solution : Subst}
    (success : unifyWithFuel fuel equations = some principal)
    (solved : Solves solution equations) :
    Subst.compose solution principal = solution := by
  induction fuel generalizing equations principal with
  | zero =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst principal
          exact Subst.compose_id_right solution
      | cons equation equations => simp [unifyWithFuel] at success
  | succ fuel induction =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst principal
          exact Subst.compose_id_right solution
      | cons equation equations =>
          simp only [unifyWithFuel] at success
          cases reduced : reduce (equation :: equations) with
          | none => simp_all
          | some reduction =>
              cases recursive :
                  unifyWithFuel fuel reduction.equations with
              | none => simp_all
              | some later =>
                  simp_all only [Option.some.injEq]
                  subst principal
                  have remainingSolved :
                      Solves solution reduction.equations :=
                    reduction.valid.complete solved
                  have laterAbsorbed :
                      Subst.compose solution later = solution :=
                    induction recursive remainingSolved
                  calc
                    Subst.compose solution
                        (Subst.compose later reduction.substitution) =
                        Subst.compose
                          (Subst.compose solution later)
                          reduction.substitution :=
                      Subst.compose_assoc solution later
                        reduction.substitution
                    _ = Subst.compose solution reduction.substitution := by
                      rw [laterAbsorbed]
                    _ = solution :=
                      reduction.valid.absorbed solved

/-- A successful fuel-bounded run returns an absorbing principal solution. -/
theorem unifyWithFuel_absorbingPrincipal
    {fuel : Nat} {equations : List Equation} {principal : Subst}
    (success : unifyWithFuel fuel equations = some principal) :
    AbsorbingPrincipal equations principal := by
  exact ⟨unifyWithFuel_mostGeneral success,
    fun solution solved => unifyWithFuel_absorbed success solved⟩

/-- A successful fuel-bounded run returns an idempotent substitution. -/
theorem unifyWithFuel_idempotent
    {fuel : Nat} {equations : List Equation} {principal : Subst}
    (success : unifyWithFuel fuel equations = some principal) :
    Subst.compose principal principal = principal :=
  (unifyWithFuel_absorbingPrincipal success).idempotent

/-- Every solution absorbs a successful result of the public total
unifier. -/
theorem unify_absorbed
    {equations : List Equation} {principal solution : Subst}
    (success : unify equations = some principal)
    (solved : Solves solution equations) :
    Subst.compose solution principal = solution := by
  change unifyLoop (unificationVars equations) (rawNodeCount equations)
    equations = some principal at success
  obtain ⟨fuel, fuelSuccess⟩ := unifyLoop_success_has_fuel success
  exact unifyWithFuel_absorbed fuelSuccess solved

/-- A successful result of the public total unifier is absorbing as well as
most general. -/
theorem unify_absorbingPrincipal
    {equations : List Equation} {principal : Subst}
    (success : unify equations = some principal) :
    AbsorbingPrincipal equations principal := by
  exact ⟨unify_mostGeneral success,
    fun solution solved => unify_absorbed success solved⟩

/-- The public total unifier changes only variables occurring in its input
worklist. -/
theorem unify_fixes_unmentioned
    {equations : List Equation} {principal : Subst}
    (success : unify equations = some principal) :
    (∀ index, .ty index ∉ unificationVars equations →
      principal.ty index = .var index) ∧
    (∀ index, .cap index ∉ unificationVars equations →
      principal.cap index = .var index) := by
  change unifyLoop (unificationVars equations) (rawNodeCount equations)
    equations = some principal at success
  obtain ⟨fuel, fuelSuccess⟩ := unifyLoop_success_has_fuel success
  exact unifyWithFuel_fixes_unmentioned fuelSuccess

/-- In particular, the public unifier always returns an idempotent
substitution. -/
theorem unify_idempotent
    {equations : List Equation} {principal : Subst}
    (success : unify equations = some principal) :
    Subst.compose principal principal = principal :=
  (unify_absorbingPrincipal success).idempotent

/-- Solver-level interface for procedures whose successful results are
absorbing principal solutions. -/
def AbsorbingMGUSolver
    (solve : List Equation → Option Subst) : Prop :=
  ∀ equations principal,
    solve equations = some principal →
      AbsorbingPrincipal equations principal

/-- The public unifier implements the absorbing solver interface. -/
theorem unify_absorbingMGUSolver : AbsorbingMGUSolver unify := by
  intro equations principal success
  exact unify_absorbingPrincipal success

end TypePM
