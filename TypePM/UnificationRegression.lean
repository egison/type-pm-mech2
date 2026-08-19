import TypePM.UnificationTermination

/-!
# Regressions for the total executable unifier

These examples exercise the public `unify` function.  Successful results are
specified semantically--by solving the worklist and by most-general
factorization--rather than by requiring one particular representation of a
substitution.
-/

namespace TypePM
namespace UnificationRegression

theorem solves_iff_of_equation_perm
    {left right : List Equation} (permutation : left.Perm right)
    (substitution : Subst) :
    Solves substitution left ↔ Solves substitution right := by
  constructor
  · intro solved equation member
    exact solved equation (permutation.mem_iff.mpr member)
  · intro solved equation member
    exact solved equation (permutation.mem_iff.mp member)

def capIndex : CapVar := ⟨0⟩
def tyIndex : TyVar := ⟨0⟩

def capOccursEquations : List Equation :=
  [.cap (.var capIndex) (.prod [.var capIndex])]

def tyOccursEquations : List Equation :=
  [.ty (.var tyIndex) (.fn (.var tyIndex) .int)]

/-- The capability occurs check rejects `κ = Prod[κ]`. -/
theorem cap_occurs_rejected :
    unify capOccursEquations = none := by
  apply (unify_none_iff_unsatisfiable capOccursEquations).mpr
  rintro ⟨solution, solved⟩
  have head := (solves_cons solution
    (.cap (.var capIndex) (.prod [.var capIndex])) []).mp solved |>.1
  have equality :
      solution.cap capIndex =
        (Cap.prod [.var capIndex]).apply solution.cap := by
    simpa [Equation.Holds, Cap.apply] using head
  exact Cap.occurs_equation_impossible solution.cap capIndex
    (.prod [.var capIndex]) (by rfl)
    (by intro impossible; cases impossible) equality

/-- The ordinary-type occurs check rejects `α = α → Int`. -/
theorem ty_occurs_rejected :
    unify tyOccursEquations = none := by
  apply (unify_none_iff_unsatisfiable tyOccursEquations).mpr
  rintro ⟨solution, solved⟩
  have head := (solves_cons solution
    (.ty (.var tyIndex) (.fn (.var tyIndex) .int)) []).mp solved |>.1
  have equality :
      solution.ty tyIndex =
        (Ty.fn (.var tyIndex) .int).apply solution := by
    simpa [Equation.Holds, Ty.apply] using head
  exact Ty.occurs_equation_impossible solution tyIndex
    (.fn (.var tyIndex) .int) (by rfl)
    (by intro impossible; cases impossible) equality

def concreteCapability : Cap := .prod [.any]

def capabilityEquation : Equation :=
  .cap (.var capIndex) concreteCapability

def targetEquation : Equation :=
  .ty (.var tyIndex) (.slot (.var capIndex) .int)

def capabilityFirst : List Equation :=
  [capabilityEquation, targetEquation]

def targetFirst : List Equation :=
  [targetEquation, capabilityEquation]

def concreteSolution : Subst :=
  Subst.compose
    (Subst.singleCap capIndex concreteCapability)
    (Subst.singleTy tyIndex (.slot (.var capIndex) .int))

theorem concreteSolution_solves_capabilityFirst :
    Solves concreteSolution capabilityFirst := by
  simp [Solves, capabilityFirst, capabilityEquation, targetEquation,
    concreteSolution, concreteCapability, Equation.Holds, Subst.compose,
    Subst.singleCap, Subst.singleTy, Cap.apply, Cap.applyList, Ty.apply]

theorem capabilityFirst_perm_targetFirst :
    capabilityFirst.Perm targetFirst := by
  exact List.Perm.swap targetEquation capabilityEquation []

theorem concreteSolution_solves_targetFirst :
    Solves concreteSolution targetFirst :=
  (solves_iff_of_equation_perm capabilityFirst_perm_targetFirst
    concreteSolution).mp
    concreteSolution_solves_capabilityFirst

/-- Any solution of the two equations reflects the capability binding inside
the image of the ordinary type variable. -/
theorem capability_binding_reflected
    {solution : Subst}
    (capabilityHolds : capabilityEquation.Holds solution)
    (targetHolds : targetEquation.Holds solution) :
    (Ty.var tyIndex).apply solution =
      .slot concreteCapability .int := by
  have capabilityEquality :
      solution.cap capIndex = concreteCapability := by
    simpa [capabilityEquation, Equation.Holds, Cap.apply,
      concreteCapability, Cap.applyList] using capabilityHolds
  have targetEquality :
      solution.ty tyIndex = .slot (solution.cap capIndex) .int := by
    simpa [targetEquation, Equation.Holds, Ty.apply, Cap.apply] using targetHolds
  calc
    (Ty.var tyIndex).apply solution = solution.ty tyIndex := rfl
    _ = .slot (solution.cap capIndex) .int := targetEquality
    _ = .slot concreteCapability .int := by rw [capabilityEquality]

/-- Binding the capability first succeeds; the returned result is sound and
most general, and its type image contains the propagated capability. -/
theorem capability_first_accepts_sound_and_principal :
    ∃ result,
      unify capabilityFirst = some result ∧
        Solves result capabilityFirst ∧
          MostGeneral capabilityFirst result ∧
            (Ty.var tyIndex).apply result =
              .slot concreteCapability .int := by
  obtain ⟨result, success⟩ :=
    unify_complete ⟨concreteSolution,
      concreteSolution_solves_capabilityFirst⟩
  have solved := unify_sound success
  refine ⟨result, success, solved, unify_mostGeneral success, ?_⟩
  apply capability_binding_reflected
  · exact solved capabilityEquation (by simp [capabilityFirst])
  · exact solved targetEquation (by simp [capabilityFirst])

/-- Binding the ordinary type first also succeeds and later capability
composition is reflected inside that earlier type image. -/
theorem target_first_accepts_sound_and_principal :
    ∃ result,
      unify targetFirst = some result ∧
        Solves result targetFirst ∧
          MostGeneral targetFirst result ∧
            (Ty.var tyIndex).apply result =
              .slot concreteCapability .int := by
  obtain ⟨result, success⟩ :=
    unify_complete ⟨concreteSolution, concreteSolution_solves_targetFirst⟩
  have solved := unify_sound success
  refine ⟨result, success, solved, unify_mostGeneral success, ?_⟩
  apply capability_binding_reflected
  · exact solved capabilityEquation (by simp [targetFirst])
  · exact solved targetEquation (by simp [targetFirst])

/-- Acceptance of the total unifier is invariant under equation-list
permutation. -/
theorem unify_acceptance_iff_of_perm
    {left right : List Equation} (permutation : left.Perm right) :
    (∃ result, unify left = some result) ↔
      ∃ result, unify right = some result := by
  constructor
  · rintro ⟨result, success⟩
    have solvedRight : Solves result right :=
      (solves_iff_of_equation_perm permutation result).mp
        (unify_sound success)
    exact unify_complete ⟨result, solvedRight⟩
  · rintro ⟨result, success⟩
    have solvedLeft : Solves result left :=
      (solves_iff_of_equation_perm permutation result).mpr
        (unify_sound success)
    exact unify_complete ⟨result, solvedLeft⟩

theorem capabilityFirst_targetFirst_acceptance_equivalent :
    (∃ result, unify capabilityFirst = some result) ↔
      ∃ result, unify targetFirst = some result :=
  unify_acceptance_iff_of_perm capabilityFirst_perm_targetFirst

/-- Results computed from permuted worklists are semantically the same normal
form: each most-general substitution factors through the other. -/
theorem unify_results_mutually_factor_of_perm
    {left right : List Equation} (permutation : left.Perm right)
    {leftResult rightResult : Subst}
    (leftSuccess : unify left = some leftResult)
    (rightSuccess : unify right = some rightResult) :
    FactorsThrough leftResult rightResult ∧
      FactorsThrough rightResult leftResult := by
  have leftPrincipal := unify_mostGeneral leftSuccess
  have rightPrincipal := unify_mostGeneral rightSuccess
  constructor
  · exact leftPrincipal.2 rightResult
      ((solves_iff_of_equation_perm permutation rightResult).mpr
        rightPrincipal.1)
  · exact rightPrincipal.2 leftResult
      ((solves_iff_of_equation_perm permutation leftResult).mp
        leftPrincipal.1)

theorem capabilityFirst_targetFirst_results_semantically_equivalent
    {capabilityFirstResult targetFirstResult : Subst}
    (capabilityFirstSuccess :
      unify capabilityFirst = some capabilityFirstResult)
    (targetFirstSuccess : unify targetFirst = some targetFirstResult) :
    FactorsThrough capabilityFirstResult targetFirstResult ∧
      FactorsThrough targetFirstResult capabilityFirstResult :=
  unify_results_mutually_factor_of_perm capabilityFirst_perm_targetFirst
    capabilityFirstSuccess targetFirstSuccess

end UnificationRegression
end TypePM
