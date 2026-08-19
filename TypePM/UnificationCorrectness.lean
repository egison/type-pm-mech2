import TypePM.Unification

/-!
# Factorization of successful unification

This module proves the reverse semantic direction for every certified
worklist reduction.  Consequently, every successful fuel-bounded run returns
a most general solution.  Fuel exhaustion is still distinct from logical
failure; a total fuel bound and the corresponding failure-completeness theorem
belong to the subsequent termination layer.
-/

namespace TypePM

namespace Subst

/-- Extensional equality for the two function-valued substitution fields. -/
theorem eq_of_components {left right : Subst}
    (capability : ∀ index, left.cap index = right.cap index)
    (target : ∀ index, left.ty index = right.ty index) :
    left = right := by
  cases left with
  | mk leftCap leftTy =>
      cases right with
      | mk rightCap rightTy =>
          have capEquality : leftCap = rightCap := funext capability
          have tyEquality : leftTy = rightTy := funext target
          cases capEquality
          cases tyEquality
          rfl

@[simp] theorem compose_id_right (substitution : Subst) :
    Subst.compose substitution Subst.id = substitution := by
  cases substitution
  rfl

/-- Composition is associative in application order. -/
theorem compose_assoc (outer middle inner : Subst) :
    Subst.compose outer (Subst.compose middle inner) =
      Subst.compose (Subst.compose outer middle) inner := by
  apply eq_of_components
  · intro index
    exact Cap.apply_compose outer middle (inner.cap index)
  · intro index
    exact Ty.apply_compose outer middle (inner.ty index)

end Subst

/-- `specific` is obtained by applying a later substitution after `general`. -/
def FactorsThrough (general specific : Subst) : Prop :=
  ∃ later, specific = Subst.compose later general

/-- A solution through which every other solution factors. -/
def MostGeneral (equations : List Equation) (solution : Subst) : Prop :=
  Solves solution equations ∧
    ∀ specific, Solves specific equations → FactorsThrough solution specific

theorem capEquations_complete
    {left right : List Cap} {equations : List Equation}
    (paired : capEquations left right = some equations)
    {substitution : Subst}
    (equality : Cap.applyList substitution.cap left =
      Cap.applyList substitution.cap right) :
    Solves substitution equations := by
  induction left generalizing right equations with
  | nil =>
      cases right with
      | nil =>
          simp [capEquations] at paired
          subst equations
          exact solves_nil _
      | cons right rights => simp [capEquations] at paired
  | cons left lefts induction =>
      cases right with
      | nil => simp [capEquations] at paired
      | cons right rights =>
          simp only [capEquations] at paired
          cases pairedRest : capEquations lefts rights with
          | none => simp [pairedRest] at paired
          | some children =>
              simp [pairedRest] at paired
              subst equations
              simp only [Cap.applyList] at equality
              injection equality with head tail
              rw [solves_cons]
              exact ⟨by simpa [Equation.Holds] using head,
                induction pairedRest tail⟩

theorem tyEquations_complete
    {left right : List Ty} {equations : List Equation}
    (paired : tyEquations left right = some equations)
    {substitution : Subst}
    (equality : Ty.applyList substitution left =
      Ty.applyList substitution right) :
    Solves substitution equations := by
  induction left generalizing right equations with
  | nil =>
      cases right with
      | nil =>
          simp [tyEquations] at paired
          subst equations
          exact solves_nil _
      | cons right rights => simp [tyEquations] at paired
  | cons left lefts induction =>
      cases right with
      | nil => simp [tyEquations] at paired
      | cons right rights =>
          simp only [tyEquations] at paired
          cases pairedRest : tyEquations lefts rights with
          | none => simp [pairedRest] at paired
          | some children =>
              simp [pairedRest] at paired
              subst equations
              simp only [Ty.applyList] at equality
              injection equality with head tail
              rw [solves_cons]
              exact ⟨by simpa [Equation.Holds] using head,
                induction pairedRest tail⟩

private theorem compose_singleCap_of_equality
    (solution : Subst) (index : CapVar) (replacement : Cap)
    (equality : solution.cap index = replacement.apply solution.cap) :
    Subst.compose solution (Subst.singleCap index replacement) = solution := by
  apply Subst.eq_of_components
  · intro candidate
    by_cases same : candidate = index
    · subst candidate
      simpa [Subst.compose, Subst.singleCap] using equality.symm
    · simp [Subst.compose, Subst.singleCap, same, Cap.apply]
  · intro candidate
    rfl

private theorem compose_singleTy_of_equality
    (solution : Subst) (index : TyVar) (replacement : Ty)
    (equality : solution.ty index = replacement.apply solution) :
    Subst.compose solution (Subst.singleTy index replacement) = solution := by
  apply Subst.eq_of_components
  · intro candidate
    rfl
  · intro candidate
    by_cases same : candidate = index
    · subst candidate
      simpa [Subst.compose, Subst.singleTy] using equality.symm
    · simp [Subst.compose, Subst.singleTy, same, Ty.apply]

/-- Any input solution absorbs the elimination substitution produced by one
certified reduction. -/
theorem Reduces.absorbed
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining)
    {solution : Subst} (solved : Solves solution input) :
    Subst.compose solution first = solution := by
  cases reduction with
  | capAny => simp
  | capVarRefl => simp
  | capVarLeft =>
      obtain ⟨head, _⟩ := (solves_cons solution _ _).mp solved
      simp only [Equation.Holds, Cap.apply] at head
      exact compose_singleCap_of_equality solution _ _ head
  | capVarRight =>
      obtain ⟨head, _⟩ := (solves_cons solution _ _).mp solved
      simp only [Equation.Holds, Cap.apply] at head
      exact compose_singleCap_of_equality solution _ _ head.symm
  | capProd => simp
  | capCon => simp
  | tyVarRefl => simp
  | tyVarLeft =>
      obtain ⟨head, _⟩ := (solves_cons solution _ _).mp solved
      simp only [Equation.Holds, Ty.apply] at head
      exact compose_singleTy_of_equality solution _ _ head
  | tyVarRight =>
      obtain ⟨head, _⟩ := (solves_cons solution _ _).mp solved
      simp only [Equation.Holds, Ty.apply] at head
      exact compose_singleTy_of_equality solution _ _ head.symm
  | tyInt => simp
  | tyFn => simp
  | tyProd => simp
  | tyData => simp
  | tyMatcher => simp
  | tySlot => simp

/-- Every input solution factors through the first elimination. -/
theorem Reduces.factors_first
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining)
    {solution : Subst} (solved : Solves solution input) :
    FactorsThrough first solution := by
  exact ⟨solution, (reduction.absorbed solved).symm⟩

/-- The reverse direction of `Reduces.sound`: a worklist reduction loses no
solutions. -/
theorem Reduces.complete
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining)
    {solution : Subst} (solved : Solves solution input) :
    Solves solution remaining := by
  cases reduction with
  | capAny => exact (solves_cons solution _ _).mp solved |>.2
  | capVarRefl => exact (solves_cons solution _ _).mp solved |>.2
  | capVarLeft notOccurs =>
      obtain ⟨_, rest⟩ := (solves_cons solution _ _).mp solved
      apply (solves_map_apply solution _ _).mpr
      rw [compose_singleCap_of_equality solution _ _
        (by
          have head := (solves_cons solution _ _).mp solved |>.1
          simpa [Equation.Holds, Cap.apply] using head)]
      exact rest
  | capVarRight notOccurs =>
      obtain ⟨_, rest⟩ := (solves_cons solution _ _).mp solved
      apply (solves_map_apply solution _ _).mpr
      rw [compose_singleCap_of_equality solution _ _
        (by
          have head := (solves_cons solution _ _).mp solved |>.1
          simpa [Equation.Holds, Cap.apply] using head.symm)]
      exact rest
  | capProd paired =>
      obtain ⟨head, rest⟩ := (solves_cons solution _ _).mp solved
      apply (solves_append solution _ _).mpr
      refine ⟨capEquations_complete paired ?_, rest⟩
      simp only [Equation.Holds, Cap.apply] at head
      injection head
  | capCon paired =>
      obtain ⟨head, rest⟩ := (solves_cons solution _ _).mp solved
      apply (solves_append solution _ _).mpr
      refine ⟨capEquations_complete paired ?_, rest⟩
      simp only [Equation.Holds, Cap.apply] at head
      injection head
  | tyVarRefl => exact (solves_cons solution _ _).mp solved |>.2
  | tyVarLeft notOccurs =>
      obtain ⟨_, rest⟩ := (solves_cons solution _ _).mp solved
      apply (solves_map_apply solution _ _).mpr
      rw [compose_singleTy_of_equality solution _ _
        (by
          have head := (solves_cons solution _ _).mp solved |>.1
          simpa [Equation.Holds, Ty.apply] using head)]
      exact rest
  | tyVarRight notOccurs =>
      obtain ⟨_, rest⟩ := (solves_cons solution _ _).mp solved
      apply (solves_map_apply solution _ _).mpr
      rw [compose_singleTy_of_equality solution _ _
        (by
          have head := (solves_cons solution _ _).mp solved |>.1
          simpa [Equation.Holds, Ty.apply] using head.symm)]
      exact rest
  | tyInt => exact (solves_cons solution _ _).mp solved |>.2
  | tyFn =>
      obtain ⟨head, rest⟩ := (solves_cons solution _ _).mp solved
      simp only [Equation.Holds, Ty.apply] at head
      injection head with domain codomain
      rw [solves_cons, solves_cons]
      exact ⟨by simpa [Equation.Holds] using domain,
        by simpa [Equation.Holds] using codomain, rest⟩
  | tyProd paired =>
      obtain ⟨head, rest⟩ := (solves_cons solution _ _).mp solved
      apply (solves_append solution _ _).mpr
      refine ⟨tyEquations_complete paired ?_, rest⟩
      simp only [Equation.Holds, Ty.apply] at head
      injection head
  | tyData paired =>
      obtain ⟨head, rest⟩ := (solves_cons solution _ _).mp solved
      apply (solves_append solution _ _).mpr
      refine ⟨tyEquations_complete paired ?_, rest⟩
      simp only [Equation.Holds, Ty.apply] at head
      injection head
  | tyMatcher =>
      obtain ⟨head, rest⟩ := (solves_cons solution _ _).mp solved
      simp only [Equation.Holds, Ty.apply] at head
      injection head with capability target
      rw [solves_cons, solves_cons]
      exact ⟨by simpa [Equation.Holds] using capability,
        by simpa [Equation.Holds] using target, rest⟩
  | tySlot =>
      obtain ⟨head, rest⟩ := (solves_cons solution _ _).mp solved
      simp only [Equation.Holds, Ty.apply] at head
      injection head with capability target
      rw [solves_cons, solves_cons]
      exact ⟨by simpa [Equation.Holds] using capability,
        by simpa [Equation.Holds] using target, rest⟩

/-- Every successful fuel-bounded run returns a most general solution.  This
does not assert that a particular fuel value is sufficient. -/
theorem unifyWithFuel_mostGeneral
    {fuel : Nat} {equations : List Equation} {solution : Subst}
    (success : unifyWithFuel fuel equations = some solution) :
    MostGeneral equations solution := by
  refine ⟨unifyWithFuel_sound success, ?_⟩
  intro specific specificSolves
  induction fuel generalizing equations solution with
  | zero =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst solution
          exact ⟨specific, (Subst.compose_id_right specific).symm⟩
      | cons equation equations => simp [unifyWithFuel] at success
  | succ fuel induction =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst solution
          exact ⟨specific, (Subst.compose_id_right specific).symm⟩
      | cons equation equations =>
          simp only [unifyWithFuel] at success
          cases reduced : reduce (equation :: equations) with
          | none => simp_all
          | some reduction =>
              cases recursive : unifyWithFuel fuel reduction.equations with
              | none => simp_all
              | some later =>
                  simp_all only [Option.some.injEq]
                  subst solution
                  obtain ⟨post, factor⟩ :=
                    induction recursive
                      (reduction.valid.complete specificSolves)
                  refine ⟨post, ?_⟩
                  calc
                    specific = Subst.compose specific reduction.substitution :=
                      (reduction.valid.absorbed specificSolves).symm
                    _ = Subst.compose (Subst.compose post later)
                        reduction.substitution := by rw [← factor]
                    _ = Subst.compose post
                        (Subst.compose later reduction.substitution) :=
                      (Subst.compose_assoc post later
                        reduction.substitution).symm

end TypePM
