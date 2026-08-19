import TypePM.FreeVars
import TypePM.Substitution
import TypePM.Constraints

/-!
# Executable two-sort first-order unification core

Hard constraints may equate either capabilities or ordinary types.  The
worklist reducer performs an occurs check before eliminating a variable and
applies each elimination simultaneously to the remaining worklist.

`unifyWithFuel` is the executable M1 core.  Fuel exhaustion is deliberately
reported as failure; the separate totality/MGU development will replace the
fuel interface after proving a well-founded bound.  The theorem at the end of
this module already guarantees that every successful result solves the input
worklist.
-/

namespace TypePM

namespace Equation

def apply (substitution : Subst) : Equation → Equation
  | .cap left right =>
      .cap (left.apply substitution.cap) (right.apply substitution.cap)
  | .ty left right =>
      .ty (left.apply substitution) (right.apply substitution)

def Holds (substitution : Subst) : Equation → Prop
  | .cap left right =>
      left.apply substitution.cap = right.apply substitution.cap
  | .ty left right =>
      left.apply substitution = right.apply substitution

@[simp] theorem holds_apply
    (later earlier : Subst) (equation : Equation) :
    (equation.apply earlier).Holds later ↔
      equation.Holds (Subst.compose later earlier) := by
  cases equation <;> simp [Equation.apply, Equation.Holds]

end Equation

/-- Every equation in a worklist holds under one simultaneous substitution. -/
def Solves (substitution : Subst) (equations : List Equation) : Prop :=
  ∀ equation ∈ equations, equation.Holds substitution

@[simp] theorem solves_nil (substitution : Subst) :
    Solves substitution [] := by
  simp [Solves]

@[simp] theorem solves_cons
    (substitution : Subst) (equation : Equation) (equations : List Equation) :
    Solves substitution (equation :: equations) ↔
      equation.Holds substitution ∧ Solves substitution equations := by
  simp [Solves]

@[simp] theorem solves_append
    (substitution : Subst) (left right : List Equation) :
    Solves substitution (left ++ right) ↔
      Solves substitution left ∧ Solves substitution right := by
  simp [Solves, or_imp, forall_and]

theorem solves_map_apply
    (later earlier : Subst) (equations : List Equation) :
    Solves later (equations.map (Equation.apply earlier)) ↔
      Solves (Subst.compose later earlier) equations := by
  induction equations with
  | nil => simp
  | cons equation equations induction =>
      simp only [List.map_cons, solves_cons, Equation.holds_apply, induction]

mutual

theorem Cap.apply_singleCap_of_not_occurs
    (index : CapVar) (replacement capability : Cap)
    (notOccurs : capability.occurs index = false) :
    capability.apply (Subst.singleCap index replacement).cap = capability := by
  cases capability with
  | any => rfl
  | var candidate =>
      have different : candidate ≠ index := by
        simpa [Cap.occurs] using notOccurs
      simp [Cap.apply, Subst.singleCap, different]
  | prod items =>
      simp only [Cap.apply]
      exact congrArg Cap.prod
        (Cap.applyList_singleCap_of_not_occurs index replacement items notOccurs)

theorem Cap.applyList_singleCap_of_not_occurs
    (index : CapVar) (replacement : Cap) (items : List Cap)
    (notOccurs : Cap.occursList index items = false) :
    Cap.applyList (Subst.singleCap index replacement).cap items = items := by
  cases items with
  | nil => rfl
  | cons item items =>
      cases itemOccurs : item.occurs index <;>
        cases itemsOccur : Cap.occursList index items <;>
        simp_all [Cap.occursList, Cap.applyList,
          Cap.apply_singleCap_of_not_occurs,
          Cap.applyList_singleCap_of_not_occurs]

end

mutual

theorem Ty.apply_singleTy_of_not_occurs
    (index : TyVar) (replacement target : Ty)
    (notOccurs : target.occursTy index = false) :
    target.apply (Subst.singleTy index replacement) = target := by
  cases target with
  | var candidate =>
      have different : candidate ≠ index := by
        simpa [Ty.occursTy] using notOccurs
      simp [Ty.apply, Subst.singleTy, different]
  | int => rfl
  | fn domain codomain =>
      cases domainOccurs : domain.occursTy index <;>
        cases codomainOccurs : codomain.occursTy index <;>
        simp_all [Ty.occursTy, Ty.apply, Ty.apply_singleTy_of_not_occurs]
  | prod items =>
      simp only [Ty.apply]
      exact congrArg Ty.prod
        (Ty.applyList_singleTy_of_not_occurs index replacement items notOccurs)
  | matcher capability target =>
      simp only [Ty.apply]
      rw [show (Subst.singleTy index replacement).cap = Subst.id.cap by rfl,
        Cap.apply_id,
        Ty.apply_singleTy_of_not_occurs index replacement target notOccurs]
  | slot capability target =>
      simp only [Ty.apply]
      rw [show (Subst.singleTy index replacement).cap = Subst.id.cap by rfl,
        Cap.apply_id,
        Ty.apply_singleTy_of_not_occurs index replacement target notOccurs]

theorem Ty.applyList_singleTy_of_not_occurs
    (index : TyVar) (replacement : Ty) (items : List Ty)
    (notOccurs : Ty.occursTyList index items = false) :
    Ty.applyList (Subst.singleTy index replacement) items = items := by
  cases items with
  | nil => rfl
  | cons item items =>
      cases itemOccurs : item.occursTy index <;>
        cases itemsOccur : Ty.occursTyList index items <;>
        simp_all [Ty.occursTyList, Ty.applyList,
          Ty.apply_singleTy_of_not_occurs,
          Ty.applyList_singleTy_of_not_occurs]

end


/-- Pair equal-length capability lists into a worklist. -/
def capEquations : List Cap → List Cap → Option (List Equation)
  | [], [] => some []
  | left :: lefts, right :: rights => do
      let rest ← capEquations lefts rights
      pure (.cap left right :: rest)
  | _, _ => none

/-- Pair equal-length type lists into a worklist. -/
def tyEquations : List Ty → List Ty → Option (List Equation)
  | [], [] => some []
  | left :: lefts, right :: rights => do
      let rest ← tyEquations lefts rights
      pure (.ty left right :: rest)
  | _, _ => none

theorem capEquations_sound
    {left right : List Cap} {equations : List Equation}
    (paired : capEquations left right = some equations)
    {substitution : Subst} (solved : Solves substitution equations) :
    Cap.applyList substitution.cap left =
      Cap.applyList substitution.cap right := by
  induction left generalizing right equations with
  | nil =>
      cases right <;> simp [capEquations] at paired ⊢
  | cons left lefts induction =>
      cases right with
      | nil => simp [capEquations] at paired
      | cons right rights =>
          simp only [capEquations] at paired
          cases pairedRest : capEquations lefts rights <;> simp [pairedRest] at paired
          subst equations
          obtain ⟨head, tail⟩ := (solves_cons substitution
            (.cap left right) _).mp solved
          simp only [Equation.Holds] at head
          simp [Cap.applyList, head,
            induction pairedRest tail]

theorem tyEquations_sound
    {left right : List Ty} {equations : List Equation}
    (paired : tyEquations left right = some equations)
    {substitution : Subst} (solved : Solves substitution equations) :
    Ty.applyList substitution left = Ty.applyList substitution right := by
  induction left generalizing right equations with
  | nil =>
      cases right <;> simp [tyEquations] at paired ⊢
  | cons left lefts induction =>
      cases right with
      | nil => simp [tyEquations] at paired
      | cons right rights =>
          simp only [tyEquations] at paired
          cases pairedRest : tyEquations lefts rights <;> simp [pairedRest] at paired
          subst equations
          obtain ⟨head, tail⟩ := (solves_cons substitution
            (.ty left right) _).mp solved
          simp only [Equation.Holds] at head
          simp [Ty.applyList, head,
            induction pairedRest tail]

/-- One certified worklist reduction. -/
inductive Reduces : List Equation → Subst → List Equation → Prop where
  | capAny {rest} :
      Reduces (.cap .any .any :: rest) Subst.id rest
  | capVarRefl {index rest} :
      Reduces (.cap (.var index) (.var index) :: rest) Subst.id rest
  | capVarLeft {index replacement rest}
      (notOccurs : replacement.occurs index = false) :
      Reduces (.cap (.var index) replacement :: rest)
        (Subst.singleCap index replacement)
        (rest.map (Equation.apply (Subst.singleCap index replacement)))
  | capVarRight {index replacement rest}
      (notOccurs : replacement.occurs index = false) :
      Reduces (.cap replacement (.var index) :: rest)
        (Subst.singleCap index replacement)
        (rest.map (Equation.apply (Subst.singleCap index replacement)))
  | capProd {left right children rest}
      (paired : capEquations left right = some children) :
      Reduces (.cap (.prod left) (.prod right) :: rest)
        Subst.id (children ++ rest)
  | tyVarRefl {index rest} :
      Reduces (.ty (.var index) (.var index) :: rest) Subst.id rest
  | tyVarLeft {index replacement rest}
      (notOccurs : replacement.occursTy index = false) :
      Reduces (.ty (.var index) replacement :: rest)
        (Subst.singleTy index replacement)
        (rest.map (Equation.apply (Subst.singleTy index replacement)))
  | tyVarRight {index replacement rest}
      (notOccurs : replacement.occursTy index = false) :
      Reduces (.ty replacement (.var index) :: rest)
        (Subst.singleTy index replacement)
        (rest.map (Equation.apply (Subst.singleTy index replacement)))
  | tyInt {rest} :
      Reduces (.ty .int .int :: rest) Subst.id rest
  | tyFn {leftDomain leftCodomain rightDomain rightCodomain rest} :
      Reduces
        (.ty (.fn leftDomain leftCodomain) (.fn rightDomain rightCodomain) :: rest)
        Subst.id
        (.ty leftDomain rightDomain :: .ty leftCodomain rightCodomain :: rest)
  | tyProd {left right children rest}
      (paired : tyEquations left right = some children) :
      Reduces (.ty (.prod left) (.prod right) :: rest)
        Subst.id (children ++ rest)
  | tyMatcher {leftCapability rightCapability leftTarget rightTarget rest} :
      Reduces
        (.ty (.matcher leftCapability leftTarget)
          (.matcher rightCapability rightTarget) :: rest)
        Subst.id
        (.cap leftCapability rightCapability :: .ty leftTarget rightTarget :: rest)
  | tySlot {leftCapability rightCapability leftTarget rightTarget rest} :
      Reduces
        (.ty (.slot leftCapability leftTarget)
          (.slot rightCapability rightTarget) :: rest)
        Subst.id
        (.cap leftCapability rightCapability :: .ty leftTarget rightTarget :: rest)

/-- Computable data and its reduction certificate. -/
structure ReductionResult (input : List Equation) where
  substitution : Subst
  equations : List Equation
  valid : Reduces input substitution equations

/-- Perform one deterministic worklist reduction. -/
def reduce : (equations : List Equation) → Option (ReductionResult equations)
  | [] => none
  | .cap .any .any :: rest =>
      some ⟨Subst.id, rest, .capAny⟩
  | .cap (.var left) (.var right) :: rest =>
      if equality : left = right then
        equality ▸ some ⟨Subst.id, rest, .capVarRefl⟩
      else
        have reverse : right ≠ left := fun reversed => equality reversed.symm
        have notOccurs : (Cap.var right).occurs left = false := by
          simp [Cap.occurs, reverse]
        some ⟨Subst.singleCap left (.var right),
          rest.map (Equation.apply (Subst.singleCap left (.var right))),
          .capVarLeft notOccurs⟩
  | .cap (.var index) replacement :: rest =>
      if occurs : replacement.occurs index = true then none
      else
        have notOccurs : replacement.occurs index = false := by
          cases found : replacement.occurs index <;> simp_all
        some ⟨Subst.singleCap index replacement,
          rest.map (Equation.apply (Subst.singleCap index replacement)),
          .capVarLeft notOccurs⟩
  | .cap replacement (.var index) :: rest =>
      if occurs : replacement.occurs index = true then none
      else
        have notOccurs : replacement.occurs index = false := by
          cases found : replacement.occurs index <;> simp_all
        some ⟨Subst.singleCap index replacement,
          rest.map (Equation.apply (Subst.singleCap index replacement)),
          .capVarRight notOccurs⟩
  | .cap (.prod left) (.prod right) :: rest =>
      match paired : capEquations left right with
      | none => none
      | some children =>
          some ⟨Subst.id, children ++ rest, .capProd paired⟩
  | .cap _ _ :: _ => none
  | .ty (.var left) (.var right) :: rest =>
      if equality : left = right then
        equality ▸ some ⟨Subst.id, rest, .tyVarRefl⟩
      else
        have reverse : right ≠ left := fun reversed => equality reversed.symm
        have notOccurs : (Ty.var right).occursTy left = false := by
          simp [Ty.occursTy, reverse]
        some ⟨Subst.singleTy left (.var right),
          rest.map (Equation.apply (Subst.singleTy left (.var right))),
          .tyVarLeft notOccurs⟩
  | .ty (.var index) replacement :: rest =>
      if occurs : replacement.occursTy index = true then none
      else
        have notOccurs : replacement.occursTy index = false := by
          cases found : replacement.occursTy index <;> simp_all
        some ⟨Subst.singleTy index replacement,
          rest.map (Equation.apply (Subst.singleTy index replacement)),
          .tyVarLeft notOccurs⟩
  | .ty replacement (.var index) :: rest =>
      if occurs : replacement.occursTy index = true then none
      else
        have notOccurs : replacement.occursTy index = false := by
          cases found : replacement.occursTy index <;> simp_all
        some ⟨Subst.singleTy index replacement,
          rest.map (Equation.apply (Subst.singleTy index replacement)),
          .tyVarRight notOccurs⟩
  | .ty .int .int :: rest =>
      some ⟨Subst.id, rest, .tyInt⟩
  | .ty (.fn leftDomain leftCodomain) (.fn rightDomain rightCodomain) :: rest =>
      some ⟨Subst.id,
        .ty leftDomain rightDomain :: .ty leftCodomain rightCodomain :: rest,
        .tyFn⟩
  | .ty (.prod left) (.prod right) :: rest =>
      match paired : tyEquations left right with
      | none => none
      | some children =>
          some ⟨Subst.id, children ++ rest, .tyProd paired⟩
  | .ty (.matcher leftCapability leftTarget)
      (.matcher rightCapability rightTarget) :: rest =>
      some ⟨Subst.id,
        .cap leftCapability rightCapability :: .ty leftTarget rightTarget :: rest,
        .tyMatcher⟩
  | .ty (.slot leftCapability leftTarget)
      (.slot rightCapability rightTarget) :: rest =>
      some ⟨Subst.id,
        .cap leftCapability rightCapability :: .ty leftTarget rightTarget :: rest,
        .tySlot⟩
  | .ty _ _ :: _ => none

@[simp] private theorem compose_id_right (substitution : Subst) :
    Subst.compose substitution Subst.id = substitution := by
  cases substitution
  rfl

private theorem holds_compose_id_iff
    (substitution : Subst) (equation : Equation) :
    equation.Holds (Subst.compose substitution Subst.id) ↔
      equation.Holds substitution := by
  simp

private theorem solves_compose_id_iff
    (substitution : Subst) (equations : List Equation) :
    Solves (Subst.compose substitution Subst.id) equations ↔
      Solves substitution equations := by
  constructor <;> intro solved equation member
  · exact (holds_compose_id_iff substitution equation).mp
      (solved equation member)
  · exact (holds_compose_id_iff substitution equation).mpr
      (solved equation member)

theorem Reduces.sound
    {input : List Equation} {first : Subst} {remaining : List Equation}
    (reduction : Reduces input first remaining)
    {later : Subst} (solved : Solves later remaining) :
    Solves (Subst.compose later first) input := by
  cases reduction with
  | capAny =>
      rw [solves_cons]
      exact ⟨by simp [Equation.Holds],
        (solves_compose_id_iff later _).mpr solved⟩
  | capVarRefl =>
      rw [solves_cons]
      exact ⟨by simp [Equation.Holds],
        (solves_compose_id_iff later _).mpr solved⟩
  | capVarLeft notOccurs =>
      rw [solves_cons]
      refine ⟨?_, (solves_map_apply later _ _).mp solved⟩
      simp only [Equation.Holds]
      rw [← Cap.apply_compose, ← Cap.apply_compose,
        Subst.singleCap_hit,
        Cap.apply_singleCap_of_not_occurs _ _ _ notOccurs]
  | capVarRight notOccurs =>
      rw [solves_cons]
      refine ⟨?_, (solves_map_apply later _ _).mp solved⟩
      simp only [Equation.Holds]
      rw [← Cap.apply_compose, ← Cap.apply_compose,
        Subst.singleCap_hit,
        Cap.apply_singleCap_of_not_occurs _ _ _ notOccurs]
  | capProd paired =>
      rw [solves_cons]
      obtain ⟨children, rest⟩ := (solves_append later _ _).mp solved
      refine ⟨?_, (solves_compose_id_iff later _).mpr rest⟩
      simp only [Equation.Holds, compose_id_right]
      exact congrArg Cap.prod (capEquations_sound paired children)
  | tyVarRefl =>
      rw [solves_cons]
      exact ⟨by simp [Equation.Holds],
        (solves_compose_id_iff later _).mpr solved⟩
  | tyVarLeft notOccurs =>
      rw [solves_cons]
      refine ⟨?_, (solves_map_apply later _ _).mp solved⟩
      simp only [Equation.Holds]
      rw [← Ty.apply_compose, ← Ty.apply_compose,
        Subst.singleTy_hit,
        Ty.apply_singleTy_of_not_occurs _ _ _ notOccurs]
  | tyVarRight notOccurs =>
      rw [solves_cons]
      refine ⟨?_, (solves_map_apply later _ _).mp solved⟩
      simp only [Equation.Holds]
      rw [← Ty.apply_compose, ← Ty.apply_compose,
        Subst.singleTy_hit,
        Ty.apply_singleTy_of_not_occurs _ _ _ notOccurs]
  | tyInt =>
      rw [solves_cons]
      exact ⟨by simp [Equation.Holds],
        (solves_compose_id_iff later _).mpr solved⟩
  | tyFn =>
      rw [solves_cons]
      obtain ⟨domain, codomain, rest⟩ := by
        simpa only [solves_cons] using solved
      refine ⟨?_, (solves_compose_id_iff later _).mpr rest⟩
      rw [compose_id_right]
      simp only [Equation.Holds, Ty.apply]
      simp only [Equation.Holds] at domain codomain
      rw [domain, codomain]
  | tyProd paired =>
      rw [solves_cons]
      obtain ⟨children, rest⟩ := (solves_append later _ _).mp solved
      refine ⟨?_, (solves_compose_id_iff later _).mpr rest⟩
      simp only [Equation.Holds, compose_id_right]
      exact congrArg Ty.prod (tyEquations_sound paired children)
  | tyMatcher =>
      rw [solves_cons]
      obtain ⟨capability, target, rest⟩ := by
        simpa only [solves_cons] using solved
      refine ⟨?_, (solves_compose_id_iff later _).mpr rest⟩
      rw [compose_id_right]
      simp only [Equation.Holds, Ty.apply]
      simp only [Equation.Holds] at capability target
      rw [capability, target]
  | tySlot =>
      rw [solves_cons]
      obtain ⟨capability, target, rest⟩ := by
        simpa only [solves_cons] using solved
      refine ⟨?_, (solves_compose_id_iff later _).mpr rest⟩
      rw [compose_id_right]
      simp only [Equation.Holds, Ty.apply]
      simp only [Equation.Holds] at capability target
      rw [capability, target]

/-- Fuel-bounded executable worklist unification. -/
def unifyWithFuel : Nat → List Equation → Option Subst
  | _, [] => some Subst.id
  | 0, _ :: _ => none
  | fuel + 1, equations =>
      match reduce equations with
      | none => none
      | some reduction =>
          match unifyWithFuel fuel reduction.equations with
          | none => none
          | some later => some (Subst.compose later reduction.substitution)

/-- Fuel exhaustion can cause failure, but never a false successful result. -/
theorem unifyWithFuel_sound
    {fuel : Nat} {equations : List Equation} {substitution : Subst}
    (success : unifyWithFuel fuel equations = some substitution) :
    Solves substitution equations := by
  induction fuel generalizing equations substitution with
  | zero =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst substitution
          exact solves_nil _
      | cons equation equations =>
          simp [unifyWithFuel] at success
  | succ fuel induction =>
      cases equations with
      | nil =>
          simp only [unifyWithFuel, Option.some.injEq] at success
          subst substitution
          exact solves_nil _
      | cons equation equations =>
          simp only [unifyWithFuel] at success
          cases reduced : reduce (equation :: equations) with
          | none => simp_all
          | some reduction =>
              cases recursive : unifyWithFuel fuel reduction.equations with
              | none => simp_all
              | some later =>
                  simp_all only [Option.some.injEq]
                  subst substitution
                  exact reduction.valid.sound (induction recursive)

end TypePM
