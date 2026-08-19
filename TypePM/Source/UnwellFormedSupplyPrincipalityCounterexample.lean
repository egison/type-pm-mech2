import TypePM.Source.SupplyWellFormed

/-!
# A principality obstruction below the context's fresh supply

The source relation exposes an arbitrary starting supply, although public
root inference starts at `Context.initialSupply`.  Starting below an existing
free context variable can collide with names allocated by a nested `let`.
This file kernel-checks the three independent ingredients of the resulting
obstruction: reversing equation orientation is still a legal absorbing MGU
solver, the displayed candidate targets are not mutual substitution
instances, and the starting supply is not well formed for the context.  It
does not connect the displayed generated blocks to full elaboration and
closure derivations, so it deliberately does not prove the negation of a
completeness proposition.

This module deliberately records the small semantic obstruction rather than
reintroducing the removed arbitrary-supply principality premise.  The
bad supply is proved not well formed for the context, keeping the public root
scope explicit.
-/

namespace TypePM.Source.UnwellFormedSupplyPrincipalityCounterexample

open TypePM
open TypePM.Source

/-- Reverse both sides of every equation before invoking the public unifier. -/
def flipEquation : Equation → Equation
  | .ty left right => .ty right left
  | .cap left right => .cap right left

def reverseUnify (equations : List Equation) : Option Subst :=
  unify (equations.map flipEquation)

private theorem flipEquation_holds (equation : Equation)
    (substitution : Subst) :
    (flipEquation equation).Holds substitution ↔
      equation.Holds substitution := by
  cases equation <;> simp [flipEquation, Equation.Holds, eq_comm]

private theorem solves_flipped (substitution : Subst)
    (equations : List Equation) :
    Solves substitution (equations.map flipEquation) ↔
      Solves substitution equations := by
  simp only [Solves, List.mem_map]
  constructor
  · intro solved equation member
    exact flipEquation_holds equation substitution |>.mp
      (solved (flipEquation equation) ⟨equation, member, rfl⟩)
  · intro solved equation member
    obtain ⟨original, originalMember, rfl⟩ := member
    exact flipEquation_holds original substitution |>.mpr
      (solved original originalMember)

/-- Equation orientation does not change the class of legal absorbing MGU
solvers. -/
theorem reverseUnify_absorbingMGUSolver :
    AbsorbingMGUSolver reverseUnify := by
  intro equations principal success
  have flipped := unify_absorbingPrincipal success
  constructor
  · constructor
    · exact (solves_flipped principal equations).mp flipped.solves
    · intro specific solved
      exact flipped.mostGeneral.2 specific
        ((solves_flipped specific equations).mpr solved)
  · intro solution solved
    exact flipped.absorbs ((solves_flipped solution equations).mpr solved)

private def v0 : TyVar := ⟨0⟩
private def v3 : TyVar := ⟨3⟩
private def v4 : TyVar := ⟨4⟩
private def v5 : TyVar := ⟨5⟩
private def v6 : TyVar := ⟨6⟩

/-- The free context variable `v5` lies strictly above `badSupply`. -/
def context : Context := [.mono (.var v5)]

def badSupply : Supply := ⟨0, 0⟩

/-- `λx. let y = ((x 0) outer) in something`. -/
def expression : Expr :=
  .lam (.letE (.app (.app (.var 0) (.lit 0)) (.var 1)) .something)

/-- Candidate outer block for the public equation orientation.  No
elaboration linkage is claimed in this module. -/
def standardGenerated : Generated :=
  { target := .fn (.var v0) (.matcher .any (.var v5))
    hard :=
      [.ty (.var v0) (.fn .int (.fn (.var v3) (.var v4))),
       .ty (.var v5) (.var v3)]
    pending := [] }

/-- Candidate outer block suggested by flipping equation orientations at the
nested closure.  Its second interface equation is tautological.  No
elaboration linkage is claimed in this module. -/
def alternativeGenerated : Generated :=
  { target := .fn (.var v0) (.matcher .any (.var v6))
    hard :=
      [.ty (.var v0) (.fn .int (.fn (.var v5) (.var v4))),
       .ty (.var v5) (.var v5)]
    pending := [] }

/-- First candidate target used to isolate the substitution obstruction. -/
def standardTarget : Ty :=
  .fn (.fn .int (.fn (.var v3) (.var v4)))
    (.matcher .any (.var v3))

/-- Second candidate target used to isolate the substitution obstruction. -/
def alternativeTarget : Ty :=
  .fn (.fn .int (.fn (.var v5) (.var v4)))
    (.matcher .any (.var v6))

/-- The alternative target can specialize to the standard target by merging
its two distinct variables. -/
theorem alternativeTarget_instance_standardTarget :
    IsInstance alternativeTarget standardTarget := by
  refine ⟨Subst.compose (Subst.singleTy v6 (.var v3))
    (Subst.singleTy v5 (.var v3)), ?_⟩
  simp [alternativeTarget, standardTarget, Subst.compose,
    Subst.singleTy, Ty.apply, v3, v4, v5, v6]
  rfl

/-- The converse fails: one occurrence of `v3` cannot be substituted into
the two distinct variables `v5` and `v6`. -/
theorem not_standardTarget_instance_alternativeTarget :
    ¬ IsInstance standardTarget alternativeTarget := by
  rintro ⟨substitution, equality⟩
  simp only [standardTarget, alternativeTarget, Ty.apply] at equality
  have outer := Ty.fn.inj equality
  have inner := Ty.fn.inj (Ty.fn.inj outer.1).2
  have matcher := Ty.matcher.inj outer.2
  have same : (Ty.var v5 : Ty) = .var v6 := by
    rw [← inner.1, matcher.2]
  have : v5 = v6 := Ty.var.inj same
  exact (by decide : v5 ≠ v6) this

/-- In particular the two targets are not mutually substitution instances. -/
theorem targets_not_mutualInstances :
    ¬ (IsInstance standardTarget alternativeTarget ∧
      IsInstance alternativeTarget standardTarget) :=
  fun instances => not_standardTarget_instance_alternativeTarget instances.1

theorem context_initialSupply : context.initialSupply = ⟨6, 0⟩ := by
  decide

/-- This bad starting point is excluded by the premise used for public root
inference. -/
theorem badSupply_not_wellFormed :
    ¬ badSupply.WellFormedFor context := by
  rw [Supply.WellFormedFor, context_initialSupply]
  simp [Supply.Le, badSupply]

end TypePM.Source.UnwellFormedSupplyPrincipalityCounterexample
