import TypePM.Scheme
import TypePM.Unification

/-!
# Finite context interfaces for nested source blocks

A closed `let` right-hand side may constrain variables inherited from its
surrounding source context.  The parent block receives those effects as a
finite list of equations.  Solving the list says exactly that the parent's
later substitution agrees, on the free variables of the context, with first
applying the closed block substitution and then the later substitution.
-/

namespace TypePM.Source

namespace Context

/-- Equations exposing the effect of a block substitution on every free
variable of a polymorphic context. -/
def interfaceEquations (context : Context) (block : TypePM.Subst) :
    List TypePM.Equation :=
  (context.freeTyVars.map fun index =>
      TypePM.Equation.ty (.var index) (block.ty index)) ++
  (context.freeCapVars.map fun index =>
      TypePM.Equation.cap (.var index) (block.cap index))

/-- Two substitutions agree on all variables which are free in the source
context. -/
def SubstitutionsAgree (context : Context)
    (left right : TypePM.Subst) : Prop :=
  (∀ index ∈ context.freeTyVars, left.ty index = right.ty index) ∧
    (∀ index ∈ context.freeCapVars, left.cap index = right.cap index)

theorem solves_interfaceEquations_iff
    (context : Context) (block later : TypePM.Subst) :
    TypePM.Solves later (context.interfaceEquations block) ↔
      context.SubstitutionsAgree later
        (TypePM.Subst.compose later block) := by
  constructor
  · intro solved
    constructor
    · intro index membership
      have held := solved
        (TypePM.Equation.ty (.var index) (block.ty index)) (by
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨index, membership, rfl⟩)
      change later.ty index = (block.ty index).apply later at held
      exact held
    · intro index membership
      have held := solved
        (TypePM.Equation.cap (.var index) (block.cap index)) (by
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨index, membership, rfl⟩)
      change later.cap index = (block.cap index).apply later.cap at held
      exact held
  · rintro ⟨tyAgree, capAgree⟩
    intro equation membership
    simp only [interfaceEquations, List.mem_append, List.mem_map] at membership
    rcases membership with tyMembership | capMembership
    · obtain ⟨index, indexMember, rfl⟩ := tyMembership
      change later.ty index = (block.ty index).apply later
      exact tyAgree index indexMember
    · obtain ⟨index, indexMember, rfl⟩ := capMembership
      change later.cap index = (block.cap index).apply later.cap
      exact capAgree index indexMember

end Context

end TypePM.Source
