import TypePM.BlockClosureTransport
import TypePM.Source.Elaboration

/-!
# Transport across `let` context interfaces

Two principal closures of one right-hand-side block may choose different
representative substitutions.  Their context-interface equation lists can
therefore be literally different.  This file deliberately avoids equating
those lists.  Instead it postcomposes an outer solution with one closure and
proves that the result absorbs the other closure.  Absorption is exactly the
condition required to solve the other context interface.
-/

namespace TypePM

namespace PrincipalBlockClosure

/-- Mutually factoring absorbing closure representatives absorb one another.
The proof uses the factorization of `left` through `right` and idempotence of
`right`; no equality or renaming of representative variables is required. -/
theorem compose_eq_left_of_representativeTransport
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      RepresentativeTransportUsing left right forward backward)
    (_leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing) :
    Subst.compose left.substitution right.substitution =
      left.substitution := by
  calc
    Subst.compose left.substitution right.substitution =
        Subst.compose
          (Subst.compose backward right.substitution)
          right.substitution := by rw [transport.2]
    _ = Subst.compose backward
          (Subst.compose right.substitution right.substitution) :=
      (Subst.compose_assoc backward right.substitution
        right.substitution).symm
    _ = Subst.compose backward right.substitution := by
      rw [right.substitution_idempotent rightAbsorbing]
    _ = left.substitution := transport.2

/-- Symmetric form of `compose_eq_left_of_representativeTransport`. -/
theorem compose_eq_right_of_representativeTransport
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      RepresentativeTransportUsing left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (_rightAbsorbing : right.Absorbing) :
    Subst.compose right.substitution left.substitution =
      right.substitution := by
  calc
    Subst.compose right.substitution left.substitution =
        Subst.compose
          (Subst.compose forward left.substitution)
          left.substitution := by rw [transport.1]
    _ = Subst.compose forward
          (Subst.compose left.substitution left.substitution) :=
      (Subst.compose_assoc forward left.substitution
        left.substitution).symm
    _ = Subst.compose forward left.substitution := by
      rw [left.substitution_idempotent leftAbsorbing]
    _ = right.substitution := transport.1

/-- Postcomposing an arbitrary later substitution with `left` produces a
substitution which globally absorbs `right`. -/
theorem postcompose_left_absorbs_right
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward later : Subst}
    (transport :
      RepresentativeTransportUsing left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing) :
    Subst.compose
        (Subst.compose later left.substitution)
        right.substitution =
      Subst.compose later left.substitution := by
  calc
    Subst.compose
        (Subst.compose later left.substitution)
        right.substitution =
      Subst.compose later
        (Subst.compose left.substitution right.substitution) :=
        (Subst.compose_assoc later left.substitution
          right.substitution).symm
    _ = Subst.compose later left.substitution := by
      rw [compose_eq_left_of_representativeTransport transport
        leftAbsorbing rightAbsorbing]

end PrincipalBlockClosure

namespace Source

namespace Context

/-- Global absorption implies all of its finite context-interface equations.
This is the bridge from substitution algebra to a `let` effect worklist. -/
theorem solves_interfaceEquations_of_absorbs
    (context : Context) (block later : Subst)
    (absorbs : Subst.compose later block = later) :
    Solves later (context.interfaceEquations block) := by
  apply (context.solves_interfaceEquations_iff block later).2
  constructor
  · intro index _membership
    exact congrArg (fun substitution => substitution.ty index) absorbs.symm
  · intro index _membership
    exact congrArg (fun substitution => substitution.cap index) absorbs.symm

end Context

namespace PrincipalBlockClosure

/-- Although the two literal interface worklists can differ, composing any
outer substitution with `left` always solves the interface exposed by
`right`.  This includes the representative-sensitive case where the same
equation is oriented in opposite directions by the two closures. -/
theorem postcompose_left_solves_right_interface
    {generated : Generated}
    {left right : TypePM.PrincipalBlockClosure generated}
    {forward backward later : Subst}
    (transport : TypePM.PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    Solves (Subst.compose later left.substitution)
      (context.interfaceEquations right.substitution) := by
  apply context.solves_interfaceEquations_of_absorbs
  exact TypePM.PrincipalBlockClosure.postcompose_left_absorbs_right
    transport leftAbsorbing rightAbsorbing

/-- Existential-free public form: the representative transport is supplied
by principality of the two closures of the same generated block. -/
theorem postcompose_solves_other_interface
    {generated : Generated}
    (left right : TypePM.PrincipalBlockClosure generated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (later : Subst) (context : Context) :
    Solves (Subst.compose later left.substitution)
      (context.interfaceEquations right.substitution) := by
  obtain ⟨forward, backward, transport⟩ :=
    left.representativeTransport right
  exact postcompose_left_solves_right_interface transport leftAbsorbing
    rightAbsorbing context

/-- The interface part of `Generated.fromLet` becomes automatic after the
outer solution is postcomposed with the other representative.  Therefore the
whole hard worklist is solved exactly when its body hard worklist is solved. -/
theorem postcompose_left_solves_fromLet_hard_iff
    {generated : Generated}
    {left right : TypePM.PrincipalBlockClosure generated}
    {forward backward later : Subst}
    (transport : TypePM.PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (body : Generated) :
    Solves (Subst.compose later left.substitution)
        (Generated.fromLet
          (context.interfaceEquations right.substitution) body).hard ↔
      Solves (Subst.compose later left.substitution) body.hard := by
  simp only [Generated.fromLet, solves_append]
  exact and_iff_right
    (postcompose_left_solves_right_interface transport leftAbsorbing
      rightAbsorbing context)

/-- Public representative-independent form of the preceding equivalence. -/
theorem postcompose_solves_other_fromLet_hard_iff
    {generated : Generated}
    (left right : TypePM.PrincipalBlockClosure generated)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (later : Subst) (context : Context) (body : Generated) :
    Solves (Subst.compose later left.substitution)
        (Generated.fromLet
          (context.interfaceEquations right.substitution) body).hard ↔
      Solves (Subst.compose later left.substitution) body.hard := by
  obtain ⟨forward, backward, transport⟩ :=
    left.representativeTransport right
  exact postcompose_left_solves_fromLet_hard_iff transport leftAbsorbing
    rightAbsorbing context body

/-- A convenient solution-producing form.  Body equations expressed before
the `left` substitution are transported by `solves_map_apply`; the resulting
outer substitution simultaneously solves `right`'s interface and the body. -/
theorem postcompose_left_solves_fromLet_hard
    {generated : Generated}
    {left right : TypePM.PrincipalBlockClosure generated}
    {forward backward later : Subst}
    (transport : TypePM.PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (body : Generated)
    (bodySolved : Solves later
      (body.hard.map (Equation.apply left.substitution))) :
    Solves (Subst.compose later left.substitution)
      (Generated.fromLet
        (context.interfaceEquations right.substitution) body).hard := by
  apply (postcompose_left_solves_fromLet_hard_iff transport leftAbsorbing
    rightAbsorbing context body).2
  exact (solves_map_apply later left.substitution body.hard).1 bodySolved

end PrincipalBlockClosure

end Source

end TypePM
