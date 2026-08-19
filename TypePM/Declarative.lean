import TypePM.GenerationFreshness
import TypePM.Saturation

/-!
# Declarative M1 source typing

`Typing` is built only from the relational generator, declarative saturation,
simultaneous satisfaction of residual equations, and substitution.  Its
definition does not mention the executable generator, unifier, inference
function, or a terminal audit.
-/

namespace TypePM

/-- Complete evidence for one declarative source typing.  This structure is
data in `Type`; `Typing` below hides the choice of witnesses propositionally. -/
structure TypingDerivation
    (context : Context) (expression : Expr) (target : Ty) where
  generated : Generated
  next : Nat
  finalHard : List Equation
  finalPending : List CheckObligation
  hardSubstitution : Subst
  residualSubstitution : Subst
  generation :
    Generates context expression context.nextVar generated next
  saturation :
    Saturated generated.hard generated.pending
      finalHard finalPending hardSubstitution
  residualSolved :
    Solves residualSubstitution
      (residualEquations hardSubstitution finalPending)
  target_eq :
    target = generated.target.apply
      (Subst.compose residualSubstitution hardSubstitution)

/-- A source expression has a type when there exists a relational generation,
declarative saturation, and one simultaneous solution of all residual
checking equations yielding that type. -/
def Typing (context : Context) (expression : Expr) (target : Ty) : Prop :=
  Nonempty (TypingDerivation context expression target)

namespace Equation

/-- Applying any later substitution preserves an equation already solved by
an earlier substitution. -/
theorem holds_postcompose
    {equation : Equation} {earlier : Subst}
    (held : equation.Holds earlier) (later : Subst) :
    equation.Holds (Subst.compose later earlier) := by
  cases equation with
  | cap left right =>
      simp only [Equation.Holds] at held ⊢
      rw [← Cap.apply_compose, ← Cap.apply_compose, held]
  | ty left right =>
      simp only [Equation.Holds] at held ⊢
      rw [← Ty.apply_compose, ← Ty.apply_compose, held]

end Equation

/-- Applying any later substitution preserves a solved equation list. -/
theorem solves_postcompose
    {equations : List Equation} {earlier : Subst}
    (solved : Solves earlier equations) (later : Subst) :
    Solves (Subst.compose later earlier) equations := by
  intro equation membership
  exact Equation.holds_postcompose (solved equation membership) later

namespace TypingDerivation

/-- The composed final substitution still solves all saturated hard
equations. -/
theorem finalHard_solved
    {context : Context} {expression : Expr} {target : Ty}
    (derivation : TypingDerivation context expression target) :
    Solves
      (Subst.compose derivation.residualSubstitution
        derivation.hardSubstitution)
      derivation.finalHard := by
  exact solves_postcompose derivation.saturation.principal.1
    derivation.residualSubstitution

/-- Every obligation left after hard saturation becomes a genuine checking
conversion under the one composed final substitution. -/
theorem remaining_checkConversion
    {context : Context} {expression : Expr} {target : Ty}
    (derivation : TypingDerivation context expression target) :
    ∀ obligation ∈ derivation.finalPending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply
            (Subst.compose derivation.residualSubstitution
              derivation.hardSubstitution))
          (obligation.expected.apply
            (Subst.compose derivation.residualSubstitution
              derivation.hardSubstitution)) := by
  intro obligation membership
  obtain ⟨conversionClass, conversion⟩ := residualEquations_sound
    derivation.residualSolved obligation membership
  exact ⟨conversionClass, by
    simpa only [Ty.apply_compose] using conversion⟩

/-- The relational generation embedded in a source typing is well scoped:
all generated ordinary variables are below `next`, and every variable not
inherited from the context starts at `Context.nextVar`. -/
theorem generation_wellScoped
    {context : Context} {expression : Expr} {target : Ty}
    (derivation : TypingDerivation context expression target) :
    derivation.generated.tyVarsBelow derivation.next ∧
      derivation.generated.tyVarsFromContextOrFresh
        context context.nextVar := by
  exact derivation.generation.tyVarsWellScoped (Nat.le_refl _)

end TypingDerivation

namespace Typing

/-- A `Typing` proof exposes a witness whose remaining obligations all have
checking conversions. -/
theorem exists_remaining_checkConversions
    {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing context expression target) :
    ∃ derivation : TypingDerivation context expression target,
      ∀ obligation ∈ derivation.finalPending,
        ∃ conversionClass,
          CheckConversion conversionClass
            (obligation.source.apply
              (Subst.compose derivation.residualSubstitution
                derivation.hardSubstitution))
            (obligation.expected.apply
              (Subst.compose derivation.residualSubstitution
                derivation.hardSubstitution)) := by
  rcases typing with ⟨derivation⟩
  exact ⟨derivation, derivation.remaining_checkConversion⟩

/-- A `Typing` proof exposes the freshness invariant of its relationally
generated problem. -/
theorem exists_generation_wellScoped
    {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing context expression target) :
    ∃ derivation : TypingDerivation context expression target,
      derivation.generated.tyVarsBelow derivation.next ∧
        derivation.generated.tyVarsFromContextOrFresh
          context context.nextVar := by
  rcases typing with ⟨derivation⟩
  exact ⟨derivation, derivation.generation_wellScoped⟩

end Typing

end TypePM
