import TypePM.Syntax
import TypePM.Checking

/-!
# M0 raw synthesis and explicit-root checking

`RootChecks` assumes that its expected type has already been justified by an
outer construct.  It is not yet the source acceptance relation.
-/

namespace TypePM

mutual

inductive Synth : Context → Expr → Ty → Prop where
  | var {context index target} :
      context[index]? = some target →
      Synth context (.var index) target
  | lit {context value} :
      Synth context (.lit value) .int
  | something {context target} :
      Synth context .something (.matcher .any target)
  | tuple {context expressions targets} :
      Synths context expressions targets →
      Synth context (.tuple expressions) (.prod targets)

inductive Synths : Context → List Expr → List Ty → Prop where
  | nil {context} : Synths context [] []
  | cons {context expression target expressions targets} :
      Synth context expression target →
      Synths context expressions targets →
      Synths context (expression :: expressions) (target :: targets)

end

/-- Checking against an explicitly supplied root expected type. -/
inductive RootChecks : Context → Expr → Ty → Prop where
  | via {context expression source expected kind} :
      Synth context expression source →
      CheckConversion kind source expected →
      RootChecks context expression expected

namespace Synth

theorem tuple_target
    {context : Context} {expressions : List Expr} {target : Ty}
    (typing : Synth context (.tuple expressions) target) :
    ∃ targets, target = .prod targets := by
  cases typing with
  | tuple _ => exact ⟨_, rfl⟩

theorem something_target
    {context : Context} {target : Ty}
    (typing : Synth context .something target) :
    ∃ result, target = .matcher .any result := by
  cases typing with
  | something => exact ⟨_, rfl⟩

end Synth

end TypePM
