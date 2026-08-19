import TypePM.InferenceCompleteness

/-!
# Exact M1 acceptance

Soundness and completeness make public inference a decision procedure for
the existence of an independent declarative typing.
-/

namespace TypePM

/-- An expression is typable when it has at least one declarative result
type. -/
def Typable (context : Context) (expression : Expr) : Prop :=
  ∃ target, Typing context expression target

namespace Inference

/-- Public inference succeeds exactly for declaratively typable M1
expressions. -/
theorem typable_iff_infer_isSome
    (context : Context) (expression : Expr) :
    Typable context expression ↔ infer context expression ≠ none := by
  constructor
  · rintro ⟨target, typing⟩
    exact typing.infer_isSome
  · intro succeeds
    cases computed : infer context expression with
    | none => exact False.elim (succeeds computed)
    | some target =>
        exact ⟨target, infer_success_typing computed⟩

/-- Typability is decidable by running public inference. -/
def typableDecidable (context : Context) (expression : Expr) :
    Decidable (Typable context expression) :=
  match computed : infer context expression with
  | none => isFalse (by
      rintro ⟨target, typing⟩
      exact typing.infer_isSome computed)
  | some target =>
      isTrue ⟨target, infer_success_typing computed⟩

end Inference

end TypePM
