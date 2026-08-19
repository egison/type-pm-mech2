import TypePM.InferenceProcedure
import TypePM.SolverCertified

/-!
# Public M1 inference

The public procedure instantiates the generic inference pipeline with the
total certified unifier.  It exposes only the inferred type; substitutions
remain internal evidence used by the metatheory.
-/

namespace TypePM

/-- Infer the type of an M1 expression in a monomorphic context. -/
def infer (context : Context) (expression : Expr) : Option Ty :=
  (inferUsing unify context expression).map InferenceResult.target

namespace Inference

/-- M1 acceptance soundness: every type returned by public inference has an
independent declarative `Typing` derivation. -/
theorem infer_success_typing
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer context expression = some target) :
    Typing context expression target := by
  unfold infer at success
  cases computed : inferUsing unify context expression with
  | none => simp [computed] at success
  | some result =>
      simp only [computed, Option.map_some, Option.some.injEq] at success
      subst target
      exact inferUsing_sound unify
        (fun _ _ solved => unify_mostGeneral solved) computed

end Inference

end TypePM
