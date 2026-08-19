import TypePM.Declarative
import TypePM.SaturationProcedure

/-!
# Inference assembled from an abstract MGU solver

The source generator, hard saturation, and residual checking solver are
composed here without fixing an implementation of first-order unification.
The public `infer` later instantiates `inferUsing` with the total certified MGU
solver.
-/

namespace TypePM

/-- Publicly relevant result of one inference run. -/
structure InferenceResult where
  substitution : Subst
  target : Ty

def inferGeneratedUsing
    (solveHard : List Equation → Option Subst)
    (generated : Generated) : Option InferenceResult := do
  let saturated ← saturateUsing solveHard generated.hard generated.pending
  let residual ← solveHard
    (residualEquations saturated.substitution saturated.pending)
  let substitution := Subst.compose residual saturated.substitution
  pure ⟨substitution, generated.target.apply substitution⟩

def inferUsing
    (solveHard : List Equation → Option Subst)
    (context : Context) (expression : Expr) : Option InferenceResult :=
  match generate context expression context.nextVar with
  | none => none
  | some (generated, _) => inferGeneratedUsing solveHard generated

theorem inferUsing_sound
    (solveHard : List Equation → Option Subst)
    (solverPrincipal : ∀ equations substitution,
      solveHard equations = some substitution →
        MostGeneral equations substitution)
    {context : Context} {expression : Expr} {result : InferenceResult}
    (success : inferUsing solveHard context expression = some result) :
    Typing context expression result.target := by
  cases generatedResult : generate context expression context.nextVar with
  | none => simp [inferUsing, generatedResult] at success
  | some generatedAndNext =>
      cases generatedAndNext with
      | mk generated next =>
          simp only [inferUsing, generatedResult] at success
          unfold inferGeneratedUsing at success
          cases saturatedResult :
              saturateUsing solveHard generated.hard generated.pending with
          | none => simp [saturatedResult] at success
          | some saturated =>
              rw [saturatedResult] at success
              change
                (solveHard (residualEquations saturated.substitution
                    saturated.pending)).bind (fun residual =>
                  some
                    { substitution := Subst.compose residual
                        saturated.substitution
                      target := generated.target.apply
                        (Subst.compose residual saturated.substitution) }) =
                  some result at success
              cases residualResult : solveHard
                  (residualEquations saturated.substitution
                    saturated.pending) with
              | none => simp [residualResult] at success
              | some residual =>
                  simp only [residualResult, Option.bind_some,
                    Option.some.injEq] at success
                  subst result
                  exact ⟨
                    { generated := generated
                      next := next
                      finalHard := saturated.hard
                      finalPending := saturated.pending
                      hardSubstitution := saturated.substitution
                      residualSubstitution := residual
                      generation := generate_to_generates generatedResult
                      saturation := saturateUsing_sound solveHard
                        solverPrincipal saturatedResult
                      residualSolved :=
                        (solverPrincipal _ _ residualResult).1
                      target_eq := rfl }⟩

end TypePM
