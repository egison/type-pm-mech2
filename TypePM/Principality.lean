import TypePM.Inference
import TypePM.ResolutionTransport
import TypePM.Solver

/-!
# Principality of inference

An arbitrary declarative typing may choose a later instance of the generated
type.  Public inference instead solves both the saturated hard equations and
the residual checking equations most generally.  Residual-equation transport
aligns the two possible representatives of the hard MGU.
-/

namespace TypePM

/-- A declarative result is principal when every other declarative result is
its substitution instance. -/
def PrincipalTyping
    (context : Context) (expression : Expr) (target : Ty) : Prop :=
  Typing context expression target ∧
    ∀ other, Typing context expression other → IsInstance target other

namespace Inference

/-- Generic principality for any complete most-general-unifier
implementation. -/
theorem inferUsing_principal
    {solve : List Equation → Option Subst}
    (solver : CompleteMGUSolver solve)
    {context : Context} {expression : Expr} {result : InferenceResult}
    (success : inferUsing solve context expression = some result)
    {target : Ty} (typing : Typing context expression target) :
    IsInstance result.target target := by
  rcases typing with ⟨derivation⟩
  have generatedResult := generates_to_generate derivation.generation
  simp only [inferUsing, generatedResult] at success
  unfold inferGeneratedUsing at success
  cases saturatedResult :
      saturateUsing solve derivation.generated.hard
        derivation.generated.pending with
  | none => simp [saturatedResult] at success
  | some saturated =>
      rw [saturatedResult] at success
      change
        (solve (residualEquations saturated.substitution
            saturated.pending)).bind (fun residual =>
          some
            { substitution := Subst.compose residual saturated.substitution
              target := derivation.generated.target.apply
                (Subst.compose residual saturated.substitution) }) =
          some result at success
      cases residualResult : solve
          (residualEquations saturated.substitution saturated.pending) with
      | none => simp [residualResult] at success
      | some residual =>
          simp only [residualResult, Option.bind_some,
            Option.some.injEq] at success
          subst result
          have executableSaturation :
              Saturated derivation.generated.hard
                derivation.generated.pending saturated.hard
                saturated.pending saturated.substitution :=
            TypePM.saturateUsing_sound solve solver.principal saturatedResult
          have finalState :=
            executableSaturation.finalState_unique derivation.saturation
          have declarativeResidualSolved :
              Solves derivation.residualSubstitution
                (residualEquations derivation.hardSubstitution
                  saturated.pending) := by
            rw [finalState.2]
            exact derivation.residualSolved
          have factors :=
            executableSaturation.finalSubstitutions_mutualFactors
              derivation.saturation
          obtain ⟨post, hardFactor, transportedSolved⟩ :=
            ResolutionTransport.residualEquations_transport_of_mutualFactors
              factors.1 factors.2 declarativeResidualSolved
          have residualPrincipal := solver.principal _ _ residualResult
          obtain ⟨later, residualFactor⟩ :=
            residualPrincipal.2 _ transportedSolved
          have finalFactor :
              Subst.compose derivation.residualSubstitution
                  derivation.hardSubstitution =
                Subst.compose later
                  (Subst.compose residual saturated.substitution) := by
            calc
              Subst.compose derivation.residualSubstitution
                  derivation.hardSubstitution =
                  Subst.compose derivation.residualSubstitution
                    (Subst.compose post saturated.substitution) := by
                      rw [hardFactor]
              _ = Subst.compose
                    (Subst.compose derivation.residualSubstitution post)
                    saturated.substitution :=
                  Subst.compose_assoc _ _ _
              _ = Subst.compose (Subst.compose later residual)
                    saturated.substitution := by
                  rw [residualFactor]
              _ = Subst.compose later
                    (Subst.compose residual saturated.substitution) :=
                  (Subst.compose_assoc _ _ _).symm
          refine ⟨later, ?_⟩
          calc
            (derivation.generated.target.apply
                (Subst.compose residual saturated.substitution)).apply later =
                derivation.generated.target.apply
                  (Subst.compose later
                    (Subst.compose residual saturated.substitution)) :=
              Ty.apply_compose later
                (Subst.compose residual saturated.substitution)
                derivation.generated.target
            _ = derivation.generated.target.apply
                  (Subst.compose derivation.residualSubstitution
                    derivation.hardSubstitution) := by
              rw [finalFactor]
            _ = target := derivation.target_eq.symm

/-- M1 public inference returns a type that is more general than every
declarative `Typing` result. -/
theorem infer_principal
    {context : Context} {expression : Expr} {principal target : Ty}
    (success : infer context expression = some principal)
    (typing : Typing context expression target) :
    IsInstance principal target := by
  unfold infer at success
  cases computed : inferUsing unify context expression with
  | none => simp [computed] at success
  | some result =>
      simp only [computed, Option.map_some, Option.some.injEq] at success
      subst principal
      exact inferUsing_principal unify_completeMGUSolver computed typing

/-- A successful public result packages both its declarative derivation and
its principality property. -/
theorem infer_success_principalTyping
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer context expression = some target) :
    PrincipalTyping context expression target := by
  exact ⟨infer_success_typing success,
    fun _ typing => infer_principal success typing⟩

end Inference

namespace PrincipalTyping

/-- Any two principal representatives are mutually substitution instances.
The stronger statement that the witnessing substitutions are finite
renamings is a separate target-uniqueness theorem. -/
theorem mutualInstances
    {context : Context} {expression : Expr} {left right : Ty}
    (leftPrincipal : PrincipalTyping context expression left)
    (rightPrincipal : PrincipalTyping context expression right) :
    IsInstance left right ∧ IsInstance right left :=
  ⟨leftPrincipal.2 right rightPrincipal.1,
    rightPrincipal.2 left leftPrincipal.1⟩

end PrincipalTyping

end TypePM
