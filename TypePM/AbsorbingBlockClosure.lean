import TypePM.AbsorbingUnification
import TypePM.BlockClosure

/-!
# Absorption for principal block closure

Hard saturation and residual checking solve two worklists in sequence.  This
module records the additional normalization property supplied by the
executable unifier and proves that it survives their composition.
-/

namespace TypePM

/-- A successful saturation run ends with the absorbing principal solution
returned by its final solver call. -/
theorem saturateLoop_absorbingPrincipal
    {solve : List Equation → Option Subst}
    (solverAbsorbing : AbsorbingMGUSolver solve)
    {fuel : Nat} {hard : List Equation} {pending : List CheckObligation}
    {output : SaturationOutput}
    (success : saturateLoop solve fuel hard pending = some output) :
    AbsorbingPrincipal output.hard output.substitution := by
  induction fuel generalizing hard pending output with
  | zero => simp [saturateLoop] at success
  | succ fuel induction =>
      simp only [saturateLoop] at success
      cases solved : solve hard with
      | none => simp [solved] at success
      | some substitution =>
          simp only [solved] at success
          let promoted := promoteUnder substitution pending
          change
            (match promoted.equations with
              | [] => some ⟨hard, pending, substitution⟩
              | _ :: _ => saturateLoop solve fuel
                  (hard ++ promoted.equations) promoted.pending) =
              some output at success
          cases equationsCase : promoted.equations with
          | nil =>
              rw [equationsCase] at success
              injection success with outputEquality
              subst output
              exact solverAbsorbing hard substitution solved
          | cons equation equations =>
              rw [equationsCase] at success
              exact induction success

theorem saturateUsing_absorbingPrincipal
    {solve : List Equation → Option Subst}
    (solverAbsorbing : AbsorbingMGUSolver solve)
    {hard : List Equation} {pending : List CheckObligation}
    {output : SaturationOutput}
    (success : saturateUsing solve hard pending = some output) :
    AbsorbingPrincipal output.hard output.substitution :=
  saturateLoop_absorbingPrincipal solverAbsorbing success

/-- Residual equations constructed from an idempotent hard substitution are
already normalized by that substitution. -/
theorem CheckObligation.residualEquations_map_apply_of_idempotent
    (obligation : CheckObligation) (substitution : Subst)
    (idempotent :
      Subst.compose substitution substitution = substitution) :
    (obligation.residualEquations substitution).map
        (Equation.apply substitution) =
      obligation.residualEquations substitution := by
  have sourceFixed :
      (obligation.source.apply substitution).apply substitution =
        obligation.source.apply substitution := by
    rw [Ty.apply_compose, idempotent]
  have expectedFixed :
      (obligation.expected.apply substitution).apply substitution =
        obligation.expected.apply substitution := by
    rw [Ty.apply_compose, idempotent]
  have canonical := Resolution.resolve_apply_canonical_of_retract
    substitution Subst.id
    (obligation.source.apply substitution)
    (obligation.expected.apply substitution)
    (by simpa only [Ty.apply_id] using sourceFixed)
    (by simpa only [Ty.apply_id] using expectedFixed)
  have equationsFixed := canonical.2
  rw [sourceFixed, expectedFixed] at equationsFixed
  simpa only [CheckObligation.residualEquations,
    CheckObligation.resolutionUnder] using equationsFixed.symm

/-- List form of normalization for all residual equations. -/
theorem residualEquations_map_apply_of_idempotent
    (substitution : Subst) (obligations : List CheckObligation)
    (idempotent :
      Subst.compose substitution substitution = substitution) :
    (residualEquations substitution obligations).map
        (Equation.apply substitution) =
      residualEquations substitution obligations := by
  induction obligations with
  | nil => rfl
  | cons obligation obligations induction =>
      simp only [residualEquations, List.map_append]
      rw [obligation.residualEquations_map_apply_of_idempotent
          substitution idempotent,
        induction]

namespace PrincipalBlockClosure

/-- Both solver calls used by a closure selected absorbing representatives. -/
def Absorbing {generated : Generated}
    (closure : PrincipalBlockClosure generated) : Prop :=
  AbsorbingPrincipal closure.finalHard closure.hardSubstitution ∧
    AbsorbingPrincipal
      (residualEquations closure.hardSubstitution closure.finalPending)
      closure.residualSubstitution

/-- A substitution solves the two normalized worklists exposed by a closed
block. -/
def SolvesFinal {generated : Generated}
    (closure : PrincipalBlockClosure generated) (solution : Subst) : Prop :=
  Solves solution closure.finalHard ∧
    Solves solution
      (residualEquations closure.hardSubstitution closure.finalPending)

/-- The two normalized worklists solved by the final composed
substitution. -/
def finalEquations {generated : Generated}
    (closure : PrincipalBlockClosure generated) : List Equation :=
  closure.finalHard ++
    residualEquations closure.hardSubstitution closure.finalPending

/-- Every solution of both final worklists absorbs the composed substitution
chosen by an absorbing closure. -/
theorem absorbsFinalSolution {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing)
    {solution : Subst} (solved : closure.SolvesFinal solution) :
    Subst.compose solution closure.substitution = solution := by
  calc
    Subst.compose solution closure.substitution =
        Subst.compose solution
          (Subst.compose closure.residualSubstitution
            closure.hardSubstitution) := rfl
    _ = Subst.compose
          (Subst.compose solution closure.residualSubstitution)
          closure.hardSubstitution :=
      Subst.compose_assoc solution closure.residualSubstitution
        closure.hardSubstitution
    _ = Subst.compose solution closure.hardSubstitution := by
      rw [absorbing.2.absorbs solved.2]
    _ = solution := absorbing.1.absorbs solved.1

/-- The composed closure substitution solves its normalized residual
worklist. -/
theorem substitution_solves_residual {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) :
    Solves closure.substitution
      (residualEquations closure.hardSubstitution closure.finalPending) := by
  apply (solves_map_apply closure.residualSubstitution
    closure.hardSubstitution _).mp
  rw [residualEquations_map_apply_of_idempotent
    closure.hardSubstitution closure.finalPending
    absorbing.1.idempotent]
  exact absorbing.2.solves

/-- The composed closure substitution solves both normalized final
worklists. -/
theorem substitution_solvesFinal {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) :
    closure.SolvesFinal closure.substitution :=
  ⟨closure.finalHard_solved,
    closure.substitution_solves_residual absorbing⟩

/-- The final hard/residual composition is itself an absorbing principal
solution of the concatenated normalized worklists. -/
theorem substitution_absorbingPrincipal {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) :
    AbsorbingPrincipal closure.finalEquations closure.substitution := by
  have finalSolved := closure.substitution_solvesFinal absorbing
  have solvedEquations :
      Solves closure.substitution closure.finalEquations := by
    exact (solves_append closure.substitution _ _).mpr finalSolved
  refine ⟨⟨solvedEquations, ?_⟩, ?_⟩
  · intro specific specificSolved
    have specificFinal : closure.SolvesFinal specific :=
      (solves_append specific _ _).mp specificSolved
    exact ⟨specific,
      (closure.absorbsFinalSolution absorbing specificFinal).symm⟩
  · intro specific specificSolved
    exact closure.absorbsFinalSolution absorbing
      ((solves_append specific _ _).mp specificSolved)

/-- The hard/residual composed substitution of an absorbing closure is
idempotent. -/
theorem substitution_idempotent {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) :
    Subst.compose closure.substitution closure.substitution =
      closure.substitution :=
  (closure.substitution_absorbingPrincipal absorbing).idempotent

end PrincipalBlockClosure

/-- A successful executable block closure driven by an absorbing solver
returns a principal closure whose two representatives are absorbing. -/
theorem inferGeneratedUsing_absorbingPrincipalBlockClosure
    {solve : List Equation → Option Subst}
    (solverAbsorbing : AbsorbingMGUSolver solve)
    {generated : Generated} {result : InferenceResult}
    (success : inferGeneratedUsing solve generated = some result) :
    ∃ closure : PrincipalBlockClosure generated,
      result.substitution = closure.substitution ∧
        result.target = closure.target ∧ closure.Absorbing := by
  unfold inferGeneratedUsing at success
  cases saturationResult :
      saturateUsing solve generated.hard generated.pending with
  | none => simp [saturationResult] at success
  | some saturated =>
      rw [saturationResult] at success
      change
        (solve (residualEquations saturated.substitution
            saturated.pending)).bind (fun residual =>
          some
            { substitution := Subst.compose residual saturated.substitution
              target := generated.target.apply
                (Subst.compose residual saturated.substitution) }) =
          some result at success
      cases residualResult :
          solve (residualEquations saturated.substitution saturated.pending) with
      | none => simp [residualResult] at success
      | some residual =>
          simp only [residualResult, Option.bind_some,
            Option.some.injEq] at success
          subst result
          have hardAbsorbing :=
            saturateUsing_absorbingPrincipal solverAbsorbing
              saturationResult
          have residualAbsorbing :=
            solverAbsorbing _ _ residualResult
          let closure : PrincipalBlockClosure generated :=
            { finalHard := saturated.hard
              finalPending := saturated.pending
              hardSubstitution := saturated.substitution
              residualSubstitution := residual
              saturation := saturateUsing_sound solve
                (fun equations substitution solved =>
                  (solverAbsorbing equations substitution solved).mostGeneral)
                saturationResult
              residualPrincipal := residualAbsorbing.mostGeneral }
          exact ⟨closure, rfl, rfl, hardAbsorbing, residualAbsorbing⟩

/-- The final substitution computed by the concrete block-closure algorithm
is idempotent. -/
theorem inferGeneratedUsing_unify_substitution_idempotent
    {generated : Generated} {result : InferenceResult}
    (success : inferGeneratedUsing unify generated = some result) :
    Subst.compose result.substitution result.substitution =
      result.substitution := by
  obtain ⟨closure, substitutionEquality, _, absorbing⟩ :=
    inferGeneratedUsing_absorbingPrincipalBlockClosure
      unify_absorbingMGUSolver success
  rw [substitutionEquality]
  exact closure.substitution_idempotent absorbing

end TypePM
