import TypePM.GeneratedSupport
import TypePM.NoGuess
import TypePM.AbsorbingSupportRange
import TypePM.ResolutionSupport

/-!
# Support preservation through hard saturation
-/

namespace TypePM

/-- Variables available while saturating a hard/pending worklist. -/
def saturationSupport (hard : List Equation)
    (pending : List CheckObligation) : List UnificationVar :=
  unificationVars hard ++ pendingUnificationVars pending

/-- The hard/pending support of a generated block is contained in its full
support, which additionally includes the result type. -/
theorem Generated.saturationSupport_subset (generated : Generated) :
  ∀ candidate,
      candidate ∈ saturationSupport generated.hard generated.pending →
        candidate ∈ generated.unificationVars := by
  intro candidate member
  simp only [saturationSupport, Generated.unificationVars,
    List.mem_append] at member ⊢
  rcases member with hard | pending
  · exact Or.inl (Or.inr hard)
  · exact Or.inr pending

/-- Promotion neither invents variables nor changes the stored obligations. -/
theorem promoteUnder_support
    (substitution : Subst) (pending : List CheckObligation) :
    (∀ candidate,
      candidate ∈ unificationVars
          (promoteUnder substitution pending).equations →
        candidate ∈ pendingUnificationVars pending) ∧
    (∀ candidate,
      candidate ∈ pendingUnificationVars
          (promoteUnder substitution pending).pending →
        candidate ∈ pendingUnificationVars pending) := by
  induction pending with
  | nil => simp [promoteUnder, unificationVars, pendingUnificationVars]
  | cons obligation pending induction =>
      by_cases possible :
          (obligation.source.apply substitution).couldSpecial
            (obligation.expected.apply substitution) = true
      · simp only [promoteUnder, possible, if_pos]
        constructor
        · intro candidate member
          show candidate ∈ obligation.unificationVars ++
            pendingUnificationVars pending
          exact List.mem_append_right _ (induction.1 candidate member)
        · intro candidate member
          simp only [pendingUnificationVars, List.mem_append] at member ⊢
          rcases member with head | tail
          · exact Or.inl head
          · exact Or.inr (induction.2 candidate tail)
      · simp only [promoteUnder, possible]
        constructor
        · intro candidate member
          change candidate ∈
            obligation.source.unificationVars ++
              obligation.expected.unificationVars ++
                unificationVars
                  (promoteUnder substitution pending).equations at member
          simp only [List.mem_append] at member
          simp only [pendingUnificationVars, CheckObligation.unificationVars,
            List.mem_append]
          rcases member with (source | expected) | tail
          · exact Or.inl (Or.inl source)
          · exact Or.inl (Or.inr expected)
          · exact Or.inr (induction.1 candidate tail)
        · intro candidate member
          show candidate ∈ obligation.unificationVars ++
            pendingUnificationVars pending
          exact List.mem_append_right _ (induction.2 candidate member)

namespace PromotionClosure

/-- Declarative saturation preserves the finite support of its initial
hard equations and pending obligations. -/
theorem support_subset
    {hard : List Equation} {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    (closure : PromotionClosure hard pending finalHard finalPending) :
    ∀ candidate, candidate ∈ saturationSupport finalHard finalPending →
      candidate ∈ saturationSupport hard pending := by
  induction closure with
  | refl =>
      intro candidate member
      exact member
  | @step currentHard currentPending substitution promoted
      finalHard finalPending principal promotionEquality progress rest
      induction =>
      intro candidate member
      have intermediate := induction candidate member
      simp only [saturationSupport, unificationVars_append,
        List.mem_append] at intermediate ⊢
      rcases intermediate with hardMember | pendingMember
      · rcases hardMember with oldHard | promotedMember
        · exact Or.inl oldHard
        · exact Or.inr
            ((promoteUnder_support substitution currentPending).1 candidate
              (by rw [promotionEquality]; exact promotedMember))
      · exact Or.inr
          ((promoteUnder_support substitution currentPending).2 candidate
            (by rw [promotionEquality]; exact pendingMember))

end PromotionClosure

theorem Saturated.support_subset
    {hard : List Equation} {pending : List CheckObligation}
    {finalHard : List Equation} {finalPending : List CheckObligation}
    {substitution : Subst}
    (saturated : Saturated hard pending finalHard finalPending substitution) :
    ∀ candidate, candidate ∈ saturationSupport finalHard finalPending →
      candidate ∈ saturationSupport hard pending :=
  saturated.closure.support_subset

theorem Saturated.support_subset_generated
    {generated : Generated} {finalHard : List Equation}
    {finalPending : List CheckObligation} {substitution : Subst}
    (saturated : Saturated generated.hard generated.pending
      finalHard finalPending substitution) :
    ∀ candidate,
      candidate ∈ saturationSupport finalHard finalPending →
        candidate ∈ generated.unificationVars := by
  intro candidate member
  exact generated.saturationSupport_subset candidate
    (saturated.support_subset candidate member)

/-- One successful hard-saturation run using the concrete unifier returns a
substitution confined to the variables of its initial hard/pending state. -/
theorem saturateLoop_unify_localized
    {fuel : Nat} {hard : List Equation}
    {pending : List CheckObligation} {output : SaturationOutput}
    (success : saturateLoop unify fuel hard pending = some output) :
    output.substitution.Localized (saturationSupport hard pending) := by
  induction fuel generalizing hard pending output with
  | zero => simp [saturateLoop] at success
  | succ fuel induction =>
      simp only [saturateLoop] at success
      cases solved : unify hard with
      | none => simp [solved] at success
      | some substitution =>
          simp only [solved] at success
          let promoted := promoteUnder substitution pending
          change
            (match promoted.equations with
              | [] => some ⟨hard, pending, substitution⟩
              | _ :: _ => saturateLoop unify fuel
                  (hard ++ promoted.equations) promoted.pending) =
              some output at success
          cases equationsCase : promoted.equations with
          | nil =>
              rw [equationsCase] at success
              injection success with outputEquality
              subst output
              exact (unify_localized solved).mono (by
                intro candidate member
                exact List.mem_append_left _ member)
          | cons equation equations =>
              rw [equationsCase] at success
              apply (induction success).mono
              intro candidate member
              simp only [saturationSupport, unificationVars_append,
                List.mem_append] at member ⊢
              rcases member with hardMember | pendingMember
              · rcases hardMember with oldHard | promotedMember
                · exact Or.inl oldHard
                · exact Or.inr
                    ((promoteUnder_support substitution pending).1 candidate
                      (by simpa [promoted, equationsCase] using promotedMember))
              · exact Or.inr
                  ((promoteUnder_support substitution pending).2 candidate
                    (by simpa [promoted] using pendingMember))

theorem saturateUsing_unify_localized
    {hard : List Equation} {pending : List CheckObligation}
    {output : SaturationOutput}
    (success : saturateUsing unify hard pending = some output) :
    output.substitution.Localized (saturationSupport hard pending) :=
  saturateLoop_unify_localized success

/-- Residual resolution stays inside any support containing the normalized
obligation and localizing the hard substitution. -/
theorem CheckObligation.residualEquations_support
    {support : List UnificationVar} {substitution : Subst}
    (localized : substitution.Localized support)
    (obligation : CheckObligation)
    (covered : ∀ candidate, candidate ∈ obligation.unificationVars →
      candidate ∈ support) :
    ∀ candidate,
      candidate ∈ TypePM.unificationVars
          (obligation.residualEquations substitution) →
        candidate ∈ support := by
  intro candidate member
  rcases obligation.resolutionUnder substitution |>.equations_support
      candidate member with source | expected
  · exact Subst.Localized.ty_apply_mem localized obligation.source
      (fun candidate member => covered candidate
        (List.mem_append_left _ member)) candidate source
  · exact Subst.Localized.ty_apply_mem localized obligation.expected
      (fun candidate member => covered candidate
        (List.mem_append_right _ member)) candidate expected

theorem residualEquations_support
    {support : List UnificationVar} {substitution : Subst}
    (localized : substitution.Localized support)
    (obligations : List CheckObligation)
    (covered : ∀ obligation, obligation ∈ obligations →
      ∀ candidate, candidate ∈ obligation.unificationVars →
        candidate ∈ support) :
    ∀ candidate,
      candidate ∈ unificationVars
          (residualEquations substitution obligations) →
        candidate ∈ support := by
  induction obligations with
  | nil => simp [residualEquations, unificationVars]
  | cons obligation obligations induction =>
      intro candidate member
      simp only [residualEquations, unificationVars_append,
        List.mem_append] at member
      rcases member with head | tail
      · exact obligation.residualEquations_support localized
          (fun candidate member => covered obligation (by simp) candidate member)
          candidate head
      · exact induction
          (fun item itemMember candidate member =>
            covered item (by simp [itemMember]) candidate member)
          candidate tail

/-- Absorption rules out both changes and fresh names outside a generated
block, so every absorbing principal closure is localized. -/
theorem PrincipalBlockClosure.localized_of_absorbing
    {generated : Generated} (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) : closure.Localized := by
  have hardLocalized :
      closure.hardSubstitution.Localized generated.unificationVars :=
    absorbing.1.localized.mono (by
      intro candidate member
      exact closure.saturation.support_subset_generated candidate
        (List.mem_append_left _ member))
  have residualSupport : ∀ candidate,
      candidate ∈ unificationVars
        (residualEquations closure.hardSubstitution closure.finalPending) →
      candidate ∈ generated.unificationVars :=
    residualEquations_support hardLocalized closure.finalPending (by
      intro obligation obligationMember candidate candidateMember
      exact closure.saturation.support_subset_generated candidate
        (List.mem_append_right _
          (mem_pendingUnificationVars obligationMember candidateMember)))
  have finalSupport : ∀ candidate,
      candidate ∈ unificationVars closure.finalEquations →
        candidate ∈ generated.unificationVars := by
    intro candidate member
    simp only [PrincipalBlockClosure.finalEquations,
      unificationVars_append, List.mem_append] at member
    rcases member with hard | residual
    · exact closure.saturation.support_subset_generated candidate
        (List.mem_append_left _ hard)
    · exact residualSupport candidate residual
  exact (closure.substitution_absorbingPrincipal absorbing).localized.mono
    finalSupport

/-- Executable block closure exposes a principal witness localized to the
complete generated support. -/
theorem inferGeneratedUsing_unify_localizedPrincipalBlockClosure
    {generated : Generated} {result : InferenceResult}
    (success : inferGeneratedUsing unify generated = some result) :
    ∃ closure : PrincipalBlockClosure generated,
      result.substitution = closure.substitution ∧
        result.target = closure.target ∧
          closure.Absorbing ∧ closure.Localized := by
  obtain ⟨closure, substitutionEquality, targetEquality, absorbing⟩ :=
    inferGeneratedUsing_absorbingPrincipalBlockClosure
      unify_absorbingMGUSolver success
  exact ⟨closure, substitutionEquality, targetEquality, absorbing,
    closure.localized_of_absorbing absorbing⟩

end TypePM
