import TypePM.SaturationUniqueness

/-!
# Transport of residual checking equations between equivalent MGUs

Residual checking is classified only after hard saturation.  This module
shows that changing the representative MGU does not lose residual solutions.
-/

namespace TypePM

namespace ResolutionTransport

/-- The complete branch tag lives beside `resolve`, where its normalized
shape parser is available. -/
abbrev Branch := Resolution.Branch

def branch {source expected : Ty} :
    Resolution source expected → Branch :=
  Resolution.branch

@[simp] theorem branch_ordinary (source expected : Ty) :
    branch (.ordinary source expected) = .ordinary := rfl

@[simp] theorem branch_matcherToSlot_equal
    (producer consumer : Cap) (sourceTarget expectedTarget : Ty) :
    branch (.matcherToSlot producer consumer sourceTarget expectedTarget
      (.equal : CapabilityResolution producer consumer)) =
        .matcherToSlotEqual := rfl

@[simp] theorem branch_matcherToSlot_any
    (producer : Cap) (sourceTarget expectedTarget : Ty) :
    branch (.matcherToSlot producer .any sourceTarget expectedTarget
      (.rootedAny : CapabilityResolution producer .any)) =
        .matcherToSlotAny := rfl

@[simp] theorem branch_productMatcher
    (duals : List Dual) (nonempty : duals ≠ [])
    (expectedCapability : Cap) (expectedTarget : Ty) :
    branch (.productMatcher (duals.map Dual.matcherType) duals rfl nonempty
      expectedCapability expectedTarget) = .productMatcher := rfl

@[simp] theorem branch_productMatcherToSlot_equal
    (duals : List Dual) (nonempty : duals ≠ [])
    (consumer : Cap) (expectedTarget : Ty) :
    branch (.productMatcherToSlot (duals.map Dual.matcherType) duals rfl
      nonempty consumer expectedTarget
      (.equal : CapabilityResolution
        (.prod (Dual.capabilities duals)) consumer)) =
        .productMatcherToSlotEqual := rfl

@[simp] theorem branch_productMatcherToSlot_any
    (duals : List Dual) (nonempty : duals ≠ [])
    (expectedTarget : Ty) :
    branch (.productMatcherToSlot (duals.map Dual.matcherType) duals rfl
      nonempty .any expectedTarget
      (.rootedAny : CapabilityResolution
        (.prod (Dual.capabilities duals)) .any)) =
        .productMatcherToSlotAny := rfl

/-- Canonicality needed to transport residual equations through a later
substitution.  The fine branch distinguishes capability equality from the
source-rooted `Any` case; equality of the coarse `ConversionClass` would not
be sufficient. -/
structure CanonicalUnder (post : Subst) (source expected : Ty) : Prop where
  sameBranch :
    branch (resolve source expected) =
      branch (resolve (source.apply post) (expected.apply post))
  equations :
    (resolve (source.apply post) (expected.apply post)).equations =
      (resolve source expected).equations.map (Equation.apply post)

/-- A residual solution after `post` composes with `post` to solve the
earlier canonical residual worklist. -/
theorem solves_transport
    {post residual : Subst} {source expected : Ty}
    (canonical : CanonicalUnder post source expected)
    (solved : Solves residual
      (resolve (source.apply post) (expected.apply post)).equations) :
    Solves (Subst.compose residual post)
      (resolve source expected).equations := by
  apply (solves_map_apply residual post _).mp
  rw [← canonical.equations]
  exact solved

/-- Canonicality for every original obligation in a pending list. -/
def PendingCanonicalUnder
    (post general : Subst) (pending : List CheckObligation) : Prop :=
  ∀ obligation ∈ pending,
    CanonicalUnder post
      (obligation.source.apply general)
      (obligation.expected.apply general)

/-- Forward and reverse factorization make the later representative a
retractable instance on each obligation, which is exactly the hypothesis
needed by normalized resolution. -/
theorem canonicalUnder_of_factorizations
    {general specific post retract : Subst}
    (obligation : CheckObligation)
    (forwardFactor : specific = Subst.compose post general)
    (reverseFactor : general = Subst.compose retract specific) :
    CanonicalUnder post
      (obligation.source.apply general)
      (obligation.expected.apply general) := by
  have sourceRetracts :
      ((obligation.source.apply general).apply post).apply retract =
        obligation.source.apply general := by
    calc
      ((obligation.source.apply general).apply post).apply retract =
          (obligation.source.apply
            (Subst.compose post general)).apply retract := by
        rw [Ty.apply_compose post general obligation.source]
      _ = (obligation.source.apply specific).apply retract := by
        rw [forwardFactor]
      _ = obligation.source.apply general := by
        rw [Ty.apply_compose retract specific obligation.source,
          ← reverseFactor]
  have expectedRetracts :
      ((obligation.expected.apply general).apply post).apply retract =
        obligation.expected.apply general := by
    calc
      ((obligation.expected.apply general).apply post).apply retract =
          (obligation.expected.apply
            (Subst.compose post general)).apply retract := by
        rw [Ty.apply_compose post general obligation.expected]
      _ = (obligation.expected.apply specific).apply retract := by
        rw [forwardFactor]
      _ = obligation.expected.apply general := by
        rw [Ty.apply_compose retract specific obligation.expected,
          ← reverseFactor]
  have canonical := Resolution.resolve_apply_canonical_of_retract
    post retract (obligation.source.apply general)
      (obligation.expected.apply general)
      sourceRetracts expectedRetracts
  exact
    { sameBranch := by simpa [branch] using canonical.1
      equations := canonical.2 }

theorem pendingCanonicalUnder_of_factorizations
    {general specific post retract : Subst}
    {pending : List CheckObligation}
    (forwardFactor : specific = Subst.compose post general)
    (reverseFactor : general = Subst.compose retract specific) :
    PendingCanonicalUnder post general pending := by
  intro obligation _
  exact canonicalUnder_of_factorizations obligation
    forwardFactor reverseFactor

/-- One-obligation form, stated with the factorization equation supplied by
`FactorsThrough`. -/
theorem obligation_residual_transport
    {general specific post residual : Subst}
    (obligation : CheckObligation)
    (factor : specific = Subst.compose post general)
    (canonical : CanonicalUnder post
      (obligation.source.apply general)
      (obligation.expected.apply general))
    (solved : Solves residual
      (obligation.residualEquations specific)) :
    Solves (Subst.compose residual post)
      (obligation.residualEquations general) := by
  have sourceEquality :
      obligation.source.apply specific =
        (obligation.source.apply general).apply post := by
    rw [factor]
    exact (Ty.apply_compose post general obligation.source).symm
  have expectedEquality :
      obligation.expected.apply specific =
        (obligation.expected.apply general).apply post := by
    rw [factor]
    exact (Ty.apply_compose post general obligation.expected).symm
  simp only [CheckObligation.residualEquations,
    CheckObligation.resolutionUnder] at solved ⊢
  rw [sourceEquality, expectedEquality] at solved
  exact solves_transport canonical solved

/-- Lift one-obligation transport to the concatenated residual worklist of a
whole pending block. -/
theorem residualEquations_transport
    {general specific post residual : Subst}
    {pending : List CheckObligation}
    (factor : specific = Subst.compose post general)
    (canonical : PendingCanonicalUnder post general pending)
    (solved : Solves residual (residualEquations specific pending)) :
    Solves (Subst.compose residual post)
      (residualEquations general pending) := by
  induction pending with
  | nil => simp [residualEquations]
  | cons obligation pending induction =>
      simp only [residualEquations] at solved ⊢
      obtain ⟨headSolved, tailSolved⟩ :=
        (solves_append residual _ _).mp solved
      apply (solves_append (Subst.compose residual post) _ _).mpr
      refine ⟨obligation_residual_transport obligation factor
        (canonical obligation (by simp)) headSolved, ?_⟩
      exact induction
        (fun member memberInTail => canonical member (by simp [memberInTail]))
        tailSolved

/-- Mutual factorization packages the forward substitution needed by the
transport theorem.  The reverse factor is retained explicitly because it is
what justifies `CanonicalUnder`: it prevents variables from gaining rigid
matcher/slot or `Any` constructors in only one representative. -/
theorem residualEquations_transport_of_mutualFactors
    {general specific residual : Subst}
    {pending : List CheckObligation}
    (forward : FactorsThrough general specific)
    (reverse : FactorsThrough specific general)
    (solved : Solves residual (residualEquations specific pending)) :
    ∃ post,
      specific = Subst.compose post general ∧
      Solves (Subst.compose residual post)
        (residualEquations general pending) := by
  obtain ⟨post, factor⟩ := forward
  obtain ⟨retract, reverseFactor⟩ := reverse
  exact ⟨post, factor,
    residualEquations_transport factor
      (pendingCanonicalUnder_of_factorizations factor reverseFactor) solved⟩

end ResolutionTransport

end TypePM
