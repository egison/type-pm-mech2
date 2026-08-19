import TypePM.GeneratedSupport

/-!
# Variable support of residual resolution
-/

namespace TypePM

private theorem Dual.capabilities_support (duals : List Dual) :
    ∀ candidate,
      candidate ∈ Cap.unificationVarsList (Dual.capabilities duals) →
        candidate ∈ Ty.unificationVarsList (duals.map Dual.matcherType) := by
  induction duals with
  | nil => simp [Dual.capabilities, Cap.unificationVarsList,
      Ty.unificationVarsList]
  | cons dual duals induction =>
      intro candidate member
      simp only [Dual.capabilities, List.map_cons,
        Cap.unificationVarsList, Ty.unificationVarsList,
        Dual.matcherType, Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with head | tail
      · exact Or.inl (Or.inl head)
      · exact Or.inr (induction candidate tail)

private theorem Dual.targets_support (duals : List Dual) :
    ∀ candidate,
      candidate ∈ Ty.unificationVarsList (Dual.targets duals) →
        candidate ∈ Ty.unificationVarsList (duals.map Dual.matcherType) := by
  induction duals with
  | nil => simp [Dual.targets, Ty.unificationVarsList]
  | cons dual duals induction =>
      intro candidate member
      simp only [Dual.targets, List.map_cons, Ty.unificationVarsList,
        Dual.matcherType, Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with head | tail
      · exact Or.inl (Or.inr head)
      · exact Or.inr (induction candidate tail)

/-- Every residual equation is assembled from subterms of the two types
indexed by its resolution. -/
theorem Resolution.equations_support
    {source expected : Ty} (resolution : Resolution source expected) :
    ∀ candidate, candidate ∈ unificationVars resolution.equations →
      candidate ∈ source.unificationVars ∨
        candidate ∈ expected.unificationVars := by
  intro candidate member
  cases resolution with
  | ordinary source expected =>
      simpa [Resolution.equations, unificationVars,
        Equation.unificationVars] using member
  | matcherToSlot producer consumer sourceTarget expectedTarget capability =>
      cases capability with
      | equal =>
          have member' : candidate ∈
              producer.unificationVars ++ consumer.unificationVars ++
                sourceTarget.unificationVars ++
                  expectedTarget.unificationVars := by
            simpa [Resolution.equations, CapabilityResolution.equations,
              unificationVars, Equation.unificationVars,
              List.append_assoc] using member
          simp only [List.mem_append] at member'
          rcases member' with left | expectedMember
          · rcases left with caps | sourceMember
            · rcases caps with producerMember | consumerMember
              · exact Or.inl (List.mem_append_left _ producerMember)
              · exact Or.inr (List.mem_append_left _ consumerMember)
            · exact Or.inl (List.mem_append_right _ sourceMember)
          · exact Or.inr (List.mem_append_right _ expectedMember)
      | rootedAny =>
          have member' : candidate ∈
              sourceTarget.unificationVars ++
                expectedTarget.unificationVars := by
            simpa [Resolution.equations, CapabilityResolution.equations,
              unificationVars, Equation.unificationVars] using member
          simp only [List.mem_append] at member'
          rcases member' with sourceMember | expectedMember
          · exact Or.inl (List.mem_append_right _ sourceMember)
          · exact Or.inr (List.mem_append_right _ expectedMember)
  | productMatcher items duals types_eq nonempty expectedCapability
      expectedTarget =>
      have member' : candidate ∈
          Cap.unificationVarsList (Dual.capabilities duals) ++
            expectedCapability.unificationVars ++
              Ty.unificationVarsList (Dual.targets duals) ++
                expectedTarget.unificationVars := by
        simpa [Resolution.equations, unificationVars,
          Equation.unificationVars, Cap.unificationVars,
          Ty.unificationVars, List.append_assoc] using member
      rw [← types_eq]
      simp only [List.mem_append] at member'
      rcases member' with left | expectedTargetMember
      · rcases left with caps | sourceTargets
        · rcases caps with sourceCapability | expectedCapabilityMember
          · exact Or.inl
              (Dual.capabilities_support duals candidate sourceCapability)
          · exact Or.inr (List.mem_append_left _ expectedCapabilityMember)
        · exact Or.inl (Dual.targets_support duals candidate sourceTargets)
      · exact Or.inr (List.mem_append_right _ expectedTargetMember)
  | productMatcherToSlot items duals types_eq nonempty consumer expectedTarget
      capability =>
      cases capability with
      | equal =>
          have member' : candidate ∈
              Cap.unificationVarsList (Dual.capabilities duals) ++
                consumer.unificationVars ++
                  Ty.unificationVarsList (Dual.targets duals) ++
                    expectedTarget.unificationVars := by
            simpa [Resolution.equations, CapabilityResolution.equations,
              unificationVars, Equation.unificationVars,
              Cap.unificationVars, Ty.unificationVars,
              List.append_assoc] using member
          rw [← types_eq]
          simp only [List.mem_append] at member'
          rcases member' with left | expectedTargetMember
          · rcases left with caps | sourceTargets
            · rcases caps with sourceCapability | consumerMember
              · exact Or.inl
                  (Dual.capabilities_support duals candidate sourceCapability)
              · exact Or.inr (List.mem_append_left _ consumerMember)
            · exact Or.inl
                (Dual.targets_support duals candidate sourceTargets)
          · exact Or.inr (List.mem_append_right _ expectedTargetMember)
      | rootedAny =>
          have member' : candidate ∈
              Ty.unificationVarsList (Dual.targets duals) ++
                expectedTarget.unificationVars := by
            simpa [Resolution.equations, CapabilityResolution.equations,
              unificationVars, Equation.unificationVars,
              Ty.unificationVars] using member
          rw [← types_eq]
          simp only [List.mem_append] at member'
          rcases member' with sourceTargets | expectedTargetMember
          · exact Or.inl (Dual.targets_support duals candidate sourceTargets)
          · exact Or.inr (List.mem_append_right _ expectedTargetMember)

end TypePM
