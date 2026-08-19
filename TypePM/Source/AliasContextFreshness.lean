import TypePM.FreshAliasPrincipalClosure
import TypePM.Source.ContextInterfaceSupport
import TypePM.Source.GeneratedSupportBounds
import TypePM.Source.InterfaceAliasFreshness

/-!
# Source-context preservation across finite fresh aliases

An alias sequence changes a closure substitution by precomposing the
accumulated substitutions for its fresh endpoints.  If those endpoints do
not occur in the original finite context interface, the precomposition is
invisible both to context closing and to the literal interface equations.
-/

namespace TypePM.Source

open FreshAliasSequence
open FreshAliasPrincipalClosure
open InterfaceAliasDecomposition.AliasFreshness

/-- The exact source-context information needed to erase an accumulated
alias substitution from a closure-interface alignment. -/
structure CumulativeAliasContextFixed
    (aliases : List Alias) {generated : Generated}
    (closure : PrincipalBlockClosure generated) (context : Context) : Prop where
  closedContext :
    context.applyFree
        (Subst.compose closure.substitution
          (sequenceSubstitution aliases)) =
      context.applyFree closure.substitution
  interfaceEquations :
    context.interfaceEquations
        (Subst.compose closure.substitution
          (sequenceSubstitution aliases)) =
      context.interfaceEquations closure.substitution

/-- None of the fresh endpoints introduced by an alias sequence occurs in a
finite support.  Existing endpoints need not be restricted for this basic
fixed-point property. -/
def FreshEndpointsAvoid
    (support : List UnificationVar) (aliases : List Alias) : Prop :=
  ∀ alias, alias ∈ aliases → freshVariable alias ∉ support

theorem FreshEndpointsAvoid.tail
    {support : List UnificationVar} {alias : Alias} {aliases : List Alias}
    (avoids : FreshEndpointsAvoid support (alias :: aliases)) :
    FreshEndpointsAvoid support aliases := by
  intro candidate member
  exact avoids candidate (by simp [member])

/-- The accumulated alias substitution fixes every supported ordinary type
variable when every fresh endpoint avoids that support. -/
theorem sequenceSubstitution_ty_eq_var_of_freshEndpointsAvoid
    {support : List UnificationVar} (aliases : List Alias)
    (avoids : FreshEndpointsAvoid support aliases)
    (index : TyVar) (member : .ty index ∈ support) :
    (sequenceSubstitution aliases).ty index = .var index := by
  induction aliases with
  | nil => rfl
  | cons alias aliases induction =>
      have tailFixed := induction avoids.tail
      have headAbsent := avoids alias (by simp)
      simp only [sequenceSubstitution, Subst.compose]
      rw [tailFixed]
      cases alias with
      | ty fresh existing =>
          have different : index ≠ fresh := by
            intro equality
            subst index
            exact headAbsent member
          simp [aliasSubstitution, Subst.singleTy, Ty.apply, different]
      | cap fresh existing =>
          simp [aliasSubstitution, Subst.singleCap, Ty.apply]

/-- Capability-variable counterpart of
`sequenceSubstitution_ty_eq_var_of_freshEndpointsAvoid`. -/
theorem sequenceSubstitution_cap_eq_var_of_freshEndpointsAvoid
    {support : List UnificationVar} (aliases : List Alias)
    (avoids : FreshEndpointsAvoid support aliases)
    (index : CapVar) (member : .cap index ∈ support) :
    (sequenceSubstitution aliases).cap index = .var index := by
  induction aliases with
  | nil => rfl
  | cons alias aliases induction =>
      have tailFixed := induction avoids.tail
      have headAbsent := avoids alias (by simp)
      simp only [sequenceSubstitution, Subst.compose]
      rw [tailFixed]
      cases alias with
      | ty fresh existing =>
          simp [aliasSubstitution, Subst.singleTy, Cap.apply]
      | cap fresh existing =>
          have different : index ≠ fresh := by
            intro equality
            subst index
            exact headAbsent member
          simp [aliasSubstitution, Subst.singleCap, Cap.apply, different]

/-- Freshness from `ScopedBy` can be narrowed to any sub-support. -/
theorem FreshEndpointsAvoid.of_scopedBy
    {support subset : List UnificationVar} {aliases : List Alias}
    (scopeProof : ScopedBy support aliases)
    (contained : ∀ candidate, candidate ∈ subset → candidate ∈ support) :
    FreshEndpointsAvoid subset aliases := by
  intro alias aliasMember freshMember
  exact (scopeProof.2 alias aliasMember).1 (contained _ freshMember)

private theorem mem_unificationVars_of_equation_mem
    {candidate : UnificationVar} {equation : Equation}
    {equations : List Equation} (equationMember : equation ∈ equations)
    (candidateMember : candidate ∈ equation.unificationVars) :
    candidate ∈ TypePM.unificationVars equations := by
  induction equations with
  | nil => simp at equationMember
  | cons head tail induction =>
      simp only [List.mem_cons] at equationMember
      simp only [TypePM.unificationVars, List.mem_append]
      rcases equationMember with rfl | tailMember
      · exact Or.inl candidateMember
      · exact Or.inr (induction tailMember)

/-- A type whose whole finite support is protected from fresh alias
endpoints is fixed by the accumulated alias substitution. -/
theorem Ty.apply_sequenceSubstitution_eq_self_of_freshEndpointsAvoid
    {support : List UnificationVar} (aliases : List Alias)
    (avoids : FreshEndpointsAvoid support aliases) (target : Ty)
    (contained : ∀ candidate, candidate ∈ target.unificationVars →
      candidate ∈ support) :
    target.apply (sequenceSubstitution aliases) = target := by
  calc
    target.apply (sequenceSubstitution aliases) = target.apply Subst.id := by
      apply Ty.apply_eq_of_agree target
      · intro index member
        exact sequenceSubstitution_ty_eq_var_of_freshEndpointsAvoid
          aliases avoids index
            (contained (.ty index)
              ((Ty.mem_tyVars_iff_unificationVars index target).mp member))
      · intro index member
        exact sequenceSubstitution_cap_eq_var_of_freshEndpointsAvoid
          aliases avoids index
            (contained (.cap index)
              ((Ty.mem_capVars_iff_unificationVars index target).mp member))
    _ = target := Ty.apply_id target

/-- Capability counterpart of
`Ty.apply_sequenceSubstitution_eq_self_of_freshEndpointsAvoid`. -/
theorem Cap.apply_sequenceSubstitution_eq_self_of_freshEndpointsAvoid
    {support : List UnificationVar} (aliases : List Alias)
    (avoids : FreshEndpointsAvoid support aliases) (capability : Cap)
    (contained : ∀ candidate, candidate ∈ capability.unificationVars →
      candidate ∈ support) :
    capability.apply (sequenceSubstitution aliases).cap = capability := by
  calc
    capability.apply (sequenceSubstitution aliases).cap =
        capability.apply Subst.id.cap := by
      apply Cap.apply_eq_of_agree capability
      intro index member
      exact sequenceSubstitution_cap_eq_var_of_freshEndpointsAvoid
        aliases avoids index
          (contained (.cap index)
            ((Cap.mem_capVars_iff_unificationVars index capability).mp member))
    _ = capability := Cap.apply_id capability

/-- Every equation, hence in particular every interface right-hand side, is
fixed by an alias sequence whose fresh endpoints avoid the equation list. -/
theorem equations_map_apply_sequenceSubstitution_eq_self
    (aliases : List Alias) (equations : List Equation)
    (avoids : FreshEndpointsAvoid
      (TypePM.unificationVars equations) aliases) :
    equations.map (Equation.apply (sequenceSubstitution aliases)) =
      equations := by
  have mapped :
      equations.map (Equation.apply (sequenceSubstitution aliases)) =
        equations.map id := by
    apply List.map_congr_left
    intro equation equationMember
    have contained : ∀ candidate,
        candidate ∈ equation.unificationVars →
          candidate ∈ TypePM.unificationVars equations := by
      intro candidate candidateMember
      exact mem_unificationVars_of_equation_mem equationMember candidateMember
    cases equation with
    | ty left right =>
        simp only [Equation.apply, id_eq]
        rw [Ty.apply_sequenceSubstitution_eq_self_of_freshEndpointsAvoid
          aliases avoids left (fun candidate member =>
            contained candidate (List.mem_append_left _ member))]
        rw [Ty.apply_sequenceSubstitution_eq_self_of_freshEndpointsAvoid
          aliases avoids right (fun candidate member =>
            contained candidate (List.mem_append_right _ member))]
    | cap left right =>
        simp only [Equation.apply, id_eq]
        rw [Cap.apply_sequenceSubstitution_eq_self_of_freshEndpointsAvoid
          aliases avoids left (fun candidate member =>
            contained candidate (List.mem_append_left _ member))]
        rw [Cap.apply_sequenceSubstitution_eq_self_of_freshEndpointsAvoid
          aliases avoids right (fun candidate member =>
            contained candidate (List.mem_append_right _ member))]
  exact mapped.trans (List.map_id equations)

/-- Interface-specialized form exposing literal fixedness of every left- and
right-hand side under the accumulated alias substitution. -/
theorem Context.interfaceEquations_map_apply_sequenceSubstitution_eq_self
    (context : Context) (block : Subst) (aliases : List Alias)
    (avoids : FreshEndpointsAvoid
      (TypePM.unificationVars (context.interfaceEquations block)) aliases) :
    (context.interfaceEquations block).map
        (Equation.apply (sequenceSubstitution aliases)) =
      context.interfaceEquations block :=
  equations_map_apply_sequenceSubstitution_eq_self aliases
    (context.interfaceEquations block) avoids

/-- Every variable free in a source context occurs on the left of its
interface equations, independently of the chosen block substitution. -/
theorem Context.unificationVars_subset_interfaceEquations
    (context : Context) (block : Subst) :
    ∀ candidate, candidate ∈ context.unificationVars →
      candidate ∈ TypePM.unificationVars
        (context.interfaceEquations block) := by
  intro candidate member
  cases candidate with
  | ty index =>
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
        at member
      rcases member with tyMember | capMember
      · obtain ⟨source, sourceMember, equality⟩ := tyMember
        injection equality with indexEquality
        subst source
        apply mem_unificationVars_of_equation_mem
          (equation := .ty (.var index) (block.ty index))
        · apply List.mem_append_left
          exact List.mem_map.mpr ⟨index, sourceMember, rfl⟩
        · simp [Equation.unificationVars, Ty.unificationVars]
      · obtain ⟨source, _sourceMember, equality⟩ := capMember
        cases equality
  | cap index =>
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
        at member
      rcases member with tyMember | capMember
      · obtain ⟨source, _sourceMember, equality⟩ := tyMember
        cases equality
      · obtain ⟨source, sourceMember, equality⟩ := capMember
        injection equality with indexEquality
        subst source
        apply mem_unificationVars_of_equation_mem
          (equation := .cap (.var index) (block.cap index))
        · apply List.mem_append_right
          exact List.mem_map.mpr ⟨index, sourceMember, rfl⟩
        · simp [Equation.unificationVars, Cap.unificationVars]

/-- Avoiding all variables of the original interface is enough for the
accumulated alias substitution to leave the block substitution unchanged on
all free variables of the source context. -/
theorem contextSubstitutionsAgree_of_freshEndpointsAvoid_interface
    (aliases : List Alias) {generated : Generated}
    (closure : PrincipalBlockClosure generated) (context : Context)
    (avoids : FreshEndpointsAvoid
      (TypePM.unificationVars
        (context.interfaceEquations closure.substitution)) aliases) :
    context.SubstitutionsAgree
      (Subst.compose closure.substitution (sequenceSubstitution aliases))
      closure.substitution := by
  constructor
  · intro index member
    have supported : .ty index ∈ TypePM.unificationVars
        (context.interfaceEquations closure.substitution) :=
      Context.unificationVars_subset_interfaceEquations context
        closure.substitution (.ty index) (by
          simp [Context.unificationVars, member])
    change ((sequenceSubstitution aliases).ty index).apply
      closure.substitution = closure.substitution.ty index
    rw [sequenceSubstitution_ty_eq_var_of_freshEndpointsAvoid
      aliases avoids index supported]
    rfl
  · intro index member
    have supported : .cap index ∈ TypePM.unificationVars
        (context.interfaceEquations closure.substitution) :=
      Context.unificationVars_subset_interfaceEquations context
        closure.substitution (.cap index) (by
          simp [Context.unificationVars, member])
    change ((sequenceSubstitution aliases).cap index).apply
      closure.substitution.cap = closure.substitution.cap index
    rw [sequenceSubstitution_cap_eq_var_of_freshEndpointsAvoid
      aliases avoids index supported]
    rfl

/-- Agreement on source-context variables gives literal equality of the
finite interface equation lists. -/
theorem Context.interfaceEquations_eq_of_substitutionsAgree
    (context : Context) {left right : Subst}
    (agree : context.SubstitutionsAgree left right) :
    context.interfaceEquations left = context.interfaceEquations right := by
  simp only [Context.interfaceEquations]
  congr 1
  · apply List.map_congr_left
    intro index member
    rw [agree.1 index member]
  · apply List.map_congr_left
    intro index member
    rw [agree.2 index member]

/-- Direct source-freshness endpoint: if no alias fresh endpoint occurs in
the original finite interface, both fields required to erase the accumulated
alias substitution follow automatically. -/
theorem cumulativeAliasContextFixed_of_freshEndpointsAvoid_interface
    (aliases : List Alias) {generated : Generated}
    (closure : PrincipalBlockClosure generated) (context : Context)
    (avoids : FreshEndpointsAvoid
      (TypePM.unificationVars
        (context.interfaceEquations closure.substitution)) aliases) :
    CumulativeAliasContextFixed aliases closure context := by
  have agree := contextSubstitutionsAgree_of_freshEndpointsAvoid_interface
    aliases closure context avoids
  exact
    { closedContext :=
        Context.applyFree_eq_of_substitutionsAgree agree
      interfaceEquations :=
        Context.interfaceEquations_eq_of_substitutionsAgree context agree }

/-- `InterfaceAliasFreshness`'s `ScopedBy` certificate discharges cumulative
context preservation once the original interface support is included in the
certificate's support. -/
theorem cumulativeAliasContextFixed_of_scopedBy
    {support : List UnificationVar} (aliases : List Alias)
    {generated : Generated} (closure : PrincipalBlockClosure generated)
    (context : Context) (scopeProof : ScopedBy support aliases)
    (interfaceSupported : ∀ candidate,
      candidate ∈ TypePM.unificationVars
        (context.interfaceEquations closure.substitution) →
      candidate ∈ support) :
    CumulativeAliasContextFixed aliases closure context := by
  apply cumulativeAliasContextFixed_of_freshEndpointsAvoid_interface
  exact FreshEndpointsAvoid.of_scopedBy scopeProof interfaceSupported

/-- Source-facing endpoint avoiding the generally false requirement that the
whole interface be contained in generated support.  An interface variable is
either inherited from the well-formed outer context or occurs in an image of
the localized closure substitution.  Fresh-interval separation excludes the
first case and `ScopedBy` excludes the second. -/
theorem cumulativeAliasContextFixed_of_scopedBy_sourceFresh
    (aliases : List Alias) {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) (context : Context)
    (start finish : Supply) (wellFormed : start.WellFormedFor context)
    (scopeProof : ScopedBy generated.unificationVars aliases)
    (freshIn : ∀ alias, alias ∈ aliases →
      (freshVariable alias).FreshIn start finish) :
    CumulativeAliasContextFixed aliases closure context := by
  apply cumulativeAliasContextFixed_of_freshEndpointsAvoid_interface
  intro alias aliasMember interfaceMember
  have endpointOutside := (scopeProof.2 alias aliasMember).1
  have endpointFresh := freshIn alias aliasMember
  have contextOutside : freshVariable alias ∉ context.unificationVars := by
    intro contextMember
    generalize endpointEquality : freshVariable alias = endpoint at contextMember endpointFresh
    have belowInitial :=
      Context.member_unificationVars_below_initialSupply contextMember
    cases endpoint with
    | ty index =>
        exact (Nat.not_le_of_gt
          (Nat.lt_of_lt_of_le belowInitial wellFormed.1)) endpointFresh.1
    | cap index =>
        exact (Nat.not_le_of_gt
          (Nat.lt_of_lt_of_le belowInitial wellFormed.2)) endpointFresh.1
  rcases Context.interfaceEquations_support_origin context
      closure.substitution interfaceMember with
    inherited | tyImage | capImage
  · exact contextOutside inherited
  · obtain ⟨input, inputMember, imageMember⟩ := tyImage
    by_cases supported : .ty input ∈ generated.unificationVars
    · exact endpointOutside
        ((closure.localized_of_absorbing absorbing).tyRange
          input supported (freshVariable alias) imageMember)
    · rw [(closure.localized_of_absorbing absorbing).fixesTy
          input supported] at imageMember
      have equality : freshVariable alias = .ty input := by
        simpa [Ty.unificationVars] using imageMember
      apply contextOutside
      rw [equality]
      simp [Context.unificationVars, inputMember]
  · obtain ⟨input, inputMember, imageMember⟩ := capImage
    by_cases supported : .cap input ∈ generated.unificationVars
    · exact endpointOutside
        ((closure.localized_of_absorbing absorbing).capRange
          input supported (freshVariable alias) imageMember)
    · rw [(closure.localized_of_absorbing absorbing).fixesCap
          input supported] at imageMember
      have equality : freshVariable alias = .cap input := by
        simpa [Cap.unificationVars] using imageMember
      apply contextOutside
      rw [equality]
      simp [Context.unificationVars, inputMember]

namespace InterfaceAliasDecomposition.Automatic.FreshClosureInterfaceDecomposition

/-- Left-side specialization for the automatically constructed scoped
interface decomposition. -/
theorem leftCumulativeAliasContextFixed
    {generated : Generated}
    {left right : PrincipalBlockClosure generated} {context : Context}
    (certificate : FreshClosureInterfaceDecomposition left right context)
    (interfaceSupported : ∀ candidate,
      candidate ∈ TypePM.unificationVars
        (context.interfaceEquations left.substitution) →
      candidate ∈ certificate.support) :
    CumulativeAliasContextFixed
      certificate.decomposition.equations.leftAliases left context :=
  cumulativeAliasContextFixed_of_scopedBy
    certificate.decomposition.equations.leftAliases left context
    certificate.leftScoped interfaceSupported

/-- Right-side specialization for the automatically constructed scoped
interface decomposition. -/
theorem rightCumulativeAliasContextFixed
    {generated : Generated}
    {left right : PrincipalBlockClosure generated} {context : Context}
    (certificate : FreshClosureInterfaceDecomposition left right context)
    (interfaceSupported : ∀ candidate,
      candidate ∈ TypePM.unificationVars
        (context.interfaceEquations right.substitution) →
      candidate ∈ certificate.support) :
    CumulativeAliasContextFixed
      certificate.decomposition.equations.rightAliases right context :=
  cumulativeAliasContextFixed_of_scopedBy
    certificate.decomposition.equations.rightAliases right context
    certificate.rightScoped interfaceSupported

end InterfaceAliasDecomposition.Automatic.FreshClosureInterfaceDecomposition

end TypePM.Source
