import TypePM.Checking
import TypePM.Unification

/-!
# Normalized resolution of delayed checking obligations

`resolve` is applied only after the saturated hard substitution.  It inspects
the resulting outer constructors, but it does not solve the equalities between
the types and capabilities inside those constructors.  Those equalities are
returned as a worklist for the ordinary unifier.

An unresolved expected variable always takes the ordinary branch.  In
particular, this module never instantiates such a variable to `matcher` or
`slot` merely to make a special conversion applicable.
-/

namespace TypePM

/-- The two unitary branches of a capability demand.  The `rootedAny` branch
is available only when the normalized consumer is already syntactically
`Cap.any`; otherwise resolution emits an equality. -/
inductive CapabilityResolution : Cap → Cap → Type where
  | equal {producer consumer : Cap} :
      CapabilityResolution producer consumer
  | rootedAny {producer : Cap} :
      CapabilityResolution producer .any

namespace CapabilityResolution

def isRootedAny {producer consumer : Cap} :
    CapabilityResolution producer consumer → Bool
  | .equal => false
  | .rootedAny => true

def equations {producer consumer : Cap} :
    CapabilityResolution producer consumer → List Equation
  | .equal => [.cap producer consumer]
  | .rootedAny => []

theorem sound
    {producer consumer : Cap}
    (resolution : CapabilityResolution producer consumer)
    {substitution : Subst}
    (solved : Solves substitution resolution.equations) :
    CapabilityDemand
      (producer.apply substitution.cap)
      (consumer.apply substitution.cap) := by
  cases resolution with
  | equal =>
      have equality :
          producer.apply substitution.cap =
            consumer.apply substitution.cap := by
        simpa [CapabilityResolution.equations, Solves, Equation.Holds]
          using solved
      rw [equality]
      exact .equal
  | rootedAny =>
      exact .any

end CapabilityResolution

/-- A resolution is indexed by the normalized source and expected types that
it classifies.  Product constructors contain a proof of nonemptiness because
the empty product has no matcher-product conversion. -/
inductive Resolution : Ty → Ty → Type where
  | ordinary (source expected : Ty) :
      Resolution source expected
  | matcherToSlot
      (producer consumer : Cap) (sourceTarget expectedTarget : Ty)
      (capability : CapabilityResolution producer consumer) :
      Resolution
        (.matcher producer sourceTarget)
        (.slot consumer expectedTarget)
  | productMatcher
      (items : List Ty) (duals : List Dual)
      (types_eq : duals.map Dual.matcherType = items)
      (nonempty : duals ≠ [])
      (expectedCapability : Cap) (expectedTarget : Ty) :
      Resolution
        (.prod items)
        (.matcher expectedCapability expectedTarget)
  | productMatcherToSlot
      (items : List Ty) (duals : List Dual)
      (types_eq : duals.map Dual.matcherType = items)
      (nonempty : duals ≠ [])
      (consumer : Cap) (expectedTarget : Ty)
      (capability :
        CapabilityResolution (.prod (Dual.capabilities duals)) consumer) :
      Resolution
        (.prod items)
        (.slot consumer expectedTarget)

namespace Resolution

/-- The complete branch selected by normalized resolution.  Unlike
`ConversionClass`, this also records whether a slot consumer was the rigid
`Any` root or generated a residual capability equality. -/
inductive Branch where
  | ordinary
  | matcherToSlotEqual
  | matcherToSlotAny
  | productMatcher
  | productMatcherToSlotEqual
  | productMatcherToSlotAny
deriving Repr, DecidableEq

def branch {source expected : Ty} :
    Resolution source expected → Branch
  | .ordinary _ _ => .ordinary
  | .matcherToSlot _ _ _ _ capability =>
      if capability.isRootedAny then .matcherToSlotAny
      else .matcherToSlotEqual
  | .productMatcher _ _ _ _ _ _ => .productMatcher
  | .productMatcherToSlot _ _ _ _ _ _ capability =>
      if capability.isRootedAny then .productMatcherToSlotAny
      else .productMatcherToSlotEqual

def conversionClass {source expected : Ty} :
    Resolution source expected → ConversionClass
  | .ordinary _ _ => .ordinary
  | .matcherToSlot _ _ _ _ _ => .matcherToSlot
  | .productMatcher _ _ _ _ _ _ => .productMatcher
  | .productMatcherToSlot _ _ _ _ _ _ _ => .productMatcherToSlot

/-- Equalities deliberately left for the ordinary two-sort unifier. -/
def equations {source expected : Ty} :
    Resolution source expected → List Equation
  | .ordinary source expected => [.ty source expected]
  | .matcherToSlot _ _ sourceTarget expectedTarget capability =>
      capability.equations ++ [.ty sourceTarget expectedTarget]
  | .productMatcher _ duals _ _ expectedCapability expectedTarget =>
      [ .cap (.prod (Dual.capabilities duals)) expectedCapability,
        .ty (.prod (Dual.targets duals)) expectedTarget ]
  | .productMatcherToSlot _ duals _ _ _ expectedTarget capability =>
      capability.equations ++
        [.ty (.prod (Dual.targets duals)) expectedTarget]

/-- Special means that checking changes the outer type constructor. -/
def Special {source expected : Ty}
    (resolution : Resolution source expected) : Prop :=
  match resolution with
  | .ordinary _ _ => False
  | _ => True

end Resolution

private structure MatcherItems (items : List Ty) where
  duals : List Dual
  types_eq : duals.map Dual.matcherType = items

private def matcherItems? :
    (items : List Ty) → Option (MatcherItems items)
  | [] => some ⟨[], rfl⟩
  | .matcher capability target :: items =>
      match matcherItems? items with
      | none => none
      | some rest =>
          some
            { duals := ⟨capability, target⟩ :: rest.duals
              types_eq := by simp [Dual.matcherType, rest.types_eq] }
  | _ :: _ => none

private structure MatcherProduct (items : List Ty)
    extends MatcherItems items where
  nonempty : duals ≠ []

private def matcherProduct? :
    (items : List Ty) → Option (MatcherProduct items)
  | [] => none
  | .matcher capability target :: items =>
      match matcherItems? items with
      | none => none
      | some rest =>
          some
            { duals := ⟨capability, target⟩ :: rest.duals
              types_eq := by simp [Dual.matcherType, rest.types_eq]
              nonempty := by simp }
  | _ :: _ => none

private def capabilityResolution (producer consumer : Cap) :
    CapabilityResolution producer consumer :=
  match consumer with
  | .any => .rootedAny
  | .var _ => .equal
  | .prod _ => .equal

/-- Classify one obligation after applying the saturated hard substitution.

The function is total at this layer: unsupported outer shapes fall back to an
ordinary equality, whose consistency is decided by the ordinary unifier.
-/
def resolve :
    (source expected : Ty) → Resolution source expected
  | .matcher producer sourceTarget, .slot consumer expectedTarget =>
      .matcherToSlot producer consumer sourceTarget expectedTarget
        (capabilityResolution producer consumer)
  | .prod items, .matcher expectedCapability expectedTarget =>
      match matcherProduct? items with
      | none => .ordinary (.prod items)
          (.matcher expectedCapability expectedTarget)
      | some product =>
          .productMatcher items product.duals product.types_eq
            product.nonempty expectedCapability expectedTarget
  | .prod items, .slot consumer expectedTarget =>
      match matcherProduct? items with
      | none => .ordinary (.prod items) (.slot consumer expectedTarget)
      | some product =>
          .productMatcherToSlot items product.duals product.types_eq
            product.nonempty consumer expectedTarget
            (capabilityResolution
              (.prod (Dual.capabilities product.duals)) consumer)
  | source, expected => .ordinary source expected

namespace Resolution

private def Dual.apply (substitution : Subst) (dual : Dual) : Dual :=
  ⟨dual.capability.apply substitution.cap, dual.target.apply substitution⟩

private theorem matcherTypes_apply
    (substitution : Subst) (duals : List Dual) :
    Ty.applyList substitution (duals.map Dual.matcherType) =
      (duals.map (Dual.apply substitution)).map Dual.matcherType := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [Ty.applyList, Ty.apply, Dual.matcherType, Dual.apply, induction]

private theorem capabilities_apply
    (substitution : Subst) (duals : List Dual) :
    Cap.applyList substitution.cap (Dual.capabilities duals) =
      Dual.capabilities (duals.map (Dual.apply substitution)) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp only [Dual.capabilities, List.map_cons, List.map_map] at induction ⊢
      simp [Cap.applyList, Dual.apply, Function.comp_def, induction]

private theorem targets_apply
    (substitution : Subst) (duals : List Dual) :
    Ty.applyList substitution (Dual.targets duals) =
      Dual.targets (duals.map (Dual.apply substitution)) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp only [Dual.targets, List.map_cons, List.map_map] at induction ⊢
      simp [Ty.applyList, Dual.apply, Function.comp_def, induction]

private theorem Dual.matcherType_injective :
    Function.Injective Dual.matcherType := by
  intro left right equality
  cases left with
  | mk leftCapability leftTarget =>
      cases right with
      | mk rightCapability rightTarget =>
          simp only [Dual.matcherType] at equality
          injection equality with capabilityEquality targetEquality
          cases capabilityEquality
          cases targetEquality
          rfl

private theorem matcherTypes_injective :
    Function.Injective (List.map Dual.matcherType) := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right with
      | nil => rfl
      | cons => simp at equality
  | cons item items induction =>
      intro right equality
      cases right with
      | nil => simp at equality
      | cons other others =>
          simp only [List.map_cons] at equality
          injection equality with headEquality tailEquality
          have itemEquality := Dual.matcherType_injective headEquality
          have itemsEquality := induction tailEquality
          cases itemEquality
          cases itemsEquality
          rfl

private theorem matcherItems?_matcherTypes (duals : List Dual) :
    ∃ parsed, matcherItems? (duals.map Dual.matcherType) = some parsed := by
  induction duals with
  | nil =>
      exact ⟨⟨[], rfl⟩, rfl⟩
  | cons dual duals induction =>
      obtain ⟨rest, restEquality⟩ := induction
      exact ⟨_, by
        simp only [List.map_cons, Dual.matcherType, matcherItems?]
        rw [restEquality]⟩

private theorem matcherProduct?_matcherTypes
    (duals : List Dual) (nonempty : duals ≠ []) :
    ∃ parsed, matcherProduct? (duals.map Dual.matcherType) = some parsed := by
  cases duals with
  | nil => exact (nonempty rfl).elim
  | cons dual duals =>
      obtain ⟨rest, restEquality⟩ := matcherItems?_matcherTypes duals
      exact ⟨_, by
        simp only [List.map_cons, Dual.matcherType, matcherProduct?]
        rw [restEquality]⟩

private theorem matcherProduct?_complete
    {items : List Ty} {duals : List Dual}
    (nonempty : duals ≠ [])
    (typesEquality : duals.map Dual.matcherType = items) :
    ∃ parsed, matcherProduct? items = some parsed := by
  rw [← typesEquality]
  exact matcherProduct?_matcherTypes duals nonempty

private theorem matcherProduct_duals_unique
    {items : List Ty} (left right : MatcherProduct items) :
    left.duals = right.duals := by
  apply matcherTypes_injective
  exact left.types_eq.trans right.types_eq.symm

private theorem matcherProduct?_apply
    (substitution : Subst) {items : List Ty}
    (parsed : MatcherProduct items) :
    ∃ applied,
      matcherProduct? (Ty.applyList substitution items) = some applied ∧
      applied.duals = parsed.duals.map (Dual.apply substitution) := by
  have nonempty : parsed.duals.map (Dual.apply substitution) ≠ [] := by
    simpa using parsed.nonempty
  have typesEquality :
      (parsed.duals.map (Dual.apply substitution)).map Dual.matcherType =
        Ty.applyList substitution items := by
    calc
      (parsed.duals.map (Dual.apply substitution)).map Dual.matcherType =
          Ty.applyList substitution
            (parsed.duals.map Dual.matcherType) :=
        (matcherTypes_apply substitution parsed.duals).symm
      _ = Ty.applyList substitution items :=
        congrArg (Ty.applyList substitution) parsed.types_eq
  obtain ⟨applied, parsedApplied⟩ :=
    matcherProduct?_complete nonempty typesEquality
  refine ⟨applied, parsedApplied, ?_⟩
  apply matcherTypes_injective
  exact applied.types_eq.trans typesEquality.symm

private theorem matcherProduct?_none_apply_of_retract
    (post retract : Subst) {items : List Ty}
    (itemsRetract :
      Ty.applyList retract (Ty.applyList post items) = items)
    (notParsed : matcherProduct? items = none) :
    matcherProduct? (Ty.applyList post items) = none := by
  cases parsedApplied : matcherProduct? (Ty.applyList post items) with
  | none => rfl
  | some applied =>
      have nonempty : applied.duals.map (Dual.apply retract) ≠ [] := by
        simpa using applied.nonempty
      have typesEquality :
          (applied.duals.map (Dual.apply retract)).map Dual.matcherType =
            items := by
        calc
          (applied.duals.map (Dual.apply retract)).map Dual.matcherType =
              Ty.applyList retract
                (applied.duals.map Dual.matcherType) :=
            (matcherTypes_apply retract applied.duals).symm
          _ = Ty.applyList retract (Ty.applyList post items) :=
            congrArg (Ty.applyList retract) applied.types_eq
          _ = items := itemsRetract
      obtain ⟨parsed, parsedOriginal⟩ :=
        matcherProduct?_complete nonempty typesEquality
      rw [notParsed] at parsedOriginal
      contradiction

private theorem Ty.var_image_is_var_of_retract
    (post retract : Subst) (index : TyVar)
    (retracts : ((Ty.var index).apply post).apply retract = .var index) :
    ∃ candidate, post.ty index = .var candidate := by
  cases imageEquality : post.ty index with
  | var candidate => exact ⟨candidate, rfl⟩
  | int => simp [Ty.apply, imageEquality] at retracts
  | fn => simp [Ty.apply, imageEquality] at retracts
  | prod => simp [Ty.apply, imageEquality] at retracts
  | matcher => simp [Ty.apply, imageEquality] at retracts
  | slot => simp [Ty.apply, imageEquality] at retracts

private theorem Cap.var_image_is_var_of_retract
    (post retract : Subst) (index : CapVar)
    (retracts :
      ((Cap.var index).apply post.cap).apply retract.cap = .var index) :
    ∃ candidate, post.cap index = .var candidate := by
  cases imageEquality : post.cap index with
  | var candidate => exact ⟨candidate, rfl⟩
  | any => simp [Cap.apply, imageEquality] at retracts
  | prod => simp [Cap.apply, imageEquality] at retracts

private theorem capabilityResolution_branch_apply_of_retract
    (post retract : Subst) (producer consumer : Cap)
    (consumerRetracts :
      (consumer.apply post.cap).apply retract.cap = consumer) :
    (capabilityResolution producer consumer).isRootedAny =
      (capabilityResolution
        (producer.apply post.cap) (consumer.apply post.cap)).isRootedAny := by
  cases consumer with
  | any => rfl
  | prod => rfl
  | var index =>
      obtain ⟨candidate, imageEquality⟩ :=
        Cap.var_image_is_var_of_retract post retract index consumerRetracts
      rw [show (Cap.var index).apply post.cap = .var candidate by
        simpa [Cap.apply] using imageEquality]
      rfl

private theorem capabilityResolution_equations_apply_of_retract
    (post retract : Subst) (producer consumer : Cap)
    (consumerRetracts :
      (consumer.apply post.cap).apply retract.cap = consumer) :
    (capabilityResolution
        (producer.apply post.cap) (consumer.apply post.cap)).equations =
      (capabilityResolution producer consumer).equations.map
        (Equation.apply post) := by
  cases consumer with
  | any => rfl
  | prod => rfl
  | var index =>
      obtain ⟨candidate, imageEquality⟩ :=
        Cap.var_image_is_var_of_retract post retract index consumerRetracts
      rw [show (Cap.var index).apply post.cap = .var candidate by
        simpa [Cap.apply] using imageEquality]
      simp [capabilityResolution, CapabilityResolution.equations,
        Equation.apply, Cap.apply, imageEquality]

private theorem resolve_matcher_slot_apply_canonical_of_retract
    (post retract : Subst)
    (producer consumer : Cap) (sourceTarget expectedTarget : Ty)
    (consumerRetracts :
      (consumer.apply post.cap).apply retract.cap = consumer) :
    (resolve (Ty.matcher producer sourceTarget)
        (Ty.slot consumer expectedTarget)).branch =
      (resolve
        ((Ty.matcher producer sourceTarget).apply post)
        ((Ty.slot consumer expectedTarget).apply post)).branch ∧
    (resolve
        ((Ty.matcher producer sourceTarget).apply post)
        ((Ty.slot consumer expectedTarget).apply post)).equations =
      (resolve (Ty.matcher producer sourceTarget)
        (Ty.slot consumer expectedTarget)).equations.map
          (Equation.apply post) := by
  have branchEquality := capabilityResolution_branch_apply_of_retract
    post retract producer consumer consumerRetracts
  have equationsEquality := capabilityResolution_equations_apply_of_retract
    post retract producer consumer consumerRetracts
  constructor
  · simp only [Ty.apply, resolve, Resolution.branch]
    rw [branchEquality]
  · simp only [Ty.apply, resolve, Resolution.equations,
      List.map_append, List.map_cons, List.map_nil, Equation.apply]
    rw [equationsEquality]

private theorem resolve_product_matcher_apply_canonical_of_retract
    (post retract : Subst) (items : List Ty)
    (expectedCapability : Cap) (expectedTarget : Ty)
    (itemsRetract :
      Ty.applyList retract (Ty.applyList post items) = items) :
    (resolve (Ty.prod items)
        (Ty.matcher expectedCapability expectedTarget)).branch =
      (resolve
        ((Ty.prod items).apply post)
        ((Ty.matcher expectedCapability expectedTarget).apply post)).branch ∧
    (resolve
        ((Ty.prod items).apply post)
        ((Ty.matcher expectedCapability expectedTarget).apply post)).equations =
      (resolve (Ty.prod items)
        (Ty.matcher expectedCapability expectedTarget)).equations.map
          (Equation.apply post) := by
  cases parsedOriginal : matcherProduct? items with
  | none =>
      have parsedApplied := matcherProduct?_none_apply_of_retract
        post retract itemsRetract parsedOriginal
      simp [Ty.apply, resolve, parsedOriginal, parsedApplied,
        Resolution.branch, Resolution.equations, Equation.apply]
  | some original =>
      obtain ⟨applied, parsedApplied, dualsEquality⟩ :=
        matcherProduct?_apply post original
      constructor
      · simp [Ty.apply, resolve, parsedOriginal, parsedApplied,
          Resolution.branch]
      · simp only [Ty.apply, resolve]
        rw [parsedOriginal, parsedApplied]
        simp only [Resolution.equations, List.map_cons, List.map_nil,
          Equation.apply]
        rw [dualsEquality]
        simp [Cap.apply, Ty.apply, capabilities_apply, targets_apply]

private theorem resolve_product_slot_apply_canonical_of_retract
    (post retract : Subst) (items : List Ty)
    (consumer : Cap) (expectedTarget : Ty)
    (itemsRetract :
      Ty.applyList retract (Ty.applyList post items) = items)
    (consumerRetracts :
      (consumer.apply post.cap).apply retract.cap = consumer) :
    (resolve (Ty.prod items)
        (Ty.slot consumer expectedTarget)).branch =
      (resolve
        ((Ty.prod items).apply post)
        ((Ty.slot consumer expectedTarget).apply post)).branch ∧
    (resolve
        ((Ty.prod items).apply post)
        ((Ty.slot consumer expectedTarget).apply post)).equations =
      (resolve (Ty.prod items)
        (Ty.slot consumer expectedTarget)).equations.map
          (Equation.apply post) := by
  cases parsedOriginal : matcherProduct? items with
  | none =>
      have parsedApplied := matcherProduct?_none_apply_of_retract
        post retract itemsRetract parsedOriginal
      simp [Ty.apply, resolve, parsedOriginal, parsedApplied,
        Resolution.branch, Resolution.equations, Equation.apply]
  | some original =>
      obtain ⟨applied, parsedApplied, dualsEquality⟩ :=
        matcherProduct?_apply post original
      have producerEquality :
          Cap.prod (Dual.capabilities applied.duals) =
            (Cap.prod (Dual.capabilities original.duals)).apply post.cap := by
        rw [dualsEquality]
        simp [Cap.apply, capabilities_apply]
      have branchEquality := capabilityResolution_branch_apply_of_retract
        post retract (.prod (Dual.capabilities original.duals)) consumer
        consumerRetracts
      have equationsEquality :=
        capabilityResolution_equations_apply_of_retract
          post retract (.prod (Dual.capabilities original.duals)) consumer
          consumerRetracts
      constructor
      · simp only [Ty.apply, resolve]
        rw [parsedOriginal, parsedApplied]
        simp only [Resolution.branch]
        rw [producerEquality, ← branchEquality]
      · simp only [Ty.apply, resolve]
        rw [parsedOriginal, parsedApplied]
        simp only [Resolution.equations, List.map_append, List.map_cons,
          List.map_nil, Equation.apply]
        rw [producerEquality, equationsEquality, dualsEquality]
        simp [Ty.apply, targets_apply]

/-- Resolution commutes with a substitution that has a retraction on the two
classified types.  The reverse map rules out a variable acquiring a rigid
matcher, slot, product-item, or `Any` head only in the later representative. -/
theorem resolve_apply_canonical_of_retract
    (post retract : Subst) (source expected : Ty)
    (sourceRetracts : (source.apply post).apply retract = source)
    (expectedRetracts : (expected.apply post).apply retract = expected) :
    (resolve source expected).branch =
      (resolve (source.apply post) (expected.apply post)).branch ∧
    (resolve (source.apply post) (expected.apply post)).equations =
      (resolve source expected).equations.map (Equation.apply post) := by
  cases source with
  | var index =>
      obtain ⟨candidate, imageEquality⟩ :=
        Ty.var_image_is_var_of_retract post retract index sourceRetracts
      simp [Ty.apply, imageEquality, resolve, Resolution.branch,
        Resolution.equations, Equation.apply]
  | int =>
      simp [Ty.apply, resolve, Resolution.branch,
        Resolution.equations, Equation.apply]
  | fn domain codomain =>
      simp [Ty.apply, resolve, Resolution.branch,
        Resolution.equations, Equation.apply]
  | slot capability target =>
      simp [Ty.apply, resolve, Resolution.branch,
        Resolution.equations, Equation.apply]
  | matcher producer sourceTarget =>
      cases expected with
      | var index =>
          obtain ⟨candidate, imageEquality⟩ :=
            Ty.var_image_is_var_of_retract post retract index expectedRetracts
          simp [Ty.apply, imageEquality, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | int =>
          simp [Ty.apply, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | fn domain codomain =>
          simp [Ty.apply, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | prod items =>
          simp [Ty.apply, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | matcher capability target =>
          simp [Ty.apply, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | slot consumer expectedTarget =>
          have consumerRetracts :
              (consumer.apply post.cap).apply retract.cap = consumer := by
            simp only [Ty.apply] at expectedRetracts
            injection expectedRetracts
          exact resolve_matcher_slot_apply_canonical_of_retract
            post retract producer consumer sourceTarget expectedTarget
            consumerRetracts
  | prod items =>
      have itemsRetract :
          Ty.applyList retract (Ty.applyList post items) = items := by
        simp only [Ty.apply] at sourceRetracts
        injection sourceRetracts
      cases expected with
      | var index =>
          obtain ⟨candidate, imageEquality⟩ :=
            Ty.var_image_is_var_of_retract post retract index expectedRetracts
          simp [Ty.apply, imageEquality, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | int =>
          simp [Ty.apply, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | fn domain codomain =>
          simp [Ty.apply, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | prod expectedItems =>
          simp [Ty.apply, resolve, Resolution.branch,
            Resolution.equations, Equation.apply]
      | matcher expectedCapability expectedTarget =>
          exact resolve_product_matcher_apply_canonical_of_retract
            post retract items expectedCapability expectedTarget itemsRetract
      | slot consumer expectedTarget =>
          have consumerRetracts :
              (consumer.apply post.cap).apply retract.cap = consumer := by
            simp only [Ty.apply] at expectedRetracts
            injection expectedRetracts
          exact resolve_product_slot_apply_canonical_of_retract
            post retract items consumer expectedTarget itemsRetract
            consumerRetracts

/-- Solving the residual equalities makes a normalized resolution a genuine
checking conversion. -/
theorem sound
    {source expected : Ty}
    (resolution : Resolution source expected)
    {substitution : Subst}
    (solved : Solves substitution resolution.equations) :
    CheckConversion resolution.conversionClass
      (source.apply substitution) (expected.apply substitution) := by
  cases resolution with
  | ordinary source expected =>
      have equality :
          source.apply substitution = expected.apply substitution := by
        simpa [Resolution.equations, Solves, Equation.Holds] using solved
      rw [equality]
      exact .ordinary
  | matcherToSlot producer consumer sourceTarget expectedTarget capability =>
      simp only [Resolution.equations] at solved
      obtain ⟨capabilitySolved, targetSolved⟩ :=
        (solves_append substitution _ _).mp solved
      have targetEquality :
          sourceTarget.apply substitution =
            expectedTarget.apply substitution := by
        simpa [Solves, Equation.Holds] using targetSolved
      have demand := capability.sound capabilitySolved
      simpa [Resolution.conversionClass, Ty.apply, targetEquality] using
        (CheckConversion.matcherToSlot demand)
  | productMatcher items duals typesEquality nonempty
      expectedCapability expectedTarget =>
      simp only [Resolution.equations] at solved
      obtain ⟨capabilitySolved, rest⟩ :=
        (solves_cons substitution _ _).mp solved
      obtain ⟨targetSolved, _⟩ :=
        (solves_cons substitution _ _).mp rest
      simp only [Equation.Holds] at capabilitySolved targetSolved
      let applied := duals.map (Dual.apply substitution)
      have appliedNonempty : applied ≠ [] := by
        simpa [applied] using nonempty
      have appliedSourceEquality :
          Ty.applyList substitution items =
            applied.map Dual.matcherType := by
        rw [← typesEquality]
        exact matcherTypes_apply substitution duals
      have expectedCapabilityEquality :
          expectedCapability.apply substitution.cap =
            Cap.prod (Dual.capabilities applied) := by
        rw [← capabilitySolved]
        simp [Cap.apply, applied, capabilities_apply]
      have expectedTargetEquality :
          expectedTarget.apply substitution =
            Ty.prod (Dual.targets applied) := by
        rw [← targetSolved]
        simp [Ty.apply, applied, targets_apply]
      simpa [Resolution.conversionClass, Ty.apply, appliedSourceEquality,
        expectedCapabilityEquality, expectedTargetEquality, applied] using
        (CheckConversion.productMatcher (duals := applied) appliedNonempty)
  | productMatcherToSlot items duals typesEquality nonempty
      consumer expectedTarget capability =>
      simp only [Resolution.equations] at solved
      obtain ⟨capabilitySolved, targetSolved⟩ :=
        (solves_append substitution _ _).mp solved
      have targetEquality :
          (Ty.prod (Dual.targets duals)).apply substitution =
            expectedTarget.apply substitution := by
        simpa [Solves, Equation.Holds] using targetSolved
      let applied := duals.map (Dual.apply substitution)
      have appliedNonempty : applied ≠ [] := by
        simpa [applied] using nonempty
      have appliedSourceEquality :
          Ty.applyList substitution items =
            applied.map Dual.matcherType := by
        rw [← typesEquality]
        exact matcherTypes_apply substitution duals
      have demand := capability.sound capabilitySolved
      have appliedDemand :
          CapabilityDemand
            (Cap.prod (Dual.capabilities applied))
            (consumer.apply substitution.cap) := by
        simpa [Cap.apply, applied, capabilities_apply] using demand
      have expectedTargetEquality :
          expectedTarget.apply substitution =
            Ty.prod (Dual.targets applied) := by
        rw [← targetEquality]
        simp [Ty.apply, applied, targets_apply]
      simpa [Resolution.conversionClass, Ty.apply, appliedSourceEquality,
        expectedTargetEquality, applied] using
        (CheckConversion.productMatcherToSlot
          (duals := applied) appliedNonempty appliedDemand)

/-- Every special normalized resolution has an expected type whose outer
matcher/slot constructor was already explicit before residual solving. -/
theorem special_expected_head
    {source expected : Ty}
    (resolution : Resolution source expected)
    (special : resolution.Special) :
    (∃ capability target, expected = .matcher capability target) ∨
      (∃ capability target, expected = .slot capability target) := by
  cases resolution with
  | ordinary => simp [Resolution.Special] at special
  | matcherToSlot => exact Or.inr ⟨_, _, rfl⟩
  | productMatcher => exact Or.inl ⟨_, _, rfl⟩
  | productMatcherToSlot => exact Or.inr ⟨_, _, rfl⟩

end Resolution

/-- Soundness stated directly for the executable classifier. -/
theorem resolve_sound
    {source expected : Ty}
    {substitution : Subst}
    (solved : Solves substitution (resolve source expected).equations) :
    CheckConversion (resolve source expected).conversionClass
      (source.apply substitution) (expected.apply substitution) :=
  (resolve source expected).sound solved

end TypePM
