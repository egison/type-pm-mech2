import TypePM.Source.SchemeSupportBounds
import TypePM.BlockClosureSupport

/-!
# Provenance and bounds for generated source support

Every variable exposed by source elaboration either comes from the free
variables of the input context or was allocated between the input and output
supplies.  Keeping the lower bound as well as the upper bound is what makes
support sets from sequential sibling elaborations disjoint.
-/

namespace TypePM
namespace Source

namespace Context

/-- The two-sorted finite support of the free variables of a scheme context. -/
def unificationVars (context : Context) : List UnificationVar :=
  context.freeTyVars.map UnificationVar.ty ++
    context.freeCapVars.map UnificationVar.cap

end Context

end Source

namespace GeneratedItems

/-- Support of the list-shaped source generation result. -/
def unificationVars (generated : GeneratedItems) : List UnificationVar :=
  Ty.unificationVarsList generated.targets ++
    TypePM.unificationVars generated.hard ++
      pendingUnificationVars generated.pending

end GeneratedItems

namespace UnificationVar

/-- A variable was allocated in the half-open interval between two source
supplies, in its own variable sort. -/
def FreshIn (start finish : Source.Supply) : UnificationVar → Prop
  | .ty index => start.ty ≤ index.index ∧ index.index < finish.ty
  | .cap index => start.cap ≤ index.index ∧ index.index < finish.cap

theorem FreshIn.below {start finish : Source.Supply}
    {candidate : UnificationVar}
    (fresh : candidate.FreshIn start finish) :
    candidate.Below finish.ty finish.cap := by
  cases candidate <;> exact fresh.2

theorem FreshIn.extend_finish
    {start middle finish : Source.Supply} {candidate : UnificationVar}
    (fresh : candidate.FreshIn start middle)
    (increases : Source.Supply.Le middle finish) :
    candidate.FreshIn start finish := by
  cases candidate with
  | ty index => exact ⟨fresh.1, Nat.lt_of_lt_of_le fresh.2 increases.1⟩
  | cap index => exact ⟨fresh.1, Nat.lt_of_lt_of_le fresh.2 increases.2⟩

theorem FreshIn.lower_start
    {start middle finish : Source.Supply} {candidate : UnificationVar}
    (increases : Source.Supply.Le start middle)
    (fresh : candidate.FreshIn middle finish) :
    candidate.FreshIn start finish := by
  cases candidate with
  | ty index => exact ⟨Nat.le_trans increases.1 fresh.1, fresh.2⟩
  | cap index => exact ⟨Nat.le_trans increases.2 fresh.1, fresh.2⟩

end UnificationVar

namespace Source

/-- Strong support invariant for one generated block. -/
def GeneratedSupportProvenance
    (context : Context) (start finish : Supply) (generated : Generated) : Prop :=
  ∀ candidate, candidate ∈ generated.unificationVars →
    candidate ∈ context.unificationVars ∨ candidate.FreshIn start finish

/-- List counterpart of `Generated.SupportProvenance`. -/
def GeneratedItemsSupportProvenance
    (context : Context) (start finish : Supply)
    (generated : GeneratedItems) : Prop :=
  ∀ candidate, candidate ∈ generated.unificationVars →
    candidate ∈ context.unificationVars ∨ candidate.FreshIn start finish

theorem Context.member_unificationVars_below_initialSupply
    {context : Context} {candidate : UnificationVar}
    (member : candidate ∈ context.unificationVars) :
    candidate.Below context.initialSupply.ty context.initialSupply.cap := by
  simp only [Context.unificationVars, List.mem_append, List.mem_map] at member
  rcases member with tyMember | capMember
  · obtain ⟨index, indexMember, rfl⟩ := tyMember
    exact context.freeTy_index_lt_initialSupply indexMember
  · obtain ⟨index, indexMember, rfl⟩ := capMember
    exact context.freeCap_index_lt_initialSupply indexMember

theorem Context.ty_mem_unificationVars_of_scheme
    {context : Context} {scheme : Scheme} {index : TyVar}
    (schemeMember : scheme ∈ context)
    (indexMember : index ∈ scheme.freeTyVars) :
    .ty index ∈ context.unificationVars := by
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨index, ?_, rfl⟩
  rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
  exact ⟨scheme, schemeMember, indexMember⟩

theorem Context.cap_mem_unificationVars_of_scheme
    {context : Context} {scheme : Scheme} {index : CapVar}
    (schemeMember : scheme ∈ context)
    (indexMember : index ∈ scheme.freeCapVars) :
    .cap index ∈ context.unificationVars := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨index, ?_, rfl⟩
  rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap]
  exact ⟨scheme, schemeMember, indexMember⟩

/-- Applying a localized substitution to a context preserves the same
context-or-fresh provenance split as the substitution's support. -/
theorem Context.applyFree_supportProvenance
    {context : Context} {start finish : Supply}
    {support : List UnificationVar} {substitution : Subst}
    (localized : substitution.Localized support)
    (supportProvenance : ∀ candidate, candidate ∈ support →
      candidate ∈ context.unificationVars ∨
        candidate.FreshIn start finish) :
    ∀ candidate,
      candidate ∈ (context.applyFree substitution).unificationVars →
        candidate ∈ context.unificationVars ∨
          candidate.FreshIn start finish := by
  intro candidate member
  simp only [Context.unificationVars, List.mem_append,
    List.mem_map] at member
  rcases member with tyMember | capMember
  · obtain ⟨candidateIndex, candidateMember, rfl⟩ := tyMember
    obtain ⟨input, inputMember, imageMember⟩ :=
      context.freeTy_applyFree_origin substitution candidateMember
    by_cases inputSupported : .ty input ∈ support
    · exact supportProvenance (.ty candidateIndex)
        (localized.tyRange input inputSupported (.ty candidateIndex) imageMember)
    · rw [localized.fixesTy input inputSupported] at imageMember
      have equality : candidateIndex = input := by
        simpa [Ty.unificationVars] using imageMember
      subst candidateIndex
      exact Or.inl (List.mem_append_left _
        (List.mem_map.mpr ⟨input, inputMember, rfl⟩))
  · obtain ⟨candidateIndex, candidateMember, rfl⟩ := capMember
    rcases context.freeCap_applyFree_origin substitution candidateMember with
      tyOrigin | capOrigin
    · obtain ⟨input, inputMember, imageMember⟩ := tyOrigin
      by_cases inputSupported : .ty input ∈ support
      · exact supportProvenance (.cap candidateIndex)
          (localized.tyRange input inputSupported (.cap candidateIndex)
            imageMember)
      · rw [localized.fixesTy input inputSupported] at imageMember
        simp [Ty.unificationVars] at imageMember
    · obtain ⟨input, inputMember, imageMember⟩ := capOrigin
      by_cases inputSupported : .cap input ∈ support
      · exact supportProvenance (.cap candidateIndex)
          (localized.capRange input inputSupported (.cap candidateIndex)
            imageMember)
      · rw [localized.fixesCap input inputSupported] at imageMember
        have equality : candidateIndex = input := by
          simpa [Cap.unificationVars] using imageMember
        subst candidateIndex
        exact Or.inl (List.mem_append_right _
          (List.mem_map.mpr ⟨input, inputMember, rfl⟩))

theorem Context.generalized_cons_support_subset
    (context : Context) (target : Ty) :
    ∀ candidate,
      candidate ∈ Context.unificationVars
          (context.generalize target :: context) →
        candidate ∈ context.unificationVars := by
  intro candidate member
  simp only [Context.unificationVars, List.mem_append,
    List.mem_map] at member ⊢
  rcases member with tyMember | capMember
  · obtain ⟨index, indexMember, rfl⟩ := tyMember
    apply Or.inl
    refine ⟨index, ?_, rfl⟩
    rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap] at indexMember ⊢
    obtain ⟨scheme, schemeMember, freeMember⟩ := indexMember
    simp only [List.mem_cons] at schemeMember
    rcases schemeMember with rfl | schemeMember
    · have inContext := (Context.mem_generalize_freeTyVars).mp freeMember |>.2
      rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap] at inContext
      exact inContext
    · exact ⟨scheme, schemeMember, freeMember⟩
  · obtain ⟨index, indexMember, rfl⟩ := capMember
    apply Or.inr
    refine ⟨index, ?_, rfl⟩
    rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap] at indexMember ⊢
    obtain ⟨scheme, schemeMember, freeMember⟩ := indexMember
    simp only [List.mem_cons] at schemeMember
    rcases schemeMember with rfl | schemeMember
    · have inContext := (Context.mem_generalize_freeCapVars).mp freeMember |>.2
      rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap] at inContext
      exact inContext
    · exact ⟨scheme, schemeMember, freeMember⟩

theorem Context.mono_ty_cons_support
    (context : Context) (index : TyVar) :
    ∀ candidate,
      candidate ∈ Context.unificationVars
          (Scheme.mono (.var index) :: context) →
        candidate = .ty index ∨ candidate ∈ context.unificationVars := by
  intro candidate member
  simp only [Context.unificationVars, List.mem_append,
    List.mem_map] at member ⊢
  rcases member with tyMember | capMember
  · obtain ⟨candidateIndex, candidateMember, rfl⟩ := tyMember
    rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
      at candidateMember
    obtain ⟨scheme, schemeMember, freeMember⟩ := candidateMember
    simp only [List.mem_cons] at schemeMember
    rcases schemeMember with rfl | schemeMember
    · left
      change candidateIndex ∈ dedupFirst [index] at freeMember
      have equality : candidateIndex = index := by
        have raw := mem_dedupFirst.mp freeMember
        simpa using raw
      subst candidateIndex
      rfl
    · right
      apply Or.inl
      refine ⟨candidateIndex, ?_, rfl⟩
      rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
      exact ⟨scheme, schemeMember, freeMember⟩
  · right
    obtain ⟨candidateIndex, candidateMember, rfl⟩ := capMember
    apply Or.inr
    refine ⟨candidateIndex, ?_, rfl⟩
    rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap]
      at candidateMember ⊢
    obtain ⟨scheme, schemeMember, freeMember⟩ := candidateMember
    simp only [List.mem_cons] at schemeMember
    rcases schemeMember with rfl | schemeMember
    · change candidateIndex ∈ dedupFirst [] at freeMember
      have raw := mem_dedupFirst.mp freeMember
      simp at raw
    · exact ⟨scheme, schemeMember, freeMember⟩
private theorem mem_unificationVars_exists_equation
    {equations : List Equation} {candidate : UnificationVar}
    (member : candidate ∈ TypePM.unificationVars equations) :
    ∃ equation, equation ∈ equations ∧
      candidate ∈ equation.unificationVars := by
  induction equations with
  | nil => simp [TypePM.unificationVars] at member
  | cons equation equations induction =>
      simp only [TypePM.unificationVars, List.mem_append] at member
      rcases member with head | tail
      · exact ⟨equation, by simp, head⟩
      · obtain ⟨origin, originMember, candidateMember⟩ := induction tail
        exact ⟨origin, by simp [originMember], candidateMember⟩

/-- Interface equations expose only original context variables and localized
images of those variables. -/
theorem Context.interface_supportProvenance
    {context : Context} {start finish : Supply}
    {support : List UnificationVar} {substitution : Subst}
    (localized : substitution.Localized support)
    (supportProvenance : ∀ candidate, candidate ∈ support →
      candidate ∈ context.unificationVars ∨
        candidate.FreshIn start finish) :
    ∀ candidate,
      candidate ∈ TypePM.unificationVars
          (context.interfaceEquations substitution) →
        candidate ∈ context.unificationVars ∨
          candidate.FreshIn start finish := by
  intro candidate member
  obtain ⟨equation, equationMember, candidateMember⟩ :=
    mem_unificationVars_exists_equation member
  simp only [Context.interfaceEquations, List.mem_append,
    List.mem_map] at equationMember
  rcases equationMember with tyEquation | capEquation
  · obtain ⟨input, inputMember, rfl⟩ := tyEquation
    simp only [Equation.unificationVars, Ty.unificationVars,
      List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at candidateMember
    rcases candidateMember with rfl | imageMember
    · exact Or.inl (List.mem_append_left _
        (List.mem_map.mpr ⟨input, inputMember, rfl⟩))
    · by_cases inputSupported : .ty input ∈ support
      · exact supportProvenance candidate
          (localized.tyRange input inputSupported candidate imageMember)
      · rw [localized.fixesTy input inputSupported] at imageMember
        have equality : candidate = .ty input := by
          simpa [Ty.unificationVars] using imageMember
        subst candidate
        exact Or.inl (List.mem_append_left _
          (List.mem_map.mpr ⟨input, inputMember, rfl⟩))
  · obtain ⟨input, inputMember, rfl⟩ := capEquation
    simp only [Equation.unificationVars, Cap.unificationVars,
      List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at candidateMember
    rcases candidateMember with rfl | imageMember
    · exact Or.inl (List.mem_append_right _
        (List.mem_map.mpr ⟨input, inputMember, rfl⟩))
    · by_cases inputSupported : .cap input ∈ support
      · exact supportProvenance candidate
          (localized.capRange input inputSupported candidate imageMember)
      · rw [localized.fixesCap input inputSupported] at imageMember
        have equality : candidate = .cap input := by
          simpa [Cap.unificationVars] using imageMember
        subst candidate
        exact Or.inl (List.mem_append_right _
          (List.mem_map.mpr ⟨input, inputMember, rfl⟩))

/-- Provenance immediately supplies the usual strict upper bound when the
starting supply is well formed for the input context. -/
theorem GeneratedSupportProvenance.below
    {context : Context} {start finish : Supply} {generated : Generated}
    (provenance : GeneratedSupportProvenance context start finish generated)
    (wellFormed : start.WellFormedFor context)
    (increases : start.Le finish) :
    ∀ candidate, candidate ∈ generated.unificationVars →
      candidate.Below finish.ty finish.cap := by
  intro candidate member
  rcases provenance candidate member with contextMember | fresh
  · have belowInitial :=
      Context.member_unificationVars_below_initialSupply contextMember
    cases candidate with
    | ty index =>
      exact Nat.lt_of_lt_of_le belowInitial
          (Nat.le_trans wellFormed.1 increases.1)
    | cap index =>
      exact Nat.lt_of_lt_of_le belowInitial
          (Nat.le_trans wellFormed.2 increases.2)
  · exact fresh.below

private theorem scheme_mem_of_getElem?_eq_some
    {context : Context} {index : Nat} {scheme : Scheme}
    (lookup : context[index]? = some scheme) : scheme ∈ context := by
  induction context generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero => simp at lookup; subst scheme; simp
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          exact List.mem_cons_of_mem head (induction lookup)

private theorem supportProvenance_var
    {context : Context} {index : Nat} {start : Supply} {scheme : Scheme}
    (lookup : context[index]? = some scheme) :
    GeneratedSupportProvenance context start (scheme.instantiate start).2
      { target := (scheme.instantiate start).1, hard := [], pending := [] } := by
  intro candidate member
  simp only [Generated.unificationVars, TypePM.unificationVars,
    pendingUnificationVars, List.append_nil] at member
  have schemeMember := scheme_mem_of_getElem?_eq_some lookup
  cases candidate with
  | ty index =>
      rcases Scheme.instantiate_ty_origin _ _ member with free | fresh
      · exact Or.inl (Context.ty_mem_unificationVars_of_scheme
          schemeMember free)
      · exact Or.inr fresh
  | cap index =>
      rcases Scheme.instantiate_cap_origin _ _ member with free | fresh
      · exact Or.inl (Context.cap_mem_unificationVars_of_scheme
          schemeMember free)
      · exact Or.inr fresh

theorem supportProvenance_closed_instantiate
    {context : Context} {start : Supply} {scheme : Scheme}
    (closed : scheme.Closed) :
    GeneratedSupportProvenance context start (scheme.instantiate start).2
      { target := (scheme.instantiate start).1, hard := [], pending := [] } := by
  intro candidate member
  simp only [Generated.unificationVars, TypePM.unificationVars,
    pendingUnificationVars, List.append_nil] at member
  cases candidate with
  | ty index =>
      rcases Scheme.instantiate_ty_origin _ _ member with free | fresh
      · rw [closed.1] at free
        simp at free
      · exact Or.inr fresh
  | cap index =>
      rcases Scheme.instantiate_cap_origin _ _ member with free | fresh
      · rw [closed.2] at free
        simp at free
      · exact Or.inr fresh

private theorem supportProvenance_lit
    {context : Context} (_value : Int) {start : Supply} :
    GeneratedSupportProvenance context start start
      { target := .int, hard := [], pending := [] } := by
  intro candidate member
  simp [Generated.unificationVars, TypePM.unificationVars,
    pendingUnificationVars, Ty.unificationVars] at member

private theorem supportProvenance_something
    {context : Context} {start : Supply} :
    GeneratedSupportProvenance context start (start.nextTy 1)
      { target := .matcher .any (.var ⟨start.ty⟩), hard := [], pending := [] } := by
  intro candidate member
  have equality : candidate = .ty ⟨start.ty⟩ := by
    simpa [Generated.unificationVars, TypePM.unificationVars,
      pendingUnificationVars, Ty.unificationVars,
      Cap.unificationVars] using member
  subst candidate
  exact Or.inr (by simp [UnificationVar.FreshIn, Supply.nextTy])

private theorem supportProvenance_lam
    {signature : Signature} {context : Context} {body : Expr} {start : Supply}
    {generatedBody : Generated} {finish : Supply}
    (bodyElaboration : Elaborates signature
      (.mono (.var ⟨start.ty⟩) :: context) body
      (start.nextTy 1) generatedBody finish)
    (bodyProvenance : GeneratedSupportProvenance
      (.mono (.var ⟨start.ty⟩) :: context)
      (start.nextTy 1) finish generatedBody) :
    GeneratedSupportProvenance context start finish
      { target := .fn (.var ⟨start.ty⟩) generatedBody.target,
        hard := generatedBody.hard, pending := generatedBody.pending } := by
  intro candidate member
  simp only [Generated.unificationVars, Ty.unificationVars,
    List.mem_append] at member
  rcases member with targetOrHard | pending
  rcases targetOrHard with target | hard
  rcases target with domain | bodyTarget
  · have equality : candidate = .ty ⟨start.ty⟩ := by
      simpa [Ty.unificationVars] using domain
    subst candidate
    exact Or.inr (by
      simp [UnificationVar.FreshIn]
      exact bodyElaboration.supply_le_next.1)
  · have bodyMember : candidate ∈ generatedBody.unificationVars := by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inl bodyTarget)
    rcases bodyProvenance candidate bodyMember with bodyContext | fresh
    · rcases Context.mono_ty_cons_support context ⟨start.ty⟩
        candidate bodyContext with rfl | outer
      · exact Or.inr (by
          simp [UnificationVar.FreshIn]
          exact bodyElaboration.supply_le_next.1)
      · exact Or.inl outer
    · exact Or.inr (fresh.lower_start (Supply.le_nextTy start 1))
  · have bodyMember : candidate ∈ generatedBody.unificationVars := by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inr hard)
    rcases bodyProvenance candidate bodyMember with bodyContext | fresh
    · rcases Context.mono_ty_cons_support context ⟨start.ty⟩
        candidate bodyContext with rfl | outer
      · exact Or.inr (by
          simp [UnificationVar.FreshIn]
          exact bodyElaboration.supply_le_next.1)
      · exact Or.inl outer
    · exact Or.inr (fresh.lower_start (Supply.le_nextTy start 1))
  · have bodyMember : candidate ∈ generatedBody.unificationVars := by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inr pending
    rcases bodyProvenance candidate bodyMember with bodyContext | fresh
    · rcases Context.mono_ty_cons_support context ⟨start.ty⟩
        candidate bodyContext with rfl | outer
      · exact Or.inr (by
          simp [UnificationVar.FreshIn]
          exact bodyElaboration.supply_le_next.1)
      · exact Or.inl outer
    · exact Or.inr (fresh.lower_start (Supply.le_nextTy start 1))

theorem supportProvenance_fromApp
    {signature : Signature} {context : Context} {argument : Expr} {start : Supply}
    {generatedFunction : Generated} {afterFunction : Supply}
    {generatedArgument : Generated} {afterArgument : Supply}
    (functionIncreases : start.Le afterFunction)
    (argumentElaboration :
      Elaborates signature context argument afterFunction generatedArgument afterArgument)
    (functionProvenance :
      GeneratedSupportProvenance context start afterFunction generatedFunction)
    (argumentProvenance :
      GeneratedSupportProvenance context afterFunction afterArgument generatedArgument) :
    GeneratedSupportProvenance context start (afterArgument.nextTy 2)
      { target := .var ⟨afterArgument.ty + 1⟩,
        hard := generatedFunction.hard ++ generatedArgument.hard ++
          [.ty generatedFunction.target
            (.fn (.var ⟨afterArgument.ty⟩)
              (.var ⟨afterArgument.ty + 1⟩))],
        pending := generatedFunction.pending ++ generatedArgument.pending ++
          [⟨generatedArgument.target, .var ⟨afterArgument.ty⟩⟩] } := by
  intro candidate member
  simp only [Generated.unificationVars, Ty.unificationVars,
    TypePM.unificationVars, pendingUnificationVars,
    CheckObligation.unificationVars, List.mem_append,
    unificationVars_append, pendingUnificationVars_append,
    Equation.unificationVars, List.mem_cons, List.not_mem_nil, or_false] at member
  have startToArgument : Supply.Le start afterArgument :=
    Supply.le_trans functionIncreases
      argumentElaboration.supply_le_next
  have argumentToFinish : Supply.Le afterArgument (afterArgument.nextTy 2) :=
    Supply.le_nextTy afterArgument 2
  have liftFunction : ∀ {candidate},
      candidate ∈ context.unificationVars ∨
          candidate.FreshIn start afterFunction →
        candidate ∈ context.unificationVars ∨
          candidate.FreshIn start (afterArgument.nextTy 2) := by
    intro origin candidateOrigin
    rcases candidateOrigin with outer | fresh
    · exact Or.inl outer
    · exact Or.inr (fresh.extend_finish
        (Supply.le_trans argumentElaboration.supply_le_next argumentToFinish))
  have liftArgument : ∀ {candidate},
      candidate ∈ context.unificationVars ∨
          candidate.FreshIn afterFunction afterArgument →
        candidate ∈ context.unificationVars ∨
          candidate.FreshIn start (afterArgument.nextTy 2) := by
    intro origin candidateOrigin
    rcases candidateOrigin with outer | fresh
    · exact Or.inl outer
    · exact Or.inr ((fresh.lower_start
        functionIncreases).extend_finish argumentToFinish)
  have freshAt (offset : Nat) (offsetLt : offset < 2) :
      UnificationVar.FreshIn start (afterArgument.nextTy 2)
        (.ty ⟨afterArgument.ty + offset⟩) := by
    simp only [UnificationVar.FreshIn, Supply.nextTy]
    exact ⟨Nat.le_trans startToArgument.1 (Nat.le_add_right _ _),
      Nat.add_lt_add_left offsetLt _⟩
  rcases member with (rfl | (functionHard | argumentHard) | functionTarget |
      rfl | rfl) | (functionPending | argumentPending) | argumentTarget | rfl
  · exact Or.inr (freshAt 1 (by omega))
  · exact liftFunction (functionProvenance candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inr functionHard)))
  · exact liftArgument (argumentProvenance candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inr argumentHard)))
  · exact liftFunction (functionProvenance candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inl functionTarget)))
  · simpa using Or.inr (freshAt 0 (by omega))

  · exact Or.inr (freshAt 1 (by omega))
  · exact liftFunction (functionProvenance candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inr functionPending))
  · exact liftArgument (argumentProvenance candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inr argumentPending))
  · exact liftArgument (argumentProvenance candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inl argumentTarget)))
  · simpa using Or.inr (freshAt 0 (by omega))

private theorem supportProvenance_app
    {signature : Signature} {context : Context} {function argument : Expr}
    {start : Supply} {generatedFunction : Generated}
    {afterFunction : Supply} {generatedArgument : Generated}
    {afterArgument : Supply}
    (functionElaboration :
      Elaborates signature context function start generatedFunction afterFunction)
    (argumentElaboration :
      Elaborates signature context argument afterFunction generatedArgument afterArgument)
    (functionProvenance :
      GeneratedSupportProvenance context start afterFunction generatedFunction)
    (argumentProvenance :
      GeneratedSupportProvenance context afterFunction afterArgument generatedArgument) :
    GeneratedSupportProvenance context start (afterArgument.nextTy 2)
      (Generated.fromApp generatedFunction generatedArgument
        (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩)) := by
  simpa [Generated.fromApp] using
    supportProvenance_fromApp functionElaboration.supply_le_next
      argumentElaboration functionProvenance argumentProvenance

private theorem supportProvenance_tuple
    {signature : Signature} {context : Context} {items : List Expr} {start : Supply}
    {generatedItems : GeneratedItems} {finish : Supply}
    (_itemsElaboration :
      ElaboratesItems signature context items start generatedItems finish)
    (itemsProvenance : GeneratedItemsSupportProvenance
      context start finish generatedItems) :
    GeneratedSupportProvenance context start finish
      { target := .prod generatedItems.targets,
        hard := generatedItems.hard, pending := generatedItems.pending } := by
  intro candidate member
  apply itemsProvenance candidate
  simpa [Generated.unificationVars, GeneratedItems.unificationVars,
    Ty.unificationVars] using member

private theorem supportProvenance_items_nil
    {context : Context} {start : Supply} :
    GeneratedItemsSupportProvenance context start start
      { targets := [], hard := [], pending := [] } := by
  intro candidate member
  simp [GeneratedItems.unificationVars, Ty.unificationVarsList,
    TypePM.unificationVars, pendingUnificationVars] at member

private theorem supportProvenance_items_cons
    {signature : Signature} {context : Context} {item : Expr} {items : List Expr} {start : Supply}
    {generatedItem : Generated} {afterItem : Supply}
    {generatedItems : GeneratedItems} {finish : Supply}
    (itemElaboration :
      Elaborates signature context item start generatedItem afterItem)
    (itemsElaboration :
      ElaboratesItems signature context items afterItem generatedItems finish)
    (itemProvenance : GeneratedSupportProvenance
      context start afterItem generatedItem)
    (itemsProvenance : GeneratedItemsSupportProvenance
      context afterItem finish generatedItems) :
    GeneratedItemsSupportProvenance context start finish
      { targets := generatedItem.target :: generatedItems.targets,
        hard := generatedItem.hard ++ generatedItems.hard,
        pending := generatedItem.pending ++ generatedItems.pending } := by
  intro candidate member
  simp only [GeneratedItems.unificationVars, Ty.unificationVarsList,
    unificationVars_append, pendingUnificationVars_append,
    List.mem_append] at member
  have liftItem : ∀ {candidate},
      candidate ∈ context.unificationVars ∨
          candidate.FreshIn start afterItem →
        candidate ∈ context.unificationVars ∨
          candidate.FreshIn start finish := by
    intro origin candidateOrigin
    rcases candidateOrigin with outer | fresh
    · exact Or.inl outer
    · exact Or.inr (fresh.extend_finish itemsElaboration.supply_le_next)
  have liftItems : ∀ {candidate},
      candidate ∈ context.unificationVars ∨
          candidate.FreshIn afterItem finish →
        candidate ∈ context.unificationVars ∨
          candidate.FreshIn start finish := by
    intro origin candidateOrigin
    rcases candidateOrigin with outer | fresh
    · exact Or.inl outer
    · exact Or.inr (fresh.lower_start itemElaboration.supply_le_next)
  rcases member with targetOrHard | pending
  · rcases targetOrHard with target | hard
    · rcases target with itemTarget | itemsTarget
      · exact liftItem (itemProvenance candidate (by
          simp only [Generated.unificationVars, List.mem_append]
          exact Or.inl (Or.inl itemTarget)))
      · exact liftItems (itemsProvenance candidate (by
          simp only [GeneratedItems.unificationVars, List.mem_append]
          exact Or.inl (Or.inl itemsTarget)))
    · rcases hard with itemHard | itemsHard
      · exact liftItem (itemProvenance candidate (by
          simp only [Generated.unificationVars, List.mem_append]
          exact Or.inl (Or.inr itemHard)))
      · exact liftItems (itemsProvenance candidate (by
          simp only [GeneratedItems.unificationVars, List.mem_append]
          exact Or.inl (Or.inr itemsHard)))
  · rcases pending with itemPending | itemsPending
    · exact liftItem (itemProvenance candidate (by
        simp only [Generated.unificationVars, List.mem_append]
        exact Or.inr itemPending))
    · exact liftItems (itemsProvenance candidate (by
        simp only [GeneratedItems.unificationVars, List.mem_append]
        exact Or.inr itemsPending))

private theorem supportProvenance_let
    {signature : Signature} {context : Context} {value body : Expr} {start : Supply}
    {generatedValue : Generated} {afterValue : Supply}
    {generatedBody : Generated} {finish : Supply}
    (valueElaboration :
      Elaborates signature context value start generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (bodyElaboration : Elaborates signature
      ((context.applyFree closure.substitution).generalize closure.target ::
        context.applyFree closure.substitution)
      body
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply)
      generatedBody finish)
    (valueProvenance : GeneratedSupportProvenance
      context start afterValue generatedValue)
    (bodyProvenance : GeneratedSupportProvenance
      ((context.applyFree closure.substitution).generalize closure.target ::
        context.applyFree closure.substitution)
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply)
      finish generatedBody) :
    GeneratedSupportProvenance context start finish
      (Generated.fromLet
        (context.interfaceEquations closure.substitution) generatedBody) := by
  intro candidate member
  simp only [Generated.fromLet, Generated.unificationVars,
    unificationVars_append, List.mem_append] at member
  have localized := closure.localized_of_absorbing absorbing
  have afterValueToFinish : Supply.Le afterValue finish :=
    Supply.le_trans (Supply.le_join_left afterValue
      (context.applyFree closure.substitution).initialSupply)
      bodyElaboration.supply_le_next
  have startToBodyStart : Supply.Le start
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply) :=
    Supply.le_trans valueElaboration.supply_le_next
      (Supply.le_join_left afterValue
        (context.applyFree closure.substitution).initialSupply)
  have liftValue : ∀ {candidate},
      candidate ∈ context.unificationVars ∨
          candidate.FreshIn start afterValue →
        candidate ∈ context.unificationVars ∨
          candidate.FreshIn start finish := by
    intro origin candidateOrigin
    rcases candidateOrigin with outer | fresh
    · exact Or.inl outer
    · exact Or.inr (fresh.extend_finish afterValueToFinish)
  have closedProvenance := Context.applyFree_supportProvenance
    localized valueProvenance
  have liftBody : ∀ {candidate}, candidate ∈ generatedBody.unificationVars →
      candidate ∈ context.unificationVars ∨
        candidate.FreshIn start finish := by
    intro origin bodyMember
    rcases bodyProvenance origin bodyMember with bodyContext | fresh
    · have closedMember := Context.generalized_cons_support_subset
        (context.applyFree closure.substitution) closure.target
        origin bodyContext
      exact liftValue (closedProvenance origin closedMember)
    · exact Or.inr (fresh.lower_start startToBodyStart)
  rcases member with targetOrHard | pending
  · rcases targetOrHard with target | effectsOrHard
    · exact liftBody (by
        simp only [Generated.unificationVars, List.mem_append]
        exact Or.inl (Or.inl target))
    · rcases effectsOrHard with effects | hard
      · exact liftValue (Context.interface_supportProvenance
          localized valueProvenance candidate effects)
      · exact liftBody (by
          simp only [Generated.unificationVars, List.mem_append]
          exact Or.inl (Or.inr hard))
  · exact liftBody (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inr pending)

private theorem supportProvenance_call_nil
    {context : Context} {accumulated : Generated} {start : Supply} :
    ∀ outerStart, outerStart.Le start →
      GeneratedSupportProvenance context outerStart start accumulated →
      GeneratedSupportProvenance context outerStart start accumulated := by
  intro outerStart _ provenance
  exact provenance

private theorem supportProvenance_call_cons
    {signature : Signature} {context : Context}
    {accumulated : Generated} {argument : Expr} {arguments : List Expr}
    {start : Supply} {generatedArgument : Generated}
    {afterArgument : Supply} {generated : Generated} {finish : Supply}
    (argumentElaboration : Elaborates signature context argument start
      generatedArgument afterArgument)
    (_restElaboration : ElaboratesCall signature context
      (Generated.fromApp accumulated generatedArgument
        (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
      arguments (afterArgument.nextTy 2) generated finish)
    (argumentProvenance : GeneratedSupportProvenance context start
      afterArgument generatedArgument)
    (restProvenance : ∀ outerStart,
      outerStart.Le (afterArgument.nextTy 2) →
      GeneratedSupportProvenance context outerStart
        (afterArgument.nextTy 2)
        (Generated.fromApp accumulated generatedArgument
          (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩)) →
      GeneratedSupportProvenance context outerStart finish generated) :
    ∀ outerStart, outerStart.Le start →
      GeneratedSupportProvenance context outerStart start accumulated →
      GeneratedSupportProvenance context outerStart finish generated := by
  intro outerStart outerToStart accumulatedProvenance
  have appliedProvenance : GeneratedSupportProvenance context outerStart
      (afterArgument.nextTy 2)
      (Generated.fromApp accumulated generatedArgument
        (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩)) := by
    simpa [Generated.fromApp] using
      supportProvenance_fromApp outerToStart argumentElaboration
        accumulatedProvenance argumentProvenance
  apply restProvenance outerStart
  · exact Supply.le_trans outerToStart
      (Supply.le_trans argumentElaboration.supply_le_next
        (Supply.le_nextTy afterArgument 2))
  · exact appliedProvenance

private theorem supportProvenance_ctor
    {signature : Signature} {context : Context} {constructor : DataCtor}
    {arguments : List Expr} {scheme : Scheme} {start finish : Supply}
    {generated : Generated}
    (_lookup : signature.lookupDataConstructor constructor = some scheme)
    (_arity : arguments.length = scheme.callArity) (closed : scheme.Closed)
    (_call : ElaboratesCall signature context
      ⟨(scheme.instantiate start).1, [], []⟩ arguments
      (scheme.instantiate start).2 generated finish)
    (callProvenance : ∀ outerStart,
      outerStart.Le (scheme.instantiate start).2 →
      GeneratedSupportProvenance context outerStart
        (scheme.instantiate start).2
        ⟨(scheme.instantiate start).1, [], []⟩ →
      GeneratedSupportProvenance context outerStart finish generated) :
    GeneratedSupportProvenance context start finish generated := by
  apply callProvenance start
  · simp [Supply.Le, Scheme.instantiate]
  · exact supportProvenance_closed_instantiate closed

private theorem supportProvenance_prim
    {signature : Signature} {context : Context} {operation : PrimOp}
    {arguments : List Expr} {scheme : Scheme} {start finish : Supply}
    {generated : Generated}
    (_lookup : signature.lookupPrimitive operation = some scheme)
    (_arity : arguments.length = scheme.callArity) (closed : scheme.Closed)
    (_call : ElaboratesCall signature context
      ⟨(scheme.instantiate start).1, [], []⟩ arguments
      (scheme.instantiate start).2 generated finish)
    (callProvenance : ∀ outerStart,
      outerStart.Le (scheme.instantiate start).2 →
      GeneratedSupportProvenance context outerStart
        (scheme.instantiate start).2
        ⟨(scheme.instantiate start).1, [], []⟩ →
      GeneratedSupportProvenance context outerStart finish generated) :
    GeneratedSupportProvenance context start finish generated := by
  apply callProvenance start
  · simp [Supply.Le, Scheme.instantiate]
  · exact supportProvenance_closed_instantiate closed

private theorem supportProvenance_ifE
    {signature : Signature} {context : Context}
    {condition thenBranch elseBranch : Expr} {start finish : Supply}
    {generated : Generated}
    (_call : ElaboratesCall signature context
      ⟨(conditionalScheme.instantiate start).1, [], []⟩
      [condition, thenBranch, elseBranch]
      (conditionalScheme.instantiate start).2 generated finish)
    (callProvenance : ∀ outerStart,
      outerStart.Le (conditionalScheme.instantiate start).2 →
      GeneratedSupportProvenance context outerStart
        (conditionalScheme.instantiate start).2
        ⟨(conditionalScheme.instantiate start).1, [], []⟩ →
      GeneratedSupportProvenance context outerStart finish generated) :
    GeneratedSupportProvenance context start finish generated := by
  apply callProvenance start
  · simp [Supply.Le, Scheme.instantiate]
  · exact supportProvenance_closed_instantiate conditionalScheme_closed

/-- Every generated variable either comes from the input context or was
allocated by this elaboration. -/
theorem Elaborates.supportProvenance
    {signature : Signature} {context : Context} {expression : Expr} {start finish : Supply}
    {generated : Generated}
    (derivation : Elaborates signature context expression start generated finish) :
    GeneratedSupportProvenance context start finish generated :=
  Elaborates.rec
    (motive_1 := fun context _ start generated finish _ =>
      GeneratedSupportProvenance context start finish generated)
    (motive_2 := fun context _ start generated finish _ =>
      GeneratedItemsSupportProvenance context start finish generated)
    (motive_3 := fun context accumulated _ start generated finish _ =>
      ∀ outerStart, outerStart.Le start →
        GeneratedSupportProvenance context outerStart start accumulated →
        GeneratedSupportProvenance context outerStart finish generated)
    supportProvenance_var (fun {_} {value} {_} => supportProvenance_lit value)
    supportProvenance_something supportProvenance_lam
    supportProvenance_app supportProvenance_tuple supportProvenance_let
    supportProvenance_ctor supportProvenance_prim supportProvenance_ifE
    supportProvenance_items_nil supportProvenance_items_cons
    supportProvenance_call_nil supportProvenance_call_cons derivation

/-- List counterpart of `Elaborates.supportProvenance`. -/
theorem ElaboratesItems.supportProvenance
    {signature : Signature} {context : Context} {expressions : List Expr} {start finish : Supply}
    {generated : GeneratedItems}
    (derivation : ElaboratesItems signature context expressions start generated finish) :
    GeneratedItemsSupportProvenance context start finish generated :=
  ElaboratesItems.rec
    (motive_1 := fun context _ start generated finish _ =>
      GeneratedSupportProvenance context start finish generated)
    (motive_2 := fun context _ start generated finish _ =>
      GeneratedItemsSupportProvenance context start finish generated)
    (motive_3 := fun context accumulated _ start generated finish _ =>
      ∀ outerStart, outerStart.Le start →
        GeneratedSupportProvenance context outerStart start accumulated →
        GeneratedSupportProvenance context outerStart finish generated)
    supportProvenance_var (fun {_} {value} {_} => supportProvenance_lit value)
    supportProvenance_something supportProvenance_lam
    supportProvenance_app supportProvenance_tuple supportProvenance_let
    supportProvenance_ctor supportProvenance_prim supportProvenance_ifE
    supportProvenance_items_nil supportProvenance_items_cons
    supportProvenance_call_nil supportProvenance_call_cons derivation

/-- List provenance gives the same strict output-supply bound as block
provenance. -/
theorem GeneratedItemsSupportProvenance.below
    {context : Context} {start finish : Supply}
    {generated : GeneratedItems}
    (provenance : GeneratedItemsSupportProvenance
      context start finish generated)
    (wellFormed : start.WellFormedFor context)
    (increases : start.Le finish) :
    ∀ candidate, candidate ∈ generated.unificationVars →
      candidate.Below finish.ty finish.cap := by
  intro candidate member
  rcases provenance candidate member with contextMember | fresh
  · have belowInitial :=
      Context.member_unificationVars_below_initialSupply contextMember
    cases candidate with
    | ty index =>
        exact Nat.lt_of_lt_of_le belowInitial
          (Nat.le_trans wellFormed.1 increases.1)
    | cap index =>
        exact Nat.lt_of_lt_of_le belowInitial
          (Nat.le_trans wellFormed.2 increases.2)
  · exact fresh.below

/-- Every variable generated by expression elaboration is below its output
supply when the input supply covers the context. -/
theorem Elaborates.support_below
    {signature : Signature} {context : Context} {expression : Expr} {start finish : Supply}
    {generated : Generated}
    (derivation : Elaborates signature context expression start generated finish)
    (wellFormed : start.WellFormedFor context) :
    ∀ candidate, candidate ∈ generated.unificationVars →
      candidate.Below finish.ty finish.cap :=
  derivation.supportProvenance.below wellFormed derivation.supply_le_next

/-- List counterpart of `Elaborates.support_below`. -/
theorem ElaboratesItems.support_below
    {signature : Signature} {context : Context} {expressions : List Expr} {start finish : Supply}
    {generated : GeneratedItems}
    (derivation : ElaboratesItems signature context expressions start generated finish)
    (wellFormed : start.WellFormedFor context) :
    ∀ candidate, candidate ∈ generated.unificationVars →
      candidate.Below finish.ty finish.cap :=
  derivation.supportProvenance.below wellFormed derivation.supply_le_next

/-- A localized principal closure of an elaborated value cannot raise the
closed context's initial supply above the value's output supply. -/
theorem Elaborates.closedContext_initialSupply_le
    {signature : Signature} {context : Context} {value : Expr} {start afterValue : Supply}
    {generatedValue : Generated}
    (valueElaboration :
      Elaborates signature context value start generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (wellFormed : start.WellFormedFor context) :
    (context.applyFree closure.substitution).initialSupply.Le afterValue := by
  apply Context.applyFree_initialSupply_le_of_localized
    (closure.localized_of_absorbing absorbing) context afterValue
  · exact Supply.le_trans wellFormed valueElaboration.supply_le_next
  · exact valueElaboration.support_below wellFormed

end Source
end TypePM
