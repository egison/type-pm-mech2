import TypePM.Source.GeneratedSupportBounds

/-!
# Support of source context interface equations

The equations exported by a closed `let` block mention only variables already
free in the surrounding context and variables occurring in the block
substitution's images of those free variables.
-/

namespace TypePM
namespace Source

namespace Context

/-- Ordinary-variable interface equations mention either a free context
variable or a variable in the corresponding substitution image. -/
theorem tyInterface_support_origin
    (indices : List TyVar) (block : Subst) {candidate : UnificationVar}
    (member : candidate ∈ TypePM.unificationVars
      (indices.map fun index => Equation.ty (.var index) (block.ty index))) :
    (∃ index, index ∈ indices ∧ candidate = .ty index) ∨
      ∃ index, index ∈ indices ∧
        candidate ∈ (block.ty index).unificationVars := by
  induction indices with
  | nil => simp [TypePM.unificationVars] at member
  | cons index indices induction =>
      simp only [List.map_cons, TypePM.unificationVars,
        Equation.unificationVars, Ty.unificationVars,
        List.mem_append] at member
      rcases member with (head | image) | tail
      · have equality : candidate = .ty index := by
          simpa using head
        exact Or.inl ⟨index, by simp, equality⟩
      · exact Or.inr ⟨index, by simp, image⟩
      · rcases induction tail with original | image
        · obtain ⟨source, sourceMember, equality⟩ := original
          exact Or.inl ⟨source, by simp [sourceMember], equality⟩
        · obtain ⟨source, sourceMember, imageMember⟩ := image
          exact Or.inr ⟨source, by simp [sourceMember], imageMember⟩

/-- Capability-variable interface equations mention either a free context
variable or a variable in the corresponding substitution image. -/
theorem capInterface_support_origin
    (indices : List CapVar) (block : Subst) {candidate : UnificationVar}
    (member : candidate ∈ TypePM.unificationVars
      (indices.map fun index => Equation.cap (.var index) (block.cap index))) :
    (∃ index, index ∈ indices ∧ candidate = .cap index) ∨
      ∃ index, index ∈ indices ∧
        candidate ∈ (block.cap index).unificationVars := by
  induction indices with
  | nil => simp [TypePM.unificationVars] at member
  | cons index indices induction =>
      simp only [List.map_cons, TypePM.unificationVars,
        Equation.unificationVars, Cap.unificationVars,
        List.mem_append] at member
      rcases member with (head | image) | tail
      · have equality : candidate = .cap index := by
          simpa using head
        exact Or.inl ⟨index, by simp, equality⟩
      · exact Or.inr ⟨index, by simp, image⟩
      · rcases induction tail with original | image
        · obtain ⟨source, sourceMember, equality⟩ := original
          exact Or.inl ⟨source, by simp [sourceMember], equality⟩
        · obtain ⟨source, sourceMember, imageMember⟩ := image
          exact Or.inr ⟨source, by simp [sourceMember], imageMember⟩

/-- Exact provenance of every variable mentioned by a context interface. -/
theorem interfaceEquations_support_origin
    (context : Context) (block : Subst) {candidate : UnificationVar}
    (member : candidate ∈
      TypePM.unificationVars (context.interfaceEquations block)) :
    candidate ∈ context.unificationVars ∨
      (∃ index, index ∈ context.freeTyVars ∧
        candidate ∈ (block.ty index).unificationVars) ∨
      (∃ index, index ∈ context.freeCapVars ∧
        candidate ∈ (block.cap index).unificationVars) := by
  simp only [Context.interfaceEquations, unificationVars_append,
    List.mem_append] at member
  rcases member with tyMember | capMember
  · rcases tyInterface_support_origin context.freeTyVars block tyMember with
      original | image
    · obtain ⟨index, indexMember, rfl⟩ := original
      exact Or.inl (by
        simp [Context.unificationVars, indexMember])
    · exact Or.inr (Or.inl image)
  · rcases capInterface_support_origin context.freeCapVars block capMember with
      original | image
    · obtain ⟨index, indexMember, rfl⟩ := original
      exact Or.inl (by
        simp [Context.unificationVars, indexMember])
    · exact Or.inr (Or.inr image)

/-- A substitution localized to a support with context-or-fresh provenance
exports an interface with the same provenance. -/
theorem interfaceEquations_supportProvenance
    {context : Context} {start finish : Supply}
    {blockSupport : List UnificationVar} {block : Subst}
    (localized : block.Localized blockSupport)
    (blockProvenance : ∀ candidate, candidate ∈ blockSupport →
      candidate ∈ context.unificationVars ∨ candidate.FreshIn start finish) :
    ∀ candidate,
      candidate ∈ TypePM.unificationVars (context.interfaceEquations block) →
        candidate ∈ context.unificationVars ∨ candidate.FreshIn start finish := by
  intro candidate member
  rcases interfaceEquations_support_origin context block member with
    original | tyImage | capImage
  · exact Or.inl original
  · obtain ⟨index, indexMember, imageMember⟩ := tyImage
    by_cases supported : .ty index ∈ blockSupport
    · exact blockProvenance candidate
        (localized.tyRange index supported candidate imageMember)
    · rw [localized.fixesTy index supported] at imageMember
      have equality : candidate = .ty index := by
        simpa [Ty.unificationVars] using imageMember
      subst candidate
      exact Or.inl (by simp [Context.unificationVars, indexMember])
  · obtain ⟨index, indexMember, imageMember⟩ := capImage
    by_cases supported : .cap index ∈ blockSupport
    · exact blockProvenance candidate
        (localized.capRange index supported candidate imageMember)
    · rw [localized.fixesCap index supported] at imageMember
      have equality : candidate = .cap index := by
        simpa [Cap.unificationVars] using imageMember
      subst candidate
      exact Or.inl (by simp [Context.unificationVars, indexMember])

/-- Under a well-formed starting supply, interface support is also strictly
below the finishing supply. -/
theorem interfaceEquations_support_below
    {context : Context} {start finish : Supply}
    {blockSupport : List UnificationVar} {block : Subst}
    (localized : block.Localized blockSupport)
    (blockProvenance : ∀ candidate, candidate ∈ blockSupport →
      candidate ∈ context.unificationVars ∨ candidate.FreshIn start finish)
    (wellFormed : start.WellFormedFor context)
    (increases : start.Le finish) :
    ∀ candidate,
      candidate ∈ TypePM.unificationVars (context.interfaceEquations block) →
        candidate.Below finish.ty finish.cap := by
  intro candidate member
  rcases interfaceEquations_supportProvenance localized blockProvenance
      candidate member with original | fresh
  · have belowInitial :=
      Context.member_unificationVars_below_initialSupply original
    cases candidate with
    | ty index =>
        exact Nat.lt_of_lt_of_le belowInitial
          (Nat.le_trans wellFormed.1 increases.1)
    | cap index =>
        exact Nat.lt_of_lt_of_le belowInitial
          (Nat.le_trans wellFormed.2 increases.2)
  · exact fresh.below

end Context

namespace Generated

/-- `fromLet` adds precisely the interface-effect support to the body block's
support. -/
theorem mem_unificationVars_fromLet_iff
    (effects : List Equation) (body : Generated)
    (candidate : UnificationVar) :
    candidate ∈ (Generated.fromLet effects body).unificationVars ↔
      candidate ∈ TypePM.unificationVars effects ∨
        candidate ∈ body.unificationVars := by
  simp only [Generated.fromLet, Generated.unificationVars,
    unificationVars_append, List.mem_append]
  constructor
  · rintro ((target | effects | hard) | pending)
    · exact Or.inr (Or.inl (Or.inl target))
    · exact Or.inl effects
    · exact Or.inr (Or.inl (Or.inr hard))
    · exact Or.inr (Or.inr pending)
  · rintro (effects | (target | hard) | pending)
    · exact Or.inl (Or.inr (Or.inl effects))
    · exact Or.inl (Or.inl target)
    · exact Or.inl (Or.inr (Or.inr hard))
    · exact Or.inr pending

end Generated

/-- Provenance for the added effects and for the body composes into provenance
for the whole `fromLet` block. -/
theorem GeneratedSupportProvenance.fromLet
    {context : Context} {start finish : Supply}
    {effects : List Equation} {body : Generated}
    (effectsProvenance : ∀ candidate,
      candidate ∈ TypePM.unificationVars effects →
        candidate ∈ context.unificationVars ∨ candidate.FreshIn start finish)
    (bodyProvenance : GeneratedSupportProvenance
      context start finish body) :
    GeneratedSupportProvenance context start finish
      (Generated.fromLet effects body) := by
  intro candidate member
  rcases (Generated.mem_unificationVars_fromLet_iff
      effects body candidate).mp member with
    effect | bodyMember
  · exact effectsProvenance candidate effect
  · exact bodyProvenance candidate bodyMember

/-- Convenience endpoint combining localized block support, its provenance,
and body provenance across a source `let` boundary. -/
theorem GeneratedSupportProvenance.fromLet_interface
    {context : Context} {start finish : Supply}
    {blockSupport : List UnificationVar} {block : Subst} {body : Generated}
    (localized : block.Localized blockSupport)
    (blockProvenance : ∀ candidate, candidate ∈ blockSupport →
      candidate ∈ context.unificationVars ∨ candidate.FreshIn start finish)
    (bodyProvenance : GeneratedSupportProvenance
      context start finish body) :
    GeneratedSupportProvenance context start finish
      (Generated.fromLet (context.interfaceEquations block) body) := by
  apply GeneratedSupportProvenance.fromLet
  · exact Context.interfaceEquations_supportProvenance
      localized blockProvenance
  · exact bodyProvenance

end Source
end TypePM
