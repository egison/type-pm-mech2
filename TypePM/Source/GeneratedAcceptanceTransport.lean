import TypePM.BlockOrderInvariance
import TypePM.DeclarativeCoverage
import TypePM.Source.ElaborationRenaming
import TypePM.Source.InterfaceClosureTransport

/-!
# Acceptance transport for source-generated blocks

This module connects the two-sort variable-renaming algebra used by source
elaboration with the representative-insensitive context interfaces used at a
`letE` boundary.  The basic transport is exact: a global bijective change of
ordinary and capability variable names preserves and reflects block
acceptance.
-/

namespace TypePM.Source

namespace ElaborationRenaming

namespace Generated

/-- The acceptance-level endpoint needed by completeness induction.  Exact
renaming below is intentionally stronger and compositional for ordinary
syntax constructors; a general `letE` representative change must establish
this endpoint through its interface and residual-solution bridges. -/
def AcceptanceEquivalent
    (left right : TypePM.Generated) : Prop :=
  TypePM.BlockAccepts left ↔ TypePM.BlockAccepts right

/-- Exact correspondence under one global two-sort variable renaming.  The
same renaming acts on the result type, hard equations, and delayed checking
obligations. -/
def RenamedBy (rho : VariableRenaming)
    (left right : TypePM.Generated) : Prop :=
  right = renameGenerated rho left

namespace RenamedBy

/-- Exact renamed blocks have equivalent acceptance. -/
theorem blockAccepts_iff
    {rho : VariableRenaming} {left right : TypePM.Generated}
    (related : RenamedBy rho left right) :
    TypePM.BlockAccepts left ↔ TypePM.BlockAccepts right := by
  rw [related]
  exact ElaborationRenaming.blockAccepts_renameVariables_iff rho left

/-- Forget exact term-by-term correspondence and retain precisely the
acceptance equivalence consumed by source completeness. -/
theorem acceptanceEquivalent
    {rho : VariableRenaming} {left right : TypePM.Generated}
    (related : RenamedBy rho left right) :
    AcceptanceEquivalent left right :=
  related.blockAccepts_iff

/-- Function application preserves exact correspondence when both children
and the two freshly allocated result types use the same global renaming. -/
theorem app
    {rho : VariableRenaming}
    {function argument renamedFunction renamedArgument : TypePM.Generated}
    {domain target renamedDomain renamedTarget : Ty}
    (functionRelated : RenamedBy rho function renamedFunction)
    (argumentRelated : RenamedBy rho argument renamedArgument)
    (domainRelated : renamedDomain = renameTy rho domain)
    (targetRelated : renamedTarget = renameTy rho target) :
    RenamedBy rho
      { target := target
        hard := function.hard ++ argument.hard ++
          [.ty function.target (.fn domain target)]
        pending := function.pending ++ argument.pending ++
          [⟨argument.target, domain⟩] }
      { target := renamedTarget
        hard := renamedFunction.hard ++ renamedArgument.hard ++
          [.ty renamedFunction.target (.fn renamedDomain renamedTarget)]
        pending := renamedFunction.pending ++ renamedArgument.pending ++
          [⟨renamedArgument.target, renamedDomain⟩] } := by
  subst renamedFunction
  subst renamedArgument
  subst renamedDomain
  subst renamedTarget
  simp [RenamedBy, renameGenerated, renameTy, renameEquation,
    renameObligation, Equation.apply, CheckObligation.apply,
    Ty.apply, List.map_append]

/-- Lambda wrapping preserves exact correspondence. -/
theorem lam
    {rho : VariableRenaming} {body renamedBody : TypePM.Generated}
    {domain renamedDomain : Ty}
    (bodyRelated : RenamedBy rho body renamedBody)
    (domainRelated : renamedDomain = renameTy rho domain) :
    RenamedBy rho
      { target := .fn domain body.target
        hard := body.hard
        pending := body.pending }
      { target := .fn renamedDomain renamedBody.target
        hard := renamedBody.hard
        pending := renamedBody.pending } := by
  subst renamedBody
  subst renamedDomain
  simp [RenamedBy, renameGenerated, renameTy, Ty.apply]

/-- A complete `letE` block commutes with renaming when the parent context,
the selected value closure, and the generated body are all transported by
the same global renaming. -/
theorem fromLet
    {rho : VariableRenaming} {context : Context}
    {valueGenerated : TypePM.Generated}
    (closure : PrincipalBlockClosure valueGenerated)
    (body : TypePM.Generated) :
    RenamedBy rho
      (TypePM.Source.Generated.fromLet
        (context.interfaceEquations closure.substitution) body)
      (TypePM.Source.Generated.fromLet
        ((renameContext rho context).interfaceEquations
          (renameClosure rho closure).substitution)
        (renameGenerated rho body)) := by
  change _ = renameGenerated rho
    (TypePM.Source.Generated.fromLet
      (context.interfaceEquations closure.substitution) body)
  rw [renameGenerated_fromLet,
    Context.interfaceEquations_renameVariables,
    renameClosure_substitution]

/-- Consequently the same-representative `letE` transport preserves and
reflects acceptance. -/
theorem fromLet_blockAccepts_iff
    {rho : VariableRenaming} {context : Context}
    {valueGenerated : TypePM.Generated}
    (closure : PrincipalBlockClosure valueGenerated)
    (body : TypePM.Generated) :
    TypePM.BlockAccepts
        (TypePM.Source.Generated.fromLet
          (context.interfaceEquations closure.substitution) body) ↔
      TypePM.BlockAccepts
        (TypePM.Source.Generated.fromLet
          ((renameContext rho context).interfaceEquations
            (renameClosure rho closure).substitution)
          (renameGenerated rho body)) :=
  (fromLet closure body).blockAccepts_iff

/-- A second closure representative may replace `renameClosure closure` when
its substitution is exactly the conjugated substitution and the global
renaming fixes the outer context.  This is the strongest representative-
changing result obtainable by literal generated-block renaming; the general
factorization-only case needs the interface-aware relation below. -/
theorem fromLet_otherClosure
    {rho : VariableRenaming} {context : Context}
    {leftGenerated rightGenerated : TypePM.Generated}
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (contextFixed : renameContext rho context = context)
    (substitutionRelated :
      right.substitution = renameSubstitution rho left.substitution)
    (body : TypePM.Generated) :
    RenamedBy rho
      (TypePM.Source.Generated.fromLet
        (context.interfaceEquations left.substitution) body)
      (TypePM.Source.Generated.fromLet
        (context.interfaceEquations right.substitution)
        (renameGenerated rho body)) := by
  change _ = renameGenerated rho
    (TypePM.Source.Generated.fromLet
      (context.interfaceEquations left.substitution) body)
  rw [renameGenerated_fromLet,
    Context.interfaceEquations_renameVariables,
    contextFixed, ← substitutionRelated]

/-- Acceptance form of `fromLet_otherClosure`. -/
theorem fromLet_otherClosure_blockAccepts_iff
    {rho : VariableRenaming} {context : Context}
    {leftGenerated rightGenerated : TypePM.Generated}
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (contextFixed : renameContext rho context = context)
    (substitutionRelated :
      right.substitution = renameSubstitution rho left.substitution)
    (body : TypePM.Generated) :
    TypePM.BlockAccepts
        (TypePM.Source.Generated.fromLet
          (context.interfaceEquations left.substitution) body) ↔
      TypePM.BlockAccepts
        (TypePM.Source.Generated.fromLet
          (context.interfaceEquations right.substitution)
          (renameGenerated rho body)) :=
  (fromLet_otherClosure left right contextFixed substitutionRelated body).blockAccepts_iff

end RenamedBy

end Generated


namespace GeneratedItems

/-- Exact two-sort renaming correspondence for tuple-item accumulators. -/
def RenamedBy (rho : VariableRenaming)
    (left right : TypePM.GeneratedItems) : Prop :=
  right = renameGeneratedItems rho left

namespace RenamedBy

/-- Empty tuple-item accumulators correspond under every renaming. -/
theorem nil (rho : VariableRenaming) :
    RenamedBy rho ⟨[], [], []⟩ ⟨[], [], []⟩ := by
  simp [RenamedBy, renameGeneratedItems, Ty.applyList]

/-- Consing one generated item preserves the same global renaming across all
three accumulated fields, including both worklist appends. -/
theorem cons
    {rho : VariableRenaming}
    {item renamedItem : TypePM.Generated}
    {items renamedItems : TypePM.GeneratedItems}
    (itemRelated : Generated.RenamedBy rho item renamedItem)
    (itemsRelated : RenamedBy rho items renamedItems) :
    RenamedBy rho
      { targets := item.target :: items.targets
        hard := item.hard ++ items.hard
        pending := item.pending ++ items.pending }
      { targets := renamedItem.target :: renamedItems.targets
        hard := renamedItem.hard ++ renamedItems.hard
        pending := renamedItem.pending ++ renamedItems.pending } := by
  subst renamedItem
  subst renamedItems
  simp [RenamedBy, renameGeneratedItems,
    renameGenerated, renameTy, Ty.applyList, List.map_append]

/-- Turning corresponding item accumulators into tuple blocks preserves
exact correspondence and therefore also preserves acceptance. -/
theorem tuple
    {rho : VariableRenaming} {items renamedItems : TypePM.GeneratedItems}
    (itemsRelated : RenamedBy rho items renamedItems) :
    Generated.RenamedBy rho
      { target := .prod items.targets
        hard := items.hard
        pending := items.pending }
      { target := .prod renamedItems.targets
        hard := renamedItems.hard
        pending := renamedItems.pending } := by
  subst renamedItems
  simp [Generated.RenamedBy, renameGenerated,
    renameGeneratedItems, renameTy, Ty.apply]

end RenamedBy

end GeneratedItems

namespace BlockAccepts

/-- Simultaneously renaming ordinary and capability variables preserves
declarative block acceptance. -/
theorem renameVariables
    (rho : VariableRenaming) {generated : Generated}
    (accepts : TypePM.BlockAccepts generated) :
    TypePM.BlockAccepts (renameGenerated rho generated) := by
  rcases accepts with ⟨finalHard, finalPending, hardSubstitution,
    residualSubstitution, saturation, residualSolved⟩
  refine ⟨finalHard.map (renameEquation rho),
    finalPending.map (renameObligation rho),
    renameSubstitution rho hardSubstitution,
    renameSubstitution rho residualSubstitution,
    Saturated.renameVariables rho saturation, ?_⟩
  rw [residualEquations_renameVariables]
  exact (solves_renameVariables rho residualSubstitution _).2
    residualSolved

/-- Two-sort renaming preserves and reflects declarative block acceptance. -/
theorem renameVariables_iff
    (rho : VariableRenaming) (generated : Generated) :
    TypePM.BlockAccepts (renameGenerated rho generated) ↔
      TypePM.BlockAccepts generated := by
  constructor
  · intro accepts
    have restored := renameVariables rho.symm accepts
    simpa using restored
  · exact renameVariables rho

/-- A block without delayed checking obligations is acceptable exactly as
soon as its hard equations have one solution.  This small constructor is
useful for isolating what the interface lemmas already prove independently
of residual checking transport. -/
theorem of_solvable_noPending
    {generated : TypePM.Generated}
    (noPending : generated.pending = [])
    {solution : Subst} (solved : Solves solution generated.hard) :
    TypePM.BlockAccepts generated := by
  cases generated with
  | mk target hard pending =>
      simp only at noPending
      subst pending
      obtain ⟨principal, success⟩ := unify_complete ⟨solution, solved⟩
      refine ⟨hard, [], principal, Subst.id, ?_, ?_⟩
      · exact
          { closure := .refl
            principal := unify_mostGeneral success
            stable := by simp [promoteUnder] }
      · simp [residualEquations]

/-- Acceptance always exposes a solution of the initial hard worklist. -/
theorem hard_solvable
    {generated : TypePM.Generated}
    (accepts : TypePM.BlockAccepts generated) :
    ∃ solution, Solves solution generated.hard := by
  rcases accepts with ⟨finalHard, finalPending, hardSubstitution,
    residualSubstitution, saturation, residualSolved⟩
  let solution := Subst.compose residualSubstitution hardSubstitution
  have finalSolved : Solves solution finalHard :=
    solves_postcompose saturation.principal.1 residualSubstitution
  exact ⟨solution, fun equation membership =>
    finalSolved equation
      (saturation.closure.hard_mem_final equation membership)⟩

end BlockAccepts


/-- The hard-equation bridge available for two different absorbing closure
representatives after the left source block and body have been globally
renamed.  The bridge deliberately records the residual-checking gap: it
transports every suitably normalized body hard solution, while making no
unsupported claim about `Saturated` or residual worklists. -/
def FromLetHardSolutionBridge
    {valueGenerated : TypePM.Generated}
    (rho : VariableRenaming)
    (left : PrincipalBlockClosure valueGenerated)
    (right : PrincipalBlockClosure (renameGenerated rho valueGenerated))
    (context : Context) (body : TypePM.Generated) : Prop :=
  ∀ {later : Subst},
    Solves later
        ((renameGenerated rho body).hard.map
          (Equation.apply (renameClosure rho left).substitution)) →
      Solves
        (Subst.compose later (renameClosure rho left).substitution)
        (TypePM.Source.Generated.fromLet
          ((renameContext rho context).interfaceEquations
            right.substitution)
          (renameGenerated rho body)).hard

/-- `InterfaceClosureTransport` proves the hard-equation bridge for every
pair of absorbing representatives. -/
theorem fromLetHardSolutionBridge
    {valueGenerated : TypePM.Generated}
    (rho : VariableRenaming)
    (left : PrincipalBlockClosure valueGenerated)
    (right : PrincipalBlockClosure (renameGenerated rho valueGenerated))
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (body : TypePM.Generated) :
    FromLetHardSolutionBridge rho left right context body := by
  intro later bodySolved
  let renamedLeft := renameClosure rho left
  have renamedLeftAbsorbing : renamedLeft.Absorbing :=
    renameClosure_absorbing rho left leftAbsorbing
  obtain ⟨forward, backward, transport⟩ :=
    renamedLeft.representativeTransport right
  exact Source.PrincipalBlockClosure.postcompose_left_solves_fromLet_hard
    transport
    renamedLeftAbsorbing rightAbsorbing (renameContext rho context)
    (renameGenerated rho body) bodySolved

/-- In the delayed-check-free case, the hard-solution bridge upgrades to an
actual one-way `BlockAccepts` transport.  `bodyFixed` is the freshness/
normalization fact expected from source elaboration: the renamed value
closure acts identically on the already closed body equations. -/
theorem fromLet_otherClosure_blockAccepts_of_noPending
    {valueGenerated : TypePM.Generated}
    (rho : VariableRenaming)
    (left : PrincipalBlockClosure valueGenerated)
    (right : PrincipalBlockClosure (renameGenerated rho valueGenerated))
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) (body : TypePM.Generated)
    (bodyNoPending : (renameGenerated rho body).pending = [])
    (bodyFixed :
      (renameGenerated rho body).hard.map
          (Equation.apply (renameClosure rho left).substitution) =
        (renameGenerated rho body).hard)
    (accepts : TypePM.BlockAccepts
      (TypePM.Source.Generated.fromLet
        ((renameContext rho context).interfaceEquations
          (renameClosure rho left).substitution)
        (renameGenerated rho body))) :
    TypePM.BlockAccepts
      (TypePM.Source.Generated.fromLet
        ((renameContext rho context).interfaceEquations right.substitution)
        (renameGenerated rho body)) := by
  obtain ⟨solution, wholeSolved⟩ := BlockAccepts.hard_solvable accepts
  have bodySolved : Solves solution (renameGenerated rho body).hard :=
    ((solves_append solution _ _).1 wholeSolved).2
  have normalizedBodySolved :
      Solves solution
        ((renameGenerated rho body).hard.map
          (Equation.apply (renameClosure rho left).substitution)) := by
    rwa [bodyFixed]
  have transported := fromLetHardSolutionBridge rho left right
    leftAbsorbing rightAbsorbing context body normalizedBodySolved
  apply BlockAccepts.of_solvable_noPending
    (generated := TypePM.Source.Generated.fromLet
      ((renameContext rho context).interfaceEquations right.substitution)
      (renameGenerated rho body))
  · simpa [TypePM.Source.Generated.fromLet] using bodyNoPending
  · exact transported

end ElaborationRenaming

end TypePM.Source
