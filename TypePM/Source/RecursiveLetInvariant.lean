import TypePM.Source.InterfaceAliasFreshness
import TypePM.Source.ScopedElaborationComposition
import TypePM.Source.LetSupplyStability
import TypePM.Source.ContextInterfaceSupport

/-!
# Recursive invariant for representative-independent `let`

The value expressions of two derivations of the same nested `letE` need not
produce literally equal `Generated` blocks.  Consequently the
same-generated `ClosureInterfaceDecomposition` is not, by itself, a strong
enough induction hypothesis.

This module records the heterogeneous closure invariant needed at that
boundary.  It deliberately contains no arbitrary-supply statement: every
source-facing comparison below keeps `Supply.WellFormedFor` explicit.
-/

namespace TypePM.Source

open InterfaceAliasDecomposition

/-- Transport data for principal closures of two possibly different
generated value blocks.  One renaming simultaneously aligns the closed outer
context, the principal value type, the generalized binding, and the exposed
interface equations.

The final field is equation-level rather than literal equality because an
absorbing representative can expose a fresh alias on one side and a
reflexive equation on the other. -/
structure CrossGeneratedClosureAlignment
    {leftGenerated rightGenerated : Generated}
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (context : Context) where
  rho : VariableRenaming
  closedContext_exact :
    (context.applyFree left.substitution).applyFree rho.substitution =
      context.applyFree right.substitution
  target_exact : left.target.apply rho.substitution = right.target
  generalized_exact :
    ((context.applyFree left.substitution).generalize left.target).applyFree
        rho.substitution =
      (context.applyFree right.substitution).generalize right.target
  equations : InterfaceAliasDecomposition.EquationLists.EquationCommonCore
    ((context.interfaceEquations left.substitution).map
      (ElaborationRenaming.renameEquation rho))
    (context.interfaceEquations right.substitution)

namespace CrossGeneratedClosureAlignment

/-- Existing same-generated closure decomposition is the reflexive-index
special case of the recursive invariant. -/
def ofClosureInterfaceDecomposition
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {context : Context}
    (decomposition : ClosureInterfaceDecomposition left right context) :
    CrossGeneratedClosureAlignment left right context :=
  { rho := decomposition.rho
    closedContext_exact := decomposition.closedContext_exact
    target_exact := decomposition.target_exact
    generalized_exact := decomposition.generalized_exact
    equations := decomposition.equations }

/-- Two absorbing closures of one generated block automatically satisfy the
heterogeneous invariant. -/
noncomputable def ofSameGenerated
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    CrossGeneratedClosureAlignment left right context := by
  let related := left.representativeTransport right
  let forward := Classical.choose related
  let remaining := Classical.choose_spec related
  let backward := Classical.choose remaining
  have transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward := Classical.choose_spec remaining
  exact ofClosureInterfaceDecomposition <|
    ClosureInterfaceDecomposition.build transport
      leftAbsorbing rightAbsorbing context

/-- Exact target transport gives the target-level principality consequence
also when the two closures have different generated-block indices. -/
theorem targets_mutualInstances
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context) :
    IsInstance left.target right.target ∧
      IsInstance right.target left.target := by
  rw [← alignment.target_exact]
  exact ClosureInterfaceDecomposition.renameTy_mutualInstances
    alignment.rho left.target

/-- The two body contexts occurring in relational `letE` constructors are
literally related by the same renaming.  Keeping this as a named endpoint is
important: target mutual instancehood alone cannot transport a body
elaboration. -/
theorem bodyContext_exact
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context}
    (alignment : CrossGeneratedClosureAlignment left right context) :
    (((context.applyFree left.substitution).generalize left.target ::
        context.applyFree left.substitution).map
      (Scheme.applyFree alignment.rho.substitution)) =
      ((context.applyFree right.substitution).generalize right.target ::
        context.applyFree right.substitution) := by
  simp only [List.map_cons]
  rw [alignment.generalized_exact]
  change _ ::
      (context.applyFree left.substitution).applyFree
        alignment.rho.substitution = _
  rw [alignment.closedContext_exact]

end CrossGeneratedClosureAlignment

namespace VariableRenaming

/-- A closure-interface renaming is local to a completed value block when it
fixes every name at or above the value's finishing supply.  This is the
missing condition which lets the body reuse the ordinary consecutive fresh
stream without another global renaming. -/
def FixesAtOrAbove (rho : VariableRenaming) (boundary : Supply) : Prop :=
  (∀ index : TyVar, boundary.ty ≤ index.index →
      rho.tyForward index = index) ∧
    (∀ index : CapVar, boundary.cap ≤ index.index →
      rho.capForward index = index)

theorem FixesAtOrAbove.mapsFrom_self
    {rho : VariableRenaming} {boundary : Supply}
    (fixed : rho.FixesAtOrAbove boundary) :
    boundary.MapsFrom rho boundary := by
  constructor
  · intro offset
    exact fixed.1 ⟨boundary.ty + offset⟩ (Nat.le_add_right _ _)
  · intro offset
    exact fixed.2 ⟨boundary.cap + offset⟩ (Nat.le_add_right _ _)

theorem FixesAtOrAbove.tyForward_lt
    {rho : VariableRenaming} {boundary : Supply}
    (fixed : rho.FixesAtOrAbove boundary)
    {index : TyVar} (below : index.index < boundary.ty) :
    (rho.tyForward index).index < boundary.ty := by
  by_cases result : (rho.tyForward index).index < boundary.ty
  · exact result
  · have atOrAbove : boundary.ty ≤ (rho.tyForward index).index :=
      Nat.le_of_not_gt result
    have imageFixed := fixed.1 (rho.tyForward index) atOrAbove
    have originalFixed : rho.tyForward index = index := by
      apply rho.tyForward_injective
      simp [imageFixed]
    rw [originalFixed] at atOrAbove
    exact False.elim ((Nat.not_le_of_gt below) atOrAbove)

theorem FixesAtOrAbove.capForward_lt
    {rho : VariableRenaming} {boundary : Supply}
    (fixed : rho.FixesAtOrAbove boundary)
    {index : CapVar} (below : index.index < boundary.cap) :
    (rho.capForward index).index < boundary.cap := by
  by_cases result : (rho.capForward index).index < boundary.cap
  · exact result
  · have atOrAbove : boundary.cap ≤ (rho.capForward index).index :=
      Nat.le_of_not_gt result
    have imageFixed := fixed.2 (rho.capForward index) atOrAbove
    have originalFixed : rho.capForward index = index := by
      apply rho.capForward_injective
      simp [imageFixed]
    rw [originalFixed] at atOrAbove
    exact False.elim ((Nat.not_le_of_gt below) atOrAbove)

/-- A renaming localized below a well-formed boundary sends every context
name below the same numeric boundary.  This is the numeric fact needed to
make both defensive `letE` joins collapse to the common value finish. -/
theorem FixesAtOrAbove.wellFormedFor_renameContext
    {rho : VariableRenaming} {boundary : Supply} {context : Context}
    (fixed : rho.FixesAtOrAbove boundary)
    (wellFormed : boundary.WellFormedFor context) :
    boundary.WellFormedFor (ElaborationRenaming.renameContext rho context) := by
  simp only [Supply.WellFormedFor, Context.initialSupply, Supply.Le]
  constructor
  · apply TyVar.next_le_of_forall_lt
    intro index member
    have renamedMember : index ∈
        (ElaborationRenaming.renameContext rho context).freeTyVars :=
      (mem_dedupFirst).2 member
    rw [ElaborationRenaming.Context.freeTyVars_renameContext]
      at renamedMember
    obtain ⟨original, originalMember, equality⟩ :=
      List.mem_map.mp renamedMember
    subst index
    apply fixed.tyForward_lt
    exact Nat.lt_of_lt_of_le
      (Context.freeTy_index_lt_initialSupply originalMember) wellFormed.1
  · apply CapVar.next_le_of_forall_lt
    intro index member
    have renamedMember : index ∈
        (ElaborationRenaming.renameContext rho context).freeCapVars :=
      (mem_dedupFirst).2 member
    rw [ElaborationRenaming.Context.freeCapVars_renameContext]
      at renamedMember
    obtain ⟨original, originalMember, equality⟩ :=
      List.mem_map.mp renamedMember
    subst index
    apply fixed.capForward_lt
    exact Nat.lt_of_lt_of_le
        (Context.freeCap_index_lt_initialSupply originalMember) wellFormed.2

theorem FixesAtOrAbove.mono
    {rho : VariableRenaming} {source target : Supply}
    (fixed : rho.FixesAtOrAbove source) (increases : source.Le target) :
    rho.FixesAtOrAbove target := by
  constructor
  · intro index above
    exact fixed.1 index (Nat.le_trans increases.1 above)
  · intro index above
    exact fixed.2 index (Nat.le_trans increases.2 above)

end VariableRenaming

/-- Closure alignment localized below the value's finishing supply.  The
locality field is what separates a usable recursive invariant from a bare
interface decomposition. -/
structure FreshClosureAlignment
    {leftGenerated rightGenerated : Generated}
    (left : PrincipalBlockClosure leftGenerated)
    (right : PrincipalBlockClosure rightGenerated)
    (context : Context) (boundary : Supply) where
  alignment : CrossGeneratedClosureAlignment left right context
  fixesAtOrAbove : alignment.rho.FixesAtOrAbove boundary

namespace FreshClosureAlignment

theorem bodyNames_mapFrom
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context} {boundary : Supply}
    (alignment : FreshClosureAlignment left right context boundary) :
    boundary.MapsFrom alignment.alignment.rho boundary :=
  alignment.fixesAtOrAbove.mapsFrom_self

theorem bodyContext_exact
    {leftGenerated rightGenerated : Generated}
    {left : PrincipalBlockClosure leftGenerated}
    {right : PrincipalBlockClosure rightGenerated}
    {context : Context} {boundary : Supply}
    (alignment : FreshClosureAlignment left right context boundary) :
    (((context.applyFree left.substitution).generalize left.target ::
        context.applyFree left.substitution).map
      (Scheme.applyFree alignment.alignment.rho.substitution)) =
      ((context.applyFree right.substitution).generalize right.target ::
        context.applyFree right.substitution) :=
  alignment.alignment.bodyContext_exact

end FreshClosureAlignment

namespace Supply.WellFormedFor

/-- Generalization adds no new free context names, so adjoining the
generalized scheme preserves a well-formed supply. -/
theorem generalized_cons
    {boundary : Supply} {context : Context}
    (wellFormed : boundary.WellFormedFor context) (target : Ty) :
    boundary.WellFormedFor (context.generalize target :: context) := by
  simp only [Supply.WellFormedFor, Context.initialSupply, Supply.Le,
    List.flatMap_cons]
  constructor
  · apply TyVar.next_le_of_forall_lt
    intro index member
    rcases List.mem_append.mp member with head | tail
    · have freeHead : index ∈ (context.generalize target).freeTyVars :=
        head
      have inContext :=
        (Context.mem_generalize_freeTyVars.mp freeHead).2
      exact Nat.lt_of_lt_of_le
        (Context.freeTy_index_lt_initialSupply inContext) wellFormed.1
    · exact Nat.lt_of_lt_of_le
        (Context.freeTy_index_lt_initialSupply ((mem_dedupFirst).2 tail))
        wellFormed.1
  · apply CapVar.next_le_of_forall_lt
    intro index member
    rcases List.mem_append.mp member with head | tail
    · have freeHead : index ∈ (context.generalize target).freeCapVars :=
        head
      have inContext :=
        (Context.mem_generalize_freeCapVars.mp freeHead).2
      exact Nat.lt_of_lt_of_le
        (Context.freeCap_index_lt_initialSupply inContext) wellFormed.2
    · exact Nat.lt_of_lt_of_le
        (Context.freeCap_index_lt_initialSupply ((mem_dedupFirst).2 tail))
        wellFormed.2

/-- A freshly allocated monomorphic ordinary variable can be adjoined after
advancing the ordinary supply once. -/
theorem monomorphic_cons_nextTy
    {boundary : Supply} {context : Context}
    (wellFormed : boundary.WellFormedFor context) :
    (boundary.nextTy 1).WellFormedFor
      (.mono (.var ⟨boundary.ty⟩) :: context) := by
  simp only [Supply.WellFormedFor, Context.initialSupply, Supply.Le,
    List.flatMap_cons]
  constructor
  · apply TyVar.next_le_of_forall_lt
    intro index member
    rcases List.mem_append.mp member with head | tail
    · have equality : index = ⟨boundary.ty⟩ := by
        change index ∈ dedupFirst [⟨boundary.ty⟩] at head
        simpa using (mem_dedupFirst.mp head)
      subst index
      simp [Supply.nextTy]
    · have below := Context.freeTy_index_lt_initialSupply
          ((mem_dedupFirst).2 tail)
      simp only [Supply.WellFormedFor, Supply.Le] at wellFormed
      simp only [Supply.nextTy]
      exact Nat.le_trans
        (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le below wellFormed.1))
        (Nat.le_add_right _ _)
  · apply CapVar.next_le_of_forall_lt
    intro index member
    rcases List.mem_append.mp member with head | tail
    · change index ∈ dedupFirst [] at head
      simpa using (mem_dedupFirst.mp head)
    · have below := Context.freeCap_index_lt_initialSupply
          ((mem_dedupFirst).2 tail)
      simp only [Supply.WellFormedFor, Supply.Le] at wellFormed
      simpa [Supply.nextTy] using Nat.lt_of_lt_of_le below wellFormed.2

end Supply.WellFormedFor

mutual

/-- A renaming which is already fixed on the entire future fresh stream
transports a well-formed elaboration without changing either numeric supply.
This is stronger than a bare `Alignment.transport` endpoint: it constructs
the finite alignment certificate structurally, including through nested
`letE` nodes. -/
theorem Elaborates.alignment_of_fixesAtOrAbove
    {rho : VariableRenaming}
    {context : Context} {expression : Expr} {start next : Supply}
    {generated : Generated}
    (derivation : Elaborates context expression start generated next)
    (wellFormed : start.WellFormedFor context)
    (fixed : rho.FixesAtOrAbove start) :
    ElaborationRenaming.Alignment rho derivation start next := by
  cases derivation with
  | @var context index start scheme lookup =>
      exact .var lookup
        (fixed.mapsFrom_self.mapsPrefix scheme.tyArity scheme.capArity)
  | lit => exact .lit
  | @something context start =>
      exact .something (fixed.1 ⟨start.ty⟩ (Nat.le_refl _))
  | @lam context body start generatedBody next bodyDerivation =>
      have bodyFixed := fixed.mono (Supply.le_nextTy start 1)
      have bodyAlignment := bodyDerivation.alignment_of_fixesAtOrAbove
        wellFormed.monomorphic_cons_nextTy bodyFixed
      exact .lam (fixed.1 ⟨start.ty⟩ (Nat.le_refl _)) bodyAlignment
  | @app context function argument start generatedFunction afterFunction
      generatedArgument afterArgument functionDerivation argumentDerivation =>
      have functionAlignment :=
        functionDerivation.alignment_of_fixesAtOrAbove wellFormed fixed
      have argumentWellFormed :=
        wellFormed.mono functionDerivation.supply_le_next
      have argumentFixed :=
        fixed.mono functionDerivation.supply_le_next
      have argumentAlignment :=
        argumentDerivation.alignment_of_fixesAtOrAbove
          argumentWellFormed argumentFixed
      have startToArgument : start.Le afterArgument :=
        Supply.le_trans functionDerivation.supply_le_next
          argumentDerivation.supply_le_next
      exact .app functionAlignment argumentAlignment
        (fixed.1 ⟨afterArgument.ty⟩ startToArgument.1)
        (fixed.1 ⟨afterArgument.ty + 1⟩
          (Nat.le_trans startToArgument.1 (Nat.le_add_right _ _)))
  | @tuple context items start generatedItems next itemsDerivation =>
      exact .tuple
        (itemsDerivation.alignment_of_fixesAtOrAbove wellFormed fixed)
  | @letE context value body start generatedValue afterValue generatedBody
      next valueDerivation closure absorbing bodyDerivation =>
      have valueAlignment :=
        valueDerivation.alignment_of_fixesAtOrAbove wellFormed fixed
      have sourceBodySupply :
          afterValue.join
              (context.applyFree closure.substitution).initialSupply =
            afterValue :=
        valueDerivation.letBodySupply_eq closure absorbing wellFormed
      let renamedClosure := ElaborationRenaming.renameClosure rho closure
      have renamedAbsorbing : renamedClosure.Absorbing :=
        ElaborationRenaming.renameClosure_absorbing rho closure absorbing
      have renamedValueDerivation := valueAlignment.transport
      have renamedWellFormed :
          start.WellFormedFor
            (ElaborationRenaming.renameContext rho context) :=
        fixed.wellFormedFor_renameContext wellFormed
      have targetBodySupply :
          afterValue.join
              ((ElaborationRenaming.renameContext rho context).applyFree
                renamedClosure.substitution).initialSupply =
            afterValue :=
        renamedValueDerivation.letBodySupply_eq renamedClosure
          renamedAbsorbing renamedWellFormed
      have closedWellFormed :
          afterValue.WellFormedFor
            (context.applyFree closure.substitution) :=
        valueDerivation.closedContext_initialSupply_le closure absorbing
          wellFormed
      have bodyWellFormedAtFinish :=
        closedWellFormed.generalized_cons closure.target
      have bodyWellFormed :
          Supply.WellFormedFor
              ((context.applyFree closure.substitution).generalize
                  closure.target ::
                context.applyFree closure.substitution)
            (afterValue.join
              (context.applyFree closure.substitution).initialSupply) := by
        rw [sourceBodySupply]
        exact bodyWellFormedAtFinish
      have startToBody : start.Le
          (afterValue.join
            (context.applyFree closure.substitution).initialSupply) :=
        Supply.le_trans valueDerivation.supply_le_next
          (Supply.le_join_left _ _)
      have bodyAlignment :=
        bodyDerivation.alignment_of_fixesAtOrAbove bodyWellFormed
          (fixed.mono startToBody)
      have bodyStartsEqual :
          afterValue.join
              ((ElaborationRenaming.renameContext rho context).applyFree
                renamedClosure.substitution).initialSupply =
            afterValue.join
              (context.applyFree closure.substitution).initialSupply := by
        rw [targetBodySupply, sourceBodySupply]
      have targetBodyAlignment : ElaborationRenaming.Alignment rho
          bodyDerivation
          (afterValue.join
            ((ElaborationRenaming.renameContext rho context).applyFree
              renamedClosure.substitution).initialSupply)
          next := by
        rw [bodyStartsEqual]
        exact bodyAlignment
      exact ElaborationRenaming.Alignment.letE
        (absorbing := absorbing) valueAlignment targetBodyAlignment

/-- List counterpart of `Elaborates.alignment_of_fixesAtOrAbove`. -/
theorem ElaboratesItems.alignment_of_fixesAtOrAbove
    {rho : VariableRenaming}
    {context : Context} {expressions : List Expr} {start next : Supply}
    {generated : GeneratedItems}
    (derivation :
      ElaboratesItems context expressions start generated next)
    (wellFormed : start.WellFormedFor context)
    (fixed : rho.FixesAtOrAbove start) :
    ElaborationRenaming.ItemsAlignment rho derivation start next := by
  cases derivation with
  | nil => exact .nil
  | @cons context item items start generatedItem afterItem generatedItems
      next itemDerivation itemsDerivation =>
      have itemAlignment :=
        itemDerivation.alignment_of_fixesAtOrAbove wellFormed fixed
      have itemsWellFormed := wellFormed.mono itemDerivation.supply_le_next
      have itemsFixed := fixed.mono itemDerivation.supply_le_next
      exact .cons itemAlignment
        (itemsDerivation.alignment_of_fixesAtOrAbove
          itemsWellFormed itemsFixed)

end

/-- Direct transport corollary used at the body of a nested `letE`. -/
theorem Elaborates.transport_of_fixesAtOrAbove
    {rho : VariableRenaming}
    {context : Context} {expression : Expr} {start next : Supply}
    {generated : Generated}
    (derivation : Elaborates context expression start generated next)
    (wellFormed : start.WellFormedFor context)
    (fixed : rho.FixesAtOrAbove start) :
    Elaborates (ElaborationRenaming.renameContext rho context)
      expression start (ElaborationRenaming.renameGenerated rho generated)
      next :=
  (derivation.alignment_of_fixesAtOrAbove wellFormed fixed).transport

/-- Interface equations produced by a completed value cannot mention names
hidden strictly later by the body comparison. -/
theorem Elaborates.interfaceEquations_avoid_laterHidden
    {context : Context} {value : Expr} {start afterValue finish : Supply}
    {generatedValue : Generated}
    (valueDerivation :
      Elaborates context value start generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (wellFormed : start.WellFormedFor context)
    {hidden : List UnificationVar}
    (hiddenFresh : VariablesFreshIn afterValue finish hidden) :
    EquationsAvoid hidden
      (context.interfaceEquations closure.substitution) := by
  intro candidate interfaceMember hiddenMember
  have interfaceBelow := Context.interfaceEquations_support_below
    (closure.localized_of_absorbing absorbing)
    valueDerivation.supportProvenance wellFormed
    valueDerivation.supply_le_next candidate interfaceMember
  have hiddenRange := hiddenFresh candidate hiddenMember
  cases candidate with
  | ty index =>
      exact (Nat.not_le_of_gt interfaceBelow) hiddenRange.1
  | cap index =>
      exact (Nat.not_le_of_gt interfaceBelow) hiddenRange.1

/-- Equation-level common core together with the target and pending
equalities required to move it through a generated frame. -/
structure GeneratedEquationCommonCore (left right : Generated) where
  equations : InterfaceAliasDecomposition.EquationLists.EquationCommonCore
    left.hard right.hard
  target_eq : left.target = right.target
  pending_eq : left.pending = right.pending

namespace GeneratedEquationCommonCore

open InterfaceAliasDecomposition.EquationLists

private noncomputable def prependListSame {left right : List Equation}
    (initial : List Equation) (decomposition : EquationCommonCore left right) :
    EquationCommonCore (initial ++ left) (initial ++ right) :=
  match initial with
  | [] => decomposition
  | equation :: tail =>
      EquationCommonCore.prependSame equation
        (prependListSame tail decomposition)

@[simp] private theorem prependListSame_core
    {left right : List Equation} (initial : List Equation)
    (decomposition : EquationCommonCore left right) :
    (prependListSame initial decomposition).core =
      initial ++ decomposition.core := by
  induction initial with
  | nil => rfl
  | cons equation tail induction =>
      simp [prependListSame, EquationCommonCore.prependSame, induction]

@[simp] private theorem prependListSame_leftAliases
    {left right : List Equation} (initial : List Equation)
    (decomposition : EquationCommonCore left right) :
    (prependListSame initial decomposition).leftAliases =
      decomposition.leftAliases := by
  induction initial with
  | nil => rfl
  | cons equation tail induction =>
      simp [prependListSame, EquationCommonCore.prependSame, induction]

@[simp] private theorem prependListSame_rightAliases
    {left right : List Equation} (initial : List Equation)
    (decomposition : EquationCommonCore left right) :
    (prependListSame initial decomposition).rightAliases =
      decomposition.rightAliases := by
  induction initial with
  | nil => rfl
  | cons equation tail induction =>
      simp [prependListSame, EquationCommonCore.prependSame, induction]

/-- A common core remains a common core under every source-generated frame.
The aliases are unchanged; only their shared core is enlarged by the fixed
frame material. -/
noncomputable def frame
    {left right : Generated}
    (decomposition : GeneratedEquationCommonCore left right)
    (generatedFrame : GeneratedFrame) :
    GeneratedEquationCommonCore
      (generatedFrame.plug left) (generatedFrame.plug right) := by
  induction generatedFrame generalizing left right with
  | hole => exact decomposition
  | lam domain outer induction =>
      apply induction
      exact
        { equations := decomposition.equations
          target_eq := by
            simp [Generated.fromLam, decomposition.target_eq]
          pending_eq := decomposition.pending_eq }
  | appFunction argument domain target outer induction =>
      apply induction
      let suffix := argument.hard ++
        [.ty left.target (.fn domain target)]
      have suffixEquality : suffix = argument.hard ++
          [.ty right.target (.fn domain target)] := by
        simp [suffix, decomposition.target_eq]
      let prepared := decomposition.equations.appendSame suffix
      exact
        { equations :=
            { core := prepared.core
              leftAliases := prepared.leftAliases
              rightAliases := prepared.rightAliases
              leftEquivalent := by
                simpa [prepared, suffix, Generated.fromApp,
                  List.append_assoc] using prepared.leftEquivalent
              rightEquivalent := by
                change HardEquivalent _
                  (right.hard ++ argument.hard ++
                    [.ty right.target (.fn domain target)])
                rw [List.append_assoc]
                rw [← suffixEquality]
                exact prepared.rightEquivalent }
          target_eq := rfl
          pending_eq := by
            change left.pending ++ argument.pending ++
                [⟨argument.target, domain⟩] =
              right.pending ++ argument.pending ++
                [⟨argument.target, domain⟩]
            rw [decomposition.pending_eq] }
  | appArgument function domain target outer induction =>
      apply induction
      let prepared := prependListSame function.hard
        (decomposition.equations.appendSame
          [.ty function.target (.fn domain target)])
      exact
        { equations :=
            { core := prepared.core
              leftAliases := prepared.leftAliases
              rightAliases := prepared.rightAliases
              leftEquivalent := by
                simpa [prepared, Generated.fromApp, List.append_assoc] using
                  prepared.leftEquivalent
              rightEquivalent := by
                simpa [prepared, Generated.fromApp, List.append_assoc] using
                  prepared.rightEquivalent }
          target_eq := rfl
          pending_eq := by
            change function.pending ++ left.pending ++
                [⟨left.target, domain⟩] =
              function.pending ++ right.pending ++
                [⟨right.target, domain⟩]
            rw [decomposition.pending_eq, decomposition.target_eq] }
  | tupleItem before after outer induction =>
      apply induction
      let prepared := prependListSame before.hard
        (decomposition.equations.appendSame after.hard)
      exact
        { equations :=
            { core := prepared.core
              leftAliases := prepared.leftAliases
              rightAliases := prepared.rightAliases
              leftEquivalent := by
                simpa [prepared, GeneratedItems.asTuple,
                  GeneratedItems.append, GeneratedItems.singleton,
                  GeneratedItems.cons, GeneratedItems.nil,
                  List.append_assoc] using prepared.leftEquivalent
              rightEquivalent := by
                simpa [prepared, GeneratedItems.asTuple,
                  GeneratedItems.append, GeneratedItems.singleton,
                  GeneratedItems.cons, GeneratedItems.nil,
                  List.append_assoc] using prepared.rightEquivalent }
          target_eq := by
            simp only [GeneratedItems.asTuple, GeneratedItems.append,
              GeneratedItems.singleton, GeneratedItems.cons,
              GeneratedItems.nil, List.append_assoc]
            rw [decomposition.target_eq]
          pending_eq := by
            simp only [GeneratedItems.asTuple, GeneratedItems.append,
              GeneratedItems.singleton, GeneratedItems.cons,
              GeneratedItems.nil, List.append_assoc]
            rw [decomposition.pending_eq] }
  | letBody effects outer induction =>
      apply induction
      exact
        { equations := prependListSame effects decomposition.equations
          target_eq := decomposition.target_eq
          pending_eq := decomposition.pending_eq }

@[simp] theorem frame_leftAliases
    {left right : Generated}
    (decomposition : GeneratedEquationCommonCore left right)
    (generatedFrame : GeneratedFrame) :
    (decomposition.frame generatedFrame).equations.leftAliases =
      decomposition.equations.leftAliases := by
  induction generatedFrame generalizing left right <;>
    simp_all [frame, EquationCommonCore.appendSame]

@[simp] theorem frame_rightAliases
    {left right : Generated}
    (decomposition : GeneratedEquationCommonCore left right)
    (generatedFrame : GeneratedFrame) :
    (decomposition.frame generatedFrame).equations.rightAliases =
      decomposition.equations.rightAliases := by
  induction generatedFrame generalizing left right <;>
    simp_all [frame, EquationCommonCore.appendSame]

/-- Shared generated block underlying the equation decomposition after a
frame has been applied.  The target and pending list are common by the other
two fields of `GeneratedEquationCommonCore`. -/
noncomputable def framedCore
    {left right : Generated}
    (decomposition : GeneratedEquationCommonCore left right)
    (generatedFrame : GeneratedFrame) : Generated :=
  let framed := decomposition.frame generatedFrame
  { target := (generatedFrame.plug left).target
    hard := framed.equations.core
    pending := (generatedFrame.plug left).pending }

/-- Exact freshness obligation for lifting an equation common core to every
admissible enclosing source frame. -/
def FrameAdmissible
    (hidden : List UnificationVar)
    {left right : Generated}
    (decomposition : GeneratedEquationCommonCore left right) : Prop :=
  ∀ generatedFrame, generatedFrame.Avoids hidden →
    let framed := decomposition.frame generatedFrame
    FreshAliasSequence.Admissible framed.equations.leftAliases
        (decomposition.framedCore generatedFrame) ∧
      FreshAliasSequence.Admissible framed.equations.rightAliases
        (decomposition.framedCore generatedFrame)

/-- Frame-wise alias admissibility upgrades the equation decomposition to
the target-aware contextual relation consumed by ordinary source
constructors. -/
theorem scopedContextualEquivalent_of_frameAdmissible
    {hidden : List UnificationVar} {left right : Generated}
    (decomposition : GeneratedEquationCommonCore left right)
    (admissible : FrameAdmissible hidden decomposition) :
    Generated.ScopedContextualEquivalent hidden left right := by
  intro generatedFrame frameAvoids
  let framed := decomposition.frame generatedFrame
  let core := decomposition.framedCore generatedFrame
  obtain ⟨leftAdmissible, rightAdmissible⟩ :=
    admissible generatedFrame frameAvoids
  have common : FreshAliasSequence.CommonCoreEquivalent
      (generatedFrame.plug left) (generatedFrame.plug right) := by
    refine ⟨core, framed.equations.leftAliases,
      framed.equations.rightAliases, leftAdmissible, rightAdmissible,
      ?_, ?_, ?_, ?_⟩
    · rw [InterfaceAliasDecomposition.EquationLists.addAll_hard]
      exact framed.equations.leftEquivalent
    · rw [InterfaceAliasDecomposition.EquationLists.addAll_hard]
      exact framed.equations.rightEquivalent
    · simp [core, framedCore]
    · simp [core, framedCore, framed.pending_eq]
  exact common.blockAccepts_iff

end GeneratedEquationCommonCore

namespace GeneratedFrame

/-- Avoidance is closed under plugging an avoiding block into an avoiding
frame.  This is the support fact needed to reuse one local-alias certificate
under every admissible enclosing source constructor. -/
theorem plug_avoids
    {hidden : List UnificationVar} {frame : GeneratedFrame}
    {generated : Generated}
    (frameAvoids : frame.Avoids hidden)
    (generatedAvoids : GeneratedAvoids hidden generated) :
    GeneratedAvoids hidden (frame.plug generated) := by
  induction frame generalizing generated with
  | hole => exact generatedAvoids
  | lam domain outer induction =>
      rcases frameAvoids with ⟨domainAvoids, outerAvoids⟩
      apply induction outerAvoids
      simp_all [GeneratedAvoids, VariablesAvoid,
        Generated.fromLam, Generated.unificationVars,
        Ty.unificationVars]
      intro candidate member
      rcases member with domainMember | targetMember | hardMember |
          pendingMember
      · exact domainAvoids candidate domainMember
      · exact generatedAvoids candidate (Or.inl targetMember)
      · exact generatedAvoids candidate (Or.inr (Or.inl hardMember))
      · exact generatedAvoids candidate (Or.inr (Or.inr pendingMember))
  | appFunction argument domain target outer induction =>
      rcases frameAvoids with ⟨argumentAvoids, domainAvoids,
        targetAvoids, outerAvoids⟩
      apply induction outerAvoids
      simp_all [GeneratedAvoids, VariablesAvoid,
        Generated.fromApp, Generated.unificationVars,
        Equation.unificationVars, CheckObligation.unificationVars,
        pendingUnificationVars, TypePM.unificationVars, Ty.unificationVars]
      intro candidate member
      rcases member with targetMember | generatedHard | argumentHard |
          generatedTarget | domainMember | targetMember | generatedPending |
          argumentPending | argumentTarget | domainMember
      · exact targetAvoids candidate targetMember
      · exact generatedAvoids candidate (Or.inr (Or.inl generatedHard))
      · exact argumentAvoids candidate (Or.inr (Or.inl argumentHard))
      · exact generatedAvoids candidate (Or.inl generatedTarget)
      · exact domainAvoids candidate domainMember
      · exact targetAvoids candidate targetMember
      · exact generatedAvoids candidate (Or.inr (Or.inr generatedPending))
      · exact argumentAvoids candidate (Or.inr (Or.inr argumentPending))
      · exact argumentAvoids candidate (Or.inl argumentTarget)
      · exact domainAvoids candidate domainMember
  | appArgument function domain target outer induction =>
      rcases frameAvoids with ⟨functionAvoids, domainAvoids,
        targetAvoids, outerAvoids⟩
      apply induction outerAvoids
      simp_all [GeneratedAvoids, VariablesAvoid,
        Generated.fromApp, Generated.unificationVars,
        Equation.unificationVars, CheckObligation.unificationVars,
        pendingUnificationVars, TypePM.unificationVars, Ty.unificationVars]
      intro candidate member
      rcases member with targetMember | functionHard | generatedHard |
          functionTarget | domainMember | targetMember | functionPending |
          generatedPending | generatedTarget | domainMember
      · exact targetAvoids candidate targetMember
      · exact functionAvoids candidate (Or.inr (Or.inl functionHard))
      · exact generatedAvoids candidate (Or.inr (Or.inl generatedHard))
      · exact functionAvoids candidate (Or.inl functionTarget)
      · exact domainAvoids candidate domainMember
      · exact targetAvoids candidate targetMember
      · exact functionAvoids candidate (Or.inr (Or.inr functionPending))
      · exact generatedAvoids candidate (Or.inr (Or.inr generatedPending))
      · exact generatedAvoids candidate (Or.inl generatedTarget)
      · exact domainAvoids candidate domainMember
  | tupleItem before after outer induction =>
      rcases frameAvoids with ⟨beforeAvoids, afterAvoids, outerAvoids⟩
      apply induction outerAvoids
      have itemAvoids : GeneratedItemsAvoid hidden
          (GeneratedItems.singleton generated) :=
        GeneratedItemsAvoid.singleton generatedAvoids
      have innerAvoids := GeneratedItemsAvoid.append itemAvoids afterAvoids
      have combinedAvoids := GeneratedItemsAvoid.append beforeAvoids innerAvoids
      intro candidate member hiddenMember
      apply combinedAvoids candidate ?_ hiddenMember
      simpa only [GeneratedItems.asTuple, Generated.unificationVars,
        Ty.unificationVars, GeneratedItems.unificationVars] using member
  | letBody effects outer induction =>
      rcases frameAvoids with ⟨effectsAvoids, outerAvoids⟩
      apply induction outerAvoids
      simp_all [GeneratedAvoids, VariablesAvoid,
        Generated.fromLet, Generated.unificationVars]
      intro candidate member
      rcases member with targetMember | effectsMember | hardMember |
          pendingMember
      · exact generatedAvoids candidate (Or.inl targetMember)
      · exact effectsAvoids candidate effectsMember
      · exact generatedAvoids candidate (Or.inr (Or.inl hardMember))
      · exact generatedAvoids candidate (Or.inr (Or.inr pendingMember))

end GeneratedFrame

/-- Final composition law for a heterogeneous `letE` step.  The interface
comparison accounts for the two value-closure representatives; the body
comparison accounts for recursive elaboration after transporting the left
body to the right body context.  Their hidden-name intervals are disjoint
and concatenate.

This theorem makes the two genuinely remaining obligations explicit:
constructing `interfaceRelated` from the closure alignment, and recursively
constructing `bodyComparison`. -/
theorem scopedLetStep
    {start afterValue leftNext rightNext : Supply}
    {leftEffects rightEffects : List Equation}
    {leftBody transportedLeftBody rightBody : Generated}
    {interfaceHidden : List UnificationVar}
    (startToValue : start.Le afterValue)
    (valueToBodyFinish : afterValue.Le leftNext)
    (interfaceFresh :
      VariablesFreshIn start afterValue interfaceHidden)
    (interfaceRelated : Generated.ScopedContextualEquivalent
      interfaceHidden
      (Generated.fromLet leftEffects leftBody)
      (Generated.fromLet rightEffects transportedLeftBody))
    (bodyComparison : ScopedGeneratedComparison afterValue
      leftNext rightNext transportedLeftBody rightBody)
    (rightEffectsAvoidBodyHidden :
      ∀ hidden, VariablesFreshIn afterValue leftNext hidden →
        EquationsAvoid hidden rightEffects) :
    ScopedGeneratedComparison start leftNext rightNext
      (Generated.fromLet leftEffects leftBody)
      (Generated.fromLet rightEffects rightBody) := by
  obtain ⟨nextEquality, bodyHidden, bodyFresh, bodyRelated⟩ :=
    bodyComparison
  subst rightNext
  let hidden := interfaceHidden ++ bodyHidden
  refine ⟨rfl, hidden, ?_, ?_⟩
  · exact VariablesFreshIn.append
      (interfaceFresh.widen (Supply.le_refl start) valueToBodyFinish)
      (bodyFresh.widen startToValue (Supply.le_refl leftNext))
  · have interfaceAtCombined := interfaceRelated.antitone
        (larger := hidden)
        (fun candidate member => List.mem_append_left _ member)
    have bodyUnderInterface :=
      Generated.ScopedContextualEquivalent.letBody rightEffects
        (rightEffectsAvoidBodyHidden bodyHidden bodyFresh) bodyRelated
    have bodyAtCombined := bodyUnderInterface.antitone
      (larger := hidden)
      (fun candidate member => List.mem_append_right _ member)
    exact interfaceAtCombined.trans bodyAtCombined

/-- The stronger induction hypothesis needed for the value child of a
`letE`.  Unlike `ScopedGeneratedComparison`, it quantifies over the principal
closures subsequently chosen by the two parent constructors.

The well-formed supply premise is part of the invariant because the same
claim is false for a supply below `context.initialSupply`. -/
def ClosureAlignedElaborations : Prop :=
  ∀ {context : Context} {expression : Expr} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      Elaborates context expression start leftGenerated leftNext →
        Elaborates context expression start rightGenerated rightNext →
          leftNext = rightNext ∧
            ∀ (leftClosure : PrincipalBlockClosure leftGenerated)
                (rightClosure : PrincipalBlockClosure rightGenerated),
              leftClosure.Absorbing → rightClosure.Absorbing →
                Nonempty (FreshClosureAlignment
                  leftClosure rightClosure context leftNext)

/-- Any closure-aligned elaboration invariant already contains the exact
supply agreement needed by sequential source constructors. -/
theorem ClosureAlignedElaborations.next_eq
    (coherent : ClosureAlignedElaborations)
    {context : Context} {expression : Expr} {start : Supply}
    {leftGenerated rightGenerated : Generated}
    {leftNext rightNext : Supply}
    (wellFormed : start.WellFormedFor context)
    (leftElaboration : Elaborates context expression start
      leftGenerated leftNext)
    (rightElaboration : Elaborates context expression start
      rightGenerated rightNext) :
    leftNext = rightNext :=
  (coherent wellFormed leftElaboration rightElaboration).1

/-- The same invariant supplies the heterogeneous closure transport consumed
at a nested `letE` boundary. -/
theorem ClosureAlignedElaborations.closureAlignment
    (coherent : ClosureAlignedElaborations)
    {context : Context} {expression : Expr} {start : Supply}
    {leftGenerated rightGenerated : Generated}
    {leftNext rightNext : Supply}
    (wellFormed : start.WellFormedFor context)
    (leftElaboration : Elaborates context expression start
      leftGenerated leftNext)
    (rightElaboration : Elaborates context expression start
      rightGenerated rightNext)
    (leftClosure : PrincipalBlockClosure leftGenerated)
    (rightClosure : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : leftClosure.Absorbing)
    (rightAbsorbing : rightClosure.Absorbing) :
    Nonempty (FreshClosureAlignment
      leftClosure rightClosure context leftNext) :=
  (coherent wellFormed leftElaboration rightElaboration).2
    leftClosure rightClosure leftAbsorbing rightAbsorbing

end TypePM.Source
