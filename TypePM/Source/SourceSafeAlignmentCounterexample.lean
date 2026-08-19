import TypePM.Source.DirectLetComparison

/-!
# A source-derived obstruction to support-local closure alignment

The concrete inner-let example below has two elaborations of the same source
term from a well-formed supply.  At that `let`, the same
value block has two absorbing principal closures whose targets choose the
two opposite representatives of a variable equality.  One representative
is inherited from the enclosing context and therefore lies below the value
interval.  Consequently no closure alignment can both transport the two
targets and fix every name outside a fresh value interval.
-/

namespace TypePM.Source.SourceSafeAlignmentCounterexample

open TypePM.Source

private def inherited : TyVar := ⟨0⟩
private def representative : TyVar := ⟨3⟩
private def valueStart : Supply := ⟨1, 0⟩
private def valueFinish : Supply := ⟨4, 0⟩
private def context : Context := [.mono (.var inherited)]

private theorem inherited_ne_representative :
    inherited ≠ representative := by decide

/-- Any fresh interval for the inner value excludes its inherited context
variable. -/
private theorem inherited_outside
    {hidden : List UnificationVar}
    (fresh : VariablesFreshIn valueStart valueFinish hidden) :
    .ty inherited ∉ hidden := by
  intro member
  have range := fresh (.ty inherited) member
  simp [UnificationVar.FreshIn, valueStart, inherited] at range

/-- The exact obstruction, independent of how the alignment was built. -/
theorem no_supported_target_alignment
    {rho : VariableRenaming} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn valueStart valueFinish hidden)
    (fixed : rho.FixesOutside hidden)
    (targetExact :
      (Ty.var representative).apply rho.substitution = .var inherited) :
    False := by
  have inheritedFixed : rho.tyForward inherited = inherited :=
    fixed.1 inherited (inherited_outside fresh)
  have representativeImage : rho.tyForward representative = inherited := by
    simpa [VariableRenaming.substitution, Ty.apply] using targetExact
  have same := rho.tyForward_injective
    (representativeImage.trans inheritedFixed.symm)
  exact inherited_ne_representative same.symm

private def valueExpression : Expr :=
  .app (.lam (.var 1)) (.lit 0)

private def valueGenerated : Generated :=
  { target := .var representative
    hard :=
      [.ty
        (.fn (.var ⟨1⟩) (.var inherited))
        (.fn (.var ⟨2⟩) (.var representative))]
    pending := [⟨.int, .var ⟨2⟩⟩] }

/-- The value block at the obstructing inner `let` is produced by an actual
source elaboration from a well-formed starting supply. -/
theorem value_elaborates :
    Elaborates context valueExpression valueStart
      valueGenerated valueFinish := by
  have varDerivation := Elaborates.var (supply := Supply.mk 2 0)
    (context := [.mono (.var ⟨1⟩), .mono (.var inherited)])
    (index := 1) (by rfl)
  have function := Elaborates.lam
    (context := [.mono (.var inherited)])
    (supply := Supply.mk 1 0) varDerivation
  have argument : Elaborates [.mono (.var inherited)] (.lit 0) ⟨2, 0⟩
      ⟨.int, [], []⟩ ⟨2, 0⟩ := .lit
  simpa [context, valueExpression, valueGenerated, Scheme.instantiate_mono,
    Supply.nextTy, valueStart, valueFinish, inherited, representative] using
      Elaborates.app function argument

theorem valueStart_wellFormed :
    valueStart.WellFormedFor context := by
  unfold Supply.WellFormedFor
  rw [show context.initialSupply = valueStart by decide]
  exact Supply.le_refl valueStart

private def firstInherited : Subst :=
  Subst.compose (Subst.singleTy inherited (.var representative))
    (Subst.singleTy ⟨1⟩ (.var ⟨2⟩))

private def finalInherited : Subst :=
  Subst.compose (Subst.singleTy ⟨2⟩ .int) firstInherited

private def firstRepresentative : Subst :=
  Subst.compose (Subst.singleTy representative (.var inherited))
    (Subst.singleTy ⟨1⟩ (.var ⟨2⟩))

private def finalRepresentative : Subst :=
  Subst.compose (Subst.singleTy ⟨2⟩ .int) firstRepresentative

private def promotedHard : List Equation :=
  valueGenerated.hard ++ [.ty .int (.var ⟨2⟩)]

private def promotion : Promotion :=
  { equations := [.ty .int (.var ⟨2⟩)]
    pending := [] }

private def reduceFunction :
    Reduces valueGenerated.hard Subst.id
      [.ty (.var ⟨1⟩) (.var ⟨2⟩),
        .ty (.var inherited) (.var representative)] := by
  exact .tyFn

private def reduceArgument :
    Reduces
      [.ty (.var ⟨1⟩) (.var ⟨2⟩),
        .ty (.var inherited) (.var representative)]
      (Subst.singleTy ⟨1⟩ (.var ⟨2⟩))
      [.ty (.var inherited) (.var representative)] := by
  apply Reduces.tyVarLeft
  simp [Ty.occursTy]

private def reduceInherited :
    Reduces [.ty (.var inherited) (.var representative)]
      (Subst.singleTy inherited (.var representative)) [] := by
  apply Reduces.tyVarLeft
  simp [inherited, representative, Ty.occursTy]

private def reduceRepresentative :
    Reduces [.ty (.var inherited) (.var representative)]
      (Subst.singleTy representative (.var inherited)) [] := by
  apply Reduces.tyVarRight
  simp [inherited, representative, Ty.occursTy]

private theorem firstInherited_absorbing :
    AbsorbingPrincipal valueGenerated.hard firstInherited := by
  constructor
  · constructor
    · simp [valueGenerated, firstInherited, Equation.Holds,
        Subst.compose, Subst.singleTy, Ty.apply,
        inherited, representative]
    · intro solution solved
      refine ⟨solution, ?_⟩
      have afterFunction := reduceFunction.complete solved
      have afterArgument := reduceArgument.complete afterFunction
      have absorbedArgument := reduceArgument.absorbed afterFunction
      have absorbedInherited := reduceInherited.absorbed afterArgument
      exact (show Subst.compose solution firstInherited = solution from by
        simp only [firstInherited, Subst.compose_assoc]
        rw [absorbedInherited, absorbedArgument]).symm
  · intro solution solved
    have afterFunction := reduceFunction.complete solved
    have afterArgument := reduceArgument.complete afterFunction
    have absorbedArgument := reduceArgument.absorbed afterFunction
    have absorbedInherited := reduceInherited.absorbed afterArgument
    show Subst.compose solution firstInherited = solution
    simp only [firstInherited, Subst.compose_assoc]
    rw [absorbedInherited, absorbedArgument]

private theorem firstRepresentative_absorbing :
    AbsorbingPrincipal valueGenerated.hard firstRepresentative := by
  constructor
  · constructor
    · simp [valueGenerated, firstRepresentative, Equation.Holds,
        Subst.compose, Subst.singleTy, Ty.apply,
        inherited, representative]
    · intro solution solved
      refine ⟨solution, ?_⟩
      have afterFunction := reduceFunction.complete solved
      have afterArgument := reduceArgument.complete afterFunction
      have absorbedArgument := reduceArgument.absorbed afterFunction
      have absorbedRepresentative := reduceRepresentative.absorbed afterArgument
      exact (show Subst.compose solution firstRepresentative = solution from by
        simp only [firstRepresentative, Subst.compose_assoc]
        rw [absorbedRepresentative, absorbedArgument]).symm
  · intro solution solved
    have afterFunction := reduceFunction.complete solved
    have afterArgument := reduceArgument.complete afterFunction
    have absorbedArgument := reduceArgument.absorbed afterFunction
    have absorbedRepresentative := reduceRepresentative.absorbed afterArgument
    show Subst.compose solution firstRepresentative = solution
    simp only [firstRepresentative, Subst.compose_assoc]
    rw [absorbedRepresentative, absorbedArgument]

private def reduceFunctionFinal :
    Reduces promotedHard Subst.id
      [.ty (.var ⟨1⟩) (.var ⟨2⟩),
        .ty (.var inherited) (.var representative),
        .ty .int (.var ⟨2⟩)] := by
  exact .tyFn

private def reduceArgumentFinal :
    Reduces
      [.ty (.var ⟨1⟩) (.var ⟨2⟩),
        .ty (.var inherited) (.var representative),
        .ty .int (.var ⟨2⟩)]
      (Subst.singleTy ⟨1⟩ (.var ⟨2⟩))
      [.ty (.var inherited) (.var representative),
        .ty .int (.var ⟨2⟩)] := by
  apply Reduces.tyVarLeft
  simp [Ty.occursTy]

private def reduceInheritedFinal :
    Reduces
      [.ty (.var inherited) (.var representative),
        .ty .int (.var ⟨2⟩)]
      (Subst.singleTy inherited (.var representative))
      [.ty .int (.var ⟨2⟩)] := by
  apply Reduces.tyVarLeft
  simp [inherited, representative, Ty.occursTy]

private def reduceRepresentativeFinal :
    Reduces
      [.ty (.var inherited) (.var representative),
        .ty .int (.var ⟨2⟩)]
      (Subst.singleTy representative (.var inherited))
      [.ty .int (.var ⟨2⟩)] := by
  apply Reduces.tyVarRight
  simp [inherited, representative, Ty.occursTy]

private def reduceDomainFinal :
    Reduces [.ty .int (.var ⟨2⟩)]
      (Subst.singleTy ⟨2⟩ .int) [] := by
  apply Reduces.tyVarRight
  simp [Ty.occursTy]

private theorem finalInherited_absorbing :
    AbsorbingPrincipal promotedHard finalInherited := by
  constructor
  · constructor
    · simp [promotedHard, valueGenerated, finalInherited, firstInherited,
        Equation.Holds, Subst.compose, Subst.singleTy, Ty.apply,
        inherited, representative]
    · intro solution solved
      refine ⟨solution, ?_⟩
      have afterFunction := reduceFunctionFinal.complete solved
      have afterArgument := reduceArgumentFinal.complete afterFunction
      have afterAlias := reduceInheritedFinal.complete afterArgument
      have absorbedArgument := reduceArgumentFinal.absorbed afterFunction
      have absorbedAlias := reduceInheritedFinal.absorbed afterArgument
      have absorbedDomain := reduceDomainFinal.absorbed afterAlias
      exact (show Subst.compose solution finalInherited = solution from by
        simp only [finalInherited, firstInherited, Subst.compose_assoc]
        rw [absorbedDomain, absorbedAlias, absorbedArgument]).symm
  · intro solution solved
    have afterFunction := reduceFunctionFinal.complete solved
    have afterArgument := reduceArgumentFinal.complete afterFunction
    have afterAlias := reduceInheritedFinal.complete afterArgument
    have absorbedArgument := reduceArgumentFinal.absorbed afterFunction
    have absorbedAlias := reduceInheritedFinal.absorbed afterArgument
    have absorbedDomain := reduceDomainFinal.absorbed afterAlias
    show Subst.compose solution finalInherited = solution
    simp only [finalInherited, firstInherited, Subst.compose_assoc]
    rw [absorbedDomain, absorbedAlias, absorbedArgument]

private theorem finalRepresentative_absorbing :
    AbsorbingPrincipal promotedHard finalRepresentative := by
  constructor
  · constructor
    · simp [promotedHard, valueGenerated, finalRepresentative,
        firstRepresentative, Equation.Holds, Subst.compose, Subst.singleTy,
        Ty.apply, inherited, representative]
    · intro solution solved
      refine ⟨solution, ?_⟩
      have afterFunction := reduceFunctionFinal.complete solved
      have afterArgument := reduceArgumentFinal.complete afterFunction
      have afterAlias := reduceRepresentativeFinal.complete afterArgument
      have absorbedArgument := reduceArgumentFinal.absorbed afterFunction
      have absorbedAlias := reduceRepresentativeFinal.absorbed afterArgument
      have absorbedDomain := reduceDomainFinal.absorbed afterAlias
      exact (show Subst.compose solution finalRepresentative = solution from by
        simp only [finalRepresentative, firstRepresentative,
          Subst.compose_assoc]
        rw [absorbedDomain, absorbedAlias, absorbedArgument]).symm
  · intro solution solved
    have afterFunction := reduceFunctionFinal.complete solved
    have afterArgument := reduceArgumentFinal.complete afterFunction
    have afterAlias := reduceRepresentativeFinal.complete afterArgument
    have absorbedArgument := reduceArgumentFinal.absorbed afterFunction
    have absorbedAlias := reduceRepresentativeFinal.absorbed afterArgument
    have absorbedDomain := reduceDomainFinal.absorbed afterAlias
    show Subst.compose solution finalRepresentative = solution
    simp only [finalRepresentative, firstRepresentative, Subst.compose_assoc]
    rw [absorbedDomain, absorbedAlias, absorbedArgument]

private theorem promotion_exact_inherited :
    promoteUnder firstInherited valueGenerated.pending = promotion := by
  simp [valueGenerated, firstInherited, promotion, promoteUnder,
    Subst.compose, Subst.singleTy, Ty.apply, Ty.couldSpecial,
    Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherProduct, Ty.mayBecomeExpectedMatcher,
    Ty.mayBecomeExpectedSlot, inherited, representative]

private theorem promotion_exact_representative :
    promoteUnder firstRepresentative valueGenerated.pending = promotion := by
  simp [valueGenerated, firstRepresentative, promotion, promoteUnder,
    Subst.compose, Subst.singleTy, Ty.apply, Ty.couldSpecial,
    Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherProduct, Ty.mayBecomeExpectedMatcher,
    Ty.mayBecomeExpectedSlot, inherited, representative]

private theorem id_absorbing : AbsorbingPrincipal [] Subst.id := by
  constructor
  · constructor
    · exact solves_nil _
    · intro solution _
      exact ⟨solution, by simp⟩
  · intro solution _
    simp

private def inheritedClosure : PrincipalBlockClosure valueGenerated :=
  { finalHard := promotedHard
    finalPending := []
    hardSubstitution := finalInherited
    residualSubstitution := Subst.id
    saturation :=
      { closure := .step firstInherited_absorbing.mostGeneral
          promotion_exact_inherited (by simp [promotion]) .refl
        principal := finalInherited_absorbing.mostGeneral
        stable := by simp [promoteUnder] }
    residualPrincipal := by
      simpa [residualEquations] using id_absorbing.mostGeneral }

private def representativeClosure : PrincipalBlockClosure valueGenerated :=
  { finalHard := promotedHard
    finalPending := []
    hardSubstitution := finalRepresentative
    residualSubstitution := Subst.id
    saturation :=
      { closure := .step firstRepresentative_absorbing.mostGeneral
          promotion_exact_representative (by simp [promotion]) .refl
        principal := finalRepresentative_absorbing.mostGeneral
        stable := by simp [promoteUnder] }
    residualPrincipal := by
      simpa [residualEquations] using id_absorbing.mostGeneral }

private theorem inheritedClosure_absorbing : inheritedClosure.Absorbing := by
  constructor
  · exact finalInherited_absorbing
  · simpa [inheritedClosure, residualEquations] using id_absorbing

private theorem representativeClosure_absorbing :
    representativeClosure.Absorbing := by
  constructor
  · exact finalRepresentative_absorbing
  · simpa [representativeClosure, residualEquations] using id_absorbing

@[simp] private theorem inheritedClosure_substitution :
    inheritedClosure.substitution = finalInherited := by
  simp [PrincipalBlockClosure.substitution, inheritedClosure]

@[simp] private theorem representativeClosure_substitution :
    representativeClosure.substitution = finalRepresentative := by
  simp [PrincipalBlockClosure.substitution, representativeClosure]

@[simp] private theorem inheritedClosure_target :
    inheritedClosure.target = .var representative := by
  change (Ty.var representative).apply inheritedClosure.substitution = _
  simp [PrincipalBlockClosure.substitution,
    inheritedClosure, finalInherited, firstInherited, Subst.compose,
    Subst.singleTy, Ty.apply, inherited, representative]

@[simp] private theorem representativeClosure_target :
    representativeClosure.target = .var inherited := by
  change (Ty.var representative).apply representativeClosure.substitution = _
  simp [PrincipalBlockClosure.substitution,
    representativeClosure, finalRepresentative, firstRepresentative,
    Subst.compose, Subst.singleTy, Ty.apply, inherited, representative]

private def swap : VariableRenaming :=
  let permutation := FinitePermutation.swap inherited representative
  { tyForward := permutation.forward
    tyBackward := permutation.backward
    capForward := id
    capBackward := id
    ty_backward_forward := permutation.backward_forward
    ty_forward_backward := permutation.forward_backward
    cap_backward_forward := fun _ => rfl
    cap_forward_backward := fun _ => rfl }

private theorem swap_fixesAtOrAbove :
    swap.FixesAtOrAbove valueFinish := by
  constructor
  · intro index above
    have neither : index ≠ inherited ∧ index ≠ representative := by
      constructor <;> intro equality <;> subst index <;>
        simp [valueFinish, inherited, representative] at above
    simp [swap, FinitePermutation.swap, FinitePermutation.swapIndex,
      neither.1, neither.2]
  · intro _index _above
    rfl

/-- The usual closure alignment itself exists and is local below the value
finish.  Thus the later nonexistence of `SourceSafeWholeLetAlignment` is not
vacuous. -/
noncomputable def freshClosureAlignment : FreshClosureAlignment
    inheritedClosure representativeClosure context valueFinish := by
  have closedContextExact :
      (context.applyFree inheritedClosure.substitution).applyFree
          swap.substitution =
        context.applyFree representativeClosure.substitution := by
    simp [context, inheritedClosure_substitution,
      representativeClosure_substitution, finalInherited,
      firstInherited, finalRepresentative, firstRepresentative,
      swap, VariableRenaming.substitution, FinitePermutation.swap,
      FinitePermutation.swapIndex, Context.applyFree, Scheme.mono,
      Scheme.applyFree, PolyTy.applyFree, PolyTy.ofTy, Subst.compose,
      Subst.singleTy, Ty.apply, inherited, representative]
  have targetExact :
      inheritedClosure.target.apply swap.substitution =
        representativeClosure.target := by
    simp [inheritedClosure_target, representativeClosure_target,
      swap, VariableRenaming.substitution, FinitePermutation.swap,
      FinitePermutation.swapIndex, Ty.apply, inherited, representative]
  have generalizedExact :
      ((context.applyFree inheritedClosure.substitution).generalize
          inheritedClosure.target).applyFree swap.substitution =
        (context.applyFree representativeClosure.substitution).generalize
          representativeClosure.target := by
    rw [Context.generalize_variableRenaming_exact]
    rw [closedContextExact, targetExact]
  let equations :=
    InterfaceAliasDecomposition.EquationLists.EquationCommonCore.tyAlias_refl
      representative inherited []
  have equationsExact :
      InterfaceAliasDecomposition.EquationLists.EquationCommonCore
        ((context.interfaceEquations inheritedClosure.substitution).map
          (ElaborationRenaming.renameEquation swap))
        (context.interfaceEquations representativeClosure.substitution) := by
    simpa [context, inheritedClosure_substitution,
      representativeClosure_substitution, finalInherited,
      firstInherited, finalRepresentative, firstRepresentative,
      Context.interfaceEquations, Context.freeTyVars, Context.freeCapVars,
      Scheme.freeTyVars, Scheme.freeCapVars, Scheme.mono, PolyTy.ofTy,
      PolyTy.freeTyVars, PolyTy.freeCapVars, dedupFirst, dedup,
      List.idxOf, List.findIdx, List.findIdx.go,
      ElaborationRenaming.renameEquation, Equation.apply,
      swap, VariableRenaming.substitution, FinitePermutation.swap,
      FinitePermutation.swapIndex, Subst.compose, Subst.singleTy, Ty.apply,
      inherited, representative] using equations
  exact
    { alignment :=
        { rho := swap
          closedContext_exact := closedContextExact
          target_exact := targetExact
          generalized_exact := generalizedExact
          equations := equationsExact }
      fixesAtOrAbove := swap_fixesAtOrAbove }

private def emptyBody : Generated :=
  { target := .int, hard := [], pending := [] }

private def letExpression : Expr :=
  .letE valueExpression (.lit 0)

/-- The first obstructing closure is actually selected by a complete source
`let` derivation. -/
theorem inherited_let_elaborates :
    Elaborates context letExpression valueStart
      (Generated.fromLet
        (context.interfaceEquations inheritedClosure.substitution)
        emptyBody)
      valueFinish := by
  have bodyStart :
      valueFinish.join
          (context.applyFree inheritedClosure.substitution).initialSupply =
        valueFinish :=
    value_elaborates.letBodySupply_eq inheritedClosure
      inheritedClosure_absorbing valueStart_wellFormed
  have body : Elaborates
      ((context.applyFree inheritedClosure.substitution).generalize
          inheritedClosure.target ::
        context.applyFree inheritedClosure.substitution)
      (.lit 0) valueFinish emptyBody valueFinish := .lit
  rw [← bodyStart] at body
  exact .letE value_elaborates inheritedClosure
    inheritedClosure_absorbing body

/-- The opposite representative occurs in a second derivation of the same
source `let`, at the same well-formed start and finish. -/
theorem representative_let_elaborates :
    Elaborates context letExpression valueStart
      (Generated.fromLet
        (context.interfaceEquations representativeClosure.substitution)
        emptyBody)
      valueFinish := by
  have bodyStart :
      valueFinish.join
          (context.applyFree representativeClosure.substitution).initialSupply =
        valueFinish :=
    value_elaborates.letBodySupply_eq representativeClosure
      representativeClosure_absorbing valueStart_wellFormed
  have body : Elaborates
      ((context.applyFree representativeClosure.substitution).generalize
            representativeClosure.target ::
        context.applyFree representativeClosure.substitution)
      (.lit 0) valueFinish emptyBody valueFinish := .lit
  rw [← bodyStart] at body
  exact .letE value_elaborates representativeClosure
    representativeClosure_absorbing body

private noncomputable def directInterfaceEquations :
    InterfaceAliasDecomposition.EquationLists.EquationCommonCore
      (context.interfaceEquations inheritedClosure.substitution)
      (context.interfaceEquations representativeClosure.substitution) := by
  let base :=
    InterfaceAliasDecomposition.EquationLists.EquationCommonCore.tyAlias_refl
      representative inherited []
  refine
    { core := base.core
      leftAliases := base.leftAliases
      rightAliases := base.rightAliases
      leftEquivalent := base.leftEquivalent.trans ?_
      rightEquivalent := base.rightEquivalent }
  simpa [context, inheritedClosure_substitution,
    representativeClosure_substitution, finalInherited, firstInherited,
    finalRepresentative, firstRepresentative, Context.interfaceEquations,
    Context.freeTyVars, Context.freeCapVars, Scheme.freeTyVars,
    Scheme.freeCapVars, Scheme.mono, PolyTy.ofTy, PolyTy.freeTyVars,
    PolyTy.freeCapVars, dedupFirst, dedup, List.idxOf, List.findIdx,
    List.findIdx.go, Subst.compose, Subst.singleTy, Ty.apply,
    Equation.swapSides, inherited, representative] using
      HardEquivalent.cons_swap
        (.ty (.var representative) (.var inherited)) []

private noncomputable def directBlockDecomposition :
    GeneratedEquationCommonCore
      (Generated.fromLet
        (context.interfaceEquations inheritedClosure.substitution) emptyBody)
      (Generated.fromLet
        (context.interfaceEquations representativeClosure.substitution)
        emptyBody) := by
  let equations := directInterfaceEquations.appendSame emptyBody.hard
  exact
  { equations :=
      { core := equations.core
        leftAliases := equations.leftAliases
        rightAliases := equations.rightAliases
        leftEquivalent := by
          simpa [Generated.fromLet, equations] using equations.leftEquivalent
        rightEquivalent := by
          simpa [Generated.fromLet, equations] using equations.rightEquivalent }
    target_eq := rfl
    pending_eq := rfl }

private theorem directFramedCore_eq
    (frame : GeneratedFrame) :
    directBlockDecomposition.framedCore frame =
      frame.plug emptyBody := by
  rw [GeneratedEquationCommonCore.framedCore_eq_plug_coreBlock]
  congr 1

private theorem directHiddenFresh :
    VariablesFreshIn valueStart valueFinish [.ty representative] := by
  intro candidate member
  have equality : candidate = .ty representative := by simpa using member
  subst candidate
  simp [UnificationVar.FreshIn, valueStart, valueFinish, representative]

private theorem directFrameAdmissible :
    directBlockDecomposition.FrameAdmissible [.ty representative] := by
  intro frame frameAvoids
  have emptyAvoids : GeneratedAvoids [.ty representative] emptyBody := by
    intro candidate member _forbidden
    simp [emptyBody, Generated.unificationVars, Ty.unificationVars,
      TypePM.unificationVars, pendingUnificationVars] at member
  have coreAvoids : GeneratedAvoids [.ty representative]
      (directBlockDecomposition.framedCore frame) := by
    rw [directFramedCore_eq]
    exact GeneratedFrame.plug_avoids frameAvoids emptyAvoids
  have freshAbsent : .ty representative ∉
      (directBlockDecomposition.framedCore frame).unificationVars := by
    intro member
    exact coreAvoids (.ty representative) member (by simp)
  have different : (.ty representative : UnificationVar) ≠ .ty inherited := by
    decide
  have aliasAdmissible :
      (FreshAliasSequence.Alias.ty representative inherited).Admissible
        (directBlockDecomposition.framedCore frame) :=
    InterfaceAliasDecomposition.AliasFreshness.alias_admissible_of_not_mem
      (.ty representative inherited)
      (directBlockDecomposition.framedCore frame) different freshAbsent
  dsimp only
  rw [show (directBlockDecomposition.frame frame).equations.leftAliases =
      [.ty representative inherited] by
    simp [directBlockDecomposition, directInterfaceEquations,
      InterfaceAliasDecomposition.EquationLists.EquationCommonCore.tyAlias_refl,
      InterfaceAliasDecomposition.EquationLists.EquationCommonCore.appendSame]]
  rw [show (directBlockDecomposition.frame frame).equations.rightAliases =
      [] by
    simp [directBlockDecomposition, directInterfaceEquations,
      InterfaceAliasDecomposition.EquationLists.EquationCommonCore.tyAlias_refl,
      InterfaceAliasDecomposition.EquationLists.EquationCommonCore.appendSame]]
  exact ⟨⟨aliasAdmissible, trivial⟩, trivial⟩

/-- The source-derived obstruction to isolated renaming is positive at the
corrected endpoint: the two complete `Generated.fromLet` blocks have a
direct scoped comparison. -/
theorem actual_direct_scopedGeneratedComparison :
    ScopedGeneratedComparison valueStart valueFinish valueFinish
      (Generated.fromLet
        (context.interfaceEquations inheritedClosure.substitution) emptyBody)
      (Generated.fromLet
        (context.interfaceEquations representativeClosure.substitution)
        emptyBody) :=
  (DirectGeneratedComparisonCertificate.ofEquationCommonCore
    [.ty representative] directHiddenFresh directBlockDecomposition
    directFrameAdmissible).scopedGeneratedComparison

/-- Even for the two closures occurring in the source derivations above,
no `SourceSafeWholeLetAlignment` can exist.  The failure is already in
`FixesOutside`; frame admissibility is irrelevant to the contradiction. -/
theorem no_sourceSafeWholeLetAlignment
    (alignment : FreshClosureAlignment inheritedClosure
      representativeClosure context valueFinish)
    (body : Generated) :
    ¬ Nonempty
      (SourceSafeWholeLetAlignment (start := valueStart) alignment body) := by
  rintro ⟨safe⟩
  apply no_supported_target_alignment safe.hiddenFresh safe.fixesOutside
  simpa using alignment.alignment.target_exact

/-- Concrete open-context inner-let instance of the negative result: the
value derivation, both absorbing closures, and their fresh closure alignment
are the definitions above. -/
theorem actual_no_sourceSafeWholeLetAlignment :
    ¬ Nonempty (SourceSafeWholeLetAlignment (start := valueStart)
      freshClosureAlignment emptyBody) :=
  no_sourceSafeWholeLetAlignment freshClosureAlignment emptyBody

end TypePM.Source.SourceSafeAlignmentCounterexample
