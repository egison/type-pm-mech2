import TypePM.Source.ElaborationRenaming

/-!
# A root-level counterexample to whole-block renaming coherence

Even from the empty context, two absorbing representatives at a nested `let`
can expose respectively a genuine alias and a tautological interface equation.
A global bijective change of names preserves tautological equations, so it
cannot identify the resulting generated blocks.
-/

namespace TypePM.Source.GlobalRenamingCounterexample

open TypePM
open TypePM.Source

set_option linter.unusedSimpArgs false

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, eliminatedVariable?, unificationVars,
        Equation.unificationVars, Ty.unificationVars,
        Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, Ty.nodeCount, Ty.nodeCountList,
        Cap.nodeCount, Cap.nodeCountList,
        Ty.occursTy, Ty.occursTyList, Cap.occurs, Cap.occursList,
        Equation.apply, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
        Subst.singleTy, Subst.singleCap, Subst.compose, Subst.id])

private def p : TyVar := ⟨0⟩
private def a : TyVar := ⟨1⟩
private def d : TyVar := ⟨2⟩
private def r : TyVar := ⟨3⟩

/-- `λx. let y = ((λz. x) 0) in 0`. -/
def expression : Source.Expr :=
  .lam (.letE (.app (.lam (.var 1)) (.lit 0)) (.lit 0))

private def valueExpression : Source.Expr :=
  .app (.lam (.var 1)) (.lit 0)

private def valueGenerated : Generated :=
  { target := .var r
    hard := [.ty (.fn (.var a) (.var p)) (.fn (.var d) (.var r))]
    pending := [⟨.int, .var d⟩] }

private def firstRight : Subst :=
  Subst.compose (Subst.singleTy r (.var p))
    (Subst.singleTy a (.var d))

private def finalRight : Subst :=
  Subst.compose (Subst.singleTy d .int) firstRight

private def firstLeft : Subst :=
  Subst.compose (Subst.singleTy p (.var r))
    (Subst.singleTy a (.var d))

private def finalLeft : Subst :=
  Subst.compose (Subst.singleTy d .int) firstLeft

private def executableSubstitution : Subst :=
  Subst.compose Subst.id finalLeft

private def finalHard : List Equation :=
  valueGenerated.hard ++ [.ty .int (.var d)]

private def firstPromotion : Promotion :=
  { equations := [.ty .int (.var d)]
    pending := [] }

private theorem a_ne_d : a ≠ d := by decide
private theorem d_ne_a : d ≠ a := by decide
private theorem r_ne_p : r ≠ p := by decide
private theorem p_ne_r_private : p ≠ r := by decide

private def reduceFn :
    Reduces valueGenerated.hard Subst.id
      [.ty (.var a) (.var d), .ty (.var p) (.var r)] := by
  exact .tyFn

private def reduceA :
    Reduces [.ty (.var a) (.var d), .ty (.var p) (.var r)]
      (Subst.singleTy a (.var d)) [.ty (.var p) (.var r)] := by
  apply Reduces.tyVarLeft
  simp [a_ne_d, d_ne_a, Ty.occursTy]

private def reduceR :
    Reduces [.ty (.var p) (.var r)]
      (Subst.singleTy r (.var p)) [] := by
  apply Reduces.tyVarRight
  simp [r_ne_p, p_ne_r_private, Ty.occursTy]

private theorem firstRight_absorbing :
    AbsorbingPrincipal valueGenerated.hard firstRight := by
  constructor
  · constructor
    · simp [valueGenerated, firstRight, Equation.Holds,
        Subst.compose, Subst.singleTy, Subst.id, Ty.apply,
        p, a, d, r]
    · intro solution solved
      refine ⟨solution, ?_⟩
      have afterFn := reduceFn.complete solved
      have afterA := reduceA.complete afterFn
      have absorbedA := reduceA.absorbed afterFn
      have absorbedR := reduceR.absorbed afterA
      exact (show Subst.compose solution
            (Subst.compose (Subst.singleTy r (.var p))
              (Subst.singleTy a (.var d))) = solution from by
          rw [Subst.compose_assoc, absorbedR, absorbedA]).symm
  · intro solution solved
    have afterFn := reduceFn.complete solved
    have afterA := reduceA.complete afterFn
    have absorbedA := reduceA.absorbed afterFn
    have absorbedR := reduceR.absorbed afterA
    show Subst.compose solution firstRight = solution
    simp only [firstRight, Subst.compose_assoc]
    rw [absorbedR, absorbedA]

private def reduceFnFinal :
    Reduces finalHard Subst.id
      [.ty (.var a) (.var d), .ty (.var p) (.var r),
        .ty .int (.var d)] := by
  exact .tyFn

private def reduceAFinal :
    Reduces
      [.ty (.var a) (.var d), .ty (.var p) (.var r),
        .ty .int (.var d)]
      (Subst.singleTy a (.var d))
      [.ty (.var p) (.var r), .ty .int (.var d)] := by
  apply Reduces.tyVarLeft
  simp [a_ne_d, d_ne_a, Ty.occursTy]

private def reduceRFinal :
    Reduces [.ty (.var p) (.var r), .ty .int (.var d)]
      (Subst.singleTy r (.var p)) [.ty .int (.var d)] := by
  apply Reduces.tyVarRight
  simp [r_ne_p, p_ne_r_private, Ty.occursTy]

private def reduceDFinal :
    Reduces [.ty .int (.var d)] (Subst.singleTy d .int) [] := by
  apply Reduces.tyVarRight
  simp [Ty.occursTy]

private theorem finalRight_absorbing :
    AbsorbingPrincipal finalHard finalRight := by
  constructor
  · constructor
    · simp [finalHard, valueGenerated, finalRight, firstRight,
        Equation.Holds, Subst.compose, Subst.singleTy, Subst.id,
        Ty.apply, p, a, d, r]
    · intro solution solved
      refine ⟨solution, ?_⟩
      have afterFn := reduceFnFinal.complete solved
      have afterA := reduceAFinal.complete afterFn
      have afterR := reduceRFinal.complete afterA
      have absorbedA := reduceAFinal.absorbed afterFn
      have absorbedR := reduceRFinal.absorbed afterA
      have absorbedD := reduceDFinal.absorbed afterR
      apply Eq.symm
      show Subst.compose solution finalRight = solution
      simp only [finalRight, firstRight, Subst.compose_assoc]
      rw [absorbedD, absorbedR, absorbedA]
  · intro solution solved
    have afterFn := reduceFnFinal.complete solved
    have afterA := reduceAFinal.complete afterFn
    have afterR := reduceRFinal.complete afterA
    have absorbedA := reduceAFinal.absorbed afterFn
    have absorbedR := reduceRFinal.absorbed afterA
    have absorbedD := reduceDFinal.absorbed afterR
    show Subst.compose solution finalRight = solution
    simp only [finalRight, firstRight, Subst.compose_assoc]
    rw [absorbedD, absorbedR, absorbedA]

private theorem promotion_exact :
    promoteUnder firstRight valueGenerated.pending = firstPromotion := by
  simp [valueGenerated, firstRight, firstPromotion, promoteUnder,
    Subst.compose, Subst.singleTy, Ty.apply, Ty.couldSpecial,
    Ty.mayBecomeMatcher, Ty.mayBecomeMatcherItems,
    Ty.mayBecomeMatcherProduct, Ty.mayBecomeExpectedMatcher,
    Ty.mayBecomeExpectedSlot, a, d, p, r]

private def alternativeClosure : PrincipalBlockClosure valueGenerated :=
  { finalHard := finalHard
    finalPending := []
    hardSubstitution := finalRight
    residualSubstitution := Subst.id
    saturation :=
      { closure := .step firstRight_absorbing.mostGeneral promotion_exact
          (by simp [firstPromotion]) .refl
        principal := finalRight_absorbing.mostGeneral
        stable := by simp [promoteUnder] }
    residualPrincipal := by
      constructor
      · exact solves_nil _
      · intro solution _
        exact ⟨solution, by simp⟩ }

private theorem id_absorbing : AbsorbingPrincipal [] Subst.id := by
  constructor
  · constructor
    · exact solves_nil _
    · intro solution _
      exact ⟨solution, by simp⟩
  · intro solution _
    simp

private theorem alternativeClosure_absorbing :
    alternativeClosure.Absorbing := by
  constructor
  · exact finalRight_absorbing
  · simpa [alternativeClosure, residualEquations] using id_absorbing

@[simp] private theorem alternativeClosure_substitution :
    alternativeClosure.substitution = finalRight := by
  simp [PrincipalBlockClosure.substitution, alternativeClosure]

@[simp] private theorem alternativeClosure_target :
    alternativeClosure.target = .var p := by
  rw [PrincipalBlockClosure.target, alternativeClosure_substitution]
  simp [
    valueGenerated, finalRight, firstRight, Subst.compose,
    Subst.singleTy, Ty.apply, p, a, d, r]

private theorem value_elaborates :
    Elaborates [.mono (.var p)] valueExpression ⟨1, 0⟩
      valueGenerated ⟨4, 0⟩ := by
  have varDerivation :=
    Elaborates.var (supply := Supply.mk 2 0)
      (context := [.mono (.var a), .mono (.var p)])
      (index := 1) (by rfl)
  have function := Elaborates.lam
    (context := [.mono (.var p)]) (supply := Supply.mk 1 0)
    varDerivation
  have argument : Elaborates [.mono (.var p)] (.lit 0) ⟨2, 0⟩
      ⟨.int, [], []⟩ ⟨2, 0⟩ := .lit
  simpa [valueExpression, valueGenerated, Scheme.instantiate_mono,
    Supply.nextTy,
    p, a, d, r] using Elaborates.app function argument

def executableGenerated : Generated :=
  { target := .fn (.var p) .int
    hard := [.ty (.var p) (.var r)]
    pending := [] }

def alternativeGenerated : Generated :=
  { target := .fn (.var p) .int
    hard := [.ty (.var p) (.var p)]
    pending := [] }

theorem p_ne_r : p ≠ r := by decide

private theorem elaborate_value_exact :
    elaborate [.mono (.var p)] valueExpression ⟨1, 0⟩ =
      some (valueGenerated, ⟨4, 0⟩) := by
  rfl

private theorem close_value_exact :
    inferGeneratedUsing unify valueGenerated =
      some ⟨executableSubstitution, .var r⟩ := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [valueGenerated]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, firstLeft, finalLeft, executableSubstitution, p, a, d, r]
  simp only [saturateLoop]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, firstLeft, finalLeft, executableSubstitution, p, a, d, r]
  simp only [residualEquations]
  compute_unification

/-- Exact deterministic result for the public empty-root elaboration. -/
theorem executable_exact :
    elaborate [] expression (Context.initialSupply []) =
      some (executableGenerated, ⟨4, 0⟩) := by
  rw [show Context.initialSupply ([] : Context) = ⟨0, 0⟩ by rfl]
  rw [show expression = .lam (.letE valueExpression (.lit 0)) by rfl]
  rw [elaborate]
  simp only [Supply.nextTy, Nat.zero_add, p]
  rw [elaborate]
  have valueExact :
      elaborate [.mono (.var ⟨0⟩)] valueExpression ⟨1, 0⟩ =
        some (valueGenerated, ⟨4, 0⟩) := by
    simpa [p] using elaborate_value_exact
  rw [valueExact]
  simp [close_value_exact, elaborate, executableGenerated,
    executableSubstitution, Context.initialSupply,
    Context.applyFree, Context.generalize, Context.generalizedTyVars,
    Context.generalizedCapVars, Context.freeTyVars, Context.freeCapVars,
    Context.interfaceEquations, Scheme.mono, Scheme.applyFree,
    Scheme.freeTyVars, Scheme.freeCapVars, PolyTy.ofTy, PolyTy.close,
    PolyTy.openBound, PolyTy.applyFree, PolyTy.freeTyVars,
    PolyTy.freeCapVars, Supply.join, Generated.fromLet,
    finalLeft, firstLeft, Subst.compose, Subst.singleTy, Subst.id,
    Ty.apply, Ty.tyVars, Ty.capVars, TyVar.next, CapVar.next,
    dedupFirst, dedup, List.idxOf, List.findIdx, List.findIdx.go,
    p, a, d, r]

/-- The deterministic result is also the first relational witness. -/
theorem executable_elaborates :
    Elaborates [] expression (Context.initialSupply [])
      executableGenerated ⟨4, 0⟩ :=
  elaborate_sound executable_exact

/-- The tautological-interface representative is a valid relational
elaboration from the public empty-context supply. -/
theorem alternative_elaborates :
    Elaborates [] expression (Context.initialSupply [])
      alternativeGenerated ⟨4, 0⟩ := by
  have body : Elaborates
      ((Context.applyFree alternativeClosure.substitution
          [.mono (.var p)]).generalize
            alternativeClosure.target ::
        Context.applyFree alternativeClosure.substitution
          [.mono (.var p)])
      (.lit 0)
      (Supply.join ⟨4, 0⟩
        (Context.applyFree alternativeClosure.substitution
          [.mono (.var p)]).initialSupply)
      ⟨.int, [], []⟩
      (Supply.join ⟨4, 0⟩
        (Context.applyFree alternativeClosure.substitution
          [.mono (.var p)]).initialSupply) := .lit
  have letDerivation := Elaborates.letE value_elaborates
    alternativeClosure alternativeClosure_absorbing body
  simpa [expression, valueExpression, alternativeGenerated,
    Context.initialSupply,
    Context.interfaceEquations, Context.freeTyVars, Context.freeCapVars,
    Context.applyFree, Scheme.applyFree, Scheme.mono, Scheme.freeTyVars,
    Scheme.freeCapVars, PolyTy.ofTy, PolyTy.applyFree,
    PolyTy.freeTyVars, PolyTy.freeCapVars, Generated.fromLet,
    alternativeClosure_substitution, finalRight, firstRight,
    Subst.compose, Subst.singleTy, Ty.apply, Supply.nextTy, Supply.join,
    TyVar.next, CapVar.next, dedupFirst, dedup, List.idxOf,
    List.findIdx, List.findIdx.go, p, a, d, r] using
      Elaborates.lam (context := []) (supply := Supply.mk 0 0)
        letDerivation

/-- No uniform global renaming maps the tautological alternative interface
to the executable block's genuine alias. -/
theorem no_global_renaming (rho : VariableRenaming) :
    ElaborationRenaming.renameGenerated rho alternativeGenerated ≠
      executableGenerated := by
  intro equality
  have hardEquality := congrArg Generated.hard equality
  simp [ElaborationRenaming.renameGenerated,
    ElaborationRenaming.renameEquation, Equation.apply,
    VariableRenaming.substitution, alternativeGenerated,
    executableGenerated, Ty.apply] at hardEquality
  exact p_ne_r (hardEquality.1.symm.trans hardEquality.2)

end TypePM.Source.GlobalRenamingCounterexample
