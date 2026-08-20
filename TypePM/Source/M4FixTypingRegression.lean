import TypePM.Source.M4FixTyping

/-!
# Exact regressions for M4 singleton direct-self recursion

The positive fixtures pin the unary context convention and the exact public
inference result.  The negative fixtures distinguish the language boundary
(bare, aliased, higher-order, and nested mutual-style self use) from the
remaining implementation boundary (a syntactically direct matcher-root fix
whose matcher literal is not typed by this module).
-/

namespace TypePM.Source.M4FixTypingRegression

open DirectSelf

set_option linter.unusedSimpArgs false

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, tyEquations, capEquations, eliminatedVariable?,
        unificationVars, Equation.unificationVars, Ty.unificationVars,
        Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, Ty.nodeCount, Ty.nodeCountList,
        Cap.nodeCount, Cap.nodeCountList,
        Ty.occursTy, Ty.occursTyList, Cap.occurs, Cap.occursList,
        Equation.apply, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
        Subst.singleTy, Subst.singleCap, Subst.compose, Subst.id])

def directBody : Expr :=
  .app (.var 1) (.var 0)

def concreteIntBody : Expr :=
  .prim .add
    [ .app (.var 1) (.prim .add [.var 0, .lit (-1)]),
      .lit 1 ]

def bareBody : Expr :=
  .var 1

def aliasBody : Expr :=
  .letE (.var 1) (.app (.var 0) (.var 1))

def higherOrderBody : Expr :=
  .app (.var 0) (.var 1)

/-- The inner fix attempts to capture the outer self, which would create a
second recursive origin. -/
def mutualStyleBody : Expr :=
  .fixE (.app (.var 3) (.var 0))

def shiftedLambdaBody : Expr :=
  .lam (.app (.var 2) (.var 0))

def shiftedLetBody : Expr :=
  .letE (.lit 0) (.app (.var 2) (.var 1))

def shiftedPattern : Pattern :=
  .tuple [.var, .value (.app (.var 2) (.var 1))]

def shiftedConjunctionPattern : Pattern :=
  .and .var (.value (.app (.var 2) (.var 1)))

def shiftedPatternBody : Expr :=
  .matchAll (.var 0) .something shiftedPattern
    (.app (.var 2) (.var 1))

def shiftedConjunctionBody : Expr :=
  .matchAll (.var 0) .something shiftedConjunctionPattern
    (.app (.var 2) (.var 1))

def shiftedClause : MatcherClause :=
  .mk .capture
    (.app (.var 2) (.var 1))
    [.mk .var (.app (.var 3) (.var 2))]

def shiftedClauseBody : Expr :=
  .matcher [shiftedClause]

/-- Argument is index zero, self is index one, and the outer context follows. -/
theorem unary_body_context_exact
    (domain codomain : Ty) (context : Context) :
    Fix.bodyContext domain codomain context =
      Scheme.mono domain :: Scheme.mono (.fn domain codomain) :: context := by
  rfl

theorem matcher_root_fix_shape_exact :
    Fix.domain (.matcher []) ⟨3, 4⟩ =
        .slot (.var ⟨4⟩) (.var ⟨3⟩) ∧
      Fix.codomain (.matcher []) ⟨3, 4⟩ =
        .matcher (.var ⟨5⟩) (.var ⟨4⟩) ∧
      Fix.bodySupply (.matcher []) ⟨3, 4⟩ = ⟨5, 6⟩ := by
  exact ⟨rfl, rfl, rfl⟩

theorem direct_body_checked_exact :
    check 1 directBody = true := by
  simp [directBody, check, checkFuel, checkHead, checkHeadFuel]

theorem direct_body_declarative : Holds directBody :=
  (holds_iff_check directBody).2 direct_body_checked_exact

theorem lambda_shift_checked_exact :
    check 1 shiftedLambdaBody = true := by
  simp [shiftedLambdaBody, check, checkFuel, checkHead, checkHeadFuel]

theorem let_shift_checked_exact :
    check 1 shiftedLetBody = true := by
  simp [shiftedLetBody, check, checkFuel, checkHead, checkHeadFuel]

/-- The value expression after one pattern variable sees self at index two,
and the match body receives the same one-binder shift. -/
theorem pattern_shifts_checked_exact :
    check 1 shiftedPatternBody = true := by
  simp [shiftedPatternBody, shiftedPattern, check, checkFuel, checkHead,
    checkHeadFuel, checkPattern, checkPatternFuel, checkPatterns,
    checkPatternsFuel, patternBindingCount, patternBindingCountList]

/-- A conjunction adds the binders of its left side before checking its right
side, and its body sees the total number of binders from both sides. -/
theorem conjunction_shifts_checked_exact :
    check 1 shiftedConjunctionBody = true := by
  simp [shiftedConjunctionBody, shiftedConjunctionPattern, check, checkFuel,
    checkHead, checkHeadFuel, checkPattern, checkPatternFuel,
    patternBindingCount]

/-- A next-matcher expression has capture at index zero, fix argument at one,
and recursive self at two.  An arm body additionally has its data variable at
index zero, shifting capture, argument, and self to one, two, and three. -/
theorem clause_shifts_checked_exact :
    check 1 shiftedClauseBody = true := by
  simp [shiftedClauseBody, shiftedClause, check, checkFuel, checkHead,
    checkHeadFuel, checkClauses, checkClausesFuel, checkClause,
    checkClauseFuel, checkArms, checkArmsFuel, checkArm, checkArmFuel,
    PPat.captureCount, DPat.bindingCount]

theorem bare_self_checked_exact :
    check 1 bareBody = false := by
  simp [bareBody, check, checkFuel]

theorem alias_checked_exact :
    check 1 aliasBody = false := by
  simp [aliasBody, check, checkFuel, checkHead, checkHeadFuel]

theorem higher_order_checked_exact :
    check 1 higherOrderBody = false := by
  simp [higherOrderBody, check, checkFuel, checkHead, checkHeadFuel]

theorem mutual_style_checked_exact :
    check 1 mutualStyleBody = false := by
  simp [mutualStyleBody, check, checkFuel, mentions, checkHead,
    checkHeadFuel]

def directGenerated : Generated :=
  { target := .fn (.var ⟨0⟩) (.var ⟨1⟩)
    hard :=
      [ .ty (.fn (.var ⟨0⟩) (.var ⟨1⟩))
          (.fn (.var ⟨2⟩) (.var ⟨3⟩)),
        .ty (.var ⟨3⟩) (.var ⟨1⟩) ]
    pending := [⟨.var ⟨0⟩, .var ⟨2⟩⟩] }

theorem elaborate_direct_exact :
    elaborateFix Paper1Signature.signature [] directBody ⟨0, 0⟩ =
      some (directGenerated, ⟨4, 0⟩) := by
  simp [elaborateFix, directBody, directGenerated, DirectSelf.check,
    DirectSelf.checkFuel, elaborateFixUsing, DirectSelf.checkHead,
    DirectSelf.checkHeadFuel, Fix.bodyContext, elaborate, Generated.fromFix,
    Fix.domain, Fix.codomain, Fix.bodySupply, Scheme.mono,
    Scheme.instantiate, Supply.nextTy]

theorem close_direct_exact :
    (inferGeneratedUsing unify directGenerated).bind
      (fun result => some result.target) =
      some (.fn (.var ⟨2⟩) (.var ⟨3⟩)) := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [directGenerated]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  have resolutionTrace :
      resolve (.var ⟨2⟩) (.var ⟨2⟩) =
        .ordinary (.var ⟨2⟩) (.var ⟨2⟩) := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id]
  rw [resolutionTrace]
  simp [Resolution.equations]
  compute_unification

theorem infer_direct_exact :
    inferFix Paper1Signature.signature [] directBody =
      some (.fn (.var ⟨2⟩) (.var ⟨3⟩)) := by
  unfold inferFix inferFixUsing
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    elaborate_direct_exact]
  exact close_direct_exact

theorem direct_relational :
    FixElaborates Paper1Signature.signature [] (.fixE directBody) ⟨0, 0⟩
      directGenerated ⟨4, 0⟩ :=
  elaborateFix_sound Paper1Signature.wellFormed elaborate_direct_exact

theorem direct_fixTyping :
    FixTyping Paper1Signature.signature [] directBody
      (.fn (.var ⟨2⟩) (.var ⟨3⟩)) :=
  FixInference.inferFix_success_fixTyping Paper1Signature.wellFormed
    infer_direct_exact

theorem infer_bare_none :
    inferFix Paper1Signature.signature [] bareBody = none := by
  simp [inferFix, inferFixUsing, elaborateFix, elaborateFixUsing,
    bare_self_checked_exact]

theorem infer_alias_none :
    inferFix Paper1Signature.signature [] aliasBody = none := by
  simp [inferFix, inferFixUsing, elaborateFix, elaborateFixUsing,
    alias_checked_exact]

theorem infer_higher_order_none :
    inferFix Paper1Signature.signature [] higherOrderBody = none := by
  simp [inferFix, inferFixUsing, elaborateFix, elaborateFixUsing,
    higher_order_checked_exact]

theorem infer_mutual_style_none :
    inferFix Paper1Signature.signature [] mutualStyleBody = none := by
  simp [inferFix, inferFixUsing, elaborateFix, elaborateFixUsing,
    mutual_style_checked_exact]

theorem bare_not_fixTyping (target : Ty) :
    ¬ FixTyping Paper1Signature.signature [] bareBody target :=
  not_fixTyping_of_not_direct
    (by intro direct; simpa [bare_self_checked_exact] using
      (DirectSelf.holds_iff_check bareBody).1 direct) target

theorem alias_not_fixTyping (target : Ty) :
    ¬ FixTyping Paper1Signature.signature [] aliasBody target :=
  not_fixTyping_of_not_direct
    (by intro direct; simpa [alias_checked_exact] using
      (DirectSelf.holds_iff_check aliasBody).1 direct) target

theorem higher_order_not_fixTyping (target : Ty) :
    ¬ FixTyping Paper1Signature.signature [] higherOrderBody target :=
  not_fixTyping_of_not_direct
    (by intro direct; simpa [higher_order_checked_exact] using
      (DirectSelf.holds_iff_check higherOrderBody).1 direct) target

theorem mutual_style_not_fixTyping (target : Ty) :
    ¬ FixTyping Paper1Signature.signature [] mutualStyleBody target :=
  not_fixTyping_of_not_direct
    (by intro direct; simpa [mutual_style_checked_exact] using
      (DirectSelf.holds_iff_check mutualStyleBody).1 direct) target

/-- The direct-self classifier already handles the complete matcher syntax,
but the M3 body elaborator has no matcher-literal rule.  This is the exact
remaining matcher-root recursion gap, not a claim about multiset typing. -/
theorem matcher_root_direct_but_unelaborated :
    check 1 shiftedClauseBody = true ∧
      elaborateFix Paper1Signature.signature [] shiftedClauseBody ⟨0, 0⟩ =
        none := by
  constructor
  · exact clause_shifts_checked_exact
  · simp [elaborateFix, elaborateFixUsing, clause_shifts_checked_exact,
      shiftedClauseBody, elaborate]

end TypePM.Source.M4FixTypingRegression
