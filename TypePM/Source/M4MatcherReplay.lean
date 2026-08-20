import TypePM.Source.M4StructuralReplay

/-!
# Executable replay for M4 matcher literals

Primitive-pattern and data-pattern headers are structurally deterministic.
The first part of this module proves that every relational header derivation
is returned exactly by its executable elaborator.  The remaining matcher
components then replay expression callbacks while using child coherence to
align source-ordered supplies.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source
open MatcherTyping

mutual

private theorem ppatFuel_executable
    {signature : FrozenSignature} {fuel : Nat} {pattern : PPat}
    {expectedTarget : Ty} {expectedCapability : Option Cap}
    {supply next : Supply} {generated : GeneratedPPat}
    (enoughFuel : PPat.typingSize pattern < fuel)
    (derivation : PPatElaborates signature pattern expectedTarget
      expectedCapability supply generated next) :
    elaboratePPatFuel signature fuel pattern expectedTarget expectedCapability
      supply = some (generated, next) := by
  cases fuel with
  | zero => simp at enoughFuel
  | succ fuel =>
      cases derivation with
      | hole => simp [elaboratePPatFuel]
      | wild => simp [elaboratePPatFuel]
      | capture => simp [elaboratePPatFuel]
      | @ctor constructor fields expectedTarget expectedCapability supply scheme
          generatedFields next lookup arity fieldsDerivation =>
          have fieldsExecutable := ppatsFuel_executable (fuel := fuel)
            (by
              simp only [PPat.typingSize] at enoughFuel
              omega) fieldsDerivation
          simp [elaboratePPatFuel, lookup, arity, fieldsExecutable]
termination_by PPat.typingSize pattern * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [PPat.typingSize]
  all_goals omega

private theorem ppatsFuel_executable
    {signature : FrozenSignature} {fuel : Nat} {patterns : List PPat}
    {expected : List Dual} {supply next : Supply}
    {generated : GeneratedPPats}
    (enoughFuel : PPat.listTypingSize patterns < fuel)
    (derivation : PPatsElaborate signature patterns expected supply generated
      next) :
    elaboratePPatFieldsFuel signature fuel patterns expected supply =
      some (generated, next) := by
  cases fuel with
  | zero => simp at enoughFuel
  | succ fuel =>
      cases derivation with
      | nil => simp [elaboratePPatFieldsFuel]
      | @cons pattern patterns expected expecteds supply generatedPattern
          afterPattern generatedPatterns next head tail =>
          have headExecutable := ppatFuel_executable (fuel := fuel)
            (by
              simp only [PPat.listTypingSize] at enoughFuel
              omega) head
          have tailExecutable := ppatsFuel_executable (fuel := fuel)
            (by
              simp only [PPat.listTypingSize] at enoughFuel
              omega) tail
          simp [elaboratePPatFieldsFuel, headExecutable, tailExecutable]
termination_by PPat.listTypingSize patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [PPat.listTypingSize]
  all_goals omega

end

/-- Every relational primitive-pattern derivation is replayed exactly. -/
theorem PPatElaborates.executable
    {signature : FrozenSignature} {pattern : PPat} {expectedTarget : Ty}
    {expectedCapability : Option Cap} {supply next : Supply}
    {generated : GeneratedPPat}
    (derivation : PPatElaborates signature pattern expectedTarget
      expectedCapability supply generated next) :
    elaboratePPat signature pattern expectedTarget expectedCapability supply =
      some (generated, next) := by
  apply ppatFuel_executable (derivation := derivation)
  omega

/-- Every relational primitive-pattern field derivation is replayed exactly. -/
theorem PPatsElaborate.executable
    {signature : FrozenSignature} {patterns : List PPat}
    {expected : List Dual} {supply next : Supply}
    {generated : GeneratedPPats}
    (derivation : PPatsElaborate signature patterns expected supply generated
      next) :
    elaboratePPatFields signature patterns expected supply =
      some (generated, next) := by
  apply ppatsFuel_executable (derivation := derivation)
  omega

mutual

private theorem dpatFuel_executable
    {signature : FrozenSignature} {fuel : Nat} {pattern : DPat}
    {expected : Ty} {supply next : Supply} {generated : GeneratedDPat}
    (enoughFuel : DPat.typingSize pattern < fuel)
    (derivation : DPatElaborates signature pattern expected supply generated
      next) :
    elaborateDPatFuel signature fuel pattern expected supply =
      some (generated, next) := by
  cases fuel with
  | zero => simp at enoughFuel
  | succ fuel =>
      cases derivation with
      | var => simp [elaborateDPatFuel]
      | wild => simp [elaborateDPatFuel]
      | @ctor constructor fields expected supply scheme fieldTypes resultType
          generatedFields next lookup arity peel fieldsDerivation =>
          have fieldsExecutable := dpatsFuel_executable (fuel := fuel)
            (by
              simp only [DPat.typingSize] at enoughFuel
              omega) fieldsDerivation
          have peel' :
              peelFunctionExact scheme.callArity
                  (scheme.instantiate supply).1 =
                some (fieldTypes, resultType) := by
            simpa [arity] using peel
          simp [elaborateDPatFuel, lookup, arity, peel', fieldsExecutable]
      | @tuple items expected supply fields generatedItems next fieldsEquality
          itemsDerivation =>
          subst fields
          have itemsExecutable := dpatsFuel_executable (fuel := fuel)
            (by
              simp only [DPat.typingSize] at enoughFuel
              omega) itemsDerivation
          simp [elaborateDPatFuel, itemsExecutable]
termination_by DPat.typingSize pattern * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [DPat.typingSize]
  all_goals omega

private theorem dpatsFuel_executable
    {signature : FrozenSignature} {fuel : Nat} {patterns : List DPat}
    {expected : List Ty} {supply next : Supply}
    {generated : GeneratedDPats}
    (enoughFuel : DPat.listTypingSize patterns < fuel)
    (derivation : DPatsElaborate signature patterns expected supply generated
      next) :
    elaborateDPatFieldsFuel signature fuel patterns expected supply =
      some (generated, next) := by
  cases fuel with
  | zero => simp at enoughFuel
  | succ fuel =>
      cases derivation with
      | nil => simp [elaborateDPatFieldsFuel]
      | @cons pattern patterns expected expecteds supply generatedPattern
          afterPattern generatedPatterns next head tail =>
          have headExecutable := dpatFuel_executable (fuel := fuel)
            (by
              simp only [DPat.listTypingSize] at enoughFuel
              omega) head
          have tailExecutable := dpatsFuel_executable (fuel := fuel)
            (by
              simp only [DPat.listTypingSize] at enoughFuel
              omega) tail
          simp [elaborateDPatFieldsFuel, headExecutable, tailExecutable]
termination_by DPat.listTypingSize patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [DPat.listTypingSize]
  all_goals omega

end

/-- Every relational data-pattern derivation is replayed exactly. -/
theorem DPatElaborates.executable
    {signature : FrozenSignature} {pattern : DPat} {expected : Ty}
    {supply next : Supply} {generated : GeneratedDPat}
    (derivation : DPatElaborates signature pattern expected supply generated
      next) :
    elaborateDPat signature pattern expected supply = some (generated, next) := by
  apply dpatFuel_executable (derivation := derivation)
  omega

/-- Every relational data-pattern field derivation is replayed exactly. -/
theorem DPatsElaborate.executable
    {signature : FrozenSignature} {patterns : List DPat}
    {expected : List Ty} {supply next : Supply}
    {generated : GeneratedDPats}
    (derivation : DPatsElaborate signature patterns expected supply generated
      next) :
    elaborateDPatFields signature patterns expected supply =
      some (generated, next) := by
  apply dpatsFuel_executable (derivation := derivation)
  omega

/-! ## Replay of callback-parametric matcher components -/

private theorem checkedExpressionFuel_replay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {expected : Ty} {supply next : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (bound : expression.complexity < limit)
    (derivation : CheckedExpressionElaboratesUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) context expression
      expected supply generated next) :
    ∃ computed,
      elaborateCheckedExpressionUsing (M4.elaborateFuel signature fuel) context
          expression expected supply = some (computed, next) ∧
        CheckedExpressionElaboratesUsing (ElaboratesFuel signature fuel) context
          expression expected supply computed next := by
  cases derivation with
  | mk child =>
      obtain ⟨computed, computedNext, executable, computedDerivation⟩ :=
        replay expression bound child.2 signatureWellFormed child.1
      obtain ⟨comparison⟩ := coherent expression bound signatureWellFormed
        child.1 child.2 computedDerivation
      cases comparison.next_eq
      exact ⟨_, by
        simp [elaborateCheckedExpressionUsing, executable],
        .mk computedDerivation⟩

private theorem nextMatcherItemsFuel_replay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {items : List Expr} {holes : List Dual} {supply next : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (bound : Expr.listComplexity items < limit)
    (derivation : NextMatcherItemsElaborateUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) context items holes
      supply generated next) :
    ∃ computed,
      elaborateNextMatcherItemsUsing (M4.elaborateFuel signature fuel) context
          items holes supply = some (computed, next) ∧
        NextMatcherItemsElaborateUsing (ElaboratesFuel signature fuel) context
          items holes supply computed next := by
  induction derivation with
  | nil => exact ⟨_, by simp [elaborateNextMatcherItemsUsing], .nil⟩
  | @cons item items hole holes supply generatedItem afterItem generatedItems
      next head tail induction =>
      obtain ⟨computedItem, itemExecutable, computedHead⟩ :=
        checkedExpressionFuel_replay coherent replay signatureWellFormed (by
          simp only [Expr.listComplexity_cons] at bound
          omega) head
      obtain ⟨computedItems, itemsExecutable, computedTail⟩ := induction (by
        simp only [Expr.listComplexity_cons] at bound
        omega)
      exact ⟨_, by
        simp [elaborateNextMatcherItemsUsing, itemExecutable, itemsExecutable],
        .cons computedHead computedTail⟩

private theorem nextMatchersFuel_replay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {holes : List Dual} {supply next : Supply}
    {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (bound : expression.complexity < limit)
    (derivation : NextMatchersElaborateUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) context expression
      holes supply generated next) :
    ∃ computed,
      elaborateNextMatchersUsing (M4.elaborateFuel signature fuel) context
          expression holes supply = some (computed, next) ∧
        NextMatchersElaborateUsing (ElaboratesFuel signature fuel) context
          expression holes supply computed next := by
  cases derivation with
  | zero checked =>
      obtain ⟨computed, executable, computedDerivation⟩ :=
        checkedExpressionFuel_replay coherent replay signatureWellFormed bound
          checked
      exact ⟨_, by simp [elaborateNextMatchersUsing, executable],
        .zero computedDerivation⟩
  | one checked =>
      obtain ⟨computed, executable, computedDerivation⟩ :=
        checkedExpressionFuel_replay coherent replay signatureWellFormed bound
          checked
      exact ⟨_, by simp [elaborateNextMatchersUsing, executable],
        .one computedDerivation⟩
  | many components =>
      obtain ⟨computed, executable, computedDerivation⟩ :=
        nextMatcherItemsFuel_replay coherent replay signatureWellFormed (by
          simp only [Expr.complexity_tuple] at bound
          omega) components
      exact ⟨_, by simp [elaborateNextMatchersUsing, executable],
        .many computedDerivation⟩

private theorem matcherArmFuel_replay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {captures : List Ty} {matcherTarget : Ty} {holes : List Dual}
    {arm : MatcherArm} {supply next : Supply} {generated : GeneratedChecks}
    (signatureWellFormed : signature.WellFormed)
    (bound : arm.complexity < limit)
    (derivation : MatcherArmElaboratesUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) DPatElaborates
      signature context captures matcherTarget holes arm supply generated next) :
    ∃ computed,
      elaborateMatcherArmUsing (M4.elaborateFuel signature fuel) signature
          context captures matcherTarget holes arm supply = some (computed, next) ∧
        MatcherArmElaboratesUsing (ElaboratesFuel signature fuel) DPatElaborates
          signature context captures matcherTarget holes arm supply computed next := by
  cases derivation with
  | @mk header body supply generatedHeader afterHeader generatedBody next
      headerDerivation bodyDerivation =>
      have headerExecutable :=
        TypePM.Source.M4.CompletenessArchitecture.DPatElaborates.executable
          headerDerivation
      obtain ⟨computedBody, bodyExecutable, computedBodyDerivation⟩ :=
        checkedExpressionFuel_replay coherent replay signatureWellFormed (by
          simp only [MatcherArm.complexity_mk] at bound
          omega) bodyDerivation
      exact ⟨_, by
        simp [elaborateMatcherArmUsing, headerExecutable, bodyExecutable],
        .mk headerDerivation computedBodyDerivation⟩

private theorem matcherArmsFuel_replay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {captures : List Ty} {matcherTarget : Ty} {holes : List Dual}
    {arms : List MatcherArm} {supply next : Supply}
    {generated : GeneratedArms}
    (signatureWellFormed : signature.WellFormed)
    (bound : MatcherArm.listComplexity arms < limit)
    (derivation : MatcherArmsElaborateUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) DPatElaborates
      signature context captures matcherTarget holes arms supply generated next) :
    ∃ computed,
      elaborateMatcherArmsUsing (M4.elaborateFuel signature fuel) signature
          context captures matcherTarget holes arms supply = some (computed, next) ∧
        MatcherArmsElaborateUsing (ElaboratesFuel signature fuel) DPatElaborates
          signature context captures matcherTarget holes arms supply computed next := by
  induction derivation with
  | nil => exact ⟨_, by simp [elaborateMatcherArmsUsing], .nil⟩
  | @cons arm arms supply generatedArm afterArm generatedArms next head tail
      induction =>
      obtain ⟨computedArm, armExecutable, computedHead⟩ :=
        matcherArmFuel_replay coherent replay signatureWellFormed (by
          simp only [MatcherArm.listComplexity_cons] at bound
          omega) head
      obtain ⟨computedArms, armsExecutable, computedTail⟩ := induction (by
        simp only [MatcherArm.listComplexity_cons] at bound
        omega)
      exact ⟨_, by
        simp [elaborateMatcherArmsUsing, armExecutable, armsExecutable],
        .cons computedHead computedTail⟩

private theorem matcherClauseFuel_replay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {matcherTarget : Ty} {clause : MatcherClause} {supply next : Supply}
    {generated : GeneratedMatcherClause}
    (signatureWellFormed : signature.WellFormed)
    (bound : clause.complexity < limit)
    (derivation : MatcherClauseElaboratesUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) PPatElaborates
      DPatElaborates signature context matcherTarget clause supply generated next) :
    ∃ computed,
      elaborateMatcherClauseUsing (M4.elaborateFuel signature fuel) signature
          context matcherTarget clause supply = some (computed, next) ∧
        MatcherClauseElaboratesUsing (ElaboratesFuel signature fuel)
          PPatElaborates DPatElaborates signature context matcherTarget clause
          supply computed next := by
  cases derivation with
  | @mk header nextMatchers arms supply generatedHeader afterHeader generatedNext
      afterNext generatedArms next shape headerDerivation nextDerivation
      armsDerivation =>
      have shapeCheck : (MatcherClause.mk header nextMatchers arms).toShape.check
          signature = true := shape.check_eq_true
      have headerExecutable :=
        TypePM.Source.M4.CompletenessArchitecture.PPatElaborates.executable
          headerDerivation
      obtain ⟨computedNext, nextExecutable, computedNextDerivation⟩ :=
        nextMatchersFuel_replay coherent replay signatureWellFormed (by
          simp only [MatcherClause.complexity_mk] at bound
          omega) nextDerivation
      obtain ⟨computedArms, armsExecutable, computedArmsDerivation⟩ :=
        matcherArmsFuel_replay coherent replay signatureWellFormed (by
          simp only [MatcherClause.complexity_mk] at bound
          omega) armsDerivation
      exact ⟨_, by
        simp [elaborateMatcherClauseUsing, MatcherClause.header,
          MatcherClause.nextMatchers, MatcherClause.arms, shapeCheck,
          headerExecutable, nextExecutable, armsExecutable],
        .mk shape headerDerivation computedNextDerivation
          computedArmsDerivation⟩

private theorem matcherClausesFuel_replay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {matcherTarget : Ty} {clauses : List MatcherClause} {supply next : Supply}
    {generated : GeneratedMatcherClauses}
    (signatureWellFormed : signature.WellFormed)
    (bound : MatcherClause.listComplexity clauses < limit)
    (derivation : MatcherClausesElaborateUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) PPatElaborates
      DPatElaborates signature context matcherTarget clauses supply generated next) :
    ∃ computed,
      elaborateMatcherClausesUsing (M4.elaborateFuel signature fuel) signature
          context matcherTarget clauses supply = some (computed, next) ∧
        MatcherClausesElaborateUsing (ElaboratesFuel signature fuel)
          PPatElaborates DPatElaborates signature context matcherTarget clauses
          supply computed next := by
  induction derivation with
  | nil => exact ⟨_, by simp [elaborateMatcherClausesUsing], .nil⟩
  | @cons clause clauses supply generatedClause afterClause generatedClauses
      next head tail induction =>
      obtain ⟨computedClause, clauseExecutable, computedHead⟩ :=
        matcherClauseFuel_replay coherent replay signatureWellFormed (by
          simp only [MatcherClause.listComplexity_cons] at bound
          omega) head
      obtain ⟨computedClauses, clausesExecutable, computedTail⟩ := induction (by
        simp only [MatcherClause.listComplexity_cons] at bound
        omega)
      exact ⟨_, by
        simp [elaborateMatcherClausesUsing, clauseExecutable, clausesExecutable],
        .cons computedHead computedTail⟩

/-- Matcher literals preserve non-exact fuel-local replay. -/
theorem matcherM4FuelReplayStep : MatcherM4FuelReplayStep := by
  intro clauses coherent replay
  intro signature fuel context supply next generated derivation
    signatureWellFormed wellFormed
  cases fuel with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel =>
      simp only [ElaboratesFuel] at derivation
      have tracked :=
        M4FreshRenaming.MatcherTyping.MatcherLiteralElaboratesUsing.trackContextSupport
          signatureWellFormed wellFormed derivation
      cases tracked with
      | @mk generatedClauses next checked clausesDerivation =>
          have checkedValue : staticChecks signature clauses = true :=
            (staticChecksHold_iff signature clauses).1 checked
          obtain ⟨computedClauses, clausesExecutable,
              computedClausesDerivation⟩ :=
            matcherClausesFuel_replay coherent replay signatureWellFormed (by
              simp only [Expr.complexity_matcher]
              omega) clausesDerivation
          have clausesExecutableUsing :
              elaborateMatcherClausesUsing
                  (M4.elaborateFuelUsing unify signature fuel) signature context
                  (.var ⟨supply.ty⟩) clauses
                  ⟨supply.ty + 1, supply.cap + 1⟩ =
                some (computedClauses, next) := by
            simpa [M4.elaborateFuel] using clausesExecutable
          exact ⟨_, next, by
            simp [M4.elaborateFuel, M4.elaborateFuelUsing,
              elaborateMatcherLiteralUsing, checkedValue,
              clausesExecutableUsing],
            .mk checked computedClausesDerivation⟩

end TypePM.Source.M4.CompletenessArchitecture
