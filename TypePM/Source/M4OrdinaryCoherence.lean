import TypePM.Source.M4SupportedCoherence

/-!
# Coherence for ordinary M4 roots

The root constructors in this module are shared with M2, but their children
may use any M4 rule.  Consequently they cannot be translated to an M2 source
derivation.  Instead, the proofs compose the already completed supported
generated-block certificates and then use `SupportedM4FuelPairProperty.toFull`
to add principal-closure alignment.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source

private theorem typeAvoids_previousTy
    {start next : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn (start.nextTy 1) next hidden) :
    TypeAvoids hidden (.var ⟨start.ty⟩) := by
  intro candidate member hiddenMember
  have equality : candidate = .ty ⟨start.ty⟩ := by
    simpa [Ty.unificationVars] using member
  subst candidate
  have range := fresh (.ty ⟨start.ty⟩) hiddenMember
  simp [UnificationVar.FreshIn, Supply.nextTy] at range
  omega

private theorem typeAvoids_ty_of_finish_le
    {start finish : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn start finish hidden)
    {index : TyVar} (finishLe : finish.ty ≤ index.index) :
    TypeAvoids hidden (.var index) := by
  intro candidate member hiddenMember
  have equality : candidate = .ty index := by
    simpa [Ty.unificationVars] using member
  subst candidate
  have range := fresh (.ty index) hiddenMember
  exact Nat.not_lt_of_ge finishLe range.2

private theorem freshIntervals_disjoint
    {firstStart middle finish : Supply}
    {firstHidden secondHidden : List UnificationVar}
    (firstFresh : VariablesFreshIn firstStart middle firstHidden)
    (secondFresh : VariablesFreshIn middle finish secondHidden) :
    ∀ candidate, candidate ∈ firstHidden → candidate ∉ secondHidden := by
  intro candidate firstMember secondMember
  have firstRange := firstFresh candidate firstMember
  have secondRange := secondFresh candidate secondMember
  cases candidate with
  | ty index =>
      simp only [UnificationVar.FreshIn] at firstRange secondRange
      omega
  | cap index =>
      simp only [UnificationVar.FreshIn] at firstRange secondRange
      omega

/-- M4 counterpart of the M2 sequential cross-avoidance lemma. -/
private theorem elaboratesFuel_sequential_crossAvoidance
    {signature : FrozenSignature} (signatureWellFormed : signature.WellFormed)
    {earlierFuel laterFuel : Nat} {context : Context}
    {earlierExpression laterExpression : Expr} {start middle finish : Supply}
    {earlierGenerated laterGenerated : Generated}
    (earlierElaboration : ElaboratesFuel signature earlierFuel context
      earlierExpression start earlierGenerated middle)
    (laterElaboration : ElaboratesFuel signature laterFuel context
      laterExpression middle laterGenerated finish)
    (wellFormed : start.WellFormedFor context)
    {earlierHidden laterHidden : List UnificationVar}
    (earlierFresh : VariablesFreshIn start middle earlierHidden)
    (laterFresh : VariablesFreshIn middle finish laterHidden) :
    GeneratedAvoids earlierHidden laterGenerated ∧
      GeneratedAvoids laterHidden earlierGenerated := by
  constructor
  · exact VariablesScopedBy.avoids_earlier earlierFresh
      (laterElaboration.supportProvenance signatureWellFormed).scopedByInitialSupply
      wellFormed (Supply.le_refl middle)
  · exact VariablesScopedBy.avoids_later
      (earlierElaboration.supportProvenance
        signatureWellFormed).scopedByInitialSupply
      laterFresh wellFormed earlierElaboration.supply_le_next
      (Supply.le_refl middle)

/-- Pairwise supported coherence for a source-ordered M4 sibling list. -/
def SupportedM4ItemsFuelPairProperty (expressions : List Expr) : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {start : Supply}
      {leftItems rightItems : GeneratedItems} {leftNext rightNext : Supply}
      {leftFuel rightFuel : Nat},
    signature.WellFormed → start.WellFormedFor context →
      ItemsElaborateUsing (ElaboratesFuel signature leftFuel) context
          expressions start leftItems leftNext →
        ItemsElaborateUsing (ElaboratesFuel signature rightFuel) context
            expressions start rightItems rightNext →
          Nonempty (SupportedM2ItemsPairCoherence start leftNext rightNext
            leftItems rightItems)

/-- Supported coherence for an M4 fixed-arity call fold whose accumulated
function blocks may already differ. -/
def SupportedM4CallFuelPairProperty (arguments : List Expr) : Prop :=
  ∀ {signature : FrozenSignature} {context : Context}
      {outerStart start : Supply} {leftFuel rightFuel : Nat}
      {leftAccumulated rightAccumulated leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    signature.WellFormed →
      outerStart.WellFormedFor context → outerStart.Le start →
      GeneratedSupportProvenance context outerStart start leftAccumulated →
      GeneratedSupportProvenance context outerStart start rightAccumulated →
      SupportedEntailedAlignmentCertificate outerStart start
        leftAccumulated rightAccumulated →
      CallElaboratesUsing (ElaboratesFuel signature leftFuel) context
        leftAccumulated arguments start leftGenerated leftNext →
      CallElaboratesUsing (ElaboratesFuel signature rightFuel) context
        rightAccumulated arguments start rightGenerated rightNext →
      Nonempty (SupportedM2PairCoherence outerStart leftNext rightNext
        leftGenerated rightGenerated)

/-- M4 sibling-list counterpart of sequential cross-avoidance. -/
private theorem itemsElaborateUsing_cons_crossAvoidance
    {signature : FrozenSignature} (signatureWellFormed : signature.WellFormed)
    {itemFuel itemsFuel : Nat} {context : Context} {item : Expr}
    {items : List Expr} {start middle finish : Supply}
    {generatedItem : Generated} {generatedItems : GeneratedItems}
    (itemElaboration : ElaboratesFuel signature itemFuel context item start
      generatedItem middle)
    (itemsElaboration : ItemsElaborateUsing
      (ElaboratesFuel signature itemsFuel) context items middle
      generatedItems finish)
    (wellFormed : start.WellFormedFor context)
    {itemHidden itemsHidden : List UnificationVar}
    (itemFresh : VariablesFreshIn start middle itemHidden)
    (itemsFresh : VariablesFreshIn middle finish itemsHidden) :
    GeneratedItemsAvoid itemHidden generatedItems ∧
      GeneratedAvoids itemsHidden generatedItem := by
  have itemsSupport := itemsElaboration.supportProvenance
    (fun child => child.supply_le_next)
    (fun child => child.supportProvenance signatureWellFormed)
  constructor
  · exact VariablesScopedBy.avoids_earlier itemFresh
      itemsSupport.scopedByInitialSupply wellFormed (Supply.le_refl middle)
  · exact VariablesScopedBy.avoids_later
      (itemElaboration.supportProvenance
        signatureWellFormed).scopedByInitialSupply
      itemsFresh wellFormed itemElaboration.supply_le_next
      (Supply.le_refl middle)

namespace SupportedM4FuelPairProperty

/-- Variable leaves are deterministic after the common context lookup. -/
theorem var (index : Nat) : SupportedM4FuelPairProperty (.var index) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel _signatureWellFormed _wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          obtain ⟨leftScheme, leftLookup, rfl, rfl⟩ := leftElaboration
          obtain ⟨rightScheme, rightLookup, rfl, rfl⟩ := rightElaboration
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          exact ⟨
            { next_eq := rfl
              certificate := SupportedEntailedAlignmentCertificate.refl
                start (leftScheme.instantiate start).2 _ }⟩

/-- Integer literals elaborate literally. -/
theorem lit (value : Int) : SupportedM4FuelPairProperty (.lit value) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel _signatureWellFormed _wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          obtain ⟨rfl, rfl⟩ := leftElaboration
          obtain ⟨rfl, rfl⟩ := rightElaboration
          exact ⟨
            { next_eq := rfl
              certificate := SupportedEntailedAlignmentCertificate.refl
                _ _ _ }⟩

/-- The anonymous matcher leaf allocates the same ordinary type variable. -/
theorem something : SupportedM4FuelPairProperty .something := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel _signatureWellFormed _wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          obtain ⟨rfl, rfl⟩ := leftElaboration
          obtain ⟨rfl, rfl⟩ := rightElaboration
          exact ⟨
            { next_eq := rfl
              certificate := SupportedEntailedAlignmentCertificate.refl
                start (start.nextTy 1) _ }⟩

/-- Lambda composition works for arbitrary M4 bodies. -/
theorem lam {body : Expr}
    (bodyProperty : SupportedM4FuelPairProperty body) :
    SupportedM4FuelPairProperty (.lam body) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          obtain ⟨leftBody, leftBodyElaboration, rfl⟩ := leftElaboration
          obtain ⟨rightBody, rightBodyElaboration, rfl⟩ := rightElaboration
          have bodyWellFormed := wellFormed.monomorphic_cons_nextTy
          obtain ⟨bodyResult⟩ := bodyProperty signatureWellFormed
            bodyWellFormed leftBodyElaboration rightBodyElaboration
          cases bodyResult.next_eq
          let rebased := bodyResult.certificate.rebase
            (bodyResult.certificate.hiddenFresh.widen
              (Supply.le_nextTy start 1) (Supply.le_refl leftNext))
          exact ⟨
            { next_eq := rfl
              certificate := rebased.lam (.var ⟨start.ty⟩)
                (by
                  simpa [rebased,
                    SupportedEntailedAlignmentCertificate.rebase] using
                    (typeAvoids_previousTy
                      bodyResult.certificate.hiddenFresh)) }⟩

/-- Application composition for arbitrary M4 children. -/
theorem app {function argument : Expr}
    (functionProperty : SupportedM4FuelPairProperty function)
    (argumentProperty : SupportedM4FuelPairProperty argument) :
    SupportedM4FuelPairProperty (.app function argument) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          obtain ⟨leftFunction, leftAfterFunction, leftArgument,
            leftAfterArgument, leftFunctionElaboration,
            leftArgumentElaboration, rfl, rfl⟩ := leftElaboration
          obtain ⟨rightFunction, rightAfterFunction, rightArgument,
            rightAfterArgument, rightFunctionElaboration,
            rightArgumentElaboration, rfl, rfl⟩ := rightElaboration
          obtain ⟨functionResult⟩ := functionProperty signatureWellFormed
            wellFormed leftFunctionElaboration rightFunctionElaboration
          cases functionResult.next_eq
          obtain ⟨argumentResult⟩ := argumentProperty signatureWellFormed
            (wellFormed.mono leftFunctionElaboration.supply_le_next)
            leftArgumentElaboration rightArgumentElaboration
          cases argumentResult.next_eq
          have afterArgumentToNext : leftAfterArgument.Le
              (leftAfterArgument.nextTy 2) :=
            Supply.le_nextTy leftAfterArgument 2
          have functionToArgument : leftAfterFunction.Le leftAfterArgument :=
            leftArgumentElaboration.supply_le_next
          let functionCertificate := functionResult.certificate.rebase
            (functionResult.certificate.hiddenFresh.widen
              (Supply.le_refl start)
              (Supply.le_trans functionToArgument afterArgumentToNext))
          let argumentCertificate := argumentResult.certificate.rebase
            (argumentResult.certificate.hiddenFresh.widen
              leftFunctionElaboration.supply_le_next afterArgumentToNext)
          obtain ⟨leftArgumentAvoids, leftFunctionAvoids⟩ :=
            elaboratesFuel_sequential_crossAvoidance signatureWellFormed
              leftFunctionElaboration leftArgumentElaboration wellFormed
              functionResult.certificate.hiddenFresh
              argumentResult.certificate.hiddenFresh
          obtain ⟨rightArgumentAvoids, rightFunctionAvoids⟩ :=
            elaboratesFuel_sequential_crossAvoidance signatureWellFormed
              rightFunctionElaboration rightArgumentElaboration wellFormed
              functionResult.certificate.hiddenFresh
              argumentResult.certificate.hiddenFresh
          have functionDomainAvoids := typeAvoids_ty_of_finish_le
            functionResult.certificate.hiddenFresh
              (index := ⟨leftAfterArgument.ty⟩) functionToArgument.1
          have functionTargetAvoids := typeAvoids_ty_of_finish_le
            functionResult.certificate.hiddenFresh
              (index := ⟨leftAfterArgument.ty + 1⟩) (by
                change leftAfterFunction.ty ≤ leftAfterArgument.ty + 1
                exact Nat.le_trans functionToArgument.1
                  (Nat.le_add_right _ _))
          have argumentDomainAvoids := typeAvoids_ty_of_finish_le
            argumentResult.certificate.hiddenFresh
              (index := ⟨leftAfterArgument.ty⟩) (Nat.le_refl _)
          have argumentTargetAvoids := typeAvoids_ty_of_finish_le
            argumentResult.certificate.hiddenFresh
              (index := ⟨leftAfterArgument.ty + 1⟩) (by
                change leftAfterArgument.ty ≤ leftAfterArgument.ty + 1
                omega)
          exact ⟨
            { next_eq := rfl
              certificate := functionCertificate.app argumentCertificate
                (.var ⟨leftAfterArgument.ty⟩)
                (.var ⟨leftAfterArgument.ty + 1⟩)
                (by exact leftArgumentAvoids)
                (by exact rightArgumentAvoids)
                (by exact leftFunctionAvoids)
                (by exact rightFunctionAvoids)
                (by exact functionDomainAvoids)
                (by exact functionTargetAvoids)
                (by exact argumentDomainAvoids)
                (by exact argumentTargetAvoids)
                (freshIntervals_disjoint
                  functionResult.certificate.hiddenFresh
                  argumentResult.certificate.hiddenFresh) }⟩

/-- Empty sibling lists are literally identical. -/
theorem itemsNil : SupportedM4ItemsFuelPairProperty [] := by
  intro signature context start leftItems rightItems leftNext rightNext
    leftFuel rightFuel _signatureWellFormed _wellFormed leftElaboration
    rightElaboration
  cases leftElaboration
  cases rightElaboration
  exact ⟨
    { next_eq := rfl
      certificate := SupportedItemsAlignmentCertificate.refl
        start start GeneratedItems.nil }⟩

/-- Sequential sibling-list composition for arbitrary M4 children. -/
theorem itemsCons {item : Expr} {items : List Expr}
    (itemProperty : SupportedM4FuelPairProperty item)
    (itemsProperty : SupportedM4ItemsFuelPairProperty items) :
    SupportedM4ItemsFuelPairProperty (item :: items) := by
  intro signature context start leftItems rightItems leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftElaboration with
  | @cons _ _ _ leftItem leftAfterItem leftTail leftTailNext
      leftItemElaboration leftTailElaboration =>
    cases rightElaboration with
    | @cons _ _ _ rightItem rightAfterItem rightTail rightTailNext
        rightItemElaboration rightTailElaboration =>
      obtain ⟨itemResult⟩ := itemProperty signatureWellFormed wellFormed
        leftItemElaboration rightItemElaboration
      cases itemResult.next_eq
      obtain ⟨tailResult⟩ := itemsProperty signatureWellFormed
        (wellFormed.mono leftItemElaboration.supply_le_next)
        leftTailElaboration rightTailElaboration
      cases tailResult.next_eq
      let itemCertificate := itemResult.certificate.rebase
        (itemResult.certificate.hiddenFresh.widen
          (Supply.le_refl start)
          (leftTailElaboration.supply_le_next
            (fun child => child.supply_le_next)))
      let tailCertificate := tailResult.certificate.rebase
        (tailResult.certificate.hiddenFresh.widen
          leftItemElaboration.supply_le_next (Supply.le_refl leftNext))
      obtain ⟨leftTailAvoids, leftItemAvoids⟩ :=
        itemsElaborateUsing_cons_crossAvoidance signatureWellFormed
          leftItemElaboration leftTailElaboration wellFormed
          itemResult.certificate.hiddenFresh
          tailResult.certificate.hiddenFresh
      obtain ⟨rightTailAvoids, rightItemAvoids⟩ :=
        itemsElaborateUsing_cons_crossAvoidance signatureWellFormed
          rightItemElaboration rightTailElaboration wellFormed
          itemResult.certificate.hiddenFresh
          tailResult.certificate.hiddenFresh
      exact ⟨
        { next_eq := rfl
          certificate := SupportedItemsAlignmentCertificate.itemsCons
            itemCertificate tailCertificate
            (by exact leftTailAvoids)
            (by exact rightTailAvoids)
            (by exact leftItemAvoids)
            (by exact rightItemAvoids)
            (freshIntervals_disjoint
              itemResult.certificate.hiddenFresh
              tailResult.certificate.hiddenFresh) }⟩

/-- A tuple changes only the flat generated-items view. -/
theorem tuple {items : List Expr}
    (itemsProperty : SupportedM4ItemsFuelPairProperty items) :
    SupportedM4FuelPairProperty (.tuple items) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          obtain ⟨leftItems, leftItemsElaboration, rfl⟩ := leftElaboration
          obtain ⟨rightItems, rightItemsElaboration, rfl⟩ := rightElaboration
          obtain ⟨itemsResult⟩ := itemsProperty signatureWellFormed wellFormed
            leftItemsElaboration rightItemsElaboration
          exact ⟨
            { next_eq := itemsResult.next_eq
              certificate := itemsResult.certificate.itemsTuple }⟩

/-- Fold pointwise M4 coherence into sibling-list coherence. -/
theorem itemsOfEach {items : List Expr}
    (each : ∀ item, item ∈ items → SupportedM4FuelPairProperty item) :
    SupportedM4ItemsFuelPairProperty items := by
  induction items with
  | nil => exact itemsNil
  | cons item items induction =>
      exact itemsCons (each item (by simp))
        (induction (by
          intro tail tailMember
          exact each tail (by simp [tailMember])))

/-- A call with no remaining arguments returns its accumulated block. -/
theorem callNil : SupportedM4CallFuelPairProperty [] := by
  intro signature context outerStart start leftFuel rightFuel
    leftAccumulated rightAccumulated leftGenerated rightGenerated leftNext
    rightNext _signatureWellFormed _wellFormed _outerToStart _leftProvenance
    _rightProvenance accumulatedCertificate leftElaboration rightElaboration
  cases leftElaboration
  cases rightElaboration
  exact ⟨
    { next_eq := rfl
      certificate := accumulatedCertificate }⟩

/-- One call-fold step composes the accumulator with an arbitrary M4
argument, then passes the supported result to the tail. -/
theorem callCons {argument : Expr} {arguments : List Expr}
    (argumentProperty : SupportedM4FuelPairProperty argument)
    (argumentsProperty : SupportedM4CallFuelPairProperty arguments) :
    SupportedM4CallFuelPairProperty (argument :: arguments) := by
  intro signature context outerStart start leftFuel rightFuel
    leftAccumulated rightAccumulated leftGenerated rightGenerated leftNext
    rightNext signatureWellFormed wellFormed outerToStart leftProvenance
    rightProvenance accumulatedCertificate leftElaboration rightElaboration
  cases leftElaboration with
  | @cons _ _ _ _ leftArgument leftAfterArgument _ _
      leftArgumentElaboration leftRestElaboration =>
    cases rightElaboration with
    | @cons _ _ _ _ rightArgument rightAfterArgument _ _
        rightArgumentElaboration rightRestElaboration =>
      obtain ⟨argumentResult⟩ := argumentProperty signatureWellFormed
        (wellFormed.mono outerToStart)
        leftArgumentElaboration rightArgumentElaboration
      cases argumentResult.next_eq
      have startToAfter : start.Le leftAfterArgument :=
        leftArgumentElaboration.supply_le_next
      have afterToNext : leftAfterArgument.Le
          (leftAfterArgument.nextTy 2) :=
        Supply.le_nextTy leftAfterArgument 2
      have outerToAfter : outerStart.Le leftAfterArgument :=
        Supply.le_trans outerToStart startToAfter
      have outerToNext : outerStart.Le (leftAfterArgument.nextTy 2) :=
        Supply.le_trans outerToAfter afterToNext
      let accumulatedWide := accumulatedCertificate.rebase
        (accumulatedCertificate.hiddenFresh.widen
          (Supply.le_refl outerStart)
          (Supply.le_trans startToAfter afterToNext))
      let argumentWide := argumentResult.certificate.rebase
        (argumentResult.certificate.hiddenFresh.widen outerToStart afterToNext)
      have leftArgumentAvoids : GeneratedAvoids
          accumulatedCertificate.hidden leftArgument :=
        VariablesScopedBy.avoids_earlier
          accumulatedCertificate.hiddenFresh
          (leftArgumentElaboration.supportProvenance
            signatureWellFormed).scopedByInitialSupply
          wellFormed (Supply.le_refl start)
      have rightArgumentAvoids : GeneratedAvoids
          accumulatedCertificate.hidden rightArgument :=
        VariablesScopedBy.avoids_earlier
          accumulatedCertificate.hiddenFresh
          (rightArgumentElaboration.supportProvenance
            signatureWellFormed).scopedByInitialSupply
          wellFormed (Supply.le_refl start)
      have leftAccumulatedAvoids : GeneratedAvoids
          argumentResult.certificate.hidden leftAccumulated :=
        VariablesScopedBy.avoids_later
          leftProvenance.scopedByInitialSupply
          argumentResult.certificate.hiddenFresh wellFormed
          outerToStart (Supply.le_refl start)
      have rightAccumulatedAvoids : GeneratedAvoids
          argumentResult.certificate.hidden rightAccumulated :=
        VariablesScopedBy.avoids_later
          rightProvenance.scopedByInitialSupply
          argumentResult.certificate.hiddenFresh wellFormed
          outerToStart (Supply.le_refl start)
      have accumulatedDomainAvoids := typeAvoids_ty_of_finish_le
        accumulatedCertificate.hiddenFresh
          (index := ⟨leftAfterArgument.ty⟩)
          (Nat.le_trans startToAfter.1 (Nat.le_refl _))
      have accumulatedTargetAvoids := typeAvoids_ty_of_finish_le
        accumulatedCertificate.hiddenFresh
          (index := ⟨leftAfterArgument.ty + 1⟩) (by
            change start.ty ≤ leftAfterArgument.ty + 1
            exact Nat.le_trans startToAfter.1 (Nat.le_add_right _ _))
      have argumentDomainAvoids := typeAvoids_ty_of_finish_le
        argumentResult.certificate.hiddenFresh
          (index := ⟨leftAfterArgument.ty⟩) (Nat.le_refl _)
      have argumentTargetAvoids := typeAvoids_ty_of_finish_le
        argumentResult.certificate.hiddenFresh
          (index := ⟨leftAfterArgument.ty + 1⟩) (by
            change leftAfterArgument.ty ≤ leftAfterArgument.ty + 1
            omega)
      let appliedCertificate := accumulatedWide.app argumentWide
        (.var ⟨leftAfterArgument.ty⟩)
        (.var ⟨leftAfterArgument.ty + 1⟩)
        leftArgumentAvoids rightArgumentAvoids
        leftAccumulatedAvoids rightAccumulatedAvoids
        accumulatedDomainAvoids accumulatedTargetAvoids
        argumentDomainAvoids argumentTargetAvoids
        (freshIntervals_disjoint accumulatedCertificate.hiddenFresh
          argumentResult.certificate.hiddenFresh)
      have leftAppliedProvenance : GeneratedSupportProvenance context
          outerStart (leftAfterArgument.nextTy 2)
          (Generated.fromApp leftAccumulated leftArgument
            (.var ⟨leftAfterArgument.ty⟩)
            (.var ⟨leftAfterArgument.ty + 1⟩)) :=
        GeneratedSupportProvenance.fromApp_recursive outerToStart
          leftArgumentElaboration.supply_le_next leftProvenance
          (leftArgumentElaboration.supportProvenance signatureWellFormed)
      have rightAppliedProvenance : GeneratedSupportProvenance context
          outerStart (leftAfterArgument.nextTy 2)
          (Generated.fromApp rightAccumulated rightArgument
            (.var ⟨leftAfterArgument.ty⟩)
            (.var ⟨leftAfterArgument.ty + 1⟩)) :=
        GeneratedSupportProvenance.fromApp_recursive outerToStart
          rightArgumentElaboration.supply_le_next rightProvenance
          (rightArgumentElaboration.supportProvenance signatureWellFormed)
      exact argumentsProperty signatureWellFormed wellFormed outerToNext
        leftAppliedProvenance rightAppliedProvenance appliedCertificate
        leftRestElaboration rightRestElaboration

/-- Fold pointwise M4 coherence into call-fold coherence. -/
theorem callOfEach {arguments : List Expr}
    (each : ∀ argument, argument ∈ arguments →
      SupportedM4FuelPairProperty argument) :
    SupportedM4CallFuelPairProperty arguments := by
  induction arguments with
  | nil => exact callNil
  | cons argument arguments induction =>
      exact callCons (each argument (by simp))
        (induction (by
          intro tail tailMember
          exact each tail (by simp [tailMember])))

/-- Constructor calls start from the same closed scheme instance. -/
theorem ctor (constructor : DataCtor) {arguments : List Expr}
    (argumentsProperty : SupportedM4CallFuelPairProperty arguments) :
    SupportedM4FuelPairProperty (.ctor constructor arguments) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          obtain ⟨leftScheme, leftLookup, _leftArity, leftClosed, leftCall⟩ :=
            leftElaboration
          obtain ⟨rightScheme, rightLookup, _rightArity, rightClosed,
            rightCall⟩ := rightElaboration
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          exact argumentsProperty signatureWellFormed wellFormed
            (by simp [Supply.Le, Scheme.instantiate])
            (supportProvenance_closed_instantiate leftClosed)
            (supportProvenance_closed_instantiate rightClosed)
            (SupportedEntailedAlignmentCertificate.refl start
              (leftScheme.instantiate start).2 _)
            leftCall rightCall

/-- Primitive calls use the same closed-scheme call fold. -/
theorem prim (operation : PrimOp) {arguments : List Expr}
    (argumentsProperty : SupportedM4CallFuelPairProperty arguments) :
    SupportedM4FuelPairProperty (.prim operation arguments) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          obtain ⟨leftScheme, leftLookup, _leftArity, leftClosed, leftCall⟩ :=
            leftElaboration
          obtain ⟨rightScheme, rightLookup, _rightArity, rightClosed,
            rightCall⟩ := rightElaboration
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          exact argumentsProperty signatureWellFormed wellFormed
            (by simp [Supply.Le, Scheme.instantiate])
            (supportProvenance_closed_instantiate leftClosed)
            (supportProvenance_closed_instantiate rightClosed)
            (SupportedEntailedAlignmentCertificate.refl start
              (leftScheme.instantiate start).2 _)
            leftCall rightCall

/-- Conditionals are the fixed closed three-argument call. -/
theorem ifE {condition thenBranch elseBranch : Expr}
    (argumentsProperty : SupportedM4CallFuelPairProperty
      [condition, thenBranch, elseBranch]) :
    SupportedM4FuelPairProperty (.ifE condition thenBranch elseBranch) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          exact argumentsProperty signatureWellFormed wellFormed
            (by simp [Supply.Le, Scheme.instantiate])
            (supportProvenance_closed_instantiate conditionalScheme_closed)
            (supportProvenance_closed_instantiate conditionalScheme_closed)
            (SupportedEntailedAlignmentCertificate.refl start
              (conditionalScheme.instantiate start).2 _)
            leftElaboration rightElaboration

end SupportedM4FuelPairProperty

private theorem expression_complexity_lt_list_succ
    {expression : Expr} {expressions : List Expr}
    (member : expression ∈ expressions) :
    expression.complexity < Expr.listComplexity expressions + 1 := by
  induction expressions with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with equality | tailMember
      · subst expression
        simp [Expr.listComplexity]
        omega
      · have smaller := induction tailMember
        simp [Expr.listComplexity]
        omega

/-- All ordinary M4 roots are coherent even when their children use the new
M4 constructors. -/
theorem ordinaryM4CoherenceStep : OrdinaryM4CoherenceStep := by
  intro expression root induction
  cases root with
  | var index =>
      exact SupportedM4FuelPairProperty.toFull
        (SupportedM4FuelPairProperty.var index)
  | lit value =>
      exact SupportedM4FuelPairProperty.toFull
        (SupportedM4FuelPairProperty.lit value)
  | something =>
      exact SupportedM4FuelPairProperty.toFull
        SupportedM4FuelPairProperty.something
  | lam body =>
      apply SupportedM4FuelPairProperty.toFull
      apply SupportedM4FuelPairProperty.lam
      exact FullM4FuelPairProperty.toSupported
        (induction body (by simp [Expr.complexity]))
  | app function argument =>
      apply SupportedM4FuelPairProperty.toFull
      apply SupportedM4FuelPairProperty.app
      · exact FullM4FuelPairProperty.toSupported (induction function (by
          simp [Expr.complexity]
          omega))
      · exact FullM4FuelPairProperty.toSupported (induction argument (by
          simp [Expr.complexity]
          omega))
  | tuple items =>
      apply SupportedM4FuelPairProperty.toFull
      apply SupportedM4FuelPairProperty.tuple
      apply SupportedM4FuelPairProperty.itemsOfEach
      intro item member
      apply FullM4FuelPairProperty.toSupported
      exact induction item (by
        have smaller := expression_complexity_lt_list_succ member
        simpa [Expr.complexity] using smaller)
  | ctor constructor arguments =>
      apply SupportedM4FuelPairProperty.toFull
      apply SupportedM4FuelPairProperty.ctor constructor
      apply SupportedM4FuelPairProperty.callOfEach
      intro argument member
      apply FullM4FuelPairProperty.toSupported
      exact induction argument (by
        have smaller := expression_complexity_lt_list_succ member
        simpa [Expr.complexity] using smaller)
  | prim operation arguments =>
      apply SupportedM4FuelPairProperty.toFull
      apply SupportedM4FuelPairProperty.prim operation
      apply SupportedM4FuelPairProperty.callOfEach
      intro argument member
      apply FullM4FuelPairProperty.toSupported
      exact induction argument (by
        have smaller := expression_complexity_lt_list_succ member
        simpa [Expr.complexity] using smaller)
  | ifE condition thenBranch elseBranch =>
      apply SupportedM4FuelPairProperty.toFull
      apply SupportedM4FuelPairProperty.ifE
      apply SupportedM4FuelPairProperty.callOfEach
      intro argument member
      apply FullM4FuelPairProperty.toSupported
      exact induction argument (by
        have smaller := expression_complexity_lt_list_succ member
        simp [Expr.listComplexity] at smaller
        simp [Expr.complexity]
        omega)

end TypePM.Source.M4.CompletenessArchitecture
