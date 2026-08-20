import TypePM.Source.M4OrdinaryCoherence
import TypePM.Source.M4FreshRenamingTransport

/-!
# Supported pair coherence for M4 user patterns

User patterns contain recursively elaborated source expressions, so their
coherence is parameterized by a pair-coherence hypothesis for every embedded
expression.  A generated dual is encoded as one ordinary generated-block
target; this lets the existing supported alias certificates compose pattern
lists without introducing a second alias calculus.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source

/-- Inject both components of a generated pattern dual into an ordinary type. -/
def encodedPatternDual (dual : Dual) : Ty :=
  .fn (.slot dual.capability (.prod [])) dual.target

/-- Ordinary generated-block view of one generated user pattern. -/
def patternAsGenerated (generated : GeneratedPattern) : Generated :=
  { target := encodedPatternDual generated.dual
    hard := generated.hard
    pending := generated.pending }

/-- Flat generated-items view of a generated pattern list. -/
def patternsAsGeneratedItems
    (generated : GeneratedPatterns) : GeneratedItems :=
  { targets := generated.duals.map encodedPatternDual
    hard := generated.hard
    pending := generated.pending }

/-- Supply, binding-interface, and supported semantic agreement for one user
pattern elaborated with two possibly different M4 fuel values. -/
structure SupportedM4PatternPairCoherence
    (start leftNext rightNext : Supply)
    (left right : GeneratedPattern) where
  next_eq : leftNext = rightNext
  bindings_eq : left.bindings = right.bindings
  certificate : SupportedEntailedAlignmentCertificate start leftNext
    (patternAsGenerated left) (patternAsGenerated right)
  leftBindingsAvoid : VariablesAvoid certificate.hidden
    (Ty.unificationVarsList left.bindings)
  rightBindingsAvoid : VariablesAvoid certificate.hidden
    (Ty.unificationVarsList right.bindings)

/-- Pattern-list counterpart of `SupportedM4PatternPairCoherence`. -/
structure SupportedM4PatternsPairCoherence
    (start leftNext rightNext : Supply)
    (left right : GeneratedPatterns) where
  next_eq : leftNext = rightNext
  bindings_eq : left.bindings = right.bindings
  certificate : SupportedItemsAlignmentCertificate start leftNext
    (patternsAsGeneratedItems left) (patternsAsGeneratedItems right)
  leftBindingsAvoid : VariablesAvoid certificate.hidden
    (Ty.unificationVarsList left.bindings)
  rightBindingsAvoid : VariablesAvoid certificate.hidden
    (Ty.unificationVarsList right.bindings)

/-- The callback hypothesis consumed at embedded value-pattern expressions. -/
def SupportedM4ExpressionPairProperty
    (signature : FrozenSignature) (leftFuel rightFuel : Nat) : Prop :=
  ∀ {context : Context} {expression : Expr} {start : Supply}
      {left right : Generated} {leftNext rightNext : Supply},
    start.WellFormedFor context →
      ElaboratesFuel signature leftFuel context expression start left leftNext →
      ElaboratesFuel signature rightFuel context expression start right rightNext →
      Nonempty (SupportedM2PairCoherence start leftNext rightNext left right)

/-- Complexity-bounded callback used when pattern coherence is discharged
from the induction hypothesis of an enclosing expression constructor. -/
def SupportedM4ExpressionPairPropertyBelow
    (signature : FrozenSignature) (leftFuel rightFuel limit : Nat) : Prop :=
  ∀ {context : Context} {expression : Expr} {start : Supply}
      {left right : Generated} {leftNext rightNext : Supply},
    expression.complexity < limit →
      start.WellFormedFor context →
        ElaboratesFuel signature leftFuel context expression start left leftNext →
        ElaboratesFuel signature rightFuel context expression start right rightNext →
        Nonempty (SupportedM2PairCoherence start leftNext rightNext left right)

/-- The syntax-independent part of an embedded-expression comparison. -/
def M4ExpressionSupplyPairProperty
    (left right : M4ExpressionElaborationRelation) : Prop :=
  ∀ {context : Context} {expression : Expr} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    left context expression start leftGenerated leftNext →
      right context expression start rightGenerated rightNext →
      leftNext = rightNext

mutual

/-- Pattern synthesis has a fuel-independent supply and binding interface as
soon as embedded expressions have a fuel-independent finishing supply. -/
theorem PatternElaboratesUsing.shapeCoherence
    {left right : M4ExpressionElaborationRelation}
    (expressionSupply : M4ExpressionSupplyPairProperty left right)
    {signature : FrozenSignature} {context : Context}
    {arguments : PatternContext} {pattern : Pattern} {bindings : List Ty}
    {start : Supply} {leftGenerated rightGenerated : GeneratedPattern}
    {leftNext rightNext : Supply}
    (leftDerivation : PatternElaboratesUsing left signature context arguments
      pattern bindings start leftGenerated leftNext)
    (rightDerivation : PatternElaboratesUsing right signature context arguments
      pattern bindings start rightGenerated rightNext) :
    leftNext = rightNext ∧ leftGenerated.bindings = rightGenerated.bindings := by
  cases leftDerivation with
  | var => cases rightDerivation; exact ⟨rfl, rfl⟩
  | wild => cases rightDerivation; exact ⟨rfl, rfl⟩
  | value leftExpression =>
      cases rightDerivation with
      | value rightExpression =>
          cases expressionSupply leftExpression rightExpression
          exact ⟨rfl, rfl⟩
  | @ctor constructor fields bindings start leftScheme leftFields leftFinish
      leftLookup leftArity leftFieldsDerivation =>
      cases rightDerivation with
      | @ctor _ _ _ _ rightScheme rightFields rightFinish rightLookup
          rightArity rightFieldsDerivation =>
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          exact PatternsElaborateUsing.shapeCoherence
            (left := left) (right := right) expressionSupply
            leftFieldsDerivation rightFieldsDerivation
  | tuple leftItemsDerivation =>
      cases rightDerivation with
      | tuple rightItemsDerivation =>
          exact PatternsElaborateUsing.shapeCoherence
            (left := left) (right := right) expressionSupply
            leftItemsDerivation rightItemsDerivation
  | @and leftPattern rightPattern bindings start leftFirst leftMiddle
      leftSecond leftFinish leftFirstDerivation leftSecondDerivation =>
      cases rightDerivation with
      | @and _ _ _ _ rightFirst rightMiddle rightSecond rightFinish
          rightFirstDerivation rightSecondDerivation =>
          obtain ⟨middleEquality, bindingEquality⟩ :=
            PatternElaboratesUsing.shapeCoherence
              (left := left) (right := right) expressionSupply
              leftFirstDerivation rightFirstDerivation
          cases middleEquality
          rw [← bindingEquality] at rightSecondDerivation
          exact PatternElaboratesUsing.shapeCoherence
            (left := left) (right := right) expressionSupply
            (pattern := rightPattern)
            (leftGenerated := leftSecond) (rightGenerated := rightSecond)
            leftSecondDerivation rightSecondDerivation
  | @or leftPattern rightPattern bindings start leftFirst leftMiddle
      leftSecond leftFinish leftChecks leftFirstDerivation leftSecondDerivation
      leftBindingChecks =>
      cases rightDerivation with
      | @or _ _ _ _ rightFirst rightMiddle rightSecond rightFinish rightChecks
          rightFirstDerivation rightSecondDerivation rightBindingChecks =>
          obtain ⟨middleEquality, leftBindingEquality⟩ :=
            PatternElaboratesUsing.shapeCoherence
              (left := left) (right := right) expressionSupply
              leftFirstDerivation rightFirstDerivation
          cases middleEquality
          obtain ⟨finishEquality, rightBindingEquality⟩ :=
            PatternElaboratesUsing.shapeCoherence
              (left := left) (right := right) expressionSupply
              leftSecondDerivation rightSecondDerivation
          exact ⟨finishEquality, leftBindingEquality⟩
  | embed leftLookup => cases rightDerivation; exact ⟨rfl, rfl⟩
  | @app function fields bindings start leftScheme leftFields leftFinish
      leftLookup leftArity leftFieldsDerivation =>
      cases rightDerivation with
      | @app _ _ _ _ rightScheme rightFields rightFinish rightLookup
          rightArity rightFieldsDerivation =>
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          exact PatternsElaborateUsing.shapeCoherence
            (left := left) (right := right) expressionSupply
            leftFieldsDerivation rightFieldsDerivation
termination_by pattern.complexity * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

/-- List counterpart of `PatternElaboratesUsing.shapeCoherence`. -/
theorem PatternsElaborateUsing.shapeCoherence
    {left right : M4ExpressionElaborationRelation}
    (expressionSupply : M4ExpressionSupplyPairProperty left right)
    {signature : FrozenSignature} {context : Context}
    {arguments : PatternContext} {patterns : List Pattern} {bindings : List Ty}
    {start : Supply} {leftGenerated rightGenerated : GeneratedPatterns}
    {leftNext rightNext : Supply}
    (leftDerivation : PatternsElaborateUsing left signature context arguments
      patterns bindings start leftGenerated leftNext)
    (rightDerivation : PatternsElaborateUsing right signature context arguments
      patterns bindings start rightGenerated rightNext) :
    leftNext = rightNext ∧ leftGenerated.bindings = rightGenerated.bindings := by
  cases leftDerivation with
  | nil => cases rightDerivation; exact ⟨rfl, rfl⟩
  | @cons pattern patterns bindings start leftHead leftMiddle leftTail leftFinish
      leftHeadDerivation leftTailDerivation =>
      cases rightDerivation with
      | @cons _ _ _ _ rightHead rightMiddle rightTail rightFinish
          rightHeadDerivation rightTailDerivation =>
          obtain ⟨middleEquality, bindingEquality⟩ :=
            PatternElaboratesUsing.shapeCoherence
              (left := left) (right := right) expressionSupply
              leftHeadDerivation rightHeadDerivation
          cases middleEquality
          rw [← bindingEquality] at rightTailDerivation
          exact PatternsElaborateUsing.shapeCoherence
            (left := left) (right := right) expressionSupply
            (patterns := patterns)
            (leftGenerated := leftTail) (rightGenerated := rightTail)
            leftTailDerivation rightTailDerivation
termination_by Pattern.listComplexity patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [Pattern.listComplexity]
  all_goals omega

end

/-- Fuel-specialized structural coherence.  Scope tracking supplies the
well-formed callback context needed to invoke embedded-expression
coherence. -/
theorem PatternElaboratesUsing.fuelShapeCoherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    (signatureWellFormed : signature.WellFormed)
    (expressionPair : SupportedM4ExpressionPairProperty
      signature leftFuel rightFuel)
    {context : Context} {outerStart start : Supply}
    {arguments : PatternContext} {pattern : Pattern} {bindings : List Ty}
    {leftGenerated rightGenerated : GeneratedPattern}
    {leftNext rightNext : Supply}
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (leftDerivation : PatternElaboratesUsing
      (ElaboratesFuel signature leftFuel) signature context arguments pattern
      bindings start leftGenerated leftNext)
    (rightDerivation : PatternElaboratesUsing
      (ElaboratesFuel signature rightFuel) signature context arguments pattern
      bindings start rightGenerated rightNext) :
    leftNext = rightNext ∧ leftGenerated.bindings = rightGenerated.bindings := by
  have leftTracked := M4FreshRenaming.PatternElaboratesUsing.trackContextSupport
    signatureWellFormed contextWellFormed argumentsSupport bindingsSupport
    outerToStart leftDerivation
  have rightTracked := M4FreshRenaming.PatternElaboratesUsing.trackContextSupport
    signatureWellFormed contextWellFormed argumentsSupport bindingsSupport
    outerToStart rightDerivation
  apply PatternElaboratesUsing.shapeCoherence
    (left := M4FreshRenaming.WellFormedFuelLeaf signature leftFuel)
    (right := M4FreshRenaming.WellFormedFuelLeaf signature rightFuel) _
    leftTracked rightTracked
  intro childContext expression childStart leftChild rightChild
    leftChildNext rightChildNext leftLeaf rightLeaf
  obtain ⟨comparison⟩ := expressionPair leftLeaf.1 leftLeaf.2 rightLeaf.2
  exact comparison.next_eq

/-- List counterpart of `PatternElaboratesUsing.fuelShapeCoherence`. -/
theorem PatternsElaborateUsing.fuelShapeCoherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    (signatureWellFormed : signature.WellFormed)
    (expressionPair : SupportedM4ExpressionPairProperty
      signature leftFuel rightFuel)
    {context : Context} {outerStart start : Supply}
    {arguments : PatternContext} {patterns : List Pattern} {bindings : List Ty}
    {leftGenerated rightGenerated : GeneratedPatterns}
    {leftNext rightNext : Supply}
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (leftDerivation : PatternsElaborateUsing
      (ElaboratesFuel signature leftFuel) signature context arguments patterns
      bindings start leftGenerated leftNext)
    (rightDerivation : PatternsElaborateUsing
      (ElaboratesFuel signature rightFuel) signature context arguments patterns
      bindings start rightGenerated rightNext) :
    leftNext = rightNext ∧ leftGenerated.bindings = rightGenerated.bindings := by
  have leftTracked := M4FreshRenaming.PatternsElaborateUsing.trackContextSupport
    signatureWellFormed contextWellFormed argumentsSupport bindingsSupport
    outerToStart leftDerivation
  have rightTracked := M4FreshRenaming.PatternsElaborateUsing.trackContextSupport
    signatureWellFormed contextWellFormed argumentsSupport bindingsSupport
    outerToStart rightDerivation
  apply PatternsElaborateUsing.shapeCoherence
    (left := M4FreshRenaming.WellFormedFuelLeaf signature leftFuel)
    (right := M4FreshRenaming.WellFormedFuelLeaf signature rightFuel) _
    leftTracked rightTracked
  intro childContext expression childStart leftChild rightChild
    leftChildNext rightChildNext leftLeaf rightLeaf
  obtain ⟨comparison⟩ := expressionPair leftLeaf.1 leftLeaf.2 rightLeaf.2
  exact comparison.next_eq

private theorem typeAvoids_patternCapabilityAtFinish
    {start finish : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn start finish hidden) :
    TypeAvoids hidden (.slot (.var ⟨finish.cap⟩) (.prod [])) := by
  intro candidate member hiddenMember
  have range := fresh candidate hiddenMember
  cases candidate with
  | cap index =>
      simp [Ty.unificationVars, Cap.unificationVars,
        UnificationVar.FreshIn] at member range
      rcases member with equality | impossible
      · have rawEquality := congrArg CapVar.index equality
        simp only at rawEquality
        omega
      · change false = true at impossible
        contradiction
  | ty index =>
      simp [Ty.unificationVars, Cap.unificationVars] at member
      change false = true at member
      contradiction

private theorem entailedPendingEq_weaken
    {weaker stronger : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq weaker left right)
    (entails : ∀ substitution, Solves substitution stronger →
      Solves substitution weaker) :
    EntailedPendingEq stronger left right := by
  induction aligned with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (head.weaken entails) induction

private def repackageCertificate
    {start next : Supply} {left right left' right' : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (leftScoped : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
      left'.unificationVars certificate.leftAliases)
    (rightScoped : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
      right'.unificationVars certificate.rightAliases)
    (aligned : EntailedGeneratedAlignment
      (FreshAliasSequence.addAll certificate.leftAliases left')
      (FreshAliasSequence.addAll certificate.rightAliases right')) :
    SupportedEntailedAlignmentCertificate start next left' right' :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := leftScoped
    rightScoped := rightScoped
    aligned := aligned }

private theorem patternAsGenerated_value
    (generated : Generated) (bindings : List Ty) (finish : Supply) :
    patternAsGenerated
      ⟨⟨.var ⟨finish.cap⟩, generated.target⟩, bindings, generated.hard,
        generated.pending⟩ =
      Generated.fromLam (.slot (.var ⟨finish.cap⟩) (.prod [])) generated :=
  rfl

private def supportedPatternRefl
    (start next : Supply) (generated : GeneratedPattern) :
    SupportedM4PatternPairCoherence start next next generated generated :=
  { next_eq := rfl
    bindings_eq := rfl
    certificate := SupportedEntailedAlignmentCertificate.refl start next
      (patternAsGenerated generated)
    leftBindingsAvoid := by
      intro candidate member hidden
      change candidate ∈ [] at hidden
      simp at hidden
    rightBindingsAvoid := by
      intro candidate member hidden
      change candidate ∈ [] at hidden
      simp at hidden }

private theorem supportedValuePattern
    {start leftFinish rightFinish : Supply}
    {leftGenerated rightGenerated : Generated} {bindings : List Ty}
    (child : SupportedM2PairCoherence start leftFinish rightFinish
      leftGenerated rightGenerated)
    (leftBindingsAvoid : VariablesAvoid child.certificate.hidden
      (Ty.unificationVarsList bindings))
    (rightBindingsAvoid : VariablesAvoid child.certificate.hidden
      (Ty.unificationVarsList bindings)) :
    Nonempty (SupportedM4PatternPairCoherence start
      ⟨leftFinish.ty, leftFinish.cap + 1⟩
      ⟨rightFinish.ty, rightFinish.cap + 1⟩
      ⟨⟨.var ⟨leftFinish.cap⟩, leftGenerated.target⟩, bindings,
        leftGenerated.hard, leftGenerated.pending⟩
      ⟨⟨.var ⟨rightFinish.cap⟩, rightGenerated.target⟩, bindings,
        rightGenerated.hard, rightGenerated.pending⟩) := by
  cases child.next_eq
  let patternFinish : Supply :=
    ⟨leftFinish.ty, leftFinish.cap + 1⟩
  let widened : SupportedEntailedAlignmentCertificate start patternFinish
      leftGenerated rightGenerated := child.certificate.rebase
    (child.certificate.hiddenFresh.widen (Supply.le_refl start)
      (by simp [patternFinish, Supply.Le]))
  have domainAvoids : TypeAvoids widened.hidden
      (.slot (.var ⟨leftFinish.cap⟩) (.prod [])) := by
    simpa [widened, SupportedEntailedAlignmentCertificate.rebase] using
      typeAvoids_patternCapabilityAtFinish child.certificate.hiddenFresh
  exact ⟨
    { next_eq := rfl
      bindings_eq := rfl
      certificate := by
        simpa only [patternAsGenerated_value] using
          widened.lam (.slot (.var ⟨leftFinish.cap⟩) (.prod []))
            domainAvoids
      leftBindingsAvoid := leftBindingsAvoid
      rightBindingsAvoid := rightBindingsAvoid }⟩

private theorem encodedDual_apply_components
    {left right : Dual} {substitution : Subst}
    (equality : (encodedPatternDual left).apply substitution =
      (encodedPatternDual right).apply substitution) :
    left.capability.apply substitution.cap =
        right.capability.apply substitution.cap ∧
      left.target.apply substitution = right.target.apply substitution := by
  simp only [encodedPatternDual, Ty.apply] at equality
  injection equality with domains targets
  injection domains with capabilities _units
  exact ⟨capabilities, targets⟩

private theorem encodedDualList_apply_components
    {left right : List Dual} {substitution : Subst}
    (equality : Ty.applyList substitution
        (left.map encodedPatternDual) =
      Ty.applyList substitution (right.map encodedPatternDual)) :
    Cap.applyList substitution.cap (Dual.capabilities left) =
        Cap.applyList substitution.cap (Dual.capabilities right) ∧
      Ty.applyList substitution (Dual.targets left) =
        Ty.applyList substitution (Dual.targets right) := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [Ty.applyList] at equality ⊢
  | cons leftHead leftTail induction =>
      cases right with
      | nil => simp [Ty.applyList] at equality
      | cons rightHead rightTail =>
          simp only [List.map_cons, Ty.applyList, List.cons.injEq] at equality
          obtain ⟨headEquality, tailEquality⟩ := equality
          obtain ⟨capabilityEquality, targetEquality⟩ :=
            encodedDual_apply_components headEquality
          obtain ⟨capabilitiesEquality, targetsEquality⟩ :=
            induction tailEquality
          constructor
          · change leftHead.capability.apply substitution.cap ::
                Cap.applyList substitution.cap (Dual.capabilities leftTail) =
              rightHead.capability.apply substitution.cap ::
                Cap.applyList substitution.cap (Dual.capabilities rightTail)
            rw [capabilityEquality, capabilitiesEquality]
          · change leftHead.target.apply substitution ::
                Ty.applyList substitution (Dual.targets leftTail) =
              rightHead.target.apply substitution ::
                Ty.applyList substitution (Dual.targets rightTail)
            rw [targetEquality, targetsEquality]

private theorem encodedDualList_result
    {left right : List Dual} {substitution : Subst}
    (equality : Ty.applyList substitution
        (left.map encodedPatternDual) =
      Ty.applyList substitution (right.map encodedPatternDual)) :
    (encodedPatternDual
      ⟨.prod (Dual.capabilities left), .prod (Dual.targets left)⟩).apply
        substitution =
      (encodedPatternDual
        ⟨.prod (Dual.capabilities right), .prod (Dual.targets right)⟩).apply
          substitution := by
  obtain ⟨capabilitiesEquality, targetsEquality⟩ :=
    encodedDualList_apply_components equality
  simp [encodedPatternDual, Ty.apply, Cap.apply, capabilitiesEquality,
    targetsEquality]

private theorem occursTyList_encodedPatternDual
    (index : TyVar) (duals : List Dual) :
    Ty.occursTyList index (duals.map encodedPatternDual) =
      Ty.occursTyList index (Dual.targets duals) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [encodedPatternDual, Dual.targets, Ty.occursTyList,
        Ty.occursTy, induction]

private theorem occursCapList_encodedPatternDual
    (index : CapVar) (duals : List Dual) :
    Ty.occursCapList index (duals.map encodedPatternDual) =
      (Cap.occursList index (Dual.capabilities duals) ||
        Ty.occursCapList index (Dual.targets duals)) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [encodedPatternDual, Dual.capabilities, Dual.targets, induction,
        Ty.occursCapList, Ty.occursCap, Cap.occursList,
        Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private def tuplePatternResult (generated : GeneratedPatterns) : GeneratedPattern :=
  { dual := ⟨.prod (Dual.capabilities generated.duals),
      .prod (Dual.targets generated.duals)⟩
    bindings := generated.bindings
    hard := generated.hard
    pending := generated.pending }

private theorem tuplePattern_mem_unificationVars_iff
    (generated : GeneratedPatterns) (candidate : UnificationVar) :
    candidate ∈
        (patternAsGenerated (tuplePatternResult generated)).unificationVars ↔
      candidate ∈ (GeneratedItems.asTuple
        (patternsAsGeneratedItems generated)).unificationVars := by
  cases candidate with
  | cap index =>
    simp [patternAsGenerated, tuplePatternResult, encodedPatternDual,
      patternsAsGeneratedItems, GeneratedItems.asTuple,
      Generated.unificationVars, Ty.unificationVars, Cap.unificationVars,
      occursCapList_encodedPatternDual, Ty.occursCapList,
      Bool.or_eq_true]
    constructor
    · rintro (capability | target | hard | pending)
      · exact Or.inl (Or.inl capability)
      · exact Or.inl (Or.inr target)
      · exact Or.inr (Or.inl hard)
      · exact Or.inr (Or.inr pending)
    · rintro ((capability | target) | hard | pending)
      · exact Or.inl capability
      · exact Or.inr (Or.inl target)
      · exact Or.inr (Or.inr (Or.inl hard))
      · exact Or.inr (Or.inr (Or.inr pending))
  | ty index =>
    simp [patternAsGenerated, tuplePatternResult, encodedPatternDual,
      patternsAsGeneratedItems, GeneratedItems.asTuple,
      Generated.unificationVars, Ty.unificationVars, Cap.unificationVars,
      occursTyList_encodedPatternDual, Ty.occursTyList]

private theorem addAll_hard_eq_of_hard_eq
    (aliases : List FreshAliasSequence.Alias) {left right : Generated}
    (equality : left.hard = right.hard) :
    (FreshAliasSequence.addAll aliases left).hard =
      (FreshAliasSequence.addAll aliases right).hard := by
  induction aliases generalizing left right with
  | nil => exact equality
  | cons alias aliases induction =>
      simp only [FreshAliasSequence.addAll]
      apply induction
      cases alias <;> simp [FreshAliasSequence.Alias.add,
        FreshAliasElimination.addTyAlias,
        FreshAliasElimination.addCapAlias, equality]

private theorem scopedBy_tuplePattern
    {generated : GeneratedPatterns}
    {aliases : List FreshAliasSequence.Alias}
    (scope : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
      (GeneratedItems.asTuple
        (patternsAsGeneratedItems generated)).unificationVars aliases) :
    InterfaceAliasDecomposition.AliasFreshness.ScopedBy
      (patternAsGenerated (tuplePatternResult generated)).unificationVars
      aliases := by
  refine ⟨scope.1, ?_⟩
  intro alias member
  have endpoints := scope.2 alias member
  constructor
  · intro freshMember
    exact endpoints.1 ((tuplePattern_mem_unificationVars_iff generated _).mp
      freshMember)
  · exact (tuplePattern_mem_unificationVars_iff generated _).mpr endpoints.2

private def supportedTuplePattern
    {start next : Supply} {left right : GeneratedPatterns}
    (certificate : SupportedItemsAlignmentCertificate start next
      (patternsAsGeneratedItems left) (patternsAsGeneratedItems right)) :
    SupportedEntailedAlignmentCertificate start next
      (patternAsGenerated (tuplePatternResult left))
      (patternAsGenerated (tuplePatternResult right)) := by
  let base := certificate.itemsTuple
  apply repackageCertificate base
  · exact scopedBy_tuplePattern base.leftScoped
  · exact scopedBy_tuplePattern base.rightScoped
  · have aligned := base.aligned
    change EntailedGeneratedAlignment
      (FreshAliasSequence.addAll certificate.leftAliases
        (GeneratedItems.asTuple (patternsAsGeneratedItems left)))
      (FreshAliasSequence.addAll certificate.rightAliases
        (GeneratedItems.asTuple (patternsAsGeneratedItems right))) at aligned
    change EntailedGeneratedAlignment
      (FreshAliasSequence.addAll certificate.leftAliases
        (patternAsGenerated (tuplePatternResult left)))
      (FreshAliasSequence.addAll certificate.rightAliases
        (patternAsGenerated (tuplePatternResult right)))
    have leftHard :
        (FreshAliasSequence.addAll certificate.leftAliases
          (patternAsGenerated (tuplePatternResult left))).hard =
        (FreshAliasSequence.addAll certificate.leftAliases
          (GeneratedItems.asTuple
            (patternsAsGeneratedItems left))).hard :=
      addAll_hard_eq_of_hard_eq _ rfl
    have rightHard :
        (FreshAliasSequence.addAll certificate.rightAliases
          (patternAsGenerated (tuplePatternResult right))).hard =
        (FreshAliasSequence.addAll certificate.rightAliases
          (GeneratedItems.asTuple
            (patternsAsGeneratedItems right))).hard :=
      addAll_hard_eq_of_hard_eq _ rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [leftHard, rightHard]
      exact aligned.hardEquivalent
    · intro substitution solved
      have baseSolved : Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases
            (GeneratedItems.asTuple
              (patternsAsGeneratedItems left))).hard := by
        exact Eq.mp (congrArg (Solves substitution) leftHard) solved
      have targetEquality := aligned.targetEntailed substitution baseSolved
      have productEquality :
          (Ty.prod (left.duals.map encodedPatternDual)).apply substitution =
            (Ty.prod (right.duals.map encodedPatternDual)).apply substitution := by
        simpa only [FreshAliasSequence.addAll_target,
          patternsAsGeneratedItems, GeneratedItems.asTuple] using
          targetEquality
      have listEquality : Ty.applyList substitution
          (left.duals.map encodedPatternDual) =
          Ty.applyList substitution (right.duals.map encodedPatternDual) := by
        simpa only [Ty.apply, Ty.prod.injEq] using productEquality
      simpa only [FreshAliasSequence.addAll_target, patternAsGenerated,
        tuplePatternResult] using
        encodedDualList_result listEquality
    · simpa only [FreshAliasSequence.addAll_pending,
        patternAsGenerated, tuplePatternResult, patternsAsGeneratedItems,
        GeneratedItems.asTuple] using
        entailedPendingEq_weaken aligned.pendingAligned (by
          intro substitution solved
          exact Eq.mp (congrArg (Solves substitution) leftHard) solved)

private theorem freshIntervals_disjoint
    {firstStart middle finish : Supply}
    {firstHidden secondHidden : List UnificationVar}
    (firstFresh : VariablesFreshIn firstStart middle firstHidden)
    (secondFresh : VariablesFreshIn middle finish secondHidden) :
    ∀ candidate, candidate ∈ firstHidden → candidate ∉ secondHidden := by
  intro candidate firstMember secondMember
  have firstRange := firstFresh candidate firstMember
  have secondRange := secondFresh candidate secondMember
  cases candidate <;>
    simp only [UnificationVar.FreshIn] at firstRange secondRange <;> omega

private theorem patternAsGenerated_support
    {context : Context} {start finish : Supply}
    {generated : GeneratedPattern}
    (support : GeneratedPatternSupportProvenance context start finish generated) :
    GeneratedSupportProvenance context start finish
      (patternAsGenerated generated) := by
  intro candidate member
  apply support candidate
  cases candidate with
  | cap index =>
      simp [patternAsGenerated, encodedPatternDual,
        Generated.unificationVars, GeneratedPattern.unificationVars,
        dualVariables, Ty.unificationVars] at member ⊢
      rcases member with capability | impossible | target | hard | pending
      · exact Or.inl capability
      · contradiction
      · exact Or.inr (Or.inl target)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hard)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr pending)))
  | ty index =>
      simp [patternAsGenerated, encodedPatternDual,
        Generated.unificationVars, GeneratedPattern.unificationVars,
        dualVariables, Ty.unificationVars] at member ⊢
      rcases member with impossible | target | hard | pending
      · contradiction
      · exact Or.inl target
      · exact Or.inr (Or.inr (Or.inl hard))
      · exact Or.inr (Or.inr (Or.inr pending))

private theorem capOccurs_dualLists_iff
    (index : CapVar) (duals : List Dual) :
    Cap.occursList index (Dual.capabilities duals) = true ∨
        Ty.occursCapList index (Dual.targets duals) = true ↔
      ∃ dual, dual ∈ duals ∧
        (Cap.occurs index dual.capability = true ∨
          Ty.occursCap index dual.target = true) := by
  induction duals with
  | nil => simp [Dual.capabilities, Dual.targets, Cap.occursList,
      Ty.occursCapList]
  | cons dual duals induction =>
      change
        (Cap.occurs index dual.capability ||
            Cap.occursList index (Dual.capabilities duals)) = true ∨
          (Ty.occursCap index dual.target ||
            Ty.occursCapList index (Dual.targets duals)) = true ↔ _
      simp only [Bool.or_eq_true]
      constructor
      · rintro ((headCapability | tailCapability) |
          headTarget | tailTarget)
        · exact ⟨dual, by simp, Or.inl headCapability⟩
        · obtain ⟨found, member, occurs⟩ :=
            induction.mp (Or.inl tailCapability)
          exact ⟨found, by simp [member], occurs⟩
        · exact ⟨dual, by simp, Or.inr headTarget⟩
        · obtain ⟨found, member, occurs⟩ :=
            induction.mp (Or.inr tailTarget)
          exact ⟨found, by simp [member], occurs⟩
      · rintro ⟨found, member, occurs⟩
        simp only [List.mem_cons] at member
        rcases member with equality | member
        · subst found
          rcases occurs with capability | target
          · exact Or.inl (Or.inl capability)
          · exact Or.inr (Or.inl target)
        · rcases induction.mpr ⟨found, member, occurs⟩ with
            capability | target
          · exact Or.inl (Or.inr capability)
          · exact Or.inr (Or.inr target)

private theorem tyOccurs_dualTargets_iff
    (index : TyVar) (duals : List Dual) :
    Ty.occursTyList index (Dual.targets duals) = true ↔
      ∃ dual, dual ∈ duals ∧ Ty.occursTy index dual.target = true := by
  induction duals with
  | nil => simp [Dual.targets, Ty.occursTyList]
  | cons dual duals induction =>
      change
        (Ty.occursTy index dual.target ||
          Ty.occursTyList index (Dual.targets duals)) = true ↔ _
      simp only [Bool.or_eq_true]
      constructor
      · rintro (head | tail)
        · exact ⟨dual, by simp, head⟩
        · obtain ⟨found, member, occurs⟩ := induction.mp tail
          exact ⟨found, by simp [member], occurs⟩
      · rintro ⟨found, member, occurs⟩
        simp only [List.mem_cons] at member
        rcases member with equality | member
        · subst found
          exact Or.inl occurs
        · exact Or.inr (induction.mpr ⟨found, member, occurs⟩)

private theorem patternsAsGeneratedItems_support
    {context : Context} {start finish : Supply}
    {generated : GeneratedPatterns}
    (support : GeneratedPatternsSupportProvenance context start finish generated) :
    GeneratedItemsSupportProvenance context start finish
      (patternsAsGeneratedItems generated) := by
  intro candidate member
  apply support candidate
  cases candidate with
  | cap index =>
      simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
        GeneratedPatterns.unificationVars, dualUnificationVars,
        dualVariables, occursCapList_encodedPatternDual,
        capOccurs_dualLists_iff] at member ⊢
      rcases member with dual | hard | pending
      · exact Or.inl dual
      · exact Or.inr (Or.inr (Or.inl hard))
      · exact Or.inr (Or.inr (Or.inr pending))
  | ty index =>
      simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
        GeneratedPatterns.unificationVars, dualUnificationVars,
        dualVariables, occursTyList_encodedPatternDual,
        tyOccurs_dualTargets_iff] at member ⊢
      rcases member with dual | hard | pending
      · exact Or.inl dual
      · exact Or.inr (Or.inr (Or.inl hard))
      · exact Or.inr (Or.inr (Or.inr pending))

/-- Every forbidden variable lies strictly below the current allocation
boundary in its own sort. -/
def VariablesBelowSupply
    (forbidden : List UnificationVar) (boundary : Supply) : Prop :=
  ∀ candidate, candidate ∈ forbidden →
    candidate.Below boundary.ty boundary.cap

namespace VariablesBelowSupply

theorem mono {forbidden : List UnificationVar} {earlier later : Supply}
    (below : VariablesBelowSupply forbidden earlier)
    (increases : earlier.Le later) :
    VariablesBelowSupply forbidden later := by
  intro candidate member
  have bound := below candidate member
  cases candidate <;>
    simp only [UnificationVar.Below, Supply.Le] at bound increases ⊢ <;>
    omega

end VariablesBelowSupply

private theorem freshIn_to_belowFinish
    {start finish : Supply} {variables : List UnificationVar}
    (fresh : VariablesFreshIn start finish variables) :
    VariablesBelowSupply variables finish := by
  intro candidate member
  have range := fresh candidate member
  cases candidate <;>
    simp only [UnificationVar.FreshIn, UnificationVar.Below] at range ⊢ <;>
    exact range.2

private theorem support_avoids_laterFresh
    {context : Context} {outerStart middle finish : Supply}
    {observed hidden : List UnificationVar}
    (contextWellFormed : outerStart.WellFormedFor context)
    (outerToMiddle : outerStart.Le middle)
    (support : VariablesSupportProvenance context outerStart middle observed)
    (hiddenFresh : VariablesFreshIn middle finish hidden) :
    VariablesAvoid hidden observed := by
  intro candidate observedMember hiddenMember
  rcases support candidate observedMember with contextMember | allocated
  · have contextBound := Context.member_unificationVars_below_initialSupply
      contextMember
    have hiddenRange := hiddenFresh candidate hiddenMember
    cases candidate <;>
      simp only [UnificationVar.Below, UnificationVar.FreshIn,
        Supply.WellFormedFor, Supply.Le]
        at contextBound hiddenRange contextWellFormed outerToMiddle <;> omega
  · have hiddenRange := hiddenFresh candidate hiddenMember
    cases candidate <;>
      simp only [UnificationVar.FreshIn] at allocated hiddenRange <;> omega

private theorem freshObserved_avoids_belowForbidden
    {forbidden observed : List UnificationVar} {start finish : Supply}
    (below : VariablesBelowSupply forbidden start)
    (fresh : VariablesFreshIn start finish observed) :
    VariablesAvoid forbidden observed := by
  intro candidate observedMember forbiddenMember
  have lower := fresh candidate observedMember
  have upper := below candidate forbiddenMember
  cases candidate <;>
    simp only [UnificationVar.FreshIn, UnificationVar.Below] at lower upper <;>
    omega

private theorem extendedContext_avoids
    {context : Context} {bindings : List Ty}
    {forbidden : List UnificationVar}
    (contextAvoids : VariablesAvoid forbidden context.unificationVars)
    (bindingsAvoid : VariablesAvoid forbidden
      (Ty.unificationVarsList bindings)) :
    VariablesAvoid forbidden
      (Pattern.extendContext bindings context).unificationVars := by
  induction bindings with
  | nil => simpa [Pattern.extendContext] using contextAvoids
  | cons binding bindings induction =>
      intro candidate member forbiddenMember
      have origin := Context.mono_cons_unificationVars_origin
        (bindings.map Scheme.mono ++ context) binding member
      rcases origin with bindingMember | tailMember
      · exact bindingsAvoid candidate (by
          simpa [Ty.unificationVarsList] using Or.inl bindingMember)
          forbiddenMember
      · apply induction
        · intro item itemMember hidden
          exact bindingsAvoid item (by
            simpa [Ty.unificationVarsList] using Or.inr itemMember) hidden
        · exact tailMember
        · exact forbiddenMember

/-- Avoidance information retained by one generated user pattern. -/
structure GeneratedPatternAvoidance
    (forbidden : List UnificationVar) (generated : GeneratedPattern) : Prop where
  block : GeneratedAvoids forbidden (patternAsGenerated generated)
  bindings : VariablesAvoid forbidden
    (Ty.unificationVarsList generated.bindings)

/-- Avoidance information retained by a generated user-pattern list. -/
structure GeneratedPatternsAvoidance
    (forbidden : List UnificationVar) (generated : GeneratedPatterns) : Prop where
  block : GeneratedItemsAvoid forbidden (patternsAsGeneratedItems generated)
  bindings : VariablesAvoid forbidden
    (Ty.unificationVarsList generated.bindings)

private theorem generatedAvoids_of_support
    {context : Context} {start finish : Supply} {generated : Generated}
    {forbidden : List UnificationVar}
    (contextAvoids : VariablesAvoid forbidden context.unificationVars)
    (below : VariablesBelowSupply forbidden start)
    (support : GeneratedSupportProvenance context start finish generated) :
    GeneratedAvoids forbidden generated := by
  intro candidate member forbiddenMember
  rcases support candidate member with contextMember | fresh
  · exact contextAvoids candidate contextMember forbiddenMember
  · have upper := below candidate forbiddenMember
    cases candidate <;>
      simp only [UnificationVar.FreshIn, UnificationVar.Below]
        at fresh upper <;> omega

private theorem variablesAvoid_of_support
    {context : Context} {start finish : Supply}
    {observed forbidden : List UnificationVar}
    (contextAvoids : VariablesAvoid forbidden context.unificationVars)
    (below : VariablesBelowSupply forbidden start)
    (support : VariablesSupportProvenance context start finish observed) :
    VariablesAvoid forbidden observed := by
  intro candidate member forbiddenMember
  rcases support candidate member with contextMember | fresh
  · exact contextAvoids candidate contextMember forbiddenMember
  · have upper := below candidate forbiddenMember
    cases candidate <;>
      simp only [UnificationVar.FreshIn, UnificationVar.Below]
        at fresh upper <;> omega

private theorem fieldEquations_avoid
    {forbidden : List UnificationVar} {actual expected : List Dual}
    (actualAvoids : VariablesAvoid forbidden (dualUnificationVars actual))
    (expectedAvoids : VariablesAvoid forbidden (dualUnificationVars expected)) :
    VariablesAvoid forbidden
      (TypePM.unificationVars (Pattern.fieldEquations actual expected)) := by
  induction actual generalizing expected with
  | nil => simp [VariablesAvoid, Pattern.fieldEquations, TypePM.unificationVars]
  | cons actual actuals induction =>
      cases expected with
      | nil => simp [VariablesAvoid, Pattern.fieldEquations, TypePM.unificationVars]
      | cons expected expecteds =>
          intro candidate member forbiddenMember
          have origin :
              candidate ∈ actual.target.unificationVars ∨
              candidate ∈ expected.target.unificationVars ∨
              candidate ∈ actual.capability.unificationVars ∨
              candidate ∈ expected.capability.unificationVars ∨
              candidate ∈ TypePM.unificationVars
                (Pattern.fieldEquations actuals expecteds) := by
            simpa [Pattern.fieldEquations, TypePM.unificationVars,
              Equation.unificationVars, dualVariables] using member
          rcases origin with actualTarget | expectedTarget | actualCapability |
              expectedCapability | tailMember
          · exact actualAvoids candidate (by
              simp [dualUnificationVars, dualVariables, actualTarget])
              forbiddenMember
          · exact expectedAvoids candidate (by
              simp [dualUnificationVars, dualVariables, expectedTarget])
              forbiddenMember
          · exact actualAvoids candidate (by
              simp [dualUnificationVars, dualVariables, actualCapability])
              forbiddenMember
          · exact expectedAvoids candidate (by
              simp [dualUnificationVars, dualVariables, expectedCapability])
              forbiddenMember
          · apply induction
              (fun item itemMember hidden => actualAvoids item (by
                simp only [dualUnificationVars, List.flatMap_cons,
                  List.mem_append]
                exact Or.inr itemMember) hidden)
              (fun item itemMember hidden => expectedAvoids item (by
                simp only [dualUnificationVars, List.flatMap_cons,
                  List.mem_append]
                exact Or.inr itemMember) hidden)
              candidate tailMember forbiddenMember

private theorem dualEquations_avoid
    {forbidden : List UnificationVar} {left right : Dual}
    (leftAvoids : VariablesAvoid forbidden (dualVariables left))
    (rightAvoids : VariablesAvoid forbidden (dualVariables right)) :
    VariablesAvoid forbidden
      (TypePM.unificationVars (Pattern.dualEquations left right)) := by
  intro candidate member forbiddenMember
  simp [Pattern.dualEquations, TypePM.unificationVars,
    Equation.unificationVars] at member
  rcases member with leftTarget | rightTarget | leftCapability | rightCapability
  · exact leftAvoids candidate (by simp [dualVariables, leftTarget])
      forbiddenMember
  · exact rightAvoids candidate (by simp [dualVariables, rightTarget])
      forbiddenMember
  · exact leftAvoids candidate (by simp [dualVariables, leftCapability])
      forbiddenMember
  · exact rightAvoids candidate (by simp [dualVariables, rightCapability])
      forbiddenMember

private theorem bindingEquations_avoid
    {forbidden : List UnificationVar} {left right : List Ty}
    {checks : List Equation}
    (leftAvoids : VariablesAvoid forbidden (Ty.unificationVarsList left))
    (rightAvoids : VariablesAvoid forbidden (Ty.unificationVarsList right))
    (computed : Pattern.bindingEquations left right = some checks) :
    VariablesAvoid forbidden (TypePM.unificationVars checks) := by
  induction left generalizing right checks with
  | nil =>
      cases right <;> simp [Pattern.bindingEquations] at computed
      cases computed
      simp [VariablesAvoid, TypePM.unificationVars]
  | cons left lefts induction =>
      cases right with
      | nil => simp [Pattern.bindingEquations] at computed
      | cons right rights =>
          simp only [Pattern.bindingEquations] at computed
          cases tailResult : Pattern.bindingEquations lefts rights with
          | none => simp [tailResult] at computed
          | some tail =>
            simp [tailResult] at computed
            subst checks
            intro candidate member forbiddenMember
            simp only [TypePM.unificationVars, Equation.unificationVars,
              List.mem_append] at member
            rcases member with headMember | tailMember
            · rcases headMember with leftMember | rightMember
              · exact leftAvoids candidate (by
                  simp [Ty.unificationVarsList, leftMember]) forbiddenMember
              · exact rightAvoids candidate (by
                  simp [Ty.unificationVarsList, rightMember]) forbiddenMember
            · exact induction
                (fun item itemMember hidden => leftAvoids item (by
                  simp [Ty.unificationVarsList, itemMember]) hidden)
                (fun item itemMember hidden => rightAvoids item (by
                  simp [Ty.unificationVarsList, itemMember]) hidden)
                tailResult candidate tailMember forbiddenMember

private theorem generated_target_avoids
    {forbidden : List UnificationVar} {generated : Generated}
    (avoids : GeneratedAvoids forbidden generated) :
    TypeAvoids forbidden generated.target := by
  intro candidate member hidden
  exact avoids candidate (by
    simp [Generated.unificationVars, member]) hidden

private theorem generated_hard_avoids
    {forbidden : List UnificationVar} {generated : Generated}
    (avoids : GeneratedAvoids forbidden generated) :
    EquationsAvoid forbidden generated.hard := by
  intro candidate member hidden
  exact avoids candidate (by
    simp [Generated.unificationVars, member]) hidden

private theorem generated_pending_avoids
    {forbidden : List UnificationVar} {generated : Generated}
    (avoids : GeneratedAvoids forbidden generated) :
    VariablesAvoid forbidden (pendingUnificationVars generated.pending) := by
  intro candidate member hidden
  exact avoids candidate (by
    simp [Generated.unificationVars, member]) hidden

private theorem items_duals_avoid
    {forbidden : List UnificationVar} {generated : GeneratedPatterns}
    (avoids : GeneratedItemsAvoid forbidden
      (patternsAsGeneratedItems generated)) :
    VariablesAvoid forbidden (dualUnificationVars generated.duals) := by
  intro candidate member hidden
  apply avoids candidate _ hidden
  cases candidate with
  | cap index =>
      simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
        dualUnificationVars, dualVariables, occursCapList_encodedPatternDual,
        capOccurs_dualLists_iff] at member ⊢
      exact Or.inl member
  | ty index =>
      simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
        dualUnificationVars, dualVariables, occursTyList_encodedPatternDual,
        tyOccurs_dualTargets_iff] at member ⊢
      exact Or.inl member

private theorem items_hard_avoid
    {forbidden : List UnificationVar} {generated : GeneratedPatterns}
    (avoids : GeneratedItemsAvoid forbidden
      (patternsAsGeneratedItems generated)) :
    EquationsAvoid forbidden generated.hard := by
  intro candidate member hidden
  exact avoids candidate (by
    simp [patternsAsGeneratedItems, GeneratedItems.unificationVars, member]) hidden

private theorem items_pending_avoid
    {forbidden : List UnificationVar} {generated : GeneratedPatterns}
    (avoids : GeneratedItemsAvoid forbidden
      (patternsAsGeneratedItems generated)) :
    VariablesAvoid forbidden (pendingUnificationVars generated.pending) := by
  intro candidate member hidden
  exact avoids candidate (by
    simp [patternsAsGeneratedItems, GeneratedItems.unificationVars, member]) hidden

private theorem patternBlock_avoid
    {forbidden : List UnificationVar} {generated : GeneratedPattern}
    (dualAvoids : VariablesAvoid forbidden (dualVariables generated.dual))
    (hardAvoids : EquationsAvoid forbidden generated.hard)
    (pendingAvoids : VariablesAvoid forbidden
      (pendingUnificationVars generated.pending)) :
    GeneratedAvoids forbidden (patternAsGenerated generated) := by
  intro candidate member hidden
  cases candidate with
  | cap index =>
      simp [patternAsGenerated, encodedPatternDual,
        Generated.unificationVars, Ty.unificationVars]
        at member
      rcases member with capability | impossible | target | hard | pending
      · exact dualAvoids _ (by simp [dualVariables, capability]) hidden
      · contradiction
      · exact dualAvoids _ (by simp [dualVariables, target]) hidden
      · exact hardAvoids _ hard hidden
      · exact pendingAvoids _ pending hidden
  | ty index =>
      simp [patternAsGenerated, encodedPatternDual,
        Generated.unificationVars, Ty.unificationVars]
        at member
      rcases member with impossible | target | hard | pending
      · contradiction
      · exact dualAvoids _ (by simp [dualVariables, target]) hidden
      · exact hardAvoids _ hard hidden
      · exact pendingAvoids _ pending hidden

private theorem patternsBlock_avoid
    {forbidden : List UnificationVar} {generated : GeneratedPatterns}
    (dualsAvoid : VariablesAvoid forbidden
      (dualUnificationVars generated.duals))
    (hardAvoid : EquationsAvoid forbidden generated.hard)
    (pendingAvoid : VariablesAvoid forbidden
      (pendingUnificationVars generated.pending)) :
    GeneratedItemsAvoid forbidden (patternsAsGeneratedItems generated) := by
  intro candidate member hidden
  cases candidate with
  | cap index =>
      simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
        occursCapList_encodedPatternDual, capOccurs_dualLists_iff] at member
      rcases member with dual | hard | pending
      · exact dualsAvoid _ (by
          simpa [dualUnificationVars, dualVariables,
            capOccurs_dualLists_iff] using dual) hidden
      · exact hardAvoid _ hard hidden
      · exact pendingAvoid _ pending hidden
  | ty index =>
      simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
        occursTyList_encodedPatternDual, tyOccurs_dualTargets_iff] at member
      rcases member with dual | hard | pending
      · exact dualsAvoid _ (by
          simpa [dualUnificationVars, dualVariables,
            tyOccurs_dualTargets_iff] using dual) hidden
      · exact hardAvoid _ hard hidden
      · exact pendingAvoid _ pending hidden

private theorem pattern_dual_avoid
    {forbidden : List UnificationVar} {generated : GeneratedPattern}
    (avoids : GeneratedAvoids forbidden (patternAsGenerated generated)) :
    VariablesAvoid forbidden (dualVariables generated.dual) := by
  intro candidate member hidden
  apply avoids candidate _ hidden
  cases candidate with
  | cap index =>
      simp [patternAsGenerated, encodedPatternDual,
        Generated.unificationVars, dualVariables, Ty.unificationVars]
        at member ⊢
      rcases member with capability | target
      · exact Or.inl capability
      · exact Or.inr (Or.inr (Or.inl target))
  | ty index =>
      simp [patternAsGenerated, encodedPatternDual,
        Generated.unificationVars, dualVariables, Ty.unificationVars]
        at member ⊢
      exact Or.inr (Or.inl member)

private theorem equationsAvoid_append
    {forbidden : List UnificationVar} {left right : List Equation}
    (leftAvoids : EquationsAvoid forbidden left)
    (rightAvoids : EquationsAvoid forbidden right) :
    EquationsAvoid forbidden (left ++ right) := by
  intro candidate member hidden
  simp only [unificationVars_append, List.mem_append] at member
  rcases member with member | member
  · exact leftAvoids candidate member hidden
  · exact rightAvoids candidate member hidden

private theorem pendingAvoid_append
    {forbidden : List UnificationVar}
    {left right : List CheckObligation}
    (leftAvoids : VariablesAvoid forbidden (pendingUnificationVars left))
    (rightAvoids : VariablesAvoid forbidden (pendingUnificationVars right)) :
    VariablesAvoid forbidden (pendingUnificationVars (left ++ right)) := by
  intro candidate member hidden
  simp only [pendingUnificationVars_append, List.mem_append] at member
  rcases member with member | member
  · exact leftAvoids candidate member hidden
  · exact rightAvoids candidate member hidden

private theorem solves_fieldEquations_iff
    (substitution : Subst) {actual expected : List Dual}
    (arity : actual.length = expected.length) :
    Solves substitution (Pattern.fieldEquations actual expected) ↔
      Cap.applyList substitution.cap (Dual.capabilities actual) =
          Cap.applyList substitution.cap (Dual.capabilities expected) ∧
        Ty.applyList substitution (Dual.targets actual) =
          Ty.applyList substitution (Dual.targets expected) := by
  induction actual generalizing expected with
  | nil =>
      cases expected <;> simp [Pattern.fieldEquations] at arity ⊢
  | cons actualHead actualTail induction =>
      cases expected with
      | nil => simp at arity
      | cons expectedHead expectedTail =>
          simp only [List.length_cons, Nat.succ.injEq] at arity
          have fieldsCons : Pattern.fieldEquations
              (actualHead :: actualTail) (expectedHead :: expectedTail) =
              [.ty actualHead.target expectedHead.target,
                .cap actualHead.capability expectedHead.capability] ++
                Pattern.fieldEquations actualTail expectedTail := rfl
          rw [fieldsCons, solves_append, induction arity]
          simp only [solves_cons, solves_nil, and_true, Equation.Holds,
            Dual.capabilities, Dual.targets]
          constructor
          · rintro ⟨⟨targetHead, capabilityHead⟩, tail⟩
            constructor
            · simp only [List.map_cons, Cap.applyList]
              rw [capabilityHead, tail.1]
            · simp only [List.map_cons, Ty.applyList]
              rw [targetHead, tail.2]
          · rintro ⟨capabilities, targets⟩
            have capabilityParts := List.cons.inj capabilities
            have targetParts := List.cons.inj targets
            exact ⟨⟨targetParts.1, capabilityParts.1⟩,
              capabilityParts.2, targetParts.2⟩

private theorem solves_dualEquations_iff
    (substitution : Subst) (left right : Dual) :
    Solves substitution (Pattern.dualEquations left right) ↔
      left.target.apply substitution = right.target.apply substitution ∧
        left.capability.apply substitution.cap =
          right.capability.apply substitution.cap := by
  simp [Pattern.dualEquations, Equation.Holds]

private theorem solves_bindingEquations_iff
    (substitution : Subst) {left right : List Ty} {checks : List Equation}
    (computed : Pattern.bindingEquations left right = some checks) :
    Solves substitution checks ↔
      Ty.applyList substitution left = Ty.applyList substitution right := by
  induction left generalizing right checks with
  | nil =>
      cases right <;> simp [Pattern.bindingEquations] at computed ⊢
      cases computed
      simp
  | cons leftHead leftTail induction =>
      cases right with
      | nil => simp [Pattern.bindingEquations] at computed
      | cons rightHead rightTail =>
          simp only [Pattern.bindingEquations] at computed
          cases tailComputed : Pattern.bindingEquations leftTail rightTail with
          | none => simp [tailComputed] at computed
          | some tailChecks =>
              simp [tailComputed] at computed
              subst checks
              simp [Ty.applyList, Equation.Holds, induction tailComputed]

private theorem fieldEquations_actual_subset
    {actual expected : List Dual}
    (arity : actual.length = expected.length) :
    ∀ candidate, candidate ∈ dualUnificationVars actual →
      candidate ∈ TypePM.unificationVars
        (Pattern.fieldEquations actual expected) := by
  induction actual generalizing expected with
  | nil =>
      intro candidate member
      simp [dualUnificationVars] at member
  | cons actualHead actualTail induction =>
      cases expected with
      | nil => simp at arity
      | cons expectedHead expectedTail =>
          simp only [List.length_cons, Nat.succ.injEq] at arity
          intro candidate member
          simp only [dualUnificationVars, List.flatMap_cons, List.mem_append]
            at member
          rcases member with headMember | tailMember
          · cases candidate with
            | cap index =>
                simp [dualVariables, Pattern.fieldEquations,
                  TypePM.unificationVars, Equation.unificationVars]
                  at headMember ⊢
                rcases headMember with capability | target
                · exact Or.inr (Or.inr (Or.inl capability))
                · exact Or.inl target
            | ty index =>
                simp [dualVariables, Pattern.fieldEquations,
                  TypePM.unificationVars, Equation.unificationVars]
                  at headMember ⊢
                exact Or.inl headMember
          · have tailFound := induction arity candidate tailMember
            simp [Pattern.fieldEquations, TypePM.unificationVars,
              Equation.unificationVars]
            exact Or.inr (Or.inr (Or.inr (Or.inr tailFound)))

private def fieldPatternResult (result : Dual) (expected : List Dual)
    (generated : GeneratedPatterns) : GeneratedPattern :=
  { dual := result
    bindings := generated.bindings
    hard := generated.hard ++
      Pattern.fieldEquations generated.duals expected
    pending := generated.pending }

private theorem fieldPattern_base_subset
    (result : Dual) {expected : List Dual} (generated : GeneratedPatterns)
    (arity : generated.duals.length = expected.length) :
    ∀ candidate,
      candidate ∈ (patternsAsGeneratedItems generated).unificationVars →
      candidate ∈
        (patternAsGenerated
          (fieldPatternResult result expected generated)).unificationVars := by
  intro candidate member
  cases candidate with
  | cap index =>
      simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
        occursCapList_encodedPatternDual, capOccurs_dualLists_iff,
        patternAsGenerated, fieldPatternResult, encodedPatternDual,
        Generated.unificationVars, Ty.unificationVars] at member ⊢
      rcases member with dualMember | hardMember | pendingMember
      · have found := fieldEquations_actual_subset arity (.cap index) (by
          simpa [dualUnificationVars, dualVariables,
            capOccurs_dualLists_iff] using dualMember)
        simp_all
      · simp_all
      · simp_all
  | ty index =>
      simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
        occursTyList_encodedPatternDual, tyOccurs_dualTargets_iff,
        patternAsGenerated, fieldPatternResult, encodedPatternDual,
        Generated.unificationVars, Ty.unificationVars] at member ⊢
      rcases member with dualMember | hardMember | pendingMember
      · have found := fieldEquations_actual_subset arity (.ty index) (by
          simpa [dualUnificationVars, dualVariables,
            tyOccurs_dualTargets_iff] using dualMember)
        simp_all
      · simp_all
      · simp_all

private theorem scopedBy_fieldPattern
    {aliases : List FreshAliasSequence.Alias}
    {hidden : List UnificationVar} (result : Dual) {expected : List Dual}
    (generated : GeneratedPatterns)
    (scope : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
      (patternsAsGeneratedItems generated).unificationVars aliases)
    (aliasFresh : ∀ alias, alias ∈ aliases →
      InterfaceAliasDecomposition.AliasFreshness.freshVariable alias ∈
        hidden)
    (resultAvoids : VariablesAvoid hidden (dualVariables result))
    (expectedAvoids : VariablesAvoid hidden
      (dualUnificationVars expected))
    (arity : generated.duals.length = expected.length) :
    InterfaceAliasDecomposition.AliasFreshness.ScopedBy
      (patternAsGenerated
        (fieldPatternResult result expected generated)).unificationVars
      aliases := by
  refine ⟨scope.1, ?_⟩
  intro alias aliasMember
  have endpoints := scope.2 alias aliasMember
  constructor
  · intro freshMember
    let fresh :=
      InterfaceAliasDecomposition.AliasFreshness.freshVariable alias
    have baseAvoid : GeneratedItemsAvoid [fresh]
        (patternsAsGeneratedItems generated) := by
      intro candidate member forbidden
      have equality : candidate = fresh := by simpa using forbidden
      subst candidate
      exact endpoints.1 member
    have actualAvoid := items_duals_avoid baseAvoid
    have hardAvoid := items_hard_avoid baseAvoid
    have pendingAvoid := items_pending_avoid baseAvoid
    have resultAvoid : VariablesAvoid [fresh] (dualVariables result) := by
      intro candidate member forbidden
      have equality : candidate = fresh := by simpa using forbidden
      subst candidate
      exact resultAvoids fresh member (aliasFresh alias aliasMember)
    have expectedAvoid : VariablesAvoid [fresh]
        (dualUnificationVars expected) := by
      intro candidate member forbidden
      have equality : candidate = fresh := by simpa using forbidden
      subst candidate
      exact expectedAvoids fresh member (aliasFresh alias aliasMember)
    have outputAvoid : GeneratedAvoids [fresh]
        (patternAsGenerated
          (fieldPatternResult result expected generated)) :=
      patternBlock_avoid resultAvoid
        (equationsAvoid_append hardAvoid
          (fieldEquations_avoid actualAvoid expectedAvoid)) pendingAvoid
    exact outputAvoid fresh freshMember (by simp [fresh])
  · exact fieldPattern_base_subset result generated arity _ endpoints.2

private def supportedFieldPattern
    {start next : Supply} {left right : GeneratedPatterns}
    (result : Dual) (expected : List Dual)
    (leftArity : left.duals.length = expected.length)
    (rightArity : right.duals.length = expected.length)
    (certificate : SupportedItemsAlignmentCertificate start next
      (patternsAsGeneratedItems left) (patternsAsGeneratedItems right))
    (resultAvoids : VariablesAvoid certificate.hidden
      (dualVariables result))
    (expectedAvoids : VariablesAvoid certificate.hidden
      (dualUnificationVars expected)) :
    SupportedEntailedAlignmentCertificate start next
      (patternAsGenerated (fieldPatternResult result expected left))
      (patternAsGenerated (fieldPatternResult result expected right)) := by
  let base := certificate.itemsTuple
  apply repackageCertificate base
  · exact scopedBy_fieldPattern result left base.leftScoped
      base.leftAliasFresh resultAvoids expectedAvoids leftArity
  · exact scopedBy_fieldPattern result right base.rightScoped
      base.rightAliasFresh resultAvoids expectedAvoids rightArity
  · have aligned := base.aligned
    change EntailedGeneratedAlignment
      (FreshAliasSequence.addAll certificate.leftAliases
        (GeneratedItems.asTuple (patternsAsGeneratedItems left)))
      (FreshAliasSequence.addAll certificate.rightAliases
        (GeneratedItems.asTuple (patternsAsGeneratedItems right))) at aligned
    let leftOutput := patternAsGenerated
      (fieldPatternResult result expected left)
    let rightOutput := patternAsGenerated
      (fieldPatternResult result expected right)
    have leftHard :
        (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard =
          (FreshAliasSequence.addAll certificate.leftAliases
            (GeneratedItems.asTuple
              (patternsAsGeneratedItems left))).hard ++
            Pattern.fieldEquations left.duals expected := by
      simp [leftOutput, fieldPatternResult, patternAsGenerated,
        patternsAsGeneratedItems, GeneratedItems.asTuple,
        InterfaceAliasDecomposition.EquationLists.addAll_hard,
        InterfaceAliasDecomposition.EquationLists.addAliases_append]
    have rightHard :
        (FreshAliasSequence.addAll certificate.rightAliases rightOutput).hard =
          (FreshAliasSequence.addAll certificate.rightAliases
            (GeneratedItems.asTuple
              (patternsAsGeneratedItems right))).hard ++
            Pattern.fieldEquations right.duals expected := by
      simp [rightOutput, fieldPatternResult, patternAsGenerated,
        patternsAsGeneratedItems, GeneratedItems.asTuple,
        InterfaceAliasDecomposition.EquationLists.addAll_hard,
        InterfaceAliasDecomposition.EquationLists.addAliases_append]
    refine ⟨?_, ?_, ?_⟩
    · change HardEquivalent
        (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard
        (FreshAliasSequence.addAll certificate.rightAliases rightOutput).hard
      rw [leftHard, rightHard]
      intro substitution
      simp only [solves_append]
      constructor
      · rintro ⟨leftBase, leftFields⟩
        have rightBase := (aligned.hardEquivalent substitution).mp leftBase
        have encodedEquality := aligned.targetEntailed substitution leftBase
        have listEquality : Ty.applyList substitution
            (left.duals.map encodedPatternDual) =
            Ty.applyList substitution
              (right.duals.map encodedPatternDual) := by
          simpa [FreshAliasSequence.addAll_target,
            patternsAsGeneratedItems, GeneratedItems.asTuple,
            Ty.apply] using encodedEquality
        obtain ⟨capabilities, targets⟩ :=
          encodedDualList_apply_components listEquality
        have leftComponents :=
          (solves_fieldEquations_iff substitution leftArity).mp leftFields
        apply And.intro rightBase
        apply (solves_fieldEquations_iff substitution rightArity).mpr
        exact ⟨capabilities.symm.trans leftComponents.1,
          targets.symm.trans leftComponents.2⟩
      · rintro ⟨rightBase, rightFields⟩
        have leftBase := (aligned.hardEquivalent substitution).mpr rightBase
        have encodedEquality := aligned.targetEntailed substitution leftBase
        have listEquality : Ty.applyList substitution
            (left.duals.map encodedPatternDual) =
            Ty.applyList substitution
              (right.duals.map encodedPatternDual) := by
          simpa [FreshAliasSequence.addAll_target,
            patternsAsGeneratedItems, GeneratedItems.asTuple,
            Ty.apply] using encodedEquality
        obtain ⟨capabilities, targets⟩ :=
          encodedDualList_apply_components listEquality
        have rightComponents :=
          (solves_fieldEquations_iff substitution rightArity).mp rightFields
        apply And.intro leftBase
        apply (solves_fieldEquations_iff substitution leftArity).mpr
        exact ⟨capabilities.trans rightComponents.1,
          targets.trans rightComponents.2⟩
    · intro substitution solved
      simp [FreshAliasSequence.addAll_target,
        fieldPatternResult, patternAsGenerated]
    · simpa [FreshAliasSequence.addAll_pending, leftOutput, rightOutput,
        fieldPatternResult, patternAsGenerated, patternsAsGeneratedItems,
        GeneratedItems.asTuple] using
        entailedPendingEq_weaken aligned.pendingAligned (by
          intro substitution solved
          exact (solves_append substitution _ _).mp
            (Eq.mp (congrArg (Solves substitution) leftHard) solved) |>.1)

private def pairPatterns (first second : GeneratedPattern) : GeneratedPatterns :=
  { duals := [first.dual, second.dual]
    bindings := second.bindings
    hard := first.hard ++ (second.hard ++ [])
    pending := first.pending ++ (second.pending ++ []) }

private def dualPairPatternResult (first second : GeneratedPattern)
    (bindings : List Ty) (checks : List Equation) : GeneratedPattern :=
  { dual := first.dual
    bindings := bindings
    hard := first.hard ++ second.hard ++
      Pattern.dualEquations first.dual second.dual ++ checks
    pending := first.pending ++ second.pending }

private theorem dualPair_base_subset
    (first second : GeneratedPattern) (bindings : List Ty)
    (checks : List Equation) :
    ∀ candidate,
      candidate ∈
          (patternsAsGeneratedItems (pairPatterns first second)).unificationVars →
        candidate ∈
          (patternAsGenerated
            (dualPairPatternResult first second bindings checks)).unificationVars := by
  intro candidate member
  cases candidate with
  | cap index =>
      simp [patternsAsGeneratedItems, pairPatterns,
        GeneratedItems.unificationVars, patternAsGenerated,
        dualPairPatternResult, encodedPatternDual,
        Generated.unificationVars, TypePM.unificationVars,
        Pattern.dualEquations, Equation.unificationVars,
        Ty.occursCapList, Ty.occursCap] at member ⊢
      rcases member with duals | firstHard | secondHard | firstPending |
          secondPending
      · rcases duals with firstDual | secondCapability | secondTarget
        · exact Or.inl firstDual
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl secondCapability))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl secondTarget))))
      · exact Or.inr (Or.inl firstHard)
      · exact Or.inr (Or.inr (Or.inl secondHard))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl firstPending))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr secondPending))))))))
  | ty index =>
      simp [patternsAsGeneratedItems, pairPatterns,
        GeneratedItems.unificationVars, patternAsGenerated,
        dualPairPatternResult, encodedPatternDual,
        Generated.unificationVars, TypePM.unificationVars,
        Pattern.dualEquations, Equation.unificationVars,
        Ty.occursTyList, Ty.occursTy] at member ⊢
      rcases member with duals | firstHard | secondHard | firstPending |
          secondPending
      · rcases duals with firstTarget | secondTarget
        · exact Or.inl firstTarget
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl secondTarget))))
      · exact Or.inr (Or.inl firstHard)
      · exact Or.inr (Or.inr (Or.inl secondHard))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl firstPending))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr secondPending))))))

private theorem scopedBy_dualPairPattern
    {aliases : List FreshAliasSequence.Alias}
    {hidden : List UnificationVar} (first second : GeneratedPattern)
    (bindings : List Ty) (checks : List Equation)
    (scope : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
      (patternsAsGeneratedItems (pairPatterns first second)).unificationVars
      aliases)
    (aliasFresh : ∀ alias, alias ∈ aliases →
      InterfaceAliasDecomposition.AliasFreshness.freshVariable alias ∈
        hidden)
    (checksAvoid : EquationsAvoid hidden checks) :
    InterfaceAliasDecomposition.AliasFreshness.ScopedBy
      (patternAsGenerated
        (dualPairPatternResult first second bindings checks)).unificationVars
      aliases := by
  refine ⟨scope.1, ?_⟩
  intro alias aliasMember
  have endpoints := scope.2 alias aliasMember
  constructor
  · intro freshMember
    let fresh :=
      InterfaceAliasDecomposition.AliasFreshness.freshVariable alias
    have baseAvoid : GeneratedItemsAvoid [fresh]
        (patternsAsGeneratedItems (pairPatterns first second)) := by
      intro candidate member forbidden
      have equality : candidate = fresh := by simpa using forbidden
      subst candidate
      exact endpoints.1 member
    have dualsAvoid := items_duals_avoid baseAvoid
    have firstDualAvoid : VariablesAvoid [fresh]
        (dualVariables first.dual) := by
      intro candidate member forbidden
      exact dualsAvoid candidate (by
        simp [pairPatterns, dualUnificationVars, member]) forbidden
    have secondDualAvoid : VariablesAvoid [fresh]
        (dualVariables second.dual) := by
      intro candidate member forbidden
      exact dualsAvoid candidate (by
        simp [pairPatterns, dualUnificationVars, member]) forbidden
    have commonChecksAvoid : EquationsAvoid [fresh] checks := by
      intro candidate member forbidden
      have equality : candidate = fresh := by simpa using forbidden
      subst candidate
      exact checksAvoid fresh member (aliasFresh alias aliasMember)
    have outputAvoid : GeneratedAvoids [fresh]
        (patternAsGenerated
          (dualPairPatternResult first second bindings checks)) :=
      patternBlock_avoid firstDualAvoid
        (equationsAvoid_append
          (equationsAvoid_append (by
              simpa [pairPatterns] using items_hard_avoid baseAvoid)
            (dualEquations_avoid firstDualAvoid secondDualAvoid))
          commonChecksAvoid)
        (by simpa [pairPatterns, dualPairPatternResult] using
          items_pending_avoid baseAvoid)
    exact outputAvoid fresh freshMember (by simp [fresh])
  · exact dualPair_base_subset first second bindings checks _ endpoints.2

private def supportedDualPairPattern
    {start next : Supply}
    {leftFirst leftSecond rightFirst rightSecond : GeneratedPattern}
    (leftBindings rightBindings : List Ty) (checks : List Equation)
    (certificate : SupportedItemsAlignmentCertificate start next
      (patternsAsGeneratedItems (pairPatterns leftFirst leftSecond))
      (patternsAsGeneratedItems (pairPatterns rightFirst rightSecond)))
    (checksAvoid : EquationsAvoid certificate.hidden checks) :
    SupportedEntailedAlignmentCertificate start next
      (patternAsGenerated
        (dualPairPatternResult leftFirst leftSecond leftBindings checks))
      (patternAsGenerated
        (dualPairPatternResult rightFirst rightSecond rightBindings checks)) := by
  let base := certificate.itemsTuple
  apply repackageCertificate base
  · exact scopedBy_dualPairPattern leftFirst leftSecond leftBindings checks
      base.leftScoped base.leftAliasFresh checksAvoid
  · exact scopedBy_dualPairPattern rightFirst rightSecond rightBindings checks
      base.rightScoped base.rightAliasFresh checksAvoid
  · have aligned := base.aligned
    change EntailedGeneratedAlignment
      (FreshAliasSequence.addAll certificate.leftAliases
        (GeneratedItems.asTuple
          (patternsAsGeneratedItems (pairPatterns leftFirst leftSecond))))
      (FreshAliasSequence.addAll certificate.rightAliases
        (GeneratedItems.asTuple
          (patternsAsGeneratedItems (pairPatterns rightFirst rightSecond))))
      at aligned
    let leftOutput := patternAsGenerated
      (dualPairPatternResult leftFirst leftSecond leftBindings checks)
    let rightOutput := patternAsGenerated
      (dualPairPatternResult rightFirst rightSecond rightBindings checks)
    have leftHard :
        (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard =
          (FreshAliasSequence.addAll certificate.leftAliases
            (GeneratedItems.asTuple (patternsAsGeneratedItems
              (pairPatterns leftFirst leftSecond)))).hard ++
            Pattern.dualEquations leftFirst.dual leftSecond.dual ++ checks := by
      simp [leftOutput, dualPairPatternResult, pairPatterns,
        patternAsGenerated, patternsAsGeneratedItems,
        GeneratedItems.asTuple,
        InterfaceAliasDecomposition.EquationLists.addAll_hard,
        InterfaceAliasDecomposition.EquationLists.addAliases_append,
        List.append_assoc]
    have rightHard :
        (FreshAliasSequence.addAll certificate.rightAliases rightOutput).hard =
          (FreshAliasSequence.addAll certificate.rightAliases
            (GeneratedItems.asTuple (patternsAsGeneratedItems
              (pairPatterns rightFirst rightSecond)))).hard ++
            Pattern.dualEquations rightFirst.dual rightSecond.dual ++ checks := by
      simp [rightOutput, dualPairPatternResult, pairPatterns,
        patternAsGenerated, patternsAsGeneratedItems,
        GeneratedItems.asTuple,
        InterfaceAliasDecomposition.EquationLists.addAll_hard,
        InterfaceAliasDecomposition.EquationLists.addAliases_append,
        List.append_assoc]
    have componentEquality (substitution : Subst)
        (leftSolved : Solves substitution
          (FreshAliasSequence.addAll certificate.leftAliases
            (GeneratedItems.asTuple (patternsAsGeneratedItems
              (pairPatterns leftFirst leftSecond)))).hard) :
        leftFirst.dual.capability.apply substitution.cap =
            rightFirst.dual.capability.apply substitution.cap ∧
          leftFirst.dual.target.apply substitution =
            rightFirst.dual.target.apply substitution ∧
          leftSecond.dual.capability.apply substitution.cap =
            rightSecond.dual.capability.apply substitution.cap ∧
          leftSecond.dual.target.apply substitution =
            rightSecond.dual.target.apply substitution := by
      have encodedEquality := aligned.targetEntailed substitution leftSolved
      have listEquality : Ty.applyList substitution
          ([leftFirst.dual, leftSecond.dual].map encodedPatternDual) =
          Ty.applyList substitution
            ([rightFirst.dual, rightSecond.dual].map encodedPatternDual) := by
        simpa [FreshAliasSequence.addAll_target, patternsAsGeneratedItems,
          pairPatterns, GeneratedItems.asTuple, Ty.apply] using encodedEquality
      have headEquality := List.cons.inj listEquality
      have tailEquality := List.cons.inj headEquality.2
      obtain ⟨firstCapability, firstTarget⟩ :=
        encodedDual_apply_components headEquality.1
      obtain ⟨secondCapability, secondTarget⟩ :=
        encodedDual_apply_components tailEquality.1
      exact ⟨firstCapability, firstTarget, secondCapability, secondTarget⟩
    refine ⟨?_, ?_, ?_⟩
    · change HardEquivalent
        (FreshAliasSequence.addAll certificate.leftAliases leftOutput).hard
        (FreshAliasSequence.addAll certificate.rightAliases rightOutput).hard
      rw [leftHard, rightHard]
      intro substitution
      simp only [solves_append]
      constructor
      · rintro ⟨⟨leftBase, leftDual⟩, common⟩
        have rightBase := (aligned.hardEquivalent substitution).mp leftBase
        obtain ⟨firstCap, firstTarget, secondCap, secondTarget⟩ :=
          componentEquality substitution leftBase
        have leftComponents :=
          (solves_dualEquations_iff substitution _ _).mp leftDual
        apply And.intro
        · apply And.intro rightBase
          apply (solves_dualEquations_iff substitution _ _).mpr
          exact ⟨firstTarget.symm.trans
              (leftComponents.1.trans secondTarget),
            firstCap.symm.trans (leftComponents.2.trans secondCap)⟩
        · exact common
      · rintro ⟨⟨rightBase, rightDual⟩, common⟩
        have leftBase := (aligned.hardEquivalent substitution).mpr rightBase
        obtain ⟨firstCap, firstTarget, secondCap, secondTarget⟩ :=
          componentEquality substitution leftBase
        have rightComponents :=
          (solves_dualEquations_iff substitution _ _).mp rightDual
        apply And.intro
        · apply And.intro leftBase
          apply (solves_dualEquations_iff substitution _ _).mpr
          exact ⟨firstTarget.trans
              (rightComponents.1.trans secondTarget.symm),
            firstCap.trans (rightComponents.2.trans secondCap.symm)⟩
        · exact common
    · intro substitution solved
      have components := componentEquality substitution
        ((solves_append substitution _ _).mp
          ((solves_append substitution _ _).mp
            (Eq.mp (congrArg (Solves substitution) leftHard) solved)).1).1
      simp [FreshAliasSequence.addAll_target,
        dualPairPatternResult, patternAsGenerated, encodedPatternDual,
        Ty.apply, components.1, components.2.1]
    · simp only [FreshAliasSequence.addAll_pending]
      change EntailedPendingEq
        (FreshAliasSequence.addAll certificate.leftAliases
          (patternAsGenerated (dualPairPatternResult leftFirst leftSecond
            leftBindings checks))).hard
        (leftFirst.pending ++ leftSecond.pending)
        (rightFirst.pending ++ rightSecond.pending)
      simpa [FreshAliasSequence.addAll_pending, leftOutput, rightOutput,
        dualPairPatternResult, patternAsGenerated, patternsAsGeneratedItems,
        pairPatterns, GeneratedItems.asTuple] using
        entailedPendingEq_weaken aligned.pendingAligned (by
          intro substitution solved
          have solvedOutput : Solves substitution
              (FreshAliasSequence.addAll certificate.leftAliases
                leftOutput).hard := by
            simpa [leftOutput, dualPairPatternResult, patternAsGenerated,
              List.append_assoc] using solved
          exact ((solves_append substitution _ _).mp
            ((solves_append substitution _ _).mp
              (Eq.mp (congrArg (Solves substitution) leftHard)
                solvedOutput)).1).1)

theorem PatternsElaborateUsing.generatedDualsLength
    {relation : M4ExpressionElaborationRelation} {signature : FrozenSignature}
    {context : Context} {arguments : PatternContext} {patterns : List Pattern}
    {bindings : List Ty} {start finish : Supply}
    {generated : GeneratedPatterns}
    (derivation : PatternsElaborateUsing relation signature context arguments
      patterns bindings start generated finish) :
    generated.duals.length = patterns.length := by
  induction patterns generalizing bindings start generated finish with
  | nil => cases derivation; rfl
  | cons pattern patterns induction =>
      cases derivation with
      | cons head tail => simp [induction tail]

private theorem variablesAvoid_hiddenAppend
    {first second observed : List UnificationVar}
    (firstAvoid : VariablesAvoid first observed)
    (secondAvoid : VariablesAvoid second observed) :
    VariablesAvoid (first ++ second) observed := by
  intro candidate member hidden
  rcases List.mem_append.mp hidden with hidden | hidden
  · exact firstAvoid candidate member hidden
  · exact secondAvoid candidate member hidden

private def supportedPatternPairItems
    {start next : Supply}
    {leftFirst rightFirst leftSecond rightSecond : GeneratedPattern}
    (first : SupportedEntailedAlignmentCertificate start next
      (patternAsGenerated leftFirst) (patternAsGenerated rightFirst))
    (second : SupportedEntailedAlignmentCertificate start next
      (patternAsGenerated leftSecond) (patternAsGenerated rightSecond))
    (leftSecondAvoids : GeneratedAvoids first.hidden
      (patternAsGenerated leftSecond))
    (rightSecondAvoids : GeneratedAvoids first.hidden
      (patternAsGenerated rightSecond))
    (leftFirstAvoids : GeneratedAvoids second.hidden
      (patternAsGenerated leftFirst))
    (rightFirstAvoids : GeneratedAvoids second.hidden
      (patternAsGenerated rightFirst))
    (hiddenDisjoint : ∀ candidate, candidate ∈ first.hidden →
      candidate ∉ second.hidden) :
    SupportedItemsAlignmentCertificate start next
      (patternsAsGeneratedItems (pairPatterns leftFirst leftSecond))
      (patternsAsGeneratedItems (pairPatterns rightFirst rightSecond)) := by
  let empty := SupportedItemsAlignmentCertificate.refl start next
    GeneratedItems.nil
  have nilAvoid (forbidden : List UnificationVar) :
      GeneratedItemsAvoid forbidden GeneratedItems.nil := by
    intro candidate member
    simp [GeneratedItems.nil, GeneratedItems.unificationVars,
      Ty.unificationVarsList, TypePM.unificationVars,
      pendingUnificationVars] at member
  have emptyHiddenAvoid (generated : Generated) :
      GeneratedAvoids empty.hidden generated := by
    intro candidate member hidden
    change candidate ∈ [] at hidden
    simp at hidden
  have emptyDisjoint : ∀ candidate, candidate ∈ second.hidden →
      candidate ∉ empty.hidden := by
    intro candidate member hidden
    change candidate ∈ [] at hidden
    simp at hidden
  let tail := SupportedItemsAlignmentCertificate.itemsCons second empty
    (nilAvoid second.hidden) (nilAvoid second.hidden)
    (emptyHiddenAvoid (patternAsGenerated leftSecond))
    (emptyHiddenAvoid (patternAsGenerated rightSecond)) emptyDisjoint
  have combined := SupportedItemsAlignmentCertificate.itemsCons first tail
    (by
      intro candidate member hidden
      apply leftSecondAvoids candidate _ hidden
      change candidate ∈ (GeneratedItems.singleton
        (patternAsGenerated leftSecond)).unificationVars at member
      simpa using member)
    (by
      intro candidate member hidden
      apply rightSecondAvoids candidate _ hidden
      change candidate ∈ (GeneratedItems.singleton
        (patternAsGenerated rightSecond)).unificationVars at member
      simpa using member)
    (by
      intro candidate member hidden
      apply leftFirstAvoids candidate member
      simpa [tail, empty, SupportedItemsAlignmentCertificate.itemsCons,
        SupportedItemsAlignmentCertificate.refl] using hidden)
    (by
      intro candidate member hidden
      apply rightFirstAvoids candidate member
      simpa [tail, empty, SupportedItemsAlignmentCertificate.itemsCons,
        SupportedItemsAlignmentCertificate.refl] using hidden)
    (by
      intro candidate member hidden
      apply hiddenDisjoint candidate member
      simpa [tail, empty, SupportedItemsAlignmentCertificate.itemsCons,
        SupportedItemsAlignmentCertificate.refl] using hidden)
  change SupportedItemsAlignmentCertificate start next
    (patternsAsGeneratedItems (pairPatterns leftFirst leftSecond))
    (patternsAsGeneratedItems (pairPatterns rightFirst rightSecond)) at combined
  exact combined

private theorem supportedPatternPairItems_hidden
    {start next : Supply}
    {leftFirst rightFirst leftSecond rightSecond : GeneratedPattern}
    (first : SupportedEntailedAlignmentCertificate start next
      (patternAsGenerated leftFirst) (patternAsGenerated rightFirst))
    (second : SupportedEntailedAlignmentCertificate start next
      (patternAsGenerated leftSecond) (patternAsGenerated rightSecond))
    (leftSecondAvoids : GeneratedAvoids first.hidden
      (patternAsGenerated leftSecond))
    (rightSecondAvoids : GeneratedAvoids first.hidden
      (patternAsGenerated rightSecond))
    (leftFirstAvoids : GeneratedAvoids second.hidden
      (patternAsGenerated leftFirst))
    (rightFirstAvoids : GeneratedAvoids second.hidden
      (patternAsGenerated rightFirst))
    (hiddenDisjoint : ∀ candidate, candidate ∈ first.hidden →
      candidate ∉ second.hidden) :
    (supportedPatternPairItems first second leftSecondAvoids
      rightSecondAvoids leftFirstAvoids rightFirstAvoids
      hiddenDisjoint).hidden = first.hidden ++ second.hidden := by
  unfold supportedPatternPairItems
  change first.hidden ++ (second.hidden ++ []) =
    first.hidden ++ second.hidden
  simp

private theorem supportedDualPairPattern_hidden
    {start next : Supply}
    {leftFirst leftSecond rightFirst rightSecond : GeneratedPattern}
    (leftBindings rightBindings : List Ty) (checks : List Equation)
    (certificate : SupportedItemsAlignmentCertificate start next
      (patternsAsGeneratedItems (pairPatterns leftFirst leftSecond))
      (patternsAsGeneratedItems (pairPatterns rightFirst rightSecond)))
    (checksAvoid : EquationsAvoid certificate.hidden checks) :
    (supportedDualPairPattern leftBindings rightBindings checks certificate
      checksAvoid).hidden = certificate.hidden := by
  rfl

private def transportSupportedCertificate
    {start next : Supply} {left right left' right' : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (leftEquality : left = left') (rightEquality : right = right') :
    SupportedEntailedAlignmentCertificate start next left' right' := by
  subst left'
  subst right'
  exact certificate

private theorem transportSupportedCertificate_hidden
    {start next : Supply} {left right left' right' : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (leftEquality : left = left') (rightEquality : right = right') :
    (transportSupportedCertificate certificate leftEquality
      rightEquality).hidden = certificate.hidden := by
  subst left'
  subst right'
  rfl
mutual

/-- Phase-local avoidance for user patterns.  Unlike coarse outer-start
provenance, this theorem keeps the explicit context, pattern arguments, and
incoming bindings separate, so it remains usable across a sibling boundary. -/
theorem PatternElaboratesUsing.avoids_of_inputs
    {signature : FrozenSignature} (signatureWellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {arguments : PatternContext}
    {pattern : Pattern} {bindings : List Ty} {start finish : Supply}
    {generated : GeneratedPattern} {forbidden : List UnificationVar}
    (contextAvoids : VariablesAvoid forbidden context.unificationVars)
    (argumentsAvoids : VariablesAvoid forbidden
      (dualUnificationVars arguments))
    (bindingsAvoids : VariablesAvoid forbidden
      (Ty.unificationVarsList bindings))
    (below : VariablesBelowSupply forbidden start)
    (derivation : PatternElaboratesUsing (ElaboratesFuel signature fuel)
      signature context arguments pattern bindings start generated finish) :
    GeneratedPatternAvoidance forbidden generated := by
  cases derivation with
  | var =>
      have dualAvoids : VariablesAvoid forbidden
          (dualVariables (⟨.var ⟨start.cap⟩, .var ⟨start.ty⟩⟩ : Dual)) := by
        apply freshObserved_avoids_belowForbidden
          (finish := ⟨start.ty + 1, start.cap + 1⟩) below
        intro candidate member
        cases candidate with
        | cap index =>
            have equality : index = ⟨start.cap⟩ := by
              simpa [dualVariables, Ty.unificationVars,
                Cap.unificationVars] using member
            cases equality
            simp [UnificationVar.FreshIn]
        | ty index =>
            have equality : index = ⟨start.ty⟩ := by
              simpa [dualVariables, Ty.unificationVars,
                Cap.unificationVars] using member
            cases equality
            simp [UnificationVar.FreshIn]
      have outputBindings : VariablesAvoid forbidden
          (Ty.unificationVarsList (bindings ++ [.var ⟨start.ty⟩])) := by
        intro candidate member hidden
        rw [Ty.unificationVarsList_append] at member
        simp only [List.mem_append] at member
        rcases member with inherited | fresh
        · exact bindingsAvoids candidate inherited hidden
        · exact freshObserved_avoids_belowForbidden
            (finish := ⟨start.ty + 1, start.cap⟩) below (by
            intro item itemMember
            cases item with
            | cap index =>
                simp [Ty.unificationVarsList, Ty.unificationVars]
                  at itemMember
            | ty index =>
                have equality : index = ⟨start.ty⟩ := by
                  simpa [Ty.unificationVarsList, Ty.unificationVars] using
                    itemMember
                cases equality
                simp [UnificationVar.FreshIn]) candidate fresh hidden
      exact ⟨patternBlock_avoid dualAvoids (by
          intro candidate member
          simp [TypePM.unificationVars] at member)
        (by intro candidate member; simp [pendingUnificationVars] at member),
        outputBindings⟩
  | wild =>
      have dualAvoids : VariablesAvoid forbidden
          (dualVariables (⟨.var ⟨start.cap⟩, .var ⟨start.ty⟩⟩ : Dual)) := by
        apply freshObserved_avoids_belowForbidden
          (finish := ⟨start.ty + 1, start.cap + 1⟩) below
        intro candidate member
        cases candidate with
        | cap index =>
            have equality : index = ⟨start.cap⟩ := by
              simpa [dualVariables, Ty.unificationVars,
                Cap.unificationVars] using member
            cases equality
            simp [UnificationVar.FreshIn]
        | ty index =>
            have equality : index = ⟨start.ty⟩ := by
              simpa [dualVariables, Ty.unificationVars,
                Cap.unificationVars] using member
            cases equality
            simp [UnificationVar.FreshIn]
      exact ⟨patternBlock_avoid dualAvoids (by
          intro candidate member
          simp [TypePM.unificationVars] at member)
        (by intro candidate member; simp [pendingUnificationVars] at member),
        bindingsAvoids⟩
  | @value expression bindings start inferred afterExpression
      expressionDerivation =>
      have childAvoids := generatedAvoids_of_support
        (extendedContext_avoids contextAvoids bindingsAvoids) below
        (expressionDerivation.supportProvenance signatureWellFormed)
      have startToAfter := expressionDerivation.supply_le_next
      have dualAvoids : VariablesAvoid forbidden
          (dualVariables
            (⟨.var ⟨afterExpression.cap⟩, inferred.target⟩ : Dual)) := by
        intro candidate member hidden
        cases candidate with
        | cap index =>
            simp [dualVariables, Cap.unificationVars]
              at member
            rcases member with capability | target
            · have bound := below (.cap index) hidden
              have equality : index = ⟨afterExpression.cap⟩ := by
                simpa [Cap.unificationVars] using capability
              cases equality
              simp only [UnificationVar.Below, Supply.Le] at bound startToAfter
              omega
            · exact generated_target_avoids childAvoids _ (by
                simpa using target) hidden
        | ty index =>
            simp [dualVariables, Cap.unificationVars]
              at member
            exact generated_target_avoids childAvoids _ (by
              simpa using member) hidden
      exact ⟨patternBlock_avoid dualAvoids
          (generated_hard_avoids childAvoids)
          (generated_pending_avoids childAvoids), bindingsAvoids⟩
  | @ctor constructor fields bindings start scheme generatedFields finish
      lookup arity fieldsDerivation =>
      have instantiationIncrease : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, DualScheme.instantiate]
      have fieldsAvoids := PatternsElaborateUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids bindingsAvoids
        (below.mono instantiationIncrease) fieldsDerivation
      have closed := signatureWellFormed.baseWellFormed
        |>.patternConstructorClosed_of_lookup lookup
      have instantiatedAvoids := variablesAvoid_of_support
        (context := []) (start := start)
        (by intro candidate member
            simp [Context.unificationVars, Context.freeTyVars,
              Context.freeCapVars, dedupFirst, dedup] at member) below
        (DualScheme.instantiate_support closed start)
      have expectedAvoids : VariablesAvoid forbidden
          (dualUnificationVars (scheme.instantiate start).1.fields) := by
        intro candidate member hidden
        exact instantiatedAvoids candidate (by simp [member]) hidden
      have resultAvoids : VariablesAvoid forbidden
          (dualVariables (scheme.instantiate start).1.result) := by
        intro candidate member hidden
        exact instantiatedAvoids candidate (by simp [member]) hidden
      have actualAvoids := items_duals_avoid fieldsAvoids.block
      exact ⟨patternBlock_avoid resultAvoids
          (equationsAvoid_append (items_hard_avoid fieldsAvoids.block)
            (fieldEquations_avoid actualAvoids expectedAvoids))
          (items_pending_avoid fieldsAvoids.block), fieldsAvoids.bindings⟩
  | @tuple items bindings start generatedItems finish itemsDerivation =>
      have itemsAvoids := PatternsElaborateUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids bindingsAvoids below
        itemsDerivation
      exact ⟨by
          intro candidate member hidden
          apply itemsAvoids.block candidate _ hidden
          have tupleMember :=
            (tuplePattern_mem_unificationVars_iff generatedItems candidate).mp
              member
          simpa [GeneratedItems.asTuple, GeneratedItems.unificationVars,
            Generated.unificationVars, Ty.unificationVars] using tupleMember,
        itemsAvoids.bindings⟩
  | @and left right bindings start generatedLeft afterLeft generatedRight finish
      leftDerivation rightDerivation =>
      have leftAvoids := PatternElaboratesUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids bindingsAvoids below
        leftDerivation
      have startToLeft := leftDerivation.supply_le_next
        (fun child => child.supply_le_next)
      have rightAvoids := PatternElaboratesUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids leftAvoids.bindings
        (below.mono startToLeft) rightDerivation
      have leftDual := pattern_dual_avoid leftAvoids.block
      have rightDual := pattern_dual_avoid rightAvoids.block
      exact ⟨patternBlock_avoid leftDual
          (equationsAvoid_append
            (equationsAvoid_append (generated_hard_avoids leftAvoids.block)
              (generated_hard_avoids rightAvoids.block))
            (dualEquations_avoid leftDual rightDual))
          (pendingAvoid_append (generated_pending_avoids leftAvoids.block)
            (generated_pending_avoids rightAvoids.block)),
        rightAvoids.bindings⟩
  | @or left right bindings start generatedLeft afterLeft generatedRight finish
      checks leftDerivation rightDerivation checksComputed =>
      have leftAvoids := PatternElaboratesUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids bindingsAvoids below
        leftDerivation
      have startToLeft := leftDerivation.supply_le_next
        (fun child => child.supply_le_next)
      have rightAvoids := PatternElaboratesUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids bindingsAvoids
        (below.mono startToLeft) rightDerivation
      have leftDual := pattern_dual_avoid leftAvoids.block
      have rightDual := pattern_dual_avoid rightAvoids.block
      have checksAvoid := bindingEquations_avoid leftAvoids.bindings
        rightAvoids.bindings checksComputed
      exact ⟨patternBlock_avoid leftDual
          (equationsAvoid_append
            (equationsAvoid_append
              (equationsAvoid_append (generated_hard_avoids leftAvoids.block)
                (generated_hard_avoids rightAvoids.block))
              (dualEquations_avoid leftDual rightDual)) checksAvoid)
          (pendingAvoid_append (generated_pending_avoids leftAvoids.block)
            (generated_pending_avoids rightAvoids.block)),
        leftAvoids.bindings⟩
  | @embed index bindings start selected lookup =>
      have selectedAvoids : VariablesAvoid forbidden
          (dualVariables selected) := by
        intro candidate member hidden
        apply argumentsAvoids candidate _ hidden
        rw [dualUnificationVars, List.mem_flatMap]
        have selectedMember : selected ∈ arguments := by
          obtain ⟨bound, equality⟩ := List.getElem?_eq_some_iff.mp lookup
          rw [← equality]
          exact List.getElem_mem bound
        exact ⟨selected, selectedMember, member⟩
      exact ⟨patternBlock_avoid selectedAvoids (by
          intro candidate member
          simp [TypePM.unificationVars] at member)
        (by intro candidate member; simp [pendingUnificationVars] at member),
        bindingsAvoids⟩
  | @app function fields bindings start scheme generatedFields finish
      lookup arity fieldsDerivation =>
      have instantiationIncrease : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, DualScheme.instantiate]
      have fieldsAvoids := PatternsElaborateUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids bindingsAvoids
        (below.mono instantiationIncrease) fieldsDerivation
      have closed := FrozenSignature.lookupPatternFunction_closed
        signatureWellFormed lookup
      have instantiatedAvoids := variablesAvoid_of_support
        (context := []) (start := start)
        (by intro candidate member
            simp [Context.unificationVars, Context.freeTyVars,
              Context.freeCapVars, dedupFirst, dedup] at member) below
        (DualScheme.instantiate_support closed start)
      have expectedAvoids : VariablesAvoid forbidden
          (dualUnificationVars (scheme.instantiate start).1.fields) := by
        intro candidate member hidden
        exact instantiatedAvoids candidate (by simp [member]) hidden
      have resultAvoids : VariablesAvoid forbidden
          (dualVariables (scheme.instantiate start).1.result) := by
        intro candidate member hidden
        exact instantiatedAvoids candidate (by simp [member]) hidden
      have actualAvoids := items_duals_avoid fieldsAvoids.block
      exact ⟨patternBlock_avoid resultAvoids
          (equationsAvoid_append (items_hard_avoid fieldsAvoids.block)
            (fieldEquations_avoid actualAvoids expectedAvoids))
          (items_pending_avoid fieldsAvoids.block), fieldsAvoids.bindings⟩
termination_by pattern.complexity * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

/-- List counterpart of `PatternElaboratesUsing.avoids_of_inputs`. -/
theorem PatternsElaborateUsing.avoids_of_inputs
    {signature : FrozenSignature} (signatureWellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {arguments : PatternContext}
    {patterns : List Pattern} {bindings : List Ty} {start finish : Supply}
    {generated : GeneratedPatterns} {forbidden : List UnificationVar}
    (contextAvoids : VariablesAvoid forbidden context.unificationVars)
    (argumentsAvoids : VariablesAvoid forbidden
      (dualUnificationVars arguments))
    (bindingsAvoids : VariablesAvoid forbidden
      (Ty.unificationVarsList bindings))
    (below : VariablesBelowSupply forbidden start)
    (derivation : PatternsElaborateUsing (ElaboratesFuel signature fuel)
      signature context arguments patterns bindings start generated finish) :
    GeneratedPatternsAvoidance forbidden generated := by
  cases derivation with
  | nil =>
      exact ⟨by
          intro candidate member
          simp [patternsAsGeneratedItems, GeneratedItems.unificationVars,
            Ty.unificationVarsList, TypePM.unificationVars,
            pendingUnificationVars] at member,
        bindingsAvoids⟩
  | @cons pattern patterns bindings start generatedHead afterHead generatedTail
      finish headDerivation tailDerivation =>
      have headAvoids := PatternElaboratesUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids bindingsAvoids below
        headDerivation
      have startToHead := headDerivation.supply_le_next
        (fun child => child.supply_le_next)
      have tailAvoids := PatternsElaborateUsing.avoids_of_inputs
        signatureWellFormed contextAvoids argumentsAvoids headAvoids.bindings
        (below.mono startToHead) tailDerivation
      have headDual := pattern_dual_avoid headAvoids.block
      have tailDuals := items_duals_avoid tailAvoids.block
      have combinedDuals : VariablesAvoid forbidden
          (dualUnificationVars (generatedHead.dual :: generatedTail.duals)) := by
        intro candidate member hidden
        simp only [dualUnificationVars, List.flatMap_cons, List.mem_append]
          at member
        rcases member with headMember | tailMember
        · exact headDual candidate headMember hidden
        · exact tailDuals candidate tailMember hidden
      exact ⟨patternsBlock_avoid combinedDuals
          (equationsAvoid_append (generated_hard_avoids headAvoids.block)
            (items_hard_avoid tailAvoids.block))
          (pendingAvoid_append (generated_pending_avoids headAvoids.block)
            (items_pending_avoid tailAvoids.block)), tailAvoids.bindings⟩
termination_by Pattern.listComplexity patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [Pattern.listComplexity]
  all_goals omega

end

set_option maxRecDepth 2048

mutual

/-- Full supported semantic coherence for a user pattern, parameterized only
by the supported coherence of its embedded expressions. -/
theorem PatternElaboratesUsing.supportedFuelPairCoherenceBelow
    {signature : FrozenSignature} {leftFuel rightFuel limit : Nat}
    (signatureWellFormed : signature.WellFormed)
    (expressionPair : SupportedM4ExpressionPairPropertyBelow
      signature leftFuel rightFuel limit)
    {context : Context} {outerStart start : Supply}
    {arguments : PatternContext} {pattern : Pattern} {bindings : List Ty}
    {leftGenerated rightGenerated : GeneratedPattern}
    {leftNext rightNext : Supply}
    (complexityBound : pattern.complexity < limit)
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (leftDerivation : PatternElaboratesUsing
      (ElaboratesFuel signature leftFuel) signature context arguments pattern
      bindings start leftGenerated leftNext)
    (rightDerivation : PatternElaboratesUsing
      (ElaboratesFuel signature rightFuel) signature context arguments pattern
      bindings start rightGenerated rightNext) :
    Nonempty (SupportedM4PatternPairCoherence start leftNext rightNext
      leftGenerated rightGenerated) := by
  cases leftDerivation with
  | var =>
      cases rightDerivation
      exact ⟨supportedPatternRefl _ _ _⟩
  | wild =>
      cases rightDerivation
      exact ⟨supportedPatternRefl _ _ _⟩
  | @value expression bindings start leftInferred leftAfter leftExpression =>
      cases rightDerivation with
      | @value _ _ _ rightInferred rightAfter rightExpression =>
          have contextSupport := Pattern.extendContext_support
            (bindingsSupport.extend_finish (Supply.le_refl start))
          have childWellFormed :=
            M4FreshRenaming.Supply.WellFormedFor.of_contextSupport
              contextWellFormed outerToStart contextSupport
          obtain ⟨child⟩ := expressionPair (by
              simp_all [Pattern.complexity]
              omega) childWellFormed
            leftExpression rightExpression
          have bindingsAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart bindingsSupport child.certificate.hiddenFresh
          exact supportedValuePattern child bindingsAvoid bindingsAvoid
  | @ctor constructor fields bindings start leftScheme leftFields leftFinish
      leftLookup leftArity leftFieldsDerivation =>
      cases rightDerivation with
      | @ctor _ _ _ _ rightScheme rightFields rightFinish rightLookup
          rightArity rightFieldsDerivation =>
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          have startToFields : start.Le (leftScheme.instantiate start).2 := by
            simp [Supply.Le, DualScheme.instantiate]
          obtain ⟨fieldsResult⟩ :=
            PatternsElaborateUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.complexity]
                omega) contextWellFormed
              (argumentsSupport.extend_finish startToFields)
              (bindingsSupport.extend_finish startToFields)
              (Supply.le_trans outerToStart startToFields)
              leftFieldsDerivation rightFieldsDerivation
          cases fieldsResult.next_eq
          have closed := signatureWellFormed.baseWellFormed
            |>.patternConstructorClosed_of_lookup leftLookup
          have instantiatedSupport := DualScheme.instantiate_support closed start
          have emptyWellFormed : start.WellFormedFor ([] : Context) := by
            change 0 ≤ start.ty ∧ 0 ≤ start.cap
            exact ⟨Nat.zero_le _, Nat.zero_le _⟩
          have instantiatedAvoid := support_avoids_laterFresh emptyWellFormed
            startToFields instantiatedSupport
            fieldsResult.certificate.hiddenFresh
          have resultAvoid : VariablesAvoid fieldsResult.certificate.hidden
              (dualVariables (leftScheme.instantiate start).1.result) := by
            intro candidate member hidden
            exact instantiatedAvoid candidate (by simp [member]) hidden
          have expectedAvoid : VariablesAvoid fieldsResult.certificate.hidden
              (dualUnificationVars
                (leftScheme.instantiate start).1.fields) := by
            intro candidate member hidden
            exact instantiatedAvoid candidate (by simp [member]) hidden
          have leftLength :=
            (TypePM.Source.M4.CompletenessArchitecture.PatternsElaborateUsing.generatedDualsLength
              leftFieldsDerivation).trans leftArity
          have rightLength :=
            (TypePM.Source.M4.CompletenessArchitecture.PatternsElaborateUsing.generatedDualsLength
              rightFieldsDerivation).trans rightArity
          have instantiatedFieldsLength :
              (leftScheme.instantiate start).1.fields.length =
                leftScheme.fields.length := by
            simp [DualScheme.instantiate]
          let fieldsCertificate := fieldsResult.certificate.rebase
            (fieldsResult.certificate.hiddenFresh.widen startToFields
              (Supply.le_refl leftNext))
          exact ⟨
            { next_eq := rfl
              bindings_eq := fieldsResult.bindings_eq
              certificate := supportedFieldPattern
                (leftScheme.instantiate start).1.result
                (leftScheme.instantiate start).1.fields
                (leftLength.trans instantiatedFieldsLength.symm)
                (rightLength.trans instantiatedFieldsLength.symm)
                fieldsCertificate (by
                  simpa only [fieldsCertificate,
                    SupportedItemsAlignmentCertificate.rebase] using resultAvoid)
                (by
                  simpa only [fieldsCertificate,
                    SupportedItemsAlignmentCertificate.rebase] using expectedAvoid)
              leftBindingsAvoid := fieldsResult.leftBindingsAvoid
              rightBindingsAvoid := fieldsResult.rightBindingsAvoid }⟩
  | @tuple items bindings start leftItems leftFinish leftItemsDerivation =>
      cases rightDerivation with
      | @tuple _ _ _ rightItems rightFinish rightItemsDerivation =>
          obtain ⟨itemsResult⟩ :=
            PatternsElaborateUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.complexity]
                omega) contextWellFormed
              argumentsSupport bindingsSupport outerToStart
              leftItemsDerivation rightItemsDerivation
          exact ⟨
            { next_eq := itemsResult.next_eq
              bindings_eq := itemsResult.bindings_eq
              certificate := supportedTuplePattern itemsResult.certificate
              leftBindingsAvoid := itemsResult.leftBindingsAvoid
              rightBindingsAvoid := itemsResult.rightBindingsAvoid }⟩
  | @and left right bindings start leftFirst leftMiddle leftSecond leftFinish
      leftFirstDerivation leftSecondDerivation =>
      cases rightDerivation with
      | @and _ _ _ _ rightFirst rightMiddle rightSecond rightFinish
          rightFirstDerivation rightSecondDerivation =>
          obtain ⟨firstResult⟩ :=
            PatternElaboratesUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.complexity]
                omega) contextWellFormed
              argumentsSupport bindingsSupport outerToStart
              leftFirstDerivation rightFirstDerivation
          cases firstResult.next_eq
          rw [← firstResult.bindings_eq] at rightSecondDerivation
          have startToMiddle := leftFirstDerivation.supply_le_next
            (fun child => child.supply_le_next)
          have leftFirstSupport := leftFirstDerivation.supportProvenance
            signatureWellFormed (fun child => child.supply_le_next)
            (fun child => child.supportProvenance signatureWellFormed)
            argumentsSupport bindingsSupport outerToStart
          have outputBindings : VariablesSupportProvenance context outerStart
              leftMiddle (Ty.unificationVarsList leftFirst.bindings) := by
            intro candidate member
            exact leftFirstSupport candidate (by
              simp [GeneratedPattern.unificationVars, member])
          obtain ⟨secondResult⟩ :=
            PatternElaboratesUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.complexity]
                omega) contextWellFormed
              (argumentsSupport.extend_finish startToMiddle) outputBindings
              (Supply.le_trans outerToStart startToMiddle)
              leftSecondDerivation rightSecondDerivation
          cases secondResult.next_eq
          have contextSupport : VariablesSupportProvenance context outerStart
              start context.unificationVars := fun _ member => Or.inl member
          have contextAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart contextSupport firstResult.certificate.hiddenFresh
          have argumentsAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart argumentsSupport firstResult.certificate.hiddenFresh
          have bindingsAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart bindingsSupport firstResult.certificate.hiddenFresh
          have below := freshIn_to_belowFinish
            firstResult.certificate.hiddenFresh
          have leftSecondAvoid := PatternElaboratesUsing.avoids_of_inputs
            signatureWellFormed contextAvoid argumentsAvoid
            firstResult.leftBindingsAvoid below leftSecondDerivation
          have rightSecondAvoid := PatternElaboratesUsing.avoids_of_inputs
            signatureWellFormed contextAvoid argumentsAvoid
            firstResult.leftBindingsAvoid below rightSecondDerivation
          have leftFirstBlockSupport := patternAsGenerated_support
            leftFirstSupport
          have rightFirstSupport := patternAsGenerated_support
            (rightFirstDerivation.supportProvenance signatureWellFormed
              (fun child => child.supply_le_next)
              (fun child => child.supportProvenance signatureWellFormed)
              argumentsSupport bindingsSupport outerToStart)
          have leftFirstAvoid := support_avoids_laterFresh contextWellFormed
            (Supply.le_trans outerToStart startToMiddle) leftFirstBlockSupport
            secondResult.certificate.hiddenFresh
          have rightFirstAvoid := support_avoids_laterFresh contextWellFormed
            (Supply.le_trans outerToStart startToMiddle) rightFirstSupport
            secondResult.certificate.hiddenFresh
          let firstCertificate := firstResult.certificate.rebase
            (firstResult.certificate.hiddenFresh.widen (Supply.le_refl start)
              (leftSecondDerivation.supply_le_next
                (fun child => child.supply_le_next)))
          let secondCertificate := secondResult.certificate.rebase
            (secondResult.certificate.hiddenFresh.widen startToMiddle
              (Supply.le_refl leftNext))
          let pairCertificate := supportedPatternPairItems firstCertificate
            secondCertificate leftSecondAvoid.block rightSecondAvoid.block
            leftFirstAvoid rightFirstAvoid
            (freshIntervals_disjoint firstResult.certificate.hiddenFresh
              secondResult.certificate.hiddenFresh)
          have pairHidden : pairCertificate.hidden =
              firstResult.certificate.hidden ++
                secondResult.certificate.hidden := by
            simpa [pairCertificate, firstCertificate, secondCertificate,
              SupportedEntailedAlignmentCertificate.rebase] using
              supportedPatternPairItems_hidden firstCertificate
                secondCertificate leftSecondAvoid.block rightSecondAvoid.block
                leftFirstAvoid rightFirstAvoid
                (freshIntervals_disjoint
                  firstResult.certificate.hiddenFresh
                  secondResult.certificate.hiddenFresh)
          have noChecks : EquationsAvoid pairCertificate.hidden [] := by
            intro candidate member
            simp [TypePM.unificationVars] at member
          let rawAndCertificate := supportedDualPairPattern
            leftSecond.bindings rightSecond.bindings [] pairCertificate noChecks
          have leftAndEquality :
              patternAsGenerated (dualPairPatternResult leftFirst leftSecond
                leftSecond.bindings []) =
              patternAsGenerated
                { dual := leftFirst.dual
                  bindings := leftSecond.bindings
                  hard := leftFirst.hard ++ leftSecond.hard ++
                    Pattern.dualEquations leftFirst.dual leftSecond.dual
                  pending := leftFirst.pending ++ leftSecond.pending } := by
            simp [dualPairPatternResult]
          have rightAndEquality :
              patternAsGenerated (dualPairPatternResult rightFirst rightSecond
                rightSecond.bindings []) =
              patternAsGenerated
                { dual := rightFirst.dual
                  bindings := rightSecond.bindings
                  hard := rightFirst.hard ++ rightSecond.hard ++
                    Pattern.dualEquations rightFirst.dual rightSecond.dual
                  pending := rightFirst.pending ++ rightSecond.pending } := by
            simp [dualPairPatternResult]
          let andCertificate : SupportedEntailedAlignmentCertificate start
              leftNext
              (patternAsGenerated
                { dual := leftFirst.dual
                  bindings := leftSecond.bindings
                  hard := leftFirst.hard ++ leftSecond.hard ++
                    Pattern.dualEquations leftFirst.dual leftSecond.dual
                  pending := leftFirst.pending ++ leftSecond.pending })
              (patternAsGenerated
                { dual := rightFirst.dual
                  bindings := rightSecond.bindings
                  hard := rightFirst.hard ++ rightSecond.hard ++
                    Pattern.dualEquations rightFirst.dual rightSecond.dual
                  pending := rightFirst.pending ++ rightSecond.pending }) :=
            transportSupportedCertificate rawAndCertificate
              leftAndEquality rightAndEquality
          have andHidden : andCertificate.hidden =
              firstResult.certificate.hidden ++
                secondResult.certificate.hidden := by
            calc
              andCertificate.hidden = pairCertificate.hidden := by
                calc
                  andCertificate.hidden = rawAndCertificate.hidden := by
                    exact transportSupportedCertificate_hidden
                      rawAndCertificate leftAndEquality rightAndEquality
                  _ = pairCertificate.hidden := by
                    exact supportedDualPairPattern_hidden leftSecond.bindings
                      rightSecond.bindings [] pairCertificate noChecks
              _ = _ := pairHidden
          exact ⟨
            { next_eq := rfl
              bindings_eq := secondResult.bindings_eq
              certificate := andCertificate
              leftBindingsAvoid := by
                rw [andHidden]
                exact variablesAvoid_hiddenAppend leftSecondAvoid.bindings
                  secondResult.leftBindingsAvoid
              rightBindingsAvoid := by
                rw [andHidden]
                exact variablesAvoid_hiddenAppend rightSecondAvoid.bindings
                  secondResult.rightBindingsAvoid }⟩
  | @or left right bindings start leftFirst leftMiddle leftSecond leftFinish
      leftChecks leftFirstDerivation leftSecondDerivation leftChecksComputed =>
      cases rightDerivation with
      | @or _ _ _ _ rightFirst rightMiddle rightSecond rightFinish rightChecks
          rightFirstDerivation rightSecondDerivation rightChecksComputed =>
          obtain ⟨firstResult⟩ :=
            PatternElaboratesUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.complexity]
                omega) contextWellFormed
              argumentsSupport bindingsSupport outerToStart
              leftFirstDerivation rightFirstDerivation
          cases firstResult.next_eq
          have startToMiddle := leftFirstDerivation.supply_le_next
            (fun child => child.supply_le_next)
          obtain ⟨secondResult⟩ :=
            PatternElaboratesUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.complexity]
                omega) contextWellFormed
              (argumentsSupport.extend_finish startToMiddle)
              (bindingsSupport.extend_finish startToMiddle)
              (Supply.le_trans outerToStart startToMiddle)
              leftSecondDerivation rightSecondDerivation
          cases secondResult.next_eq
          have checksEquality : leftChecks = rightChecks := by
            rw [firstResult.bindings_eq, secondResult.bindings_eq]
              at leftChecksComputed
            rw [leftChecksComputed] at rightChecksComputed
            exact Option.some.inj rightChecksComputed
          subst rightChecks
          have contextSupport : VariablesSupportProvenance context outerStart
              start context.unificationVars := fun _ member => Or.inl member
          have contextAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart contextSupport firstResult.certificate.hiddenFresh
          have argumentsAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart argumentsSupport firstResult.certificate.hiddenFresh
          have bindingsAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart bindingsSupport firstResult.certificate.hiddenFresh
          have below := freshIn_to_belowFinish
            firstResult.certificate.hiddenFresh
          have leftSecondAvoid := PatternElaboratesUsing.avoids_of_inputs
            signatureWellFormed contextAvoid argumentsAvoid bindingsAvoid below
            leftSecondDerivation
          have rightSecondAvoid := PatternElaboratesUsing.avoids_of_inputs
            signatureWellFormed contextAvoid argumentsAvoid bindingsAvoid below
            rightSecondDerivation
          have leftFirstSupport := leftFirstDerivation.supportProvenance
            signatureWellFormed (fun child => child.supply_le_next)
            (fun child => child.supportProvenance signatureWellFormed)
            argumentsSupport bindingsSupport outerToStart
          have rightFirstSupport := rightFirstDerivation.supportProvenance
            signatureWellFormed (fun child => child.supply_le_next)
            (fun child => child.supportProvenance signatureWellFormed)
            argumentsSupport bindingsSupport outerToStart
          have leftFirstAvoid := support_avoids_laterFresh contextWellFormed
            (Supply.le_trans outerToStart startToMiddle)
            (patternAsGenerated_support leftFirstSupport)
            secondResult.certificate.hiddenFresh
          have rightFirstAvoid := support_avoids_laterFresh contextWellFormed
            (Supply.le_trans outerToStart startToMiddle)
            (patternAsGenerated_support rightFirstSupport)
            secondResult.certificate.hiddenFresh
          let firstCertificate := firstResult.certificate.rebase
            (firstResult.certificate.hiddenFresh.widen (Supply.le_refl start)
              (leftSecondDerivation.supply_le_next
                (fun child => child.supply_le_next)))
          let secondCertificate := secondResult.certificate.rebase
            (secondResult.certificate.hiddenFresh.widen
              startToMiddle (Supply.le_refl leftNext))
          let pairCertificate := supportedPatternPairItems firstCertificate
            secondCertificate leftSecondAvoid.block rightSecondAvoid.block
            leftFirstAvoid rightFirstAvoid
            (freshIntervals_disjoint firstResult.certificate.hiddenFresh
              secondResult.certificate.hiddenFresh)
          have pairHidden : pairCertificate.hidden =
              firstResult.certificate.hidden ++
                secondResult.certificate.hidden := by
            simpa [pairCertificate, firstCertificate, secondCertificate,
              SupportedEntailedAlignmentCertificate.rebase] using
              supportedPatternPairItems_hidden firstCertificate
                secondCertificate leftSecondAvoid.block rightSecondAvoid.block
                leftFirstAvoid rightFirstAvoid
                (freshIntervals_disjoint
                  firstResult.certificate.hiddenFresh
                  secondResult.certificate.hiddenFresh)
          have firstBindingsSupport : VariablesSupportProvenance context
              outerStart leftMiddle
              (Ty.unificationVarsList leftFirst.bindings) := by
            intro candidate member
            apply leftFirstSupport candidate
            simp [GeneratedPattern.unificationVars, member]
          have firstBindingsLaterAvoid := support_avoids_laterFresh
            contextWellFormed (Supply.le_trans outerToStart startToMiddle)
            firstBindingsSupport secondResult.certificate.hiddenFresh
          have checksAvoid := bindingEquations_avoid
            (variablesAvoid_hiddenAppend firstResult.leftBindingsAvoid
              firstBindingsLaterAvoid)
            (variablesAvoid_hiddenAppend leftSecondAvoid.bindings
              secondResult.leftBindingsAvoid) leftChecksComputed
          have checksAvoidPair : EquationsAvoid pairCertificate.hidden
              leftChecks := by
            rw [pairHidden]
            exact checksAvoid
          have rightFirstBindingsLaterAvoid : VariablesAvoid
              secondResult.certificate.hidden
              (Ty.unificationVarsList rightFirst.bindings) := by
            rw [← firstResult.bindings_eq]
            exact firstBindingsLaterAvoid
          let orCertificate := supportedDualPairPattern
            leftFirst.bindings rightFirst.bindings leftChecks pairCertificate
            checksAvoidPair
          have orHidden : orCertificate.hidden =
              firstResult.certificate.hidden ++
                secondResult.certificate.hidden := by
            calc
              orCertificate.hidden = pairCertificate.hidden := by
                exact supportedDualPairPattern_hidden leftFirst.bindings
                  rightFirst.bindings leftChecks pairCertificate
                  checksAvoidPair
              _ = _ := pairHidden
          exact ⟨
            { next_eq := rfl
              bindings_eq := firstResult.bindings_eq
              certificate := orCertificate
              leftBindingsAvoid := by
                rw [orHidden]
                exact variablesAvoid_hiddenAppend
                  firstResult.leftBindingsAvoid firstBindingsLaterAvoid
              rightBindingsAvoid := by
                rw [orHidden]
                exact variablesAvoid_hiddenAppend
                  firstResult.rightBindingsAvoid
                  rightFirstBindingsLaterAvoid }⟩
  | @embed index bindings start leftSelected leftLookup =>
      cases rightDerivation with
      | @embed _ _ _ rightSelected rightLookup =>
          have selectedEquality : leftSelected = rightSelected := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightSelected
          exact ⟨supportedPatternRefl _ _ _⟩
  | @app function fields bindings start leftScheme leftFields leftFinish
      leftLookup leftArity leftFieldsDerivation =>
      cases rightDerivation with
      | @app _ _ _ _ rightScheme rightFields rightFinish rightLookup
          rightArity rightFieldsDerivation =>
          have schemeEquality : leftScheme = rightScheme := by
            rw [leftLookup] at rightLookup
            exact Option.some.inj rightLookup
          subst rightScheme
          have startToFields : start.Le (leftScheme.instantiate start).2 := by
            simp [Supply.Le, DualScheme.instantiate]
          obtain ⟨fieldsResult⟩ :=
            PatternsElaborateUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.complexity]
                omega) contextWellFormed
              (argumentsSupport.extend_finish startToFields)
              (bindingsSupport.extend_finish startToFields)
              (Supply.le_trans outerToStart startToFields)
              leftFieldsDerivation rightFieldsDerivation
          cases fieldsResult.next_eq
          have closed := FrozenSignature.lookupPatternFunction_closed
            signatureWellFormed leftLookup
          have instantiatedSupport := DualScheme.instantiate_support closed start
          have emptyWellFormed : start.WellFormedFor ([] : Context) := by
            change 0 ≤ start.ty ∧ 0 ≤ start.cap
            exact ⟨Nat.zero_le _, Nat.zero_le _⟩
          have instantiatedAvoid := support_avoids_laterFresh emptyWellFormed
            startToFields instantiatedSupport
            fieldsResult.certificate.hiddenFresh
          have resultAvoid : VariablesAvoid fieldsResult.certificate.hidden
              (dualVariables (leftScheme.instantiate start).1.result) := by
            intro candidate member hidden
            exact instantiatedAvoid candidate (by simp [member]) hidden
          have expectedAvoid : VariablesAvoid fieldsResult.certificate.hidden
              (dualUnificationVars
                (leftScheme.instantiate start).1.fields) := by
            intro candidate member hidden
            exact instantiatedAvoid candidate (by simp [member]) hidden
          let fieldsCertificate := fieldsResult.certificate.rebase
            (fieldsResult.certificate.hiddenFresh.widen startToFields
              (Supply.le_refl leftNext))
          have instantiatedFieldsLength :
              (leftScheme.instantiate start).1.fields.length =
                leftScheme.fields.length := by
            simp [DualScheme.instantiate]
          exact ⟨
            { next_eq := rfl
              bindings_eq := fieldsResult.bindings_eq
              certificate := supportedFieldPattern
                (leftScheme.instantiate start).1.result
                (leftScheme.instantiate start).1.fields
                ((TypePM.Source.M4.CompletenessArchitecture.PatternsElaborateUsing.generatedDualsLength
                  leftFieldsDerivation).trans leftArity |>.trans
                    instantiatedFieldsLength.symm)
                ((TypePM.Source.M4.CompletenessArchitecture.PatternsElaborateUsing.generatedDualsLength
                  rightFieldsDerivation).trans rightArity |>.trans
                    instantiatedFieldsLength.symm)
                fieldsCertificate (by
                  simpa only [fieldsCertificate,
                    SupportedItemsAlignmentCertificate.rebase] using resultAvoid)
                (by
                  simpa only [fieldsCertificate,
                    SupportedItemsAlignmentCertificate.rebase] using expectedAvoid)
              leftBindingsAvoid := fieldsResult.leftBindingsAvoid
              rightBindingsAvoid := fieldsResult.rightBindingsAvoid }⟩
termination_by pattern.complexity * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

/-- Full supported semantic coherence for a source-ordered pattern list. -/
theorem PatternsElaborateUsing.supportedFuelPairCoherenceBelow
    {signature : FrozenSignature} {leftFuel rightFuel limit : Nat}
    (signatureWellFormed : signature.WellFormed)
    (expressionPair : SupportedM4ExpressionPairPropertyBelow
      signature leftFuel rightFuel limit)
    {context : Context} {outerStart start : Supply}
    {arguments : PatternContext} {patterns : List Pattern} {bindings : List Ty}
    {leftGenerated rightGenerated : GeneratedPatterns}
    {leftNext rightNext : Supply}
    (complexityBound : Pattern.listComplexity patterns < limit)
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (leftDerivation : PatternsElaborateUsing
      (ElaboratesFuel signature leftFuel) signature context arguments patterns
      bindings start leftGenerated leftNext)
    (rightDerivation : PatternsElaborateUsing
      (ElaboratesFuel signature rightFuel) signature context arguments patterns
      bindings start rightGenerated rightNext) :
    Nonempty (SupportedM4PatternsPairCoherence start leftNext rightNext
      leftGenerated rightGenerated) := by
  cases leftDerivation with
  | nil =>
      cases rightDerivation
      exact ⟨
        { next_eq := rfl
          bindings_eq := rfl
          certificate := SupportedItemsAlignmentCertificate.refl start start _
          leftBindingsAvoid := by
            intro candidate member hidden
            change candidate ∈ [] at hidden
            simp at hidden
          rightBindingsAvoid := by
            intro candidate member hidden
            change candidate ∈ [] at hidden
            simp at hidden }⟩
  | @cons pattern patterns bindings start leftHead leftMiddle leftTail leftFinish
      leftHeadDerivation leftTailDerivation =>
      cases rightDerivation with
      | @cons _ _ _ _ rightHead rightMiddle rightTail rightFinish
          rightHeadDerivation rightTailDerivation =>
          obtain ⟨headResult⟩ :=
            PatternElaboratesUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.listComplexity]
                omega) contextWellFormed
              argumentsSupport bindingsSupport outerToStart
              leftHeadDerivation rightHeadDerivation
          cases headResult.next_eq
          rw [← headResult.bindings_eq] at rightTailDerivation
          have startToMiddle := leftHeadDerivation.supply_le_next
            (fun child => child.supply_le_next)
          have leftHeadSupport := leftHeadDerivation.supportProvenance
            signatureWellFormed (fun child => child.supply_le_next)
            (fun child => child.supportProvenance signatureWellFormed)
            argumentsSupport bindingsSupport outerToStart
          have outputBindings : VariablesSupportProvenance context outerStart
              leftMiddle (Ty.unificationVarsList leftHead.bindings) := by
            intro candidate member
            exact leftHeadSupport candidate (by
              simp [GeneratedPattern.unificationVars, member])
          obtain ⟨tailResult⟩ :=
            PatternsElaborateUsing.supportedFuelPairCoherenceBelow
              signatureWellFormed expressionPair (by
                simp_all [Pattern.listComplexity]
                omega) contextWellFormed
              (argumentsSupport.extend_finish startToMiddle) outputBindings
              (Supply.le_trans outerToStart startToMiddle)
              leftTailDerivation rightTailDerivation
          cases tailResult.next_eq
          have contextSupport : VariablesSupportProvenance context outerStart
              start context.unificationVars := fun _ member => Or.inl member
          have contextAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart contextSupport headResult.certificate.hiddenFresh
          have argumentsAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart argumentsSupport headResult.certificate.hiddenFresh
          have bindingsAvoid := support_avoids_laterFresh contextWellFormed
            outerToStart bindingsSupport headResult.certificate.hiddenFresh
          have below := freshIn_to_belowFinish
            headResult.certificate.hiddenFresh
          have leftTailAvoid := PatternsElaborateUsing.avoids_of_inputs
            signatureWellFormed contextAvoid argumentsAvoid
            headResult.leftBindingsAvoid below leftTailDerivation
          have rightTailAvoid := PatternsElaborateUsing.avoids_of_inputs
            signatureWellFormed contextAvoid argumentsAvoid
            headResult.leftBindingsAvoid below rightTailDerivation
          have leftHeadAvoid := support_avoids_laterFresh contextWellFormed
            (Supply.le_trans outerToStart startToMiddle)
            (patternAsGenerated_support leftHeadSupport)
            tailResult.certificate.hiddenFresh
          have rightHeadAvoid := support_avoids_laterFresh contextWellFormed
            (Supply.le_trans outerToStart startToMiddle)
            (patternAsGenerated_support
              (rightHeadDerivation.supportProvenance signatureWellFormed
                (fun child => child.supply_le_next)
                (fun child => child.supportProvenance signatureWellFormed)
                argumentsSupport bindingsSupport outerToStart))
            tailResult.certificate.hiddenFresh
          let headCertificate := headResult.certificate.rebase
            (headResult.certificate.hiddenFresh.widen (Supply.le_refl start)
              (leftTailDerivation.supply_le_next
                (fun child => child.supply_le_next)))
          let tailCertificate := tailResult.certificate.rebase
            (tailResult.certificate.hiddenFresh.widen startToMiddle
              (Supply.le_refl leftNext))
          exact ⟨
            { next_eq := rfl
              bindings_eq := tailResult.bindings_eq
              certificate := SupportedItemsAlignmentCertificate.itemsCons
                headCertificate tailCertificate leftTailAvoid.block
                rightTailAvoid.block leftHeadAvoid rightHeadAvoid
                (freshIntervals_disjoint
                  headResult.certificate.hiddenFresh
                  tailResult.certificate.hiddenFresh)
              leftBindingsAvoid := variablesAvoid_hiddenAppend
                leftTailAvoid.bindings tailResult.leftBindingsAvoid
              rightBindingsAvoid := variablesAvoid_hiddenAppend
                rightTailAvoid.bindings tailResult.rightBindingsAvoid }⟩
termination_by Pattern.listComplexity patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [Pattern.listComplexity]
  all_goals omega

end

/-- Unbounded public wrapper for callers that already have coherence for
every possible embedded expression. -/
theorem PatternElaboratesUsing.supportedFuelPairCoherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    (signatureWellFormed : signature.WellFormed)
    (expressionPair : SupportedM4ExpressionPairProperty
      signature leftFuel rightFuel)
    {context : Context} {outerStart start : Supply}
    {arguments : PatternContext} {pattern : Pattern} {bindings : List Ty}
    {leftGenerated rightGenerated : GeneratedPattern}
    {leftNext rightNext : Supply}
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (leftDerivation : PatternElaboratesUsing
      (ElaboratesFuel signature leftFuel) signature context arguments pattern
      bindings start leftGenerated leftNext)
    (rightDerivation : PatternElaboratesUsing
      (ElaboratesFuel signature rightFuel) signature context arguments pattern
      bindings start rightGenerated rightNext) :
    Nonempty (SupportedM4PatternPairCoherence start leftNext rightNext
      leftGenerated rightGenerated) := by
  apply PatternElaboratesUsing.supportedFuelPairCoherenceBelow
    signatureWellFormed
    (limit := pattern.complexity + 1)
    (fun _bound wellFormed left right =>
      expressionPair wellFormed left right)
    (Nat.lt_succ_self _)
    contextWellFormed argumentsSupport bindingsSupport outerToStart
    leftDerivation rightDerivation

/-- Unbounded public wrapper for source-ordered pattern lists. -/
theorem PatternsElaborateUsing.supportedFuelPairCoherence
    {signature : FrozenSignature} {leftFuel rightFuel : Nat}
    (signatureWellFormed : signature.WellFormed)
    (expressionPair : SupportedM4ExpressionPairProperty
      signature leftFuel rightFuel)
    {context : Context} {outerStart start : Supply}
    {arguments : PatternContext} {patterns : List Pattern} {bindings : List Ty}
    {leftGenerated rightGenerated : GeneratedPatterns}
    {leftNext rightNext : Supply}
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (leftDerivation : PatternsElaborateUsing
      (ElaboratesFuel signature leftFuel) signature context arguments patterns
      bindings start leftGenerated leftNext)
    (rightDerivation : PatternsElaborateUsing
      (ElaboratesFuel signature rightFuel) signature context arguments patterns
      bindings start rightGenerated rightNext) :
    Nonempty (SupportedM4PatternsPairCoherence start leftNext rightNext
      leftGenerated rightGenerated) := by
  apply PatternsElaborateUsing.supportedFuelPairCoherenceBelow
    signatureWellFormed
    (limit := Pattern.listComplexity patterns + 1)
    (fun _bound wellFormed left right =>
      expressionPair wellFormed left right)
    (Nat.lt_succ_self _)
    contextWellFormed argumentsSupport bindingsSupport outerToStart
    leftDerivation rightDerivation

end TypePM.Source.M4.CompletenessArchitecture
