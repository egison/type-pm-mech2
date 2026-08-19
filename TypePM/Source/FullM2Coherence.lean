import TypePM.Source.BoundedClosureRenaming
import TypePM.Source.EntailedElaborationComposition
import TypePM.Source.ProvenancedFreshClosureAlignment

/-!
# Full M2 source-coherence induction boundary

The semantic alignment certificate used for acceptance does not, by itself,
preserve principal targets: an admissible fresh alias may still occur in the
raw target.  This module records the exact stronger result required by the
final source induction.  It combines

* equality of the two finishing supplies,
* an asymmetric finite-alias semantic alignment certificate, and
* a closure alignment whose renaming fixes the entire future fresh stream.

The last field is stronger than target-level mutual instancehood.  It is the
form needed at a surrounding `letE`: its exact body-context equality and its
`FixesAtOrAbove` proof feed directly into
`Elaborates.transport_of_fixesAtOrAbove`.

The module also isolates the remaining recursive proof as a standard
well-founded source-expression induction.  Ordinary constructors and the
`letE` constructor are separate premises, so work on the representative-
sensitive `letE` step does not need to duplicate the recursion argument.
-/

namespace TypePM.Source

/-- Supply agreement plus the support-strengthened semantic certificate.
This is the constructor-compositional core of full M2 coherence. -/
structure SupportedM2PairCoherence
    (start leftNext rightNext : Supply)
    (left right : Generated) where
  next_eq : leftNext = rightNext
  certificate : SupportedEntailedAlignmentCertificate
    start leftNext left right

/-- Generic closure theorem which removes closure reasoning from every
individual source constructor.  The two derivations supply the numeric
support bounds; the supported certificate supplies alias admissibility,
target invariance, and cumulative context fixedness. -/
def SupportedCertificateClosureAlignmentComplete : Prop :=
  ∀ {signature : Signature} {context : Context} {expression : Expr}
      {start next : Supply} {left right : Generated},
    start.WellFormedFor context →
      Elaborates signature context expression start left next →
        Elaborates signature context expression start right next →
          SupportedEntailedAlignmentCertificate start next left right →
            ∀ (leftClosure : PrincipalBlockClosure left)
                (rightClosure : PrincipalBlockClosure right),
              leftClosure.Absorbing → rightClosure.Absorbing →
                Nonempty (ProvenancedFreshClosureAlignment
                  leftClosure rightClosure context next)

/-- Constructor-compositional pair property before applying the generic
closure theorem. -/
def SupportedM2PairProperty (expression : Expr) : Prop :=
  ∀ {signature : Signature} {context : Context} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      Elaborates signature context expression start
          leftGenerated leftNext →
        Elaborates signature context expression start
            rightGenerated rightNext →
          Nonempty (SupportedM2PairCoherence start leftNext rightNext
            leftGenerated rightGenerated)

/-- List-valued counterpart used by tuple elaboration. -/
structure SupportedM2ItemsPairCoherence
    (start leftNext rightNext : Supply)
    (left right : GeneratedItems) where
  next_eq : leftNext = rightNext
  certificate : SupportedItemsAlignmentCertificate
    start leftNext left right

/-- Pairwise supported coherence for sibling expression lists. -/
def SupportedM2ItemsProperty (expressions : List Expr) : Prop :=
  ∀ {signature : Signature} {context : Context} {start : Supply}
      {leftItems rightItems : GeneratedItems}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      ElaboratesItems signature context expressions start leftItems leftNext →
        ElaboratesItems signature context expressions start rightItems rightNext →
          Nonempty (SupportedM2ItemsPairCoherence start leftNext rightNext
            leftItems rightItems)

/-- Supported coherence for a call fold whose two accumulated function
blocks may already differ.  Provenance is retained so that the next argument
is known to avoid aliases allocated by the accumulator, and conversely. -/
def SupportedM2CallProperty (arguments : List Expr) : Prop :=
  ∀ {signature : Signature} {context : Context}
      {outerStart start : Supply}
      {leftAccumulated rightAccumulated leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    outerStart.WellFormedFor context →
      outerStart.Le start →
      GeneratedSupportProvenance context outerStart start leftAccumulated →
      GeneratedSupportProvenance context outerStart start rightAccumulated →
      SupportedEntailedAlignmentCertificate outerStart start
        leftAccumulated rightAccumulated →
      ElaboratesCall signature context leftAccumulated arguments start
        leftGenerated leftNext →
      ElaboratesCall signature context rightAccumulated arguments start
        rightGenerated rightNext →
      Nonempty (SupportedM2PairCoherence outerStart leftNext rightNext
        leftGenerated rightGenerated)

namespace SupportedM2PairProperty

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

/-- Variable leaves are deterministic once the common context lookup is
fixed. -/
theorem var (index : Nat) : SupportedM2PairProperty (.var index) := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext _wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | @var _ _ _ leftScheme leftLookup =>
    cases rightElaboration with
    | @var _ _ _ rightScheme rightLookup =>
      have schemeEquality : leftScheme = rightScheme := by
        rw [leftLookup] at rightLookup
        exact Option.some.inj rightLookup
      subst rightScheme
      exact ⟨
        { next_eq := rfl
          certificate := SupportedEntailedAlignmentCertificate.refl
            start (leftScheme.instantiate start).2 _ }⟩

/-- Integer literals elaborate literally. -/
theorem lit (value : Int) : SupportedM2PairProperty (.lit value) := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext _wellFormed leftElaboration rightElaboration
  cases leftElaboration
  cases rightElaboration
  exact ⟨
    { next_eq := rfl
      certificate := SupportedEntailedAlignmentCertificate.refl
        start start _ }⟩

/-- The anonymous matcher leaf allocates the same single ordinary type
variable in every derivation. -/
theorem something : SupportedM2PairProperty .something := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext _wellFormed leftElaboration rightElaboration
  cases leftElaboration
  cases rightElaboration
  exact ⟨
    { next_eq := rfl
      certificate := SupportedEntailedAlignmentCertificate.refl
        start (start.nextTy 1) _ }⟩

/-- Lambda composition rebases the body-local hidden interval to the outer
start and inserts the common fresh parameter type. -/
theorem lam {body : Expr}
    (bodyProperty : SupportedM2PairProperty body) :
    SupportedM2PairProperty (.lam body) := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | lam leftBodyElaboration =>
    cases rightElaboration with
    | lam rightBodyElaboration =>
      have bodyWellFormed := wellFormed.monomorphic_cons_nextTy
      obtain ⟨bodyResult⟩ := bodyProperty bodyWellFormed
        leftBodyElaboration rightBodyElaboration
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

/-- Application composition joins the two sequentially fresh alias ranges.
The source support bounds provide all four cross-avoidance facts required by
the support-strengthened application certificate. -/
theorem app {function argument : Expr}
    (functionProperty : SupportedM2PairProperty function)
    (argumentProperty : SupportedM2PairProperty argument) :
    SupportedM2PairProperty (.app function argument) := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | @app _ _ _ _ leftFunction leftAfterFunction leftArgument
      leftAfterArgument leftFunctionElaboration leftArgumentElaboration =>
    cases rightElaboration with
    | @app _ _ _ _ rightFunction rightAfterFunction rightArgument
        rightAfterArgument rightFunctionElaboration rightArgumentElaboration =>
      obtain ⟨functionResult⟩ := functionProperty wellFormed
        leftFunctionElaboration rightFunctionElaboration
      cases functionResult.next_eq
      obtain ⟨argumentResult⟩ := argumentProperty
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
        Elaborates.sequential_crossAvoidance
          leftFunctionElaboration leftArgumentElaboration wellFormed
          functionResult.certificate.hiddenFresh
          argumentResult.certificate.hiddenFresh
      obtain ⟨rightArgumentAvoids, rightFunctionAvoids⟩ :=
        Elaborates.sequential_crossAvoidance
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
            (by
              change GeneratedAvoids functionResult.certificate.hidden _
              exact leftArgumentAvoids)
            (by
              change GeneratedAvoids functionResult.certificate.hidden _
              exact rightArgumentAvoids)
            (by
              change GeneratedAvoids argumentResult.certificate.hidden _
              exact leftFunctionAvoids)
            (by
              change GeneratedAvoids argumentResult.certificate.hidden _
              exact rightFunctionAvoids)
            (by
              change TypeAvoids functionResult.certificate.hidden _
              exact functionDomainAvoids)
            (by
              change TypeAvoids functionResult.certificate.hidden _
              exact functionTargetAvoids)
            (by
              change TypeAvoids argumentResult.certificate.hidden _
              exact argumentDomainAvoids)
            (by
              change TypeAvoids argumentResult.certificate.hidden _
              exact argumentTargetAvoids)
            (by
              change ∀ candidate,
                candidate ∈ functionResult.certificate.hidden →
                  candidate ∉ argumentResult.certificate.hidden
              exact freshIntervals_disjoint
                functionResult.certificate.hiddenFresh
                argumentResult.certificate.hiddenFresh) }⟩

/-- Empty sibling lists are literally identical. -/
theorem itemsNil : SupportedM2ItemsProperty [] := by
  intro signature context start leftItems rightItems leftNext rightNext
    _wellFormed leftElaboration rightElaboration
  cases leftElaboration
  cases rightElaboration
  exact ⟨
    { next_eq := rfl
      certificate := SupportedItemsAlignmentCertificate.refl
        start start GeneratedItems.nil }⟩

/-- Sequential list composition is the list analogue of application
composition. -/
theorem itemsCons {item : Expr} {items : List Expr}
    (itemProperty : SupportedM2PairProperty item)
    (itemsProperty : SupportedM2ItemsProperty items) :
    SupportedM2ItemsProperty (item :: items) := by
  intro signature context start leftItems rightItems leftNext rightNext
    wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | @cons _ _ _ _ leftItem leftAfterItem leftTail leftTailNext
      leftItemElaboration leftTailElaboration =>
    cases rightElaboration with
    | @cons _ _ _ _ rightItem rightAfterItem rightTail rightTailNext
        rightItemElaboration rightTailElaboration =>
      obtain ⟨itemResult⟩ := itemProperty wellFormed
        leftItemElaboration rightItemElaboration
      cases itemResult.next_eq
      obtain ⟨tailResult⟩ := itemsProperty
        (wellFormed.mono leftItemElaboration.supply_le_next)
        leftTailElaboration rightTailElaboration
      cases tailResult.next_eq
      let itemCertificate := itemResult.certificate.rebase
        (itemResult.certificate.hiddenFresh.widen
          (Supply.le_refl start) leftTailElaboration.supply_le_next)
      let tailCertificate := tailResult.certificate.rebase
        (tailResult.certificate.hiddenFresh.widen
          leftItemElaboration.supply_le_next (Supply.le_refl leftNext))
      obtain ⟨leftTailAvoids, leftItemAvoids⟩ :=
        ElaboratesItems.cons_crossAvoidance
          leftItemElaboration leftTailElaboration wellFormed
          itemResult.certificate.hiddenFresh
          tailResult.certificate.hiddenFresh
      obtain ⟨rightTailAvoids, rightItemAvoids⟩ :=
        ElaboratesItems.cons_crossAvoidance
          rightItemElaboration rightTailElaboration wellFormed
          itemResult.certificate.hiddenFresh
          tailResult.certificate.hiddenFresh
      exact ⟨
        { next_eq := rfl
          certificate := SupportedItemsAlignmentCertificate.itemsCons
            itemCertificate tailCertificate
            (by
              change GeneratedItemsAvoid itemResult.certificate.hidden _
              exact leftTailAvoids)
            (by
              change GeneratedItemsAvoid itemResult.certificate.hidden _
              exact rightTailAvoids)
            (by
              change GeneratedAvoids tailResult.certificate.hidden _
              exact leftItemAvoids)
            (by
              change GeneratedAvoids tailResult.certificate.hidden _
              exact rightItemAvoids)
            (by
              change ∀ candidate, candidate ∈ itemResult.certificate.hidden →
                candidate ∉ tailResult.certificate.hidden
              exact freshIntervals_disjoint
                itemResult.certificate.hiddenFresh
                tailResult.certificate.hiddenFresh) }⟩

/-- A tuple merely changes the flat items view to a generated product. -/
theorem tuple {items : List Expr}
    (itemsProperty : SupportedM2ItemsProperty items) :
    SupportedM2PairProperty (.tuple items) := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | tuple leftItemsElaboration =>
    cases rightElaboration with
    | tuple rightItemsElaboration =>
      obtain ⟨itemsResult⟩ := itemsProperty wellFormed
        leftItemsElaboration rightItemsElaboration
      exact ⟨
        { next_eq := itemsResult.next_eq
          certificate := itemsResult.certificate.itemsTuple }⟩

/-- A call with no remaining arguments returns its accumulated block. -/
theorem callNil : SupportedM2CallProperty [] := by
  intro signature context outerStart start leftAccumulated rightAccumulated
    leftGenerated rightGenerated leftNext rightNext _wellFormed _outerToStart
    _leftProvenance _rightProvenance accumulatedCertificate
    leftElaboration rightElaboration
  cases leftElaboration
  cases rightElaboration
  exact ⟨
    { next_eq := rfl
      certificate := accumulatedCertificate }⟩

/-- One call-fold step combines the accumulated function block with the next
argument, then passes the enlarged supported certificate to the tail. -/
theorem callCons {argument : Expr} {arguments : List Expr}
    (argumentProperty : SupportedM2PairProperty argument)
    (argumentsProperty : SupportedM2CallProperty arguments) :
    SupportedM2CallProperty (argument :: arguments) := by
  intro signature context outerStart start leftAccumulated rightAccumulated
    leftGenerated rightGenerated leftNext rightNext wellFormed outerToStart
    leftProvenance rightProvenance accumulatedCertificate
    leftElaboration rightElaboration
  cases leftElaboration with
  | @cons _ _ _ _ _ leftArgument leftAfterArgument _ _
      leftArgumentElaboration leftRestElaboration =>
    cases rightElaboration with
    | @cons _ _ _ _ _ rightArgument rightAfterArgument _ _
        rightArgumentElaboration rightRestElaboration =>
      obtain ⟨argumentResult⟩ := argumentProperty
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
          leftArgumentElaboration.supportProvenance.scopedByInitialSupply
          wellFormed (Supply.le_refl start)
      have rightArgumentAvoids : GeneratedAvoids
          accumulatedCertificate.hidden rightArgument :=
        VariablesScopedBy.avoids_earlier
          accumulatedCertificate.hiddenFresh
          rightArgumentElaboration.supportProvenance.scopedByInitialSupply
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
            exact Nat.le_add_right _ _)
      let appliedCertificate := accumulatedWide.app argumentWide
        (.var ⟨leftAfterArgument.ty⟩)
        (.var ⟨leftAfterArgument.ty + 1⟩)
        (by
          change GeneratedAvoids accumulatedCertificate.hidden _
          exact leftArgumentAvoids)
        (by
          change GeneratedAvoids accumulatedCertificate.hidden _
          exact rightArgumentAvoids)
        (by
          change GeneratedAvoids argumentResult.certificate.hidden _
          exact leftAccumulatedAvoids)
        (by
          change GeneratedAvoids argumentResult.certificate.hidden _
          exact rightAccumulatedAvoids)
        (by
          change TypeAvoids accumulatedCertificate.hidden _
          exact accumulatedDomainAvoids)
        (by
          change TypeAvoids accumulatedCertificate.hidden _
          exact accumulatedTargetAvoids)
        (by
          change TypeAvoids argumentResult.certificate.hidden _
          exact argumentDomainAvoids)
        (by
          change TypeAvoids argumentResult.certificate.hidden _
          exact argumentTargetAvoids)
        (by
          change ∀ candidate, candidate ∈ accumulatedCertificate.hidden →
            candidate ∉ argumentResult.certificate.hidden
          exact freshIntervals_disjoint accumulatedCertificate.hiddenFresh
            argumentResult.certificate.hiddenFresh)
      have leftAppliedProvenance : GeneratedSupportProvenance context
          outerStart (leftAfterArgument.nextTy 2)
          (Generated.fromApp leftAccumulated leftArgument
            (.var ⟨leftAfterArgument.ty⟩)
            (.var ⟨leftAfterArgument.ty + 1⟩)) := by
        simpa [Generated.fromApp] using
          supportProvenance_fromApp outerToStart leftArgumentElaboration
            leftProvenance leftArgumentElaboration.supportProvenance
      have rightAppliedProvenance : GeneratedSupportProvenance context
          outerStart (leftAfterArgument.nextTy 2)
          (Generated.fromApp rightAccumulated rightArgument
            (.var ⟨leftAfterArgument.ty⟩)
            (.var ⟨leftAfterArgument.ty + 1⟩)) := by
        simpa [Generated.fromApp] using
          supportProvenance_fromApp outerToStart rightArgumentElaboration
            rightProvenance rightArgumentElaboration.supportProvenance
      exact argumentsProperty wellFormed outerToNext
        leftAppliedProvenance rightAppliedProvenance appliedCertificate
        leftRestElaboration rightRestElaboration

/-- Constructor calls start from the same closed scheme instance and then
use the generic call-fold coherence theorem. -/
theorem ctor (constructor : DataCtor) {arguments : List Expr}
    (argumentsProperty : SupportedM2CallProperty arguments) :
    SupportedM2PairProperty (.ctor constructor arguments) := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | @ctor _ _ _ leftScheme _ _ _ leftClosed leftLookup _ leftCall =>
    rename_i leftClosedProof
    cases rightElaboration with
    | @ctor _ _ _ rightScheme _ _ _ rightClosed rightLookup _ rightCall =>
      rename_i rightClosedProof
      have schemeEquality : leftScheme = rightScheme := by
        rw [leftClosed] at rightClosed
        exact Option.some.inj rightClosed
      subst rightScheme
      exact argumentsProperty wellFormed
        (by simp [Supply.Le, Scheme.instantiate])
        (supportProvenance_closed_instantiate leftClosedProof)
        (supportProvenance_closed_instantiate rightClosedProof)
        (SupportedEntailedAlignmentCertificate.refl start
          (leftScheme.instantiate start).2 _)
        leftCall rightCall

/-- Primitive calls use the same closed-scheme call fold. -/
theorem prim (operation : PrimOp) {arguments : List Expr}
    (argumentsProperty : SupportedM2CallProperty arguments) :
    SupportedM2PairProperty (.prim operation arguments) := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | @prim _ _ _ leftScheme _ _ _ leftClosed leftLookup _ leftCall =>
    rename_i leftClosedProof
    cases rightElaboration with
    | @prim _ _ _ rightScheme _ _ _ rightClosed rightLookup _ rightCall =>
      rename_i rightClosedProof
      have schemeEquality : leftScheme = rightScheme := by
        rw [leftClosed] at rightClosed
        exact Option.some.inj rightClosed
      subst rightScheme
      exact argumentsProperty wellFormed
        (by simp [Supply.Le, Scheme.instantiate])
        (supportProvenance_closed_instantiate leftClosedProof)
        (supportProvenance_closed_instantiate rightClosedProof)
        (SupportedEntailedAlignmentCertificate.refl start
          (leftScheme.instantiate start).2 _)
        leftCall rightCall

/-- Conditionals are the fixed closed three-argument call. -/
theorem ifE {condition thenBranch elseBranch : Expr}
    (argumentsProperty : SupportedM2CallProperty
      [condition, thenBranch, elseBranch]) :
    SupportedM2PairProperty (.ifE condition thenBranch elseBranch) := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | ifE leftCall =>
    cases rightElaboration with
    | ifE rightCall =>
      exact argumentsProperty wellFormed
        (by simp [Supply.Le, Scheme.instantiate])
        (supportProvenance_closed_instantiate conditionalScheme_closed)
        (supportProvenance_closed_instantiate conditionalScheme_closed)
        (SupportedEntailedAlignmentCertificate.refl start
          (conditionalScheme.instantiate start).2 _)
        leftCall rightCall

/-- Fold pointwise expression coherence into sibling-list coherence. -/
theorem itemsOfEach {items : List Expr}
    (each : ∀ item, item ∈ items → SupportedM2PairProperty item) :
    SupportedM2ItemsProperty items := by
  induction items with
  | nil => exact itemsNil
  | cons item items induction =>
      exact itemsCons (each item (by simp))
        (induction (by
          intro tail tailMember
          exact each tail (by simp [tailMember])))

/-- Fold pointwise expression coherence into call-fold coherence. -/
theorem callOfEach {arguments : List Expr}
    (each : ∀ argument, argument ∈ arguments →
      SupportedM2PairProperty argument) :
    SupportedM2CallProperty arguments := by
  induction arguments with
  | nil => exact callNil
  | cons argument arguments induction =>
      exact callCons (each argument (by simp))
        (induction (by
          intro tail tailMember
          exact each tail (by simp [tailMember])))

end SupportedM2PairProperty

/-- The simultaneous result required for two derivations of one source
expression.  `certificate` is the acceptance-level semantic comparison;
`closureAlignment` is the stronger recursive invariant used by a surrounding
`letE`. -/
structure FullM2PairCoherence
    (start leftNext rightNext : Supply)
    (left right : Generated) (context : Context) where
  next_eq : leftNext = rightNext
  certificate : SupportedEntailedAlignmentCertificate
    start leftNext left right
  closureAlignment :
    ∀ (leftClosure : PrincipalBlockClosure left)
        (rightClosure : PrincipalBlockClosure right),
      leftClosure.Absorbing → rightClosure.Absorbing →
        Nonempty (ProvenancedFreshClosureAlignment
          leftClosure rightClosure context leftNext)

namespace FullM2PairCoherence

/-- Upgrade the constructor-compositional core using the single generic
closure-alignment theorem. -/
theorem ofSupported
    (closureComplete : SupportedCertificateClosureAlignmentComplete)
    {signature : Signature} {context : Context} {expression : Expr}
    {start leftNext rightNext : Supply} {left right : Generated}
    (wellFormed : start.WellFormedFor context)
    (leftElaboration : Elaborates signature context expression start
      left leftNext)
    (rightElaboration : Elaborates signature context expression start
      right rightNext)
    (supported : SupportedM2PairCoherence start leftNext rightNext
      left right) :
    Nonempty (FullM2PairCoherence start leftNext rightNext
      left right context) := by
  cases supported.next_eq
  exact ⟨
    { next_eq := rfl
      certificate := supported.certificate
      closureAlignment := closureComplete wellFormed leftElaboration
        rightElaboration supported.certificate }⟩

/-- The semantic certificate component, packaged in the existential form
used by the existing `letE` handler. -/
theorem entailedAlignment
    {start leftNext rightNext : Supply} {left right : Generated}
    {context : Context}
    (coherence : FullM2PairCoherence start leftNext rightNext left right
      context) :
    leftNext = rightNext ∧
      Nonempty (EntailedAlignmentCertificate start leftNext left right) :=
  ⟨coherence.next_eq, ⟨coherence.certificate.toCertificate⟩⟩

/-- Any two absorbing principal closures of a coherent pair have mutually
substitutable targets. -/
theorem closureTargets_mutualInstances
    {start leftNext rightNext : Supply} {left right : Generated}
    {context : Context}
    (coherence : FullM2PairCoherence start leftNext rightNext left right
      context)
    (leftClosure : PrincipalBlockClosure left)
    (rightClosure : PrincipalBlockClosure right)
    (leftAbsorbing : leftClosure.Absorbing)
    (rightAbsorbing : rightClosure.Absorbing) :
    IsInstance leftClosure.target rightClosure.target ∧
      IsInstance rightClosure.target leftClosure.target := by
  obtain ⟨alignment⟩ := coherence.closureAlignment leftClosure
    rightClosure leftAbsorbing rightAbsorbing
  exact alignment.alignment.alignment.targets_mutualInstances

/-- Acceptance is preserved and reflected in every frame avoiding the
locally hidden alias endpoints. -/
theorem blockAccepts_iff
    {start leftNext rightNext : Supply} {left right : Generated}
    {context : Context}
    (coherence : FullM2PairCoherence start leftNext rightNext left right
      context)
    (frame : GeneratedFrame)
    (frameAvoids : frame.Avoids coherence.certificate.hidden) :
    BlockAccepts (frame.plug left) ↔ BlockAccepts (frame.plug right) :=
  coherence.certificate.toCertificate.blockAccepts_iff frame frameAvoids

end FullM2PairCoherence

/-- Coherence for all pairs of well-formed derivations of one fixed source
expression.  Quantifying over signatures, contexts, and supplies here makes
the induction hypothesis reusable inside lambda and `letE` body contexts. -/
def FullM2PairProperty (expression : Expr) : Prop :=
  ∀ {signature : Signature} {context : Context} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      Elaborates signature context expression start
          leftGenerated leftNext →
        Elaborates signature context expression start
            rightGenerated rightNext →
          Nonempty (FullM2PairCoherence start leftNext rightNext
            leftGenerated rightGenerated context)

/-- Apply the generic closure theorem once, after ordinary constructor
composition has produced a supported semantic certificate. -/
theorem SupportedM2PairProperty.toFull
    (closureComplete : SupportedCertificateClosureAlignmentComplete)
    {expression : Expr}
    (supported : SupportedM2PairProperty expression) :
    FullM2PairProperty expression := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  obtain ⟨result⟩ := supported wellFormed leftElaboration rightElaboration
  exact FullM2PairCoherence.ofSupported closureComplete wellFormed
    leftElaboration rightElaboration result

/-- Forget the generic closure component while retaining the supported
semantic certificate. -/
theorem FullM2PairProperty.toSupported
    {expression : Expr} (full : FullM2PairProperty expression) :
    SupportedM2PairProperty expression := by
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  obtain ⟨result⟩ := full wellFormed leftElaboration rightElaboration
  exact ⟨
    { next_eq := result.next_eq
      certificate := result.certificate }⟩

/-- Concrete recursive core of the `letE` case.  Once the value children
have full coherence, their future-fixed closure alignment transports the
left body derivation to the right closed context without changing its source
expression or numeric supplies.  The body induction hypothesis can then be
applied to two derivations in literally the same context.

The remaining outer `letE` work is purely generated-block composition:
combine the returned body coherence with the two interface equation lists. -/
theorem FullM2PairProperty.transportLetBody
    {value body : Expr}
    (bodyCoherent : FullM2PairProperty body)
    {signature : Signature} {context : Context} {start afterValue : Supply}
    {leftValue rightValue leftBody rightBody : Generated}
    {leftNext rightNext : Supply}
    (wellFormed : start.WellFormedFor context)
    (leftValueElaboration : Elaborates signature context value start
      leftValue afterValue)
    (rightValueElaboration : Elaborates signature context value start
      rightValue afterValue)
    (valueCoherence : FullM2PairCoherence start afterValue afterValue
      leftValue rightValue context)
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (leftAbsorbing : leftClosure.Absorbing)
    (rightAbsorbing : rightClosure.Absorbing)
    (leftBodyElaboration : Elaborates signature
      ((context.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        context.applyFree leftClosure.substitution)
      body
      (afterValue.join
        (context.applyFree leftClosure.substitution).initialSupply)
      leftBody leftNext)
    (rightBodyElaboration : Elaborates signature
      ((context.applyFree rightClosure.substitution).generalize
          rightClosure.target ::
        context.applyFree rightClosure.substitution)
      body
      (afterValue.join
        (context.applyFree rightClosure.substitution).initialSupply)
      rightBody rightNext) :
    ∃ alignment : ProvenancedFreshClosureAlignment leftClosure rightClosure
        context afterValue,
      Elaborates signature
          ((context.applyFree rightClosure.substitution).generalize
              rightClosure.target ::
            context.applyFree rightClosure.substitution)
        body afterValue
        (ElaborationRenaming.renameGenerated
          alignment.alignment.alignment.rho leftBody) leftNext ∧
      Nonempty (FullM2PairCoherence afterValue leftNext rightNext
        (ElaborationRenaming.renameGenerated
          alignment.alignment.alignment.rho leftBody)
        rightBody
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)) := by
  obtain ⟨alignment⟩ := valueCoherence.closureAlignment
    leftClosure rightClosure leftAbsorbing rightAbsorbing
  have leftBodyStart := leftValueElaboration.letBodySupply_eq
    leftClosure leftAbsorbing wellFormed
  have rightBodyStart := rightValueElaboration.letBodySupply_eq
    rightClosure rightAbsorbing wellFormed
  have leftBodyAtFinish := leftBodyElaboration
  rw [leftBodyStart] at leftBodyAtFinish
  have rightBodyAtFinish := rightBodyElaboration
  rw [rightBodyStart] at rightBodyAtFinish
  have leftClosedWellFormed : afterValue.WellFormedFor
      (context.applyFree leftClosure.substitution) :=
    leftValueElaboration.closedContext_initialSupply_le
      leftClosure leftAbsorbing wellFormed
  have leftBodyWellFormed : afterValue.WellFormedFor
      ((context.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        context.applyFree leftClosure.substitution) :=
    leftClosedWellFormed.generalized_cons leftClosure.target
  have rightClosedWellFormed : afterValue.WellFormedFor
      (context.applyFree rightClosure.substitution) :=
    rightValueElaboration.closedContext_initialSupply_le
      rightClosure rightAbsorbing wellFormed
  have rightBodyWellFormed : afterValue.WellFormedFor
      ((context.applyFree rightClosure.substitution).generalize
          rightClosure.target ::
        context.applyFree rightClosure.substitution) :=
    rightClosedWellFormed.generalized_cons rightClosure.target
  have transported := leftBodyAtFinish.transport_of_fixesAtOrAbove
    leftBodyWellFormed alignment.alignment.fixesAtOrAbove
  have bodyContextExact :
      ElaborationRenaming.renameContext alignment.alignment.alignment.rho
          ((context.applyFree leftClosure.substitution).generalize
              leftClosure.target ::
            context.applyFree leftClosure.substitution) =
        ((context.applyFree rightClosure.substitution).generalize
              rightClosure.target ::
            context.applyFree rightClosure.substitution) := by
    change
      (((context.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        context.applyFree leftClosure.substitution).map
        (Scheme.applyFree alignment.alignment.alignment.rho.substitution)) = _
    exact alignment.alignment.bodyContext_exact
  rw [bodyContextExact] at transported
  refine ⟨alignment, transported, ?_⟩
  exact bodyCoherent rightBodyWellFormed transported rightBodyAtFinish

/-- The full pairwise source-coherence statement. -/
def FullM2Coherence : Prop :=
  ∀ expression, FullM2PairProperty expression

/-- An abstract `letE` step for the final source induction.  Its induction
hypothesis contains every strictly smaller expression, not only the direct
value and body children.  This is the useful form for nested expression lists
and accumulated calls. -/
def FullM2LetStep : Prop :=
  ∀ (value body : Expr),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.letE value body).complexity →
        FullM2PairProperty smaller) →
      FullM2PairProperty (.letE value body)

/-- The non-recursive generated-block obligation left after
`FullM2PairProperty.transportLetBody`.  At this point the body derivations
already share the right closed context and the body induction hypothesis has
already been applied.  An implementation only has to combine the two
interface equation lists, the value closure alignment, and the returned body
coherence into the outer `fromLet` coherence. -/
def FullM2LetAssemblyHandler : Prop :=
  ∀ {signature : Signature} {context : Context} {value body : Expr}
      {start afterValue : Supply}
      {leftValue rightValue leftBody rightBody : Generated}
      {leftNext rightNext : Supply}
      (_wellFormed : start.WellFormedFor context)
      (_leftValueElaboration : Elaborates signature context value start
        leftValue afterValue)
      (_rightValueElaboration : Elaborates signature context value start
        rightValue afterValue)
      (_valueCoherence : FullM2PairCoherence start afterValue afterValue
        leftValue rightValue context)
      (leftClosure : PrincipalBlockClosure leftValue)
      (rightClosure : PrincipalBlockClosure rightValue)
      (_leftAbsorbing : leftClosure.Absorbing)
      (_rightAbsorbing : rightClosure.Absorbing)
      (_leftBodyElaboration : Elaborates signature
        ((context.applyFree leftClosure.substitution).generalize
            leftClosure.target ::
          context.applyFree leftClosure.substitution)
        body
        (afterValue.join
          (context.applyFree leftClosure.substitution).initialSupply)
        leftBody leftNext)
      (_rightBodyElaboration : Elaborates signature
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)
        body
        (afterValue.join
          (context.applyFree rightClosure.substitution).initialSupply)
        rightBody rightNext)
      (alignment : ProvenancedFreshClosureAlignment leftClosure rightClosure
        context afterValue)
      (_transportedBody : Elaborates signature
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)
        body afterValue
        (ElaborationRenaming.renameGenerated
          alignment.alignment.alignment.rho leftBody) leftNext)
      (_bodyCoherence : FullM2PairCoherence afterValue leftNext rightNext
        (ElaborationRenaming.renameGenerated
          alignment.alignment.alignment.rho leftBody)
        rightBody
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)),
    Nonempty (FullM2PairCoherence start leftNext rightNext
      (Generated.fromLet
        (context.interfaceEquations leftClosure.substitution) leftBody)
      (Generated.fromLet
        (context.interfaceEquations rightClosure.substitution) rightBody)
      context)

/-- Exact semantic bridge.  This premise retains both source body
derivations; their support bounds are needed to prove that the closure
renaming is fixed under the combined interface reference. -/
def FullM2LetSupportedAssemblyBridge : Prop :=
  ∀ {signature : Signature} {context : Context} {value body : Expr}
      {start afterValue : Supply}
      {leftValue rightValue leftBody rightBody : Generated}
      {leftNext rightNext : Supply}
      (_wellFormed : start.WellFormedFor context)
      (_leftValueElaboration : Elaborates signature context value start
        leftValue afterValue)
      (_rightValueElaboration : Elaborates signature context value start
        rightValue afterValue)
      (_valueCoherence : FullM2PairCoherence start afterValue afterValue
        leftValue rightValue context)
      (leftClosure : PrincipalBlockClosure leftValue)
      (rightClosure : PrincipalBlockClosure rightValue)
      (_leftAbsorbing : leftClosure.Absorbing)
      (_rightAbsorbing : rightClosure.Absorbing)
      (_leftBodyElaboration : Elaborates signature
        ((context.applyFree leftClosure.substitution).generalize
            leftClosure.target ::
          context.applyFree leftClosure.substitution)
        body
        (afterValue.join
          (context.applyFree leftClosure.substitution).initialSupply)
        leftBody leftNext)
      (_rightBodyElaboration : Elaborates signature
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)
        body
        (afterValue.join
          (context.applyFree rightClosure.substitution).initialSupply)
        rightBody rightNext)
      (alignment : ProvenancedFreshClosureAlignment leftClosure rightClosure
        context afterValue)
      (_transportedBody : Elaborates signature
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)
        body afterValue
        (ElaborationRenaming.renameGenerated
          alignment.alignment.alignment.rho leftBody) leftNext)
      (_bodyCoherence : FullM2PairCoherence afterValue leftNext rightNext
        (ElaborationRenaming.renameGenerated
          alignment.alignment.alignment.rho leftBody)
        rightBody
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)),
    Nonempty (SupportedM2PairCoherence start leftNext rightNext
      (Generated.fromLet
        (context.interfaceEquations leftClosure.substitution) leftBody)
      (Generated.fromLet
        (context.interfaceEquations rightClosure.substitution) rightBody))

/-- The semantic bridge becomes the full let handler by one uniform closure
upgrade on the two original outer `letE` derivations. -/
theorem fullM2LetAssemblyHandler_of_supportedBridge
    (closureComplete : SupportedCertificateClosureAlignmentComplete)
    (bridge : FullM2LetSupportedAssemblyBridge) :
    FullM2LetAssemblyHandler := by
  intro signature context value body start afterValue
    leftValue rightValue leftBody rightBody leftNext rightNext
    wellFormed leftValueElaboration rightValueElaboration valueCoherence
    leftClosure rightClosure leftAbsorbing rightAbsorbing
    leftBodyElaboration rightBodyElaboration alignment transportedBody
    bodyCoherence
  obtain ⟨supported⟩ := bridge wellFormed leftValueElaboration
    rightValueElaboration valueCoherence leftClosure rightClosure
    leftAbsorbing rightAbsorbing leftBodyElaboration rightBodyElaboration
    alignment transportedBody bodyCoherence
  let leftLet : Elaborates signature context (.letE value body) start
      (Generated.fromLet
        (context.interfaceEquations leftClosure.substitution) leftBody)
      leftNext :=
    .letE leftValueElaboration leftClosure leftAbsorbing leftBodyElaboration
  let rightLet : Elaborates signature context (.letE value body) start
      (Generated.fromLet
        (context.interfaceEquations rightClosure.substitution) rightBody)
      rightNext :=
    .letE rightValueElaboration rightClosure rightAbsorbing
      rightBodyElaboration
  exact FullM2PairCoherence.ofSupported closureComplete wellFormed
    leftLet rightLet supported

/-- The concrete recursive `letE` step, reduced to the non-recursive outer
block assembly handler above. -/
theorem fullM2LetStep_of_assembly
    (assemble : FullM2LetAssemblyHandler) : FullM2LetStep := by
  intro value body induction
  intro signature context start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  cases leftElaboration with
  | letE leftValueElaboration leftClosure leftAbsorbing
      leftBodyElaboration =>
    cases rightElaboration with
    | letE rightValueElaboration rightClosure rightAbsorbing
        rightBodyElaboration =>
      have valueProperty : FullM2PairProperty value :=
        induction value (by simp [Expr.complexity]; omega)
      obtain ⟨valueCoherence⟩ := valueProperty wellFormed
        leftValueElaboration rightValueElaboration
      cases valueCoherence.next_eq
      have bodyProperty : FullM2PairProperty body :=
        induction body (by simp [Expr.complexity]; omega)
      obtain ⟨alignment, transportedBody, ⟨bodyCoherence⟩⟩ :=
        bodyProperty.transportLetBody wellFormed
          leftValueElaboration rightValueElaboration valueCoherence
          leftClosure rightClosure leftAbsorbing rightAbsorbing
          leftBodyElaboration rightBodyElaboration
      exact assemble wellFormed leftValueElaboration rightValueElaboration
        valueCoherence leftClosure rightClosure leftAbsorbing rightAbsorbing
        leftBodyElaboration rightBodyElaboration alignment transportedBody
        bodyCoherence

/-- Composition of all source constructors other than `letE`.  Separating
this premise from `FullM2LetStep` isolates the representative-sensitive
`letE` assembly used by the completed proof. -/
def FullM2OrdinaryStep : Prop :=
  ∀ expression : Expr,
    (∀ value body, expression ≠ .letE value body) →
      (∀ smaller : Expr,
        smaller.complexity < expression.complexity →
          FullM2PairProperty smaller) →
        FullM2PairProperty expression

/-- Ordinary-constructor composition at the supported-certificate level.
This is the target of the mutual expression/items/call induction; closure
alignment is added only after the constructor result has been assembled. -/
def SupportedM2OrdinaryStep : Prop :=
  ∀ expression : Expr,
    (∀ value body, expression ≠ .letE value body) →
      (∀ smaller : Expr,
        smaller.complexity < expression.complexity →
          SupportedM2PairProperty smaller) →
        SupportedM2PairProperty expression

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

/-- All ordinary M2 constructors support certificate composition.
The later source constructors have no `Elaborates` constructor yet, so their
pair properties hold vacuously. -/
theorem supportedM2OrdinaryStep : SupportedM2OrdinaryStep := by
  intro expression notLet induction
  cases expression with
  | var index => exact SupportedM2PairProperty.var index
  | lit value => exact SupportedM2PairProperty.lit value
  | something => exact SupportedM2PairProperty.something
  | lam body =>
      exact SupportedM2PairProperty.lam
        (induction body (by simp [Expr.complexity]))
  | app function argument =>
      exact SupportedM2PairProperty.app
        (induction function (by simp [Expr.complexity]; omega))
        (induction argument (by simp [Expr.complexity]; omega))
  | tuple items =>
      apply SupportedM2PairProperty.tuple
      apply SupportedM2PairProperty.itemsOfEach
      intro item member
      exact induction item (by
        have smaller := expression_complexity_lt_list_succ member
        simpa [Expr.complexity] using smaller)
  | letE value body =>
      exact False.elim (notLet value body rfl)
  | ctor constructor arguments =>
      apply SupportedM2PairProperty.ctor constructor
      apply SupportedM2PairProperty.callOfEach
      intro argument member
      exact induction argument (by
        have smaller := expression_complexity_lt_list_succ member
        simpa [Expr.complexity] using smaller)
  | prim operation arguments =>
      apply SupportedM2PairProperty.prim operation
      apply SupportedM2PairProperty.callOfEach
      intro argument member
      exact induction argument (by
        have smaller := expression_complexity_lt_list_succ member
        simpa [Expr.complexity] using smaller)
  | ifE condition thenBranch elseBranch =>
      apply SupportedM2PairProperty.ifE
      apply SupportedM2PairProperty.callOfEach
      intro argument member
      exact induction argument (by
        have smaller := expression_complexity_lt_list_succ member
        simp [Expr.listComplexity] at smaller
        simp [Expr.complexity]
        omega)
  | fixE body =>
      intro signature context start leftGenerated rightGenerated
        leftNext rightNext wellFormed leftElaboration rightElaboration
      cases leftElaboration
  | matcher clauses =>
      intro signature context start leftGenerated rightGenerated
        leftNext rightNext wellFormed leftElaboration rightElaboration
      cases leftElaboration
  | matchAll target matcher pattern body =>
      intro signature context start leftGenerated rightGenerated
        leftNext rightNext wellFormed leftElaboration rightElaboration
      cases leftElaboration
  | matchFirst target matcher arms =>
      intro signature context start leftGenerated rightGenerated
        leftNext rightNext wellFormed leftElaboration rightElaboration
      cases leftElaboration

/-- A supported ordinary step becomes the full ordinary step through the
single generic closure theorem. -/
theorem fullM2OrdinaryStep_of_supported
    (closureComplete : SupportedCertificateClosureAlignmentComplete)
    (ordinary : SupportedM2OrdinaryStep) : FullM2OrdinaryStep := by
  intro expression notLet induction
  apply SupportedM2PairProperty.toFull closureComplete
  exact ordinary expression notLet (fun smaller smallerMeasure =>
    FullM2PairProperty.toSupported
      (induction smaller smallerMeasure))

/-- The minimal well-founded induction principle for the full M2 invariant.
No constructor-specific reasoning is hidden here: the ordinary and `letE`
steps are exactly the two explicit premises above. -/
theorem fullM2Coherence_of_steps
    (ordinary : FullM2OrdinaryStep)
    (letStep : FullM2LetStep) :
    FullM2Coherence := by
  intro expression
  apply (measure Expr.complexity).wf.induction expression
  intro current induction
  by_cases isLet : ∃ value body, current = .letE value body
  · obtain ⟨value, body, rfl⟩ := isLet
    exact letStep value body (fun smaller smallerMeasure =>
      induction smaller smallerMeasure)
  · exact ordinary current
      (by
        intro value body equality
        exact isLet ⟨value, body, equality⟩)
      (fun smaller smallerMeasure => induction smaller smallerMeasure)

/-- Final assembly endpoint: ordinary constructor composition plus the
non-recursive whole-`letE` block lemma imply full M2 coherence. -/
theorem fullM2Coherence_of_ordinary_and_letAssembly
    (ordinary : FullM2OrdinaryStep)
    (assemble : FullM2LetAssemblyHandler) :
    FullM2Coherence :=
  fullM2Coherence_of_steps ordinary
    (fullM2LetStep_of_assembly assemble)

/-- Fully factored endpoint used by the implementation: mutual ordinary
composition produces supported certificates, the generic closure theorem
upgrades them, and only the whole-`letE` assembly remains specialized. -/
theorem fullM2Coherence_of_supportedOrdinary_and_letAssembly
    (closureComplete : SupportedCertificateClosureAlignmentComplete)
    (ordinary : SupportedM2OrdinaryStep)
    (assemble : FullM2LetAssemblyHandler) :
    FullM2Coherence :=
  fullM2Coherence_of_ordinary_and_letAssembly
    (fullM2OrdinaryStep_of_supported closureComplete ordinary) assemble

/-- With ordinary constructor composition discharged above, only the generic
closure theorem and whole-let assembly remain as external obligations. -/
theorem fullM2Coherence_of_letAssembly
    (closureComplete : SupportedCertificateClosureAlignmentComplete)
    (assemble : FullM2LetAssemblyHandler) :
    FullM2Coherence :=
  fullM2Coherence_of_supportedOrdinary_and_letAssembly
    closureComplete supportedM2OrdinaryStep assemble

/-- The exact semantic bridge plus the generic closure theorem imply full
M2 coherence. -/
theorem fullM2Coherence_of_supportedLetBridge
    (closureComplete : SupportedCertificateClosureAlignmentComplete)
    (bridge : FullM2LetSupportedAssemblyBridge) :
    FullM2Coherence :=
  fullM2Coherence_of_letAssembly closureComplete
    (fullM2LetAssemblyHandler_of_supportedBridge closureComplete bridge)

namespace FullM2Coherence

/-- Full coherence supplies the semantic `letE` handler consumed by the
existing structural source-composition theorem. -/
theorem entailedLetAlignmentHandler
    (coherent : FullM2Coherence) :
    EntailedAlignmentCertificate.EntailedLetAlignmentHandler := by
  intro signature context value body start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  obtain ⟨result⟩ := coherent (.letE value body) wellFormed
    leftElaboration rightElaboration
  exact result.entailedAlignment

/-- Consequently, full coherence also supplies the older contextual
comparison handler without exposing its internal alias sequences. -/
theorem letComparisonHandler
    (coherent : FullM2Coherence) : LetComparisonHandler :=
  EntailedAlignmentCertificate.letComparisonHandler
    coherent.entailedLetAlignmentHandler

/-- The closure-locality component is exactly the recursive invariant used
by the existing representative-sensitive `letE` development. -/
theorem closureAlignedElaborations
    (coherent : FullM2Coherence) : ClosureAlignedElaborations := by
  intro signature context expression start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  obtain ⟨result⟩ := coherent expression wellFormed
    leftElaboration rightElaboration
  refine ⟨result.next_eq, ?_⟩
  intro leftClosure rightClosure leftAbsorbing rightAbsorbing
  obtain ⟨alignment⟩ := result.closureAlignment leftClosure rightClosure
    leftAbsorbing rightAbsorbing
  exact ⟨alignment.toFreshClosureAlignment⟩

/-- Supply agreement is available independently of closure choices. -/
theorem next_eq
    (coherent : FullM2Coherence)
    {signature : Signature} {context : Context} {expression : Expr}
    {start : Supply} {leftGenerated rightGenerated : Generated}
    {leftNext rightNext : Supply}
    (wellFormed : start.WellFormedFor context)
    (leftElaboration : Elaborates signature context expression start
      leftGenerated leftNext)
    (rightElaboration : Elaborates signature context expression start
      rightGenerated rightNext) :
    leftNext = rightNext := by
  obtain ⟨result⟩ := coherent expression wellFormed
    leftElaboration rightElaboration
  exact result.next_eq

/-- Target-level endpoint of the simultaneous induction result. -/
theorem closureTargets_mutualInstances
    (coherent : FullM2Coherence)
    {signature : Signature} {context : Context} {expression : Expr}
    {start : Supply} {leftGenerated rightGenerated : Generated}
    {leftNext rightNext : Supply}
    (wellFormed : start.WellFormedFor context)
    (leftElaboration : Elaborates signature context expression start
      leftGenerated leftNext)
    (rightElaboration : Elaborates signature context expression start
      rightGenerated rightNext)
    (leftClosure : PrincipalBlockClosure leftGenerated)
    (rightClosure : PrincipalBlockClosure rightGenerated)
    (leftAbsorbing : leftClosure.Absorbing)
    (rightAbsorbing : rightClosure.Absorbing) :
    IsInstance leftClosure.target rightClosure.target ∧
      IsInstance rightClosure.target leftClosure.target := by
  obtain ⟨result⟩ := coherent expression wellFormed
    leftElaboration rightElaboration
  exact result.closureTargets_mutualInstances leftClosure rightClosure
    leftAbsorbing rightAbsorbing

end FullM2Coherence

end TypePM.Source
