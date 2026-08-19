import TypePM.Source.ScopedGeneratedEquivalence

/-!
# Scoped composition of source elaborations

The ordinary source constructors compose scope-aware generated comparisons
without any representative-coherence assumption.  A `letE` changes the body
context through a chosen principal closure, so the one remaining comparison
step is exposed as an explicit handler rather than hidden in the theorem.
-/

namespace TypePM.Source

/-- The exact representative-sensitive obligation left at a source `let`.
No existence claim is made here: a caller must compare the two complete
`letE` elaborations, including their possibly different closed contexts. -/
def LetComparisonHandler : Prop :=
  ∀ {context : Context} {value body : Expr} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      Elaborates context (.letE value body) start leftGenerated leftNext →
        Elaborates context (.letE value body) start rightGenerated rightNext →
          ScopedGeneratedComparison start leftNext rightNext
            leftGenerated rightGenerated

private theorem scopedGeneratedComparison_refl
    (start next : Supply) (generated : Generated) :
    ScopedGeneratedComparison start next next generated generated := by
  exact ⟨rfl, [], VariablesFreshIn.nil _ _,
    Generated.ScopedContextualEquivalent.refl [] generated⟩

private theorem scopedItemsComparison_refl
    (start next : Supply) (generated : GeneratedItems) :
    ScopedItemsComparison start next next generated generated := by
  exact ⟨rfl, [], VariablesFreshIn.nil _ _,
    GeneratedItems.ScopedContextualEquivalent.refl [] generated⟩

/-- A lambda body's starting supply covers both the outer context and its
fresh monomorphic parameter. -/
private theorem lamBody_wellFormed
    {context : Context} {start : Supply}
    (wellFormed : start.WellFormedFor context) :
    (start.nextTy 1).WellFormedFor
      (.mono (.var ⟨start.ty⟩) :: context) := by
  simp only [Supply.WellFormedFor, Context.initialSupply, Supply.Le,
    List.flatMap_cons]
  constructor
  · apply TyVar.next_le_of_forall_lt
    intro index member
    rcases List.mem_append.mp member with head | tail
    · have equality : index = ⟨start.ty⟩ := by
        change index ∈ dedupFirst [⟨start.ty⟩] at head
        simpa using (mem_dedupFirst.mp head)
      subst index
      simp [Supply.nextTy]
    · have below := Context.freeTy_index_lt_initialSupply
          ((mem_dedupFirst).2 tail)
      simp only [Supply.WellFormedFor, Supply.Le] at wellFormed
      simp only [Supply.nextTy]
      omega
  · apply CapVar.next_le_of_forall_lt
    intro index member
    rcases List.mem_append.mp member with head | tail
    · change index ∈ dedupFirst [] at head
      simpa using (mem_dedupFirst.mp head)
    · have below := Context.freeCap_index_lt_initialSupply
          ((mem_dedupFirst).2 tail)
      simp only [Supply.WellFormedFor, Supply.Le] at wellFormed
      simp only [Supply.nextTy]
      omega

private theorem VariablesFreshIn.typeAvoids_ty_of_finish_le
    {start finish : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn start finish hidden)
    {index : TyVar} (finishLe : finish.ty ≤ index.index) :
    TypeAvoids hidden (.var index) := by
  intro candidate member hiddenMember
  have equality : candidate = .ty index := by
    simpa [Ty.unificationVars] using member
  subst candidate
  have range := fresh (.ty index) hiddenMember
  exact (Nat.not_lt_of_ge finishLe range.2)

private theorem VariablesFreshIn.typeAvoids_ty_of_lt_start
    {start finish : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn start finish hidden)
    {index : TyVar} (indexLt : index.index < start.ty) :
    TypeAvoids hidden (.var index) := by
  intro candidate member hiddenMember
  have equality : candidate = .ty index := by
    simpa [Ty.unificationVars] using member
  subst candidate
  have range := fresh (.ty index) hiddenMember
  exact (Nat.not_le_of_lt indexLt range.1)

private theorem TypeAvoids.append_forbidden
    {left right : List UnificationVar} {target : Ty}
    (leftAvoids : TypeAvoids left target)
    (rightAvoids : TypeAvoids right target) :
    TypeAvoids (left ++ right) target := by
  intro candidate member forbidden
  rcases List.mem_append.mp forbidden with leftMember | rightMember
  · exact leftAvoids candidate member leftMember
  · exact rightAvoids candidate member rightMember

private theorem scopedComposition_var
    (_letHandler : LetComparisonHandler)
    {context : Context} {index : Nat} {start : Supply} {scheme : Scheme}
    (lookup : context[index]? = some scheme) :
    ∀ {rightGenerated rightNext},
      Elaborates context (.var index) start rightGenerated rightNext →
        start.WellFormedFor context →
          ScopedGeneratedComparison start (scheme.instantiate start).2
            rightNext
            { target := (scheme.instantiate start).1,
              hard := [], pending := [] }
            rightGenerated := by
  intro rightGenerated rightNext rightElaboration wellFormed
  cases rightElaboration with
  | @var _ _ _ rightScheme rightLookup =>
      have schemeEquality : scheme = rightScheme := by
        rw [lookup] at rightLookup
        exact Option.some.inj rightLookup
      subst rightScheme
      exact scopedGeneratedComparison_refl start
        (scheme.instantiate start).2 _

private theorem scopedComposition_lit
    (_letHandler : LetComparisonHandler)
    {context : Context} {value : Int} {start : Supply} :
    ∀ {rightGenerated rightNext},
      Elaborates context (.lit value) start rightGenerated rightNext →
        start.WellFormedFor context →
          ScopedGeneratedComparison start start rightNext
            { target := .int, hard := [], pending := [] }
            rightGenerated := by
  intro rightGenerated rightNext rightElaboration wellFormed
  cases rightElaboration
  exact scopedGeneratedComparison_refl start start _

private theorem scopedComposition_something
    (_letHandler : LetComparisonHandler)
    {context : Context} {start : Supply} :
    ∀ {rightGenerated rightNext},
      Elaborates context .something start rightGenerated rightNext →
        start.WellFormedFor context →
          ScopedGeneratedComparison start (start.nextTy 1) rightNext
            { target := .matcher .any (.var ⟨start.ty⟩),
              hard := [], pending := [] }
            rightGenerated := by
  intro rightGenerated rightNext rightElaboration wellFormed
  cases rightElaboration
  exact scopedGeneratedComparison_refl start (start.nextTy 1) _

private theorem scopedComposition_lam
    (_letHandler : LetComparisonHandler)
    {context : Context} {body : Expr} {start : Supply}
    {leftBody : Generated} {leftNext : Supply}
    (_leftBodyElaboration : Elaborates
      (.mono (.var ⟨start.ty⟩) :: context) body
      (start.nextTy 1) leftBody leftNext)
    (bodyComparison : ∀ {rightBody rightNext},
      Elaborates (.mono (.var ⟨start.ty⟩) :: context) body
          (start.nextTy 1) rightBody rightNext →
        (start.nextTy 1).WellFormedFor
            (.mono (.var ⟨start.ty⟩) :: context) →
          ScopedGeneratedComparison (start.nextTy 1)
            leftNext rightNext leftBody rightBody) :
    ∀ {rightGenerated rightNext},
      Elaborates context (.lam body) start rightGenerated rightNext →
        start.WellFormedFor context →
          ScopedGeneratedComparison start leftNext rightNext
            (Generated.fromLam (.var ⟨start.ty⟩) leftBody)
            rightGenerated := by
  intro rightGenerated rightNext rightElaboration wellFormed
  cases rightElaboration with
  | lam rightBodyElaboration =>
      obtain ⟨nextEquality, hidden, hiddenFresh, bodyRelated⟩ :=
        bodyComparison rightBodyElaboration (lamBody_wellFormed wellFormed)
      subst rightNext
      refine ⟨rfl, hidden, ?_, ?_⟩
      · exact hiddenFresh.widen (Supply.le_nextTy start 1)
          (Supply.le_refl leftNext)
      · apply Generated.ScopedContextualEquivalent.lam
        · exact hiddenFresh.typeAvoids_ty_of_lt_start (by
            simp [Supply.nextTy])
        · exact bodyRelated

private theorem scopedComposition_app
    (_letHandler : LetComparisonHandler)
    {context : Context} {function argument : Expr} {start : Supply}
    {leftFunction : Generated} {leftAfterFunction : Supply}
    {leftArgument : Generated} {leftAfterArgument : Supply}
    (leftFunctionElaboration : Elaborates context function start
      leftFunction leftAfterFunction)
    (leftArgumentElaboration : Elaborates context argument leftAfterFunction
      leftArgument leftAfterArgument)
    (functionComparison : ∀ {rightFunction rightAfterFunction},
      Elaborates context function start rightFunction rightAfterFunction →
        start.WellFormedFor context →
          ScopedGeneratedComparison start leftAfterFunction
            rightAfterFunction leftFunction rightFunction)
    (argumentComparison : ∀ {rightArgument rightAfterArgument},
      Elaborates context argument leftAfterFunction rightArgument
          rightAfterArgument →
        leftAfterFunction.WellFormedFor context →
          ScopedGeneratedComparison leftAfterFunction leftAfterArgument
            rightAfterArgument leftArgument rightArgument) :
    ∀ {rightGenerated rightNext},
      Elaborates context (.app function argument) start
          rightGenerated rightNext →
        start.WellFormedFor context →
          ScopedGeneratedComparison start (leftAfterArgument.nextTy 2)
            rightNext
            (Generated.fromApp leftFunction leftArgument
              (.var ⟨leftAfterArgument.ty⟩)
              (.var ⟨leftAfterArgument.ty + 1⟩))
            rightGenerated := by
  intro rightGenerated rightNext rightElaboration wellFormed
  cases rightElaboration with
  | @app _ _ _ _ rightFunction rightAfterFunction rightArgument
      rightAfterArgument rightFunctionElaboration rightArgumentElaboration =>
      obtain ⟨functionNextEquality, functionHidden, functionFresh,
          functionRelated⟩ :=
        functionComparison rightFunctionElaboration wellFormed
      subst rightAfterFunction
      obtain ⟨argumentNextEquality, argumentHidden, argumentFresh,
          argumentRelated⟩ :=
        argumentComparison rightArgumentElaboration
          (wellFormed.mono leftFunctionElaboration.supply_le_next)
      subst rightAfterArgument
      obtain ⟨leftArgumentAvoids, rightFunctionAvoids⟩ :=
        Elaborates.sequential_crossAvoidance
          rightFunctionElaboration leftArgumentElaboration wellFormed
          functionFresh argumentFresh
      have argumentToNext :
          leftAfterArgument.Le (leftAfterArgument.nextTy 2) :=
        Supply.le_nextTy leftAfterArgument 2
      have functionToArgument :
          leftAfterFunction.Le leftAfterArgument :=
        leftArgumentElaboration.supply_le_next
      have domainAvoids : TypeAvoids
          (functionHidden ++ argumentHidden)
          (.var ⟨leftAfterArgument.ty⟩) :=
        TypeAvoids.append_forbidden
          (functionFresh.typeAvoids_ty_of_finish_le functionToArgument.1)
          (argumentFresh.typeAvoids_ty_of_finish_le (Nat.le_refl _))
      have targetAvoids : TypeAvoids
          (functionHidden ++ argumentHidden)
          (.var ⟨leftAfterArgument.ty + 1⟩) :=
        TypeAvoids.append_forbidden
          (functionFresh.typeAvoids_ty_of_finish_le
            (index := ⟨leftAfterArgument.ty + 1⟩) (by
              change leftAfterFunction.ty ≤ leftAfterArgument.ty + 1
              exact Nat.le_trans functionToArgument.1
                (Nat.le_add_right _ _)))
          (argumentFresh.typeAvoids_ty_of_finish_le
            (index := ⟨leftAfterArgument.ty + 1⟩) (by
              change leftAfterArgument.ty ≤ leftAfterArgument.ty + 1
              exact Nat.le_add_right _ _))
      refine ⟨rfl, functionHidden ++ argumentHidden, ?_, ?_⟩
      · exact VariablesFreshIn.append
          (functionFresh.widen (Supply.le_refl start)
            (Supply.le_trans functionToArgument argumentToNext))
          (argumentFresh.widen leftFunctionElaboration.supply_le_next
            argumentToNext)
      · exact Generated.ScopedContextualEquivalent.app
          (.var ⟨leftAfterArgument.ty⟩)
          (.var ⟨leftAfterArgument.ty + 1⟩)
          functionRelated argumentRelated leftArgumentAvoids
          rightFunctionAvoids domainAvoids targetAvoids

private theorem scopedComposition_tuple
    (_letHandler : LetComparisonHandler)
    {context : Context} {items : List Expr} {start : Supply}
    {leftItems : GeneratedItems} {leftNext : Supply}
    (_leftItemsElaboration :
      ElaboratesItems context items start leftItems leftNext)
    (itemsComparison : ∀ {rightItems rightNext},
      ElaboratesItems context items start rightItems rightNext →
        start.WellFormedFor context →
          ScopedItemsComparison start leftNext rightNext
            leftItems rightItems) :
    ∀ {rightGenerated rightNext},
      Elaborates context (.tuple items) start rightGenerated rightNext →
        start.WellFormedFor context →
          ScopedGeneratedComparison start leftNext rightNext
            (GeneratedItems.asTuple leftItems) rightGenerated := by
  intro rightGenerated rightNext rightElaboration wellFormed
  cases rightElaboration with
  | tuple rightItemsElaboration =>
      obtain ⟨nextEquality, hidden, hiddenFresh, itemsRelated⟩ :=
        itemsComparison rightItemsElaboration wellFormed
      subst rightNext
      exact ⟨rfl, hidden, hiddenFresh,
        GeneratedItems.ScopedContextualEquivalent.tuple itemsRelated⟩

private theorem scopedComposition_let
    (letHandler : LetComparisonHandler)
    {context : Context} {value body : Expr} {start : Supply}
    {leftValue : Generated} {leftAfterValue : Supply}
    {leftBody : Generated} {leftNext : Supply}
    (leftValueElaboration :
      Elaborates context value start leftValue leftAfterValue)
    (leftClosure : PrincipalBlockClosure leftValue)
    (leftAbsorbing : leftClosure.Absorbing)
    (leftBodyElaboration : Elaborates
      ((context.applyFree leftClosure.substitution).generalize
          leftClosure.target ::
        context.applyFree leftClosure.substitution)
      body
      (leftAfterValue.join
        (context.applyFree leftClosure.substitution).initialSupply)
      leftBody leftNext)
    (_valueComparison : ∀ {rightValue rightAfterValue},
      Elaborates context value start rightValue rightAfterValue →
        start.WellFormedFor context →
          ScopedGeneratedComparison start leftAfterValue rightAfterValue
            leftValue rightValue)
    (_bodyComparison : ∀ {rightBody rightNext},
      Elaborates
          ((context.applyFree leftClosure.substitution).generalize
              leftClosure.target ::
            context.applyFree leftClosure.substitution)
          body
          (leftAfterValue.join
            (context.applyFree leftClosure.substitution).initialSupply)
          rightBody rightNext →
        Supply.WellFormedFor
            ((context.applyFree leftClosure.substitution).generalize
                leftClosure.target ::
              context.applyFree leftClosure.substitution)
            (leftAfterValue.join
              (context.applyFree leftClosure.substitution).initialSupply) →
          ScopedGeneratedComparison
            (leftAfterValue.join
              (context.applyFree leftClosure.substitution).initialSupply)
            leftNext rightNext leftBody rightBody) :
    ∀ {rightGenerated rightNext},
      Elaborates context (.letE value body) start rightGenerated rightNext →
        start.WellFormedFor context →
          ScopedGeneratedComparison start leftNext rightNext
            (Generated.fromLet
              (context.interfaceEquations leftClosure.substitution)
              leftBody)
            rightGenerated := by
  intro rightGenerated rightNext rightElaboration wellFormed
  exact letHandler wellFormed
    (.letE leftValueElaboration leftClosure leftAbsorbing
      leftBodyElaboration)
    rightElaboration

private theorem scopedComposition_items_nil
    (_letHandler : LetComparisonHandler)
    {context : Context} {start : Supply} :
    ∀ {rightItems rightNext},
      ElaboratesItems context [] start rightItems rightNext →
        start.WellFormedFor context →
          ScopedItemsComparison start start rightNext
            GeneratedItems.nil rightItems := by
  intro rightItems rightNext rightElaboration wellFormed
  cases rightElaboration
  exact scopedItemsComparison_refl start start GeneratedItems.nil

private theorem scopedComposition_items_cons
    (_letHandler : LetComparisonHandler)
    {context : Context} {item : Expr} {items : List Expr} {start : Supply}
    {leftItem : Generated} {leftAfterItem : Supply}
    {leftItems : GeneratedItems} {leftNext : Supply}
    (leftItemElaboration :
      Elaborates context item start leftItem leftAfterItem)
    (leftItemsElaboration :
      ElaboratesItems context items leftAfterItem leftItems leftNext)
    (itemComparison : ∀ {rightItem rightAfterItem},
      Elaborates context item start rightItem rightAfterItem →
        start.WellFormedFor context →
          ScopedGeneratedComparison start leftAfterItem rightAfterItem
            leftItem rightItem)
    (itemsComparison : ∀ {rightItems rightNext},
      ElaboratesItems context items leftAfterItem rightItems rightNext →
        leftAfterItem.WellFormedFor context →
          ScopedItemsComparison leftAfterItem leftNext rightNext
            leftItems rightItems) :
    ∀ {rightItems rightNext},
      ElaboratesItems context (item :: items) start rightItems rightNext →
        start.WellFormedFor context →
          ScopedItemsComparison start leftNext rightNext
            (GeneratedItems.cons leftItem leftItems) rightItems := by
  intro rightItems rightNext rightElaboration wellFormed
  cases rightElaboration with
  | @cons _ _ _ _ rightItem rightAfterItem rightItems rightItemsNext
      rightItemElaboration rightItemsElaboration =>
      obtain ⟨itemNextEquality, itemHidden, itemFresh, itemRelated⟩ :=
        itemComparison rightItemElaboration wellFormed
      subst rightAfterItem
      obtain ⟨itemsNextEquality, itemsHidden, itemsFresh, itemsRelated⟩ :=
        itemsComparison rightItemsElaboration
          (wellFormed.mono leftItemElaboration.supply_le_next)
      subst rightNext
      obtain ⟨leftItemsAvoid, rightItemAvoid⟩ :=
        ElaboratesItems.cons_crossAvoidance
          rightItemElaboration leftItemsElaboration wellFormed
          itemFresh itemsFresh
      refine ⟨rfl, itemHidden ++ itemsHidden, ?_, ?_⟩
      · exact VariablesFreshIn.append
          (itemFresh.widen (Supply.le_refl start)
            leftItemsElaboration.supply_le_next)
          (itemsFresh.widen leftItemElaboration.supply_le_next
            (Supply.le_refl leftNext))
      · exact GeneratedItems.ScopedContextualEquivalent.cons
          itemRelated itemsRelated leftItemsAvoid rightItemAvoid

/-- All ordinary source constructors compose scoped comparisons.  The
well-formed starting supply is essential; only the representative-sensitive
`letE` branch is delegated to `letHandler`. -/
theorem Elaborates.scopedComparison
    (letHandler : LetComparisonHandler)
    {context : Context} {expression : Expr} {start : Supply}
    {leftGenerated rightGenerated : Generated}
    {leftNext rightNext : Supply}
    (leftElaboration : Elaborates context expression start
      leftGenerated leftNext)
    (rightElaboration : Elaborates context expression start
      rightGenerated rightNext)
    (wellFormed : start.WellFormedFor context) :
    ScopedGeneratedComparison start leftNext rightNext
      leftGenerated rightGenerated :=
  Elaborates.rec
    (motive_1 := fun context expression start leftGenerated leftNext _ =>
      ∀ {rightGenerated rightNext},
        Elaborates context expression start rightGenerated rightNext →
          start.WellFormedFor context →
            ScopedGeneratedComparison start leftNext rightNext
              leftGenerated rightGenerated)
    (motive_2 := fun context expressions start leftItems leftNext _ =>
      ∀ {rightItems rightNext},
        ElaboratesItems context expressions start rightItems rightNext →
          start.WellFormedFor context →
            ScopedItemsComparison start leftNext rightNext
              leftItems rightItems)
    (scopedComposition_var letHandler)
    (scopedComposition_lit letHandler)
    (scopedComposition_something letHandler)
    (scopedComposition_lam letHandler)
    (scopedComposition_app letHandler)
    (scopedComposition_tuple letHandler)
    (scopedComposition_let letHandler)
    (scopedComposition_items_nil letHandler)
    (scopedComposition_items_cons letHandler)
    leftElaboration rightElaboration wellFormed

/-- List counterpart of `Elaborates.scopedComparison`, using the same single
`letE` handler for nested item expressions. -/
theorem ElaboratesItems.scopedComparison
    (letHandler : LetComparisonHandler)
    {context : Context} {expressions : List Expr} {start : Supply}
    {leftItems rightItems : GeneratedItems}
    {leftNext rightNext : Supply}
    (leftElaboration : ElaboratesItems context expressions start
      leftItems leftNext)
    (rightElaboration : ElaboratesItems context expressions start
      rightItems rightNext)
    (wellFormed : start.WellFormedFor context) :
    ScopedItemsComparison start leftNext rightNext leftItems rightItems :=
  ElaboratesItems.rec
    (motive_1 := fun context expression start leftGenerated leftNext _ =>
      ∀ {rightGenerated rightNext},
        Elaborates context expression start rightGenerated rightNext →
          start.WellFormedFor context →
            ScopedGeneratedComparison start leftNext rightNext
              leftGenerated rightGenerated)
    (motive_2 := fun context expressions start leftItems leftNext _ =>
      ∀ {rightItems rightNext},
        ElaboratesItems context expressions start rightItems rightNext →
          start.WellFormedFor context →
            ScopedItemsComparison start leftNext rightNext
              leftItems rightItems)
    (scopedComposition_var letHandler)
    (scopedComposition_lit letHandler)
    (scopedComposition_something letHandler)
    (scopedComposition_lam letHandler)
    (scopedComposition_app letHandler)
    (scopedComposition_tuple letHandler)
    (scopedComposition_let letHandler)
    (scopedComposition_items_nil letHandler)
    (scopedComposition_items_cons letHandler)
    leftElaboration rightElaboration wellFormed

/-- Let-free elaborations have an unconditional pairwise scoped comparison:
no representative-sensitive handler is needed.  The well-formed start is
kept explicit as the source comparison invariant. -/
theorem Elaborates.scopedComparison_of_letFree
    {context : Context} {expression : Expr} {start : Supply}
    {leftGenerated rightGenerated : Generated}
    {leftNext rightNext : Supply}
    (leftElaboration : Elaborates context expression start
      leftGenerated leftNext)
    (rightElaboration : Elaborates context expression start
      rightGenerated rightNext)
    (_wellFormed : start.WellFormedFor context)
    (letFree : LetFree expression) :
    ScopedGeneratedComparison start leftNext rightNext
      leftGenerated rightGenerated := by
  have leftReplay := leftElaboration.replay_of_letFree letFree
  have rightReplay := rightElaboration.replay_of_letFree letFree
  rw [leftReplay] at rightReplay
  have pairEquality := Option.some.inj rightReplay
  injection pairEquality with generatedEquality nextEquality
  subst rightGenerated
  subst rightNext
  exact scopedGeneratedComparison_refl start leftNext leftGenerated

/-- List counterpart of `Elaborates.scopedComparison_of_letFree`. -/
theorem ElaboratesItems.scopedComparison_of_letFree
    {context : Context} {expressions : List Expr} {start : Supply}
    {leftItems rightItems : GeneratedItems}
    {leftNext rightNext : Supply}
    (leftElaboration : ElaboratesItems context expressions start
      leftItems leftNext)
    (rightElaboration : ElaboratesItems context expressions start
      rightItems rightNext)
    (_wellFormed : start.WellFormedFor context)
    (letFree : LetFreeItems expressions) :
    ScopedItemsComparison start leftNext rightNext leftItems rightItems := by
  have leftReplay := leftElaboration.replay_of_letFree letFree
  have rightReplay := rightElaboration.replay_of_letFree letFree
  rw [leftReplay] at rightReplay
  have pairEquality := Option.some.inj rightReplay
  injection pairEquality with itemsEquality nextEquality
  subst rightItems
  subst rightNext
  exact scopedItemsComparison_refl start leftNext leftItems

end TypePM.Source
