import TypePM.Source.GeneratedSupportBounds

/-!
# Scope-aware generated acceptance equivalence

A nested `letE` can choose different principal closure representatives.  The
resulting blocks need a target-aware relation: plain `BlockAccepts` equivalence
does not compose through application, because an application reads both child
targets.  This module defines one-hole generated frames and proves the
ordinary lambda, application, and tuple composition laws.

Local alias names cannot safely be exposed to every possible frame.  The
scope-aware relation therefore records a finite list of hidden names and only
tests frames that do not mention them.  Its application and tuple laws state
the remaining cross-scope freshness conditions explicitly.

The final section packages the supply-interval facts that a later structural
coherence proof will consume; it does not assume the missing `letE` interface
theorem.
-/

namespace TypePM.Source

namespace Generated

/-- The exact generated block built around a lambda body. -/
def fromLam (domain : Ty) (body : Generated) : Generated :=
  ⟨.fn domain body.target, body.hard, body.pending⟩

/-- The exact generated block built around an application pair. -/
def fromApp (function argument : Generated) (domain target : Ty) : Generated :=
  ⟨target,
    function.hard ++ argument.hard ++
      [.ty function.target (.fn domain target)],
    function.pending ++ argument.pending ++
      [⟨argument.target, domain⟩]⟩

end Generated

namespace GeneratedItems

def nil : GeneratedItems := ⟨[], [], []⟩

def cons (item : Generated) (items : GeneratedItems) : GeneratedItems :=
  ⟨item.target :: items.targets,
    item.hard ++ items.hard,
    item.pending ++ items.pending⟩

def append (left right : GeneratedItems) : GeneratedItems :=
  ⟨left.targets ++ right.targets,
    left.hard ++ right.hard,
    left.pending ++ right.pending⟩

def singleton (item : Generated) : GeneratedItems := cons item nil

def asTuple (items : GeneratedItems) : Generated :=
  ⟨.prod items.targets, items.hard, items.pending⟩

@[simp] theorem nil_append (items : GeneratedItems) :
    append nil items = items := by
  cases items
  simp [append, nil]

@[simp] theorem append_nil (items : GeneratedItems) :
    append items nil = items := by
  cases items
  simp [append, nil]

@[simp] theorem append_assoc
    (first second third : GeneratedItems) :
    append (append first second) third =
      append first (append second third) := by
  cases first
  cases second
  cases third
  simp [append, List.append_assoc]

@[simp] theorem append_singleton_cons
    (before : GeneratedItems) (item : Generated)
    (after : GeneratedItems) :
    append (append before (singleton item)) after =
      append before (cons item after) := by
  cases before
  cases item
  cases after
  simp [append, singleton, cons, nil, List.append_assoc]

@[simp] theorem singleton_append
    (item : Generated) (items : GeneratedItems) :
    append (singleton item) items = cons item items := by
  cases item
  cases items
  simp [append, singleton, cons, nil]

@[simp] theorem cons_append
    (item : Generated) (items after : GeneratedItems) :
    append (cons item items) after = cons item (append items after) := by
  cases item
  cases items
  cases after
  simp [append, cons, List.append_assoc]

end GeneratedItems

/-- One-hole source-generated context.  These are exactly the contexts used
by lambda, application, tuple collection, and `letE`; arbitrary Lean
functions are excluded so contextual equivalence remains useful. -/
inductive GeneratedFrame where
  | hole
  | lam (domain : Ty) (outer : GeneratedFrame)
  | appFunction (argument : Generated) (domain target : Ty)
      (outer : GeneratedFrame)
  | appArgument (function : Generated) (domain target : Ty)
      (outer : GeneratedFrame)
  | tupleItem (before after : GeneratedItems) (outer : GeneratedFrame)
  | letBody (effects : List Equation) (outer : GeneratedFrame)

namespace GeneratedFrame

def plug : GeneratedFrame → Generated → Generated
  | .hole, generated => generated
  | .lam domain outer, generated =>
      outer.plug (Generated.fromLam domain generated)
  | .appFunction argument domain target outer, generated =>
      outer.plug (Generated.fromApp generated argument domain target)
  | .appArgument function domain target outer, generated =>
      outer.plug (Generated.fromApp function generated domain target)
  | .tupleItem before after outer, generated =>
      outer.plug <| GeneratedItems.asTuple <|
        GeneratedItems.append before
          (GeneratedItems.append (GeneratedItems.singleton generated) after)
  | .letBody effects outer, generated =>
      outer.plug (Generated.fromLet effects generated)

end GeneratedFrame

/-! ## Scope-aware contextual acceptance

Fresh aliases introduced while reconciling two `letE` representatives are
local names.  Quantifying over every syntactically possible frame is too
strong: an arbitrary later frame could mention one of those names directly.
The following predicates make the intended side condition explicit. -/

/-- None of the observed variables belongs to the forbidden finite set. -/
def VariablesAvoid (forbidden observed : List UnificationVar) : Prop :=
  ∀ candidate, candidate ∈ observed → candidate ∉ forbidden

namespace VariablesAvoid

theorem antitone {smaller larger observed : List UnificationVar}
    (avoids : VariablesAvoid larger observed)
    (subset : ∀ candidate, candidate ∈ smaller → candidate ∈ larger) :
    VariablesAvoid smaller observed := by
  intro candidate member forbidden
  exact avoids candidate member (subset candidate forbidden)

theorem of_append_left {left right observed : List UnificationVar}
    (avoids : VariablesAvoid (left ++ right) observed) :
    VariablesAvoid left observed :=
  avoids.antitone (fun _ member => List.mem_append_left _ member)

theorem of_append_right {left right observed : List UnificationVar}
    (avoids : VariablesAvoid (left ++ right) observed) :
    VariablesAvoid right observed :=
  avoids.antitone (fun _ member => List.mem_append_right _ member)

end VariablesAvoid

def TypeAvoids (forbidden : List UnificationVar) (target : Ty) : Prop :=
  VariablesAvoid forbidden target.unificationVars

def EquationsAvoid (forbidden : List UnificationVar)
    (equations : List Equation) : Prop :=
  VariablesAvoid forbidden (TypePM.unificationVars equations)

/-- The target, hard equations, and delayed obligations avoid every forbidden
name.  This is the side condition needed when a block is fixed in a frame. -/
def GeneratedAvoids (forbidden : List UnificationVar)
    (generated : Generated) : Prop :=
  VariablesAvoid forbidden generated.unificationVars

namespace GeneratedAvoids

theorem antitone {smaller larger : List UnificationVar}
    {generated : Generated}
    (avoids : GeneratedAvoids larger generated)
    (subset : ∀ candidate, candidate ∈ smaller → candidate ∈ larger) :
    GeneratedAvoids smaller generated :=
  VariablesAvoid.antitone avoids subset

theorem of_append_left {left right : List UnificationVar}
    {generated : Generated}
    (avoids : GeneratedAvoids (left ++ right) generated) :
    GeneratedAvoids left generated :=
  avoids.antitone (fun _ member => List.mem_append_left _ member)

theorem of_append_right {left right : List UnificationVar}
    {generated : Generated}
    (avoids : GeneratedAvoids (left ++ right) generated) :
    GeneratedAvoids right generated :=
  avoids.antitone (fun _ member => List.mem_append_right _ member)

end GeneratedAvoids

private theorem tyUnificationVarsList_append
    (left right : List Ty) :
    Ty.unificationVarsList (left ++ right) =
      Ty.unificationVarsList left ++ Ty.unificationVarsList right := by
  induction left with
  | nil => rfl
  | cons item items induction =>
      simp [Ty.unificationVarsList, induction, List.append_assoc]

@[simp] theorem GeneratedItems.unificationVars_nil :
    GeneratedItems.nil.unificationVars = [] := by
  rfl

theorem GeneratedItems.mem_unificationVars_append
    (candidate : UnificationVar) (left right : GeneratedItems) :
    candidate ∈
        (GeneratedItems.append left right).unificationVars ↔
      candidate ∈ left.unificationVars ∨
        candidate ∈ right.unificationVars := by
  cases left
  cases right
  simp only [GeneratedItems.unificationVars, GeneratedItems.append,
    tyUnificationVarsList_append, unificationVars_append,
    pendingUnificationVars_append, List.mem_append]
  simp only [or_assoc, or_left_comm, or_comm]

@[simp] theorem GeneratedItems.unificationVars_singleton
    (item : Generated) :
    (GeneratedItems.singleton item).unificationVars =
      item.unificationVars := by
  cases item
  simp [GeneratedItems.unificationVars, GeneratedItems.singleton,
    GeneratedItems.cons, GeneratedItems.nil, Generated.unificationVars,
    Ty.unificationVarsList, List.append_assoc]

def GeneratedItemsAvoid (forbidden : List UnificationVar)
    (items : GeneratedItems) : Prop :=
  VariablesAvoid forbidden items.unificationVars

namespace GeneratedItemsAvoid

theorem antitone {smaller larger : List UnificationVar}
    {items : GeneratedItems}
    (avoids : GeneratedItemsAvoid larger items)
    (subset : ∀ candidate, candidate ∈ smaller → candidate ∈ larger) :
    GeneratedItemsAvoid smaller items :=
  VariablesAvoid.antitone avoids subset

theorem of_append_left {left right : List UnificationVar}
    {items : GeneratedItems}
    (avoids : GeneratedItemsAvoid (left ++ right) items) :
    GeneratedItemsAvoid left items :=
  avoids.antitone (fun _ member => List.mem_append_left _ member)

theorem of_append_right {left right : List UnificationVar}
    {items : GeneratedItems}
    (avoids : GeneratedItemsAvoid (left ++ right) items) :
    GeneratedItemsAvoid right items :=
  avoids.antitone (fun _ member => List.mem_append_right _ member)

theorem append {forbidden : List UnificationVar}
    {left right : GeneratedItems}
    (leftAvoids : GeneratedItemsAvoid forbidden left)
    (rightAvoids : GeneratedItemsAvoid forbidden right) :
    GeneratedItemsAvoid forbidden (GeneratedItems.append left right) := by
  intro candidate member forbiddenMember
  rcases (GeneratedItems.mem_unificationVars_append candidate left right).mp
      member with leftMember | rightMember
  · exact leftAvoids candidate leftMember forbiddenMember
  · exact rightAvoids candidate rightMember forbiddenMember

theorem singleton {forbidden : List UnificationVar} {item : Generated}
    (avoids : GeneratedAvoids forbidden item) :
    GeneratedItemsAvoid forbidden (GeneratedItems.singleton item) := by
  unfold GeneratedItemsAvoid
  rw [GeneratedItems.unificationVars_singleton]
  exact avoids

theorem nil (forbidden : List UnificationVar) :
    GeneratedItemsAvoid forbidden GeneratedItems.nil := by
  simp [GeneratedItemsAvoid, VariablesAvoid]

end GeneratedItemsAvoid

namespace GeneratedFrame

/-- The fixed material of a source frame avoids all forbidden local names. -/
def Avoids (forbidden : List UnificationVar) : GeneratedFrame → Prop
  | .hole => True
  | .lam domain outer =>
      TypeAvoids forbidden domain ∧ outer.Avoids forbidden
  | .appFunction argument domain target outer =>
      GeneratedAvoids forbidden argument ∧ TypeAvoids forbidden domain ∧
        TypeAvoids forbidden target ∧ outer.Avoids forbidden
  | .appArgument function domain target outer =>
      GeneratedAvoids forbidden function ∧ TypeAvoids forbidden domain ∧
        TypeAvoids forbidden target ∧ outer.Avoids forbidden
  | .tupleItem before after outer =>
      GeneratedItemsAvoid forbidden before ∧
        GeneratedItemsAvoid forbidden after ∧
        outer.Avoids forbidden
  | .letBody effects outer =>
      EquationsAvoid forbidden effects ∧ outer.Avoids forbidden

namespace Avoids

theorem antitone {smaller larger : List UnificationVar}
    {frame : GeneratedFrame}
    (avoids : frame.Avoids larger)
    (subset : ∀ candidate, candidate ∈ smaller → candidate ∈ larger) :
    frame.Avoids smaller := by
  induction frame with
  | hole => trivial
  | lam domain outer induction =>
      exact ⟨avoids.1.antitone subset, induction avoids.2⟩
  | appFunction argument domain target outer induction =>
      exact ⟨avoids.1.antitone subset,
        avoids.2.1.antitone subset,
        avoids.2.2.1.antitone subset,
        induction avoids.2.2.2⟩
  | appArgument function domain target outer induction =>
      exact ⟨avoids.1.antitone subset,
        avoids.2.1.antitone subset,
        avoids.2.2.1.antitone subset,
        induction avoids.2.2.2⟩
  | tupleItem before after outer induction =>
      exact ⟨avoids.1.antitone subset,
        avoids.2.1.antitone subset, induction avoids.2.2⟩
  | letBody effects outer induction =>
      exact ⟨avoids.1.antitone subset, induction avoids.2⟩

theorem of_append_left {left right : List UnificationVar}
    {frame : GeneratedFrame}
    (avoids : frame.Avoids (left ++ right)) : frame.Avoids left :=
  avoids.antitone (fun _ member => List.mem_append_left _ member)

theorem of_append_right {left right : List UnificationVar}
    {frame : GeneratedFrame}
    (avoids : frame.Avoids (left ++ right)) : frame.Avoids right :=
  avoids.antitone (fun _ member => List.mem_append_right _ member)

end Avoids

end GeneratedFrame

namespace Generated

/-- Contextual acceptance equivalence scoped by local names that an enclosing
frame is not allowed to mention.  The empty frame is always admissible, so
this relation still implies ordinary block-acceptance equivalence. -/
def ScopedContextualEquivalent
    (hidden : List UnificationVar) (left right : Generated) : Prop :=
  ∀ (frame : GeneratedFrame), frame.Avoids hidden →
    (BlockAccepts (frame.plug left) ↔ BlockAccepts (frame.plug right))

namespace ScopedContextualEquivalent

theorem refl (hidden : List UnificationVar) (generated : Generated) :
    ScopedContextualEquivalent hidden generated generated :=
  fun _ _ => Iff.rfl

theorem symm {hidden : List UnificationVar} {left right : Generated}
    (related : ScopedContextualEquivalent hidden left right) :
    ScopedContextualEquivalent hidden right left :=
  fun frame avoids => (related frame avoids).symm

theorem trans {hidden : List UnificationVar} {left middle right : Generated}
    (first : ScopedContextualEquivalent hidden left middle)
    (second : ScopedContextualEquivalent hidden middle right) :
    ScopedContextualEquivalent hidden left right :=
  fun frame avoids => (first frame avoids).trans (second frame avoids)

theorem antitone {smaller larger : List UnificationVar}
    {left right : Generated}
    (related : ScopedContextualEquivalent smaller left right)
    (subset : ∀ candidate, candidate ∈ smaller → candidate ∈ larger) :
    ScopedContextualEquivalent larger left right := by
  intro frame frameAvoids
  exact related frame (frameAvoids.antitone subset)

theorem blockAccepts_iff {hidden : List UnificationVar}
    {left right : Generated}
    (related : ScopedContextualEquivalent hidden left right) :
    BlockAccepts left ↔ BlockAccepts right :=
  related .hole trivial

theorem lam {hidden : List UnificationVar} (domain : Ty)
    {left right : Generated}
    (domainAvoids : TypeAvoids hidden domain)
    (related : ScopedContextualEquivalent hidden left right) :
    ScopedContextualEquivalent hidden
      (fromLam domain left) (fromLam domain right) := by
  intro outer outerAvoids
  exact related (.lam domain outer) ⟨domainAvoids, outerAvoids⟩

/-- Application composes two independently scoped child relations.  The two
cross-avoidance premises are exactly the sequential-freshness obligations:
the fixed left argument must not mention function-local names, and the fixed
right function must not mention argument-local names. -/
theorem app
    {functionHidden argumentHidden : List UnificationVar}
    {leftFunction rightFunction leftArgument rightArgument : Generated}
    (domain target : Ty)
    (functionRelated : ScopedContextualEquivalent functionHidden
      leftFunction rightFunction)
    (argumentRelated : ScopedContextualEquivalent argumentHidden
      leftArgument rightArgument)
    (leftArgumentAvoids : GeneratedAvoids functionHidden leftArgument)
    (rightFunctionAvoids : GeneratedAvoids argumentHidden rightFunction)
    (domainAvoids : TypeAvoids (functionHidden ++ argumentHidden) domain)
    (targetAvoids : TypeAvoids (functionHidden ++ argumentHidden) target) :
    ScopedContextualEquivalent (functionHidden ++ argumentHidden)
      (fromApp leftFunction leftArgument domain target)
      (fromApp rightFunction rightArgument domain target) := by
  intro outer outerAvoids
  have functionStep := functionRelated
    (.appFunction leftArgument domain target outer)
    ⟨leftArgumentAvoids,
      VariablesAvoid.of_append_left domainAvoids,
      VariablesAvoid.of_append_left targetAvoids,
      outerAvoids.of_append_left⟩
  have argumentStep := argumentRelated
    (.appArgument rightFunction domain target outer)
    ⟨rightFunctionAvoids,
      VariablesAvoid.of_append_right domainAvoids,
      VariablesAvoid.of_append_right targetAvoids,
      outerAvoids.of_append_right⟩
  exact functionStep.trans argumentStep

theorem letBody {hidden : List UnificationVar}
    (effects : List Equation) {left right : Generated}
    (effectsAvoid : EquationsAvoid hidden effects)
    (related : ScopedContextualEquivalent hidden left right) :
    ScopedContextualEquivalent hidden
      (fromLet effects left) (fromLet effects right) := by
  intro outer outerAvoids
  exact related (.letBody effects outer) ⟨effectsAvoid, outerAvoids⟩

end ScopedContextualEquivalent

end Generated

namespace GeneratedItems

/-- Sibling counterpart of `Generated.ScopedContextualEquivalent`.  Prefix,
suffix, and outer-frame scope hypotheses expose exactly what is needed to
replace one list segment inside a tuple. -/
def ScopedContextualEquivalent
    (hidden : List UnificationVar)
    (left right : GeneratedItems) : Prop :=
  ∀ (before after : GeneratedItems) (outer : GeneratedFrame),
    GeneratedItemsAvoid hidden before →
      GeneratedItemsAvoid hidden after → outer.Avoids hidden →
        (BlockAccepts
            (outer.plug <| asTuple <|
              append before (append left after)) ↔
          BlockAccepts
            (outer.plug <| asTuple <|
              append before (append right after)))

namespace ScopedContextualEquivalent

theorem refl (hidden : List UnificationVar) (items : GeneratedItems) :
    ScopedContextualEquivalent hidden items items :=
  fun _ _ _ _ _ _ => Iff.rfl

theorem cons
    {itemHidden itemsHidden : List UnificationVar}
    {leftItem rightItem : Generated}
    {leftItems rightItems : GeneratedItems}
    (itemRelated : Generated.ScopedContextualEquivalent itemHidden
      leftItem rightItem)
    (itemsRelated : ScopedContextualEquivalent itemsHidden
      leftItems rightItems)
    (leftItemsAvoid : GeneratedItemsAvoid itemHidden leftItems)
    (rightItemAvoid : GeneratedAvoids itemsHidden rightItem) :
    ScopedContextualEquivalent (itemHidden ++ itemsHidden)
      (GeneratedItems.cons leftItem leftItems)
      (GeneratedItems.cons rightItem rightItems) := by
  intro before after outer beforeAvoids afterAvoids outerAvoids
  have beforeItem := beforeAvoids.of_append_left
  have afterItem := afterAvoids.of_append_left
  have outerItem := outerAvoids.of_append_left
  have beforeItems := beforeAvoids.of_append_right
  have afterItems := afterAvoids.of_append_right
  have outerItems := outerAvoids.of_append_right
  have itemStep := itemRelated
    (.tupleItem before (append leftItems after) outer)
    ⟨beforeItem, GeneratedItemsAvoid.append leftItemsAvoid afterItem,
      outerItem⟩
  have tailStep := itemsRelated
    (append before (singleton rightItem)) after outer
    (GeneratedItemsAvoid.append beforeItems
      (GeneratedItemsAvoid.singleton rightItemAvoid))
    afterItems outerItems
  have itemStep' :
      BlockAccepts
          (outer.plug <| asTuple <|
            append before
              (append (singleton leftItem) (append leftItems after))) ↔
        BlockAccepts
          (outer.plug <| asTuple <|
            append before
              (append (singleton rightItem) (append leftItems after))) := by
    simpa [GeneratedFrame.plug] using itemStep
  have tailStep' :
      BlockAccepts
          (outer.plug <| asTuple <|
            append before
              (append (singleton rightItem) (append leftItems after))) ↔
        BlockAccepts
          (outer.plug <| asTuple <|
            append before
              (append (singleton rightItem) (append rightItems after))) := by
    simpa only [append_assoc] using tailStep
  simpa only [singleton_append, cons_append] using
    itemStep'.trans tailStep'

theorem tuple {hidden : List UnificationVar}
    {left right : GeneratedItems}
    (related : ScopedContextualEquivalent hidden left right) :
    Generated.ScopedContextualEquivalent hidden
      (asTuple left) (asTuple right) := by
  intro outer outerAvoids
  simpa [append, nil] using
    related GeneratedItems.nil GeneratedItems.nil outer
      (GeneratedItemsAvoid.nil hidden) (GeneratedItemsAvoid.nil hidden)
      outerAvoids

end ScopedContextualEquivalent

end GeneratedItems

/-! ## Fresh-name ranges used by structural coherence -/

/-- Every variable in a finite list was allocated in the given two-sorted,
half-open supply interval. -/
def VariablesFreshIn
    (start next : Supply) (variables : List UnificationVar) : Prop :=
  ∀ candidate, candidate ∈ variables →
    candidate.FreshIn start next

/-- Support of a sub-elaboration consists of names inherited below `base`
or names allocated in that sub-elaboration's own interval. -/
def VariablesScopedBy
    (base start next : Supply) (variables : List UnificationVar) : Prop :=
  ∀ candidate, candidate ∈ variables →
    candidate.Below base.ty base.cap ∨ candidate.FreshIn start next

namespace VariablesFreshIn

theorem nil (start next : Supply) :
    VariablesFreshIn start next [] := by
  simp [VariablesFreshIn]

theorem append {start next : Supply} {left right : List UnificationVar}
    (leftWithin : VariablesFreshIn start next left)
    (rightWithin : VariablesFreshIn start next right) :
    VariablesFreshIn start next (left ++ right) := by
  intro candidate member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftWithin candidate leftMember
  · exact rightWithin candidate rightMember

theorem widen {innerStart innerNext outerStart outerNext : Supply}
    {variables : List UnificationVar}
    (within : VariablesFreshIn innerStart innerNext variables)
    (starts : outerStart.Le innerStart)
    (ends : innerNext.Le outerNext) :
    VariablesFreshIn outerStart outerNext variables := by
  intro candidate member
  exact ((within candidate member).lower_start starts).extend_finish ends

end VariablesFreshIn

/-- Source support provenance is the scoped-support split at the input
context's numeric boundary. -/
theorem GeneratedSupportProvenance.scopedByInitialSupply
    {context : Context} {start finish : Supply} {generated : Generated}
    (provenance :
      GeneratedSupportProvenance context start finish generated) :
    VariablesScopedBy context.initialSupply start finish
      generated.unificationVars := by
  intro candidate member
  rcases provenance candidate member with contextMember | fresh
  · exact Or.inl
      (Context.member_unificationVars_below_initialSupply contextMember)
  · exact Or.inr fresh

/-- List counterpart of
`GeneratedSupportProvenance.scopedByInitialSupply`. -/
theorem GeneratedItemsSupportProvenance.scopedByInitialSupply
    {context : Context} {start finish : Supply}
    {generated : GeneratedItems}
    (provenance :
      GeneratedItemsSupportProvenance context start finish generated) :
    VariablesScopedBy context.initialSupply start finish
      generated.unificationVars := by
  intro candidate member
  rcases provenance candidate member with contextMember | fresh
  · exact Or.inl
      (Context.member_unificationVars_below_initialSupply contextMember)
  · exact Or.inr fresh

namespace VariablesScopedBy

/-- A later block cannot mention hidden names from an earlier allocation
interval when both share the same inherited-variable boundary. -/
theorem avoids_earlier
    {base earlierStart earlierNext laterStart laterNext : Supply}
    {hidden observed : List UnificationVar}
    (hiddenWithin : VariablesFreshIn
      earlierStart earlierNext hidden)
    (observedScoped : VariablesScopedBy
      base laterStart laterNext observed)
    (baseBefore : base.Le earlierStart)
    (separated : earlierNext.Le laterStart) :
    VariablesAvoid hidden observed := by
  intro candidate observedMember hiddenMember
  have hiddenRange := hiddenWithin candidate hiddenMember
  have observedRange := observedScoped candidate observedMember
  cases candidate with
  | ty index =>
      simp only [UnificationVar.FreshIn, UnificationVar.Below,
        Supply.Le] at hiddenRange observedRange baseBefore separated
      rcases observedRange with inherited | allocated <;> omega
  | cap index =>
      simp only [UnificationVar.FreshIn, UnificationVar.Below,
        Supply.Le] at hiddenRange observedRange baseBefore separated
      rcases observedRange with inherited | allocated <;> omega

/-- Symmetric interval separation: an earlier block cannot mention hidden
names allocated by a later block. -/
theorem avoids_later
    {base earlierStart earlierNext laterStart laterNext : Supply}
    {observed hidden : List UnificationVar}
    (observedScoped : VariablesScopedBy
      base earlierStart earlierNext observed)
    (hiddenWithin : VariablesFreshIn
      laterStart laterNext hidden)
    (baseBefore : base.Le earlierStart)
    (earlierMonotone : earlierStart.Le earlierNext)
    (separated : earlierNext.Le laterStart) :
    VariablesAvoid hidden observed := by
  intro candidate observedMember hiddenMember
  have observedRange := observedScoped candidate observedMember
  have hiddenRange := hiddenWithin candidate hiddenMember
  cases candidate with
  | ty index =>
      simp only [UnificationVar.FreshIn, UnificationVar.Below,
        Supply.Le] at observedRange hiddenRange baseBefore earlierMonotone separated
      rcases observedRange with inherited | allocated <;> omega
  | cap index =>
      simp only [UnificationVar.FreshIn, UnificationVar.Below,
        Supply.Le] at observedRange hiddenRange baseBefore earlierMonotone separated
      rcases observedRange with inherited | allocated <;> omega

end VariablesScopedBy

namespace Elaborates

/-- Exact cross-avoidance premises needed by
`Generated.ScopedContextualEquivalent.app` for two sequential expression
elaborations.  Names hidden by the earlier child cannot occur in the later
generated block, and names hidden by the later child cannot occur in the
earlier generated block. -/
theorem sequential_crossAvoidance
    {context : Context} {earlierExpression laterExpression : Expr}
    {start middle finish : Supply}
    {earlierGenerated laterGenerated : Generated}
    (earlierElaboration : Elaborates context earlierExpression start
      earlierGenerated middle)
    (laterElaboration : Elaborates context laterExpression middle
      laterGenerated finish)
    (wellFormed : start.WellFormedFor context)
    {earlierHidden laterHidden : List UnificationVar}
    (earlierFresh : VariablesFreshIn start middle earlierHidden)
    (laterFresh : VariablesFreshIn middle finish laterHidden) :
    GeneratedAvoids earlierHidden laterGenerated ∧
      GeneratedAvoids laterHidden earlierGenerated := by
  constructor
  · exact VariablesScopedBy.avoids_earlier earlierFresh
      laterElaboration.supportProvenance.scopedByInitialSupply
      wellFormed (Supply.le_refl middle)
  · exact VariablesScopedBy.avoids_later
      earlierElaboration.supportProvenance.scopedByInitialSupply
      laterFresh wellFormed earlierElaboration.supply_le_next
      (Supply.le_refl middle)

end Elaborates

namespace ElaboratesItems

/-- Exact cross-avoidance premises needed by
`GeneratedItems.ScopedContextualEquivalent.cons` for an item followed by its
sequentially elaborated sibling list. -/
theorem cons_crossAvoidance
    {context : Context} {item : Expr} {items : List Expr}
    {start middle finish : Supply}
    {generatedItem : Generated} {generatedItems : GeneratedItems}
    (itemElaboration : Elaborates context item start generatedItem middle)
    (itemsElaboration : ElaboratesItems context items middle
      generatedItems finish)
    (wellFormed : start.WellFormedFor context)
    {itemHidden itemsHidden : List UnificationVar}
    (itemFresh : VariablesFreshIn start middle itemHidden)
    (itemsFresh : VariablesFreshIn middle finish itemsHidden) :
    GeneratedItemsAvoid itemHidden generatedItems ∧
      GeneratedAvoids itemsHidden generatedItem := by
  constructor
  · exact VariablesScopedBy.avoids_earlier itemFresh
      itemsElaboration.supportProvenance.scopedByInitialSupply
      wellFormed (Supply.le_refl middle)
  · exact VariablesScopedBy.avoids_later
      itemElaboration.supportProvenance.scopedByInitialSupply
      itemsFresh wellFormed itemElaboration.supply_le_next
      (Supply.le_refl middle)

end ElaboratesItems

/-- Scope-aware comparison returned by the structural induction.  Supply
equality is packaged with the hidden-name interval and contextual relation so
sequential constructors can use all three facts together. -/
def ScopedGeneratedComparison
    (start leftNext rightNext : Supply) (left right : Generated) : Prop :=
  leftNext = rightNext ∧
    ∃ hidden : List UnificationVar,
      VariablesFreshIn start leftNext hidden ∧
        Generated.ScopedContextualEquivalent hidden left right

def ScopedItemsComparison
    (start leftNext rightNext : Supply)
    (left right : GeneratedItems) : Prop :=
  leftNext = rightNext ∧
    ∃ hidden : List UnificationVar,
      VariablesFreshIn start leftNext hidden ∧
        GeneratedItems.ScopedContextualEquivalent hidden left right

end TypePM.Source
