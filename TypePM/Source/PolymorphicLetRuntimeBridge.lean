import TypePM.NoStuck
import TypePM.UnificationSupport
import TypePM.Source.ClosureSupportRenaming
import TypePM.Source.SchemeSupportBounds
import TypePM.Source.GeneratedSupportBounds
import TypePM.Source.ClosureSupportFutureFixing

/-!
# Provenance-protected runtime typing for polymorphic `let`

`RuntimeTyping` deliberately keeps an evaluator-facing `List Ty` context.
Consequently one context entry cannot itself say that a value came from a
generalized source `let`.  This module adds that information in a separate
proof-only Boolean mask.  Only entries marked by the `letPoly` rule may use
`instantiatedVar`; ordinary runtime variables keep exact lookup typing.

The protected relation is intentionally bounded.  It supplies the structural
forms needed to use one generalized value in applications, tuples, canonical
List construction, integer addition, and same-result-type conditionals, and
it can embed any already certified `RuntimeTyping` subtree.  In particular it
does not add an unrestricted `IsInstance` constructor to `RuntimeTyping` and
does not change runtime contexts to source schemes.
-/

namespace TypePM.Runtime

mutual

/-- Runtime typing with a proof-only mask recording which context entries
were introduced by a generalized source `let`.  The evaluator-facing context
remains `List Ty`; `protected` is erased before evaluation. -/
inductive ProtectedRuntimeTyping :
    (provenance : List Bool) → Source.Expr → Ty →
      (context : List Ty := []) → Prop where
  | runtime
      (typing : RuntimeTyping expression target context) :
      ProtectedRuntimeTyping provenance expression target context
  | instantiatedVar
      (typeLookup : context[index]? = some general)
      (provenanceLookup : provenance[index]? = some true)
      (instantiation : IsInstance general target) :
      ProtectedRuntimeTyping provenance (.var index) target context
  | app
      (function : ProtectedRuntimeTyping provenance functionExpression
        (.fn domain codomain) context)
      (argument : ProtectedRuntimeTyping provenance argumentExpression
        domain context) :
      ProtectedRuntimeTyping provenance
        (.app functionExpression argumentExpression) codomain context
  | tuple
      (items : ProtectedRuntimeTypings provenance expressions targets context) :
      ProtectedRuntimeTyping provenance (.tuple expressions) (.prod targets)
        context
  | listCons
      (head : ProtectedRuntimeTyping provenance headExpression element context)
      (tail : ProtectedRuntimeTyping provenance tailExpression
        (TypePM.DataTypes.list element) context) :
      ProtectedRuntimeTyping provenance
        (.ctor DataCtor.cons [headExpression, tailExpression])
        (TypePM.DataTypes.list element) context
  | add
      (left : ProtectedRuntimeTyping provenance leftExpression .int context)
      (right : ProtectedRuntimeTyping provenance rightExpression .int context) :
      ProtectedRuntimeTyping provenance
        (.prim PrimOp.add [leftExpression, rightExpression]) .int context
  | ifE
      (condition : ProtectedRuntimeTyping provenance conditionExpression
        TypePM.DataTypes.bool context)
      (thenBranch : ProtectedRuntimeTyping provenance thenExpression
        branchTarget context)
      (elseBranch : ProtectedRuntimeTyping provenance elseExpression
        branchTarget context) :
      ProtectedRuntimeTyping provenance
        (.ifE conditionExpression thenExpression elseExpression)
        branchTarget context
  | letPoly
      (value : ProtectedRuntimeTyping provenance valueExpression general context)
      (body : ProtectedRuntimeTyping (true :: provenance) bodyExpression target
        (general :: context)) :
      ProtectedRuntimeTyping provenance (.letE valueExpression bodyExpression)
        target context

/-- Pointwise protected typing for tuple children. -/
inductive ProtectedRuntimeTypings :
    List Bool → List Source.Expr → List Ty → List Ty → Prop where
  | nil : ProtectedRuntimeTypings provenance [] [] context
  | cons
      (head : ProtectedRuntimeTyping provenance expression target context)
      (tail : ProtectedRuntimeTypings provenance expressions targets context) :
      ProtectedRuntimeTypings provenance (expression :: expressions)
        (target :: targets) context

end

/-! ## Substitution stability of protected instantiations

Source elaboration applies the solution of an enclosing constraint block to
the types produced by its children.  An ordinary `RuntimeTyping` derivation
can be transported through that operation by `RuntimeTyping.applyContext`.
For a protected variable this transport is not automatic: an earlier
`IsInstance general target` witness need not remain an instance witness after
the same later substitution is applied to both sides.

`SubstitutionStable` is the exact, derivation-local missing invariant.  It
asks only for the protected variable occurrences that actually appear in the
derivation, including occurrences below nested polymorphic lets.  Runtime
subtrees need no extra evidence because their existing substitution theorem
already transports their complete monomorphic contexts.
-/

mutual

/-- Every protected instantiation used by this derivation remains valid after
one later substitution. -/
inductive ProtectedRuntimeTypingSubstitutionStable (substitution : Subst) :
    {provenance : List Bool} → {expression : Source.Expr} → {target : Ty} →
      {context : List Ty} →
      ProtectedRuntimeTyping provenance expression target context → Prop where
  | runtime (typing : RuntimeTyping expression target context) :
      ProtectedRuntimeTypingSubstitutionStable substitution (.runtime typing)
  | instantiatedVar
      (typeLookup : context[index]? = some general)
      (provenanceLookup : provenance[index]? = some true)
      (instantiation : IsInstance general target)
      (stable : IsInstance (general.apply substitution)
        (target.apply substitution)) :
      ProtectedRuntimeTypingSubstitutionStable substitution
        (.instantiatedVar typeLookup provenanceLookup instantiation)
  | app
      (functionStable : ProtectedRuntimeTypingSubstitutionStable substitution function)
      (argumentStable : ProtectedRuntimeTypingSubstitutionStable substitution argument) :
      ProtectedRuntimeTypingSubstitutionStable substitution (.app function argument)
  | tuple
      (itemsStable : ProtectedRuntimeTypingsSubstitutionStable substitution items) :
      ProtectedRuntimeTypingSubstitutionStable substitution (.tuple items)
  | listCons
      (headStable : ProtectedRuntimeTypingSubstitutionStable substitution head)
      (tailStable : ProtectedRuntimeTypingSubstitutionStable substitution tail) :
      ProtectedRuntimeTypingSubstitutionStable substitution (.listCons head tail)
  | add
      (leftStable : ProtectedRuntimeTypingSubstitutionStable substitution left)
      (rightStable : ProtectedRuntimeTypingSubstitutionStable substitution right) :
      ProtectedRuntimeTypingSubstitutionStable substitution (.add left right)
  | ifE
      (conditionStable :
        ProtectedRuntimeTypingSubstitutionStable substitution condition)
      (thenStable : ProtectedRuntimeTypingSubstitutionStable substitution thenBranch)
      (elseStable : ProtectedRuntimeTypingSubstitutionStable substitution elseBranch) :
      ProtectedRuntimeTypingSubstitutionStable substitution
        (.ifE condition thenBranch elseBranch)
  | letPoly
      (valueStable : ProtectedRuntimeTypingSubstitutionStable substitution value)
      (bodyStable : ProtectedRuntimeTypingSubstitutionStable substitution body) :
      ProtectedRuntimeTypingSubstitutionStable substitution (.letPoly value body)

/-- List counterpart of
`ProtectedRuntimeTyping.SubstitutionStable`. -/
inductive ProtectedRuntimeTypingsSubstitutionStable (substitution : Subst) :
    {provenance : List Bool} → {expressions : List Source.Expr} →
      {targets context : List Ty} →
      ProtectedRuntimeTypings provenance expressions targets context → Prop where
  | nil : ProtectedRuntimeTypingsSubstitutionStable substitution
      (.nil (provenance := provenance)
      (context := context))
  | cons
      (headStable : ProtectedRuntimeTypingSubstitutionStable substitution head)
      (tailStable : ProtectedRuntimeTypingsSubstitutionStable substitution tail) :
      ProtectedRuntimeTypingsSubstitutionStable substitution (.cons head tail)

end

abbrev ProtectedRuntimeTyping.SubstitutionStable :=
  ProtectedRuntimeTypingSubstitutionStable

abbrev ProtectedRuntimeTypings.SubstitutionStable :=
  ProtectedRuntimeTypingsSubstitutionStable

private theorem getElem?_applyList_protected
    {context : List Ty} {index : Nat} {target : Ty}
    {substitution : Subst}
    (found : context[index]? = some target) :
    (Ty.applyList substitution context)[index]? =
      some (target.apply substitution) := by
  induction context generalizing index target with
  | nil => simp at found
  | cons head tail induction =>
      cases index with
      | zero =>
          simp at found ⊢
          subst target
          rfl
      | succ index =>
          simp only [List.getElem?_cons_succ] at found ⊢
          exact induction found

mutual

/-- Transport a protected derivation through a later substitution when every
protected instantiation used by the derivation is stable under that
substitution.  The result and the plain runtime context are transported
together; the proof-only provenance mask is unchanged. -/
protected def ProtectedRuntimeTypingSubstitutionStable.applyContext
    {typing : ProtectedRuntimeTyping provenance expression target context}
    {substitution : Subst}
    (stable : ProtectedRuntimeTypingSubstitutionStable substitution typing) :
    ProtectedRuntimeTyping provenance expression (target.apply substitution)
      (Ty.applyList substitution context) :=
  match stable with
  | .runtime runtimeTyping =>
      .runtime (runtimeTyping.applyContext substitution)
  | .instantiatedVar typeLookup provenanceLookup _ stableInstantiation =>
      .instantiatedVar (getElem?_applyList_protected typeLookup)
        provenanceLookup stableInstantiation
  | .app functionStable argumentStable =>
      .app functionStable.applyContext argumentStable.applyContext
  | .tuple itemsStable =>
      .tuple itemsStable.applyContext
  | .listCons headStable tailStable =>
      .listCons headStable.applyContext tailStable.applyContext
  | .add leftStable rightStable =>
      .add leftStable.applyContext rightStable.applyContext
  | .ifE conditionStable thenStable elseStable =>
      .ifE conditionStable.applyContext thenStable.applyContext
        elseStable.applyContext
  | .letPoly valueStable bodyStable => by
      simpa [Ty.applyList] using ProtectedRuntimeTyping.letPoly
        valueStable.applyContext bodyStable.applyContext

/-- List counterpart of `ProtectedRuntimeTyping.applyContext`. -/
protected def ProtectedRuntimeTypingsSubstitutionStable.applyContext
    {typing : ProtectedRuntimeTypings provenance expressions targets context}
    {substitution : Subst}
    (stable : ProtectedRuntimeTypingsSubstitutionStable substitution typing) :
    ProtectedRuntimeTypings provenance expressions
      (Ty.applyList substitution targets)
      (Ty.applyList substitution context) :=
  match stable with
  | .nil => .nil
  | .cons headStable tailStable =>
      .cons headStable.applyContext tailStable.applyContext

end

/-- Public typing-directed form of the stability transport theorem. -/
theorem ProtectedRuntimeTyping.applyContext
    (typing : ProtectedRuntimeTyping provenance expression target context)
    (substitution : Subst)
    (stable : typing.SubstitutionStable substitution) :
    ProtectedRuntimeTyping provenance expression (target.apply substitution)
      (Ty.applyList substitution context) :=
  stable.applyContext

/-- Public list form of `ProtectedRuntimeTyping.applyContext`. -/
theorem ProtectedRuntimeTypings.applyContext
    (typing : ProtectedRuntimeTypings provenance expressions targets context)
    (substitution : Subst)
    (stable : typing.SubstitutionStable substitution) :
    ProtectedRuntimeTypings provenance expressions
      (Ty.applyList substitution targets)
      (Ty.applyList substitution context) :=
  stable.applyContext


/-- The identity substitution is stable for every protected derivation. -/
theorem ProtectedRuntimeTyping.substitutionStable_id
    (typing : ProtectedRuntimeTyping provenance expression target context) :
    typing.SubstitutionStable Subst.id := by
  exact ProtectedRuntimeTyping.rec
    (motive_1 := fun _ _ _ _ typing => typing.SubstitutionStable Subst.id)
    (motive_2 := fun _ _ _ _ typing => typing.SubstitutionStable Subst.id)
    (fun runtimeTyping => .runtime runtimeTyping)
    (fun typeLookup provenanceLookup instantiation =>
      .instantiatedVar typeLookup provenanceLookup instantiation (by
        simpa using instantiation))
    (fun _ _ functionStable argumentStable =>
      .app functionStable argumentStable)
    (fun _ itemsStable => .tuple itemsStable)
    (fun _ _ headStable tailStable => .listCons headStable tailStable)
    (fun _ _ leftStable rightStable => .add leftStable rightStable)
    (fun _ _ _ conditionStable thenStable elseStable =>
      .ifE conditionStable thenStable elseStable)
    (fun _ _ valueStable bodyStable => .letPoly valueStable bodyStable)
    .nil
    (fun _ _ headStable tailStable => .cons headStable tailStable)
    typing

/-- List counterpart of
`ProtectedRuntimeTyping.substitutionStable_id`. -/
theorem ProtectedRuntimeTypings.substitutionStable_id
    (typing : ProtectedRuntimeTypings provenance expressions targets context) :
    typing.SubstitutionStable Subst.id := by
  exact ProtectedRuntimeTypings.rec
    (motive_1 := fun _ _ _ _ typing => typing.SubstitutionStable Subst.id)
    (motive_2 := fun _ _ _ _ typing => typing.SubstitutionStable Subst.id)
    (fun runtimeTyping => .runtime runtimeTyping)
    (fun typeLookup provenanceLookup instantiation =>
      .instantiatedVar typeLookup provenanceLookup instantiation (by
        simpa using instantiation))
    (fun _ _ functionStable argumentStable =>
      .app functionStable argumentStable)
    (fun _ itemsStable => .tuple itemsStable)
    (fun _ _ headStable tailStable => .listCons headStable tailStable)
    (fun _ _ leftStable rightStable => .add leftStable rightStable)
    (fun _ _ _ conditionStable thenStable elseStable =>
      .ifE conditionStable thenStable elseStable)
    (fun _ _ valueStable bodyStable => .letPoly valueStable bodyStable)
    .nil
    (fun _ _ headStable tailStable => .cons headStable tailStable)
    typing

/-! `PrincipalBlockClosure` supplies most-generality and `Context.generalize`
identifies variables absent from the source context.  Those facts alone do
not say that an arbitrary *later* substitution fixes the stored general type
or a particular instantiated use.  The first lemma below records a simple
strong sufficient condition.  The support-local theorem after it weakens
this to fixedness of the stored general type alone and derives that fact from
the actual let-body support. -/

/-- An instance witness remains valid under a later substitution when that
later substitution is observationally irrelevant to both endpoints. -/
theorem isInstance_apply_of_fixed
    (instantiation : IsInstance general target)
    (generalFixed : general.apply later = general)
    (targetFixed : target.apply later = target) :
    IsInstance (general.apply later) (target.apply later) := by
  simpa [generalFixed, targetFixed] using instantiation

/-- Fixing the stored general type is sufficient: the original
instantiation witness can be followed by the later substitution.  The
concrete occurrence type itself may change. -/
theorem isInstance_apply_of_general_fixed
    (instantiation : IsInstance general target)
    (generalFixed : general.apply later = general) :
    IsInstance (general.apply later) (target.apply later) := by
  rcases instantiation with ⟨witness, targetEquality⟩
  refine ⟨Subst.compose later witness, ?_⟩
  rw [generalFixed, ← Ty.apply_compose, targetEquality]

/-! ## Automatic stability from finite-support separation

The source closure machinery already records substitutions as localized to a
finite list of ordinary and capability variables.  A protected use is
therefore stable whenever its stored general type avoids that finite support.
The concrete occurrence type need not be fixed: its instantiation witness is
post-composed with the later substitution.  The judgments below collect
exactly this occurrence-local fact and derive `SubstitutionStable` for the
complete protected derivation in one structural pass.
-/

/-- No variable occurring in `target` belongs to `support`. -/
def TypeAvoidsSupport (target : Ty) (support : List UnificationVar) : Prop :=
  ∀ candidate, candidate ∈ target.unificationVars → candidate ∉ support

/-- Every variable in a type lies strictly below one source supply. -/
def TypeSupportBelowSupply (target : Ty) (boundary : Source.Supply) : Prop :=
  ∀ candidate, candidate ∈ target.unificationVars →
    candidate.Below boundary.ty boundary.cap

/-- Source support provenance proves disjointness automatically when the
stored general type is below the child's fresh allocation boundary and does
not mention a free variable of the child context. -/
theorem typeAvoidsSupport_of_generatedSupportProvenance
    {target : Ty} {context : Source.Context} {start finish : Source.Supply}
    {generated : Generated}
    (below : TypeSupportBelowSupply target start)
    (avoidsContext : ∀ candidate,
      candidate ∈ target.unificationVars →
        candidate ∉ TypePM.Source.Context.unificationVars context)
    (provenance : TypePM.Source.GeneratedSupportProvenance
      context start finish generated) :
    TypeAvoidsSupport target (TypePM.Generated.unificationVars generated) := by
  intro candidate targetMember generatedMember
  rcases provenance candidate generatedMember with contextMember | fresh
  · exact avoidsContext candidate targetMember contextMember
  · have targetBelow := below candidate targetMember
    cases candidate with
    | ty index => exact (Nat.not_lt_of_ge fresh.1) targetBelow
    | cap index => exact (Nat.not_lt_of_ge fresh.1) targetBelow

/-- A substitution localized to a disjoint support fixes the whole type. -/
theorem type_apply_eq_self_of_localized_avoids
    {target : Ty}
    (localized : Subst.Localized support substitution)
    (avoids : TypeAvoidsSupport target support) :
    target.apply substitution = target := by
  calc
    target.apply substitution = target.apply Subst.id := by
      apply TypePM.Source.Ty.apply_eq_of_agree target
      · intro index member
        exact localized.fixesTy index
          (avoids (.ty index)
            ((TypePM.Source.Ty.mem_tyVars_iff_unificationVars index target).mp
              member))
      · intro index member
        exact localized.fixesCap index
          (avoids (.cap index)
            ((TypePM.Source.Ty.mem_capVars_iff_unificationVars index target).mp
              member))
    _ = target := Ty.apply_id target

/-- Support-local form of protected-instantiation stability.  Only the
general type must be separated from the localized substitution support. -/
theorem isInstance_apply_of_localized_general_avoids
    (instantiation : IsInstance general target)
    (localized : Subst.Localized support later)
    (generalAvoids : TypeAvoidsSupport general support) :
    IsInstance (general.apply later) (target.apply later) :=
  isInstance_apply_of_general_fixed instantiation
    (type_apply_eq_self_of_localized_avoids localized generalAvoids)

mutual

  /-- Every protected occurrence in one derivation avoids a finite support.
  Runtime-only subtrees contain no protected instantiation and need no
  additional premise. -/
  inductive ProtectedRuntimeTypingSupportSeparated
      (support : List UnificationVar) :
      {provenance : List Bool} → {expression : Source.Expr} → {target : Ty} →
        {context : List Ty} →
        (typing : ProtectedRuntimeTyping provenance expression target context) →
        Prop where
    | runtime (typing : RuntimeTyping expression target context) :
        ProtectedRuntimeTypingSupportSeparated support (.runtime typing)
    | instantiatedVar
        (typeLookup : context[index]? = some general)
        (provenanceLookup : provenance[index]? = some true)
        (instantiation : IsInstance general target)
        (generalAvoids : TypeAvoidsSupport general support) :
        ProtectedRuntimeTypingSupportSeparated support
          (.instantiatedVar typeLookup provenanceLookup instantiation)
    | app
        (functionSeparated :
          ProtectedRuntimeTypingSupportSeparated support function)
        (argumentSeparated :
          ProtectedRuntimeTypingSupportSeparated support argument) :
        ProtectedRuntimeTypingSupportSeparated support (.app function argument)
    | tuple
        (itemsSeparated :
          ProtectedRuntimeTypingsSupportSeparated support items) :
        ProtectedRuntimeTypingSupportSeparated support (.tuple items)
    | listCons
        (headSeparated : ProtectedRuntimeTypingSupportSeparated support head)
        (tailSeparated : ProtectedRuntimeTypingSupportSeparated support tail) :
        ProtectedRuntimeTypingSupportSeparated support (.listCons head tail)
    | add
        (leftSeparated : ProtectedRuntimeTypingSupportSeparated support left)
        (rightSeparated : ProtectedRuntimeTypingSupportSeparated support right) :
        ProtectedRuntimeTypingSupportSeparated support (.add left right)
    | ifE
        (conditionSeparated :
          ProtectedRuntimeTypingSupportSeparated support condition)
        (thenSeparated : ProtectedRuntimeTypingSupportSeparated support thenBranch)
        (elseSeparated : ProtectedRuntimeTypingSupportSeparated support elseBranch) :
        ProtectedRuntimeTypingSupportSeparated support
          (.ifE condition thenBranch elseBranch)
    | letPoly
        (valueSeparated :
          ProtectedRuntimeTypingSupportSeparated support value)
        (bodySeparated :
          ProtectedRuntimeTypingSupportSeparated support body) :
        ProtectedRuntimeTypingSupportSeparated support (.letPoly value body)

  /-- Pointwise support separation for tuple children. -/
  inductive ProtectedRuntimeTypingsSupportSeparated
      (support : List UnificationVar) :
      {provenance : List Bool} → {expressions : List Source.Expr} →
        {targets context : List Ty} →
        (typing : ProtectedRuntimeTypings provenance expressions targets context) →
        Prop where
    | nil : ProtectedRuntimeTypingsSupportSeparated support
        (.nil (provenance := provenance) (context := context))
    | cons
        (headSeparated :
          ProtectedRuntimeTypingSupportSeparated support head)
        (tailSeparated :
          ProtectedRuntimeTypingsSupportSeparated support tail) :
        ProtectedRuntimeTypingsSupportSeparated support (.cons head tail)

end

abbrev ProtectedRuntimeTyping.SupportSeparated :=
  ProtectedRuntimeTypingSupportSeparated

abbrev ProtectedRuntimeTypings.SupportSeparated :=
  ProtectedRuntimeTypingsSupportSeparated

/-- Construct the support-separation certificate for one protected variable
directly from the actual source elaboration of the later body.  The two
numeric premises describe the already generalized type: its variables are
below the body's fresh start and are not free in the body's source context.
No fixedness equality for the solver substitution is supplied by the caller.
-/
theorem ProtectedRuntimeTypingSupportSeparated.instantiatedVarOfElaboration
    (elaboration : Source.Elaborates signature sourceContext sourceExpression
      start generated finish)
    (generalBelow : TypeSupportBelowSupply general start)
    (generalNotFree : ∀ candidate,
      candidate ∈ general.unificationVars →
        candidate ∉ TypePM.Source.Context.unificationVars sourceContext)
    (typeLookup : runtimeContext[index]? = some general)
    (provenanceLookup : provenance[index]? = some true)
    (instantiation : IsInstance general target) :
    ProtectedRuntimeTypingSupportSeparated
      (TypePM.Generated.unificationVars generated)
      (ProtectedRuntimeTyping.instantiatedVar typeLookup provenanceLookup
        instantiation) :=
  .instantiatedVar typeLookup provenanceLookup instantiation
    (typeAvoidsSupport_of_generatedSupportProvenance generalBelow generalNotFree
      elaboration.supportProvenance)

/-- Actual source-`let` boundary form.  The value elaboration, its absorbing
principal closure, and the body elaboration determine both the stored
general type and the later generated support.  The numeric separation of the
general type is derived from the value's supply/support theorem; the only
remaining premise says that the generalized type has no free occurrence in
the body context (automatic for variables genuinely bound by `generalize`).
-/
theorem ProtectedRuntimeTypingSupportSeparated.instantiatedVarOfLetBody
    (valueElaboration : Source.Elaborates signature context valueExpression
      start generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (startWellFormed : start.WellFormedFor context)
    (bodyElaboration : Source.Elaborates signature
      ((context.applyFree closure.substitution).generalize closure.target ::
        context.applyFree closure.substitution)
      bodyExpression
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply)
      generatedBody finish)
    (generalNotFree : ∀ candidate,
      candidate ∈ closure.target.unificationVars →
        candidate ∉ TypePM.Source.Context.unificationVars
          ((context.applyFree closure.substitution).generalize closure.target ::
            context.applyFree closure.substitution))
    (typeLookup : runtimeContext[index]? = some closure.target)
    (provenanceLookup : provenance[index]? = some true)
    (instantiation : IsInstance closure.target target) :
    ProtectedRuntimeTypingSupportSeparated
      (TypePM.Generated.unificationVars generatedBody)
      (ProtectedRuntimeTyping.instantiatedVar typeLookup provenanceLookup
        instantiation) := by
  have valueSupportBelow : ∀ candidate,
      candidate ∈ TypePM.Generated.unificationVars generatedValue →
        candidate.Below afterValue.ty afterValue.cap :=
    valueElaboration.supportProvenance.below startWellFormed
      valueElaboration.supply_le_next
  have generalBelowAfter : TypeSupportBelowSupply closure.target afterValue :=
    TypePM.Source.PrincipalBlockClosure.target_support_below closure absorbing
      afterValue valueSupportBelow
  have afterToBodyStart : afterValue.Le
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply) :=
    Source.Supply.le_join_left _ _
  have generalBelowBody : TypeSupportBelowSupply closure.target
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply) := by
    intro candidate member
    have below := generalBelowAfter candidate member
    cases candidate with
    | ty index => exact Nat.lt_of_lt_of_le below afterToBodyStart.1
    | cap index => exact Nat.lt_of_lt_of_le below afterToBodyStart.2
  exact .instantiatedVarOfElaboration bodyElaboration generalBelowBody
    generalNotFree typeLookup provenanceLookup instantiation

/-- Closed-outer-context specialization of the actual `let` boundary.  Here
`generalize` binds every variable of the value's principal target, so the
body context contains no free occurrence of that target and the final
separation premise is discharged automatically. -/
theorem ProtectedRuntimeTypingSupportSeparated.instantiatedVarOfClosedLetBody
    (valueElaboration : Source.Elaborates signature [] valueExpression
      start generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (startWellFormed : start.WellFormedFor ([] : Source.Context))
    (bodyElaboration : Source.Elaborates signature
      (Source.Context.generalize
          (Source.Context.applyFree closure.substitution ([] : Source.Context))
          closure.target ::
        Source.Context.applyFree closure.substitution ([] : Source.Context))
      bodyExpression
      (afterValue.join
        (Source.Context.initialSupply
          (Source.Context.applyFree closure.substitution
            ([] : Source.Context))))
      generatedBody finish)
    (typeLookup : runtimeContext[index]? = some closure.target)
    (provenanceLookup : provenance[index]? = some true)
    (instantiation : IsInstance closure.target target) :
    ProtectedRuntimeTypingSupportSeparated
      (TypePM.Generated.unificationVars generatedBody)
      (ProtectedRuntimeTyping.instantiatedVar typeLookup provenanceLookup
        instantiation) := by
  apply ProtectedRuntimeTypingSupportSeparated.instantiatedVarOfLetBody
    valueElaboration closure absorbing
    startWellFormed bodyElaboration
  · intro candidate targetMember bodyContextMember
    have outerMember := TypePM.Source.Context.generalized_cons_support_subset
      (Source.Context.applyFree closure.substitution ([] : Source.Context))
      closure.target
      candidate bodyContextMember
    simp [Source.Context.applyFree, Source.Context.unificationVars,
      Source.Context.freeTyVars, Source.Context.freeCapVars, dedupFirst, dedup]
      at outerMember
  · exact typeLookup
  · exact provenanceLookup
  · exact instantiation

mutual

  /-- Finite-support separation automatically supplies every protected
  occurrence required by `SubstitutionStable`. -/
  theorem ProtectedRuntimeTypingSupportSeparated.substitutionStable
      (separated : ProtectedRuntimeTypingSupportSeparated support typing)
      (localized : Subst.Localized support substitution) :
      typing.SubstitutionStable substitution := by
    cases separated with
    | runtime typing => exact .runtime typing
    | instantiatedVar typeLookup provenanceLookup instantiation generalAvoids =>
        exact .instantiatedVar typeLookup provenanceLookup instantiation
          (isInstance_apply_of_localized_general_avoids instantiation localized
            generalAvoids)
    | app functionSeparated argumentSeparated =>
        exact .app
          (functionSeparated.substitutionStable localized)
          (argumentSeparated.substitutionStable localized)
    | tuple itemsSeparated =>
        exact .tuple (itemsSeparated.substitutionStable localized)
    | listCons headSeparated tailSeparated =>
        exact .listCons
          (headSeparated.substitutionStable localized)
          (tailSeparated.substitutionStable localized)
    | add leftSeparated rightSeparated =>
        exact .add
          (leftSeparated.substitutionStable localized)
          (rightSeparated.substitutionStable localized)
    | ifE conditionSeparated thenSeparated elseSeparated =>
        exact .ifE
          (conditionSeparated.substitutionStable localized)
          (thenSeparated.substitutionStable localized)
          (elseSeparated.substitutionStable localized)
    | letPoly valueSeparated bodySeparated =>
        exact .letPoly
          (valueSeparated.substitutionStable localized)
          (bodySeparated.substitutionStable localized)

  /-- List counterpart of automatic stability from support separation. -/
  theorem ProtectedRuntimeTypingsSupportSeparated.substitutionStable
      (separated : ProtectedRuntimeTypingsSupportSeparated support typing)
      (localized : Subst.Localized support substitution) :
      typing.SubstitutionStable substitution := by
    cases separated with
    | nil => exact .nil
    | cons headSeparated tailSeparated =>
        exact .cons
          (headSeparated.substitutionStable localized)
          (tailSeparated.substitutionStable localized)

end

/-- Public transport endpoint requiring only localization and the structural
support-separation certificate, rather than a hand-built stability proof. -/
theorem ProtectedRuntimeTyping.applyContextOfLocalized
    (typing : ProtectedRuntimeTyping provenance expression target context)
    (localized : Subst.Localized support substitution)
    (separated : typing.SupportSeparated support) :
    ProtectedRuntimeTyping provenance expression (target.apply substitution)
      (Ty.applyList substitution context) :=
  typing.applyContext substitution (separated.substitutionStable localized)

/-- List form of `ProtectedRuntimeTyping.applyContextOfLocalized`. -/
theorem ProtectedRuntimeTypings.applyContextOfLocalized
    (typing : ProtectedRuntimeTypings provenance expressions targets context)
    (localized : Subst.Localized support substitution)
    (separated : typing.SupportSeparated support) :
    ProtectedRuntimeTypings provenance expressions
      (Ty.applyList substitution targets)
      (Ty.applyList substitution context) :=
  typing.applyContext substitution (separated.substitutionStable localized)

/-! ## The actual closed source-`let` boundary

The following certificate does not attempt to manufacture a complete runtime
typing derivation from source syntax.  It exposes the precise reusable fact
provided by an actual relational `letE` derivation: the generalized value's
bound variable is separated from the support generated later by the body.
-/

/-- The value and body elaborations hidden inside a closed source `letE`,
together with the automatically separated protected self-instantiation of
the generalized value.  This is the local source-to-runtime fact needed at a
bound-variable occurrence; building an entire protected runtime derivation
still requires a syntax-directed bridge for the surrounding body. -/
inductive ClosedLetBoundVariableSupportSeparated
    (signature : Source.Signature) (value body : Source.Expr) : Prop where
  | intro {generatedValue : Generated} {afterValue : Source.Supply}
      {closure : PrincipalBlockClosure generatedValue}
      {generatedBody : Generated} {finish : Source.Supply}
      (valueElaboration : Source.Elaborates signature [] value
        (Source.Context.initialSupply []) generatedValue afterValue)
      (absorbing : closure.Absorbing)
      (bodyElaboration : Source.Elaborates signature
        (Source.Context.generalize
            (Source.Context.applyFree closure.substitution
              ([] : Source.Context))
            closure.target ::
          Source.Context.applyFree closure.substitution ([] : Source.Context))
        body
        (afterValue.join
          (Source.Context.initialSupply
            (Source.Context.applyFree closure.substitution
              ([] : Source.Context))))
        generatedBody finish)
      (protectedUse : ProtectedRuntimeTyping [true] (.var 0) closure.target
        [closure.target])
      (separated : protectedUse.SupportSeparated
        (TypePM.Generated.unificationVars generatedBody)) :
      ClosedLetBoundVariableSupportSeparated signature value body

/-- Destructing the relational elaboration stored by a closed principal
`letE` automatically yields its body-support separation certificate.  In
particular, callers do not supply a disjointness or fixedness hypothesis. -/
theorem closedPrincipalLetBoundVariableSupportSeparated
    (derivation : Source.PrincipalTypingDerivation signature []
      (.letE value body) target) :
    ClosedLetBoundVariableSupportSeparated signature value body := by
  cases derivation with
  | mk generated next elaboration rootClosure rootAbsorbing targetEquality =>
      cases elaboration with
      | letE valueElaboration closure absorbing bodyElaboration =>
          let protectedUse : ProtectedRuntimeTyping [true] (.var 0)
              closure.target [closure.target] :=
            .instantiatedVar rfl rfl
              ⟨Subst.id, Ty.apply_id closure.target⟩
          exact .intro valueElaboration absorbing bodyElaboration protectedUse
            (ProtectedRuntimeTypingSupportSeparated.instantiatedVarOfClosedLetBody
                valueElaboration closure absorbing
                (Source.Supply.wellFormedFor_initialSupply [])
                bodyElaboration rfl rfl
                ⟨Subst.id, Ty.apply_id closure.target⟩)

/-- Successful public inference of a closed `letE` supplies the same local
body-support certificate.  This endpoint is fully automatic: its only
premises are signature well-formedness and the ordinary inference success
equation. -/
theorem inferSuccessClosedLetBoundVariableSupportSeparated
    {signature : Source.Signature} {value body : Source.Expr} {target : Ty}
    (wellFormed : signature.WellFormed)
    (success : Source.infer signature [] (.letE value body) = some target) :
    ClosedLetBoundVariableSupportSeparated signature value body := by
  rcases Source.Inference.infer_success_principalTyping wellFormed success with
    ⟨derivation⟩
  exact closedPrincipalLetBoundVariableSupportSeparated derivation

/-! ## Syntax-directed bridge for protected first-order bodies

This is the general body bridge needed below a closure that captures a
generalized binding.  It covers variables, literals, `something`, canonical
Boolean/List constructors, applications, tuples, integer addition, and
same-result-type conditionals.  Applications are restricted to ordinary
equality checks; matcher-to-slot conversions belong to the larger M4 runtime
bridge.  A nested polymorphic `let` remains a separate representative-closure
problem and is intentionally not hidden in this syntax judgment.
-/

/-- A semantic solution in which pending checks are ordinary equalities. -/
structure StrictGeneratedSemanticSolution
    (generated : Generated) (solution : Subst) : Prop where
  hard : Solves solution generated.hard
  pending : ∀ obligation ∈ generated.pending,
    obligation.source.apply solution = obligation.expected.apply solution

/-- List counterpart of `StrictGeneratedSemanticSolution`. -/
structure StrictGeneratedItemsSemanticSolution
    (generated : GeneratedItems) (solution : Subst) : Prop where
  hard : Solves solution generated.hard
  pending : ∀ obligation ∈ generated.pending,
    obligation.source.apply solution = obligation.expected.apply solution

/-- Exact M2 closure-side condition for the strict body bridge.  It does not
claim that all source checks are equalities: it requires this only for the
checks retained by the hard-saturation phase of this particular block. -/
def ClosureRemainingChecksOrdinary
    {generated : Generated} (closure : PrincipalBlockClosure generated) : Prop :=
  ∀ obligation ∈ closure.finalPending,
    CheckConversion .ordinary
      (obligation.source.apply closure.substitution)
      (obligation.expected.apply closure.substitution)

private theorem ordinaryCheckConversion_eq
    (conversion : CheckConversion .ordinary source target) :
    source = target := by
  cases conversion
  rfl

/-- Hard saturation already turns promoted checks into solved equations;
`RemainingChecksOrdinary` supplies equality for precisely the checks that
remain pending.  Together they yield the strict semantic solution required
by the protected first-order body bridge. -/
theorem strictSemanticSolution_of_closure
    {generated : Generated} (closure : PrincipalBlockClosure generated)
    (ordinary : ClosureRemainingChecksOrdinary closure) :
    StrictGeneratedSemanticSolution generated closure.substitution := by
  constructor
  · intro equation membership
    exact closure.finalHard_solved equation
      (closure.saturation.closure.hard_mem_final equation membership)
  · intro obligation membership
    rcases closure.saturation.closure.pending_covered obligation membership with
      retained | promoted
    · exact ordinaryCheckConversion_eq (ordinary obligation retained)
    · exact closure.finalHard_solved
        (.ty obligation.source obligation.expected) promoted

/-- Source schemes and the erased runtime context agree at every lookup.
An unprotected entry has the exact instantiated type.  A protected entry
stores one general runtime type and proves that every source occurrence is
an instance of it. -/
structure ProtectedContextCompatible
    (sourceContext : Source.Context) (runtimeContext : List Ty)
    (provenance : List Bool) (solution : Subst) : Prop where
  lookup : ∀ {index : Nat} {scheme : Source.Scheme}
      (supply : Source.Supply),
    sourceContext[index]? = some scheme →
      (provenance[index]? = some false ∧
        runtimeContext[index]? =
          some ((scheme.instantiate supply).1.apply solution)) ∨
      ∃ general,
        provenance[index]? = some true ∧
        runtimeContext[index]? = some general ∧
        IsInstance general ((scheme.instantiate supply).1.apply solution)

namespace ProtectedContextCompatible

private theorem sourceScheme_mem_of_getElem?_eq_some
    {context : Source.Context} {index : Nat} {scheme : Source.Scheme}
    (lookup : context[index]? = some scheme) :
    scheme ∈ context := by
  induction context generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          simp at lookup
          subst scheme
          simp
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          exact List.mem_cons_of_mem head (induction lookup)

/-- Applying a closed child block and then the parent's later solution to a
source-scheme occurrence is observationally the same as applying the later
solution directly, provided the let-boundary interface equations hold. -/
private theorem instantiate_applyFree_apply_eq_of_interface
    {context : Source.Context} {scheme : Source.Scheme}
    (schemeMember : scheme ∈ context)
    (block later : Subst)
    (solved : Solves later (context.interfaceEquations block))
    (supply : Source.Supply) :
    ((scheme.applyFree block).instantiate supply).1.apply later =
      (scheme.instantiate supply).1.apply later := by
  have agree :=
    (context.solves_interfaceEquations_iff block later).mp solved
  have bodyEquality :
      (scheme.body.applyFree block).applyFree later =
        scheme.body.applyFree later := by
    rw [Source.PolyTy.applyFree_compose]
    apply Source.PolyTy.applyFree_eq_of_agree
    · intro index membership
      exact (agree.1 index (by
        apply mem_dedupFirst.mpr
        exact List.mem_flatMap.mpr ⟨scheme, schemeMember,
          Source.Scheme.mem_freeTyVars.mpr membership⟩)).symm
    · intro index membership
      exact (agree.2 index (by
        apply mem_dedupFirst.mpr
        exact List.mem_flatMap.mpr ⟨scheme, schemeMember,
          Source.Scheme.mem_freeCapVars.mpr membership⟩)).symm
  unfold Source.Scheme.instantiate Source.Scheme.applyFree
  rw [← Source.PolyTy.openBound_applyFree,
    ← Source.PolyTy.openBound_applyFree, bodyEquality]

/-- Transport source/runtime context compatibility through the exact
interface equations exported by a nested source `let`.  The runtime context
and its provenance mask do not change. -/
theorem ofApplyFreeInterface
    (compatible : ProtectedContextCompatible sourceContext runtimeContext
      provenance later)
    (solved : Solves later (sourceContext.interfaceEquations block)) :
    ProtectedContextCompatible (sourceContext.applyFree block)
      runtimeContext provenance later := by
  constructor
  intro index transformedScheme supply lookup
  simp only [Source.Context.applyFree, List.getElem?_map] at lookup
  cases originalLookup : sourceContext[index]? with
  | none => simp [originalLookup] at lookup
  | some scheme =>
      simp only [originalLookup, Option.map_some, Option.some.injEq] at lookup
      subst transformedScheme
      have schemeMember := sourceScheme_mem_of_getElem?_eq_some originalLookup
      have targetEquality := instantiate_applyFree_apply_eq_of_interface
        schemeMember block later solved supply
      rcases compatible.lookup supply originalLookup with ordinary | protectedCase
      · rcases ordinary with ⟨provenanceLookup, runtimeLookup⟩
        exact .inl ⟨provenanceLookup, runtimeLookup.trans
          (congrArg some targetEquality.symm)⟩
      · rcases protectedCase with
          ⟨general, provenanceLookup, runtimeLookup, instantiation⟩
        exact .inr ⟨general, provenanceLookup, runtimeLookup, by
          rw [targetEquality]
          exact instantiation⟩

/-- The canonical fresh ranges are renamed to the corresponding ranges of a
second instantiation; all names outside those ranges follow `later`. -/
def canonicalInstanceSubstitution
    (canonicalSupply otherSupply : Source.Supply) (later : Subst) : Subst :=
  { ty := fun index =>
      if canonicalSupply.ty ≤ index.index then
        later.ty ⟨otherSupply.ty + (index.index - canonicalSupply.ty)⟩
      else later.ty index
    cap := fun index =>
      if canonicalSupply.cap ≤ index.index then
        later.cap ⟨otherSupply.cap + (index.index - canonicalSupply.cap)⟩
      else later.cap index }

theorem canonicalInstanceSubstitution_ty_hit
    :
    (canonicalInstanceSubstitution canonicalSupply otherSupply later).ty
        (Source.Scheme.boundTyInstance canonicalSupply position) =
      later.ty (Source.Scheme.boundTyInstance otherSupply position) := by
  simp [canonicalInstanceSubstitution, Source.Scheme.boundTyInstance]

theorem canonicalInstanceSubstitution_cap_hit
    :
    (canonicalInstanceSubstitution canonicalSupply otherSupply later).cap
        (Source.Scheme.boundCapInstance canonicalSupply position) =
      later.cap (Source.Scheme.boundCapInstance otherSupply position) := by
  simp [canonicalInstanceSubstitution, Source.Scheme.boundCapInstance]

theorem canonicalInstanceSubstitution_agrees_ty_free
    {scheme : Source.Scheme}
    (below : ∀ index ∈ scheme.freeTyVars, index.index < canonicalSupply.ty)
    (membership : index ∈ scheme.freeTyVars) :
    (canonicalInstanceSubstitution canonicalSupply otherSupply later).ty
        index = later.ty index := by
  simp [canonicalInstanceSubstitution,
    Nat.not_le_of_gt (below index membership)]

theorem canonicalInstanceSubstitution_agrees_cap_free
    {scheme : Source.Scheme}
    (below : ∀ index ∈ scheme.freeCapVars, index.index < canonicalSupply.cap)
    (membership : index ∈ scheme.freeCapVars) :
    (canonicalInstanceSubstitution canonicalSupply otherSupply later).cap
        index = later.cap index := by
  simp [canonicalInstanceSubstitution,
    Nat.not_le_of_gt (below index membership)]

/-- Any later-applied instantiation is an instance of one fixed canonical
fresh instantiation, provided the canonical ranges begin above all free names
of the scheme. -/
theorem canonicalInstantiate_isInstance
    {scheme : Source.Scheme} {canonicalSupply otherSupply : Source.Supply}
    {later : Subst}
    (freeTyBelow : ∀ index ∈ scheme.freeTyVars,
      index.index < canonicalSupply.ty)
    (freeCapBelow : ∀ index ∈ scheme.freeCapVars,
      index.index < canonicalSupply.cap) :
    IsInstance (scheme.instantiate canonicalSupply).1
      ((scheme.instantiate otherSupply).1.apply later) := by
  let witness := canonicalInstanceSubstitution canonicalSupply otherSupply later
  refine ⟨witness, ?_⟩
  unfold Source.Scheme.instantiate
  rw [← TypePM.Source.PolyTy.openBound_applyFree,
    ← TypePM.Source.PolyTy.openBound_applyFree]
  have bodyAgreement : scheme.body.applyFree witness =
      scheme.body.applyFree later := by
    apply TypePM.Source.PolyTy.applyFree_eq_of_agree
    · intro index membership
      exact canonicalInstanceSubstitution_agrees_ty_free freeTyBelow
        (Source.Scheme.mem_freeTyVars.mpr membership)
    · intro index membership
      exact canonicalInstanceSubstitution_agrees_cap_free freeCapBelow
        (Source.Scheme.mem_freeCapVars.mpr membership)
  rw [bodyAgreement]
  congr 1
  · funext position
    exact canonicalInstanceSubstitution_ty_hit
  · funext position
    exact canonicalInstanceSubstitution_cap_hit

theorem nil : ProtectedContextCompatible [] [] [] solution := by
  constructor
  intro index scheme supply lookup
  simp at lookup

/-- Extending a bridge context by one monomorphic lambda parameter. -/
theorem mono
    (tail : ProtectedContextCompatible sourceContext runtimeContext provenance
      solution) :
    ProtectedContextCompatible (.mono sourceTarget :: sourceContext)
      (sourceTarget.apply solution :: runtimeContext) (false :: provenance)
      solution := by
  constructor
  intro index scheme supply lookup
  cases index with
  | zero =>
      simp at lookup ⊢
      subst scheme
      simp [Source.Scheme.instantiate_mono]
  | succ index =>
      simp only [List.getElem?_cons_succ] at lookup ⊢
      rcases tail.lookup supply lookup with ordinary | protectedCase
      · exact .inl ordinary
      · exact .inr protectedCase

/-- Extending a bridge context by one protected generalized entry. -/
theorem pushProtected
    {scheme : Source.Scheme}
    {general : Ty} {solution : Subst}
    {sourceContext : Source.Context} {runtimeContext : List Ty}
    {provenance : List Bool}
    (instances : ∀ supply,
      IsInstance general ((scheme.instantiate supply).1.apply solution))
    (tail : ProtectedContextCompatible sourceContext runtimeContext provenance
      solution) :
    ProtectedContextCompatible (scheme :: sourceContext)
      (general :: runtimeContext) (true :: provenance) solution := by
  constructor
  intro index foundScheme supply lookup
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst foundScheme
      exact Or.inr ⟨general, rfl, rfl, instances supply⟩
  | succ index =>
      simp only [List.getElem?_cons_succ] at lookup ⊢
      rcases tail.lookup supply lookup with ordinary | protectedCase
      · exact .inl ordinary
      · exact .inr protectedCase

/-- Canonical-instance form of `pushProtected`; the instance family is now
derived from freshness rather than supplied by the caller. -/
theorem pushCanonical
    {scheme : Source.Scheme} {canonicalSupply : Source.Supply}
    {sourceContext : Source.Context} {runtimeContext : List Ty}
    {provenance : List Bool} {solution : Subst}
    (freeTyBelow : ∀ index ∈ scheme.freeTyVars,
      index.index < canonicalSupply.ty)
    (freeCapBelow : ∀ index ∈ scheme.freeCapVars,
      index.index < canonicalSupply.cap)
    (tail : ProtectedContextCompatible sourceContext runtimeContext provenance
      solution) :
    ProtectedContextCompatible (scheme :: sourceContext)
      ((scheme.instantiate canonicalSupply).1 :: runtimeContext)
      (true :: provenance) solution :=
  pushProtected
    (fun _otherSupply => canonicalInstantiate_isInstance freeTyBelow freeCapBelow)
    tail

end ProtectedContextCompatible

mutual

  /-- Syntax fragment whose relational elaboration can be translated to
  `ProtectedRuntimeTyping` without introducing another closure boundary. -/
  inductive ProtectedBodySupported : Source.Expr → Prop where
    | var : ProtectedBodySupported (.var index)
    | lit : ProtectedBodySupported (.lit value)
    | something : ProtectedBodySupported .something
    | boolTrue : ProtectedBodySupported (.ctor DataCtor.true [])
    | boolFalse : ProtectedBodySupported (.ctor DataCtor.false [])
    | listNil : ProtectedBodySupported (.ctor DataCtor.nil [])
    | listCons
        (head : ProtectedBodySupported headExpression)
        (tail : ProtectedBodySupported tailExpression) :
        ProtectedBodySupported
          (.ctor DataCtor.cons [headExpression, tailExpression])
    | app
        (function : ProtectedBodySupported functionExpression)
        (argument : ProtectedBodySupported argumentExpression) :
        ProtectedBodySupported (.app functionExpression argumentExpression)
    | add
        (left : ProtectedBodySupported leftExpression)
        (right : ProtectedBodySupported rightExpression) :
        ProtectedBodySupported (.prim PrimOp.add [leftExpression, rightExpression])
    | tuple (items : ProtectedBodiesSupported expressions) :
        ProtectedBodySupported (.tuple expressions)
    | ifE
        (condition : ProtectedBodySupported conditionExpression)
        (thenBranch : ProtectedBodySupported thenExpression)
        (elseBranch : ProtectedBodySupported elseExpression) :
        ProtectedBodySupported
          (.ifE conditionExpression thenExpression elseExpression)

  /-- Pointwise syntax coverage for tuple children. -/
  inductive ProtectedBodiesSupported : List Source.Expr → Prop where
    | nil : ProtectedBodiesSupported []
    | cons
        (head : ProtectedBodySupported expression)
        (tail : ProtectedBodiesSupported expressions) :
        ProtectedBodiesSupported (expression :: expressions)

end

private theorem strict_fromApp
    (semantic :
      StrictGeneratedSemanticSolution
        (Source.Generated.fromApp function argument domain target) solution) :
    StrictGeneratedSemanticSolution function solution ∧
      StrictGeneratedSemanticSolution argument solution ∧
      Equation.Holds solution (.ty function.target (.fn domain target)) ∧
      argument.target.apply solution = domain.apply solution := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro equation membership
    exact semantic.hard equation (by
      simp only [Source.Generated.fromApp, List.mem_append]
      exact .inl (.inl membership))
  · intro obligation membership
    exact semantic.pending obligation (by
      simp only [Source.Generated.fromApp, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact .inl (.inl membership))
  · intro equation membership
    exact semantic.hard equation (by
      simp only [Source.Generated.fromApp, List.mem_append]
      exact .inl (.inr membership))
  · intro obligation membership
    exact semantic.pending obligation (by
      simp only [Source.Generated.fromApp, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact .inl (.inr membership))
  · exact semantic.hard _ (by simp [Source.Generated.fromApp])
  · exact semantic.pending _ (by
      simp only [Source.Generated.fromApp, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact Or.inr rfl)

private theorem strict_fromLet
    (semantic : StrictGeneratedSemanticSolution
      (Source.Generated.fromLet effects body) solution) :
    Solves solution effects ∧
      StrictGeneratedSemanticSolution body solution := by
  constructor
  · intro equation membership
    exact semantic.hard equation (by
      simp only [Source.Generated.fromLet, List.mem_append]
      exact .inl membership)
  · constructor
    · intro equation membership
      exact semantic.hard equation (by
        simp only [Source.Generated.fromLet, List.mem_append]
        exact .inr membership)
    · intro obligation membership
      exact semantic.pending obligation (by
        simpa [Source.Generated.fromLet] using membership)

mutual

  /-- Relational elaboration plus a strict semantic solution determines the
  protected runtime typing of the supported first-order body fragment.  The
  only leaf information is the source/runtime context agreement above. -/
  theorem ProtectedBodySupported.elaboration_typing
      (supported : ProtectedBodySupported expression)
      (compatible : SignatureCompatible signature)
      (elaboration : Source.Elaborates signature sourceContext expression
        supply generated next)
      (semantic : StrictGeneratedSemanticSolution generated solution)
      (contextCompatible : ProtectedContextCompatible sourceContext
        runtimeContext provenance solution) :
      ProtectedRuntimeTyping provenance expression
        (generated.target.apply solution) runtimeContext := by
    cases supported with
    | var =>
        cases elaboration with
        | var lookup =>
            rcases contextCompatible.lookup supply lookup with
              ⟨_, runtimeLookup⟩ |
              ⟨general, provenanceLookup, runtimeLookup, instantiation⟩
            · exact .runtime (.var runtimeLookup)
            · exact .instantiatedVar runtimeLookup provenanceLookup instantiation
    | lit =>
        cases elaboration
        exact .runtime (.lit _)
    | something =>
        cases elaboration
        simpa [Ty.apply, Cap.apply] using
          ProtectedRuntimeTyping.runtime
            (provenance := provenance) (RuntimeTyping.something
              (solution.ty ⟨supply.ty⟩))
    | boolTrue =>
        cases elaboration with
        | ctor lookup _arity _closed call =>
            rw [compatible.boolTrue] at lookup
            cases lookup
            cases call
            simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] using
              ProtectedRuntimeTyping.runtime
                (provenance := provenance) RuntimeTyping.boolTrue
    | boolFalse =>
        cases elaboration with
        | ctor lookup _arity _closed call =>
            rw [compatible.boolFalse] at lookup
            cases lookup
            cases call
            simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] using
              ProtectedRuntimeTyping.runtime
                (provenance := provenance) RuntimeTyping.boolFalse
    | listNil =>
        cases elaboration with
        | ctor lookup _arity _closed call =>
            rw [compatible.listNil] at lookup
            cases lookup
            cases call
            simpa [Source.ConstructorSchemes.instantiate_listNil, Ty.apply,
              Ty.applyList, TypePM.DataTypes.list] using
              ProtectedRuntimeTyping.runtime (provenance := provenance)
                (RuntimeTyping.listNil (solution.ty ⟨supply.ty⟩))
    | listCons head tail =>
        cases elaboration with
        | ctor lookup _arity _closed call =>
            rw [compatible.listCons] at lookup
            cases lookup
            cases call with
            | cons headElaboration rest =>
                cases rest with
                | cons tailElaboration rest =>
                    cases rest
                    obtain ⟨firstSemantic, tailSemantic, secondEquation,
                        tailEquality⟩ := strict_fromApp semantic
                    obtain ⟨_initialSemantic, headSemantic, firstEquation,
                        headEquality⟩ := strict_fromApp firstSemantic
                    have headTyping := head.elaboration_typing compatible
                      headElaboration headSemantic contextCompatible
                    have tailTyping := tail.elaboration_typing compatible
                      tailElaboration tailSemantic contextCompatible
                    simp only [Ty.apply] at headEquality tailEquality
                    simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation
                    simp only [Source.ConstructorSchemes.instantiate_listCons]
                      at firstEquation
                    simp only [Source.Generated.fromApp, Ty.apply] at secondEquation
                    simp only [Source.Generated.fromApp, Ty.apply]
                    have firstParts := Ty.fn.inj firstEquation
                    rw [← firstParts.2] at secondEquation
                    have secondParts := Ty.fn.inj secondEquation
                    rw [← firstParts.1] at headEquality
                    rw [← secondParts.1] at tailEquality
                    rw [headEquality] at headTyping
                    rw [tailEquality] at tailTyping
                    rw [← secondParts.2]
                    exact .listCons headTyping tailTyping
    | app function argument =>
        cases elaboration with
        | app functionElaboration argumentElaboration =>
            obtain ⟨functionSemantic, argumentSemantic, functionEquation,
              argumentEquality⟩ := strict_fromApp semantic
            have functionTyping := function.elaboration_typing compatible
              functionElaboration functionSemantic contextCompatible
            have argumentTyping := argument.elaboration_typing compatible
              argumentElaboration argumentSemantic contextCompatible
            simp only [Equation.Holds, Ty.apply] at functionEquation
            rw [functionEquation] at functionTyping
            rw [argumentEquality] at argumentTyping
            exact .app functionTyping argumentTyping
    | add left right =>
        cases elaboration with
        | prim lookup _arity _closed call =>
            rw [compatible.add] at lookup
            cases lookup
            cases call with
            | cons leftElaboration rest =>
                cases rest with
                | cons rightElaboration rest =>
                    cases rest
                    obtain ⟨firstSemantic, rightSemantic, secondEquation,
                        rightEquality⟩ := strict_fromApp semantic
                    obtain ⟨_initialSemantic, leftSemantic, firstEquation,
                        leftEquality⟩ := strict_fromApp firstSemantic
                    have leftTyping := left.elaboration_typing compatible
                      leftElaboration leftSemantic contextCompatible
                    have rightTyping := right.elaboration_typing compatible
                      rightElaboration rightSemantic contextCompatible
                    simp only [Ty.apply] at leftEquality rightEquality
                    simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation
                    simp only [Source.PrimitiveSchemes.instantiate_add]
                      at firstEquation
                    simp only [Source.Generated.fromApp, Ty.apply] at secondEquation
                    simp only [Source.Generated.fromApp, Ty.apply]
                    have firstParts := Ty.fn.inj firstEquation
                    rw [← firstParts.2] at secondEquation
                    have secondParts := Ty.fn.inj secondEquation
                    rw [← firstParts.1] at leftEquality
                    rw [← secondParts.1] at rightEquality
                    rw [leftEquality] at leftTyping
                    rw [rightEquality] at rightTyping
                    rw [← secondParts.2]
                    exact .add leftTyping rightTyping
    | tuple items =>
        cases elaboration with
        | tuple itemElaboration =>
            have itemSemantic :
                StrictGeneratedItemsSemanticSolution _ solution :=
              ⟨semantic.hard, semantic.pending⟩
            exact .tuple (items.elaborationItems_typing compatible itemElaboration
              itemSemantic contextCompatible)
    | ifE condition thenBranch elseBranch =>
        cases elaboration with
        | ifE call =>
            cases call with
            | cons conditionElaboration rest =>
                cases rest with
                | cons thenElaboration rest =>
                    cases rest with
                    | cons elseElaboration rest =>
                        cases rest
                        obtain ⟨secondAccumulatedSemantic, elseSemantic,
                            thirdEquation, elseEquality⟩ :=
                          strict_fromApp semantic
                        obtain ⟨firstAccumulatedSemantic, thenSemantic,
                            secondEquation, thenEquality⟩ :=
                          strict_fromApp secondAccumulatedSemantic
                        obtain ⟨_initialSemantic, conditionSemantic,
                            firstEquation, conditionEquality⟩ :=
                          strict_fromApp firstAccumulatedSemantic
                        have conditionTyping := condition.elaboration_typing
                          compatible conditionElaboration conditionSemantic
                            contextCompatible
                        have thenTyping := thenBranch.elaboration_typing
                          compatible thenElaboration thenSemantic contextCompatible
                        have elseTyping := elseBranch.elaboration_typing
                          compatible elseElaboration elseSemantic contextCompatible
                        simp only [Ty.apply] at conditionEquality thenEquality elseEquality
                        simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation thirdEquation
                        simp only [Source.conditionalScheme_instantiate]
                          at firstEquation
                        simp only [TypePM.DataTypes.bool, Ty.apply,
                          Ty.applyList] at firstEquation
                        simp only [Source.Generated.fromApp, Ty.apply] at secondEquation thirdEquation
                        simp only [Source.Generated.fromApp, Ty.apply]
                        have firstParts := Ty.fn.inj firstEquation
                        rw [← firstParts.2] at secondEquation
                        have secondParts := Ty.fn.inj secondEquation
                        rw [← secondParts.2] at thirdEquation
                        have thirdParts := Ty.fn.inj thirdEquation
                        rw [← firstParts.1] at conditionEquality
                        rw [← secondParts.1] at thenEquality
                        rw [← thirdParts.1] at elseEquality
                        rw [conditionEquality] at conditionTyping
                        rw [thenEquality] at thenTyping
                        rw [elseEquality] at elseTyping
                        rw [← thirdParts.2]
                        exact .ifE conditionTyping thenTyping elseTyping

  /-- List counterpart of `ProtectedBodySupported.elaboration_typing`. -/
  theorem ProtectedBodiesSupported.elaborationItems_typing
      (supported : ProtectedBodiesSupported expressions)
      (compatible : SignatureCompatible signature)
      (elaboration : Source.ElaboratesItems signature sourceContext expressions
        supply generated next)
      (semantic : StrictGeneratedItemsSemanticSolution generated solution)
      (contextCompatible : ProtectedContextCompatible sourceContext
        runtimeContext provenance solution) :
      ProtectedRuntimeTypings provenance expressions
        (Ty.applyList solution generated.targets) runtimeContext := by
    cases supported with
    | nil =>
        cases elaboration
        exact .nil
    | cons head tail =>
        cases elaboration with
        | @cons _ _ _ _ generatedHead _ generatedTail _ headElaboration
            tailElaboration =>
            have headSemantic :
                StrictGeneratedSemanticSolution generatedHead solution := by
              constructor
              · intro equation membership
                exact semantic.hard equation (by
                  simp only [List.mem_append]
                  exact .inl membership)
              · intro obligation membership
                exact semantic.pending obligation (by
                  simp only [List.mem_append]
                  exact .inl membership)
            have tailSemantic :
                StrictGeneratedItemsSemanticSolution generatedTail solution := by
              constructor
              · intro equation membership
                exact semantic.hard equation (by
                  simp only [List.mem_append]
                  exact .inr membership)
              · intro obligation membership
                exact semantic.pending obligation (by
                  simp only [List.mem_append]
                  exact .inr membership)
            exact .cons
              (head.elaboration_typing compatible headElaboration headSemantic
                contextCompatible)
              (tail.elaborationItems_typing compatible tailElaboration tailSemantic
                contextCompatible)

end

/-! The following small kernel-checked obstruction is intentionally general
algebra, not a source-program regression.  It rules out an unconditional
replacement of the stability premise above. -/

private theorem variable_isInstance_int :
    IsInstance (.var ⟨0⟩) .int := by
  refine ⟨Subst.singleTy ⟨0⟩ .int, ?_⟩
  simp

private def disruptiveSubstitution : Subst :=
  Subst.singleTy ⟨0⟩ (.fn .int .int)

/-- A valid protected instantiation need not survive a later substitution.
Here the stored variable first instantiates to `Int`; the later substitution
turns the stored general type into `Int → Int`, which cannot instantiate
back to `Int`. -/
theorem protectedInstantiation_not_unconditionally_stable :
    IsInstance (.var ⟨0⟩) .int ∧
      ¬ IsInstance ((Ty.var ⟨0⟩).apply disruptiveSubstitution)
        (Ty.int.apply disruptiveSubstitution) := by
  refine ⟨variable_isInstance_int, ?_⟩
  rintro ⟨substitution, impossible⟩
  simp [disruptiveSubstitution, Ty.apply, Subst.singleTy] at impossible

mutual

/-- Preservation and ready progress for provenance-protected runtime typing.
The proof mask has no runtime representation; its only dynamic use is to
justify applying a `ValueTyping` substitution after an environment lookup. -/
theorem ProtectedRuntimeTyping.coreSafety
    (typing : ProtectedRuntimeTyping provenance expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    TypedResult target (evalFuel fuel environment expression) := by
  cases typing with
  | runtime runtimeTyping =>
      exact runtimeTyping.coreSafety fuel environment environmentTyping
  | instantiatedVar typeLookup provenanceLookup instantiation =>
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          obtain ⟨value, found, valueTyping⟩ :=
            EnvironmentTyping.lookup environmentTyping typeLookup
          rcases instantiation with ⟨substitution, targetEq⟩
          exact .inr ⟨value, by simp [evalFuel, found], by
            rw [← targetEq]
            exact valueTyping.apply substitution⟩
  | app function argument =>
      cases fuel with
      | zero => exact .inl rfl
      | succ applicationFuel =>
          have functionResult :=
            function.coreSafety applicationFuel environment environmentTyping
          rcases functionResult with functionTimeout |
            ⟨functionValue, functionSuccess, functionValueTyping⟩
          · exact .inl (by
              simp [evalFuel, functionTimeout, FuelResult.bind])
          · have argumentResult :=
              argument.coreSafety applicationFuel environment environmentTyping
            rcases argumentResult with argumentTimeout |
              ⟨argumentValue, argumentSuccess, argumentValueTyping⟩
            · exact .inl (by
                simp [evalFuel, functionSuccess, argumentTimeout,
                  FuelResult.bind])
            · cases applicationFuel with
              | zero => exact .inl (by simp [evalFuel])
              | succ bodyFuel =>
                  rcases functionValueTyping.function_canonical with
                    ⟨definitionEnvironment, definitionContext, bodyExpression,
                      functionEq, definitionEnvironmentTyping, bodyTyping⟩ |
                    ⟨definitionEnvironment, definitionContext, bodyExpression,
                      functionEq, definitionEnvironmentTyping, bodyTyping⟩
                  · subst functionValue
                    have bodyResult := bodyTyping.coreSafety bodyFuel
                      (argumentValue :: definitionEnvironment)
                      (.cons argumentValueTyping definitionEnvironmentTyping)
                    rcases bodyResult with bodyTimeout |
                      ⟨value, bodySuccess, valueTyping⟩
                    · exact .inl (by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodyTimeout)
                    · exact .inr ⟨value, by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodySuccess, valueTyping⟩
                  · subst functionValue
                    let closure := Value.recursiveClosure definitionEnvironment
                      bodyExpression
                    have closureTyping :=
                      ValueTyping.recursiveClosure definitionEnvironmentTyping
                        bodyTyping
                    have bodyResult := bodyTyping.coreSafety bodyFuel
                      (argumentValue :: closure :: definitionEnvironment)
                      (.cons argumentValueTyping
                        (.cons closureTyping definitionEnvironmentTyping))
                    rcases bodyResult with bodyTimeout |
                      ⟨value, bodySuccess, valueTyping⟩
                    · exact .inl (by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodyTimeout)
                    · exact .inr ⟨value, by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodySuccess, valueTyping⟩
  | tuple items =>
      cases fuel with
      | zero => exact .inl rfl
      | succ childFuel =>
          have children := items.coreSafety childFuel environment environmentTyping
          rcases children with timeout | ⟨values, success, childrenTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
          · exact .inr ⟨.tuple values, by
              simp [evalFuel, success, FuelResult.map], .tuple childrenTyping⟩
  | @listCons _ headExpression element _ tailExpression head tail =>
      cases fuel with
      | zero => exact .inl rfl
      | succ childFuel =>
          have children : TypedResults
              [element, TypePM.DataTypes.list element]
              (FuelResult.traverse (evalFuel childFuel environment)
                [headExpression, tailExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (head.coreSafety childFuel environment environmentTyping)
              (tail.coreSafety childFuel environment environmentTyping)
          rcases children with timeout | ⟨values, success, valuesTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
          · cases valuesTyping with
            | cons headTyping tailTyping =>
                cases tailTyping with
                | cons tailValueTyping nilTyping =>
                    cases nilTyping
                    obtain ⟨tailValues, tailEq, tailValuesTyping⟩ :=
                      tailValueTyping.list_canonical
                    subst tailEq
                    exact .inr ⟨Value.buildList (_ :: tailValues), by
                      simp [evalFuel, success, FuelResult.map,
                        Value.buildList, Value.consValue],
                      .list (.cons headTyping tailValuesTyping)⟩
  | @add _ leftExpression _ rightExpression left right =>
      cases fuel with
      | zero => exact .inl rfl
      | succ childFuel =>
          have children : TypedResults [.int, .int]
              (FuelResult.traverse (evalFuel childFuel environment)
                [leftExpression, rightExpression]) := by
            simpa [FuelResult.traverse] using TypedResult.pairTraverse
              (left.coreSafety childFuel environment environmentTyping)
              (right.coreSafety childFuel environment environmentTyping)
          rcases children with timeout | ⟨values, success, valuesTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · cases valuesTyping with
            | cons leftTyping tailTyping =>
                cases tailTyping with
                | cons rightTyping nilTyping =>
                    cases nilTyping
                    obtain ⟨leftValue, rfl⟩ := leftTyping.int_canonical
                    obtain ⟨rightValue, rfl⟩ := rightTyping.int_canonical
                    exact .inr ⟨.int (leftValue + rightValue), by
                      simp [evalFuel, success, evalPrimitive,
                        FuelResult.bind], .int _⟩
  | ifE condition thenBranch elseBranch =>
      cases fuel with
      | zero => exact .inl rfl
      | succ childFuel =>
          have conditionResult :=
            condition.coreSafety childFuel environment environmentTyping
          rcases conditionResult with timeout |
            ⟨conditionValue, success, conditionTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.bind])
          · rcases conditionTyping.bool_canonical with isTrue | isFalse
            · subst conditionValue
              have branchResult :=
                thenBranch.coreSafety childFuel environment environmentTyping
              rcases branchResult with branchTimeout |
                ⟨value, branchSuccess, valueTyping⟩
              · exact .inl (by
                  simp [evalFuel, success, branchTimeout, FuelResult.bind])
              · exact .inr ⟨value, by
                  simp [evalFuel, success, branchSuccess, FuelResult.bind],
                  valueTyping⟩
            · subst conditionValue
              have branchResult :=
                elseBranch.coreSafety childFuel environment environmentTyping
              have falseNeTrue : DataCtor.false ≠ DataCtor.true := by decide
              rcases branchResult with branchTimeout |
                ⟨value, branchSuccess, valueTyping⟩
              · exact .inl (by
                  simp [evalFuel, success, branchTimeout, FuelResult.bind,
                    falseNeTrue])
              · exact .inr ⟨value, by
                  simp [evalFuel, success, branchSuccess, FuelResult.bind,
                    falseNeTrue],
                  valueTyping⟩
  | letPoly value body =>
      cases fuel with
      | zero => exact .inl rfl
      | succ childFuel =>
          have valueResult :=
            value.coreSafety childFuel environment environmentTyping
          rcases valueResult with valueTimeout |
            ⟨valueResult, valueSuccess, valueTyping⟩
          · exact .inl (by
              simp [evalFuel, valueTimeout, FuelResult.bind])
          · have bodyResult := body.coreSafety childFuel
                (valueResult :: environment)
                (.cons valueTyping environmentTyping)
            rcases bodyResult with bodyTimeout |
              ⟨result, bodySuccess, resultTyping⟩
            · exact .inl (by
                simp [evalFuel, valueSuccess, bodyTimeout, FuelResult.bind])
            · exact .inr ⟨result, by
                simp [evalFuel, valueSuccess, bodySuccess, FuelResult.bind],
                resultTyping⟩

/-- List counterpart of `ProtectedRuntimeTyping.coreSafety`. -/
theorem ProtectedRuntimeTypings.coreSafety
    (typing : ProtectedRuntimeTypings provenance expressions targets context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    TypedResults targets
      (FuelResult.traverse (evalFuel fuel environment) expressions) := by
  cases typing with
  | nil => exact .inr ⟨[], rfl, .nil⟩
  | cons head tail =>
      have headResult := head.coreSafety fuel environment environmentTyping
      rcases headResult with headTimeout |
        ⟨headValue, headSuccess, headTyping⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · have tailResult := tail.coreSafety fuel environment environmentTyping
        rcases tailResult with tailTimeout |
          ⟨tailValues, tailSuccess, tailTyping⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            .cons headTyping tailTyping⟩

end


/-- Provenance-protected runtime typing rules out evaluator `stuck` for every
fuel amount. -/
theorem ProtectedRuntimeTyping.neverStuck
    (typing : ProtectedRuntimeTyping provenance expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    (evalFuel fuel environment expression).NotStuck :=
  (typing.coreSafety fuel environment environmentTyping).notStuck

/-! ## One protected closure boundary

`ProtectedRuntimeTyping` above deliberately returns the ordinary
`ValueTyping` judgment.  That is enough while every lambda body itself has an
ordinary `RuntimeTyping` derivation, but it cannot type a closure whose body
uses a captured generalized `let` binding at several instances.

The following proof-only layer adds exactly that missing boundary.  A
`ProtectedClosureValueTyping` either embeds an ordinary typed value or records
one plain closure together with the provenance mask captured at its
definition.  Its body is checked by `ProtectedRuntimeTyping` after a `false`
entry is pushed for the monomorphic lambda parameter.  No runtime data changes:
the closure still stores an ordinary `List Value`, and its context is still an
ordinary `List Ty`.

The application rule intentionally requires an ordinary protected argument
and returns an ordinary protected body result.  Thus this is the smallest
sound layer needed for a lambda to capture a generalized value; it does not
yet claim that protected closures may themselves be passed as arguments or
captured by another protected closure.
-/

/-- Values produced at the single protected-closure boundary. -/
inductive ProtectedClosureValueTyping : Value → Ty → Prop where
  | runtime (typing : ValueTyping value target) :
      ProtectedClosureValueTyping value target
  | plainClosure
      (environment : EnvironmentTyping values context)
      (body : ProtectedRuntimeTyping (false :: provenance) bodyExpression
        codomain (domain :: context)) :
      ProtectedClosureValueTyping
        (Value.plainClosure values bodyExpression) (.fn domain codomain)

/-- A typed result whose successful value may be the one protected closure
described by `ProtectedClosureValueTyping`. -/
def ProtectedClosureTypedResult
    (target : Ty) (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧ ProtectedClosureValueTyping value target

/-- Expression typing at the single protected-closure boundary.  The
ordinary branch retains the complete first-order protected relation; `lam`
creates the protected closure; `app` consumes either an ordinary function or
that protected closure. -/
inductive ProtectedClosureRuntimeTyping :
    (provenance : List Bool) → Source.Expr → Ty →
      (context : List Ty := []) → Prop where
  | firstOrder
      (typing : ProtectedRuntimeTyping provenance expression target context) :
      ProtectedClosureRuntimeTyping provenance expression target context
  | lam
      (body : ProtectedRuntimeTyping (false :: provenance) bodyExpression
        codomain (domain :: context)) :
      ProtectedClosureRuntimeTyping provenance (.lam bodyExpression)
        (.fn domain codomain) context
  | app
      (function : ProtectedClosureRuntimeTyping provenance functionExpression
        (.fn domain codomain) context)
      (argument : ProtectedRuntimeTyping provenance argumentExpression domain
        context) :
      ProtectedClosureRuntimeTyping provenance
        (.app functionExpression argumentExpression) codomain context
  | letPoly
      (value : ProtectedRuntimeTyping provenance valueExpression general context)
      (body : ProtectedClosureRuntimeTyping (true :: provenance) bodyExpression
        target (general :: context)) :
      ProtectedClosureRuntimeTyping provenance
        (.letE valueExpression bodyExpression) target context

/-- One closure boundary around the protected first-order body fragment.
The function side of an application may contain that boundary; the argument
remains first-order, matching `ProtectedClosureRuntimeTyping.app`. -/
inductive ProtectedClosureBodySupported : Source.Expr → Prop where
  | firstOrder (body : ProtectedBodySupported expression) :
      ProtectedClosureBodySupported expression
  | lam (body : ProtectedBodySupported bodyExpression) :
      ProtectedClosureBodySupported (.lam bodyExpression)
  | app
      (function : ProtectedClosureBodySupported functionExpression)
      (argument : ProtectedBodySupported argumentExpression) :
      ProtectedClosureBodySupported (.app functionExpression argumentExpression)
  /-- A nested principal `let` whose value is the closed identity lambda.
  This is the first representative-sensitive nested-let case: the body may
  use both this new generalized binding and generalized bindings captured
  from the surrounding protected context. -/
  | letIdentity
      (body : ProtectedClosureBodySupported bodyExpression) :
      ProtectedClosureBodySupported
        (.letE (.lam (.var 0)) bodyExpression)

private theorem generalizedIdentity_instantiate_shape
    (context : Source.Context) (domain : Ty) (supply : Source.Supply) :
    ∃ instantiatedDomain,
      ((context.generalize (.fn domain domain)).instantiate supply).1 =
        .fn instantiatedDomain instantiatedDomain := by
  simp [Source.Context.generalize, Source.Scheme.instantiate,
    Source.PolyTy.close, Source.PolyTy.openBound]

private theorem identityElaboration_closure_target_shape
    (elaboration : Source.Elaborates signature context (.lam (.var 0))
      supply generated next)
    (closure : PrincipalBlockClosure generated) :
    ∃ domain, closure.target = .fn domain domain := by
  cases elaboration with
  | lam bodyElaboration =>
      cases bodyElaboration with
      | var lookup =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst_vars
          exact ⟨(Ty.var ⟨supply.ty⟩).apply closure.substitution, by
            simp [PrincipalBlockClosure.target, Source.Scheme.instantiate_mono,
              Ty.apply]⟩

/-- Relational elaboration constructs the complete surrounding
`ProtectedClosureRuntimeTyping` derivation for the single-closure fragment.
`StrictGeneratedSemanticSolution` states the precise remaining boundary:
every pending application check in this fragment is equality. -/
theorem ProtectedClosureBodySupported.elaboration_typing
    (supported : ProtectedClosureBodySupported expression)
    (compatible : SignatureCompatible signature)
    (elaboration : Source.Elaborates signature sourceContext expression
      supply generated next)
    (semantic : StrictGeneratedSemanticSolution generated solution)
    (contextCompatible : ProtectedContextCompatible sourceContext
      runtimeContext provenance solution) :
    ProtectedClosureRuntimeTyping provenance expression
      (generated.target.apply solution) runtimeContext := by
  cases supported with
  | firstOrder body =>
      exact .firstOrder
        (body.elaboration_typing compatible elaboration semantic contextCompatible)
  | lam body =>
      cases elaboration with
      | @lam _ _ _ generatedBody _ bodyElaboration =>
          have bodySemantic :
              StrictGeneratedSemanticSolution generatedBody solution :=
            ⟨semantic.hard, semantic.pending⟩
          simpa [Ty.apply] using ProtectedClosureRuntimeTyping.lam
            (body.elaboration_typing compatible bodyElaboration bodySemantic
              contextCompatible.mono)
  | app function argument =>
      cases elaboration with
      | app functionElaboration argumentElaboration =>
          obtain ⟨functionSemantic, argumentSemantic, functionEquation,
            argumentEquality⟩ := strict_fromApp semantic
          have functionTyping := function.elaboration_typing
            compatible functionElaboration functionSemantic contextCompatible
          have argumentTyping := argument.elaboration_typing
            compatible argumentElaboration argumentSemantic contextCompatible
          simp only [Equation.Holds, Ty.apply] at functionEquation
          rw [functionEquation] at functionTyping
          rw [argumentEquality] at argumentTyping
          exact .app functionTyping argumentTyping
  | letIdentity body =>
      cases elaboration with
      | letE valueElaboration closure absorbing bodyElaboration =>
          obtain ⟨interfaceSolved, bodySemantic⟩ := strict_fromLet semantic
          let closedContext := sourceContext.applyFree closure.substitution
          let generalizedScheme := closedContext.generalize closure.target
          let canonicalSupply := closedContext.initialSupply
          let general := (generalizedScheme.instantiate canonicalSupply).1
          have closedCompatible : ProtectedContextCompatible closedContext
              runtimeContext provenance solution := by
            exact contextCompatible.ofApplyFreeInterface interfaceSolved
          have bodyCompatible : ProtectedContextCompatible
              (generalizedScheme :: closedContext)
              (general :: runtimeContext) (true :: provenance) solution := by
            apply ProtectedContextCompatible.pushCanonical
                (canonicalSupply := canonicalSupply)
            · intro index membership
              exact Source.Context.freeTyVar_lt_initialSupply
                ((Source.Context.mem_generalize_freeTyVars.mp membership).2)
            · intro index membership
              exact Source.Context.freeCapVar_lt_initialSupply
                ((Source.Context.mem_generalize_freeCapVars.mp membership).2)
            · exact closedCompatible
          have bodyTyping := body.elaboration_typing compatible bodyElaboration
            bodySemantic bodyCompatible
          obtain ⟨valueDomain, closureShape⟩ :=
            identityElaboration_closure_target_shape valueElaboration closure
          have generalShape : ∃ domain, general = .fn domain domain := by
            dsimp only [general, generalizedScheme]
            rw [closureShape]
            exact generalizedIdentity_instantiate_shape closedContext
              valueDomain canonicalSupply
          obtain ⟨generalDomain, generalEq⟩ := generalShape
          have valueTyping : ProtectedRuntimeTyping provenance
              (.lam (.var 0)) general runtimeContext := by
            rw [generalEq]
            exact .runtime (.lam (.var rfl))
          exact .letPoly valueTyping bodyTyping

namespace ProtectedClosureValueTyping

/-- A function value at this boundary is either one of the two ordinary
closure forms or the protected plain closure. -/
theorem function_canonical
    (typing : ProtectedClosureValueTyping value (.fn domain codomain)) :
      ( (∃ environment context bodyExpression,
          value = Value.plainClosure environment bodyExpression ∧
          EnvironmentTyping environment context ∧
          RuntimeTyping bodyExpression codomain (domain :: context)) ∨
        (∃ environment context bodyExpression,
          value = Value.recursiveClosure environment bodyExpression ∧
          EnvironmentTyping environment context ∧
          RuntimeTyping bodyExpression codomain
            (domain :: .fn domain codomain :: context)) ) ∨
      ∃ environment provenance context bodyExpression,
        value = Value.plainClosure environment bodyExpression ∧
        EnvironmentTyping environment context ∧
        ProtectedRuntimeTyping (false :: provenance) bodyExpression codomain
          (domain :: context) := by
  cases typing with
  | runtime runtimeTyping =>
      exact .inl runtimeTyping.function_canonical
  | plainClosure environment body =>
      exact .inr ⟨_, _, _, _, rfl, environment, body⟩

end ProtectedClosureValueTyping

namespace ProtectedClosureTypedResult

/-- The protected closure result cannot be `stuck`. -/
theorem notStuck
    (typed : ProtectedClosureTypedResult target result) : result.NotStuck := by
  rcases typed with timeout | ⟨value, success, _typing⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end ProtectedClosureTypedResult

/-- Preservation and ready progress for the single protected-closure layer. -/
theorem ProtectedClosureRuntimeTyping.coreSafety
    (typing : ProtectedClosureRuntimeTyping provenance expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    ProtectedClosureTypedResult target
      (evalFuel fuel environment expression) := by
  induction typing generalizing fuel environment with
  | firstOrder typing =>
      rcases typing.coreSafety fuel environment environmentTyping with timeout |
        ⟨value, success, valueTyping⟩
      · exact .inl timeout
      · exact .inr ⟨value, success, .runtime valueTyping⟩
  | lam body =>
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          exact .inr ⟨Value.plainClosure environment _, rfl,
            .plainClosure environmentTyping body⟩
  | app function argument functionIH =>
      cases fuel with
      | zero => exact .inl rfl
      | succ applicationFuel =>
          have functionResult :=
            functionIH applicationFuel environment environmentTyping
          rcases functionResult with functionTimeout |
            ⟨functionValue, functionSuccess, functionValueTyping⟩
          · exact .inl (by
              simp [evalFuel, functionTimeout, FuelResult.bind])
          · have argumentResult :=
              argument.coreSafety applicationFuel environment environmentTyping
            rcases argumentResult with argumentTimeout |
              ⟨argumentValue, argumentSuccess, argumentValueTyping⟩
            · exact .inl (by
                simp [evalFuel, functionSuccess, argumentTimeout,
                  FuelResult.bind])
            · cases applicationFuel with
              | zero => exact .inl (by simp [evalFuel])
              | succ bodyFuel =>
                  rcases functionValueTyping.function_canonical with
                    ordinary | protectedClosure
                  · rcases ordinary with
                      ⟨definitionEnvironment, definitionContext, bodyExpression,
                        functionEq, definitionEnvironmentTyping, bodyTyping⟩ |
                      ⟨definitionEnvironment, definitionContext, bodyExpression,
                        functionEq, definitionEnvironmentTyping, bodyTyping⟩
                    · subst functionValue
                      have bodyResult := bodyTyping.coreSafety bodyFuel
                        (argumentValue :: definitionEnvironment)
                        (.cons argumentValueTyping definitionEnvironmentTyping)
                      rcases bodyResult with bodyTimeout |
                        ⟨value, bodySuccess, valueTyping⟩
                      · exact .inl (by
                          rw [evalFuel.eq_def]
                          simp only
                          rw [functionSuccess, argumentSuccess]
                          exact bodyTimeout)
                      · exact .inr ⟨value, by
                          rw [evalFuel.eq_def]
                          simp only
                          rw [functionSuccess, argumentSuccess]
                          exact bodySuccess, .runtime valueTyping⟩
                    · subst functionValue
                      let closure := Value.recursiveClosure definitionEnvironment
                        bodyExpression
                      have closureTyping :=
                        ValueTyping.recursiveClosure definitionEnvironmentTyping
                          bodyTyping
                      have bodyResult := bodyTyping.coreSafety bodyFuel
                        (argumentValue :: closure :: definitionEnvironment)
                        (.cons argumentValueTyping
                          (.cons closureTyping definitionEnvironmentTyping))
                      rcases bodyResult with bodyTimeout |
                        ⟨value, bodySuccess, valueTyping⟩
                      · exact .inl (by
                          rw [evalFuel.eq_def]
                          simp only
                          rw [functionSuccess, argumentSuccess]
                          exact bodyTimeout)
                      · exact .inr ⟨value, by
                          rw [evalFuel.eq_def]
                          simp only
                          rw [functionSuccess, argumentSuccess]
                          exact bodySuccess, .runtime valueTyping⟩
                  · rcases protectedClosure with
                      ⟨definitionEnvironment, capturedProvenance,
                        definitionContext, bodyExpression, functionEq,
                        definitionEnvironmentTyping, bodyTyping⟩
                    subst functionValue
                    have bodyResult := bodyTyping.coreSafety bodyFuel
                      (argumentValue :: definitionEnvironment)
                      (.cons argumentValueTyping definitionEnvironmentTyping)
                    rcases bodyResult with bodyTimeout |
                      ⟨value, bodySuccess, valueTyping⟩
                    · exact .inl (by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodyTimeout)
                    · exact .inr ⟨value, by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodySuccess, .runtime valueTyping⟩
  | letPoly value body bodyIH =>
      cases fuel with
      | zero => exact .inl rfl
      | succ childFuel =>
          have valueResult :=
            value.coreSafety childFuel environment environmentTyping
          rcases valueResult with valueTimeout |
            ⟨valueResult, valueSuccess, valueTyping⟩
          · exact .inl (by
              simp [evalFuel, valueTimeout, FuelResult.bind])
          · have bodyResult := bodyIH childFuel (valueResult :: environment)
                (.cons valueTyping environmentTyping)
            rcases bodyResult with bodyTimeout |
              ⟨result, bodySuccess, resultTyping⟩
            · exact .inl (by
                simp [evalFuel, valueSuccess, bodyTimeout, FuelResult.bind])
            · exact .inr ⟨result, by
                simp [evalFuel, valueSuccess, bodySuccess, FuelResult.bind],
                resultTyping⟩

/-- The single protected-closure layer rules out evaluator `stuck`. -/
theorem ProtectedClosureRuntimeTyping.neverStuck
    (typing : ProtectedClosureRuntimeTyping provenance expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    (evalFuel fuel environment expression).NotStuck :=
  (typing.coreSafety fuel environment environmentTyping).notStuck

end TypePM.Runtime

namespace TypePM.Source

/-- A proof-only source-to-runtime certificate.  Its source component is an
actual relational `PrincipalTyping` witness (and therefore contains an
`Elaborates` derivation with all `letE` closures); its runtime component uses
the protected provenance relation above.  The last field is exactly the
instance closure used by public `Source.Typing`. -/
inductive ProvenancedRuntimeTyping
    (signature : Signature) (expression : Expr) (target : Ty) : Prop where
  | intro {principal : Ty}
      (sourcePrincipal : PrincipalTyping signature [] expression principal)
      (runtimePrincipal :
        Runtime.ProtectedRuntimeTyping [] expression principal [])
      (instantiation : IsInstance principal target) :
      ProvenancedRuntimeTyping signature expression target

namespace ProvenancedRuntimeTyping

/-- Pair an actual relational source principal derivation with its protected
runtime interpretation.  Identity instantiation makes the shared principal
type the public result type. -/
theorem ofPrincipal
    (sourcePrincipal : PrincipalTyping signature [] expression target)
    (runtimePrincipal :
      Runtime.ProtectedRuntimeTyping [] expression target []) :
    ProvenancedRuntimeTyping signature expression target :=
  .intro sourcePrincipal runtimePrincipal ⟨Subst.id, by simp⟩

/-- Erasing the runtime certificate recovers the public declarative source
typing judgment, so this relation is a strengthening of `Source.Typing`, not
an unrelated safety judgment. -/
theorem toSourceTyping
    (typing : ProvenancedRuntimeTyping signature expression target) :
    Typing signature [] expression target := by
  cases typing with
  | intro sourcePrincipal runtimePrincipal instantiation =>
      exact ⟨_, sourcePrincipal, instantiation⟩

/-- Source-to-runtime preservation for the protected polymorphic-`let`
certificate. -/
theorem coreSafety
    (typing : ProvenancedRuntimeTyping signature expression target)
    (fuel : Nat) :
    Runtime.TypedResult target (Runtime.evalFuel fuel [] expression) := by
  cases typing with
  | @intro principal sourcePrincipal runtimePrincipal instantiation =>
  have principalResult := runtimePrincipal.coreSafety fuel [] .nil
  rcases instantiation with ⟨substitution, targetEq⟩
  rcases principalResult with timeout | ⟨value, success, valueTyping⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, by
      rw [← targetEq]
      exact valueTyping.apply substitution⟩

/-- Source-to-runtime no-stuck endpoint for provenance-protected
polymorphic `let`. -/
theorem neverStuck
    (typing : ProvenancedRuntimeTyping signature expression target)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (typing.coreSafety fuel).notStuck

end ProvenancedRuntimeTyping

/-! ## Source anchor for the protected-closure boundary -/

/-- A successful principal source typing paired with the exact protected
closure runtime type.  Unlike `ProvenancedRuntimeTyping`, this certificate
does not add a final arbitrary `IsInstance` step: the one-closure value
relation intentionally has no unrestricted substitution constructor. -/
inductive ProtectedClosureProvenancedRuntimeTyping
    (signature : Signature) (expression : Expr) (target : Ty) : Prop where
  | intro
      (sourcePrincipal : PrincipalTyping signature [] expression target)
      (runtimePrincipal :
        Runtime.ProtectedClosureRuntimeTyping [] expression target []) :
      ProtectedClosureProvenancedRuntimeTyping signature expression target

namespace ProtectedClosureProvenancedRuntimeTyping

/-- Erasing the protected-closure runtime certificate recovers ordinary
declarative source typing at the inferred principal type. -/
theorem toSourceTyping
    (typing : ProtectedClosureProvenancedRuntimeTyping signature expression target) :
    Typing signature [] expression target := by
  cases typing with
  | intro sourcePrincipal runtimePrincipal =>
      exact ⟨target, sourcePrincipal, Subst.id, by simp⟩

/-- Source-anchored preservation and ready progress for the protected closure
boundary. -/
theorem coreSafety
    (typing : ProtectedClosureProvenancedRuntimeTyping signature expression target)
    (fuel : Nat) :
    Runtime.ProtectedClosureTypedResult target
      (Runtime.evalFuel fuel [] expression) := by
  cases typing with
  | intro sourcePrincipal runtimePrincipal =>
      exact runtimePrincipal.coreSafety fuel [] .nil

/-- Source-anchored no-stuck endpoint for the protected closure boundary. -/
theorem neverStuck
    (typing : ProtectedClosureProvenancedRuntimeTyping signature expression target)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (typing.coreSafety fuel).notStuck

end ProtectedClosureProvenancedRuntimeTyping

namespace Inference

/-- Successful public source inference plus a protected runtime
interpretation yields the source-to-runtime bridge certificate. -/
theorem infer_success_provenancedRuntimeTyping
    {signature : Signature} (wellFormed : signature.WellFormed)
    {expression : Expr} {target : Ty}
    (success : infer signature [] expression = some target)
    (runtimeTyping :
      Runtime.ProtectedRuntimeTyping [] expression target []) :
    ProvenancedRuntimeTyping signature expression target :=
  ProvenancedRuntimeTyping.ofPrincipal
    (infer_success_principalTyping wellFormed success) runtimeTyping

/-- Executable-inference no-stuck endpoint for the protected polymorphic
`let` bridge. -/
theorem infer_neverStuck_provenanced
    {signature : Signature} (wellFormed : signature.WellFormed)
    {expression : Expr} {target : Ty}
    (success : infer signature [] expression = some target)
    (runtimeTyping :
      Runtime.ProtectedRuntimeTyping [] expression target [])
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (infer_success_provenancedRuntimeTyping wellFormed success runtimeTyping).neverStuck
    fuel

/-- Successful inference plus the exact protected-closure runtime
interpretation yields the source-anchored one-closure certificate. -/
theorem infer_success_protectedClosureRuntimeTyping
    {signature : Signature} (wellFormed : signature.WellFormed)
    {expression : Expr} {target : Ty}
    (success : infer signature [] expression = some target)
    (runtimeTyping :
      Runtime.ProtectedClosureRuntimeTyping [] expression target []) :
    ProtectedClosureProvenancedRuntimeTyping signature expression target :=
  .intro (infer_success_principalTyping wellFormed success) runtimeTyping

/-- Executable-inference no-stuck endpoint for the one protected-closure
boundary. -/
theorem infer_neverStuck_protectedClosure
    {signature : Signature} (wellFormed : signature.WellFormed)
    {expression : Expr} {target : Ty}
    (success : infer signature [] expression = some target)
    (runtimeTyping :
      Runtime.ProtectedClosureRuntimeTyping [] expression target [])
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (infer_success_protectedClosureRuntimeTyping wellFormed success runtimeTyping).neverStuck
    fuel

end Inference

end TypePM.Source
