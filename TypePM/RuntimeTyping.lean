import TypePM.Source.Elaboration
import TypePM.Runtime.EvalFuel
import TypePM.GeneratedSemanticAcceptance

/-!
# Runtime typing for the closed canonical core

The complete source language does not yet have a proved runtime-typing
interpretation.  This module relates only the declarations used by its
certified fragment to the fixed evaluator; `matchFirst` and pattern-function
atoms still have explicit `stuck` branches in the evaluator.

This module establishes an honest state-erasure boundary for closed integer
expressions, canonical Boolean and List data, recursively nested tuples,
integer addition, `append`, `member`, `deleteFirst`, and conditionals whose
two branches have the same certified type.  It also types variables under a
monomorphic runtime context, closures, applications with an arbitrary typed
function expression, and `map`.  The judgment is declarative and syntax
directed;
it does not mention `evalFuel`, `stuck`, or a fuel amount.  Runtime values use a
separate judgment with the same type index.  Function application permits an
arbitrary typed expression in function position, and `map` applies such a
function to a canonical List.  Later modules prove preservation and progress
for this core.
-/

namespace TypePM.Runtime

set_option maxRecDepth 4096

/-- The source declarations used by the current source-to-runtime bridge agree
with the fixed meanings implemented by `evalFuel`.  Without these equalities,
a well-formed signature could assign the name `true` or `add` a different
source type while the evaluator continued to use its built-in behavior. -/
structure SignatureCompatible (signature : Source.Signature) : Prop where
  boolTrue :
    signature.lookupDataConstructor DataCtor.true =
      some Source.ConstructorSchemes.boolTrue
  boolFalse :
    signature.lookupDataConstructor DataCtor.false =
      some Source.ConstructorSchemes.boolFalse
  listNil :
    signature.lookupDataConstructor DataCtor.nil =
      some Source.ConstructorSchemes.listNil
  listCons :
    signature.lookupDataConstructor DataCtor.cons =
      some Source.ConstructorSchemes.listCons
  add :
    signature.lookupPrimitive PrimOp.add =
      some Source.PrimitiveSchemes.add
  append :
    signature.lookupPrimitive PrimOp.append =
      some Source.PrimitiveSchemes.append
  member :
    signature.lookupPrimitive PrimOp.member =
      some Source.PrimitiveSchemes.member
  deleteFirst :
    signature.lookupPrimitive PrimOp.deleteFirst =
      some Source.PrimitiveSchemes.deleteFirst

theorem paper1SignatureCompatible :
    SignatureCompatible Source.Paper1Signature.signature := by
  constructor <;> simp

mutual

/-- Declarative runtime typing for the certified expression core under a
newest-first monomorphic context.  The context defaults to `[]`, preserving
the closed-program interface used by the earlier checkpoint. -/
inductive RuntimeTyping : Source.Expr → Ty → (context : List Ty := []) → Prop where
  | var (lookup : context[index]? = some target) :
      RuntimeTyping (.var index) target context
  | lit (value : Int) : RuntimeTyping (.lit value) .int context
  | boolTrue :
      RuntimeTyping (.ctor DataCtor.true []) TypePM.DataTypes.bool context
  | boolFalse :
      RuntimeTyping (.ctor DataCtor.false []) TypePM.DataTypes.bool context
  | listNil (element : Ty) :
      RuntimeTyping (.ctor DataCtor.nil []) (TypePM.DataTypes.list element) context
  | listCons (head : RuntimeTyping headExpression element context)
      (tail : RuntimeTyping tailExpression (TypePM.DataTypes.list element) context) :
      RuntimeTyping (.ctor DataCtor.cons [headExpression, tailExpression])
        (TypePM.DataTypes.list element) context
  | tuple (items : RuntimeTypings expressions targets context) :
      RuntimeTyping (.tuple expressions) (.prod targets) context
  | lam (body : RuntimeTyping bodyExpression codomain (domain :: context)) :
      RuntimeTyping (.lam bodyExpression) (.fn domain codomain) context
  | app (function : RuntimeTyping functionExpression (.fn domain codomain) context)
      (argument : RuntimeTyping argumentExpression domain context) :
      RuntimeTyping (.app functionExpression argumentExpression) codomain context
  | fixE (body : RuntimeTyping bodyExpression codomain
      (domain :: .fn domain codomain :: context)) :
      RuntimeTyping (.fixE bodyExpression) (.fn domain codomain) context
  | add (left : RuntimeTyping leftExpression .int context)
      (right : RuntimeTyping rightExpression .int context) :
      RuntimeTyping (.prim PrimOp.add [leftExpression, rightExpression]) .int context
  | append
      (left : RuntimeTyping leftExpression (TypePM.DataTypes.list element) context)
      (right : RuntimeTyping rightExpression (TypePM.DataTypes.list element) context) :
      RuntimeTyping (.prim PrimOp.append [leftExpression, rightExpression])
        (TypePM.DataTypes.list element) context
  | member (needle : RuntimeTyping needleExpression element context)
      (target : RuntimeTyping targetExpression (TypePM.DataTypes.list element) context) :
      RuntimeTyping (.prim PrimOp.member [needleExpression, targetExpression])
        TypePM.DataTypes.bool context
  | deleteFirst (needle : RuntimeTyping needleExpression element context)
      (target : RuntimeTyping targetExpression (TypePM.DataTypes.list element) context) :
      RuntimeTyping
        (.prim PrimOp.deleteFirst [needleExpression, targetExpression])
        (TypePM.DataTypes.list element) context
  | map (function : RuntimeTyping functionExpression (.fn domain codomain) context)
      (target : RuntimeTyping targetExpression (TypePM.DataTypes.list domain) context) :
      RuntimeTyping (.prim PrimOp.map [functionExpression, targetExpression])
        (TypePM.DataTypes.list codomain) context
  | ifE (condition : RuntimeTyping conditionExpression TypePM.DataTypes.bool context)
      (thenBranch : RuntimeTyping thenExpression branchTarget context)
      (elseBranch : RuntimeTyping elseExpression branchTarget context) :
      RuntimeTyping
        (.ifE conditionExpression thenExpression elseExpression) branchTarget context
  | checked (source : RuntimeTyping expression sourceTarget context)
      (conversion : CheckConversion conversionClass sourceTarget target) :
      RuntimeTyping expression target context
  | instantiated (source : RuntimeTyping expression sourceTarget [])
      (substitution : Subst) :
      RuntimeTyping expression (sourceTarget.apply substitution) []

/-- Pointwise expression typing under one shared context. -/
inductive RuntimeTypings : List Source.Expr → List Ty →
    (context : List Ty := []) → Prop where
  | nil : RuntimeTypings [] [] context
  | cons (head : RuntimeTyping expression target context)
      (tail : RuntimeTypings expressions targets context) :
      RuntimeTypings (expression :: expressions) (target :: targets) context

end

mutual

/-- Declarative runtime typing for values, including closures together with
the typed definition environment captured when they are created. -/
inductive ValueTyping : Value → Ty → Prop where
  | int (value : Int) : ValueTyping (.int value) .int
  | boolTrue : ValueTyping (.data DataCtor.true []) TypePM.DataTypes.bool
  | boolFalse : ValueTyping (.data DataCtor.false []) TypePM.DataTypes.bool
  | tuple (items : ValueTypings values targets) :
      ValueTyping (.tuple values) (.prod targets)
  | list (items : ListValueTypings values element) :
      ValueTyping (Value.buildList values) (TypePM.DataTypes.list element)
  | plainClosure (environment : EnvironmentTyping values context)
      (body : RuntimeTyping bodyExpression codomain (domain :: context)) :
      ValueTyping (Value.plainClosure values bodyExpression) (.fn domain codomain)
  | recursiveClosure (environment : EnvironmentTyping values context)
      (body : RuntimeTyping bodyExpression codomain
        (domain :: .fn domain codomain :: context)) :
      ValueTyping (Value.recursiveClosure values bodyExpression) (.fn domain codomain)
  | checked (source : ValueTyping value sourceTarget)
      (conversion : CheckConversion conversionClass sourceTarget target) :
      ValueTyping value target
  | instantiated (source : ValueTyping value sourceTarget)
      (substitution : Subst) :
      ValueTyping value (sourceTarget.apply substitution)

/-- Pointwise runtime typing for sibling values. -/
inductive ValueTypings : List Value → List Ty → Prop where
  | nil : ValueTypings [] []
  | cons (head : ValueTyping value target)
      (tail : ValueTypings values targets) :
      ValueTypings (value :: values) (target :: targets)

/-- Homogeneous typing for the host list encoded by one canonical runtime
list value. -/
inductive ListValueTypings : List Value → Ty → Prop where
  | nil : ListValueTypings [] element
  | cons (head : ValueTyping value element)
      (tail : ListValueTypings values element) :
      ListValueTypings (value :: values) element

/-- Runtime environments are typed pointwise in newest-first order. -/
inductive EnvironmentTyping : ValueEnvironment → List Ty → Prop where
  | nil : EnvironmentTyping [] []
  | cons (head : ValueTyping value target)
      (tail : EnvironmentTyping environment context) :
      EnvironmentTyping (value :: environment) (target :: context)

end

namespace CapabilityDemand

theorem apply
    (demand : CapabilityDemand producer consumer)
    (substitution : CapSubst) :
    CapabilityDemand (producer.apply substitution) (consumer.apply substitution) := by
  cases demand with
  | equal => exact .equal
  | any => exact .any

end CapabilityDemand

namespace RuntimeDual

def apply (substitution : Subst) (dual : Dual) : Dual :=
  ⟨dual.capability.apply substitution.cap, dual.target.apply substitution⟩

private theorem capApplyList_eq_map (items : List Cap) :
    Cap.applyList substitution items = items.map (Cap.apply substitution) := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp [Cap.applyList, induction]

private theorem tyApplyList_eq_map (items : List Ty) :
    Ty.applyList substitution items = items.map (Ty.apply substitution) := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp [Ty.applyList, induction]

@[simp] theorem matcherTypes_apply (duals : List Dual) :
    Ty.applyList substitution (duals.map Dual.matcherType) =
      (duals.map (apply substitution)).map Dual.matcherType := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [Ty.applyList, Ty.apply, Dual.matcherType, apply, induction]

@[simp] theorem capabilities_apply (duals : List Dual) :
    Cap.applyList substitution.cap (Dual.capabilities duals) =
      Dual.capabilities (duals.map (apply substitution)) := by
  rw [capApplyList_eq_map]
  simp [Dual.capabilities, apply, List.map_map, Function.comp_def]

@[simp] theorem targets_apply (duals : List Dual) :
    Ty.applyList substitution (Dual.targets duals) =
      Dual.targets (duals.map (apply substitution)) := by
  rw [tyApplyList_eq_map]
  simp [Dual.targets, apply, List.map_map, Function.comp_def]

end RuntimeDual

namespace CheckConversion

theorem apply
    (conversion : CheckConversion conversionClass source target)
    (substitution : Subst) :
    CheckConversion conversionClass
      (source.apply substitution) (target.apply substitution) := by
  cases conversion with
  | ordinary => exact .ordinary
  | matcherToSlot demand =>
      simpa [Ty.apply] using .matcherToSlot
        (CapabilityDemand.apply demand substitution.cap)
  | @productMatcher duals nonempty =>
      have appliedNonempty : duals.map (RuntimeDual.apply substitution) ≠ [] := by
        simpa using nonempty
      simpa [Ty.apply, Cap.apply] using
        CheckConversion.productMatcher appliedNonempty
  | @productMatcherToSlot duals consumer nonempty demand =>
      have appliedNonempty : duals.map (RuntimeDual.apply substitution) ≠ [] := by
        simpa using nonempty
      have appliedDemand :
          CapabilityDemand
            (.prod (Dual.capabilities
              (duals.map (RuntimeDual.apply substitution))))
            (consumer.apply substitution.cap) := by
        simpa [Cap.apply] using
          CapabilityDemand.apply demand substitution.cap
      simpa [Ty.apply, Cap.apply] using
        CheckConversion.productMatcherToSlot appliedNonempty
          appliedDemand

end CheckConversion

mutual

/-- A source expression lies in the certified runtime core.  This relation
records only syntax coverage, leaving the source derivation to determine the
possibly polymorphic runtime type. -/
inductive RuntimeSupported : Source.Expr → Prop where
  | lit : RuntimeSupported (.lit value)
  | boolTrue : RuntimeSupported (.ctor DataCtor.true [])
  | boolFalse : RuntimeSupported (.ctor DataCtor.false [])
  | listNil : RuntimeSupported (.ctor DataCtor.nil [])
  | listCons (head : RuntimeSupported headExpression)
      (tail : RuntimeSupported tailExpression) :
      RuntimeSupported (.ctor DataCtor.cons [headExpression, tailExpression])
  | tuple (items : RuntimeSupporteds expressions) :
      RuntimeSupported (.tuple expressions)
  | add (left : RuntimeSupported leftExpression)
      (right : RuntimeSupported rightExpression) :
      RuntimeSupported (.prim PrimOp.add [leftExpression, rightExpression])
  | append (left : RuntimeSupported leftExpression)
      (right : RuntimeSupported rightExpression) :
      RuntimeSupported (.prim PrimOp.append [leftExpression, rightExpression])
  | member (needle : RuntimeSupported needleExpression)
      (target : RuntimeSupported targetExpression) :
      RuntimeSupported (.prim PrimOp.member [needleExpression, targetExpression])
  | deleteFirst (needle : RuntimeSupported needleExpression)
      (target : RuntimeSupported targetExpression) :
      RuntimeSupported
        (.prim PrimOp.deleteFirst [needleExpression, targetExpression])
  | ifE (condition : RuntimeSupported conditionExpression)
      (thenBranch : RuntimeSupported thenExpression)
      (elseBranch : RuntimeSupported elseExpression) :
      RuntimeSupported
        (.ifE conditionExpression thenExpression elseExpression)

inductive RuntimeSupporteds : List Source.Expr → Prop where
  | nil : RuntimeSupporteds []
  | cons (head : RuntimeSupported expression)
      (tail : RuntimeSupporteds expressions) :
      RuntimeSupporteds (expression :: expressions)

end

/-- Runtime value typing is closed under substitution of its type index. -/
theorem ValueTyping.apply
    (typing : ValueTyping value target) (substitution : Subst) :
    ValueTyping value (target.apply substitution) :=
  .instantiated typing substitution

theorem ValueTypings.apply
    (typing : ValueTypings values targets) (substitution : Subst) :
    ValueTypings values (Ty.applyList substitution targets) := by
  cases typing with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (head.apply substitution) (tail.apply substitution)

theorem EnvironmentTyping.apply
    (typing : EnvironmentTyping environment context)
    (substitution : Subst) :
    EnvironmentTyping environment (Ty.applyList substitution context) := by
  cases typing with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (head.apply substitution) (tail.apply substitution)

private theorem getElem?_applyList
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

/-- Apply one type substitution to both the result type and every entry of a
monomorphic runtime context.  Unlike the closed `instantiated` constructor,
this operation is structural: closure bodies and all of their variable
assumptions are transported together. -/
protected def RuntimeTyping.applyContext
    (substitution : Subst) :
    (typing : RuntimeTyping expression target context) →
      RuntimeTyping expression (target.apply substitution)
        (Ty.applyList substitution context)
  | .var lookup => .var (getElem?_applyList lookup)
  | .lit value => .lit value
  | .boolTrue => by
      change RuntimeTyping (.ctor DataCtor.true []) TypePM.DataTypes.bool _
      exact RuntimeTyping.boolTrue
  | .boolFalse => by
      change RuntimeTyping (.ctor DataCtor.false []) TypePM.DataTypes.bool _
      exact RuntimeTyping.boolFalse
  | .listNil element => by
      simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.list] using
        RuntimeTyping.listNil (element.apply substitution)
  | .listCons head tail => by
      simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.list] using
        RuntimeTyping.listCons (head.applyContext substitution)
          (tail.applyContext substitution)
  | .tuple items => by
      simpa [Ty.apply] using RuntimeTyping.tuple (items.applyContext substitution)
  | .lam body => by
      simpa [Ty.apply, Ty.applyList] using
        RuntimeTyping.lam (body.applyContext substitution)
  | .app function argument => by
      simpa [Ty.apply] using RuntimeTyping.app
        (function.applyContext substitution) (argument.applyContext substitution)
  | .fixE body => by
      simpa [Ty.apply, Ty.applyList] using
        RuntimeTyping.fixE (body.applyContext substitution)
  | .add left right => by
      simpa [Ty.apply] using RuntimeTyping.add
        (left.applyContext substitution) (right.applyContext substitution)
  | .append left right => by
      simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.list] using RuntimeTyping.append
        (left.applyContext substitution) (right.applyContext substitution)
  | .member needle target => by
      simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.bool,
        TypePM.DataTypes.list] using RuntimeTyping.member
          (needle.applyContext substitution) (target.applyContext substitution)
  | .deleteFirst needle target => by
      simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.list] using RuntimeTyping.deleteFirst
        (needle.applyContext substitution) (target.applyContext substitution)
  | .map function target => by
      simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.list] using RuntimeTyping.map
        (function.applyContext substitution) (target.applyContext substitution)
  | .ifE condition thenBranch elseBranch => by
      simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] using RuntimeTyping.ifE
        (condition.applyContext substitution)
        (thenBranch.applyContext substitution)
        (elseBranch.applyContext substitution)
  | .checked source conversion =>
      .checked (source.applyContext substitution)
        (TypePM.Runtime.CheckConversion.apply conversion substitution)
  | .instantiated source earlier => by
      simpa only [Ty.apply_compose, Ty.applyList] using
        RuntimeTyping.instantiated source (Subst.compose substitution earlier)

/-- List counterpart of `RuntimeTyping.applyContext`. -/
protected def RuntimeTypings.applyContext
    (substitution : Subst) :
    (typing : RuntimeTypings expressions targets context) →
      RuntimeTypings expressions (Ty.applyList substitution targets)
        (Ty.applyList substitution context)
  | .nil => .nil
  | .cons head tail =>
      .cons (head.applyContext substitution) (tail.applyContext substitution)

end


/-- Runtime expression typing is closed under substitution of its type
index.  This is essential for polymorphic empty lists. -/
theorem RuntimeTyping.apply
    (typing : RuntimeTyping expression target) (substitution : Subst) :
    RuntimeTyping expression (target.apply substitution) :=
  .instantiated typing substitution

theorem RuntimeTypings.apply
    (typing : RuntimeTypings expressions targets) (substitution : Subst) :
    RuntimeTypings expressions (Ty.applyList substitution targets) := by
  cases typing with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (head.apply substitution) (tail.apply substitution)

/-- Pointwise semantic satisfaction for an elaborated sibling list. -/
def GeneratedItems.SemanticSolution
    (generated : GeneratedItems) (solution : Subst) : Prop :=
  Solves solution generated.hard ∧
    ∀ obligation ∈ generated.pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)

private theorem fromApp_semantic_parts
    {function argument : Generated} {domain target : Ty}
    (semantic :
      (Source.Generated.fromApp function argument domain target).SemanticSolution
        solution) :
    function.SemanticSolution solution ∧
      argument.SemanticSolution solution ∧
      Equation.Holds solution (.ty function.target (.fn domain target)) ∧
      ∃ conversionClass,
        CheckConversion conversionClass
          (argument.target.apply solution) (domain.apply solution) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro equation membership
    exact semantic.1 equation (by
      simp only [Source.Generated.fromApp, List.mem_append]
      exact .inl (.inl membership))
  · intro obligation membership
    exact semantic.2 obligation (by
      simp only [Source.Generated.fromApp, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact .inl (.inl membership))
  · intro equation membership
    exact semantic.1 equation (by
      simp only [Source.Generated.fromApp, List.mem_append]
      exact .inl (.inr membership))
  · intro obligation membership
    exact semantic.2 obligation (by
      simp only [Source.Generated.fromApp, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact .inl (.inr membership))
  · exact semantic.1 _ (by
      simp [Source.Generated.fromApp])
  · exact semantic.2 ⟨argument.target, domain⟩ (by
      simp [Source.Generated.fromApp])

mutual

/-- A semantic solution of the constraints emitted for a certified expression
assigns its raw target an independent runtime typing.  The input typing is
used only as structural evidence that the expression belongs to the certified
fragment; its type index need not equal the raw target, notably for `nil`. -/
theorem RuntimeSupported.elaboration_typing
    (compatible : SignatureCompatible signature)
    (supported : RuntimeSupported expression)
    (elaboration : Source.Elaborates signature context expression supply
      generated next)
    (semantic : generated.SemanticSolution solution) :
    RuntimeTyping expression (generated.target.apply solution) := by
  cases supported with
  | lit =>
      cases elaboration
      exact .lit _
  | boolTrue =>
      cases elaboration with
      | ctor lookup _arity _closed call =>
          rw [compatible.boolTrue] at lookup
          cases lookup
          cases call
          simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] using
            RuntimeTyping.boolTrue
  | boolFalse =>
      cases elaboration with
      | ctor lookup _arity _closed call =>
          rw [compatible.boolFalse] at lookup
          cases lookup
          cases call
          simpa [Ty.apply, Ty.applyList, TypePM.DataTypes.bool] using
            RuntimeTyping.boolFalse
  | listNil =>
      cases elaboration with
      | ctor lookup _arity _closed call =>
          rw [compatible.listNil] at lookup
          cases lookup
          cases call
          simpa [Source.ConstructorSchemes.instantiate_listNil, Ty.apply,
            Ty.applyList, TypePM.DataTypes.list] using
            RuntimeTyping.listNil (solution.ty ⟨supply.ty⟩)
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
                      tailCheck⟩ := fromApp_semantic_parts semantic
                  obtain ⟨_initialSemantic, headSemantic, firstEquation,
                      headCheck⟩ := fromApp_semantic_parts firstSemantic
                  have headTyping :=
                    head.elaboration_typing compatible headElaboration headSemantic
                  have tailTyping :=
                    tail.elaboration_typing compatible tailElaboration tailSemantic
                  obtain ⟨_headClass, headConversion⟩ := headCheck
                  obtain ⟨_tailClass, tailConversion⟩ := tailCheck
                  simp only [Ty.apply] at headConversion tailConversion
                  simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation
                  simp only [Source.ConstructorSchemes.instantiate_listCons]
                    at firstEquation
                  simp only [Source.Generated.fromApp, Ty.apply] at secondEquation ⊢
                  have firstParts := Ty.fn.inj firstEquation
                  rw [← firstParts.2] at secondEquation
                  have secondParts := Ty.fn.inj secondEquation
                  rw [← firstParts.1] at headConversion
                  rw [← secondParts.1] at tailConversion
                  rw [← secondParts.2]
                  exact .listCons (.checked headTyping headConversion)
                    (.checked tailTyping tailConversion)
  | tuple items =>
      cases elaboration with
      | tuple itemElaboration =>
          have itemSemantic :
              GeneratedItems.SemanticSolution _ solution := semantic
          exact .tuple
            (items.elaborationItems_typing compatible itemElaboration itemSemantic)
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
                      _rightCheck⟩ :=
                    fromApp_semantic_parts semantic
                  obtain ⟨_initialSemantic, leftSemantic, firstEquation,
                      leftCheck⟩ :=
                    fromApp_semantic_parts firstSemantic
                  have leftTyping :=
                    left.elaboration_typing compatible leftElaboration leftSemantic
                  have rightTyping :=
                    right.elaboration_typing compatible rightElaboration rightSemantic
                  obtain ⟨_leftClass, leftConversion⟩ := leftCheck
                  obtain ⟨_rightClass, rightConversion⟩ := _rightCheck
                  simp only [Ty.apply] at leftConversion rightConversion
                  simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation
                  simp only [Source.PrimitiveSchemes.instantiate_add] at firstEquation
                  simp only [Source.Generated.fromApp, Ty.apply] at secondEquation ⊢
                  have firstParts := Ty.fn.inj firstEquation
                  rw [← firstParts.2] at secondEquation
                  have secondParts := Ty.fn.inj secondEquation
                  rw [← firstParts.1] at leftConversion
                  rw [← secondParts.1] at rightConversion
                  rw [← secondParts.2]
                  exact .add (.checked leftTyping leftConversion)
                    (.checked rightTyping rightConversion)
  | append left right =>
      cases elaboration with
      | prim lookup _arity _closed call =>
          rw [compatible.append] at lookup
          cases lookup
          cases call with
          | cons leftElaboration rest =>
              cases rest with
              | cons rightElaboration rest =>
                  cases rest
                  obtain ⟨firstSemantic, rightSemantic, secondEquation,
                      rightCheck⟩ := fromApp_semantic_parts semantic
                  obtain ⟨_initialSemantic, leftSemantic, firstEquation,
                      leftCheck⟩ := fromApp_semantic_parts firstSemantic
                  have leftTyping :=
                    left.elaboration_typing compatible leftElaboration leftSemantic
                  have rightTyping :=
                    right.elaboration_typing compatible rightElaboration rightSemantic
                  obtain ⟨_leftClass, leftConversion⟩ := leftCheck
                  obtain ⟨_rightClass, rightConversion⟩ := rightCheck
                  simp only [Ty.apply] at leftConversion rightConversion
                  simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation
                  simp only [Source.PrimitiveSchemes.instantiate_append]
                    at firstEquation
                  simp only [Source.Generated.fromApp, Ty.apply] at secondEquation ⊢
                  have firstParts := Ty.fn.inj firstEquation
                  rw [← firstParts.2] at secondEquation
                  have secondParts := Ty.fn.inj secondEquation
                  rw [← firstParts.1] at leftConversion
                  rw [← secondParts.1] at rightConversion
                  rw [← secondParts.2]
                  exact .append (.checked leftTyping leftConversion)
                    (.checked rightTyping rightConversion)
  | member needle list =>
      cases elaboration with
      | prim lookup _arity _closed call =>
          rw [compatible.member] at lookup
          cases lookup
          cases call with
          | cons needleElaboration rest =>
              cases rest with
              | cons listElaboration rest =>
                  cases rest
                  obtain ⟨firstSemantic, listSemantic, secondEquation,
                      listCheck⟩ := fromApp_semantic_parts semantic
                  obtain ⟨_initialSemantic, needleSemantic, firstEquation,
                      needleCheck⟩ := fromApp_semantic_parts firstSemantic
                  have needleTyping := needle.elaboration_typing compatible
                    needleElaboration needleSemantic
                  have listTyping := list.elaboration_typing compatible
                    listElaboration listSemantic
                  obtain ⟨_needleClass, needleConversion⟩ := needleCheck
                  obtain ⟨_listClass, listConversion⟩ := listCheck
                  simp only [Ty.apply] at needleConversion listConversion
                  simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation
                  simp only [Source.PrimitiveSchemes.instantiate_member]
                    at firstEquation
                  simp only [Source.Generated.fromApp, Ty.apply] at secondEquation ⊢
                  have firstParts := Ty.fn.inj firstEquation
                  rw [← firstParts.2] at secondEquation
                  have secondParts := Ty.fn.inj secondEquation
                  rw [← firstParts.1] at needleConversion
                  rw [← secondParts.1] at listConversion
                  rw [← secondParts.2]
                  exact .member (.checked needleTyping needleConversion)
                    (.checked listTyping listConversion)
  | deleteFirst needle list =>
      cases elaboration with
      | prim lookup _arity _closed call =>
          rw [compatible.deleteFirst] at lookup
          cases lookup
          cases call with
          | cons needleElaboration rest =>
              cases rest with
              | cons listElaboration rest =>
                  cases rest
                  obtain ⟨firstSemantic, listSemantic, secondEquation,
                      listCheck⟩ := fromApp_semantic_parts semantic
                  obtain ⟨_initialSemantic, needleSemantic, firstEquation,
                      needleCheck⟩ := fromApp_semantic_parts firstSemantic
                  have needleTyping := needle.elaboration_typing compatible
                    needleElaboration needleSemantic
                  have listTyping := list.elaboration_typing compatible
                    listElaboration listSemantic
                  obtain ⟨_needleClass, needleConversion⟩ := needleCheck
                  obtain ⟨_listClass, listConversion⟩ := listCheck
                  simp only [Ty.apply] at needleConversion listConversion
                  simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation
                  simp only [Source.PrimitiveSchemes.instantiate_deleteFirst]
                    at firstEquation
                  simp only [Source.Generated.fromApp, Ty.apply] at secondEquation ⊢
                  have firstParts := Ty.fn.inj firstEquation
                  rw [← firstParts.2] at secondEquation
                  have secondParts := Ty.fn.inj secondEquation
                  rw [← firstParts.1] at needleConversion
                  rw [← secondParts.1] at listConversion
                  rw [← secondParts.2]
                  exact .deleteFirst (.checked needleTyping needleConversion)
                    (.checked listTyping listConversion)
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
                          thirdEquation, _elseCheck⟩ :=
                        fromApp_semantic_parts semantic
                      obtain ⟨firstAccumulatedSemantic, thenSemantic,
                          secondEquation, thenCheck⟩ :=
                        fromApp_semantic_parts
                          secondAccumulatedSemantic
                      obtain ⟨_initialSemantic, conditionSemantic,
                          firstEquation, _conditionCheck⟩ :=
                        fromApp_semantic_parts
                          firstAccumulatedSemantic
                      have conditionTyping := condition.elaboration_typing
                        compatible conditionElaboration conditionSemantic
                      have thenTyping := thenBranch.elaboration_typing
                        compatible thenElaboration thenSemantic
                      have elseTyping := elseBranch.elaboration_typing
                        compatible elseElaboration elseSemantic
                      obtain ⟨_conditionClass, conditionConversion⟩ :=
                        _conditionCheck
                      obtain ⟨_thenClass, thenConversion⟩ := thenCheck
                      obtain ⟨_elseClass, elseConversion⟩ := _elseCheck
                      simp only [Ty.apply] at conditionConversion thenConversion elseConversion
                      simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation thirdEquation
                      simp only [Source.conditionalScheme_instantiate] at firstEquation
                      simp only [TypePM.DataTypes.bool, Ty.apply,
                        Ty.applyList] at firstEquation
                      simp only [Source.Generated.fromApp, Ty.apply] at secondEquation thirdEquation ⊢
                      have firstParts := Ty.fn.inj firstEquation
                      have firstResult := firstParts.2
                      rw [← firstResult] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      rw [← secondParts.2] at thirdEquation
                      have thirdParts := Ty.fn.inj thirdEquation
                      rw [← firstParts.1] at conditionConversion
                      rw [← secondParts.1] at thenConversion
                      rw [← thirdParts.1] at elseConversion
                      rw [← thirdParts.2]
                      exact .ifE (.checked conditionTyping conditionConversion)
                        (.checked thenTyping thenConversion)
                        (.checked elseTyping elseConversion)
termination_by expression.complexity * 3 + 2
decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

/-- List counterpart of `RuntimeTyping.elaboration_typing`. -/
theorem RuntimeSupporteds.elaborationItems_typing
    (compatible : SignatureCompatible signature)
    (supported : RuntimeSupporteds expressions)
    (elaboration : Source.ElaboratesItems signature context expressions supply
      generated next)
    (semantic : GeneratedItems.SemanticSolution generated solution) :
    RuntimeTypings expressions (Ty.applyList solution generated.targets) := by
  cases supported with
  | nil =>
      cases elaboration
      exact .nil
  | cons head tail =>
      cases elaboration with
      | @cons _ _ _ _ generatedItem _ generatedItems _ headElaboration
          tailElaboration =>
          have headSemantic : generatedItem.SemanticSolution solution := by
            constructor
            · intro equation membership
              exact semantic.1 equation (by
                simp only [List.mem_append]
                exact .inl membership)
            · intro obligation membership
              exact semantic.2 obligation (by
                simp only [List.mem_append]
                exact .inl membership)
          have tailSemantic :
              GeneratedItems.SemanticSolution generatedItems solution := by
            constructor
            · intro equation membership
              exact semantic.1 equation (by
                simp only [List.mem_append]
                exact .inr membership)
            · intro obligation membership
              exact semantic.2 obligation (by
                simp only [List.mem_append]
                exact .inr membership)
          exact .cons
            (head.elaboration_typing compatible headElaboration headSemantic)
            (tail.elaborationItems_typing compatible tailElaboration tailSemantic)
termination_by Source.Expr.listComplexity expressions * 3 + 1
decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

end

end TypePM.Runtime

namespace TypePM.Source

namespace Typing

private theorem PrincipalBlockClosure.semanticSolution
    {generated : Generated} (closure : PrincipalBlockClosure generated) :
    generated.SemanticSolution closure.substitution := by
  constructor
  · intro equation membership
    exact closure.finalHard_solved equation
      (closure.saturation.closure.hard_mem_final equation membership)
  · intro obligation membership
    rcases closure.saturation.closure.pending_covered obligation membership with
      retained | promoted
    · exact closure.remaining_checkConversion obligation retained
    · have equality :=
        closure.finalHard_solved
          (.ty obligation.source obligation.expected) promoted
      simp only [Equation.Holds] at equality
      rw [equality]
      exact ⟨.ordinary, .ordinary⟩

/-- **Theorem 5.6, current source-to-runtime bridge.**  A declaratively typed,
closed source expression in the `RuntimeSupported` fragment has the
corresponding runtime typing.  The proof reconstructs the runtime type from
the elaboration closure, so polymorphic List declarations and their concrete
instances are included.

The `RuntimeSupported` premise is the precise current boundary.  Removing it
requires source derivations for variables, lambda/application, `fixE`, `map`,
polymorphic `let`, matcher states, and matching search to be transported into
the already more general runtime judgment. -/
theorem toRuntimeTyping
    {signature : Signature} {expression : Expr} {target : Ty}
    (typing : Typing signature [] expression target)
    (compatible : Runtime.SignatureCompatible signature)
    (supported : Runtime.RuntimeSupported expression) :
    Runtime.RuntimeTyping expression target := by
  rcases typing with ⟨principal, principalTyping, instantiation⟩
  rcases principalTyping with ⟨derivation⟩
  rcases derivation with
    ⟨generated, next, elaboration, closure, _absorbing, principalEq⟩
  have closureTyping :
      Runtime.RuntimeTyping expression closure.target := by
    exact supported.elaboration_typing compatible elaboration
      (PrincipalBlockClosure.semanticSolution closure)
  have principalTypingRuntime :
      Runtime.RuntimeTyping expression principal := by
    rw [principalEq]
    exact closureTyping
  rcases instantiation with ⟨substitution, instanceEq⟩
  rw [← instanceEq]
  exact principalTypingRuntime.apply substitution

end Typing

end TypePM.Source
