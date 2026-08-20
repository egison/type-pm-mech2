import TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralAutomation

/-!
# A source fragment with structurally ordinary root checks

An application can select a special checking conversion even when public
inference succeeds.  This module therefore describes a conservative source
fragment whose call shape rules that case out before running inference.

Every application argument, including every argument of a constructor,
primitive, or conditional call, must have a result whose outer type
constructor is fixed by syntax to `Int` or a function type.  Type substitution
cannot turn either shape into a matcher or a product of matchers, so the
resulting application obligation always selects ordinary equality.  Function
positions and tuple children may still contain nested applications.

The `letE` rule deliberately inspects only the body.  Its right-hand side is
closed internally and its pending obligations do not occur in the generated
root block.
-/

namespace TypePM.Source

/-- Type shapes which cannot become the source of a special checking
conversion after any type substitution. -/
inductive OrdinaryArgumentTypeShape : Ty → Prop where
  | int : OrdinaryArgumentTypeShape .int
  | fn (domain codomain : Ty) : OrdinaryArgumentTypeShape (.fn domain codomain)

namespace OrdinaryArgumentTypeShape

/-- A syntactically fixed integer or function outer constructor always uses
ordinary equality, independently of the expected type and substitution. -/
theorem resolutionOrdinary
    (shape : OrdinaryArgumentTypeShape source)
    (substitution : Subst) (expected : Ty) :
    ((CheckObligation.mk source expected).resolutionUnder
      substitution).conversionClass = .ordinary := by
  cases shape <;> cases expected <;> rfl

end OrdinaryArgumentTypeShape

mutual

  /-- Source expressions whose root pending obligations are structurally
  ordinary.  The restriction is local to argument positions: variables,
  anonymous matchers, and nested applications remain available elsewhere. -/
  inductive RootOrdinarySourceFragment : Expr → Prop where
    | var (index : Nat) : RootOrdinarySourceFragment (.var index)
    | lit (value : Int) : RootOrdinarySourceFragment (.lit value)
    | something : RootOrdinarySourceFragment .something
    | lam {body : Expr}
        (bodyFragment : RootOrdinarySourceFragment body) :
        RootOrdinarySourceFragment (.lam body)
    | app {function argument : Expr}
        (functionFragment : RootOrdinarySourceFragment function)
        (argumentFragment : RootOrdinarySourceFragment argument)
        (argumentResult : OrdinaryArgumentResult argument) :
        RootOrdinarySourceFragment (.app function argument)
    | tuple {items : List Expr}
        (itemFragments : RootOrdinarySourceItems items) :
        RootOrdinarySourceFragment (.tuple items)
    | letE (value : Expr) {body : Expr}
        (bodyFragment : RootOrdinarySourceFragment body) :
        RootOrdinarySourceFragment (.letE value body)
    | ctor (constructor : DataCtor) {arguments : List Expr}
        (argumentFragments : RootOrdinaryCallArguments arguments) :
        RootOrdinarySourceFragment (.ctor constructor arguments)
    | prim (operation : PrimOp) {arguments : List Expr}
        (argumentFragments : RootOrdinaryCallArguments arguments) :
        RootOrdinarySourceFragment (.prim operation arguments)
    | ifE {condition thenBranch elseBranch : Expr}
        (argumentFragments : RootOrdinaryCallArguments
          [condition, thenBranch, elseBranch]) :
        RootOrdinarySourceFragment (.ifE condition thenBranch elseBranch)

  /-- Pointwise fragment evidence for tuple children. -/
  inductive RootOrdinarySourceItems : List Expr → Prop where
    | nil : RootOrdinarySourceItems []
    | cons {item : Expr} {items : List Expr}
        (itemFragment : RootOrdinarySourceFragment item)
        (itemFragments : RootOrdinarySourceItems items) :
        RootOrdinarySourceItems (item :: items)

  /-- A call list in which each expression belongs to the root fragment and
  also has a substitution-stable ordinary argument result shape. -/
  inductive RootOrdinaryCallArguments : List Expr → Prop where
    | nil : RootOrdinaryCallArguments []
    | cons {argument : Expr} {arguments : List Expr}
        (argumentFragment : RootOrdinarySourceFragment argument)
        (argumentResult : OrdinaryArgumentResult argument)
        (argumentFragments : RootOrdinaryCallArguments arguments) :
        RootOrdinaryCallArguments (argument :: arguments)

  /-- Expressions whose successful elaboration has an outer `Int` or
  function result directly from its outer syntax. -/
  inductive OrdinaryArgumentResult : Expr → Prop where
    | lit (value : Int) : OrdinaryArgumentResult (.lit value)
    | lam (body : Expr) : OrdinaryArgumentResult (.lam body)

end

namespace OrdinaryArgumentResult

/-- Successful relational elaboration preserves the syntactically fixed
outer result shape used by the fragment. -/
theorem elaborationTypeShape
    {signature : Signature} {context : Context} {expression : Expr}
    {supply : Supply} {generated : Generated} {next : Supply}
    (result : OrdinaryArgumentResult expression)
    (elaboration : Elaborates signature context expression supply generated next) :
    OrdinaryArgumentTypeShape generated.target := by
  cases result with
  | lit value =>
      cases elaboration
      exact .int
  | lam body =>
      cases elaboration
      exact .fn _ _

end OrdinaryArgumentResult

mutual

  /-- Fragment syntax constructs the node-indexed ordinary certificate for
  every matching relational elaboration. -/
  theorem RootOrdinarySourceFragment.structural
      {signature : Signature} {context : Context} {expression : Expr}
      {supply : Supply} {generated : Generated} {next : Supply}
      (fragment : RootOrdinarySourceFragment expression)
      (elaboration : Elaborates signature context expression supply generated next) :
      ElaborationResolutionsOrdinaryAt substitution elaboration := by
    cases fragment with
    | var index =>
        cases elaboration with
        | var lookup => exact .var lookup
    | lit value =>
        cases elaboration
        exact .lit
    | something =>
        cases elaboration
        exact .something
    | lam bodyFragment =>
        cases elaboration with
        | lam bodyElaboration =>
            exact .lam (bodyFragment.structural bodyElaboration)
    | app functionFragment argumentFragment argumentResult =>
        cases elaboration with
        | app functionElaboration argumentElaboration =>
            exact .app
              (functionFragment.structural functionElaboration)
              (argumentFragment.structural argumentElaboration)
              ((argumentResult.elaborationTypeShape argumentElaboration).resolutionOrdinary
                substitution _)
    | tuple itemFragments =>
        cases elaboration with
        | tuple itemsElaboration =>
            exact .tuple (itemFragments.structural itemsElaboration)
    | letE value bodyFragment =>
        cases elaboration with
        | letE valueElaboration closure absorbing bodyElaboration =>
            exact @ElaborationResolutionsOrdinaryAt.letE
              substitution signature context value _ supply _ _ closure
              absorbing _ next valueElaboration bodyElaboration
              (bodyFragment.structural bodyElaboration)
    | ctor constructor argumentFragments =>
        cases elaboration with
        | ctor lookup arity closed callElaboration =>
            exact @ElaborationResolutionsOrdinaryAt.ctor
              substitution signature context constructor _ _ supply generated
              next lookup arity closed callElaboration
              (argumentFragments.structural callElaboration)
    | prim operation argumentFragments =>
        cases elaboration with
        | prim lookup arity closed callElaboration =>
            exact @ElaborationResolutionsOrdinaryAt.prim
              substitution signature context operation _ _ supply generated
              next lookup arity closed callElaboration
              (argumentFragments.structural callElaboration)
    | ifE argumentFragments =>
        cases elaboration with
        | ifE callElaboration =>
            exact .ifE (argumentFragments.structural callElaboration)
  termination_by expression.complexity * 3 + 2
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

  /-- Tuple-list counterpart of `RootOrdinarySourceFragment.structural`. -/
  theorem RootOrdinarySourceItems.structural
      {signature : Signature} {context : Context} {expressions : List Expr}
      {supply : Supply} {generated : GeneratedItems} {next : Supply}
      (fragments : RootOrdinarySourceItems expressions)
      (elaboration : ElaboratesItems signature context expressions supply
        generated next) :
      ItemsResolutionsOrdinaryAt substitution elaboration := by
    cases fragments with
    | nil =>
        cases elaboration
        exact .nil
    | cons itemFragment itemFragments =>
        cases elaboration with
        | cons headElaboration tailElaboration =>
            exact .cons
              (itemFragment.structural headElaboration)
              (itemFragments.structural tailElaboration)
  termination_by Expr.listComplexity expressions * 3 + 1
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

  /-- Call-list counterpart of `RootOrdinarySourceFragment.structural`. -/
  theorem RootOrdinaryCallArguments.structural
      {signature : Signature} {context : Context} {arguments : List Expr}
      {accumulated generated : Generated} {supply next : Supply}
      (fragments : RootOrdinaryCallArguments arguments)
      (elaboration : ElaboratesCall signature context accumulated arguments
        supply generated next) :
      CallResolutionsOrdinaryAt substitution elaboration := by
    cases fragments with
    | nil =>
        cases elaboration
        exact .nil
    | cons argumentFragment argumentResult argumentFragments =>
        cases elaboration with
        | cons argumentElaboration tailElaboration =>
            exact .cons
              (argumentFragment.structural argumentElaboration)
              ((argumentResult.elaborationTypeShape argumentElaboration).resolutionOrdinary
                substitution _)
              (argumentFragments.structural tailElaboration)
  termination_by Expr.listComplexity arguments * 3
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

end

/-- An actual successful executable elaboration of the fragment makes the
local source-structural checker accept for every substitution. -/
theorem RootOrdinarySourceFragment.sourceStructuralCheckAt
    {signature : Signature} {context : Context} {expression : Expr}
    {supply next : Supply} {generated : Generated}
    (fragment : RootOrdinarySourceFragment expression)
    (wellFormed : signature.WellFormed)
    (success : elaborate signature context expression supply =
      some (generated, next)) :
    sourceStructuralOrdinaryCheckAt substitution signature context expression
      supply = true := by
  rw [sourceStructuralOrdinaryCheckAt_eq_pending success]
  simp only [List.all_eq_true, beq_iff_eq]
  exact (fragment.structural (elaborate_sound wellFormed success)).pending

/-- The explicit fragment supplies the complete root structural certificate.
This theorem does not assert that elaboration or inference succeeds; it only
discharges the ordinary-resolution side of every successful run. -/
theorem RootOrdinarySourceFragment.rootStructural
    {signature : Signature} {context : Context} {expression : Expr}
    (fragment : RootOrdinarySourceFragment expression)
    (wellFormed : signature.WellFormed) :
    InferenceRootResolutionsOrdinaryStructural signature context expression := by
  intro generated next elaborated output saturated
  let derivation := elaborate_sound wellFormed elaborated
  exact ⟨derivation, fragment.structural derivation⟩

/-- Public inference success makes the executable root checker accept on the
explicit fragment.  The success premise is used only to obtain the actual
elaboration and hard-saturation results; ordinary conversion follows from the
fragment theorem above. -/
theorem RootOrdinarySourceFragment.inferenceRootStructuralCheck
    {signature : Signature} {context : Context} {expression : Expr}
    {target : Ty}
    (fragment : RootOrdinarySourceFragment expression)
    (wellFormed : signature.WellFormed)
    (success : infer signature context expression = some target) :
    inferenceRootStructuralOrdinaryCheck signature context expression = true := by
  unfold infer elaborateRoot at success
  cases elaborated : elaborate signature context expression context.initialSupply with
  | none => simp [elaborated] at success
  | some output =>
      rcases output with ⟨generated, next⟩
      simp only [elaborated, Option.map_some] at success
      unfold inferGeneratedUsing at success
      cases saturated : saturateUsing unify generated.hard generated.pending with
      | none => simp [saturated] at success
      | some saturation =>
          unfold inferenceRootStructuralOrdinaryCheck
            inferenceRootStructuralOrdinaryCheckUsing
          simp only [elaborated, saturated]
          exact fragment.sourceStructuralCheckAt wellFormed elaborated

end TypePM.Source
