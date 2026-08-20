import TypePM.Source.PolymorphicLetInferenceOrdinary

/-!
# Structural ordinary-pending certificates

`PendingResolutionsOrdinaryAt` states the right property of a generated
pending list, but does not retain where its obligations came from.  The
judgments below mirror ordinary source elaboration.  An application records
the conversion selected for its one newly generated obligation; a
constructor, primitive, or conditional records the corresponding sequence of
call arguments.  Their soundness theorem reconstructs the certificate for
the complete generated pending list.

The fragment deliberately has no constructor for matcher syntax.  Moreover,
an application whose selected conversion is `matcherToSlot` cannot inhabit
the application constructor, because that constructor explicitly requires
`ordinary`.
-/

namespace TypePM.Source

mutual

  /-- Node-by-node evidence that all pending obligations created by one
  relational elaboration select ordinary equality under `substitution`. -/
  inductive ElaborationResolutionsOrdinaryAt (substitution : Subst) :
      {signature : Signature} → {context : Context} → {expression : Expr} →
      {supply : Supply} → {generated : Generated} → {next : Supply} →
      Elaborates signature context expression supply generated next → Prop where
    | var {context : Context} {index : Nat} {scheme : Scheme}
        (lookup : context[index]? = some scheme) :
        ElaborationResolutionsOrdinaryAt substitution (Elaborates.var lookup)
    | lit :
        ElaborationResolutionsOrdinaryAt substitution (Elaborates.lit)
    | something :
        ElaborationResolutionsOrdinaryAt substitution (Elaborates.something)
    | lam
        {signature : Signature} {context : Context} {bodyExpression : Expr}
        {supply : Supply} {generatedBody : Generated} {next : Supply}
        {bodyElaboration : Elaborates signature
          (.mono (.var ⟨supply.ty⟩) :: context) bodyExpression
          (supply.nextTy 1) generatedBody next}
        (body : ElaborationResolutionsOrdinaryAt substitution bodyElaboration) :
        ElaborationResolutionsOrdinaryAt substitution
          (Elaborates.lam bodyElaboration)
    | app
        {signature : Signature} {context : Context}
        {functionExpression argumentExpression : Expr} {supply : Supply}
        {generatedFunction : Generated} {afterFunction : Supply}
        {generatedArgument : Generated} {afterArgument : Supply}
        {functionElaboration : Elaborates signature context functionExpression
          supply generatedFunction afterFunction}
        {argumentElaboration : Elaborates signature context argumentExpression
          afterFunction generatedArgument afterArgument}
        (function :
          ElaborationResolutionsOrdinaryAt substitution functionElaboration)
        (argument :
          ElaborationResolutionsOrdinaryAt substitution argumentElaboration)
        (application :
          ((CheckObligation.mk generatedArgument.target
            (.var ⟨afterArgument.ty⟩)).resolutionUnder substitution).conversionClass =
              ConversionClass.ordinary) :
        ElaborationResolutionsOrdinaryAt substitution
          (Elaborates.app functionElaboration argumentElaboration)
    | tuple
        {signature : Signature} {context : Context} {expressions : List Expr}
        {supply : Supply} {generatedItems : GeneratedItems} {next : Supply}
        {itemsElaboration : ElaboratesItems signature context expressions supply
          generatedItems next}
        (items : ItemsResolutionsOrdinaryAt substitution itemsElaboration) :
        ElaborationResolutionsOrdinaryAt substitution
          (Elaborates.tuple itemsElaboration)
    | letE
        {signature : Signature} {context : Context}
        {valueExpression bodyExpression : Expr} {supply : Supply}
        {generatedValue : Generated} {afterValue : Supply}
        {closure : PrincipalBlockClosure generatedValue}
        {absorbing : closure.Absorbing}
        {generatedBody : Generated} {next : Supply}
        {valueElaboration : Elaborates signature context valueExpression supply
          generatedValue afterValue}
        {bodyElaboration : Elaborates signature
          ((context.applyFree closure.substitution).generalize closure.target ::
            context.applyFree closure.substitution)
          bodyExpression
          (afterValue.join
            (context.applyFree closure.substitution).initialSupply)
          generatedBody next}
        (body : ElaborationResolutionsOrdinaryAt substitution bodyElaboration) :
        ElaborationResolutionsOrdinaryAt substitution
          (Elaborates.letE valueElaboration closure absorbing bodyElaboration)
    | ctor
        {signature : Signature} {context : Context} {constructor : DataCtor}
        {arguments : List Expr} {scheme : Scheme} {supply : Supply}
        {generated : Generated} {next : Supply}
        {lookup : signature.lookupDataConstructor constructor = some scheme}
        {arity : arguments.length = scheme.callArity} {closed : scheme.Closed}
        {callElaboration : ElaboratesCall signature context
          ⟨(scheme.instantiate supply).1, [], []⟩ arguments
          (scheme.instantiate supply).2 generated next}
        (call : CallResolutionsOrdinaryAt substitution callElaboration) :
        ElaborationResolutionsOrdinaryAt substitution
          (Elaborates.ctor lookup arity closed callElaboration)
    | prim
        {signature : Signature} {context : Context} {operation : PrimOp}
        {arguments : List Expr} {scheme : Scheme} {supply : Supply}
        {generated : Generated} {next : Supply}
        {lookup : signature.lookupPrimitive operation = some scheme}
        {arity : arguments.length = scheme.callArity} {closed : scheme.Closed}
        {callElaboration : ElaboratesCall signature context
          ⟨(scheme.instantiate supply).1, [], []⟩ arguments
          (scheme.instantiate supply).2 generated next}
        (call : CallResolutionsOrdinaryAt substitution callElaboration) :
        ElaborationResolutionsOrdinaryAt substitution
          (Elaborates.prim lookup arity closed callElaboration)
    | ifE
        {signature : Signature} {context : Context}
        {condition thenBranch elseBranch : Expr} {supply : Supply}
        {generated : Generated} {next : Supply}
        {callElaboration : ElaboratesCall signature context
          ⟨(conditionalScheme.instantiate supply).1, [], []⟩
          [condition, thenBranch, elseBranch]
          (conditionalScheme.instantiate supply).2 generated next}
        (call : CallResolutionsOrdinaryAt substitution callElaboration) :
        ElaborationResolutionsOrdinaryAt substitution
          (Elaborates.ifE callElaboration)

  /-- Pointwise structural evidence for tuple children. -/
  inductive ItemsResolutionsOrdinaryAt (substitution : Subst) :
      {signature : Signature} → {context : Context} → {expressions : List Expr} →
      {supply : Supply} → {generated : GeneratedItems} → {next : Supply} →
      ElaboratesItems signature context expressions supply generated next → Prop where
    | nil : ItemsResolutionsOrdinaryAt substitution ElaboratesItems.nil
    | cons
        {signature : Signature} {context : Context}
        {expression : Expr} {expressions : List Expr} {supply : Supply}
        {generatedItem : Generated} {afterItem : Supply}
        {generatedItems : GeneratedItems} {next : Supply}
        {headElaboration : Elaborates signature context expression supply
          generatedItem afterItem}
        {tailElaboration : ElaboratesItems signature context expressions afterItem
          generatedItems next}
        (head : ElaborationResolutionsOrdinaryAt substitution headElaboration)
        (tail : ItemsResolutionsOrdinaryAt substitution tailElaboration) :
        ItemsResolutionsOrdinaryAt substitution
          (ElaboratesItems.cons headElaboration tailElaboration)

  /-- Structural evidence for a non-nullary call.  `nil` creates no new
  obligation.  Every `cons` records both the argument's evidence and the one
  conversion introduced when the accumulated function is applied to it. -/
  inductive CallResolutionsOrdinaryAt (substitution : Subst) :
      {signature : Signature} → {context : Context} →
      {accumulated : Generated} → {arguments : List Expr} →
      {supply : Supply} → {generated : Generated} → {next : Supply} →
      ElaboratesCall signature context accumulated arguments supply generated next →
      Prop where
    | nil : CallResolutionsOrdinaryAt substitution ElaboratesCall.nil
    | cons
        {signature : Signature} {context : Context}
        {accumulated : Generated} {argumentExpression : Expr}
        {argumentExpressions : List Expr} {supply : Supply}
        {generatedArgument : Generated} {afterArgument : Supply}
        {generated : Generated} {next : Supply}
        {argumentElaboration : Elaborates signature context argumentExpression
          supply generatedArgument afterArgument}
        {tailElaboration : ElaboratesCall signature context
          (Generated.fromApp accumulated generatedArgument
            (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
          argumentExpressions (afterArgument.nextTy 2) generated next}
        (argument :
          ElaborationResolutionsOrdinaryAt substitution argumentElaboration)
        (application :
          ((CheckObligation.mk generatedArgument.target
            (.var ⟨afterArgument.ty⟩)).resolutionUnder substitution).conversionClass =
              ConversionClass.ordinary)
        (tail : CallResolutionsOrdinaryAt substitution tailElaboration) :
        CallResolutionsOrdinaryAt substitution
          (ElaboratesCall.cons argumentElaboration tailElaboration)

end

mutual

  /-- Structural evidence covers exactly every pending obligation in the
  generated expression block. -/
  theorem ElaborationResolutionsOrdinaryAt.pending
      {signature : Signature} {context : Context} {expression : Expr}
      {supply : Supply} {generated : Generated} {next : Supply}
      {elaboration : Elaborates signature context expression supply generated next}
      (ordinary : ElaborationResolutionsOrdinaryAt substitution elaboration) :
      PendingResolutionsOrdinaryAt substitution generated.pending := by
    cases ordinary with
    | var | lit | something => exact PendingResolutionsOrdinaryAt.nil _
    | lam body => exact body.pending
    | app function argument application =>
        exact PendingResolutionsOrdinaryAt.fromApp
          function.pending argument.pending application
    | tuple items => exact items.pending
    | letE body => exact PendingResolutionsOrdinaryAt.fromLet body.pending
    | ctor call | prim call | ifE call =>
        exact call.pending (PendingResolutionsOrdinaryAt.nil _)
  termination_by expression.complexity * 3 + 2
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

  /-- Tuple evidence covers the concatenated pending lists of all children. -/
  theorem ItemsResolutionsOrdinaryAt.pending
      {signature : Signature} {context : Context} {expressions : List Expr}
      {supply : Supply} {generated : GeneratedItems} {next : Supply}
      {elaboration : ElaboratesItems signature context expressions supply
        generated next}
      (ordinary : ItemsResolutionsOrdinaryAt substitution elaboration) :
      PendingResolutionsOrdinaryAt substitution generated.pending := by
    cases ordinary with
    | nil => exact PendingResolutionsOrdinaryAt.nil _
    | cons head tail => exact head.pending.append tail.pending
  termination_by Expr.listComplexity expressions * 3 + 1
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

  /-- Call evidence extends an ordinary certificate for the accumulated
  function across every argument and returns the certificate for the actual
  final generated call block. -/
  theorem CallResolutionsOrdinaryAt.pending
      {signature : Signature} {context : Context}
      {accumulated generated : Generated} {arguments : List Expr}
      {supply next : Supply}
      {elaboration : ElaboratesCall signature context accumulated arguments
        supply generated next}
      (ordinary : CallResolutionsOrdinaryAt substitution elaboration)
      (accumulatedOrdinary :
        PendingResolutionsOrdinaryAt substitution accumulated.pending) :
      PendingResolutionsOrdinaryAt substitution generated.pending := by
    cases ordinary with
    | nil => exact accumulatedOrdinary
    | cons argument application tail =>
        exact tail.pending (PendingResolutionsOrdinaryAt.fromApp
          accumulatedOrdinary argument.pending application)
  termination_by Expr.listComplexity arguments * 3
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

end

/-- Structural evidence cannot hide a special matcher-to-slot conversion in
the generated pending list. -/
theorem ElaborationResolutionsOrdinaryAt.not_of_matcherToSlot
    {signature : Signature} {context : Context} {expression : Expr}
    {supply : Supply} {generated : Generated} {next : Supply}
    {elaboration : Elaborates signature context expression supply generated next}
    (membership : obligation ∈ generated.pending)
    (special :
      (obligation.resolutionUnder substitution).conversionClass =
        ConversionClass.matcherToSlot) :
    ¬ ElaborationResolutionsOrdinaryAt substitution elaboration := by
  intro ordinary
  have selected := ordinary.pending obligation membership
  rw [special] at selected
  contradiction

private theorem pendingOrdinary_of_subset
    (ordinary : PendingResolutionsOrdinaryAt substitution whole)
    (subset : ∀ obligation, obligation ∈ part → obligation ∈ whole) :
    PendingResolutionsOrdinaryAt substitution part := by
  intro obligation membership
  exact ordinary obligation (subset obligation membership)

/-- The pending list of the accumulated function is a prefix of the pending
list returned by the complete relational call. -/
theorem ElaboratesCall.accumulatedPending_subset_final
    (elaboration : ElaboratesCall signature context accumulated arguments
      supply generated next) :
    ∀ obligation, obligation ∈ accumulated.pending →
      obligation ∈ generated.pending := by
  cases arguments with
  | nil =>
      cases elaboration
      exact fun _ membership => membership
  | cons argument arguments =>
      cases elaboration with
      | cons argumentElaboration tailElaboration =>
          intro obligation membership
          exact tailElaboration.accumulatedPending_subset_final obligation (by
            simp only [Generated.fromApp, List.mem_append]
            exact .inl (.inl membership))
termination_by Expr.listComplexity arguments * 3
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals try simp
  all_goals omega

mutual

  /-- A list-level ordinary certificate can be decomposed along the exact
  relational source derivation.  Consequently the structural evidence loses
  no ordinary applications from the generated block. -/
  theorem ElaborationResolutionsOrdinaryAt.of_pending
      {signature : Signature} {context : Context} {expression : Expr}
      {supply : Supply} {generated : Generated} {next : Supply}
      (elaboration : Elaborates signature context expression supply generated next)
      (ordinary : PendingResolutionsOrdinaryAt substitution generated.pending) :
      ElaborationResolutionsOrdinaryAt substitution elaboration := by
    cases elaboration with
    | var lookup => exact .var lookup
    | lit => exact .lit
    | something => exact .something
    | lam bodyElaboration =>
        exact .lam (ElaborationResolutionsOrdinaryAt.of_pending
          bodyElaboration ordinary)
    | app functionElaboration argumentElaboration =>
        exact .app
          (ElaborationResolutionsOrdinaryAt.of_pending functionElaboration
            (pendingOrdinary_of_subset ordinary (by
              intro obligation membership
              simp only [List.mem_append]
              exact .inl (.inl membership))))
          (ElaborationResolutionsOrdinaryAt.of_pending argumentElaboration
            (pendingOrdinary_of_subset ordinary (by
              intro obligation membership
              simp only [List.mem_append]
              exact .inl (.inr membership))))
          (ordinary _ (by simp))
    | tuple itemsElaboration =>
        exact .tuple (ItemsResolutionsOrdinaryAt.of_pending
          itemsElaboration ordinary)
    | letE valueElaboration closure absorbing bodyElaboration =>
        exact ElaborationResolutionsOrdinaryAt.letE
          (valueElaboration := valueElaboration) (absorbing := absorbing)
          (ElaborationResolutionsOrdinaryAt.of_pending bodyElaboration ordinary)
    | ctor lookup arity closed callElaboration =>
        exact ElaborationResolutionsOrdinaryAt.ctor
          (lookup := lookup) (arity := arity) (closed := closed)
          (CallResolutionsOrdinaryAt.of_pending callElaboration ordinary)
    | prim lookup arity closed callElaboration =>
        exact ElaborationResolutionsOrdinaryAt.prim
          (lookup := lookup) (arity := arity) (closed := closed)
          (CallResolutionsOrdinaryAt.of_pending callElaboration ordinary)
    | ifE callElaboration =>
        exact .ifE (CallResolutionsOrdinaryAt.of_pending
          callElaboration ordinary)
  termination_by expression.complexity * 3 + 2
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

  theorem ItemsResolutionsOrdinaryAt.of_pending
      {signature : Signature} {context : Context} {expressions : List Expr}
      {supply : Supply} {generated : GeneratedItems} {next : Supply}
      (elaboration : ElaboratesItems signature context expressions supply
        generated next)
      (ordinary : PendingResolutionsOrdinaryAt substitution generated.pending) :
      ItemsResolutionsOrdinaryAt substitution elaboration := by
    cases elaboration with
    | nil => exact .nil
    | cons headElaboration tailElaboration =>
        exact .cons
          (ElaborationResolutionsOrdinaryAt.of_pending headElaboration
            (pendingOrdinary_of_subset ordinary (by
              intro obligation membership
              simp only [List.mem_append]
              exact .inl membership)))
          (ItemsResolutionsOrdinaryAt.of_pending tailElaboration
            (pendingOrdinary_of_subset ordinary (by
              intro obligation membership
              simp only [List.mem_append]
              exact .inr membership)))
  termination_by Expr.listComplexity expressions * 3 + 1
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

  theorem CallResolutionsOrdinaryAt.of_pending
      {signature : Signature} {context : Context}
      {accumulated generated : Generated} {arguments : List Expr}
      {supply next : Supply}
      (elaboration : ElaboratesCall signature context accumulated arguments
        supply generated next)
      (ordinary : PendingResolutionsOrdinaryAt substitution generated.pending) :
      CallResolutionsOrdinaryAt substitution elaboration := by
    cases elaboration with
    | nil => exact .nil
    | @cons context accumulated argument arguments supply generatedArgument
        afterArgument generated next argumentElaboration tailElaboration =>
        have prefixSubset := tailElaboration.accumulatedPending_subset_final
        have applicationMembership :
            CheckObligation.mk generatedArgument.target
                (.var ⟨afterArgument.ty⟩) ∈
              (Generated.fromApp accumulated generatedArgument
                (.var ⟨afterArgument.ty⟩)
                (.var ⟨afterArgument.ty + 1⟩)).pending := by
          simp [Generated.fromApp]
        exact .cons
          (ElaborationResolutionsOrdinaryAt.of_pending argumentElaboration
            (pendingOrdinary_of_subset ordinary (by
              intro obligation membership
              apply prefixSubset
              simp only [Generated.fromApp, List.mem_append]
              exact .inl (.inr membership))))
          (ordinary _ (prefixSubset _ applicationMembership))
          (CallResolutionsOrdinaryAt.of_pending tailElaboration ordinary)
  termination_by Expr.listComplexity arguments * 3
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals try simp
    all_goals omega

end

/-- Source-level root certificate retaining the origin of every ordinary
pending obligation in the actual relational elaboration tree. -/
def InferenceRootResolutionsOrdinaryStructural
    (signature : Signature) (context : Context) (expression : Expr) : Prop :=
  ∀ generated next,
    elaborate signature context expression context.initialSupply =
      some (generated, next) →
    ∀ output,
      saturateUsing unify generated.hard generated.pending = some output →
      ∃ elaboration : Elaborates signature context expression
          context.initialSupply generated next,
        ElaborationResolutionsOrdinaryAt output.substitution elaboration

/-- The executable root certificate can be refined into structural evidence
whenever the signature is well formed. -/
theorem InferenceRootResolutionsOrdinaryStructural.of_rootPending
    (wellFormed : signature.WellFormed)
    (ordinary : InferenceRootPendingResolutionsOrdinary signature context
      expression) :
    InferenceRootResolutionsOrdinaryStructural signature context expression := by
  intro generated next elaborated output saturated
  let derivation := elaborate_sound wellFormed elaborated
  exact ⟨derivation,
    ElaborationResolutionsOrdinaryAt.of_pending derivation
      (ordinary generated next elaborated output saturated)⟩

/-- Forgetting node origins recovers the root pending certificate used by
the protected runtime bridge. -/
theorem InferenceRootResolutionsOrdinaryStructural.rootPending
    (structural : InferenceRootResolutionsOrdinaryStructural signature context
      expression) :
    InferenceRootPendingResolutionsOrdinary signature context expression := by
  intro generated next elaborated output saturated
  obtain ⟨derivation, ordinary⟩ :=
    structural generated next elaborated output saturated
  exact ordinary.pending


namespace PolymorphicLetInferenceOrdinaryStructural

open Runtime
open PolymorphicLetProtectedSyntaxRegression

set_option linter.unusedSimpArgs false

/-! ## Actual non-nullary source regression

This existing Paper 1 fixture contains a three-argument conditional.  Its
true branch contains a two-argument list constructor, a two-argument
primitive addition, and ordinary applications of one polymorphic identity at
both `Int` and matcher types.  It therefore exercises nested application and
non-nullary call composition in one actual root elaboration.
-/

set_option maxRecDepth 100000 in
private theorem protectedSyntaxBody_rootFuelCheck :
    inferenceRootPendingResolutionsOrdinaryCheckUsing (unifyWithFuel 1000)
      Paper1Signature.signature [identityScheme] protectedSyntaxBody = true := by
  with_unfolding_all rfl

theorem protectedSyntaxBody_rootPendingCheck :
    inferenceRootPendingResolutionsOrdinaryCheck
      Paper1Signature.signature [identityScheme] protectedSyntaxBody = true := by
  exact inferenceRootPendingResolutionsOrdinaryCheck_unify_of_fuel
    protectedSyntaxBody_rootFuelCheck

theorem protectedSyntaxBody_rootPendingOrdinary :
    InferenceRootPendingResolutionsOrdinary Paper1Signature.signature
      [identityScheme] protectedSyntaxBody := by
  intro generated next elaborated
  have checked := protectedSyntaxBody_rootPendingCheck
  simp only [inferenceRootPendingResolutionsOrdinaryCheck,
    inferenceRootPendingResolutionsOrdinaryCheckUsing, elaborated] at checked
  exact RootPendingResolutionsOrdinary.of_check checked

/-- The actual root certificate is decomposed along the relational
elaboration tree.  In particular, each argument of the constructor,
primitive, and conditional calls has its own structural evidence, and every
application node carries its selected ordinary conversion. -/
theorem protectedSyntaxBody_rootStructuralOrdinary :
    InferenceRootResolutionsOrdinaryStructural Paper1Signature.signature
      [identityScheme] protectedSyntaxBody :=
  InferenceRootResolutionsOrdinaryStructural.of_rootPending
    Paper1Signature.wellFormed protectedSyntaxBody_rootPendingOrdinary

theorem protectedSyntaxBody_residualsOrdinary :
    InferenceResidualsOrdinary Paper1Signature.signature [identityScheme]
      protectedSyntaxBody :=
  InferenceRootPendingResolutionsOrdinary.inferenceResidualsOrdinary
    protectedSyntaxBody_rootStructuralOrdinary.rootPending

theorem protectedSyntaxBody_runtimeTypingFromInfer
    (success : infer Paper1Signature.signature [identityScheme]
      protectedSyntaxBody = some target) :
    ProtectedRuntimeTyping [true] protectedSyntaxBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  obtain ⟨certified⟩ := Inference.infer_success_ordinaryPrincipalTyping
    Paper1Signature.wellFormed success protectedSyntaxBody_residualsOrdinary
  have typing := protectedSyntaxBody_supported.elaboration_typing
    Runtime.paper1SignatureCompatible certified.derivation.elaboration
      (Runtime.strictSemanticSolution_of_closure certified.derivation.closure
        certified.ordinary)
      (by
        apply Runtime.ProtectedContextCompatible.pushCanonical
            (canonicalSupply := ⟨0, 0⟩)
        · intro index membership
          simp [identityScheme, Scheme.freeTyVars, PolyTy.freeTyVars,
            dedupFirst, dedup] at membership
        · intro index membership
          simp [identityScheme, Scheme.freeCapVars, PolyTy.freeCapVars,
            dedupFirst, dedup] at membership
        · exact Runtime.ProtectedContextCompatible.nil)
  rw [certified.derivation.target_eq]
  exact typing

theorem protectedSyntaxBody_neverStuckFromInfer
    (success : infer Paper1Signature.signature [identityScheme]
      protectedSyntaxBody = some target)
    (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      protectedSyntaxBody).NotStuck := by
  apply (protectedSyntaxBody_runtimeTypingFromInfer success).neverStuck
  exact EnvironmentTyping.cons
    (.plainClosure .nil (.var rfl)) EnvironmentTyping.nil

set_option maxRecDepth 100000 in
private theorem protectedSyntaxBody_sourceInferFuelSome :
    (match elaborate Paper1Signature.signature [identityScheme]
        protectedSyntaxBody (Context.initialSupply [identityScheme]) with
      | none => false
      | some (generated, _) =>
          (inferGeneratedUsing (unifyWithFuel 1000) generated).isSome) = true := by
  with_unfolding_all rfl

theorem infer_protectedSyntaxBody_isSome :
    ∃ target, infer Paper1Signature.signature [identityScheme]
      protectedSyntaxBody = some target := by
  have fuelSome := protectedSyntaxBody_sourceInferFuelSome
  cases elaborated : elaborate Paper1Signature.signature [identityScheme]
      protectedSyntaxBody (Context.initialSupply [identityScheme]) with
  | none => simp [elaborated] at fuelSome
  | some output =>
      rcases output with ⟨generated, next⟩
      simp only [elaborated] at fuelSome
      cases fuelResult : inferGeneratedUsing (unifyWithFuel 1000) generated with
      | none => simp [fuelResult] at fuelSome
      | some result =>
          have publicResult := inferGeneratedUsing_unify_of_fuel_success fuelResult
          refine ⟨result.target, ?_⟩
          unfold infer elaborateRoot
          simp [elaborated, publicResult]

/-- Public inference supplies the source derivation and the ordinary residual
certificate; no runtime typing derivation is written by hand. -/
theorem protectedSyntaxBody_runtimeTyping :
    ∃ target, ProtectedRuntimeTyping [true] protectedSyntaxBody target
      [(identityScheme.instantiate ⟨0, 0⟩).1] := by
  obtain ⟨target, success⟩ := infer_protectedSyntaxBody_isSome
  exact ⟨target, protectedSyntaxBody_runtimeTypingFromInfer success⟩

theorem protectedSyntaxBody_neverStuck (fuel : Nat) :
    (evalFuel fuel [Value.plainClosure [] (.var 0)]
      protectedSyntaxBody).NotStuck := by
  obtain ⟨target, success⟩ := infer_protectedSyntaxBody_isSome
  exact protectedSyntaxBody_neverStuckFromInfer success fuel

end PolymorphicLetInferenceOrdinaryStructural
end TypePM.Source
