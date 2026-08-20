import TypePM.Source.PolymorphicLetInferenceOrdinaryStructuralChecker

/-!
# Source-structural automation for ordinary root resolutions

The checker in this module follows the successful executable source
elaboration one node at a time.  At an application it checks exactly the
new obligation introduced at that node.  Tuple and call lists are traversed
structurally.  A `letE` right-hand side is elaborated and closed only to find
the body context and supply; its pending obligations are not checked because
they are internal to that closure and do not occur in the root pending list.

The comparison theorem is deliberately indexed by one successful executable
elaboration and one fixed substitution.  It does not claim that source
syntax alone makes applications ordinary, nor that arbitrary inference
succeeds.
-/

namespace TypePM.Source

set_option linter.unusedSimpArgs false

private def ordinaryResolutionCheck
    (substitution : Subst) (source expected : Ty) : Bool :=
  ((CheckObligation.mk source expected).resolutionUnder substitution).conversionClass ==
    .ordinary

mutual

  /-- Check the actual root obligations locally while replaying executable
  elaboration only far enough to recover the generated types and supplies
  needed at each application node. -/
  def sourceStructuralOrdinaryCheckAt
      (substitution : Subst) (signature : Signature) (context : Context) :
      Expr → Supply → Bool
    | .var _, _ => true
    | .lit _, _ => true
    | .something, _ => true
    | .lam body, supply =>
        sourceStructuralOrdinaryCheckAt substitution signature
          (.mono (.var ⟨supply.ty⟩) :: context) body (supply.nextTy 1)
    | .app function argument, supply =>
        match elaborate signature context function supply with
        | none => false
        | some (_, afterFunction) =>
            match elaborate signature context argument afterFunction with
            | none => false
            | some (generatedArgument, afterArgument) =>
                sourceStructuralOrdinaryCheckAt substitution signature context
                    function supply &&
                  sourceStructuralOrdinaryCheckAt substitution signature context
                    argument afterFunction &&
                  ordinaryResolutionCheck substitution generatedArgument.target
                    (.var ⟨afterArgument.ty⟩)
    | .tuple items, supply =>
        sourceItemsStructuralOrdinaryCheckAt substitution signature context
          items supply
    | .letE value body, supply =>
        match elaborate signature context value supply with
        | none => false
        | some (generatedValue, afterValue) =>
            match inferGeneratedUsing unify generatedValue with
            | none => false
            | some closedValue =>
                let closedContext := context.applyFree closedValue.substitution
                sourceStructuralOrdinaryCheckAt substitution signature
                  (closedContext.generalize closedValue.target :: closedContext)
                  body (afterValue.join closedContext.initialSupply)
    | .ctor constructor arguments, supply =>
        match signature.lookupDataConstructor constructor with
        | none => false
        | some scheme =>
            if arguments.length = scheme.callArity then
              sourceCallStructuralOrdinaryCheckAt substitution signature context
                ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                (scheme.instantiate supply).2
            else false
    | .prim operation arguments, supply =>
        match signature.lookupPrimitive operation with
        | none => false
        | some scheme =>
            if arguments.length = scheme.callArity then
              sourceCallStructuralOrdinaryCheckAt substitution signature context
                ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                (scheme.instantiate supply).2
            else false
    | .ifE condition thenBranch elseBranch, supply =>
        sourceCallStructuralOrdinaryCheckAt substitution signature context
          ⟨(conditionalScheme.instantiate supply).1, [], []⟩
          [condition, thenBranch, elseBranch]
          (conditionalScheme.instantiate supply).2
    | .fixE _, _ => false
    | .matcher _, _ => false
    | .matchAll _ _ _ _, _ => false
    | .matchFirst _ _ _ _, _ => false
  termination_by expression _ => expression.complexity * 3 + 2

  /-- List traversal used by tuples. -/
  def sourceItemsStructuralOrdinaryCheckAt
      (substitution : Subst) (signature : Signature) (context : Context) :
      List Expr → Supply → Bool
    | [], _ => true
    | item :: items, supply =>
        match elaborate signature context item supply with
        | none => false
        | some (_, afterItem) =>
            sourceStructuralOrdinaryCheckAt substitution signature context item
                supply &&
              sourceItemsStructuralOrdinaryCheckAt substitution signature context
                items afterItem
  termination_by expressions _ => Expr.listComplexity expressions * 3 + 1

  /-- Argument traversal used by constructors, primitives, and conditionals.
  Each nonempty step checks exactly the obligation introduced by applying the
  accumulated function type to that argument. -/
  def sourceCallStructuralOrdinaryCheckAt
      (substitution : Subst) (signature : Signature) (context : Context) :
      Generated → List Expr → Supply → Bool
    | _, [], _ => true
    | accumulated, argument :: arguments, supply =>
        match elaborate signature context argument supply with
        | none => false
        | some (generatedArgument, afterArgument) =>
            let domain : Ty := .var ⟨afterArgument.ty⟩
            let target : Ty := .var ⟨afterArgument.ty + 1⟩
            sourceStructuralOrdinaryCheckAt substitution signature context
                argument supply &&
              ordinaryResolutionCheck substitution generatedArgument.target domain &&
              sourceCallStructuralOrdinaryCheckAt substitution signature context
                (Generated.fromApp accumulated generatedArgument domain target)
                arguments (afterArgument.nextTy 2)
  termination_by _ expressions _ =>
    Expr.listComplexity expressions * 3

end

mutual

  /-- On one successful executable elaboration, structural traversal checks
  exactly the generated root pending list. -/
  theorem sourceStructuralOrdinaryCheckAt_eq_pending
      {signature : Signature} {context : Context} {expression : Expr}
      {supply next : Supply} {generated : Generated}
      (success : elaborate signature context expression supply =
        some (generated, next)) :
      sourceStructuralOrdinaryCheckAt substitution signature context expression
          supply =
        generated.pending.all (fun obligation =>
          (obligation.resolutionUnder substitution).conversionClass ==
            .ordinary) := by
    cases expression with
    | var index =>
        cases lookup : context[index]? with
        | none => simp [elaborate, lookup] at success
        | some scheme =>
            have equality :
                (⟨(scheme.instantiate supply).1, [], []⟩,
                  (scheme.instantiate supply).2) = (generated, next) :=
              Option.some.inj (by simpa [elaborate, lookup] using success)
            injection equality with generatedEquality nextEquality
            subst generated
            subst next
            simp [sourceStructuralOrdinaryCheckAt]
    | lit value =>
        have equality : (⟨Ty.int, [], []⟩, supply) = (generated, next) :=
          Option.some.inj (by simpa [elaborate] using success)
        injection equality with generatedEquality nextEquality
        subst generated
        subst next
        simp [sourceStructuralOrdinaryCheckAt]
    | something =>
        have equality :
            (⟨Ty.matcher .any (.var ⟨supply.ty⟩), [], []⟩,
              supply.nextTy 1) = (generated, next) :=
          Option.some.inj (by simpa [elaborate] using success)
        injection equality with generatedEquality nextEquality
        subst generated
        subst next
        simp [sourceStructuralOrdinaryCheckAt]
    | lam body =>
        cases bodyResult : elaborate signature
            (.mono (.var ⟨supply.ty⟩) :: context) body (supply.nextTy 1) with
        | none => simp [elaborate, bodyResult] at success
        | some output =>
            cases output with
            | mk generatedBody afterBody =>
                have equality :
                    (⟨Ty.fn (.var ⟨supply.ty⟩) generatedBody.target,
                        generatedBody.hard, generatedBody.pending⟩,
                      afterBody) = (generated, next) :=
                  Option.some.inj
                    (by simpa [elaborate, bodyResult] using success)
                injection equality with generatedEquality nextEquality
                subst generated
                subst next
                rw [sourceStructuralOrdinaryCheckAt]
                exact sourceStructuralOrdinaryCheckAt_eq_pending
                  (substitution := substitution) (signature := signature)
                  (context := .mono (.var ⟨supply.ty⟩) :: context)
                  (expression := body) (supply := supply.nextTy 1)
                  (next := afterBody) (generated := generatedBody) bodyResult
    | app function argument =>
        cases functionResult : elaborate signature context function supply with
        | none => simp [elaborate, functionResult] at success
        | some functionOutput =>
            cases functionOutput with
            | mk generatedFunction afterFunction =>
              cases argumentResult : elaborate signature context argument
                  afterFunction with
              | none => simp [elaborate, functionResult, argumentResult] at success
              | some argumentOutput =>
                cases argumentOutput with
                | mk generatedArgument afterArgument =>
                  have equality :
                      (⟨Ty.var ⟨afterArgument.ty + 1⟩,
                          generatedFunction.hard ++ generatedArgument.hard ++
                            [.ty generatedFunction.target
                              (.fn (.var ⟨afterArgument.ty⟩)
                                (.var ⟨afterArgument.ty + 1⟩))],
                          generatedFunction.pending ++
                            generatedArgument.pending ++
                            [⟨generatedArgument.target,
                              .var ⟨afterArgument.ty⟩⟩]⟩,
                        afterArgument.nextTy 2) = (generated, next) :=
                    Option.some.inj (by
                      simpa [elaborate, functionResult, argumentResult]
                        using success)
                  injection equality with generatedEquality nextEquality
                  subst generated
                  subst next
                  rw [sourceStructuralOrdinaryCheckAt]
                  simp only [functionResult, argumentResult]
                  rw [sourceStructuralOrdinaryCheckAt_eq_pending
                      (substitution := substitution) functionResult,
                    sourceStructuralOrdinaryCheckAt_eq_pending
                      (substitution := substitution) argumentResult]
                  simp [ordinaryResolutionCheck, Bool.and_assoc]
    | tuple items =>
        cases itemsResult : elaborateItems signature context items supply with
        | none => simp [elaborate, itemsResult] at success
        | some output =>
            cases output with
            | mk generatedItems afterItems =>
                have equality :
                    (⟨Ty.prod generatedItems.targets, generatedItems.hard,
                        generatedItems.pending⟩,
                      afterItems) = (generated, next) :=
                  Option.some.inj
                    (by simpa [elaborate, itemsResult] using success)
                injection equality with generatedEquality nextEquality
                subst generated
                subst next
                rw [sourceStructuralOrdinaryCheckAt]
                exact sourceItemsStructuralOrdinaryCheckAt_eq_pending
                  (substitution := substitution) itemsResult
    | letE value body =>
        cases valueResult : elaborate signature context value supply with
        | none => simp [elaborate, valueResult] at success
        | some valueOutput =>
            cases valueOutput with
            | mk generatedValue afterValue =>
              cases closureResult : inferGeneratedUsing unify generatedValue with
              | none => simp [elaborate, valueResult, closureResult] at success
              | some closedValue =>
                let closedContext := context.applyFree closedValue.substitution
                cases bodyResult : elaborate signature
                    (closedContext.generalize closedValue.target :: closedContext)
                    body (afterValue.join closedContext.initialSupply) with
                | none =>
                    simp [elaborate, valueResult, closureResult, closedContext,
                      bodyResult] at success
                | some bodyOutput =>
                  cases bodyOutput with
                  | mk generatedBody afterBody =>
                    have equality :
                        (Generated.fromLet
                            (context.interfaceEquations closedValue.substitution)
                            generatedBody,
                          afterBody) = (generated, next) :=
                      Option.some.inj (by
                        simpa [elaborate, valueResult, closureResult,
                          closedContext, bodyResult] using success)
                    injection equality with generatedEquality nextEquality
                    subst generated
                    subst next
                    rw [sourceStructuralOrdinaryCheckAt]
                    simp only [valueResult, closureResult, closedContext,
                      bodyResult]
                    exact sourceStructuralOrdinaryCheckAt_eq_pending
                      (substitution := substitution) (signature := signature)
                      (context := closedContext.generalize closedValue.target ::
                        closedContext)
                      (expression := body)
                      (supply := afterValue.join closedContext.initialSupply)
                      (next := afterBody) (generated := generatedBody) bodyResult
    | ctor constructor arguments =>
        cases lookup : signature.lookupDataConstructor constructor with
        | none => simp [elaborate, lookup] at success
        | some scheme =>
            by_cases arity : arguments.length = scheme.callArity
            · cases callResult : elaborateCall signature context
                  ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                  (scheme.instantiate supply).2 with
              | none => simp [elaborate, lookup, arity, callResult] at success
              | some output =>
                  cases output with
                  | mk generatedCall afterCall =>
                    have equality : (generatedCall, afterCall) =
                        (generated, next) :=
                      Option.some.inj (by
                        simpa [elaborate, lookup, arity, callResult]
                          using success)
                    injection equality with generatedEquality nextEquality
                    subst generated
                    subst next
                    rw [sourceStructuralOrdinaryCheckAt]
                    simp only [lookup, arity]
                    simpa using
                      sourceCallStructuralOrdinaryCheckAt_eq_pending
                        (substitution := substitution) callResult
            · simp [elaborate, lookup, arity] at success
    | prim operation arguments =>
        cases lookup : signature.lookupPrimitive operation with
        | none => simp [elaborate, lookup] at success
        | some scheme =>
            by_cases arity : arguments.length = scheme.callArity
            · cases callResult : elaborateCall signature context
                  ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                  (scheme.instantiate supply).2 with
              | none => simp [elaborate, lookup, arity, callResult] at success
              | some output =>
                  cases output with
                  | mk generatedCall afterCall =>
                    have equality : (generatedCall, afterCall) =
                        (generated, next) :=
                      Option.some.inj (by
                        simpa [elaborate, lookup, arity, callResult]
                          using success)
                    injection equality with generatedEquality nextEquality
                    subst generated
                    subst next
                    rw [sourceStructuralOrdinaryCheckAt]
                    simp only [lookup, arity]
                    simpa using
                      sourceCallStructuralOrdinaryCheckAt_eq_pending
                        (substitution := substitution) callResult
            · simp [elaborate, lookup, arity] at success
    | ifE condition thenBranch elseBranch =>
        cases callResult : elaborateCall signature context
            ⟨(conditionalScheme.instantiate supply).1, [], []⟩
            [condition, thenBranch, elseBranch]
            (conditionalScheme.instantiate supply).2 with
        | none => simp [elaborate, callResult] at success
        | some output =>
            cases output with
            | mk generatedCall afterCall =>
              have equality : (generatedCall, afterCall) = (generated, next) :=
                Option.some.inj
                  (by simpa [elaborate, callResult] using success)
              injection equality with generatedEquality nextEquality
              subst generated
              subst next
              rw [sourceStructuralOrdinaryCheckAt]
              simpa using
                sourceCallStructuralOrdinaryCheckAt_eq_pending
                  (substitution := substitution) callResult
    | fixE body => simp [elaborate] at success
    | matcher clauses => simp [elaborate] at success
    | matchAll target matcher pattern body => simp [elaborate] at success
    | matchFirst target matcher arms fallback => simp [elaborate] at success
  termination_by expression.complexity * 3 + 2
  decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

  theorem sourceItemsStructuralOrdinaryCheckAt_eq_pending
      {signature : Signature} {context : Context} {expressions : List Expr}
      {supply next : Supply} {generated : GeneratedItems}
      (success : elaborateItems signature context expressions supply =
        some (generated, next)) :
      sourceItemsStructuralOrdinaryCheckAt substitution signature context
          expressions supply =
        generated.pending.all (fun obligation =>
          (obligation.resolutionUnder substitution).conversionClass ==
            .ordinary) := by
    cases expressions with
    | nil =>
        have equality : (⟨[], [], []⟩, supply) = (generated, next) :=
          Option.some.inj (by simpa [elaborateItems] using success)
        injection equality with generatedEquality nextEquality
        subst generated
        subst next
        simp [sourceItemsStructuralOrdinaryCheckAt]
    | cons item items =>
        cases itemResult : elaborate signature context item supply with
        | none => simp [elaborateItems, itemResult] at success
        | some itemOutput =>
            cases itemOutput with
            | mk generatedItem afterItem =>
              cases itemsResult : elaborateItems signature context items
                  afterItem with
              | none => simp [elaborateItems, itemResult, itemsResult] at success
              | some itemsOutput =>
                cases itemsOutput with
                | mk generatedItems afterItems =>
                  have equality :
                      (⟨generatedItem.target :: generatedItems.targets,
                          generatedItem.hard ++ generatedItems.hard,
                          generatedItem.pending ++ generatedItems.pending⟩,
                        afterItems) = (generated, next) :=
                    Option.some.inj (by
                      simpa [elaborateItems, itemResult, itemsResult]
                        using success)
                  injection equality with generatedEquality nextEquality
                  subst generated
                  subst next
                  rw [sourceItemsStructuralOrdinaryCheckAt]
                  simp only [itemResult]
                  rw [sourceStructuralOrdinaryCheckAt_eq_pending
                      (substitution := substitution) itemResult,
                    sourceItemsStructuralOrdinaryCheckAt_eq_pending
                      (substitution := substitution) itemsResult]
                  simp
  termination_by Expr.listComplexity expressions * 3 + 1
  decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

  theorem sourceCallStructuralOrdinaryCheckAt_eq_pending
      {signature : Signature} {context : Context}
      {accumulated generated : Generated} {expressions : List Expr}
      {supply next : Supply}
      (success : elaborateCall signature context accumulated expressions supply =
        some (generated, next)) :
      (accumulated.pending.all (fun obligation =>
          (obligation.resolutionUnder substitution).conversionClass ==
            .ordinary) &&
        sourceCallStructuralOrdinaryCheckAt substitution signature context
          accumulated expressions supply) =
        generated.pending.all (fun obligation =>
          (obligation.resolutionUnder substitution).conversionClass ==
            .ordinary) := by
    cases expressions with
    | nil =>
        have equality : (accumulated, supply) = (generated, next) :=
          Option.some.inj (by simpa [elaborateCall] using success)
        injection equality with generatedEquality nextEquality
        subst generated
        subst next
        rw [sourceCallStructuralOrdinaryCheckAt]
        exact Bool.and_true _
    | cons argument arguments =>
        cases argumentResult : elaborate signature context argument supply with
        | none => simp [elaborateCall, argumentResult] at success
        | some output =>
            cases output with
            | mk generatedArgument afterArgument =>
              let domain : Ty := .var ⟨afterArgument.ty⟩
              let target : Ty := .var ⟨afterArgument.ty + 1⟩
              let nextAccumulated := Generated.fromApp accumulated
                generatedArgument domain target
              cases restResult : elaborateCall signature context nextAccumulated
                  arguments (afterArgument.nextTy 2) with
              | none =>
                  simp [elaborateCall, argumentResult, domain, target,
                    nextAccumulated, restResult] at success
              | some restOutput =>
                cases restOutput with
                | mk generatedRest afterRest =>
                  have equality : (generatedRest, afterRest) =
                      (generated, next) :=
                    Option.some.inj (by
                      simpa [elaborateCall, argumentResult, domain, target,
                        nextAccumulated, restResult] using success)
                  injection equality with generatedEquality nextEquality
                  subst generated
                  subst next
                  rw [sourceCallStructuralOrdinaryCheckAt]
                  simp only [argumentResult, domain, target]
                  rw [sourceStructuralOrdinaryCheckAt_eq_pending
                    (substitution := substitution) argumentResult]
                  have rest := sourceCallStructuralOrdinaryCheckAt_eq_pending
                    (substitution := substitution) restResult
                  rw [← rest]
                  simp [domain, target, nextAccumulated, Generated.fromApp,
                    ordinaryResolutionCheck, Bool.and_assoc,
                    Bool.and_left_comm, Bool.and_comm]
  termination_by Expr.listComplexity expressions * 3
  decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

end

/-! The call theorem above is stated for arbitrary accumulated blocks.  Calls
created by source constructors, primitives, and conditionals start from an
empty pending list, so its final conjunct simplifies away. -/

/-- Any actual nonordinary root obligation makes the local structural check
reject. -/
theorem sourceStructuralOrdinaryCheckAt_eq_false_of_nonordinary
    {signature : Signature} {context : Context} {expression : Expr}
    {supply next : Supply} {generated : Generated}
    (success : elaborate signature context expression supply =
      some (generated, next))
    (membership : obligation ∈ generated.pending)
    (nonordinary :
      (obligation.resolutionUnder substitution).conversionClass ≠ .ordinary) :
    sourceStructuralOrdinaryCheckAt substitution signature context expression
      supply = false := by
  rw [sourceStructuralOrdinaryCheckAt_eq_pending success]
  cases checked : generated.pending.all (fun candidate =>
      (candidate.resolutionUnder substitution).conversionClass == .ordinary) with
  | false => rfl
  | true =>
      simp only [List.all_eq_true, beq_iff_eq] at checked
      exact (nonordinary (checked obligation membership)).elim

/-- Source-structural form of the complete root check.  Failure of source
elaboration or hard saturation is rejected. -/
def inferenceRootStructuralOrdinaryCheckUsing
    (solve : List Equation → Option Subst)
    (signature : Signature) (context : Context) (expression : Expr) : Bool :=
  match elaborate signature context expression context.initialSupply with
  | none => false
  | some (generated, _) =>
      match saturateUsing solve generated.hard generated.pending with
      | none => false
      | some output =>
          sourceStructuralOrdinaryCheckAt output.substitution signature context
            expression context.initialSupply

def inferenceRootStructuralOrdinaryCheck
    (signature : Signature) (context : Context) (expression : Expr) : Bool :=
  inferenceRootStructuralOrdinaryCheckUsing unify signature context expression

/-- The source-structural checker computes the same Boolean as the existing
public root checker.  This is checker equivalence for the exact executable
elaboration and selected substitution, not equivalence with the quantified
public certificate. -/
theorem inferenceRootStructuralOrdinaryCheckUsing_eq_rootPending
    (solve : List Equation → Option Subst)
    (signature : Signature) (context : Context) (expression : Expr) :
    inferenceRootStructuralOrdinaryCheckUsing solve signature context expression =
      inferenceRootPendingResolutionsOrdinaryCheckUsing solve signature context
        expression := by
  unfold inferenceRootStructuralOrdinaryCheckUsing
    inferenceRootPendingResolutionsOrdinaryCheckUsing
  cases elaborated : elaborate signature context expression context.initialSupply with
  | none => rfl
  | some output =>
      rcases output with ⟨generated, next⟩
      simp only
      cases saturated : saturateUsing solve generated.hard generated.pending with
      | none => simp [rootPendingResolutionsOrdinaryCheckUsing, saturated]
      | some result =>
          simp [rootPendingResolutionsOrdinaryCheckUsing, saturated]
          exact sourceStructuralOrdinaryCheckAt_eq_pending
            (substitution := result.substitution) elaborated

theorem inferenceRootStructuralOrdinaryCheck_eq_rootPending
    (signature : Signature) (context : Context) (expression : Expr) :
    inferenceRootStructuralOrdinaryCheck signature context expression =
      inferenceRootPendingResolutionsOrdinaryCheck signature context expression :=
  inferenceRootStructuralOrdinaryCheckUsing_eq_rootPending unify signature context
    expression

/-- A bounded solver run can establish the public source-structural check;
the existing solver-success transport supplies the unbounded `unify` result. -/
theorem inferenceRootStructuralOrdinaryCheck_unify_of_fuel
    {solverFuel : Nat} {signature : Signature} {context : Context}
    {expression : Expr}
    (checked : inferenceRootStructuralOrdinaryCheckUsing
      (unifyWithFuel solverFuel) signature context expression = true) :
    inferenceRootStructuralOrdinaryCheck signature context expression = true := by
  rw [inferenceRootStructuralOrdinaryCheck_eq_rootPending]
  apply inferenceRootPendingResolutionsOrdinaryCheck_unify_of_fuel
  rw [← inferenceRootStructuralOrdinaryCheckUsing_eq_rootPending]
  exact checked

/-- A successful public source-structural check constructs the existing
node-indexed certificate.  Only this `true`-to-certificate direction is
claimed at the public root. -/
theorem InferenceRootResolutionsOrdinaryStructural.of_sourceStructuralCheck
    {signature : Signature} {context : Context} {expression : Expr}
    (wellFormed : signature.WellFormed)
    (checked : inferenceRootStructuralOrdinaryCheck signature context expression =
      true) :
    InferenceRootResolutionsOrdinaryStructural signature context expression := by
  apply InferenceRootResolutionsOrdinaryStructural.of_check wellFormed
  rw [← inferenceRootStructuralOrdinaryCheck_eq_rootPending]
  exact checked

end TypePM.Source
