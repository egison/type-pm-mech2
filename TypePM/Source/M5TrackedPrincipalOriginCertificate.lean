import TypePM.Source.M5PrincipalOriginCertificate
import TypePM.Source.M5TwoIndexBoundedDfsSearchBridge

/-!
# Search-occurrence-tracked principal Origin certificates

`PrincipalOriginRequestEvidence` deliberately exposes only the evaluator
preservation needed by M5 typed evaluation.  In particular, its elaboration
and additional branches do not retain the child request plans from which a
nested matching search was produced.  This module adds a parallel wrapper;
the existing certificate remains unchanged and is recovered by projection.

`SearchPlanCoverage` is indexed by the exact M4 elaboration judgment.  Its
structural constructors retain coverage for every evaluated child, while the
two matching constructors retain the dedicated raw matching plan.  Therefore
an unrelated syntax tree cannot be inserted as coverage for a principal
derivation.  The dynamic fact that evaluation reached one of these static
occurrences is a separate, later `IssuedAtOccurrence` layer.
-/

namespace TypePM.Source.M5TrackedPrincipalOriginCertificate

open TypePM.Runtime
open M4
open M5CompletionArchitecture
open M5PrincipalOriginCertificate

/- The following helpers assemble exactly the proof indices used by the
structural constructors below. -/

private def appElaboration
    (functionElaboration : ElaboratesFuel signature staticFuel context function
      supply generatedFunction afterFunction)
    (argumentElaboration : ElaboratesFuel signature staticFuel context argument
      afterFunction generatedArgument afterArgument) :
    ElaboratesFuel signature (staticFuel + 1) context (.app function argument)
      supply
      (Generated.fromApp generatedFunction generatedArgument
        (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
      (afterArgument.nextTy 2) := by
  simp only [ElaboratesFuel]
  exact ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
    functionElaboration, argumentElaboration, rfl, rfl⟩

private def tupleElaboration
    (itemsElaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context items supply generated next) :
    ElaboratesFuel signature (staticFuel + 1) context (.tuple items) supply
      ⟨.prod generated.targets, generated.hard, generated.pending⟩ next := by
  simp only [ElaboratesFuel]
  exact ⟨generated, itemsElaboration, rfl⟩

private def letElaboration
    (valueElaboration : ElaboratesFuel signature staticFuel context value supply
      generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (bodyElaboration : ElaboratesFuel signature staticFuel
      ((context.applyFree closure.substitution).generalize closure.target ::
        context.applyFree closure.substitution)
      body
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply)
      generatedBody next) :
    ElaboratesFuel signature (staticFuel + 1) context (.letE value body) supply
      (Generated.fromLet
        (context.interfaceEquations closure.substitution) generatedBody) next := by
  simp only [ElaboratesFuel]
  exact ⟨generatedValue, afterValue, valueElaboration, closure, generatedBody,
    absorbing, bodyElaboration, rfl⟩

private def ctorElaboration
    (lookup : signature.base.lookupDataConstructor constructor = some scheme)
    (arity : arguments.length = scheme.callArity)
    (closed : scheme.Closed)
    (argumentsElaboration : CallElaboratesUsing
      (ElaboratesFuel signature staticFuel) context
      ⟨(scheme.instantiate supply).1, [], []⟩ arguments
      (scheme.instantiate supply).2 generated next) :
    ElaboratesFuel signature (staticFuel + 1) context
      (.ctor constructor arguments) supply generated next := by
  simp only [ElaboratesFuel]
  exact ⟨scheme, lookup, arity, closed, argumentsElaboration⟩

private def primElaboration
    (lookup : signature.base.lookupPrimitive operation = some scheme)
    (arity : arguments.length = scheme.callArity)
    (closed : scheme.Closed)
    (argumentsElaboration : CallElaboratesUsing
      (ElaboratesFuel signature staticFuel) context
      ⟨(scheme.instantiate supply).1, [], []⟩ arguments
      (scheme.instantiate supply).2 generated next) :
    ElaboratesFuel signature (staticFuel + 1) context
      (.prim operation arguments) supply generated next := by
  simp only [ElaboratesFuel]
  exact ⟨scheme, lookup, arity, closed, argumentsElaboration⟩

private def ifElaboration
    (argumentsElaboration : CallElaboratesUsing
      (ElaboratesFuel signature staticFuel) context
      ⟨(conditionalScheme.instantiate supply).1, [], []⟩
      [condition, thenBranch, elseBranch]
      (conditionalScheme.instantiate supply).2 generated next) :
    ElaboratesFuel signature (staticFuel + 1) context
      (.ifE condition thenBranch elseBranch) supply generated next := by
  simpa only [ElaboratesFuel] using argumentsElaboration

private def matchAllElaboration
    (components : MatchAllElaboratesUsing
      (ElaboratesFuel signature staticFuel) signature context targetExpression
      matcherExpression pattern bodyExpression supply
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody) next) :
    ElaboratesFuel signature (staticFuel + 1) context
      (.matchAll targetExpression matcherExpression pattern bodyExpression)
      supply
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody) next := by
  simpa only [ElaboratesFuel] using components

mutual

  /-- Static search-plan coverage for one exact elaboration and evaluator
  fuel.  A raw plan is search-free at its matching boundary because
  `RawOriginRequestPlan` has no `matchAll` or `matchFirst` constructor.
  Structural constructors are proof-indexed by the same child elaborations
  used to assemble the parent judgment. -/
  inductive SearchPlanCoverage :
      {signature : FrozenSignature} → {staticFuel : Nat} →
      {context : Context} → {expression : Expr} → {supply : Supply} →
      {generated : Generated} → {next : Supply} →
      ElaboratesFuel signature staticFuel context expression supply generated
        next → Nat → Type where
    | raw
        (elaboration : ElaboratesFuel signature staticFuel context expression
          supply generated next)
        (plan : RawOriginRequestPlan operationalFuel expression outputDemand
          inputDemand) :
        SearchPlanCoverage elaboration operationalFuel
    | app
        {function argument : Expr}
        {generatedFunction generatedArgument : Generated}
        {afterFunction afterArgument : Supply}
        (functionCoverage : SearchPlanCoverage functionElaboration childFuel)
        (argumentCoverage : SearchPlanCoverage argumentElaboration childFuel) :
        SearchPlanCoverage
          (appElaboration functionElaboration argumentElaboration)
          (childFuel + 1)
    | tuple
        (itemsCoverage : SearchItemsCoverage itemsElaboration childFuel) :
        SearchPlanCoverage (tupleElaboration itemsElaboration) (childFuel + 1)
    | letE
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {supply : Supply}
        {value body : Expr} {generatedValue generatedBody : Generated}
        {afterValue next : Supply}
        {closure : PrincipalBlockClosure generatedValue}
        {valueElaboration : ElaboratesFuel signature staticFuel context value
          supply generatedValue afterValue}
        {bodyElaboration : ElaboratesFuel signature staticFuel
          ((context.applyFree closure.substitution).generalize closure.target ::
            context.applyFree closure.substitution)
          body
          (afterValue.join
            (context.applyFree closure.substitution).initialSupply)
          generatedBody next}
        (absorbing : closure.Absorbing)
        (valueCoverage : SearchPlanCoverage valueElaboration childFuel)
        (bodyCoverage : SearchPlanCoverage bodyElaboration childFuel) :
        SearchPlanCoverage
          (letElaboration valueElaboration closure absorbing bodyElaboration)
          (childFuel + 1)
    | ctor
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {supply next : Supply} {generated : Generated}
        {constructor : DataCtor} {arguments : List Expr} {scheme : Scheme}
        {argumentsElaboration : CallElaboratesUsing
          (ElaboratesFuel signature staticFuel) context
          ⟨(scheme.instantiate supply).1, [], []⟩ arguments
          (scheme.instantiate supply).2 generated next}
        (lookup : signature.base.lookupDataConstructor constructor = some scheme)
        (arity : arguments.length = scheme.callArity)
        (closed : scheme.Closed)
        (argumentsCoverage : SearchCallCoverage argumentsElaboration childFuel) :
        SearchPlanCoverage
          (ctorElaboration lookup arity closed argumentsElaboration)
          (childFuel + 1)
    | prim
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {supply next : Supply} {generated : Generated}
        {operation : PrimOp} {arguments : List Expr} {scheme : Scheme}
        {argumentsElaboration : CallElaboratesUsing
          (ElaboratesFuel signature staticFuel) context
          ⟨(scheme.instantiate supply).1, [], []⟩ arguments
          (scheme.instantiate supply).2 generated next}
        (lookup : signature.base.lookupPrimitive operation = some scheme)
        (arity : arguments.length = scheme.callArity)
        (closed : scheme.Closed)
        (argumentsCoverage : SearchCallCoverage argumentsElaboration childFuel) :
        SearchPlanCoverage
          (primElaboration lookup arity closed argumentsElaboration)
          (childFuel + 1)
    | ifE
        (argumentsCoverage : SearchCallCoverage argumentsElaboration childFuel) :
        SearchPlanCoverage (ifElaboration argumentsElaboration) (childFuel + 1)
    | matchAll
        (components : MatchAllElaboratesUsing
          (ElaboratesFuel signature staticFuel) signature context
          targetExpression matcherExpression pattern bodyExpression supply
          (Generated.fromMatchAll generatedTarget generatedPattern
            generatedMatcher generatedBody) next)
        (plan : RawOriginMatchAllPlan (matchAllElaboration components)
          childFuel bindingIndex
          resultIndex sourceTargets targetInput matcherInput bodyInput) :
        SearchPlanCoverage (matchAllElaboration components) (childFuel + 1)
    | matchFirst
        (plan : RawOriginMatchFirstPlan elaboration childFuel bindingIndex
          resultIndex sourceTargets targetInput matcherInput fallbackInput) :
        SearchPlanCoverage elaboration (childFuel + 1)

  /-- Coverage aligned with the exact left-to-right tuple elaboration. -/
  inductive SearchItemsCoverage :
      {signature : FrozenSignature} → {staticFuel : Nat} →
      {context : Context} → {expressions : List Expr} → {supply : Supply} →
      {generated : GeneratedItems} → {next : Supply} →
      ItemsElaborateUsing (ElaboratesFuel signature staticFuel) context
        expressions supply generated next → Nat → Type where
    | nil : SearchItemsCoverage ItemsElaborateUsing.nil operationalFuel
    | cons
        (headCoverage : SearchPlanCoverage headElaboration operationalFuel)
        (tailCoverage : SearchItemsCoverage tailElaboration operationalFuel) :
        SearchItemsCoverage
          (ItemsElaborateUsing.cons headElaboration tailElaboration)
          operationalFuel

  /-- Coverage aligned with the exact normalized curried-call spine used by
  constructors, primitives, and `ifE`.  Primitive `map` is covered here as
  the two-child `.prim .map` call rather than by a fixture-specific rule. -/
  inductive SearchCallCoverage :
      {signature : FrozenSignature} → {staticFuel : Nat} →
      {context : Context} → {accumulated : Generated} →
      {arguments : List Expr} → {supply : Supply} →
      {generated : Generated} → {next : Supply} →
      CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
        accumulated arguments supply generated next → Nat → Type where
    | nil : SearchCallCoverage CallElaboratesUsing.nil operationalFuel
    | cons
        (headCoverage : SearchPlanCoverage headElaboration operationalFuel)
        (tailCoverage : SearchCallCoverage tailElaboration operationalFuel) :
        SearchCallCoverage
          (CallElaboratesUsing.cons headElaboration tailElaboration)
          operationalFuel

end

mutual

  /-- One statically retained matching occurrence in a covered expression.
  There is intentionally no constructor for `.raw`: a raw plan cannot hide a
  matching root.  Dynamic reachability and the concrete issued task are added
  by `IssuedAtOccurrence`, rather than being guessed by this syntax path. -/
  inductive SearchOccurrence :
      {signature : FrozenSignature} → {staticFuel operationalFuel : Nat} →
      {context : Context} → {expression : Expr} → {supply : Supply} →
      {generated : Generated} → {next : Supply} →
      {elaboration : ElaboratesFuel signature staticFuel context expression
        supply generated next} →
      SearchPlanCoverage elaboration operationalFuel → Type where
    | matchAll : SearchOccurrence (.matchAll components plan)
    | matchFirst : SearchOccurrence (.matchFirst plan)
    | appFunction
        (occurrence : SearchOccurrence functionCoverage) :
        SearchOccurrence (.app functionCoverage argumentCoverage)
    | appArgument
        (occurrence : SearchOccurrence argumentCoverage) :
        SearchOccurrence (.app functionCoverage argumentCoverage)
    | tuple
        (occurrence : SearchItemsOccurrence itemsCoverage) :
        SearchOccurrence (.tuple itemsCoverage)
    | letValue
        (occurrence : SearchOccurrence valueCoverage) :
        SearchOccurrence (.letE absorbing valueCoverage bodyCoverage)
    | letBody
        (occurrence : SearchOccurrence bodyCoverage) :
        SearchOccurrence (.letE absorbing valueCoverage bodyCoverage)
    | ctor
        (occurrence : SearchCallOccurrence argumentsCoverage) :
        SearchOccurrence (.ctor lookup arity closed argumentsCoverage)
    | prim
        (occurrence : SearchCallOccurrence argumentsCoverage) :
        SearchOccurrence (.prim lookup arity closed argumentsCoverage)
    | ifE
        (occurrence : SearchCallOccurrence argumentsCoverage) :
        SearchOccurrence (.ifE argumentsCoverage)

  inductive SearchItemsOccurrence :
      {signature : FrozenSignature} → {staticFuel operationalFuel : Nat} →
      {context : Context} → {expressions : List Expr} → {supply : Supply} →
      {generated : GeneratedItems} → {next : Supply} →
      {elaboration : ItemsElaborateUsing
        (ElaboratesFuel signature staticFuel) context expressions supply
        generated next} →
      SearchItemsCoverage elaboration operationalFuel → Type where
    | head
        (occurrence : SearchOccurrence headCoverage) :
        SearchItemsOccurrence (.cons headCoverage tailCoverage)
    | tail
        (occurrence : SearchItemsOccurrence tailCoverage) :
        SearchItemsOccurrence (.cons headCoverage tailCoverage)

  inductive SearchCallOccurrence :
      {signature : FrozenSignature} → {staticFuel operationalFuel : Nat} →
      {context : Context} → {accumulated : Generated} →
      {arguments : List Expr} → {supply : Supply} →
      {generated : Generated} → {next : Supply} →
      {elaboration : CallElaboratesUsing
        (ElaboratesFuel signature staticFuel) context accumulated arguments
        supply generated next} →
      SearchCallCoverage elaboration operationalFuel → Type where
    | head
        (occurrence : SearchOccurrence headCoverage) :
        SearchCallOccurrence (.cons headCoverage tailCoverage)
    | tail
        (occurrence : SearchCallOccurrence tailCoverage) :
        SearchCallOccurrence (.cons headCoverage tailCoverage)

end

/-- Dynamic matchAll leaf at one statically tracked occurrence.  The initial
state is not an input: it is reconstructed from the retained plan and exact
component elaboration by `RawOriginMatchAllPlan.issuedTask`. -/
structure MatchAllIssuedAtOccurrence
    {signature : FrozenSignature} {staticFuel childFuel bindingIndex
      resultIndex : Nat} {context : Context} {sourceTargets : List Ty}
    {targetExpression matcherExpression bodyExpression : Expr}
    {pattern : Pattern} {supply next : Supply}
    {generatedTarget generatedMatcher generatedBody : Generated}
    {generatedPattern : GeneratedPattern}
    {targetInput matcherInput bodyInput : OriginEnvironmentDemand}
    (components : MatchAllElaboratesUsing
      (ElaboratesFuel signature staticFuel) signature context targetExpression
      matcherExpression pattern bodyExpression supply
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody) next)
    (plan : RawOriginMatchAllPlan (matchAllElaboration components) childFuel
      bindingIndex resultIndex sourceTargets targetInput matcherInput bodyInput)
    (solution : Subst) (environment : ValueEnvironment)
    (targetValue matcherValue : Value)
    (resultDemand : OriginEnvironmentDemand) : Prop where
  compatible : SignatureCompatible signature.base
  semantic : (Generated.fromMatchAll generatedTarget generatedPattern
    generatedMatcher generatedBody).SemanticSolution solution
  outerSafe : FuelEnvironmentSafe bindingIndex environment
    (Ty.applyList solution sourceTargets)
  targetSuccess : evalFuel childFuel environment targetExpression = .ok targetValue
  matcherSuccess : evalFuel childFuel environment matcherExpression = .ok matcherValue
  demandCovered : OriginAnswerDemandCoveredByFuel bindingIndex resultDemand
    (Ty.applyList solution generatedPattern.bindings)

/-- A tracked matchAll occurrence reconstructs its two-index search
certificate from the retained raw plan.  In particular, initial-state typing
is obtained from `issuedTask`; it is not a free input to this theorem. -/
theorem MatchAllIssuedAtOccurrence.toSearchCertificate
    {signature : FrozenSignature} {staticFuel childFuel bindingIndex
      resultIndex : Nat} {context : Context} {sourceTargets : List Ty}
    {targetExpression matcherExpression bodyExpression : Expr}
    {pattern : Pattern} {supply next : Supply}
    {generatedTarget generatedMatcher generatedBody : Generated}
    {generatedPattern : GeneratedPattern}
    {targetInput matcherInput bodyInput : OriginEnvironmentDemand}
    {components : MatchAllElaboratesUsing
      (ElaboratesFuel signature staticFuel) signature context targetExpression
      matcherExpression pattern bodyExpression supply
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody) next}
    {plan : RawOriginMatchAllPlan (matchAllElaboration components) childFuel
      bindingIndex resultIndex sourceTargets targetInput matcherInput bodyInput}
    {solution : Subst} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    {resultDemand : OriginEnvironmentDemand}
    (issued : MatchAllIssuedAtOccurrence components plan solution environment
      targetValue matcherValue resultDemand) :
    twoIndexBoundedDfsSearchCertificateFamily
      ⟨environment, pattern, plan.patternMNodeFree, matcherValue,
        targetValue⟩
      (Ty.applyList solution generatedPattern.bindings) childFuel childFuel
      resultDemand := by
  have rawIssued := plan.issuedTask components issued.compatible issued.semantic
    issued.outerSafe issued.targetSuccess issued.matcherSuccess
  exact TwoIndexBoundedDfsSearchCertificate.ofEvaluatedInitialState
    rawIssued.patternMNodeFree rawIssued.initialTyped issued.targetSuccess
    issued.matcherSuccess issued.demandCovered

mutual

  /-- Dynamic evidence that evaluation reached one exact statically tracked
  occurrence.  This first fragment deliberately has only a `matchAll` leaf.
  The remaining constructors merely retain the call-by-value success prefix
  needed to reach a child occurrence. -/
  inductive IssuedAtOccurrence :
      {signature : FrozenSignature} → {staticFuel operationalFuel : Nat} →
      {context : Context} → {expression : Expr} → {supply : Supply} →
      {generated : Generated} → {next : Supply} →
      {elaboration : ElaboratesFuel signature staticFuel context expression
        supply generated next} →
      {coverage : SearchPlanCoverage elaboration operationalFuel} →
      SearchOccurrence coverage →
      (solution : Subst) → (environment : ValueEnvironment) →
      (task : BoundedDfsMatchingSearchTask) → (answerTypes : List Ty) →
      (callbackFuel searchFuel : Nat) →
      (resultDemand : OriginEnvironmentDemand) → Prop where
    | matchAll
        {signature : FrozenSignature} {staticFuel childFuel bindingIndex
          resultIndex : Nat} {context : Context} {sourceTargets : List Ty}
        {targetExpression matcherExpression bodyExpression : Expr}
        {pattern : Pattern} {supply next : Supply}
        {generatedTarget generatedMatcher generatedBody : Generated}
        {generatedPattern : GeneratedPattern}
        {targetInput matcherInput bodyInput : OriginEnvironmentDemand}
        {components : MatchAllElaboratesUsing
          (ElaboratesFuel signature staticFuel) signature context
          targetExpression matcherExpression pattern bodyExpression supply
          (Generated.fromMatchAll generatedTarget generatedPattern
            generatedMatcher generatedBody) next}
        {plan : RawOriginMatchAllPlan (matchAllElaboration components)
          childFuel bindingIndex resultIndex sourceTargets targetInput
          matcherInput bodyInput}
        {solution : Subst} {environment : ValueEnvironment}
        {targetValue matcherValue : Value}
        {resultDemand : OriginEnvironmentDemand}
        (issued : MatchAllIssuedAtOccurrence components plan solution
          environment targetValue matcherValue resultDemand) :
        IssuedAtOccurrence (.matchAll (components := components) (plan := plan))
          solution environment
          ⟨environment, pattern, plan.patternMNodeFree, matcherValue,
            targetValue⟩
          (Ty.applyList solution generatedPattern.bindings) childFuel childFuel
          resultDemand
    | appFunction
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {functionExpression argumentExpression : Expr}
        {supply afterFunction afterArgument : Supply}
        {generatedFunction generatedArgument : Generated}
        {functionElaboration : ElaboratesFuel signature staticFuel context
          functionExpression supply generatedFunction afterFunction}
        {argumentElaboration : ElaboratesFuel signature staticFuel context
          argumentExpression afterFunction generatedArgument afterArgument}
        {functionCoverage : SearchPlanCoverage functionElaboration childFuel}
        {argumentCoverage : SearchPlanCoverage argumentElaboration childFuel}
        {occurrence : SearchOccurrence functionCoverage}
        (issued : IssuedAtOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtOccurrence
          (.appFunction (argumentCoverage := argumentCoverage) occurrence)
          solution environment task
          answerTypes callbackFuel searchFuel resultDemand
    | appArgument
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {functionExpression argumentExpression : Expr}
        {supply afterFunction afterArgument : Supply}
        {generatedFunction generatedArgument : Generated}
        {functionElaboration : ElaboratesFuel signature staticFuel context
          functionExpression supply generatedFunction afterFunction}
        {argumentElaboration : ElaboratesFuel signature staticFuel context
          argumentExpression afterFunction generatedArgument afterArgument}
        {functionCoverage : SearchPlanCoverage functionElaboration childFuel}
        {argumentCoverage : SearchPlanCoverage argumentElaboration childFuel}
        {occurrence : SearchOccurrence argumentCoverage}
        (functionSuccess :
          evalFuel childFuel environment functionExpression = .ok functionValue)
        (issued : IssuedAtOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtOccurrence
          (.appArgument (functionCoverage := functionCoverage) occurrence)
          solution environment task
          answerTypes callbackFuel searchFuel resultDemand
    | tuple
        {itemsElaboration : ItemsElaborateUsing
          (ElaboratesFuel signature staticFuel) context items supply generated next}
        {itemsCoverage : SearchItemsCoverage itemsElaboration childFuel}
        {occurrence : SearchItemsOccurrence itemsCoverage}
        (issued : IssuedAtItemsOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtOccurrence (.tuple occurrence) solution environment task
          answerTypes callbackFuel searchFuel resultDemand
    | ctor
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {supply next : Supply} {generated : Generated}
        {constructor : DataCtor} {arguments : List Expr} {scheme : Scheme}
        {argumentsElaboration : CallElaboratesUsing
          (ElaboratesFuel signature staticFuel) context
          ⟨(scheme.instantiate supply).1, [], []⟩ arguments
          (scheme.instantiate supply).2 generated next}
        {lookup : signature.base.lookupDataConstructor constructor = some scheme}
        {arity : arguments.length = scheme.callArity}
        {closed : scheme.Closed}
        {argumentsCoverage : SearchCallCoverage argumentsElaboration childFuel}
        {occurrence : SearchCallOccurrence argumentsCoverage}
        (issued : IssuedAtCallOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtOccurrence
          (.ctor (lookup := lookup) (arity := arity) (closed := closed)
            occurrence)
          solution environment task
          answerTypes callbackFuel searchFuel resultDemand
    | prim
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {supply next : Supply} {generated : Generated}
        {operation : PrimOp} {arguments : List Expr} {scheme : Scheme}
        {argumentsElaboration : CallElaboratesUsing
          (ElaboratesFuel signature staticFuel) context
          ⟨(scheme.instantiate supply).1, [], []⟩ arguments
          (scheme.instantiate supply).2 generated next}
        {lookup : signature.base.lookupPrimitive operation = some scheme}
        {arity : arguments.length = scheme.callArity}
        {closed : scheme.Closed}
        {argumentsCoverage : SearchCallCoverage argumentsElaboration childFuel}
        {occurrence : SearchCallOccurrence argumentsCoverage}
        (issued : IssuedAtCallOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtOccurrence
          (.prim (lookup := lookup) (arity := arity) (closed := closed)
            occurrence)
          solution environment task
          answerTypes callbackFuel searchFuel resultDemand
    | ifCondition
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {conditionExpression thenExpression
          elseExpression : Expr} {supply afterCondition afterThen afterElse : Supply}
        {generatedCondition generatedThen generatedElse : Generated}
        {conditionElaboration : ElaboratesFuel signature staticFuel context
          conditionExpression (conditionalScheme.instantiate supply).2
          generatedCondition afterCondition}
        {thenElaboration : ElaboratesFuel signature staticFuel context
          thenExpression (afterCondition.nextTy 2) generatedThen afterThen}
        {elseElaboration : ElaboratesFuel signature staticFuel context
          elseExpression (afterThen.nextTy 2) generatedElse afterElse}
        {conditionCoverage : SearchPlanCoverage conditionElaboration childFuel}
        {thenCoverage : SearchPlanCoverage thenElaboration childFuel}
        {elseCoverage : SearchPlanCoverage elseElaboration childFuel}
        {occurrence : SearchOccurrence conditionCoverage}
        (issued : IssuedAtOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtOccurrence
          (.ifE (.head (tailCoverage := .cons thenCoverage
            (.cons elseCoverage .nil)) occurrence)) solution environment task
          answerTypes callbackFuel searchFuel resultDemand
    | ifThen
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {conditionExpression thenExpression
          elseExpression : Expr} {supply afterCondition afterThen afterElse : Supply}
        {generatedCondition generatedThen generatedElse : Generated}
        {conditionElaboration : ElaboratesFuel signature staticFuel context
          conditionExpression (conditionalScheme.instantiate supply).2
          generatedCondition afterCondition}
        {thenElaboration : ElaboratesFuel signature staticFuel context
          thenExpression (afterCondition.nextTy 2) generatedThen afterThen}
        {elseElaboration : ElaboratesFuel signature staticFuel context
          elseExpression (afterThen.nextTy 2) generatedElse afterElse}
        {conditionCoverage : SearchPlanCoverage conditionElaboration childFuel}
        {thenCoverage : SearchPlanCoverage thenElaboration childFuel}
        {elseCoverage : SearchPlanCoverage elseElaboration childFuel}
        {occurrence : SearchOccurrence thenCoverage}
        (conditionSuccess : evalFuel childFuel environment conditionExpression =
          .ok (Value.boolValue true))
        (issued : IssuedAtOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtOccurrence
          (.ifE (.tail (headCoverage := conditionCoverage)
            (.head (tailCoverage := .cons elseCoverage .nil) occurrence))) solution
          environment task answerTypes callbackFuel searchFuel resultDemand
    | ifElse
        {signature : FrozenSignature} {staticFuel childFuel : Nat}
        {context : Context} {conditionExpression thenExpression
          elseExpression : Expr} {supply afterCondition afterThen afterElse : Supply}
        {generatedCondition generatedThen generatedElse : Generated}
        {conditionElaboration : ElaboratesFuel signature staticFuel context
          conditionExpression (conditionalScheme.instantiate supply).2
          generatedCondition afterCondition}
        {thenElaboration : ElaboratesFuel signature staticFuel context
          thenExpression (afterCondition.nextTy 2) generatedThen afterThen}
        {elseElaboration : ElaboratesFuel signature staticFuel context
          elseExpression (afterThen.nextTy 2) generatedElse afterElse}
        {conditionCoverage : SearchPlanCoverage conditionElaboration childFuel}
        {thenCoverage : SearchPlanCoverage thenElaboration childFuel}
        {elseCoverage : SearchPlanCoverage elseElaboration childFuel}
        {occurrence : SearchOccurrence elseCoverage}
        (conditionSuccess : evalFuel childFuel environment conditionExpression =
          .ok (Value.boolValue false))
        (issued : IssuedAtOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtOccurrence
          (.ifE (.tail (headCoverage := conditionCoverage)
            (.tail (headCoverage := thenCoverage)
              (.head (tailCoverage := .nil) occurrence)))) solution
          environment task answerTypes callbackFuel searchFuel resultDemand

  /-- Dynamic left-to-right reachability inside a tuple item list. -/
  inductive IssuedAtItemsOccurrence :
      {signature : FrozenSignature} → {staticFuel operationalFuel : Nat} →
      {context : Context} → {expressions : List Expr} → {supply : Supply} →
      {generated : GeneratedItems} → {next : Supply} →
      {elaboration : ItemsElaborateUsing
        (ElaboratesFuel signature staticFuel) context expressions supply
        generated next} →
      {coverage : SearchItemsCoverage elaboration operationalFuel} →
      SearchItemsOccurrence coverage →
      (solution : Subst) → (environment : ValueEnvironment) →
      (task : BoundedDfsMatchingSearchTask) → (answerTypes : List Ty) →
      (callbackFuel searchFuel : Nat) →
      (resultDemand : OriginEnvironmentDemand) → Prop where
    | head
        {signature : FrozenSignature} {staticFuel operationalFuel : Nat}
        {context : Context} {headExpression : Expr}
        {tailExpressions : List Expr} {supply afterHead next : Supply}
        {generatedHead : Generated} {generatedTail : GeneratedItems}
        {headElaboration : ElaboratesFuel signature staticFuel context
          headExpression supply generatedHead afterHead}
        {tailElaboration : ItemsElaborateUsing
          (ElaboratesFuel signature staticFuel) context tailExpressions
          afterHead generatedTail next}
        {headCoverage : SearchPlanCoverage headElaboration operationalFuel}
        {tailCoverage : SearchItemsCoverage tailElaboration operationalFuel}
        {occurrence : SearchOccurrence headCoverage}
        (issued : IssuedAtOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtItemsOccurrence
          (.head (tailCoverage := tailCoverage) occurrence) solution environment task
          answerTypes callbackFuel searchFuel resultDemand
    | tail
        {signature : FrozenSignature} {staticFuel operationalFuel : Nat}
        {context : Context} {headExpression : Expr}
        {tailExpressions : List Expr} {supply afterHead next : Supply}
        {generatedHead : Generated} {generatedTail : GeneratedItems}
        {headElaboration : ElaboratesFuel signature staticFuel context
          headExpression supply generatedHead afterHead}
        {tailElaboration : ItemsElaborateUsing
          (ElaboratesFuel signature staticFuel) context tailExpressions
          afterHead generatedTail next}
        {headCoverage : SearchPlanCoverage headElaboration operationalFuel}
        {tailCoverage : SearchItemsCoverage tailElaboration operationalFuel}
        {occurrence : SearchItemsOccurrence tailCoverage}
        (headSuccess :
          evalFuel operationalFuel environment headExpression = .ok headValue)
        (issued : IssuedAtItemsOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtItemsOccurrence
          (.tail (headCoverage := headCoverage) occurrence) solution environment task
          answerTypes callbackFuel searchFuel resultDemand

  /-- Dynamic left-to-right reachability inside constructor and primitive
  argument spines. -/
  inductive IssuedAtCallOccurrence :
      {signature : FrozenSignature} → {staticFuel operationalFuel : Nat} →
      {context : Context} → {accumulated : Generated} →
      {arguments : List Expr} → {supply : Supply} →
      {generated : Generated} → {next : Supply} →
      {elaboration : CallElaboratesUsing
        (ElaboratesFuel signature staticFuel) context accumulated arguments
        supply generated next} →
      {coverage : SearchCallCoverage elaboration operationalFuel} →
      SearchCallOccurrence coverage →
      (solution : Subst) → (environment : ValueEnvironment) →
      (task : BoundedDfsMatchingSearchTask) → (answerTypes : List Ty) →
      (callbackFuel searchFuel : Nat) →
      (resultDemand : OriginEnvironmentDemand) → Prop where
    | head
        {signature : FrozenSignature} {staticFuel operationalFuel : Nat}
        {context : Context} {accumulated : Generated}
        {headExpression : Expr} {tailExpressions : List Expr}
        {supply afterHead next : Supply} {generatedHead generated : Generated}
        {headElaboration : ElaboratesFuel signature staticFuel context
          headExpression supply generatedHead afterHead}
        {tailElaboration : CallElaboratesUsing
          (ElaboratesFuel signature staticFuel) context
          (Generated.fromApp accumulated generatedHead
            (.var ⟨afterHead.ty⟩) (.var ⟨afterHead.ty + 1⟩))
          tailExpressions (afterHead.nextTy 2) generated next}
        {headCoverage : SearchPlanCoverage headElaboration operationalFuel}
        {tailCoverage : SearchCallCoverage tailElaboration operationalFuel}
        {occurrence : SearchOccurrence headCoverage}
        (issued : IssuedAtOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtCallOccurrence
          (.head (tailCoverage := tailCoverage) occurrence) solution environment task
          answerTypes callbackFuel searchFuel resultDemand
    | tail
        {signature : FrozenSignature} {staticFuel operationalFuel : Nat}
        {context : Context} {accumulated : Generated}
        {headExpression : Expr} {tailExpressions : List Expr}
        {supply afterHead next : Supply} {generatedHead generated : Generated}
        {headElaboration : ElaboratesFuel signature staticFuel context
          headExpression supply generatedHead afterHead}
        {tailElaboration : CallElaboratesUsing
          (ElaboratesFuel signature staticFuel) context
          (Generated.fromApp accumulated generatedHead
            (.var ⟨afterHead.ty⟩) (.var ⟨afterHead.ty + 1⟩))
          tailExpressions (afterHead.nextTy 2) generated next}
        {headCoverage : SearchPlanCoverage headElaboration operationalFuel}
        {tailCoverage : SearchCallCoverage tailElaboration operationalFuel}
        {occurrence : SearchCallOccurrence tailCoverage}
        (headSuccess :
          evalFuel operationalFuel environment headExpression = .ok headValue)
        (issued : IssuedAtCallOccurrence occurrence solution environment task
          answerTypes callbackFuel searchFuel resultDemand) :
        IssuedAtCallOccurrence
          (.tail (headCoverage := headCoverage) occurrence) solution environment task
          answerTypes callbackFuel searchFuel resultDemand

end

/-- Forget only the dynamic lifting path and discharge the certificate at its
retained `matchAll` leaf.  Mutual induction over item and call spines does not
introduce any new semantic or initial-state premise. -/
theorem IssuedAtOccurrence.toSearchCertificate
    (issued : IssuedAtOccurrence occurrence solution environment task
      answerTypes callbackFuel searchFuel resultDemand) :
    twoIndexBoundedDfsSearchCertificateFamily task answerTypes callbackFuel
      searchFuel resultDemand := by
  apply IssuedAtOccurrence.rec
    (motive_1 := fun _ _ _ task answerTypes callbackFuel searchFuel
      resultDemand _ =>
        twoIndexBoundedDfsSearchCertificateFamily task answerTypes callbackFuel
          searchFuel resultDemand)
    (motive_2 := fun _ _ _ task answerTypes callbackFuel searchFuel
      resultDemand _ =>
        twoIndexBoundedDfsSearchCertificateFamily task answerTypes callbackFuel
          searchFuel resultDemand)
    (motive_3 := fun _ _ _ task answerTypes callbackFuel searchFuel
      resultDemand _ =>
        twoIndexBoundedDfsSearchCertificateFamily task answerTypes callbackFuel
          searchFuel resultDemand)
  · exact fun leaf => leaf.toSearchCertificate
  all_goals intros
  all_goals assumption

/-- Coverage policy paired with the unchanged principal request producer.
The coverage is required for the same public request and every exact M4
elaboration of the principal expression; no independent syntax tree is an
input. -/
structure TrackedPrincipalOriginRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Type where
  base : PrincipalOriginRequestProducer derivation runtimeContext
  coverage : ∀ (operationalFuel : Nat) (outputDemand : OriginDemand)
      {target : Ty},
    IsInstance principal target →
      OriginDemandApplicable outputDemand target →
        ∀ {staticFuel supply generated next},
          (sourceElaboration : ElaboratesFuel signature staticFuel context
            expression supply generated next) →
          Nonempty (SearchPlanCoverage sourceElaboration operationalFuel)

/-- Tracked runtime certificate data.  Evaluation continues to use `base`;
the second field is retained solely for search-origin completeness. -/
structure TrackedPrincipalOriginCertificateData
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Type where
  base : PrincipalOriginCertificateData derivation runtimeContext
  trackedRequests : TrackedPrincipalOriginRequestProducer derivation
    runtimeContext
  requests_eq : trackedRequests.base = base.requests

def Certificate : RuntimeCertificateFamily :=
  fun derivation runtimeContext =>
    Nonempty (TrackedPrincipalOriginCertificateData derivation runtimeContext)

def DerivationTrackedRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty) : Prop :=
  Nonempty (TrackedPrincipalOriginRequestProducer derivation runtimeContext)

/-- Assemble tracked certificate data for the exact derivation and runtime
context presented by principal state erasure. -/
theorem certificate_of_trackedRequestProducer
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    {derivation : M4.PrincipalTypingDerivation signature context expression
      principal}
    {runtimeContext : List Ty}
    (signatureReady : RuntimeSignatureReady signature)
    (contextRealization : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (producer : DerivationTrackedRequestProducer derivation runtimeContext) :
    Certificate derivation runtimeContext := by
  rcases producer with ⟨trackedRequests⟩
  exact ⟨{
    base := {
      closureSemantic :=
        TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
          derivation.closure
      contextCompatible := contextRealization
      signatureCompatible := signatureReady.2
      requests := trackedRequests.base }
    trackedRequests := trackedRequests
    requests_eq := rfl }⟩

theorem principalStateErasure_of_trackedRequestProducers
    (produce : ∀ {signature context expression principal}
      (derivation : M4.PrincipalTypingDerivation signature context expression
        principal)
      (runtimeContext : List Ty),
      RuntimeSignatureReady signature →
        scope derivation →
          MonomorphicRuntimeContextRelation derivation runtimeContext →
            DerivationTrackedRequestProducer derivation runtimeContext) :
    PrincipalStateErasure scope Certificate
      MonomorphicRuntimeContextRelation := by
  intro signature context expression principal derivation runtimeContext
    signatureReady inScope contextRealization
  exact certificate_of_trackedRequestProducer signatureReady contextRealization
    (produce derivation runtimeContext signatureReady inScope
      contextRealization)

/-- Forget only search coverage, preserving the exact underlying principal
certificate. -/
def baseCertificate : Certificate derivation runtimeContext →
    M5PrincipalOriginCertificate.Certificate derivation runtimeContext
  | ⟨tracked⟩ => ⟨tracked.base⟩

noncomputable def evaluationInputDemand :
    EvaluationInputDemandFamily Certificate originDemandSafetyRelations := by
  intro signature context expression principal derivation runtimeContext
    certificate operationalFuel outputDemand
  exact M5PrincipalOriginCertificate.evaluationInputDemand
    (baseCertificate certificate) operationalFuel outputDemand

/-- Typed evaluation is inherited from the unchanged base certificate. -/
theorem typedEvaluation :
    TypedEvaluation Certificate originDemandSafetyRelations
      evaluationInputDemand evalFuel := by
  intro signature context expression principal target derivation runtimeContext
    certificate instantiation operationalFuel outputDemand environment
    applicable environmentSafe
  have baseSafe : OriginEnvironmentSafe
      (M5PrincipalOriginCertificate.evaluationInputDemand
        (baseCertificate certificate) operationalFuel outputDemand)
      environment runtimeContext := by
    change OriginEnvironmentSafe
      (M5PrincipalOriginCertificate.evaluationInputDemand
        (baseCertificate certificate) operationalFuel outputDemand)
      environment runtimeContext at environmentSafe
    exact environmentSafe
  exact M5PrincipalOriginCertificate.typedEvaluation
    (baseCertificate certificate) instantiation operationalFuel outputDemand
    environment applicable baseSafe

/-- A raw-plan producer has canonical coverage: its retained plan itself
rules out hidden matching roots. -/
def ofRawPlanProducer
    (producer : PrincipalRawOriginPlanProducer derivation runtimeContext) :
    TrackedPrincipalOriginRequestProducer derivation runtimeContext where
  base := producer.toRequestProducer
  coverage := by
    intro operationalFuel outputDemand target instantiation applicable
      staticFuel supply generated next sourceElaboration
    exact ⟨.raw sourceElaboration
      (producer.plan operationalFuel outputDemand)⟩

end TypePM.Source.M5TrackedPrincipalOriginCertificate
