import TypePM.RecursiveTotalClosureSafety
import TypePM.Source.M4Paper1ListExactRegression
import TypePM.Source.M4Paper1ClosedMultisetExactRegression
import TypePM.Source.M4Paper1RecursiveClosureTypingBoundary

/-!
# Total value typing for the Paper 1 recursive matcher closures

This module extracts the runtime clause certificate from a solved public M4
principal derivation.  It types the concrete recursive closure value without
pretending that the older `ValueTyping` judgment supports matcher bodies.
Dynamic safety remains a separate `TotalEnvironmentSafe` premise.
-/

namespace TypePM.Source.MatcherTyping.M4Paper1RecursiveClosureTotalTyping

open TypePM.Runtime
open TypePM.Source.Paper1Programs
open M4Paper1RecursiveSafetyBoundaryRegression

private theorem fromFix_body_semantic
    {domain codomain : Ty} {body : Generated} {solution : Subst}
    (semantic : (Generated.fromFix domain codomain body).SemanticSolution
      solution) :
    body.SemanticSolution solution ∧
      Equation.Holds solution (.ty body.target codomain) := by
  constructor
  · constructor
    · intro equation membership
      exact semantic.1 equation (by simp [Generated.fromFix, membership])
    · intro obligation membership
      exact semantic.2 obligation (by simpa [Generated.fromFix] using membership)
  · exact semantic.1 _ (by simp [Generated.fromFix])

private theorem fromLam_body_semantic
    {domain : Ty} {body : Generated} {solution : Subst}
    (semantic : (Generated.fromLam domain body).SemanticSolution solution) :
    body.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by simpa [Generated.fromLam] using membership)
  · intro obligation membership
    exact semantic.2 obligation (by simpa [Generated.fromLam] using membership)

private theorem fromApp_semantic_parts
    {function argument : Generated} {domain target : Ty} {solution : Subst}
    (semantic : Generated.SemanticSolution
      (Generated.fromApp function argument domain target) solution) :
    function.SemanticSolution solution ∧
      argument.SemanticSolution solution ∧
      Equation.Holds solution (.ty function.target (.fn domain target)) ∧
      ∃ conversionClass, CheckConversion conversionClass
        (argument.target.apply solution) (domain.apply solution) := by
  constructor
  · constructor
    · intro equation membership
      exact semantic.1 equation (by simp [Generated.fromApp, membership])
    · intro obligation membership
      exact semantic.2 obligation (by simp [Generated.fromApp, membership])
  · constructor
    · constructor
      · intro equation membership
        exact semantic.1 equation (by simp [Generated.fromApp, membership])
      · intro obligation membership
        exact semantic.2 obligation (by simp [Generated.fromApp, membership])
    · constructor
      · exact semantic.1 _ (by simp [Generated.fromApp])
      · exact semantic.2 (⟨argument.target, domain⟩ : CheckObligation)
          (by simp [Generated.fromApp])

private theorem checkConversion_fromFunction_eq
    (conversion : CheckConversion conversionClass (.fn domain codomain) target) :
    target = .fn domain codomain := by
  cases conversion
  rfl

private theorem matcherLiteral_target_eq
    (elaboration : MatcherLiteralElaboratesUsing expressionRelation
      PPatElaborates DPatElaborates Paper1FrozenSignature.signature context
      clauses supply generated next) :
    generated.target = .matcher (.var ⟨supply.cap⟩) (.var ⟨supply.ty⟩) := by
  cases elaboration
  rfl

/-- Ground every still-polymorphic type and capability variable.  It is used
only to specialize the closed runtime fixture to the concrete `something`
argument; semantic solutions are stable under this postcomposition. -/
private def closedMatcherSpecialization : Subst :=
  Subst.compose (Subst.singleTy ⟨111⟩ .int)
    (Subst.singleCap ⟨27⟩ .any)

private theorem fixElaboration_parts
    {fuel : Nat} {context : Context} {body : Expr} {start next : Supply}
    {generated : Generated}
    (elaboration : FixElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      context (.fixE body) start generated next) :
    ∃ generatedBody,
      M4.ElaboratesFuel Paper1FrozenSignature.signature fuel
        (Fix.bodyContext (Fix.domain body start)
          (Fix.codomain body start) context)
        body (Fix.bodySupply body start) generatedBody next ∧
      generated = Generated.fromFix (Fix.domain body start)
        (Fix.codomain body start) generatedBody := by
  cases elaboration with
  | fixE direct bodyElaboration => exact ⟨_, bodyElaboration, rfl⟩

private theorem matcherElaboration_parts
    (elaboration : M4.ElaboratesFuel Paper1FrozenSignature.signature fuel
      context (.matcher clauses) supply generated next) :
    ∃ bodyFuel, MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature bodyFuel)
      PPatElaborates DPatElaborates Paper1FrozenSignature.signature context
      clauses supply generated next := by
  cases fuel with
  | zero => contradiction
  | succ bodyFuel =>
      exact ⟨bodyFuel, by simpa only [M4.ElaboratesFuel] using elaboration⟩

/-- Reusable extraction theorem for a matcher-root fix in a monomorphic
source/runtime context.  It transports the solved M4 body certificate into
the total recursive-closure value rule without adding a dynamic premise. -/
theorem matcherFixElaboration_totalValueTyping
    (elaboration : M4.ElaboratesFuel Paper1FrozenSignature.signature fuel
      sourceContext (.fixE (.matcher clauses)) start generated next)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution)
    (environmentTyped : TotalEnvironmentTyping environment runtimeContext) :
    TotalValueTyping
      (Value.recursiveClosure environment (.matcher clauses))
      (generated.target.apply solution) := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
      simp only [M4.ElaboratesFuel] at elaboration
      obtain ⟨generatedBody, bodyElaboration, generated_eq⟩ :=
        fixElaboration_parts elaboration
      cases fuel with
      | zero => simp [M4.ElaboratesFuel] at bodyElaboration
      | succ bodyFuel =>
          simp only [M4.ElaboratesFuel] at bodyElaboration
          rw [generated_eq] at semantic ⊢
          obtain ⟨bodySemantic, bodyEquation⟩ :=
            fromFix_body_semantic semantic
          have bodyContextCompatible : MonomorphicContextCompatible
              (Fix.bodyContext (Fix.domain (.matcher clauses) start)
                (Fix.codomain (.matcher clauses) start) sourceContext)
              ((Fix.domain (.matcher clauses) start).apply solution ::
                ((Ty.fn (Fix.domain (.matcher clauses) start)
                  (Fix.codomain (.matcher clauses) start)).apply solution) ::
                runtimeContext)
              solution := by
            simp only [Fix.bodyContext]
            exact .cons (.cons contextCompatible)
          have clausesTyped :=
            bodyElaboration.toTotalMatcherClausesTyping_of_m4Fuel
              totalRecursiveExpressionBridge bodySemantic
              bodyContextCompatible
          simp only [Generated.fromFix, Ty.apply]
          simp only [Equation.Holds] at bodyEquation
          apply TotalValueTyping.recursiveClosure environmentTyped
          simpa [Ty.apply, bodyEquation] using
            (TotalRecursiveClosureBodyTyping.solvedMatcher
              bodyElaboration bodySemantic bodyContextCompatible clausesTyped)

/-- A matcher-root fix also exposes safety of evaluating its body literal.
This evaluates only `.matcher clauses` to a closure; it does not run clause
dispatch or any arm body. -/
theorem matcherFixElaboration_literalEvaluationSafe
    (elaboration : M4.ElaboratesFuel Paper1FrozenSignature.signature fuel
      sourceContext (.fixE (.matcher clauses)) start generated next)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible
      sourceContext runtimeContext solution) :
    ∃ domain codomain,
      generated.target.apply solution = .fn domain codomain ∧
      TotalEnvironmentSafe (.matcher clauses) codomain
        (domain :: .fn domain codomain :: runtimeContext) := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
      simp only [M4.ElaboratesFuel] at elaboration
      obtain ⟨generatedBody, bodyElaboration, generated_eq⟩ :=
        fixElaboration_parts elaboration
      cases fuel with
      | zero => simp [M4.ElaboratesFuel] at bodyElaboration
      | succ bodyFuel =>
          simp only [M4.ElaboratesFuel] at bodyElaboration
          rw [generated_eq] at semantic ⊢
          obtain ⟨bodySemantic, bodyEquation⟩ :=
            fromFix_body_semantic semantic
          have bodyContextCompatible : MonomorphicContextCompatible
              (Fix.bodyContext (Fix.domain (.matcher clauses) start)
                (Fix.codomain (.matcher clauses) start) sourceContext)
              ((Fix.domain (.matcher clauses) start).apply solution ::
                ((Ty.fn (Fix.domain (.matcher clauses) start)
                  (Fix.codomain (.matcher clauses) start)).apply solution) ::
                runtimeContext)
              solution := by
            simp only [Fix.bodyContext]
            exact .cons (.cons contextCompatible)
          let domain := (Fix.domain (.matcher clauses) start).apply solution
          let codomain := (Fix.codomain (.matcher clauses) start).apply solution
          refine ⟨domain, codomain, by
            simp [Generated.fromFix, domain, codomain, Ty.apply], ?_⟩
          have literalSafe := totalEnvironmentSafe_solvedMatcher
            bodyElaboration bodySemantic bodyContextCompatible
          simp only [Equation.Holds] at bodyEquation
          have targetShape := congrArg (Ty.apply solution)
            (matcherLiteral_target_eq bodyElaboration)
          simp only [Ty.apply] at targetShape
          have preciseTarget_eq :
              (.matcher
                ((Cap.var ⟨(Fix.bodySupply (.matcher clauses) start).cap⟩).apply
                  solution.cap)
                ((Ty.var ⟨(Fix.bodySupply (.matcher clauses) start).ty⟩).apply
                  solution)) = codomain := by
            exact targetShape.symm.trans (by simpa [codomain] using bodyEquation)
          rw [preciseTarget_eq] at literalSafe
          simpa [domain, codomain, Ty.apply] using literalSafe

/-- Public principal wrapper for the literal-evaluation boundary of a closed
matcher-root fix. -/
theorem principalMatcherFix_literalEvaluationSafe
    (typing : M4.PrincipalTyping Paper1FrozenSignature.signature []
      (.fixE (.matcher clauses)) target) :
    ∃ domain codomain,
      target = .fn domain codomain ∧
      TotalEnvironmentSafe (.matcher clauses) codomain
        [domain, .fn domain codomain] := by
  rcases typing with ⟨derivation⟩
  rcases derivation.elaboration with ⟨fuel, fuelDerivation⟩
  let solution := derivation.closure.substitution
  have semantic : derivation.generated.SemanticSolution solution :=
    TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
      derivation.closure
  obtain ⟨domain, codomain, generatedTarget, literalSafe⟩ :=
    matcherFixElaboration_literalEvaluationSafe fuelDerivation semantic .nil
  refine ⟨domain, codomain, ?_, literalSafe⟩
  rw [derivation.target_eq]
  simpa [PrincipalBlockClosure.target, solution] using generatedTarget

/-- Any closed Paper-1 matcher-root fix with a public principal M4 derivation
types its concrete recursive closure in the proof-only total value layer. -/
theorem principalMatcherFix_totalValueTyping
    (typing : M4.PrincipalTyping Paper1FrozenSignature.signature []
      (.fixE (.matcher clauses)) target) :
    TotalValueTyping (Value.recursiveClosure [] (.matcher clauses)) target := by
  rcases typing with ⟨derivation⟩
  rcases derivation.elaboration with ⟨fuel, fuelDerivation⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at fuelDerivation
  | succ fuel =>
      simp only [M4.ElaboratesFuel] at fuelDerivation
      obtain ⟨generatedBody, bodyElaboration, generated_eq⟩ :=
        fixElaboration_parts fuelDerivation
      cases fuel with
      | zero => simp [M4.ElaboratesFuel] at bodyElaboration
      | succ bodyFuel =>
              simp only [M4.ElaboratesFuel] at bodyElaboration
              let solution := derivation.closure.substitution
              have outerSemantic :
                  (Generated.fromFix
                    (Fix.domain (.matcher clauses) (Context.initialSupply []))
                    (Fix.codomain (.matcher clauses) (Context.initialSupply []))
                    generatedBody).SemanticSolution solution := by
                rw [← generated_eq]
                exact TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
                  derivation.closure
              obtain ⟨bodySemantic, bodyEquation⟩ :=
                fromFix_body_semantic outerSemantic
              have compatible : MonomorphicContextCompatible
                  (Fix.bodyContext
                    (Fix.domain (.matcher clauses) (Context.initialSupply []))
                    (Fix.codomain (.matcher clauses) (Context.initialSupply []))
                    [])
                  [
                    (Fix.domain (.matcher clauses) (Context.initialSupply [])).apply
                      solution,
                    (Ty.fn
                      (Fix.domain (.matcher clauses) (Context.initialSupply []))
                      (Fix.codomain (.matcher clauses) (Context.initialSupply []))).apply
                      solution]
                  solution := by
                simp only [Fix.bodyContext]
                exact .cons (.cons .nil)
              have clausesTyped :=
                bodyElaboration.toTotalMatcherClausesTyping_of_m4Fuel
                  totalRecursiveExpressionBridge bodySemantic compatible
              have closureTyped : TotalValueTyping
                  (Value.recursiveClosure [] (.matcher clauses))
                  (.fn
                    ((Fix.domain (.matcher clauses)
                      (Context.initialSupply [])).apply solution)
                    ((Fix.codomain (.matcher clauses)
                      (Context.initialSupply [])).apply solution)) := by
                simp only [Equation.Holds] at bodyEquation
                apply TotalValueTyping.recursiveClosure .nil
                simpa [Ty.apply, bodyEquation] using
                  (TotalRecursiveClosureBodyTyping.solvedMatcher
                    bodyElaboration bodySemantic compatible clausesTyped)
              rw [derivation.target_eq]
              simpa [PrincipalBlockClosure.target, generated_eq,
                Generated.fromFix, Ty.apply, solution] using closureTyped

/-- The actual list matcher closure from the Paper 1 execution fixture has
the exact public type computed by `M4.infer`. -/
theorem listRecursiveClosure_totalValueTyping :
    TotalValueTyping listRecursiveClosure
      M4Paper1ListExactRegression.listMatcherType := by
  exact principalMatcherFix_totalValueTyping
    (M4.infer_success_principalTyping Paper1FrozenSignature.wellFormed
      M4Paper1ListExactRegression.infer_exact)

/-- Actual Paper-1 list matcher body: evaluating the literal constructs its
matcher closure at every fuel.  The existential types are exactly the domain
and codomain selected by the public principal M4 derivation.  No clause is
dispatched by this theorem. -/
theorem listMatcherBody_literalEvaluation_totalEnvironmentSafe :
    ∃ domain codomain,
      M4Paper1ListExactRegression.listMatcherType = .fn domain codomain ∧
      TotalEnvironmentSafe (.matcher listMatcherClauses) codomain
        [domain, .fn domain codomain] := by
  exact principalMatcherFix_literalEvaluationSafe
    (M4.infer_success_principalTyping Paper1FrozenSignature.wellFormed
      M4Paper1ListExactRegression.infer_exact)

/-- Extract literal-evaluation safety for the matcher-root fix under a
surrounding lambda.  This is the source shape of the closed Paper-1 multiset
constructor before its list-library argument is applied. -/
theorem principalAppliedLambdaMatcherFix_literalEvaluationSafe
    (typing : M4.PrincipalTyping Paper1FrozenSignature.signature []
      (.app (.lam (.fixE (.matcher clauses))) argument) target) :
    ∃ capturedType domain codomain,
      TotalEnvironmentSafe (.matcher clauses) codomain
        [domain, .fn domain codomain, capturedType] := by
  rcases typing with ⟨derivation⟩
  rcases derivation.elaboration with ⟨fuel, fuelDerivation⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at fuelDerivation
  | succ fuel =>
      simp only [M4.ElaboratesFuel] at fuelDerivation
      rcases fuelDerivation with
        ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
          functionElaboration, argumentElaboration, generated_eq, next_eq⟩
      cases fuel with
      | zero => simp [M4.ElaboratesFuel] at functionElaboration
      | succ childFuel =>
          have functionShape := functionElaboration
          simp only [M4.ElaboratesFuel] at functionShape
          rcases functionShape with
            ⟨generatedFix, fixElaboration, function_eq⟩
          let solution := derivation.closure.substitution
          have outerSemantic : Generated.SemanticSolution
              (Generated.fromApp generatedFunction generatedArgument
                (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
                solution := by
            rw [← generated_eq]
            exact TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
              derivation.closure
          obtain ⟨functionSemantic, argumentSemantic, functionEquation,
              argumentConversion⟩ := fromApp_semantic_parts outerSemantic
          have fixSemantic : generatedFix.SemanticSolution solution := by
            rw [function_eq] at functionSemantic
            exact fromLam_body_semantic functionSemantic
          let capturedType :=
            (Ty.var ⟨(Context.initialSupply []).ty⟩).apply solution
          obtain ⟨domain, codomain, generatedTarget, literalSafe⟩ :=
            matcherFixElaboration_literalEvaluationSafe fixElaboration
              fixSemantic (.cons .nil)
          exact ⟨capturedType, domain, codomain, by
            simpa [capturedType] using literalSafe⟩

/-- Actual Paper-1 multiset matcher body under its captured list constructor.
As with the list theorem, this is closure-generation safety only. -/
theorem multisetMatcherBody_literalEvaluation_totalEnvironmentSafe :
    ∃ capturedListType domain codomain,
      TotalEnvironmentSafe (.matcher multisetClauses) codomain
        [domain, .fn domain codomain, capturedListType] := by
  have principal := M4.infer_success_principalTyping
    Paper1FrozenSignature.wellFormed
    M4Paper1ClosedMultisetExactRegression.infer_exact
  apply principalAppliedLambdaMatcherFix_literalEvaluationSafe
    (argument := listMatcherDefinition)
  simpa [closedMultisetDefinition, multisetWithListArgument,
    multisetDefinition] using principal

/-- The two concrete recursive closures produced while evaluating the closed
Paper-1 multiset constructor are simultaneously typable.  Their exact solved
types are exposed existentially because the theorem's purpose is the runtime
environment invariant, not a second presentation of the public principal
type. -/
theorem paper1RecursiveClosures_totalValueTyping :
    ∃ listType multisetType,
      TotalValueTyping listRecursiveClosure listType ∧
      TotalValueTyping multisetRecursiveClosure multisetType := by
  have principal := M4.infer_success_principalTyping
    Paper1FrozenSignature.wellFormed
    M4Paper1ClosedMultisetExactRegression.infer_exact
  rcases principal with ⟨derivation⟩
  rcases derivation.elaboration with ⟨fuel, fuelDerivation⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at fuelDerivation
  | succ fuel =>
      simp only [M4.ElaboratesFuel] at fuelDerivation
      rcases fuelDerivation with
        ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
          functionElaboration, argumentElaboration, generated_eq, next_eq⟩
      cases fuel with
      | zero => simp [M4.ElaboratesFuel] at functionElaboration
      | succ childFuel =>
          have functionShape := functionElaboration
          simp only [M4.ElaboratesFuel] at functionShape
          rcases functionShape with
            ⟨generatedMultiset, multisetElaboration, function_eq⟩
          let solution := derivation.closure.substitution
          have outerSemantic : Generated.SemanticSolution
              (Generated.fromApp generatedFunction generatedArgument
                (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
                solution := by
            rw [← generated_eq]
            exact TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
              derivation.closure
          obtain ⟨functionSemantic, argumentSemantic, functionEquation,
              argumentConversion⟩ := fromApp_semantic_parts outerSemantic
          obtain ⟨conversionClass, argumentConversion⟩ := argumentConversion
          have multisetSemantic : generatedMultiset.SemanticSolution solution := by
            rw [function_eq] at functionSemantic
            exact fromLam_body_semantic functionSemantic
          have listTyped : TotalValueTyping listRecursiveClosure
              (generatedArgument.target.apply solution) := by
            exact matcherFixElaboration_totalValueTyping argumentElaboration
              argumentSemantic .nil .nil
          have multisetDomainEquality :
              (Ty.var ⟨0⟩).apply solution =
                (Ty.var ⟨afterArgument.ty⟩).apply solution := by
            simp only [Equation.Holds] at functionEquation
            rw [function_eq] at functionEquation
            simp only [Generated.fromLam, Ty.apply] at functionEquation
            exact Ty.fn.inj functionEquation |>.1
          have argumentDomainEquality :
              generatedArgument.target.apply solution =
                (Ty.var ⟨afterArgument.ty⟩).apply solution := by
            have argumentShape := argumentElaboration
            simp only [M4.ElaboratesFuel] at argumentShape
            obtain ⟨argumentBody, argumentBodyElaboration,
              argumentGenerated_eq⟩ := fixElaboration_parts argumentShape
            have convertedFunction : CheckConversion conversionClass
                (.fn
                  ((Fix.domain (.matcher listMatcherClauses) afterFunction).apply
                    solution)
                  ((Fix.codomain (.matcher listMatcherClauses) afterFunction).apply
                    solution))
                ((Ty.var ⟨afterArgument.ty⟩).apply solution) := by
              simpa [argumentGenerated_eq, Generated.fromFix, Ty.apply] using
                argumentConversion
            have equality := checkConversion_fromFunction_eq convertedFunction
            rw [argumentGenerated_eq]
            simpa [Generated.fromFix, Ty.apply] using equality.symm
          have listAtCapturedType : TotalValueTyping listRecursiveClosure
              ((Ty.var ⟨0⟩).apply solution) := by
            rw [multisetDomainEquality, ← argumentDomainEquality]
            exact listTyped
          have multisetTyped : TotalValueTyping multisetRecursiveClosure
              (generatedMultiset.target.apply solution) := by
            exact matcherFixElaboration_totalValueTyping multisetElaboration
              multisetSemantic (.cons .nil) (.cons listAtCapturedType .nil)
          exact ⟨_, _, listTyped, multisetTyped⟩

/-- Consequently the exact three-value environment captured by the closed
multiset matcher has an unconditional total-environment typing.  The first
entry is given its ordinary matcher type here; a clause-aligned slot type is
the additional specialization needed by the dispatch-safety bridge. -/
theorem closedMultisetMatcherEnvironment_totalTyping :
    ∃ elementMatcherType multisetType listType,
      TotalEnvironmentTyping closedMultisetMatcherEnvironment
        [elementMatcherType, multisetType, listType] := by
  obtain ⟨listType, multisetType, listTyped, multisetTyped⟩ :=
    paper1RecursiveClosures_totalValueTyping
  exact ⟨.matcher .any .int, multisetType, listType,
    .cons (.ordinary (.something .int))
      (.cons multisetTyped (.cons listTyped .nil))⟩

/-- The concrete matcher cursor produced by `multiset something` is typable
after specializing the solved closed-constructor derivation to the concrete
`any`/`int` argument.  This remains a static value certificate; dispatch
safety still requires the separate common-fuel hypotheses. -/
theorem closedMultisetMatcherValue_totalTyping :
    ∃ target, TotalValueTyping closedMultisetMatcherValue target := by
  have principal := M4.infer_success_principalTyping
    Paper1FrozenSignature.wellFormed
    M4Paper1ClosedMultisetExactRegression.infer_exact
  rcases principal with ⟨derivation⟩
  rcases derivation.elaboration with ⟨fuel, fuelDerivation⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at fuelDerivation
  | succ fuel =>
      simp only [M4.ElaboratesFuel] at fuelDerivation
      rcases fuelDerivation with
        ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
          functionElaboration, argumentElaboration, generated_eq, next_eq⟩
      cases fuel with
      | zero => simp [M4.ElaboratesFuel] at functionElaboration
      | succ childFuel =>
          have functionShape := functionElaboration
          simp only [M4.ElaboratesFuel] at functionShape
          rcases functionShape with
            ⟨generatedMultiset, multisetElaboration, function_eq⟩
          let principalSolution := derivation.closure.substitution
          let solution :=
            Subst.compose closedMatcherSpecialization principalSolution
          have principalSemantic : Generated.SemanticSolution
              (Generated.fromApp generatedFunction generatedArgument
                (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
                principalSolution := by
            rw [← generated_eq]
            exact TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
              derivation.closure
          have outerSemantic : Generated.SemanticSolution
              (Generated.fromApp generatedFunction generatedArgument
                (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
                solution := by
            exact principalSemantic.postcompose closedMatcherSpecialization
          obtain ⟨functionSemantic, argumentSemantic, functionEquation,
              argumentConversion⟩ := fromApp_semantic_parts outerSemantic
          obtain ⟨conversionClass, argumentConversion⟩ := argumentConversion
          have multisetSemantic : generatedMultiset.SemanticSolution solution := by
            rw [function_eq] at functionSemantic
            exact fromLam_body_semantic functionSemantic
          have listTyped : TotalValueTyping listRecursiveClosure
              (generatedArgument.target.apply solution) := by
            exact matcherFixElaboration_totalValueTyping argumentElaboration
              argumentSemantic .nil .nil
          have multisetDomainEquality :
              (Ty.var ⟨0⟩).apply solution =
                (Ty.var ⟨afterArgument.ty⟩).apply solution := by
            simp only [Equation.Holds] at functionEquation
            rw [function_eq] at functionEquation
            simp only [Generated.fromLam, Ty.apply] at functionEquation
            exact Ty.fn.inj functionEquation |>.1
          have closedResultEquality :
              generatedMultiset.target.apply solution =
                M4Paper1ClosedMultisetExactRegression.closedMultisetType.apply
                  closedMatcherSpecialization := by
            simp only [Equation.Holds] at functionEquation
            rw [function_eq] at functionEquation
            simp only [Generated.fromLam, Ty.apply] at functionEquation
            have codomainEquality := Ty.fn.inj functionEquation |>.2
            have publicEquality := congrArg
              (Ty.apply closedMatcherSpecialization) derivation.target_eq
            simp [PrincipalBlockClosure.target, generated_eq,
              Generated.fromApp, Ty.apply_compose] at publicEquality
            exact codomainEquality.trans publicEquality.symm
          have argumentDomainEquality :
              generatedArgument.target.apply solution =
                (Ty.var ⟨afterArgument.ty⟩).apply solution := by
            have argumentShape := argumentElaboration
            simp only [M4.ElaboratesFuel] at argumentShape
            obtain ⟨argumentBody, argumentBodyElaboration,
              argumentGenerated_eq⟩ := fixElaboration_parts argumentShape
            have convertedFunction : CheckConversion conversionClass
                (.fn
                  ((Fix.domain (.matcher listMatcherClauses) afterFunction).apply
                    solution)
                  ((Fix.codomain (.matcher listMatcherClauses) afterFunction).apply
                    solution))
                ((Ty.var ⟨afterArgument.ty⟩).apply solution) := by
              simpa [argumentGenerated_eq, Generated.fromFix, Ty.apply] using
                argumentConversion
            have equality := checkConversion_fromFunction_eq convertedFunction
            rw [argumentGenerated_eq]
            simpa [Generated.fromFix, Ty.apply] using equality.symm
          have listAtCapturedType : TotalValueTyping listRecursiveClosure
              ((Ty.var ⟨0⟩).apply solution) := by
            rw [multisetDomainEquality, ← argumentDomainEquality]
            exact listTyped
          have multisetTyped : TotalValueTyping multisetRecursiveClosure
              (generatedMultiset.target.apply solution) := by
            exact matcherFixElaboration_totalValueTyping multisetElaboration
              multisetSemantic (.cons .nil) (.cons listAtCapturedType .nil)
          cases childFuel with
          | zero => simp [M4.ElaboratesFuel] at multisetElaboration
          | succ multisetFuel =>
              have multisetFixShape := multisetElaboration
              simp only [M4.ElaboratesFuel] at multisetFixShape
              obtain ⟨generatedMatcher, matcherElaboration,
                multisetGenerated_eq⟩ := fixElaboration_parts multisetFixShape
              rw [multisetGenerated_eq] at multisetSemantic multisetTyped
              obtain ⟨matcherSemantic, matcherEquation⟩ :=
                fromFix_body_semantic multisetSemantic
              have specializedDomain_eq :
                  (Fix.domain (.matcher multisetClauses)
                    ((Context.initialSupply []).nextTy 1)).apply solution =
                    .slot .any .int := by
                rw [multisetGenerated_eq] at closedResultEquality
                simp only [Generated.fromFix, Ty.apply] at closedResultEquality
                have domainEquality := Ty.fn.inj closedResultEquality |>.1
                simpa [M4Paper1ClosedMultisetExactRegression.closedMultisetType,
                  closedMatcherSpecialization, Subst.compose, Subst.singleTy,
                  Subst.singleCap, Ty.apply, Cap.apply] using domainEquality
              have matcherContextCompatible : MonomorphicContextCompatible
                  (Fix.bodyContext
                    (Fix.domain (.matcher multisetClauses)
                      ((Context.initialSupply []).nextTy 1))
                    (Fix.codomain (.matcher multisetClauses)
                      ((Context.initialSupply []).nextTy 1))
                    [.mono (.var ⟨0⟩)])
                  [
                    (Fix.domain (.matcher multisetClauses)
                      ((Context.initialSupply []).nextTy 1)).apply solution,
                    (Ty.fn
                      (Fix.domain (.matcher multisetClauses)
                        ((Context.initialSupply []).nextTy 1))
                      (Fix.codomain (.matcher multisetClauses)
                        ((Context.initialSupply []).nextTy 1))).apply solution,
                    (Ty.var ⟨0⟩).apply solution]
                  solution := by
                simp only [Fix.bodyContext]
                exact .cons (.cons (.cons .nil))
              have somethingTyped : TotalValueTyping Value.something
                  ((Fix.domain (.matcher multisetClauses)
                    ((Context.initialSupply []).nextTy 1)).apply solution) := by
                rw [specializedDomain_eq]
                exact .ordinary
                  (ValueTyping.checked (ValueTyping.something .int)
                    (CheckConversion.matcherToSlot CapabilityDemand.equal))
              have definitionEnvironmentTyped : TotalEnvironmentTyping
                  closedMultisetMatcherEnvironment
                  [
                    (Fix.domain (.matcher multisetClauses)
                      ((Context.initialSupply []).nextTy 1)).apply solution,
                    (Ty.fn
                      (Fix.domain (.matcher multisetClauses)
                        ((Context.initialSupply []).nextTy 1))
                      (Fix.codomain (.matcher multisetClauses)
                        ((Context.initialSupply []).nextTy 1))).apply solution,
                    (Ty.var ⟨0⟩).apply solution] := by
                exact .cons somethingTyped
                  (.cons multisetTyped (.cons listAtCapturedType .nil))
              obtain ⟨matcherFuel, matcherLiteralElaboration⟩ :=
                matcherElaboration_parts matcherElaboration
              have output_eq : generatedMatcher.target.apply solution =
                  .matcher
                    ((Cap.var ⟨(Fix.bodySupply (.matcher multisetClauses)
                      ((Context.initialSupply []).nextTy 1)).cap⟩).apply
                      solution.cap)
                    ((Ty.var ⟨(Fix.bodySupply (.matcher multisetClauses)
                      ((Context.initialSupply []).nextTy 1)).ty⟩).apply
                      solution) := by
                rw [matcherLiteral_target_eq matcherLiteralElaboration]
                rfl
              exact ⟨_, TotalValueTyping.solvedMatcherClosure
                definitionEnvironmentTyped matcherLiteralElaboration matcherSemantic
                matcherContextCompatible output_eq ⟨[], by simp⟩⟩

/-- Typing alone does not prove application safety.  Applying the recursive
closure still requires a separate safety proof for its matcher body. -/
theorem listRecursiveClosure_application_requires_bodySafety
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: []) (.matcher listMatcherClauses)
      codomain)
    (bodySafe : TotalEnvironmentSafe (.matcher listMatcherClauses) codomain
      (domain :: .fn domain codomain :: []))
    (argumentTyped : TotalValueTyping argument domain) (fuel : Nat) :
    TotalTypedResult codomain
      (applyFuel fuel listRecursiveClosure argument) := by
  exact applyFuel_recursiveClosure_totalTyped .nil bodyTyped bodySafe
    argumentTyped fuel

/-- The same separation is explicit for the actual multiset recursive
closure: its captured list closure may be totally typed, but application also
needs an independent common-fuel safety proof for the multiset matcher body. -/
theorem multisetRecursiveClosure_application_requires_bodySafety
    (environmentTyped : TotalEnvironmentTyping [listRecursiveClosure] context)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: context) (.matcher multisetClauses)
      codomain)
    (bodySafe : TotalEnvironmentSafe (.matcher multisetClauses) codomain
      (domain :: .fn domain codomain :: context))
    (argumentTyped : TotalValueTyping argument domain) (fuel : Nat) :
    TotalTypedResult codomain
      (applyFuel fuel multisetRecursiveClosure argument) := by
  exact applyFuel_recursiveClosure_totalTyped environmentTyped bodyTyped
    bodySafe argumentTyped fuel

end TypePM.Source.MatcherTyping.M4Paper1RecursiveClosureTotalTyping
