import TypePM.Source.GeneralizedOccurrenceSolution
import TypePM.Source.M4FuelEmbeddedCertificateBridge
import TypePM.Source.M4MatchFirstTotalCoreBridge
import TypePM.Source.M4OriginMapProducer
import TypePM.Source.M4OriginMatchingEvaluationBridge
import TypePM.Source.M4RawOriginRequestCertificate

/-!
# Recursive raw M4 producer for structural origin demands

`RawOriginRequestPlan` is a static request-realizability judgment for the
largest uniform raw-M4 fragment currently justified by structural origin
demands.  It fixes evaluator fuel, the output observation, and the exact
source-environment input observation without storing a semantic solution,
runtime value, or completed evaluation result.

The producer below turns a plan into an exact raw certificate by mutual
induction over expressions and tuple fields.  Plain lambdas retain the
contravariant argument-coverage proof; application transports every demand
through the solved checking conversion.
-/

namespace TypePM.Runtime

/-- Demands satisfied by every value at every type.  They still require the
evaluation itself not to be stuck. -/
inductive OriginDemand.Universal : OriginDemand → Prop where
  | none : OriginDemand.Universal .none
  | zero : OriginDemand.Universal (.fuel 0)
  | both (left : OriginDemand.Universal leftDemand)
      (right : OriginDemand.Universal rightDemand) :
      OriginDemand.Universal (.both leftDemand rightDemand)

theorem OriginDemand.Universal.valueSafe
    (universal : OriginDemand.Universal demand) (value : Value) (target : Ty) :
    OriginValueSafe demand value target := by
  induction universal with
  | none => simp only [OriginValueSafe]
  | zero => simp [OriginValueSafe, FuelValueSafe]
  | both left right leftIH rightIH =>
      exact OriginValueSafe.both leftIH rightIH

theorem OriginResultSafe.reobserveUniversal
    (safe : OriginResultSafe available target result)
    (universal : OriginDemand.Universal requested) :
    OriginResultSafe requested target result := by
  rcases safe with timeout | ⟨value, success, _valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, universal.valueSafe value target⟩

end TypePM.Runtime

namespace TypePM.Source.M4

open TypePM.Runtime

/-- Embedded certificate family used internally by the raw matching rules.
Each member is an environment-parametric preservation proof, so raw child
certificates can be checked-converted to the matcher slot selected by the
enclosing M4 solution before entering the common matching runtime bridge. -/
def RawOriginEmbeddedCertificate : FuelEmbeddedExpressionCertificateFamily :=
  fun operationalFuel bindingTypes environmentTypes expression target
      outputDemand inputDemand =>
    ∀ bindings environment,
      OriginEnvironmentSafe inputDemand (bindings ++ environment)
        (bindingTypes ++ environmentTypes) →
      OriginResultSafe outputDemand target
        (evalFuel operationalFuel (bindings ++ environment) expression)

theorem rawOriginEmbeddedEvaluatorSafe :
    FuelEmbeddedEvaluatorSafe RawOriginEmbeddedCertificate evalFuel := by
  intro operationalFuel bindingTypes environmentTypes expression target
    outputDemand inputDemand bindings environment certificate environmentSafe
  exact certificate bindings environment environmentSafe

private theorem FuelEnvironmentSafe.toOriginEnvironmentSafe
    (safe : FuelEnvironmentSafe fuel values targets) :
    OriginEnvironmentSafe (OriginEnvironmentDemand.fuel (fun _ => fuel))
      values targets := by
  refine ⟨safe.1, ?_⟩
  intro position target value targetFound valueFound
  obtain ⟨actual, actualFound, actualSafe⟩ := safe.2 position target
    targetFound
  rw [valueFound] at actualFound
  cases actualFound
  exact OriginValueSafe.ofFuel actualSafe

private theorem OriginEnvironmentSafe.toFuelEnvironmentSafe
    (safe : OriginEnvironmentSafe
      (OriginEnvironmentDemand.fuel (fun _ => fuel)) values targets) :
    FuelEnvironmentSafe fuel values targets := by
  induction values generalizing targets with
  | nil =>
      cases targets with
      | nil => exact FuelEnvironmentSafe.nil fuel
      | cons target targets =>
          have impossible := safe.1
          simp at impossible
  | cons value values induction =>
      cases targets with
      | nil =>
          have impossible := safe.1
          simp at impossible
      | cons target targets =>
          have headSafe : OriginValueSafe (.fuel fuel) value target :=
            safe.2 0 target value (by simp) (by simp)
          have tailSafe : OriginEnvironmentSafe
              (OriginEnvironmentDemand.fuel (fun _ => fuel)) values targets := by
            refine ⟨by simpa using safe.1, ?_⟩
            intro position tailTarget tailValue targetFound valueFound
            exact safe.2 (position + 1) tailTarget tailValue
              (by simpa only [List.getElem?_cons_succ] using targetFound)
              (by simpa only [List.getElem?_cons_succ] using valueFound)
          exact FuelEnvironmentSafe.cons headSafe.toFuel (induction tailSafe)

private theorem OriginEnvironmentSafe.mono
    (safe : OriginEnvironmentSafe available values targets)
    (covers : ∀ position, OriginDemand.Le (requested position)
      (available position)) :
    OriginEnvironmentSafe requested values targets := by
  refine ⟨safe.1, ?_⟩
  intro position target value targetFound valueFound
  exact (safe.2 position target value targetFound valueFound).mono
    (covers position)

private theorem monomorphicContextCompatible_prepend
    (bindings : List Ty)
    (compatible : MonomorphicContextCompatible context environmentTypes
      solution) :
    MonomorphicContextCompatible
      (bindings.map Scheme.mono ++ context)
      (Ty.applyList solution bindings ++ environmentTypes) solution := by
  induction bindings with
  | nil => simpa [Ty.applyList] using compatible
  | cons binding bindings induction =>
      simp only [List.map_cons, List.cons_append, Ty.applyList,
        List.map_cons]
      exact .cons induction

private theorem monomorphicContextCompatible_lookupRuntime
    (compatible : MonomorphicContextCompatible context environmentTypes
      solution)
    {position : Nat} {target : Ty}
    (found : environmentTypes[position]? = some target) :
    ∃ sourceTarget,
      context[position]? = some (Scheme.mono sourceTarget) ∧
        target = sourceTarget.apply solution := by
  induction position generalizing context environmentTypes target with
  | zero =>
      cases compatible with
      | nil => simp at found
      | cons compatibleTail =>
          rename_i sourceTarget
          simp at found
          exact ⟨sourceTarget, rfl, found.symm⟩
  | succ position induction =>
      cases compatible with
      | nil => simp at found
      | cons tail =>
          simp only [List.getElem?_cons_succ] at found ⊢
          exact induction tail found

private theorem SchemeOriginEnvironmentSafe.toOriginEnvironmentSafe
    (safe : SchemeOriginEnvironmentSafe demand solution values context)
    (compatible : MonomorphicContextCompatible context environmentTypes
      solution) :
    OriginEnvironmentSafe demand values environmentTypes := by
  refine ⟨safe.1.trans compatible.source_runtime_length, ?_⟩
  intro position target value targetFound valueFound
  obtain ⟨sourceTarget, sourceFound, targetEq⟩ :=
    monomorphicContextCompatible_lookupRuntime compatible targetFound
  subst target
  have sourceSafe := safe.2 position (Scheme.mono sourceTarget) value
    sourceFound valueFound ⟨0, 0⟩
  simpa [Scheme.instantiate_mono] using sourceSafe

private theorem monomorphicContextCompatible_of_eq
    (contextEq : context = sourceTargets.map Scheme.mono) :
    MonomorphicContextCompatible context (Ty.applyList solution sourceTargets)
      solution := by
  subst context
  simpa [Ty.applyList] using
    monomorphicContextCompatible_prepend sourceTargets
      (MonomorphicContextCompatible.nil (solution := solution))

private theorem sourceScheme_mem_of_getElem?_eq_some
    {context : Context} {position : Nat} {scheme : Scheme}
    (lookup : context[position]? = some scheme) :
    scheme ∈ context := by
  induction context generalizing position with
  | nil => simp at lookup
  | cons head tail induction =>
      cases position with
      | zero =>
          simp at lookup
          subst scheme
          simp
      | succ position =>
          simp only [List.getElem?_cons_succ] at lookup
          exact List.mem_cons_of_mem head (induction lookup)

/-- Pointwise universal demands need only source/runtime length alignment. -/
private theorem schemeOriginEnvironmentSafe_ofUniversal
    (lengthEq : values.length = context.length)
    (universal : ∀ position, OriginDemand.Universal (demand position)) :
    SchemeOriginEnvironmentSafe demand solution values context := by
  refine ⟨lengthEq, ?_⟩
  intro position scheme value _schemeFound _valueFound occurrenceSupply
  exact (universal position).valueSafe value
    ((scheme.instantiate occurrenceSupply).1.apply solution)

/-- Every source scheme in the surrounding context opens no fresh type or
capability variables.  This is the monomorphic-context boundary used by the
arity-zero `letE` rule; it does not claim that a general polymorphic open
`letE` can be transported. -/
def ContextSchemeArityZero (context : Context) : Prop :=
  ∀ (position : Nat) (scheme : Scheme), context[position]? = some scheme →
    scheme.tyArity = 0 ∧ scheme.capArity = 0

/-- In an arity-zero source context, occurrence-specific and outer solutions
give exactly the same instantiated occurrence type at every environment
position. -/
private theorem schemeOriginEnvironmentSafe_ofOccurrenceArityZero
    (safe : SchemeOriginEnvironmentSafe demand outer values context)
    (arityZero : ContextSchemeArityZero context)
    (occurrence : GeneralizedOccurrenceSolution context closure outer supply) :
    SchemeOriginEnvironmentSafe demand occurrence.solution values context := by
  refine ⟨safe.1, ?_⟩
  intro position scheme value schemeFound valueFound occurrenceSupply
  have outerSafe := safe.2 position scheme value schemeFound valueFound
    occurrenceSupply
  have occurrenceEq := occurrence.schemeOccurrence_eq_of_prefix_agreement
    schemeFound occurrenceSupply
    (fun offset within => by
      have zero := (arityZero position scheme schemeFound).1
      omega)
    (fun offset within => by
      have zero := (arityZero position scheme schemeFound).2
      omega)
  rw [occurrenceEq]
  exact outerSafe

/-- Closing the source context at an exact `letE` interface preserves every
structural environment observation under the enclosing solution. -/
private theorem schemeOriginEnvironmentSafe_ofApplyFreeInterface
    (safe : SchemeOriginEnvironmentSafe demand solution values context)
    (solved : Solves solution (context.interfaceEquations block)) :
    SchemeOriginEnvironmentSafe demand solution values
      (context.applyFree block) := by
  refine ⟨?_, ?_⟩
  · simpa [Context.applyFree] using safe.1
  · intro position transformedScheme value transformedFound valueFound
    simp only [Context.applyFree, List.getElem?_map] at transformedFound
    cases originalFound : context[position]? with
    | none => simp [originalFound] at transformedFound
    | some scheme =>
        simp only [originalFound, Option.map_some, Option.some.injEq] at transformedFound
        subst transformedScheme
        intro occurrenceSupply
        have valueSafe := safe.2 position scheme value originalFound valueFound
          occurrenceSupply
        rw [SchemeFuelEnvironmentSafe.instantiate_applyFree_apply_eq_of_interface
          (sourceScheme_mem_of_getElem?_eq_some originalFound) block solution
          solved occurrenceSupply]
        exact valueSafe

private theorem semanticSolution_fromLet_parts
    (semantic : (Generated.fromLet effects bodyGenerated).SemanticSolution
      solution) :
    Solves solution effects ∧ bodyGenerated.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by simp [Generated.fromLet, membership])
  · constructor
    · intro equation membership
      exact semantic.1 equation (by simp [Generated.fromLet, membership])
    · intro obligation membership
      exact semantic.2 obligation (by
        simpa [Generated.fromLet] using membership)

private theorem semanticSolution_fromMatchAll_target
    (semantic : (Generated.fromMatchAll target pattern matcher body).SemanticSolution
      solution) :
    target.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [Generated.fromMatchAll, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [Generated.fromMatchAll, membership])

private theorem semanticSolution_fromMatchAll_matcher
    (semantic : (Generated.fromMatchAll target pattern matcher body).SemanticSolution
      solution) :
    matcher.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [Generated.fromMatchAll, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [Generated.fromMatchAll, membership])

private theorem semanticSolution_fromMatchAll_body
    (semantic : (Generated.fromMatchAll target pattern matcher body).SemanticSolution
      solution) :
    body.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [Generated.fromMatchAll, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [Generated.fromMatchAll, membership])

private theorem semanticSolution_fromMatchAll_matcherConversion
    (semantic : (Generated.fromMatchAll target pattern matcher body).SemanticSolution
      solution) :
    ∃ conversionClass,
      CheckConversion conversionClass (matcher.target.apply solution)
        ((Ty.slot pattern.dual.capability target.target).apply solution) := by
  exact semantic.2
    ⟨matcher.target, .slot pattern.dual.capability target.target⟩ (by
      simp [Generated.fromMatchAll])

private theorem semanticSolution_fromMatchFirst_target
    (semantic : (MatchFirstTyping.Generated.fromMatchFirst target matcher arms).SemanticSolution
      solution) :
    target.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [MatchFirstTyping.Generated.fromMatchFirst, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [MatchFirstTyping.Generated.fromMatchFirst, membership])

private theorem semanticSolution_fromMatchFirst_matcher
    (semantic : (MatchFirstTyping.Generated.fromMatchFirst target matcher arms).SemanticSolution
      solution) :
    matcher.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [MatchFirstTyping.Generated.fromMatchFirst, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [MatchFirstTyping.Generated.fromMatchFirst, membership])

private theorem semanticSolution_fromMatchFirst_arms
    (semantic : (MatchFirstTyping.Generated.fromMatchFirst target matcher arms).SemanticSolution
      solution) :
    arms.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [MatchFirstTyping.Generated.fromMatchFirst, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [MatchFirstTyping.Generated.fromMatchFirst, membership])

private theorem semanticSolution_fromMatchFirst_fallback
    (semantic : (MatchFirstTyping.GeneratedArms.fromFallback fallback tail).SemanticSolution
      solution) :
    fallback.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [MatchFirstTyping.GeneratedArms.fromFallback, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [MatchFirstTyping.GeneratedArms.fromFallback, membership])

private theorem semanticSolution_fromMatchFirst_tail
    (semantic : (MatchFirstTyping.GeneratedArms.fromFallback fallback tail).SemanticSolution
      solution) :
    tail.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [MatchFirstTyping.GeneratedArms.fromFallback, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [MatchFirstTyping.GeneratedArms.fromFallback, membership])

private theorem semanticSolution_fromMatchFirst_armPattern
    {tail : MatchFirstTyping.GeneratedTail}
    (semantic : (⟨
      (MatchFirstTyping.GeneratedTail.fromArm targetType matcherType
        expectedResult pattern body).hard ++ tail.hard,
      (MatchFirstTyping.GeneratedTail.fromArm targetType matcherType
        expectedResult pattern body).pending ++ tail.pending⟩ :
      MatchFirstTyping.GeneratedTail).SemanticSolution solution) :
    MatcherTyping.GeneratedPatternRuntimeSolution pattern solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [MatchFirstTyping.GeneratedTail.fromArm, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [MatchFirstTyping.GeneratedTail.fromArm, membership])

private theorem semanticSolution_fromMatchFirst_armBody
    {tail : MatchFirstTyping.GeneratedTail}
    (semantic : (⟨
      (MatchFirstTyping.GeneratedTail.fromArm targetType matcherType
        expectedResult pattern body).hard ++ tail.hard,
      (MatchFirstTyping.GeneratedTail.fromArm targetType matcherType
        expectedResult pattern body).pending ++ tail.pending⟩ :
      MatchFirstTyping.GeneratedTail).SemanticSolution solution) :
    body.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by
      simp [MatchFirstTyping.GeneratedTail.fromArm, membership])
  · intro obligation membership
    exact semantic.2 obligation (by
      simp [MatchFirstTyping.GeneratedTail.fromArm, membership])

private theorem semanticSolution_fromMatchFirst_rest
    {tail : MatchFirstTyping.GeneratedTail}
    (semantic : (⟨
      (MatchFirstTyping.GeneratedTail.fromArm targetType matcherType
        expectedResult pattern body).hard ++ tail.hard,
      (MatchFirstTyping.GeneratedTail.fromArm targetType matcherType
        expectedResult pattern body).pending ++ tail.pending⟩ :
      MatchFirstTyping.GeneratedTail).SemanticSolution solution) :
    tail.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by simp [membership])
  · intro obligation membership
    exact semantic.2 obligation (by simp [membership])

private theorem semanticSolution_fromMatchFirst_bodyTarget
    {tail : MatchFirstTyping.GeneratedTail}
    (semantic : (⟨
      (MatchFirstTyping.GeneratedTail.fromArm targetType matcherType
        expectedResult pattern body).hard ++ tail.hard,
      (MatchFirstTyping.GeneratedTail.fromArm targetType matcherType
        expectedResult pattern body).pending ++ tail.pending⟩ :
      MatchFirstTyping.GeneratedTail).SemanticSolution solution) :
    body.target.apply solution = expectedResult.apply solution := by
  exact semantic.1 (.ty body.target expectedResult) (by
    simp [MatchFirstTyping.GeneratedTail.fromArm])

/-- A raw certificate whose synthesized input demand is exactly the demand
advertised by the static request plan. -/
structure ExactRawOriginRequestCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next)
    (operationalFuel : Nat) (outputDemand : OriginDemand)
    (inputDemand : OriginEnvironmentDemand) : Type where
  certificate : RawOriginRequestCertificate elaboration operationalFuel
    outputDemand
  input_eq : certificate.inputDemand = inputDemand

/-- List-valued companion used by tuple evaluation. -/
structure RawOriginItemsFuelCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (elaboration : ItemsElaborateUsing (ElaboratesFuel signature staticFuel)
      context expressions supply generated next)
    (operationalFuel resultIndex : Nat) : Type where
  inputDemand : OriginEnvironmentDemand
  preserves : SignatureCompatible signature.base → ∀ solution,
    TypePM.Runtime.GeneratedItems.SemanticSolution generated solution →
      ∀ environment,
        SchemeOriginEnvironmentSafe inputDemand solution environment context →
          FuelEnvironmentResultSafe resultIndex
            (Ty.applyList solution generated.targets)
            (FuelResult.traverse (evalFuel operationalFuel environment)
              expressions)

structure ExactRawOriginItemsFuelCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (elaboration : ItemsElaborateUsing (ElaboratesFuel signature staticFuel)
      context expressions supply generated next)
    (operationalFuel resultIndex : Nat)
    (inputDemand : OriginEnvironmentDemand) : Type where
  certificate : RawOriginItemsFuelCertificate elaboration operationalFuel
    resultIndex
  input_eq : certificate.inputDemand = inputDemand

/-- Semantic companion for a normalized n-argument curried call.  Each
constructor records the solved domain selected at one call step, together
with the child semantic solution and checking conversion for that argument. -/
inductive CurriedCallSemantic
    {signature : FrozenSignature} {staticFuel : Nat} {context : Context}
    (solution : Subst) :
    ∀ {accumulated : Generated} {arguments : List Expr} {supply : Supply}
      {generated : Generated} {next : Supply},
      CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
        accumulated arguments supply generated next → List Ty → Prop where
  | nil
      {accumulated supply}
      (semantic : TypePM.Generated.SemanticSolution accumulated solution) :
      CurriedCallSemantic solution
        (CallElaboratesUsing.nil (accumulated := accumulated)
          (supply := supply)) []
  | cons
      {accumulated argument arguments supply generatedArgument afterArgument
        generated next expectedTail}
      {head : ElaboratesFuel signature staticFuel context argument supply
        generatedArgument afterArgument}
      {tail : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
        (Generated.fromApp accumulated generatedArgument
          (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
        arguments (afterArgument.nextTy 2) generated next}
      (tailSemantic : CurriedCallSemantic solution tail expectedTail)
      (accumulatedSemantic : TypePM.Generated.SemanticSolution accumulated solution)
      (argumentSemantic : TypePM.Generated.SemanticSolution generatedArgument solution)
      (functionType : Equation.Holds solution
        (.ty accumulated.target
          (.fn (.var ⟨afterArgument.ty⟩)
            (.var ⟨afterArgument.ty + 1⟩))))
      (argumentConversion : ∃ conversionClass,
        CheckConversion conversionClass
          (generatedArgument.target.apply solution)
          ((Ty.var ⟨afterArgument.ty⟩).apply solution)) :
      CurriedCallSemantic solution
        (CallElaboratesUsing.cons head tail)
        ((Ty.var ⟨afterArgument.ty⟩).apply solution :: expectedTail)

namespace CurriedCallSemantic

/-- A semantic solution for the end of a curried-call derivation also
satisfies the exact accumulated block at its beginning. -/
theorem initialSemanticSolution
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      accumulated arguments supply generated next)
    (semantic : TypePM.Generated.SemanticSolution generated solution) :
    TypePM.Generated.SemanticSolution accumulated solution := by
  induction call with
  | nil => exact semantic
  | cons head tail tailIH =>
      exact (semanticSolution_fromApp_parts (tailIH semantic)).1

/-- Every semantic solution of the final generated block decomposes along the
entire static curried-call spine. -/
theorem ofFinalSemantic
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      accumulated arguments supply generated next)
    (semantic : TypePM.Generated.SemanticSolution generated solution) :
    ∃ expectedTypes, CurriedCallSemantic solution call expectedTypes := by
  induction call with
  | nil => exact ⟨[], .nil semantic⟩
  | @cons accumulated argument arguments supply generatedArgument afterArgument
      generated next head tail tailIH =>
      obtain ⟨expectedTail, tailSemantic⟩ := tailIH semantic
      obtain ⟨accumulatedSemantic, argumentSemantic, functionType,
        argumentConversion⟩ :=
        semanticSolution_fromApp_parts
          (initialSemanticSolution tail semantic)
      exact ⟨_, .cons (head := head) tailSemantic accumulatedSemantic argumentSemantic
        functionType argumentConversion⟩

end CurriedCallSemantic

/-- Runtime companion for a curried call.  It relates the static call spine
to left-to-right evaluator traversal without executing the curried function:
constructors and primitives evaluate their argument list directly. -/
structure RawOriginCallCertificate
    {signature : FrozenSignature} {staticFuel : Nat} {context : Context}
    {accumulated : Generated} {arguments : List Expr} {supply : Supply}
    {generated : Generated} {next : Supply}
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      accumulated arguments supply generated next)
    (operationalFuel : Nat) (demands : List OriginDemand) : Type where
  inputDemand : OriginEnvironmentDemand
  preserves : SignatureCompatible signature.base → ∀ solution,
    TypePM.Generated.SemanticSolution generated solution → ∀ environment,
      SchemeOriginEnvironmentSafe inputDemand solution environment context →
        FuelResultSafeWith
          (fun values => ∃ expectedTypes,
            CurriedCallSemantic solution call expectedTypes ∧
              OriginValueSafes demands values expectedTypes)
          (FuelResult.traverse (evalFuel operationalFuel environment) arguments)

structure ExactRawOriginCallCertificate
    {signature : FrozenSignature} {staticFuel : Nat} {context : Context}
    {accumulated : Generated} {arguments : List Expr} {supply : Supply}
    {generated : Generated} {next : Supply}
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      accumulated arguments supply generated next)
    (operationalFuel : Nat) (demands : List OriginDemand)
    (inputDemand : OriginEnvironmentDemand) : Type where
  certificate : RawOriginCallCertificate call operationalFuel demands
  input_eq : certificate.inputDemand = inputDemand

namespace ExactRawOriginCallCertificate

theorem nil
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      accumulated [] supply generated next)
    (operationalFuel : Nat) :
    Nonempty (ExactRawOriginCallCertificate call operationalFuel []
      OriginEnvironmentDemand.none) := by
  cases call
  let certificate : RawOriginCallCertificate
      (CallElaboratesUsing.nil :
        CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
          accumulated [] supply accumulated supply)
      operationalFuel [] :=
    ⟨OriginEnvironmentDemand.none, by
      intro _compatible solution semantic environment environmentSafe
      exact .inr ⟨[], by simp [FuelResult.traverse], [], .nil semantic, .nil⟩⟩
  exact ⟨⟨certificate, rfl⟩⟩

theorem cons
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      accumulated (argument :: arguments) supply generated next)
    (operationalFuel : Nat)
    (headDemand : OriginDemand) (tailDemands : List OriginDemand)
    (headInput tailInput : OriginEnvironmentDemand)
    (headCertificate : ∀ generatedArgument afterArgument,
      ∀ head : ElaboratesFuel signature staticFuel context argument supply
        generatedArgument afterArgument,
        Nonempty (ExactRawOriginRequestCertificate head operationalFuel
          headDemand headInput))
    (tailCertificate : ∀ (generatedArgument : Generated)
      (afterArgument : Supply) (generated : Generated) (next : Supply),
      ∀ tail : CallElaboratesUsing (ElaboratesFuel signature staticFuel)
        context
        (Generated.fromApp accumulated generatedArgument
          (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
        arguments (afterArgument.nextTy 2) generated next,
        Nonempty (ExactRawOriginCallCertificate tail operationalFuel
          tailDemands tailInput)) :
    Nonempty (ExactRawOriginCallCertificate call operationalFuel
      (headDemand :: tailDemands)
      (OriginEnvironmentDemand.both headInput tailInput)) := by
  cases call with
  | @cons accumulated argument arguments supply generatedArgument afterArgument
      generated next head tail =>
      obtain ⟨headExact⟩ :=
        headCertificate generatedArgument afterArgument head
      obtain ⟨tailExact⟩ :=
        tailCertificate generatedArgument afterArgument generated next tail
      let headCert := headExact.certificate
      let tailCert := tailExact.certificate
      let inputDemand := OriginEnvironmentDemand.both
        headCert.inputDemand tailCert.inputDemand
      let certificate : RawOriginCallCertificate
          (CallElaboratesUsing.cons head tail) operationalFuel
          (headDemand :: tailDemands) :=
        ⟨inputDemand, by
          intro compatible solution semantic environment environmentSafe
          have stepSemantic :=
            CurriedCallSemantic.initialSemanticSolution tail semantic
          obtain ⟨accumulatedSemantic, argumentSemantic, functionType,
            argumentConversion⟩ :=
            semanticSolution_fromApp_parts stepSemantic
          have headEnvironmentSafe := environmentSafe.mono
            (fun position => OriginDemand.Le.fromLeft (.refl _))
          have tailEnvironmentSafe := environmentSafe.mono
            (fun position => OriginDemand.Le.fromRight (.refl _))
          rcases (headCert.preserves compatible solution argumentSemantic
              environment headEnvironmentSafe) with headTimeout |
              ⟨headValue, headOk, headSafe⟩
          · exact .inl (by
              simp [FuelResult.traverse, headTimeout])
          · obtain ⟨conversionClass, conversion⟩ := argumentConversion
            have convertedHeadSafe := headSafe.ofCheckConversion conversion
            rcases tailCert.preserves compatible solution semantic environment
                tailEnvironmentSafe with tailTimeout |
                ⟨tailValues, tailOk, expectedTail, tailSemantic, tailSafe⟩
            · exact .inl (by
                simp [FuelResult.traverse, headOk, tailTimeout,
                  FuelResult.bind, FuelResult.map])
            · exact .inr ⟨headValue :: tailValues, by
                simp [FuelResult.traverse, headOk, tailOk,
                  FuelResult.bind, FuelResult.map],
                _, .cons (head := head) tailSemantic accumulatedSemantic
                  argumentSemantic functionType ⟨conversionClass, conversion⟩,
                .cons convertedHeadSafe tailSafe⟩⟩
      refine ⟨⟨certificate, ?_⟩⟩
      simp [certificate, inputDemand, headCert, tailCert,
        headExact.input_eq, tailExact.input_eq]

end ExactRawOriginCallCertificate

namespace ExactRawOriginRequestCertificate

/-- General constructor producer.  The call companion handles the complete
left-to-right argument traversal; the final premise only describes how the
runtime constructor reassembles a demanded result from safe fields. -/
theorem ctor
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.ctor constructor arguments) supply generated next)
    (childFuel : Nat) (outputDemand : OriginDemand)
    (demands : List OriginDemand) (inputDemand : OriginEnvironmentDemand)
    (callCertificate : ∀ (scheme : Scheme),
      ∀ call : CallElaboratesUsing
        (ElaboratesFuel signature staticFuel) context
        ⟨(scheme.instantiate supply).1, [], []⟩ arguments
        (scheme.instantiate supply).2 generated next,
        Nonempty (ExactRawOriginCallCertificate call childFuel demands
          inputDemand))
    (resultSafe : SignatureCompatible signature.base → ∀ (scheme : Scheme),
      signature.base.lookupDataConstructor constructor = some scheme →
      ∀ solution,
      TypePM.Generated.SemanticSolution generated solution →
      ∀ call : CallElaboratesUsing
        (ElaboratesFuel signature staticFuel) context
        ⟨(scheme.instantiate supply).1, [], []⟩ arguments
        (scheme.instantiate supply).2 generated next,
      ∀ values expectedTypes,
      CurriedCallSemantic solution call expectedTypes →
      OriginValueSafes demands values expectedTypes →
      OriginValueSafe outputDemand (.data constructor values)
        (generated.target.apply solution)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      outputDemand inputDemand) := by
  rcases elaboration with ⟨scheme, lookup, arity, closed, call⟩
  obtain ⟨callExact⟩ := callCertificate scheme call
  let callCert := callExact.certificate
  let certificate : RawOriginRequestCertificate
      (show ElaboratesFuel signature (staticFuel + 1) context
        (.ctor constructor arguments) supply generated next from
          ⟨scheme, lookup, arity, closed, call⟩)
      (childFuel + 1) outputDemand :=
    ⟨callCert.inputDemand, by
      intro compatible solution semantic environment environmentSafe
      rcases callCert.preserves compatible solution semantic environment
          environmentSafe with timeout |
          ⟨values, success, expectedTypes, callSemantic, valuesSafe⟩
      · exact .inl (by
          simp [evalFuel, FuelResult.map, timeout])
      · exact .inr ⟨.data constructor values, by
          simp [evalFuel, FuelResult.map, success],
          resultSafe compatible scheme lookup solution semantic call values
            expectedTypes callSemantic valuesSafe⟩⟩
  refine ⟨⟨certificate, ?_⟩⟩
  simpa [certificate, callCert] using callExact.input_eq

/-- General first-order primitive producer.  Argument evaluation is supplied
by the curried-call certificate; the final premise is the primitive's
execution-independent preservation law on already evaluated values. -/
theorem prim
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.prim operation arguments) supply generated next)
    (childFuel : Nat) (outputDemand : OriginDemand)
    (demands : List OriginDemand) (inputDemand : OriginEnvironmentDemand)
    (callCertificate : ∀ (scheme : Scheme),
      ∀ call : CallElaboratesUsing
        (ElaboratesFuel signature staticFuel) context
        ⟨(scheme.instantiate supply).1, [], []⟩ arguments
        (scheme.instantiate supply).2 generated next,
        Nonempty (ExactRawOriginCallCertificate call childFuel demands
          inputDemand))
    (resultSafe : SignatureCompatible signature.base → ∀ (scheme : Scheme),
      signature.base.lookupPrimitive operation = some scheme →
      ∀ solution,
      TypePM.Generated.SemanticSolution generated solution →
      ∀ call : CallElaboratesUsing
        (ElaboratesFuel signature staticFuel) context
        ⟨(scheme.instantiate supply).1, [], []⟩ arguments
        (scheme.instantiate supply).2 generated next,
      ∀ values expectedTypes,
      CurriedCallSemantic solution call expectedTypes →
      OriginValueSafes demands values expectedTypes →
      FuelResultSafeWith
        (fun value => OriginValueSafe outputDemand value
          (generated.target.apply solution))
        (evalPrimitive (applyFuel childFuel) operation values)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      outputDemand inputDemand) := by
  rcases elaboration with ⟨scheme, lookup, arity, closed, call⟩
  obtain ⟨callExact⟩ := callCertificate scheme call
  let callCert := callExact.certificate
  let certificate : RawOriginRequestCertificate
      (show ElaboratesFuel signature (staticFuel + 1) context
        (.prim operation arguments) supply generated next from
          ⟨scheme, lookup, arity, closed, call⟩)
      (childFuel + 1) outputDemand :=
    ⟨callCert.inputDemand, by
      intro compatible solution semantic environment environmentSafe
      rcases callCert.preserves compatible solution semantic environment
          environmentSafe with timeout |
          ⟨values, success, expectedTypes, callSemantic, valuesSafe⟩
      · exact .inl (by
          simp [evalFuel, FuelResult.bind, timeout])
      · rcases resultSafe compatible scheme lookup solution semantic call
            values expectedTypes callSemantic valuesSafe with primitiveTimeout |
            ⟨value, primitiveSuccess, valueSafe⟩
        · exact .inl (by
            simp [evalFuel, FuelResult.bind, success, primitiveTimeout])
        · exact .inr ⟨value, by
            simp [evalFuel, FuelResult.bind, success, primitiveSuccess],
            valueSafe⟩⟩
  refine ⟨⟨certificate, ?_⟩⟩
  simpa [certificate, callCert] using callExact.input_eq

/-- Specialized raw producer for primitive `map`.  The callback and list
expressions are evaluated at the same child fuel.  Their observations remain
structural and independent: the callback supports one `plainCall` at that
fuel, while the input exposes `listOf` the corresponding argument demand.

This rule is separate from `RawOriginPrimitiveResultPlan`: `map` invokes a
runtime callback, so its preservation law is not a first-order delta rule on
already evaluated values. -/
theorem primMap
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.prim .map [functionExpression, inputExpression]) supply generated next)
    (childFuel : Nat) (argumentDemand resultDemand : OriginDemand)
    (functionInput inputInput : OriginEnvironmentDemand)
    (functionCertificate : ∀ {childSupply generatedFunction afterFunction},
      ∀ functionElaboration : ElaboratesFuel signature staticFuel context
        functionExpression childSupply generatedFunction afterFunction,
      Nonempty (ExactRawOriginRequestCertificate functionElaboration childFuel
        (.plainCall childFuel argumentDemand resultDemand) functionInput))
    (inputCertificate : ∀ {childSupply generatedInput afterInput},
      ∀ inputElaboration : ElaboratesFuel signature staticFuel context
        inputExpression childSupply generatedInput afterInput,
      Nonempty (ExactRawOriginRequestCertificate inputElaboration childFuel
        (.listOf argumentDemand) inputInput)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.listOf resultDemand)
      (OriginEnvironmentDemand.both functionInput inputInput)) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  rcases elaboration with ⟨scheme, lookup, arity, closed, call⟩
  cases call with
      | cons functionElaboration rest =>
          cases rest with
          | cons inputElaboration rest =>
              cases rest
              obtain ⟨functionExact⟩ :=
                functionCertificate functionElaboration
              obtain ⟨inputExact⟩ := inputCertificate inputElaboration
              let certificate : RawOriginRequestCertificate parentElaboration
                  (childFuel + 1) (.listOf resultDemand) :=
                ⟨OriginEnvironmentDemand.both functionInput inputInput, by
                  intro compatible solution semantic environment environmentSafe
                  rw [compatible.map] at lookup
                  cases lookup
                  obtain ⟨firstSemantic, inputSemantic, secondEquation,
                      inputCheck⟩ := semanticSolution_fromApp_parts semantic
                  obtain ⟨_initialSemantic, functionSemantic, firstEquation,
                      functionCheck⟩ :=
                    semanticSolution_fromApp_parts firstSemantic
                  have functionEnvironmentSafe : SchemeOriginEnvironmentSafe
                      functionInput solution environment context :=
                    environmentSafe.mono
                      (fun position => .fromLeft (.refl _))
                  have inputEnvironmentSafe : SchemeOriginEnvironmentSafe
                      inputInput solution environment context :=
                    environmentSafe.mono
                      (fun position => .fromRight (.refl _))
                  have functionSafeAtSource :=
                    functionExact.certificate.preserves compatible solution
                      functionSemantic environment
                      (by simpa [functionExact.input_eq] using
                        functionEnvironmentSafe)
                  have inputSafeAtSource :=
                    inputExact.certificate.preserves compatible solution
                      inputSemantic environment
                      (by simpa [inputExact.input_eq] using inputEnvironmentSafe)
                  obtain ⟨_functionClass, functionConversion⟩ := functionCheck
                  obtain ⟨_inputClass, inputConversion⟩ := inputCheck
                  simp only [Ty.apply] at functionConversion inputConversion
                  simp only [Equation.Holds, Ty.apply] at firstEquation secondEquation
                  simp only [PrimitiveSchemes.instantiate_map] at firstEquation
                  simp only [Generated.fromApp, Ty.apply] at secondEquation ⊢
                  have firstParts := Ty.fn.inj firstEquation
                  rw [← firstParts.2] at secondEquation
                  have secondParts := Ty.fn.inj secondEquation
                  rw [← firstParts.1] at functionConversion
                  rw [← secondParts.1] at inputConversion
                  rw [← secondParts.2]
                  exact evalFuel_map_originResultSafe
                    (functionSafeAtSource.ofCheckConversion functionConversion)
                    (inputSafeAtSource.ofCheckConversion inputConversion)⟩
              refine ⟨⟨certificate, ?_⟩⟩
              rfl

/-- Raw `matchAll` composition at the bounded-search boundary.  The caller
supplies only an evaluated initial-state producer tied to the exact enclosing
M4 component derivation.  Target, matcher, and body evaluation certificates
are reconstructed from their raw child plans at one shared `childFuel`.

The outer context is explicitly monomorphic because embedded callback
contexts use plain runtime types.  Body requests must be covered by the
retained binding index; this lets arbitrary successful search bindings and
the outer environment be combined without a completed-search equation. -/
theorem matchAll
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.matchAll targetExpression matcherExpression pattern bodyExpression)
      supply generated next)
    (childFuel bindingIndex resultIndex : Nat)
    (sourceTargets : List Ty)
    (contextEq : context = sourceTargets.map Scheme.mono)
    (targetInput matcherInput bodyInput : OriginEnvironmentDemand)
    (bodyInputCovered : ∀ position,
      OriginDemand.Le (bodyInput position) (.fuel bindingIndex))
    (targetCertificate : ∀ {childSupply generatedTarget afterTarget},
      ∀ targetElaboration : ElaboratesFuel signature staticFuel context
        targetExpression childSupply generatedTarget afterTarget,
      Nonempty (ExactRawOriginRequestCertificate targetElaboration childFuel
        (.fuel childFuel) targetInput))
    (matcherCertificate : ∀ {childSupply generatedMatcher afterMatcher},
      ∀ matcherElaboration : ElaboratesFuel signature staticFuel context
        matcherExpression childSupply generatedMatcher afterMatcher,
      Nonempty (ExactRawOriginRequestCertificate matcherElaboration childFuel
        (.fuel childFuel) matcherInput))
    (bodyCertificate : ∀ {bodyContext childSupply generatedBody afterBody},
      ∀ bodyElaboration : ElaboratesFuel signature staticFuel bodyContext
        bodyExpression childSupply generatedBody afterBody,
      Nonempty (ExactRawOriginRequestCertificate bodyElaboration childFuel
        (.fuel resultIndex) bodyInput))
    (matcherRuntimeType : ∀ {generatedTarget : Generated}
        {generatedPattern : GeneratedPattern} {generatedMatcher : Generated}
        {generatedBody : Generated},
      MatchAllElaboratesUsing (ElaboratesFuel signature staticFuel) signature
        context targetExpression matcherExpression pattern bodyExpression
        supply
        (Generated.fromMatchAll generatedTarget generatedPattern
          generatedMatcher generatedBody) next →
      ∀ solution,
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody).SemanticSolution solution →
      ∃ capability,
        generatedMatcher.target.apply solution =
          .matcher capability (generatedTarget.target.apply solution))
    (initialState : ∀ {generatedTarget : Generated}
        {generatedPattern : GeneratedPattern} {generatedMatcher : Generated}
        {generatedBody : Generated},
      MatchAllElaboratesUsing (ElaboratesFuel signature staticFuel) signature
        context targetExpression matcherExpression pattern bodyExpression
        supply
        (Generated.fromMatchAll generatedTarget generatedPattern
          generatedMatcher generatedBody) next →
      ∀ _compatible : SignatureCompatible signature.base,
      ∀ solution,
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody).SemanticSolution solution →
      ∀ environment,
      FuelEnvironmentSafe bindingIndex environment
        (Ty.applyList solution sourceTargets) →
      EvaluatedTwoIndexInitialStateTyping FuelEnvironmentSafe
        FuelEnvironmentSafe childFuel bindingIndex environment
        targetExpression matcherExpression pattern
        (Ty.applyList solution generatedPattern.bindings)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.fuel resultIndex)
      (OriginEnvironmentDemand.both targetInput
        (OriginEnvironmentDemand.both matcherInput
          (OriginEnvironmentDemand.fuel (fun _ => bindingIndex))))) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  cases elaboration with
  | mk targetElaboration patternElaboration matcherElaboration bodyElaboration =>
      rename_i generatedTarget afterTarget generatedPattern afterPattern
        generatedMatcher afterMatcher generatedBody
      obtain ⟨targetExact⟩ := targetCertificate targetElaboration
      obtain ⟨matcherExact⟩ := matcherCertificate matcherElaboration
      obtain ⟨bodyExact⟩ := bodyCertificate bodyElaboration
      let componentElaboration : MatchAllElaboratesUsing
          (ElaboratesFuel signature staticFuel) signature context
          targetExpression matcherExpression pattern bodyExpression supply
          (Generated.fromMatchAll generatedTarget generatedPattern
            generatedMatcher generatedBody) next :=
        .mk targetElaboration patternElaboration matcherElaboration
          bodyElaboration
      let inputDemand := OriginEnvironmentDemand.both targetInput
        (OriginEnvironmentDemand.both matcherInput
          (OriginEnvironmentDemand.fuel (fun _ => bindingIndex)))
      let certificate : RawOriginRequestCertificate parentElaboration
          (childFuel + 1) (.fuel resultIndex) :=
        ⟨inputDemand, by
          intro compatible solution semantic environment environmentSafe
          have contextCompatible : MonomorphicContextCompatible context
              (Ty.applyList solution sourceTargets) solution :=
            monomorphicContextCompatible_of_eq contextEq
          have targetSemantic := semanticSolution_fromMatchAll_target semantic
          have matcherSemantic := semanticSolution_fromMatchAll_matcher semantic
          have bodySemantic := semanticSolution_fromMatchAll_body semantic
          obtain ⟨matcherCapability, matcherTypeEq⟩ :=
            matcherRuntimeType componentElaboration solution semantic
          have targetSchemeSafe : SchemeOriginEnvironmentSafe targetInput
              solution environment context :=
            environmentSafe.mono (fun position => .fromLeft (.refl _))
          have matcherSchemeSafe : SchemeOriginEnvironmentSafe matcherInput
              solution environment context :=
            environmentSafe.mono (fun position =>
              .fromRight (.fromLeft (.refl _)))
          have outerFuelSchemeSafe : SchemeOriginEnvironmentSafe
              (OriginEnvironmentDemand.fuel (fun _ => bindingIndex)) solution
              environment context :=
            environmentSafe.mono (fun position =>
              .fromRight (.fromRight (.refl _)))
          have targetEnvironmentSafe :=
            SchemeOriginEnvironmentSafe.toOriginEnvironmentSafe
              targetSchemeSafe contextCompatible
          have matcherEnvironmentSafe :=
            SchemeOriginEnvironmentSafe.toOriginEnvironmentSafe
              matcherSchemeSafe contextCompatible
          have outerFuelEnvironmentSafe :=
            OriginEnvironmentSafe.toFuelEnvironmentSafe
              (SchemeOriginEnvironmentSafe.toOriginEnvironmentSafe
                outerFuelSchemeSafe contextCompatible)
          have bodyContextCompatible : MonomorphicContextCompatible
              (Pattern.extendContext generatedPattern.bindings context)
              (Ty.applyList solution generatedPattern.bindings ++
                Ty.applyList solution sourceTargets) solution := by
            simpa [Pattern.extendContext] using
              monomorphicContextCompatible_prepend generatedPattern.bindings
                contextCompatible
          let targetEmbedded : RawOriginEmbeddedCertificate childFuel []
              (Ty.applyList solution sourceTargets) targetExpression
              (generatedTarget.target.apply solution) (.fuel childFuel)
              targetInput := by
            intro bindings embeddedEnvironment embeddedSafe
            exact targetExact.certificate.preserves compatible solution
              targetSemantic (bindings ++ embeddedEnvironment)
              (by simpa [targetExact.input_eq] using
                embeddedSafe.toSchemeOrigin contextCompatible)
          let matcherEmbedded : RawOriginEmbeddedCertificate childFuel []
              (Ty.applyList solution sourceTargets) matcherExpression
              (.matcher matcherCapability
                (generatedTarget.target.apply solution))
              (.fuel childFuel) matcherInput := by
            intro bindings embeddedEnvironment embeddedSafe
            have sourceSafe := matcherExact.certificate.preserves compatible solution
                matcherSemantic (bindings ++ embeddedEnvironment)
                (by simpa [matcherExact.input_eq] using
                  embeddedSafe.toSchemeOrigin contextCompatible)
            simpa [matcherTypeEq] using sourceSafe
          let bodyEmbedded : RawOriginEmbeddedCertificate childFuel
              (Ty.applyList solution generatedPattern.bindings)
              (Ty.applyList solution sourceTargets) bodyExpression
              (generatedBody.target.apply solution) (.fuel resultIndex)
              bodyInput := by
            intro bindings embeddedEnvironment embeddedSafe
            exact bodyExact.certificate.preserves compatible solution
              bodySemantic (bindings ++ embeddedEnvironment)
              (by simpa [bodyExact.input_eq] using
                embeddedSafe.toSchemeOrigin bodyContextCompatible)
          let runtimeCertificate : FuelEmbeddedMatchAllRuntimeCertificate
              RawOriginEmbeddedCertificate childFuel bindingIndex resultIndex
              (Ty.applyList solution sourceTargets) environment targetExpression
              matcherExpression pattern bodyExpression
              (generatedTarget.target.apply solution)
              (generatedBody.target.apply solution)
              matcherCapability
              (Ty.applyList solution generatedPattern.bindings) :=
            { targetInput := targetInput
              targetCertificate := targetEmbedded
              targetEnvironmentSafe := targetEnvironmentSafe
              matcherInput := matcherInput
              matcherCertificate := matcherEmbedded
              matcherEnvironmentSafe := matcherEnvironmentSafe
              initialTyped := initialState componentElaboration
                compatible solution semantic environment outerFuelEnvironmentSafe
              bodyInput := bodyInput
              bodyCertificate := bodyEmbedded
              bodyEnvironmentSafe := by
                intro bindings bindingsSafe
                have combinedFuelSafe := bindingsSafe.append
                  outerFuelEnvironmentSafe
                exact OriginEnvironmentSafe.mono
                  (FuelEnvironmentSafe.toOriginEnvironmentSafe
                    combinedFuelSafe)
                  bodyInputCovered }
          simpa [Generated.fromMatchAll, DataTypes.list, Ty.apply,
            Ty.applyList] using
            runtimeCertificate.eval_originResultSafe
              rawOriginEmbeddedEvaluatorSafe⟩
      exact ⟨⟨certificate, rfl⟩⟩

/-- Raw `matchFirst` composition at the common-fuel runtime boundary.  The
ordinary arms remain in source order and carry their own binding types and
body demands through `RawOriginMatchFirstTailPlan`; the fallback is evaluated
in the original environment. -/
theorem matchFirst
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.matchFirst targetExpression matcherExpression arms fallbackExpression)
      supply generated next)
    (childFuel bindingIndex resultIndex : Nat)
    (sourceTargets : List Ty)
    (contextEq : context = sourceTargets.map Scheme.mono)
    (targetInput matcherInput fallbackInput : OriginEnvironmentDemand)
    (targetCertificate : ∀ {childSupply generatedTarget afterTarget},
      ∀ targetElaboration : ElaboratesFuel signature staticFuel context
        targetExpression childSupply generatedTarget afterTarget,
      Nonempty (ExactRawOriginRequestCertificate targetElaboration childFuel
        (.fuel childFuel) targetInput))
    (matcherCertificate : ∀ {childSupply generatedMatcher afterMatcher},
      ∀ matcherElaboration : ElaboratesFuel signature staticFuel context
        matcherExpression childSupply generatedMatcher afterMatcher,
      Nonempty (ExactRawOriginRequestCertificate matcherElaboration childFuel
        (.fuel childFuel) matcherInput))
    (fallbackCertificate : ∀ {childSupply generatedFallback afterFallback},
      ∀ fallbackElaboration : ElaboratesFuel signature staticFuel context
        fallbackExpression childSupply generatedFallback afterFallback,
      Nonempty (ExactRawOriginRequestCertificate fallbackElaboration childFuel
        (.fuel resultIndex) fallbackInput))
    (matcherRuntimeType : ∀ {generatedTarget generatedMatcher : Generated}
        {generatedArms : MatchFirstTyping.GeneratedArms},
      MatchFirstTyping.ElaboratesUsing
        (ElaboratesFuel signature staticFuel) signature context
        (.matchFirst targetExpression matcherExpression arms fallbackExpression)
        supply
        (MatchFirstTyping.Generated.fromMatchFirst generatedTarget
          generatedMatcher generatedArms) next →
      ∀ solution,
      (MatchFirstTyping.Generated.fromMatchFirst generatedTarget generatedMatcher
        generatedArms).SemanticSolution solution →
      ∃ capability,
        generatedMatcher.target.apply solution =
          .matcher capability (generatedTarget.target.apply solution))
    (armsRuntimeSafe : ∀ {generatedTarget generatedMatcher generatedFallback : Generated}
        {generatedTail : MatchFirstTyping.GeneratedTail}
        {afterTarget afterMatcher afterFallback : Supply},
      ∀ _targetElaboration : ElaboratesFuel signature staticFuel context
        targetExpression supply generatedTarget afterTarget,
      ∀ _matcherElaboration : ElaboratesFuel signature staticFuel context
        matcherExpression afterTarget generatedMatcher afterMatcher,
      ∀ _fallbackElaboration : ElaboratesFuel signature staticFuel context
        fallbackExpression afterMatcher generatedFallback afterFallback,
      ∀ _tailElaboration : MatchFirstTyping.TailElaboratesUsing
        (ElaboratesFuel signature staticFuel) signature context
        generatedTarget.target generatedMatcher.target generatedFallback.target
        arms afterFallback generatedTail next,
      ∀ _compatible : SignatureCompatible signature.base,
      ∀ solution, generatedTail.SemanticSolution solution →
      MonomorphicContextCompatible context
        (Ty.applyList solution sourceTargets) solution →
      ∀ environment,
      FuelEnvironmentSafe bindingIndex environment
        (Ty.applyList solution sourceTargets) →
      FuelResultSafe resultIndex (generatedFallback.target.apply solution)
        (evalFuel childFuel environment fallbackExpression) →
      ∀ targetValue matcherValue,
      TwoIndexMatchFirstArmsSafe childFuel bindingIndex resultIndex environment
        targetValue matcherValue (generatedFallback.target.apply solution) arms
        fallbackExpression) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.fuel resultIndex)
      (OriginEnvironmentDemand.both targetInput
        (OriginEnvironmentDemand.both matcherInput
          (OriginEnvironmentDemand.both fallbackInput
            (OriginEnvironmentDemand.fuel (fun _ => bindingIndex)))))) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  cases elaboration with
  | matchFirst targetElaboration matcherElaboration armsElaboration =>
      cases armsElaboration with
      | fromFallback fallbackElaboration tailElaboration =>
          rename_i generatedTarget afterTarget generatedMatcher afterMatcher
            first rest generatedFallback afterFallback generatedTail
          obtain ⟨targetExact⟩ := targetCertificate targetElaboration
          obtain ⟨matcherExact⟩ := matcherCertificate matcherElaboration
          obtain ⟨fallbackExact⟩ := fallbackCertificate fallbackElaboration
          let componentElaboration : MatchFirstTyping.ElaboratesUsing
              (ElaboratesFuel signature staticFuel) signature context
              (.matchFirst targetExpression matcherExpression (first :: rest)
                fallbackExpression) supply
              (MatchFirstTyping.Generated.fromMatchFirst generatedTarget
                generatedMatcher
                (MatchFirstTyping.GeneratedArms.fromFallback generatedFallback
                  generatedTail)) next :=
            .matchFirst targetElaboration matcherElaboration
              (.fromFallback fallbackElaboration tailElaboration)
          let inputDemand := OriginEnvironmentDemand.both targetInput
            (OriginEnvironmentDemand.both matcherInput
              (OriginEnvironmentDemand.both fallbackInput
                (OriginEnvironmentDemand.fuel (fun _ => bindingIndex))))
          let certificate : RawOriginRequestCertificate parentElaboration
              (childFuel + 1) (.fuel resultIndex) :=
            ⟨inputDemand, by
              intro compatible solution semantic environment environmentSafe
              have contextCompatible : MonomorphicContextCompatible context
                  (Ty.applyList solution sourceTargets) solution :=
                monomorphicContextCompatible_of_eq contextEq
              have targetSemantic := semanticSolution_fromMatchFirst_target semantic
              have matcherSemantic := semanticSolution_fromMatchFirst_matcher semantic
              have armsSemantic := semanticSolution_fromMatchFirst_arms semantic
              have fallbackSemantic :=
                semanticSolution_fromMatchFirst_fallback armsSemantic
              have tailSemantic := semanticSolution_fromMatchFirst_tail armsSemantic
              obtain ⟨matcherCapability, matcherTypeEq⟩ :=
                matcherRuntimeType componentElaboration solution semantic
              have targetSchemeSafe : SchemeOriginEnvironmentSafe targetInput
                  solution environment context :=
                environmentSafe.mono (fun position => .fromLeft (.refl _))
              have matcherSchemeSafe : SchemeOriginEnvironmentSafe matcherInput
                  solution environment context :=
                environmentSafe.mono (fun position =>
                  .fromRight (.fromLeft (.refl _)))
              have fallbackSchemeSafe : SchemeOriginEnvironmentSafe fallbackInput
                  solution environment context :=
                environmentSafe.mono (fun position =>
                  .fromRight (.fromRight (.fromLeft (.refl _))))
              have outerFuelSchemeSafe : SchemeOriginEnvironmentSafe
                  (OriginEnvironmentDemand.fuel (fun _ => bindingIndex)) solution
                  environment context :=
                environmentSafe.mono (fun position =>
                  .fromRight (.fromRight (.fromRight (.refl _))))
              have targetEnvironmentSafe :=
                SchemeOriginEnvironmentSafe.toOriginEnvironmentSafe
                  targetSchemeSafe contextCompatible
              have matcherEnvironmentSafe :=
                SchemeOriginEnvironmentSafe.toOriginEnvironmentSafe
                  matcherSchemeSafe contextCompatible
              have outerFuelEnvironmentSafe :=
                OriginEnvironmentSafe.toFuelEnvironmentSafe
                  (SchemeOriginEnvironmentSafe.toOriginEnvironmentSafe
                    outerFuelSchemeSafe contextCompatible)
              let targetEmbedded : RawOriginEmbeddedCertificate childFuel []
                  (Ty.applyList solution sourceTargets) targetExpression
                  (generatedTarget.target.apply solution) (.fuel childFuel)
                  targetInput := by
                intro bindings embeddedEnvironment embeddedSafe
                exact targetExact.certificate.preserves compatible solution
                  targetSemantic (bindings ++ embeddedEnvironment)
                  (by simpa [targetExact.input_eq] using
                    embeddedSafe.toSchemeOrigin contextCompatible)
              let matcherEmbedded : RawOriginEmbeddedCertificate childFuel []
                  (Ty.applyList solution sourceTargets) matcherExpression
                  (.matcher matcherCapability
                    (generatedTarget.target.apply solution))
                  (.fuel childFuel) matcherInput := by
                intro bindings embeddedEnvironment embeddedSafe
                have sourceSafe := matcherExact.certificate.preserves compatible
                  solution matcherSemantic (bindings ++ embeddedEnvironment)
                  (by simpa [matcherExact.input_eq] using
                    embeddedSafe.toSchemeOrigin contextCompatible)
                simpa [matcherTypeEq] using sourceSafe
              have fallbackResult := fallbackExact.certificate.preserves
                compatible solution fallbackSemantic environment
                (by simpa [fallbackExact.input_eq] using fallbackSchemeSafe)
              let runtimeCertificate : FuelEmbeddedMatchFirstRuntimeCertificate
                  RawOriginEmbeddedCertificate childFuel bindingIndex resultIndex
                  (Ty.applyList solution sourceTargets) environment targetExpression
                  matcherExpression (first :: rest) fallbackExpression
                  (generatedTarget.target.apply solution)
                  (generatedFallback.target.apply solution) matcherCapability :=
                { targetInput := targetInput
                  targetCertificate := targetEmbedded
                  targetEnvironmentSafe := targetEnvironmentSafe
                  matcherInput := matcherInput
                  matcherCertificate := matcherEmbedded
                  matcherEnvironmentSafe := matcherEnvironmentSafe
                  armsSafe := by
                    intro targetValue matcherValue _targetSuccess _matcherSuccess
                    exact armsRuntimeSafe targetElaboration matcherElaboration
                      fallbackElaboration tailElaboration compatible solution
                      tailSemantic contextCompatible environment
                      outerFuelEnvironmentSafe fallbackResult.toFuel targetValue
                      matcherValue }
              simpa [MatchFirstTyping.Generated.fromMatchFirst,
                MatchFirstTyping.GeneratedArms.fromFallback] using
                runtimeCertificate.eval_originResultSafe
                  rawOriginEmbeddedEvaluatorSafe⟩
          exact ⟨⟨certificate, rfl⟩⟩

end ExactRawOriginRequestCertificate

/-- Canonical result shapes implemented by the runtime constructor evaluator.
The field-demand list is separate from expression plans, so this judgment
contains no semantic solution, runtime value, or evaluation result. -/
inductive RawOriginConstructorResultPlan :
    DataCtor → List OriginDemand → OriginDemand → Prop where
  | boolTrue : RawOriginConstructorResultPlan DataCtor.true [] .bool
  | boolFalse : RawOriginConstructorResultPlan DataCtor.false [] .bool
  | boolTrueFuel : RawOriginConstructorResultPlan DataCtor.true []
      (.fuel resultIndex)
  | boolFalseFuel : RawOriginConstructorResultPlan DataCtor.false []
      (.fuel resultIndex)
  | listNil : RawOriginConstructorResultPlan DataCtor.nil [] (.listOf element)
  | listCons : RawOriginConstructorResultPlan DataCtor.cons
      [element, .listOf element] (.listOf element)
  | listNilFuel : RawOriginConstructorResultPlan DataCtor.nil []
      (.fuel resultIndex)
  | listConsFuel : RawOriginConstructorResultPlan DataCtor.cons
      [.fuel resultIndex, .listOf (.fuel resultIndex)] (.fuel resultIndex)

namespace RawOriginConstructorResultPlan

private theorem listOfValueSafe_fuelItems
    (safe : ListOfValueSafe
      (fun value target => FuelValueSafe resultIndex value target)
      value target) :
    ∃ values element,
      value = Value.buildList values ∧ target = DataTypes.list element ∧
      ∀ item ∈ values, FuelValueSafe resultIndex item element := by
  induction safe with
  | nil => exact ⟨[], _, rfl, rfl, by simp⟩
  | @cons head element values headSafe tailSafe tailIH =>
      obtain ⟨tailValues, tailElement, tailValueEq, tailTypeEq,
        tailItems⟩ := tailIH
      have valuesEq : values = tailValues := by
        have viewed := congrArg Value.viewList tailValueEq
        simpa using viewed
      have elementEq : element = tailElement := by
        have argumentsEq := (Ty.data.inj tailTypeEq).2
        simpa [DataTypes.list] using argumentsEq
      subst values
      subst element
      exact ⟨head :: tailValues, tailElement, rfl, rfl, by
        intro item membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | membership
        · exact headSafe
        · exact tailItems item membership⟩

private theorem fuelValueSafe_of_listOfFuel
    (safe : OriginValueSafe (.listOf (.fuel resultIndex)) value target) :
    FuelValueSafe resultIndex value target := by
  simp only [OriginValueSafe] at safe
  have fuelItems : ListOfValueSafe
      (fun item itemTarget => FuelValueSafe resultIndex item itemTarget)
      value target := by
    simpa only [OriginValueSafe] using safe
  obtain ⟨values, element, rfl, rfl, itemsSafe⟩ :=
    listOfValueSafe_fuelItems fuelItems
  exact fuelValueSafe_list_of_forall element resultIndex values itemsSafe

private theorem fuelValueSafe_boolValue (value : Bool) (resultIndex : Nat) :
    FuelValueSafe resultIndex (Value.boolValue value) DataTypes.bool := by
  cases value <;> simp [Value.boolValue, fuelValueSafe_boolTrue,
    fuelValueSafe_boolFalse]

/-- Reassemble a structurally demanded constructor result from the solved
domains and safe runtime fields supplied by the curried-call companion. -/
theorem valueSafe
    (plan : RawOriginConstructorResultPlan constructor demands outputDemand)
    (compatible : SignatureCompatible signature.base)
    (lookup : signature.base.lookupDataConstructor constructor = some scheme)
    (semantic : TypePM.Generated.SemanticSolution generated solution)
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      ⟨(scheme.instantiate supply).1, [], []⟩ arguments
      (scheme.instantiate supply).2 generated next)
    (callSemantic : CurriedCallSemantic solution call expectedTypes)
    (valuesSafe : OriginValueSafes demands values expectedTypes) :
    OriginValueSafe outputDemand (.data constructor values)
      (generated.target.apply solution) := by
  cases plan with
  | boolTrue =>
      rw [compatible.boolTrue] at lookup
      cases lookup
      cases valuesSafe
      cases callSemantic
      simpa [Source.ConstructorSchemes.instantiate_boolTrue, Ty.apply,
        Ty.applyList, DataTypes.bool] using OriginValueSafe.boolTrue
  | boolFalse =>
      rw [compatible.boolFalse] at lookup
      cases lookup
      cases valuesSafe
      cases callSemantic
      simpa [Source.ConstructorSchemes.instantiate_boolFalse, Ty.apply,
        Ty.applyList, DataTypes.bool] using OriginValueSafe.boolFalse
  | @boolTrueFuel resultIndex =>
      rw [compatible.boolTrue] at lookup
      cases lookup
      cases valuesSafe
      cases callSemantic
      simpa [Source.ConstructorSchemes.instantiate_boolTrue, Ty.apply,
        Ty.applyList, DataTypes.bool] using
        (OriginValueSafe.ofFuel (fuelValueSafe_boolTrue resultIndex))
  | @boolFalseFuel resultIndex =>
      rw [compatible.boolFalse] at lookup
      cases lookup
      cases valuesSafe
      cases callSemantic
      simpa [Source.ConstructorSchemes.instantiate_boolFalse, Ty.apply,
        Ty.applyList, DataTypes.bool] using
        (OriginValueSafe.ofFuel (fuelValueSafe_boolFalse resultIndex))
  | @listNil element =>
      rw [compatible.listNil] at lookup
      cases lookup
      cases valuesSafe
      cases callSemantic
      simpa [Source.ConstructorSchemes.instantiate_listNil, Ty.apply,
        Ty.applyList, DataTypes.list, Value.buildList, Value.nilValue] using
        (OriginValueSafe.listNil (elementDemand := element)
          (elementType := solution.ty ⟨supply.ty⟩))
  | @listCons element =>
      rw [compatible.listCons] at lookup
      cases lookup
      cases valuesSafe with
      | cons headSafe valuesSafe =>
          cases valuesSafe with
          | cons tailSafe valuesSafe =>
              cases valuesSafe
              cases callSemantic with
              | cons tailSemantic _initialSemantic _headSemantic firstEquation
                  _headConversion =>
                  cases tailSemantic with
                  | cons tailSemantic _firstSemantic _tailValueSemantic
                      secondEquation _tailConversion =>
                      cases tailSemantic
                      simp only [Equation.Holds,
                        Source.ConstructorSchemes.instantiate_listCons,
                        Ty.apply] at firstEquation
                      simp only [Equation.Holds, Source.Generated.fromApp,
                        Ty.apply] at secondEquation
                      have firstParts := Ty.fn.inj firstEquation
                      rw [← firstParts.2] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      simp only [Ty.apply] at headSafe tailSafe
                      simp only [Source.Generated.fromApp, Ty.apply]
                      rw [← firstParts.1] at headSafe
                      rw [← secondParts.1] at tailSafe
                      rw [← secondParts.2]
                      simp only [OriginValueSafe] at tailSafe ⊢
                      cases tailSafe with
                      | nil => exact .cons headSafe .nil
                      | cons tailHead tailTail =>
                          exact .cons headSafe (.cons tailHead tailTail)
  | @listNilFuel resultIndex =>
      rw [compatible.listNil] at lookup
      cases lookup
      cases valuesSafe
      cases callSemantic
      simpa [Source.ConstructorSchemes.instantiate_listNil, Ty.apply,
        Ty.applyList, DataTypes.list, Value.buildList, Value.nilValue] using
        (OriginValueSafe.ofFuel
          (fuelValueSafe_list_of_forall (solution.ty ⟨supply.ty⟩)
            resultIndex [] (by simp)))
  | @listConsFuel resultIndex =>
      rw [compatible.listCons] at lookup
      cases lookup
      cases valuesSafe with
      | cons headSafe valuesSafe =>
          cases valuesSafe with
          | cons tailSafe valuesSafe =>
              cases valuesSafe
              cases callSemantic with
              | cons tailSemantic _initialSemantic _headSemantic firstEquation
                  _headConversion =>
                  cases tailSemantic with
                  | cons tailSemantic _firstSemantic _tailValueSemantic
                      secondEquation _tailConversion =>
                      cases tailSemantic
                      simp only [Equation.Holds,
                        Source.ConstructorSchemes.instantiate_listCons,
                        Ty.apply] at firstEquation
                      simp only [Equation.Holds, Source.Generated.fromApp,
                        Ty.apply] at secondEquation
                      have firstParts := Ty.fn.inj firstEquation
                      rw [← firstParts.2] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      simp only [Ty.apply] at headSafe tailSafe
                      simp only [Source.Generated.fromApp, Ty.apply]
                      rw [← firstParts.1] at headSafe
                      rw [← secondParts.1] at tailSafe
                      rw [← secondParts.2]
                      have headFuelSafe := headSafe.toFuel
                      simp only [OriginValueSafe] at tailSafe
                      cases tailSafe with
                      | nil =>
                          exact OriginValueSafe.ofFuel
                            (fuelValueSafe_of_listOfFuel (by
                              simp only [OriginValueSafe]
                              exact .cons headFuelSafe .nil))
                      | cons tailHead tailTail =>
                          exact OriginValueSafe.ofFuel
                            (fuelValueSafe_of_listOfFuel (by
                              simp only [OriginValueSafe]
                              exact .cons headFuelSafe
                                (.cons tailHead tailTail)))

end RawOriginConstructorResultPlan

/-- First-order primitive result shapes justified directly by the runtime
delta rules. -/
inductive RawOriginPrimitiveResultPlan :
    PrimOp → List OriginDemand → OriginDemand → Prop where
  | add : RawOriginPrimitiveResultPlan .add [.int, .int] .int
  | addFuel : RawOriginPrimitiveResultPlan .add [.int, .int]
      (.fuel resultIndex)
  | member : RawOriginPrimitiveResultPlan .member
      [.none, .listOf element] .bool
  | memberFuel : RawOriginPrimitiveResultPlan .member
      [.none, .listOf .none] (.fuel resultIndex)
  | deleteFirst : RawOriginPrimitiveResultPlan .deleteFirst
      [.none, .listOf element] (.listOf element)
  | deleteFirstFuel : RawOriginPrimitiveResultPlan .deleteFirst
      [.none, .listOf (.fuel resultIndex)] (.fuel resultIndex)

namespace RawOriginPrimitiveResultPlan

theorem resultSafe
    (plan : RawOriginPrimitiveResultPlan operation demands outputDemand)
    (compatible : SignatureCompatible signature.base)
    (lookup : signature.base.lookupPrimitive operation = some scheme)
    (semantic : TypePM.Generated.SemanticSolution generated solution)
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      ⟨(scheme.instantiate supply).1, [], []⟩ arguments
      (scheme.instantiate supply).2 generated next)
    (callSemantic : CurriedCallSemantic solution call expectedTypes)
    (valuesSafe : OriginValueSafes demands values expectedTypes) :
    FuelResultSafeWith
      (fun value => OriginValueSafe outputDemand value
        (generated.target.apply solution))
      (evalPrimitive (applyFuel operationalFuel) operation values) := by
  cases plan with
  | add =>
      rw [compatible.add] at lookup
      cases lookup
      cases valuesSafe with
      | cons leftSafe valuesSafe =>
          cases valuesSafe with
          | cons rightSafe valuesSafe =>
              cases valuesSafe
              cases callSemantic with
              | cons tailSemantic _initialSemantic _leftSemantic firstEquation
                  _leftConversion =>
                  cases tailSemantic with
                  | cons tailSemantic _firstSemantic _rightSemantic
                      secondEquation _rightConversion =>
                      cases tailSemantic
                      simp only [Equation.Holds,
                        Source.PrimitiveSchemes.instantiate_add,
                        Ty.apply] at firstEquation
                      simp only [Equation.Holds, Source.Generated.fromApp,
                        Ty.apply] at secondEquation
                      have firstParts := Ty.fn.inj firstEquation
                      rw [← firstParts.2] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      simp only [Ty.apply] at leftSafe rightSafe
                      rw [← firstParts.1] at leftSafe
                      rw [← secondParts.1] at rightSafe
                      simp only [OriginValueSafe] at leftSafe rightSafe
                      cases leftSafe
                      cases rightSafe
                      simp only [Source.Generated.fromApp, Ty.apply]
                      rw [← secondParts.2]
                      exact .inr ⟨_, rfl, OriginValueSafe.int _⟩
  | @addFuel resultIndex =>
      rw [compatible.add] at lookup
      cases lookup
      cases valuesSafe with
      | cons leftSafe valuesSafe =>
          cases valuesSafe with
          | cons rightSafe valuesSafe =>
              cases valuesSafe
              cases callSemantic with
              | cons tailSemantic _initialSemantic _leftSemantic firstEquation
                  _leftConversion =>
                  cases tailSemantic with
                  | cons tailSemantic _firstSemantic _rightSemantic
                      secondEquation _rightConversion =>
                      cases tailSemantic
                      simp only [Equation.Holds,
                        Source.PrimitiveSchemes.instantiate_add,
                        Ty.apply] at firstEquation
                      simp only [Equation.Holds, Source.Generated.fromApp,
                        Ty.apply] at secondEquation
                      have firstParts := Ty.fn.inj firstEquation
                      rw [← firstParts.2] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      simp only [Ty.apply] at leftSafe rightSafe
                      rw [← firstParts.1] at leftSafe
                      rw [← secondParts.1] at rightSafe
                      simp only [OriginValueSafe] at leftSafe rightSafe
                      cases leftSafe
                      cases rightSafe
                      simp only [Source.Generated.fromApp, Ty.apply]
                      rw [← secondParts.2]
                      exact .inr ⟨_, rfl, OriginValueSafe.ofFuel
                        (fuelValueSafe_int _ resultIndex)⟩
  | @member element =>
      rw [compatible.member] at lookup
      cases lookup
      cases valuesSafe with
      | @cons _ needleValue _ _ _ _ _needleSafe valuesSafe =>
          cases valuesSafe with
          | cons listSafe valuesSafe =>
              cases valuesSafe
              cases callSemantic with
              | cons tailSemantic _initialSemantic _needleSemantic firstEquation
                  _needleConversion =>
                  cases tailSemantic with
                  | cons tailSemantic _firstSemantic _listSemantic
                      secondEquation _listConversion =>
                      cases tailSemantic
                      simp only [Equation.Holds,
                        Source.PrimitiveSchemes.instantiate_member,
                        Ty.apply] at firstEquation
                      simp only [Equation.Holds, Source.Generated.fromApp,
                        Ty.apply] at secondEquation
                      have firstParts := Ty.fn.inj firstEquation
                      rw [← firstParts.2] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      simp only [Ty.apply] at listSafe
                      rw [← secondParts.1] at listSafe
                      simp only [Source.Generated.fromApp, Ty.apply]
                      rw [← secondParts.2]
                      simp only [OriginValueSafe] at listSafe
                      cases listSafe with
                      | nil =>
                          refine .inr ⟨Value.boolValue
                            (Value.memberStructural needleValue []), ?_,
                            OriginValueSafe.boolValue _⟩
                          simp [evalPrimitive]
                      | @cons listHead elementType items head tail =>
                          refine .inr ⟨Value.boolValue
                            (Value.memberStructural needleValue
                              (listHead :: items)), ?_,
                            OriginValueSafe.boolValue _⟩
                          simp [evalPrimitive]
  | @memberFuel resultIndex =>
      rw [compatible.member] at lookup
      cases lookup
      cases valuesSafe with
      | @cons _ needleValue _ _ _ _ _needleSafe valuesSafe =>
          cases valuesSafe with
          | cons listSafe valuesSafe =>
              cases valuesSafe
              cases callSemantic with
              | cons tailSemantic _initialSemantic _needleSemantic firstEquation
                  _needleConversion =>
                  cases tailSemantic with
                  | cons tailSemantic _firstSemantic _listSemantic
                      secondEquation _listConversion =>
                      cases tailSemantic
                      simp only [Equation.Holds,
                        Source.PrimitiveSchemes.instantiate_member,
                        Ty.apply] at firstEquation
                      simp only [Equation.Holds, Source.Generated.fromApp,
                        Ty.apply] at secondEquation
                      have firstParts := Ty.fn.inj firstEquation
                      rw [← firstParts.2] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      simp only [Ty.apply] at listSafe
                      rw [← secondParts.1] at listSafe
                      simp only [Source.Generated.fromApp, Ty.apply]
                      rw [← secondParts.2]
                      simp only [OriginValueSafe] at listSafe
                      cases listSafe with
                      | nil =>
                          refine .inr ⟨Value.boolValue
                            (Value.memberStructural needleValue []), ?_,
                            OriginValueSafe.ofFuel
                              (RawOriginConstructorResultPlan.fuelValueSafe_boolValue
                                _ resultIndex)⟩
                          simp [evalPrimitive]
                      | @cons listHead elementType items head tail =>
                          refine .inr ⟨Value.boolValue
                            (Value.memberStructural needleValue
                              (listHead :: items)), ?_,
                            OriginValueSafe.ofFuel
                              (RawOriginConstructorResultPlan.fuelValueSafe_boolValue
                                _ resultIndex)⟩
                          simp [evalPrimitive]
  | @deleteFirst element =>
      rw [compatible.deleteFirst] at lookup
      cases lookup
      cases valuesSafe with
      | @cons _ needleValue _ _ _ _ _needleSafe valuesSafe =>
          cases valuesSafe with
          | cons listSafe valuesSafe =>
              cases valuesSafe
              cases callSemantic with
              | cons tailSemantic _initialSemantic _needleSemantic firstEquation
                  _needleConversion =>
                  cases tailSemantic with
                  | cons tailSemantic _firstSemantic _listSemantic
                      secondEquation _listConversion =>
                      cases tailSemantic
                      simp only [Equation.Holds,
                        Source.PrimitiveSchemes.instantiate_deleteFirst,
                        Ty.apply] at firstEquation
                      simp only [Equation.Holds, Source.Generated.fromApp,
                        Ty.apply] at secondEquation
                      have firstParts := Ty.fn.inj firstEquation
                      rw [← firstParts.2] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      simp only [Ty.apply] at listSafe
                      rw [← secondParts.1] at listSafe
                      simp only [Source.Generated.fromApp, Ty.apply]
                      rw [← secondParts.2]
                      simp only [OriginValueSafe] at listSafe
                      obtain ⟨items, encoding⟩ := listSafe.existsViewList
                      have deletedSafe := listSafe.deleteFirstStructural
                        encoding (needle := needleValue)
                      exact .inr ⟨Value.buildList
                        (Value.deleteFirstStructural needleValue items), by
                        simp [evalPrimitive, encoding], by
                        simpa only [OriginValueSafe] using deletedSafe⟩
  | @deleteFirstFuel resultIndex =>
      rw [compatible.deleteFirst] at lookup
      cases lookup
      cases valuesSafe with
      | @cons _ needleValue _ _ _ _ _needleSafe valuesSafe =>
          cases valuesSafe with
          | cons listSafe valuesSafe =>
              cases valuesSafe
              cases callSemantic with
              | cons tailSemantic _initialSemantic _needleSemantic firstEquation
                  _needleConversion =>
                  cases tailSemantic with
                  | cons tailSemantic _firstSemantic _listSemantic
                      secondEquation _listConversion =>
                      cases tailSemantic
                      simp only [Equation.Holds,
                        Source.PrimitiveSchemes.instantiate_deleteFirst,
                        Ty.apply] at firstEquation
                      simp only [Equation.Holds, Source.Generated.fromApp,
                        Ty.apply] at secondEquation
                      have firstParts := Ty.fn.inj firstEquation
                      rw [← firstParts.2] at secondEquation
                      have secondParts := Ty.fn.inj secondEquation
                      simp only [Ty.apply] at listSafe
                      rw [← secondParts.1] at listSafe
                      simp only [Source.Generated.fromApp, Ty.apply]
                      rw [← secondParts.2]
                      simp only [OriginValueSafe] at listSafe
                      obtain ⟨items, encoding⟩ := listSafe.existsViewList
                      have deletedSafe := listSafe.deleteFirstStructural
                        encoding (needle := needleValue)
                      exact .inr ⟨Value.buildList
                        (Value.deleteFirstStructural needleValue items), by
                        simp [evalPrimitive, encoding],
                        OriginValueSafe.ofFuel
                          (RawOriginConstructorResultPlan.fuelValueSafe_of_listOfFuel (by
                            simpa only [OriginValueSafe] using deletedSafe))⟩

end RawOriginPrimitiveResultPlan

namespace ExactRawOriginRequestCertificate

/-- Conditional producer.  Static elaboration is a normalized three-argument
call, whereas runtime evaluation observes the condition and exactly one
branch; the proof keeps those two orders explicitly synchronized. -/
theorem ifE
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.ifE condition thenBranch elseBranch) supply generated next)
    (childFuel : Nat) (outputDemand : OriginDemand)
    (conditionInput thenInput elseInput : OriginEnvironmentDemand)
    (conditionCertificate : ∀ generatedCondition afterCondition,
      ∀ conditionElaboration : ElaboratesFuel signature staticFuel context
        condition (conditionalScheme.instantiate supply).2
        generatedCondition afterCondition,
        Nonempty (ExactRawOriginRequestCertificate conditionElaboration
          childFuel .bool conditionInput))
    (thenCertificate : ∀ (afterCondition : Supply) (generatedThen : Generated)
        (afterThen : Supply),
      ∀ thenElaboration : ElaboratesFuel signature staticFuel context
        thenBranch (afterCondition.nextTy 2) generatedThen afterThen,
        Nonempty (ExactRawOriginRequestCertificate thenElaboration childFuel
          outputDemand thenInput))
    (elseCertificate : ∀ (afterThen : Supply)
        (generatedElse : Generated) (afterElse : Supply),
      ∀ elseElaboration : ElaboratesFuel signature staticFuel context
        elseBranch (afterThen.nextTy 2) generatedElse afterElse,
        Nonempty (ExactRawOriginRequestCertificate elseElaboration childFuel
          outputDemand elseInput)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      outputDemand
      (OriginEnvironmentDemand.both conditionInput
        (OriginEnvironmentDemand.both thenInput elseInput))) := by
  cases elaboration with
  | @cons accumulated argument arguments callSupply generatedCondition
      afterCondition generated next conditionElaboration rest =>
      cases rest with
      | @cons accumulated argument arguments callSupply generatedThen afterThen
          callGenerated callNext thenElaboration rest =>
          cases rest with
          | @cons accumulated argument arguments callSupply generatedElse
              afterElse callGenerated callNext elseElaboration rest =>
              cases rest
              obtain ⟨conditionExact⟩ := conditionCertificate _ _
                conditionElaboration
              obtain ⟨thenExact⟩ := thenCertificate _ _ _
                thenElaboration
              obtain ⟨elseExact⟩ := elseCertificate _ _ _
                elseElaboration
              let conditionCert := conditionExact.certificate
              let thenCert := thenExact.certificate
              let elseCert := elseExact.certificate
              let inputDemand := OriginEnvironmentDemand.both
                conditionCert.inputDemand
                (OriginEnvironmentDemand.both thenCert.inputDemand
                  elseCert.inputDemand)
              let certificate : RawOriginRequestCertificate
                  (show ElaboratesFuel signature (staticFuel + 1) context
                    (.ifE condition thenBranch elseBranch) supply _ _ from
                    CallElaboratesUsing.cons conditionElaboration
                      (CallElaboratesUsing.cons thenElaboration
                        (CallElaboratesUsing.cons elseElaboration
                          CallElaboratesUsing.nil)))
                  (childFuel + 1) outputDemand :=
                ⟨inputDemand, by
                  intro compatible solution semantic environment environmentSafe
                  obtain ⟨secondAccumulatedSemantic, elseSemantic,
                    thirdEquation, elseCheck⟩ :=
                    semanticSolution_fromApp_parts semantic
                  obtain ⟨firstAccumulatedSemantic, thenSemantic,
                    secondEquation, thenCheck⟩ :=
                    semanticSolution_fromApp_parts secondAccumulatedSemantic
                  obtain ⟨_initialSemantic, conditionSemantic,
                    firstEquation, conditionCheck⟩ :=
                    semanticSolution_fromApp_parts firstAccumulatedSemantic
                  obtain ⟨_conditionClass, conditionConversion⟩ := conditionCheck
                  obtain ⟨_thenClass, thenConversion⟩ := thenCheck
                  obtain ⟨_elseClass, elseConversion⟩ := elseCheck
                  simp only [Ty.apply] at conditionConversion
                  simp only [Ty.apply] at thenConversion
                  simp only [Ty.apply] at elseConversion
                  simp only [Equation.Holds, Ty.apply] at firstEquation
                  simp only [Equation.Holds, Ty.apply] at secondEquation
                  simp only [Equation.Holds, Ty.apply] at thirdEquation
                  simp only [Source.conditionalScheme_instantiate] at firstEquation
                  simp only [DataTypes.bool, Ty.apply, Ty.applyList] at firstEquation
                  simp only [Source.Generated.fromApp, Ty.apply] at secondEquation
                  simp only [Source.Generated.fromApp, Ty.apply] at thirdEquation
                  have firstParts := Ty.fn.inj firstEquation
                  rw [← firstParts.2] at secondEquation
                  have secondParts := Ty.fn.inj secondEquation
                  rw [← secondParts.2] at thirdEquation
                  have thirdParts := Ty.fn.inj thirdEquation
                  have conditionEnvironmentSafe := environmentSafe.mono
                    (fun position => OriginDemand.Le.fromLeft (.refl _))
                  have thenEnvironmentSafe := environmentSafe.mono
                    (fun position => OriginDemand.Le.fromRight
                      (.fromLeft (.refl _)))
                  have elseEnvironmentSafe := environmentSafe.mono
                    (fun position => OriginDemand.Le.fromRight
                      (.fromRight (.refl _)))
                  rcases conditionCert.preserves compatible solution
                      conditionSemantic environment conditionEnvironmentSafe with
                      conditionTimeout |
                      ⟨conditionValue, conditionSuccess, conditionSafe⟩
                  · exact .inl (by simp [evalFuel, conditionTimeout])
                  · have checkedCondition := conditionSafe.ofCheckConversion conditionConversion
                    rw [← firstParts.1] at checkedCondition
                    simp only [OriginValueSafe] at checkedCondition
                    cases checkedCondition with
                    | true =>
                          rcases thenCert.preserves compatible solution thenSemantic
                              environment thenEnvironmentSafe with thenTimeout |
                              ⟨thenValue, thenSuccess, thenSafe⟩
                          · exact .inl (by
                              simp [evalFuel, conditionSuccess, thenTimeout])
                          · have checkedThen := thenSafe.ofCheckConversion thenConversion
                            rw [← secondParts.1] at checkedThen
                            simp only [Source.Generated.fromApp, Ty.apply]
                            rw [← thirdParts.2]
                            exact .inr ⟨thenValue, by
                                simp [evalFuel, conditionSuccess, thenSuccess],
                                checkedThen⟩
                    | false =>
                          rcases elseCert.preserves compatible solution elseSemantic
                              environment elseEnvironmentSafe with elseTimeout |
                              ⟨elseValue, elseSuccess, elseSafe⟩
                          · exact .inl (by
                              simp [evalFuel, conditionSuccess, elseTimeout,
                                DataCtor.false, DataCtor.true])
                          · have checkedElse := elseSafe.ofCheckConversion elseConversion
                            rw [← thirdParts.1] at checkedElse
                            simp only [Source.Generated.fromApp, Ty.apply]
                            rw [← thirdParts.2]
                            exact .inr ⟨elseValue, by
                                simp [evalFuel, conditionSuccess, elseSuccess,
                                  DataCtor.false, DataCtor.true],
                                checkedElse⟩⟩
              refine ⟨⟨certificate, ?_⟩⟩
              simp [certificate, inputDemand, conditionCert, thenCert, elseCert,
                conditionExact.input_eq, thenExact.input_eq, elseExact.input_eq]

end ExactRawOriginRequestCertificate

private theorem semanticSolution_postcompose
    {generated : Generated} {earlier : Subst}
    (semantic : generated.SemanticSolution earlier) (later : Subst) :
    generated.SemanticSolution (Subst.compose later earlier) := by
  constructor
  · exact solves_postcompose semantic.1 later
  · intro obligation membership
    obtain ⟨conversionClass, conversion⟩ :=
      semantic.2 obligation membership
    exact ⟨conversionClass, by
      simpa only [Ty.apply_compose] using
        TypePM.Runtime.CheckConversion.apply conversion later⟩

namespace ExactRawOriginRequestCertificate

def timeout
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next)
    (outputDemand : OriginDemand) :
    ExactRawOriginRequestCertificate elaboration 0 outputDemand OriginEnvironmentDemand.none := by
  let certificate : RawOriginRequestCertificate elaboration 0 outputDemand :=
    ⟨OriginEnvironmentDemand.none, by
      intro _compatible solution semantic environment environmentSafe
      exact .inl rfl⟩
  exact ⟨certificate, rfl⟩

def var
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next)
    (operationalFuel : Nat) (outputDemand : OriginDemand) :
    ExactRawOriginRequestCertificate elaboration operationalFuel outputDemand
      (OriginEnvironmentDemand.single position outputDemand) := by
  let certificate := RawOriginRequestCertificate.var elaboration
    operationalFuel outputDemand
  refine ⟨certificate, ?_⟩
  rfl

def litFuel
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lit literal) supply generated next)
    (operationalFuel resultIndex : Nat) :
    ExactRawOriginRequestCertificate elaboration operationalFuel (.fuel resultIndex)
      OriginEnvironmentDemand.none := by
  let certificate : RawOriginRequestCertificate elaboration operationalFuel
      (.fuel resultIndex) :=
    ⟨OriginEnvironmentDemand.none, by
      intro _compatible solution _semantic environment _environmentSafe
      simp only [ElaboratesFuel] at elaboration
      obtain ⟨generatedEq, _nextEq⟩ := elaboration
      rw [generatedEq]
      cases operationalFuel with
      | zero => exact .inl rfl
      | succ _ =>
          exact .inr ⟨.int literal, rfl,
            OriginValueSafe.ofFuel (fuelValueSafe_int literal resultIndex)⟩⟩
  exact ⟨certificate, rfl⟩

/-- A canonical integer literal supports its structural integer observation
at every operational fuel, without reading the environment. -/
def litInt
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lit literal) supply generated next)
    (operationalFuel : Nat) :
    ExactRawOriginRequestCertificate elaboration operationalFuel .int
      OriginEnvironmentDemand.none := by
  let certificate : RawOriginRequestCertificate elaboration operationalFuel
      .int :=
    ⟨OriginEnvironmentDemand.none, by
      intro _compatible solution _semantic environment _environmentSafe
      simp only [ElaboratesFuel] at elaboration
      obtain ⟨generatedEq, _nextEq⟩ := elaboration
      rw [generatedEq]
      cases operationalFuel with
      | zero => exact .inl rfl
      | succ _ => exact .inr ⟨.int literal, rfl, OriginValueSafe.int literal⟩⟩
  exact ⟨certificate, rfl⟩

def somethingFuel
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      .something supply generated next)
    (operationalFuel resultIndex : Nat) :
    ExactRawOriginRequestCertificate elaboration operationalFuel (.fuel resultIndex)
      OriginEnvironmentDemand.none := by
  let certificate : RawOriginRequestCertificate elaboration operationalFuel
      (.fuel resultIndex) :=
    ⟨OriginEnvironmentDemand.none, by
      intro _compatible solution _semantic environment _environmentSafe
      simp only [ElaboratesFuel] at elaboration
      obtain ⟨generatedEq, _nextEq⟩ := elaboration
      rw [generatedEq]
      cases operationalFuel with
      | zero => exact .inl rfl
      | succ _ =>
          exact .inr ⟨.something, rfl, OriginValueSafe.ofFuel (by
            simpa [Ty.apply, Cap.apply] using
              fuelValueSafe_something
                ((Ty.var ⟨supply.ty⟩).apply solution) resultIndex)⟩⟩
  exact ⟨certificate, rfl⟩

def both
    (left : ExactRawOriginRequestCertificate elaboration operationalFuel leftDemand leftInput)
    (right : ExactRawOriginRequestCertificate elaboration operationalFuel rightDemand rightInput) :
    ExactRawOriginRequestCertificate elaboration operationalFuel (.both leftDemand rightDemand)
      (OriginEnvironmentDemand.both leftInput rightInput) := by
  let certificate := RawOriginRequestCertificate.both left.certificate
    right.certificate
  refine ⟨certificate, ?_⟩
  simp [certificate, RawOriginRequestCertificate.both,
    left.input_eq, right.input_eq]

def weaken
    (available : ExactRawOriginRequestCertificate elaboration operationalFuel availableDemand
      inputDemand)
    (weaken : OriginDemand.Le requestedDemand availableDemand) :
    ExactRawOriginRequestCertificate elaboration operationalFuel requestedDemand inputDemand := by
  exact ⟨available.certificate.weakenOutput weaken, by
    simp [RawOriginRequestCertificate.weakenOutput, available.input_eq]⟩

def strengthenInput
    (available : ExactRawOriginRequestCertificate elaboration operationalFuel outputDemand
      inputDemand)
    (stronger : OriginEnvironmentDemand)
    (covers : ∀ position,
      OriginDemand.Le (inputDemand position) (stronger position)) :
    ExactRawOriginRequestCertificate elaboration operationalFuel outputDemand stronger := by
  let certificate := available.certificate.strengthenInput stronger (by
    intro position
    rw [available.input_eq]
    exact covers position)
  exact ⟨certificate, rfl⟩

def reobserveUniversal
    (available : ExactRawOriginRequestCertificate elaboration operationalFuel availableDemand
      inputDemand)
    (universal : OriginDemand.Universal requestedDemand) :
    ExactRawOriginRequestCertificate elaboration operationalFuel requestedDemand inputDemand := by
  let certificate : RawOriginRequestCertificate elaboration operationalFuel
      requestedDemand :=
    ⟨available.certificate.inputDemand, by
      intro compatible solution semantic environment environmentSafe
      exact OriginResultSafe.reobserveUniversal
        (available.certificate.preserves compatible solution semantic environment
          environmentSafe) universal⟩
  exact ⟨certificate, available.input_eq⟩

end ExactRawOriginRequestCertificate

namespace ExactRawOriginItemsFuelCertificate

def nil
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context [] supply generated next)
    (operationalFuel resultIndex : Nat) :
    ExactRawOriginItemsFuelCertificate elaboration operationalFuel resultIndex
      OriginEnvironmentDemand.none := by
  let certificate : RawOriginItemsFuelCertificate elaboration
      operationalFuel resultIndex :=
    ⟨OriginEnvironmentDemand.none, by
      intro _compatible solution semantic environment environmentSafe
      cases elaboration
      exact .inr ⟨[], by simp [FuelResult.traverse],
        FuelEnvironmentSafe.nil resultIndex⟩⟩
  exact ⟨certificate, rfl⟩

theorem cons
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context (expression :: expressions)
      supply generated next)
    (operationalFuel resultIndex : Nat)
    (headInput tailInput : OriginEnvironmentDemand)
    (headCertificate : ∀ generatedHead afterHead,
      ∀ headElaboration : ElaboratesFuel signature staticFuel context
        expression supply generatedHead afterHead,
        Nonempty (ExactRawOriginRequestCertificate headElaboration operationalFuel
          (.fuel resultIndex) headInput))
    (tailCertificate : ∀ afterHead generatedTail,
      ∀ tailElaboration : ItemsElaborateUsing
        (ElaboratesFuel signature staticFuel) context expressions afterHead
        generatedTail next,
        Nonempty (ExactRawOriginItemsFuelCertificate tailElaboration operationalFuel
          resultIndex tailInput)) :
    Nonempty (ExactRawOriginItemsFuelCertificate elaboration operationalFuel resultIndex
      (OriginEnvironmentDemand.both headInput tailInput)) := by
  cases elaboration with
  | @cons _ _ _ generatedHead afterHead generatedTail _ headElaboration
      tailElaboration =>
      obtain ⟨headExact⟩ :=
        headCertificate generatedHead afterHead headElaboration
      obtain ⟨tailExact⟩ :=
        tailCertificate afterHead generatedTail tailElaboration
      let headCertificate := headExact.certificate
      let tailCertificate := tailExact.certificate
      let inputDemand := OriginEnvironmentDemand.both
        headCertificate.inputDemand tailCertificate.inputDemand
      let certificate : RawOriginItemsFuelCertificate
          (ItemsElaborateUsing.cons headElaboration tailElaboration)
          operationalFuel resultIndex :=
        ⟨inputDemand, by
          intro compatible solution semantic environment environmentSafe
          have headSemantic : generatedHead.SemanticSolution solution := by
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
              TypePM.Runtime.GeneratedItems.SemanticSolution generatedTail
                solution := by
            constructor
            · intro equation membership
              exact semantic.1 equation (by
                simp only [List.mem_append]
                exact .inr membership)
            · intro obligation membership
              exact semantic.2 obligation (by
                simp only [List.mem_append]
                exact .inr membership)
          have headEnvironmentSafe := environmentSafe.mono
            (fun position => OriginDemand.Le.fromLeft (.refl _))
          have tailEnvironmentSafe := environmentSafe.mono
            (fun position => OriginDemand.Le.fromRight (.refl _))
          rcases (headCertificate.preserves compatible solution headSemantic environment
              headEnvironmentSafe).toFuel with headTimeout |
              ⟨headValue, headOk, headSafe⟩
          · exact .inl (by simp [FuelResult.traverse, headTimeout])
          · rcases tailCertificate.preserves compatible solution tailSemantic environment
                tailEnvironmentSafe with tailTimeout |
                ⟨tailValues, tailOk, tailSafe⟩
            · exact .inl (by
                simp [FuelResult.traverse, headOk, tailTimeout,
                  FuelResult.bind, FuelResult.map])
            · exact .inr ⟨headValue :: tailValues, by
                simp [FuelResult.traverse, headOk, tailOk, FuelResult.bind,
                  FuelResult.map], by
                simpa [Ty.applyList] using
                  FuelEnvironmentSafe.cons headSafe tailSafe⟩⟩
      refine ⟨⟨certificate, ?_⟩⟩
      simp [certificate, inputDemand, headCertificate, tailCertificate,
        headExact.input_eq, tailExact.input_eq]

end ExactRawOriginItemsFuelCertificate

namespace ExactRawOriginRequestCertificate

theorem tupleFuel
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.tuple expressions) supply generated next)
    (childFuel resultIndex : Nat) (inputDemand : OriginEnvironmentDemand)
    (itemsCertificate : ∀ generatedItems,
      ∀ itemsElaboration : ItemsElaborateUsing
        (ElaboratesFuel signature staticFuel) context expressions supply
        generatedItems next,
      Nonempty (ExactRawOriginItemsFuelCertificate itemsElaboration childFuel
        resultIndex inputDemand)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.fuel resultIndex) inputDemand) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedItems, itemsElaboration, generatedEq⟩ := elaboration
  obtain ⟨itemsExact⟩ := itemsCertificate generatedItems itemsElaboration
  let itemsCertificate := itemsExact.certificate
  let certificate : RawOriginRequestCertificate parentElaboration (childFuel + 1)
      (.fuel resultIndex) :=
    ⟨itemsCertificate.inputDemand, by
      intro compatible solution semantic environment environmentSafe
      have itemsSemantic :
          TypePM.Runtime.GeneratedItems.SemanticSolution generatedItems
            solution := by
        rw [generatedEq] at semantic
        exact semantic
      rw [generatedEq]
      rcases itemsCertificate.preserves compatible solution itemsSemantic environment
          environmentSafe with timeout | ⟨values, success, valuesSafe⟩
      · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
      · exact .inr ⟨.tuple values, by
          simp [evalFuel, success, FuelResult.map], OriginValueSafe.ofFuel (by
          simpa [Ty.apply] using
            fuelValueSafe_tuple_of_environment resultIndex values
              (Ty.applyList solution generatedItems.targets) valuesSafe)⟩⟩
  refine ⟨⟨certificate, ?_⟩⟩
  exact itemsExact.input_eq

/-- Structural binary-tuple rule.  Unlike `tupleFuel`, the two fields may
carry unrelated higher-order demands. -/
theorem tuplePair
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.tuple [left, right]) supply generated next)
    (childFuel : Nat) (leftDemand rightDemand : OriginDemand)
    (leftInput rightInput : OriginEnvironmentDemand)
    (leftCertificate : ∀ generatedLeft afterLeft,
      ∀ leftElaboration : ElaboratesFuel signature staticFuel context
        left supply generatedLeft afterLeft,
      Nonempty (ExactRawOriginRequestCertificate leftElaboration childFuel
        leftDemand leftInput))
    (rightCertificate : ∀ generatedLeft afterLeft generatedRight,
      ∀ _leftElaboration : ElaboratesFuel signature staticFuel context
        left supply generatedLeft afterLeft,
      ∀ rightElaboration : ElaboratesFuel signature staticFuel context
        right afterLeft generatedRight next,
      Nonempty (ExactRawOriginRequestCertificate rightElaboration childFuel
        rightDemand rightInput)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.pairOf leftDemand rightDemand)
      (OriginEnvironmentDemand.both leftInput rightInput)) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedItems, itemsElaboration, generatedEq⟩ := elaboration
  cases itemsElaboration with
  | @cons _ _ _ generatedLeft afterLeft generatedTail _ leftElaboration
      tailElaboration =>
      cases tailElaboration with
      | @cons _ _ _ generatedRight afterRight generatedNil _ rightElaboration
          nilElaboration =>
          cases nilElaboration
          obtain ⟨leftExact⟩ := leftCertificate _ _ leftElaboration
          obtain ⟨rightExact⟩ := rightCertificate _ _ _ leftElaboration
            rightElaboration
          let leftCertificate := leftExact.certificate
          let rightCertificate := rightExact.certificate
          let inputDemand := OriginEnvironmentDemand.both
            leftCertificate.inputDemand rightCertificate.inputDemand
          let certificate : RawOriginRequestCertificate parentElaboration
              (childFuel + 1) (.pairOf leftDemand rightDemand) :=
            ⟨inputDemand, by
              intro compatible solution semantic environment environmentSafe
              rw [generatedEq] at semantic ⊢
              have leftSemantic : generatedLeft.SemanticSolution solution := by
                constructor
                · intro equation membership
                  exact semantic.1 equation (by
                    simp only [List.mem_append]
                    exact .inl membership)
                · intro obligation membership
                  exact semantic.2 obligation (by
                    simp only [List.mem_append]
                    exact .inl membership)
              have rightSemantic : generatedRight.SemanticSolution solution := by
                constructor
                · intro equation membership
                  exact semantic.1 equation (by
                    simp only [List.mem_append]
                    exact .inr (.inl membership))
                · intro obligation membership
                  exact semantic.2 obligation (by
                    simp only [List.mem_append]
                    exact .inr (.inl membership))
              have leftResult := leftCertificate.preserves compatible solution
                leftSemantic environment
                (environmentSafe.mono (fun position => .fromLeft (.refl _)))
              have rightResult := rightCertificate.preserves compatible solution
                rightSemantic environment
                (environmentSafe.mono (fun position => .fromRight (.refl _)))
              rcases leftResult with leftTimeout |
                  ⟨leftValue, leftSuccess, leftSafe⟩
              · exact .inl (by simp [evalFuel, FuelResult.traverse, leftTimeout])
              · rcases rightResult with rightTimeout |
                    ⟨rightValue, rightSuccess, rightSafe⟩
                · exact .inl (by
                    simp [evalFuel, FuelResult.traverse, leftSuccess,
                      rightTimeout, FuelResult.bind, FuelResult.map])
                · exact .inr ⟨.tuple [leftValue, rightValue], by
                    simp [evalFuel, FuelResult.traverse, leftSuccess,
                      rightSuccess, FuelResult.bind, FuelResult.map], by
                    simpa [Ty.apply, Ty.applyList] using
                      OriginValueSafe.pair leftSafe rightSafe⟩⟩
          refine ⟨⟨certificate, ?_⟩⟩
          change OriginEnvironmentDemand.both leftCertificate.inputDemand
              rightCertificate.inputDemand =
            OriginEnvironmentDemand.both leftInput rightInput
          rw [leftExact.input_eq, rightExact.input_eq]

theorem lamPlainCall
    {bodyOperationalFuel lambdaOperationalFuel : Nat}
    {argumentDemand resultDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lam body) supply generated next)
    (bodyInput : OriginEnvironmentDemand)
    (bodyCertificate : ∀ generatedBody,
      ∀ bodyElaboration : ElaboratesFuel signature staticFuel
        (Scheme.mono (.var ⟨supply.ty⟩) :: context) body
        (supply.nextTy 1) generatedBody next,
      Nonempty (ExactRawOriginRequestCertificate bodyElaboration bodyOperationalFuel
        resultDemand bodyInput))
    (argumentCoversBody : OriginDemand.Le (bodyInput 0) argumentDemand) :
    Nonempty (ExactRawOriginRequestCertificate elaboration lambdaOperationalFuel
      (.plainCall (bodyOperationalFuel + 1) argumentDemand resultDemand)
      (OriginEnvironmentDemand.tail bodyInput)) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedBody, bodyElaboration, generatedEq⟩ := elaboration
  obtain ⟨bodyExact⟩ := bodyCertificate generatedBody bodyElaboration
  let bodyCertificate := bodyExact.certificate
  let inputDemand := OriginEnvironmentDemand.tail bodyCertificate.inputDemand
  let certificate : RawOriginRequestCertificate parentElaboration
      lambdaOperationalFuel
      (.plainCall (bodyOperationalFuel + 1) argumentDemand resultDemand) :=
    ⟨inputDemand, by
      intro compatible solution semantic environment environmentSafe
      cases lambdaOperationalFuel with
      | zero => exact .inl rfl
      | succ lambdaFuel =>
          rw [generatedEq] at semantic ⊢
          refine .inr ⟨.plainClosure environment body, rfl, ?_⟩
          apply OriginValueSafe.plainClosure
          intro argument argumentSafe
          apply bodyCertificate.preserves compatible solution semantic
            (argument :: environment)
          have headCovered : OriginDemand.Le
              (bodyCertificate.inputDemand 0) argumentDemand := by
            rw [bodyExact.input_eq]
            exact argumentCoversBody
          have headSafe : SchemeOriginValueSafe
              (bodyCertificate.inputDemand 0) argument
              (Scheme.mono (.var ⟨supply.ty⟩)) solution :=
            SchemeOriginValueSafe.ofMono
              (argumentSafe.mono headCovered)
          have pushed := SchemeOriginEnvironmentSafe.cons headSafe
            environmentSafe
          apply pushed.congr
          intro position _positionLt
          cases position <;> rfl⟩
  refine ⟨⟨certificate, ?_⟩⟩
  exact congrArg OriginEnvironmentDemand.tail bodyExact.input_eq

theorem lamZeroCall
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lam body) supply generated next)
    (lambdaOperationalFuel : Nat)
    (argumentDemand resultDemand : OriginDemand) :
    Nonempty (ExactRawOriginRequestCertificate elaboration lambdaOperationalFuel
      (.plainCall 0 argumentDemand resultDemand)
      OriginEnvironmentDemand.none) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedBody, bodyElaboration, generatedEq⟩ := elaboration
  let certificate : RawOriginRequestCertificate parentElaboration
      lambdaOperationalFuel (.plainCall 0 argumentDemand resultDemand) :=
    ⟨OriginEnvironmentDemand.none, by
      intro _compatible solution semantic environment environmentSafe
      cases lambdaOperationalFuel with
      | zero => exact .inl rfl
      | succ lambdaFuel =>
          rw [generatedEq] at semantic ⊢
          refine .inr ⟨.plainClosure environment body, rfl, ?_⟩
          simp only [OriginValueSafe]
          exact .zero⟩
  exact ⟨⟨certificate, rfl⟩⟩

theorem app
    {childFuel : Nat} {argumentDemand resultDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.app function argument) supply generated next)
    (functionInput argumentInput : OriginEnvironmentDemand)
    (functionCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ _argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (ExactRawOriginRequestCertificate functionElaboration childFuel
        (.plainCall childFuel argumentDemand resultDemand) functionInput))
    (argumentCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ _functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (ExactRawOriginRequestCertificate argumentElaboration childFuel
        argumentDemand argumentInput)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1) resultDemand
      (OriginEnvironmentDemand.both functionInput argumentInput)) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
    functionElaboration, argumentElaboration, generatedEq, nextEq⟩ := elaboration
  obtain ⟨functionExact⟩ := functionCertificate generatedFunction
    afterFunction generatedArgument afterArgument functionElaboration
    argumentElaboration
  obtain ⟨argumentExact⟩ := argumentCertificate generatedFunction
    afterFunction generatedArgument afterArgument functionElaboration
    argumentElaboration
  let functionCertificate := functionExact.certificate
  let argumentCertificate := argumentExact.certificate
  let inputDemand := OriginEnvironmentDemand.both
    functionCertificate.inputDemand argumentCertificate.inputDemand
  let certificate : RawOriginRequestCertificate parentElaboration
      (childFuel + 1) resultDemand :=
    ⟨inputDemand, by
      intro compatible solution semantic environment environmentSafe
      rw [generatedEq] at semantic ⊢
      have functionSemantic : generatedFunction.SemanticSolution solution := by
        constructor
        · intro equation membership
          exact semantic.1 equation (by
            simp only [Generated.fromApp, List.mem_append]
            exact .inl (.inl membership))
        · intro obligation membership
          exact semantic.2 obligation (by
            simp only [Generated.fromApp, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false]
            exact .inl (.inl membership))
      have argumentSemantic : generatedArgument.SemanticSolution solution := by
        constructor
        · intro equation membership
          exact semantic.1 equation (by
            simp only [Generated.fromApp, List.mem_append]
            exact .inl (.inr membership))
        · intro obligation membership
          exact semantic.2 obligation (by
            simp only [Generated.fromApp, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false]
            exact .inl (.inr membership))
      have functionType : generatedFunction.target.apply solution =
          .fn ((Ty.var ⟨afterArgument.ty⟩).apply solution)
            ((Ty.var ⟨afterArgument.ty + 1⟩).apply solution) := by
        exact semantic.1
          (.ty generatedFunction.target
            (.fn (.var ⟨afterArgument.ty⟩)
              (.var ⟨afterArgument.ty + 1⟩)))
          (by simp [Generated.fromApp])
      obtain ⟨conversionClass, argumentConversion⟩ :=
        semantic.2
          ⟨generatedArgument.target, Ty.var ⟨afterArgument.ty⟩⟩
          (by simp [Generated.fromApp])
      have functionSafe := functionCertificate.preserves compatible solution
        functionSemantic environment
        (environmentSafe.mono (fun position => .fromLeft (.refl _)))
      rw [functionType] at functionSafe
      have argumentSafeAtSource := argumentCertificate.preserves compatible solution
        argumentSemantic environment
        (environmentSafe.mono (fun position => .fromRight (.refl _)))
      have argumentSafe := argumentSafeAtSource.ofCheckConversion
        argumentConversion
      exact evalFuel_app_origin functionSafe argumentSafe⟩
  refine ⟨⟨certificate, ?_⟩⟩
  change OriginEnvironmentDemand.both functionCertificate.inputDemand
      argumentCertificate.inputDemand =
    OriginEnvironmentDemand.both functionInput argumentInput
  rw [functionExact.input_eq, argumentExact.input_eq]

/-- Source-derived `letE` composition when every observation requested by
the right-hand side from the outer environment is universal.  The body may
request an arbitrary structural observation from the generalized binding.

For each scheme occurrence, the exact principal right-hand-side closure
constructs an occurrence-specific semantic solution.  Universality makes the
outer runtime environment safe under that solution without assuming an
evaluation result or an occurrence-transport oracle. -/
theorem letUniversalInput
    {childFuel : Nat} {outputDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.letE value body) supply generated next)
    (valueInput bodyInput : OriginEnvironmentDemand)
    (valueInputUniversal : ∀ position,
      OriginDemand.Universal (valueInput position))
    (valueCertificate : ∀ generatedValue afterValue,
      ∀ valueElaboration : ElaboratesFuel signature staticFuel context value
        supply generatedValue afterValue,
      Nonempty (ExactRawOriginRequestCertificate valueElaboration childFuel
        (bodyInput 0) valueInput))
    (bodyCertificate : ∀ generatedValue afterValue,
      ∀ _valueElaboration : ElaboratesFuel signature staticFuel context value
        supply generatedValue afterValue,
      ∀ valueClosure : PrincipalBlockClosure generatedValue,
      ∀ bodyGenerated,
      ∀ bodyElaboration : ElaboratesFuel signature staticFuel
        ((context.applyFree valueClosure.substitution).generalize
            valueClosure.target :: context.applyFree valueClosure.substitution)
        body
        (afterValue.join
          (context.applyFree valueClosure.substitution).initialSupply)
        bodyGenerated next,
      Nonempty (ExactRawOriginRequestCertificate bodyElaboration childFuel
        outputDemand bodyInput)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      outputDemand (OriginEnvironmentDemand.tail bodyInput)) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedValue, afterValue, valueElaboration, valueClosure,
    bodyGenerated, valueAbsorbing, bodyElaboration, generatedEq⟩ := elaboration
  obtain ⟨valueExact⟩ := valueCertificate generatedValue afterValue
    valueElaboration
  obtain ⟨bodyExact⟩ := bodyCertificate generatedValue afterValue
    valueElaboration valueClosure bodyGenerated bodyElaboration
  let generalizedScheme :=
    (context.applyFree valueClosure.substitution).generalize
      valueClosure.target
  let certificate : RawOriginRequestCertificate parentElaboration
      (childFuel + 1) outputDemand :=
    ⟨OriginEnvironmentDemand.tail bodyInput, by
      intro compatible solution semantic environment environmentSafe
      rw [generatedEq] at semantic
      obtain ⟨interfaceSolved, bodySemantic⟩ :=
        semanticSolution_fromLet_parts semantic
      have valueResult : FuelResultSafeWith
          (fun value => SchemeOriginValueSafe (bodyInput 0) value
            generalizedScheme solution)
          (evalFuel childFuel environment value) := by
        let initialSupply : Supply := ⟨0, 0⟩
        let initialOccurrence :=
          TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution
            valueClosure valueAbsorbing context solution interfaceSolved
              initialSupply
        have initialEnvironmentSafe : SchemeOriginEnvironmentSafe valueInput
            initialOccurrence.solution environment context :=
          schemeOriginEnvironmentSafe_ofUniversal environmentSafe.1
            valueInputUniversal
        have initialResult := valueExact.certificate.preserves compatible
          initialOccurrence.solution initialOccurrence.semantic environment
          (by simpa [valueExact.input_eq] using initialEnvironmentSafe)
        rw [initialOccurrence.target_eq] at initialResult
        rcases initialResult with valueTimeout |
            ⟨actual, valueSuccess, _initialSafe⟩
        · exact .inl valueTimeout
        · refine .inr ⟨actual, valueSuccess, ?_⟩
          intro occurrenceSupply
          let occurrence :=
            TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution
              valueClosure valueAbsorbing context solution interfaceSolved
                occurrenceSupply
          have occurrenceEnvironmentSafe : SchemeOriginEnvironmentSafe
              valueInput occurrence.solution environment context :=
            schemeOriginEnvironmentSafe_ofUniversal environmentSafe.1
              valueInputUniversal
          have occurrenceResult := valueExact.certificate.preserves compatible
            occurrence.solution occurrence.semantic environment
            (by simpa [valueExact.input_eq] using occurrenceEnvironmentSafe)
          rw [occurrence.target_eq] at occurrenceResult
          rcases occurrenceResult with occurrenceTimeout |
              ⟨occurrenceValue, occurrenceSuccess, occurrenceSafe⟩
          · rw [valueSuccess] at occurrenceTimeout
            contradiction
          · rw [valueSuccess] at occurrenceSuccess
            cases occurrenceSuccess
            exact occurrenceSafe
      have bodyTailClosedSafe : SchemeOriginEnvironmentSafe
          (OriginEnvironmentDemand.tail bodyInput) solution environment
          (context.applyFree valueClosure.substitution) :=
        schemeOriginEnvironmentSafe_ofApplyFreeInterface environmentSafe
          interfaceSolved
      rw [generatedEq]
      apply evalFuel_letE_resultSafeWith valueResult
      intro boundValue boundSafe
      have bodyEnvironmentSafe : SchemeOriginEnvironmentSafe bodyInput
          solution (boundValue :: environment)
          (generalizedScheme ::
            context.applyFree valueClosure.substitution) := by
        have pushed := SchemeOriginEnvironmentSafe.cons boundSafe
          bodyTailClosedSafe
        apply pushed.congr
        intro position _within
        cases position <;> rfl
      exact bodyExact.certificate.preserves compatible solution bodySemantic
        (boundValue :: environment)
        (by simpa [bodyExact.input_eq] using bodyEnvironmentSafe)⟩
  exact ⟨⟨certificate, rfl⟩⟩

/-- Source-derived `letE` composition for an open monomorphic right-hand
side.  The surrounding context must contain only arity-zero schemes, so the
outer semantic solution and every occurrence-specific solution agree on all
instantiated environment types.  Unlike `letUniversalInput`, this rule
requests the right-hand side's actual outer-environment demand and therefore
needs no universality assumption.

This deliberately does not cover a general open polymorphic `letE`: fresh
prefix variables opened by a positive-arity source scheme need an additional
agreement argument that is not available from the principal closure alone. -/
theorem letArityZero
    {childFuel : Nat} {outputDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.letE value body) supply generated next)
    (valueInput bodyInput : OriginEnvironmentDemand)
    (contextArityZero : ContextSchemeArityZero context)
    (valueCertificate : ∀ generatedValue afterValue,
      ∀ valueElaboration : ElaboratesFuel signature staticFuel context value
        supply generatedValue afterValue,
      Nonempty (ExactRawOriginRequestCertificate valueElaboration childFuel
        (bodyInput 0) valueInput))
    (bodyCertificate : ∀ generatedValue afterValue,
      ∀ _valueElaboration : ElaboratesFuel signature staticFuel context value
        supply generatedValue afterValue,
      ∀ valueClosure : PrincipalBlockClosure generatedValue,
      ∀ bodyGenerated,
      ∀ bodyElaboration : ElaboratesFuel signature staticFuel
        ((context.applyFree valueClosure.substitution).generalize
            valueClosure.target :: context.applyFree valueClosure.substitution)
        body
        (afterValue.join
          (context.applyFree valueClosure.substitution).initialSupply)
        bodyGenerated next,
      Nonempty (ExactRawOriginRequestCertificate bodyElaboration childFuel
        outputDemand bodyInput)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      outputDemand (OriginEnvironmentDemand.both valueInput
        (OriginEnvironmentDemand.tail bodyInput))) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedValue, afterValue, valueElaboration, valueClosure,
    bodyGenerated, valueAbsorbing, bodyElaboration, generatedEq⟩ := elaboration
  obtain ⟨valueExact⟩ := valueCertificate generatedValue afterValue
    valueElaboration
  obtain ⟨bodyExact⟩ := bodyCertificate generatedValue afterValue
    valueElaboration valueClosure bodyGenerated bodyElaboration
  let generalizedScheme :=
    (context.applyFree valueClosure.substitution).generalize
      valueClosure.target
  let inputDemand := OriginEnvironmentDemand.both valueInput
    (OriginEnvironmentDemand.tail bodyInput)
  let certificate : RawOriginRequestCertificate parentElaboration
      (childFuel + 1) outputDemand :=
    ⟨inputDemand, by
      intro compatible solution semantic environment environmentSafe
      rw [generatedEq] at semantic
      obtain ⟨interfaceSolved, bodySemantic⟩ :=
        semanticSolution_fromLet_parts semantic
      have valueOuterSafe : SchemeOriginEnvironmentSafe valueInput solution
          environment context :=
        environmentSafe.mono (fun position => .fromLeft (.refl _))
      have bodyOuterSafe : SchemeOriginEnvironmentSafe
          (OriginEnvironmentDemand.tail bodyInput) solution environment
          context :=
        environmentSafe.mono (fun position => .fromRight (.refl _))
      have valueResult : FuelResultSafeWith
          (fun value => SchemeOriginValueSafe (bodyInput 0) value
            generalizedScheme solution)
          (evalFuel childFuel environment value) := by
        let initialSupply : Supply := ⟨0, 0⟩
        let initialOccurrence :=
          TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution
            valueClosure valueAbsorbing context solution interfaceSolved
              initialSupply
        have initialEnvironmentSafe : SchemeOriginEnvironmentSafe valueInput
            initialOccurrence.solution environment context :=
          schemeOriginEnvironmentSafe_ofOccurrenceArityZero valueOuterSafe
            contextArityZero initialOccurrence
        have initialResult := valueExact.certificate.preserves compatible
          initialOccurrence.solution initialOccurrence.semantic environment
          (by simpa [valueExact.input_eq] using initialEnvironmentSafe)
        rw [initialOccurrence.target_eq] at initialResult
        rcases initialResult with valueTimeout |
            ⟨actual, valueSuccess, _initialSafe⟩
        · exact .inl valueTimeout
        · refine .inr ⟨actual, valueSuccess, ?_⟩
          intro occurrenceSupply
          let occurrence :=
            TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution
              valueClosure valueAbsorbing context solution interfaceSolved
                occurrenceSupply
          have occurrenceEnvironmentSafe : SchemeOriginEnvironmentSafe
              valueInput occurrence.solution environment context :=
            schemeOriginEnvironmentSafe_ofOccurrenceArityZero valueOuterSafe
              contextArityZero occurrence
          have occurrenceResult := valueExact.certificate.preserves compatible
            occurrence.solution occurrence.semantic environment
            (by simpa [valueExact.input_eq] using occurrenceEnvironmentSafe)
          rw [occurrence.target_eq] at occurrenceResult
          rcases occurrenceResult with occurrenceTimeout |
              ⟨occurrenceValue, occurrenceSuccess, occurrenceSafe⟩
          · rw [valueSuccess] at occurrenceTimeout
            contradiction
          · rw [valueSuccess] at occurrenceSuccess
            cases occurrenceSuccess
            exact occurrenceSafe
      have bodyTailClosedSafe : SchemeOriginEnvironmentSafe
          (OriginEnvironmentDemand.tail bodyInput) solution environment
          (context.applyFree valueClosure.substitution) :=
        schemeOriginEnvironmentSafe_ofApplyFreeInterface bodyOuterSafe
          interfaceSolved
      rw [generatedEq]
      apply evalFuel_letE_resultSafeWith valueResult
      intro boundValue boundSafe
      have bodyEnvironmentSafe : SchemeOriginEnvironmentSafe bodyInput
          solution (boundValue :: environment)
          (generalizedScheme ::
            context.applyFree valueClosure.substitution) := by
        have pushed := SchemeOriginEnvironmentSafe.cons boundSafe
          bodyTailClosedSafe
        apply pushed.congr
        intro position _within
        cases position <;> rfl
      exact bodyExact.certificate.preserves compatible solution bodySemantic
        (boundValue :: environment)
        (by simpa [bodyExact.input_eq] using bodyEnvironmentSafe)⟩
  refine ⟨⟨certificate, ?_⟩⟩
  rfl

end ExactRawOriginRequestCertificate

mutual

  /-- Static realizability of one output observation.  The indices state the
  evaluator fuel, output demand, and exact source-environment input demand.
  No semantic solution or runtime value occurs in this judgment. -/
  inductive RawOriginRequestPlan :
      Nat → Expr → OriginDemand → OriginEnvironmentDemand → Prop where
    /-- At evaluator fuel zero every expression times out, so every output
    observation is vacuously realizable without observing the environment. -/
    | timeout : RawOriginRequestPlan 0 expression outputDemand
        OriginEnvironmentDemand.none
    | var : RawOriginRequestPlan operationalFuel (.var position) outputDemand
        (OriginEnvironmentDemand.single position outputDemand)
    | litFuel : RawOriginRequestPlan operationalFuel (.lit literal) (.fuel resultIndex)
        OriginEnvironmentDemand.none
    | litInt : RawOriginRequestPlan operationalFuel (.lit literal) .int
        OriginEnvironmentDemand.none
    | somethingFuel : RawOriginRequestPlan operationalFuel .something (.fuel resultIndex)
        OriginEnvironmentDemand.none
    /-- Canonical constructors delegate argument evaluation to the curried
    call companion and reassemble only a declared structural result shape. -/
    | ctor
        (result : RawOriginConstructorResultPlan constructor demands
          outputDemand)
        (arguments : RawOriginCallPlan childFuel expressions demands input) :
        RawOriginRequestPlan (childFuel + 1) (.ctor constructor expressions)
          outputDemand input
    /-- First-order primitives reuse the same argument companion and a
    separately checked runtime delta-rule postcondition. -/
    | prim
        (result : RawOriginPrimitiveResultPlan operation demands outputDemand)
        (arguments : RawOriginCallPlan childFuel expressions demands input) :
        RawOriginRequestPlan (childFuel + 1) (.prim operation expressions)
          outputDemand input
    /-- Primitive `map` evaluates both children at one common fuel and then
    invokes the callback at that same fuel for every list element. -/
    | primMap
        (functionPlan : RawOriginRequestPlan childFuel functionExpression
          (.plainCall childFuel argumentDemand resultDemand) functionInput)
        (inputPlan : RawOriginRequestPlan childFuel inputExpression
          (.listOf argumentDemand) inputInput) :
        RawOriginRequestPlan (childFuel + 1)
          (.prim .map [functionExpression, inputExpression])
          (.listOf resultDemand)
          (OriginEnvironmentDemand.both functionInput inputInput)
    /-- A conditional observes a canonical Boolean and only the selected
    branch at runtime, while both branch plans remain available statically. -/
    | ifE
        (condition : RawOriginRequestPlan childFuel conditionExpression .bool
          conditionInput)
        (thenBranch : RawOriginRequestPlan childFuel thenExpression outputDemand
          thenInput)
        (elseBranch : RawOriginRequestPlan childFuel elseExpression outputDemand
          elseInput) :
        RawOriginRequestPlan (childFuel + 1)
          (.ifE conditionExpression thenExpression elseExpression) outputDemand
          (OriginEnvironmentDemand.both conditionInput
            (OriginEnvironmentDemand.both thenInput elseInput))
    /-- A binary tuple may expose unrelated structural observations of its
    two fields. -/
    | tuplePair
        (left : RawOriginRequestPlan childFuel leftExpression leftDemand
          leftInput)
        (right : RawOriginRequestPlan childFuel rightExpression rightDemand
          rightInput) :
        RawOriginRequestPlan (childFuel + 1)
          (.tuple [leftExpression, rightExpression])
          (.pairOf leftDemand rightDemand)
          (OriginEnvironmentDemand.both leftInput rightInput)
    /-- A positive tuple observation uses one less evaluator fuel for every
    field and requests the same ordinary result index from every field. -/
    | tupleFuel
        (items : RawOriginItemsFuelPlan childFuel expressions resultIndex input) :
        RawOriginRequestPlan (childFuel + 1) (.tuple expressions) (.fuel resultIndex)
          input
    /-- A positive future call delegates its result observation to the body.
    The public argument demand must cover the body's exact position-zero
    demand; the remaining positions become the captured-environment demand. -/
    | lamPlainCall
        (bodyPlan : RawOriginRequestPlan bodyOperationalFuel body resultDemand bodyInput)
        (argumentCoversBody : OriginDemand.Le (bodyInput 0) argumentDemand) :
        RawOriginRequestPlan lambdaOperationalFuel (.lam body)
          (.plainCall (bodyOperationalFuel + 1)
            argumentDemand resultDemand)
          (OriginEnvironmentDemand.tail bodyInput)
    | lamZeroCall : RawOriginRequestPlan lambdaOperationalFuel (.lam body)
        (.plainCall 0 argumentDemand resultDemand)
        OriginEnvironmentDemand.none
    /-- Uniform application transports any argument demand through the
    normalized checking conversion stored by the parent block. -/
    | app
        (functionPlan : RawOriginRequestPlan childFuel function
          (.plainCall childFuel argumentDemand resultDemand) functionInput)
        (argumentPlan : RawOriginRequestPlan childFuel argument argumentDemand
          argumentInput) :
        RawOriginRequestPlan (childFuel + 1) (.app function argument) resultDemand
          (OriginEnvironmentDemand.both functionInput argumentInput)
    /-- A generalized `letE` may delegate its binding observation to the
    right-hand side when the latter's outer-environment observations are
    universal under every occurrence-specific semantic solution. -/
    | letUniversalInput
        (valuePlan : RawOriginRequestPlan childFuel value (bodyInput 0)
          valueInput)
        (valueInputUniversal : ∀ position,
          OriginDemand.Universal (valueInput position))
        (bodyPlan : RawOriginRequestPlan childFuel body outputDemand bodyInput) :
        RawOriginRequestPlan (childFuel + 1) (.letE value body) outputDemand
          (OriginEnvironmentDemand.tail bodyInput)
    | both
        (left : RawOriginRequestPlan operationalFuel expression leftDemand leftInput)
        (right : RawOriginRequestPlan operationalFuel expression rightDemand rightInput) :
        RawOriginRequestPlan operationalFuel expression (.both leftDemand rightDemand)
          (OriginEnvironmentDemand.both leftInput rightInput)
    | weaken
        (available : RawOriginRequestPlan operationalFuel expression availableDemand input)
        (weaken : OriginDemand.Le requestedDemand availableDemand) :
        RawOriginRequestPlan operationalFuel expression requestedDemand input
    /-- Once evaluation is known not to be stuck, it can be reobserved with a
    demand that is satisfied by every value and type. -/
    | universal
        (available : RawOriginRequestPlan operationalFuel expression availableDemand input)
        (requested : OriginDemand.Universal requestedDemand) :
        RawOriginRequestPlan operationalFuel expression requestedDemand input
    | strengthenInput
        (available : RawOriginRequestPlan operationalFuel expression outputDemand input)
        (covers : ∀ position,
          OriginDemand.Le (input position) (stronger position)) :
        RawOriginRequestPlan operationalFuel expression outputDemand stronger

  /-- Tuple-field companion: every field must realize the same positive
  ordinary-fuel output observation at the tuple's child evaluator fuel. -/
  inductive RawOriginItemsFuelPlan :
      Nat → List Expr → Nat → OriginEnvironmentDemand → Prop where
    | nil : RawOriginItemsFuelPlan operationalFuel [] resultIndex
        OriginEnvironmentDemand.none
    | cons
        (head : RawOriginRequestPlan operationalFuel expression (.fuel resultIndex)
          headInput)
        (tail : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
          tailInput) :
        RawOriginItemsFuelPlan operationalFuel (expression :: expressions)
          resultIndex (OriginEnvironmentDemand.both headInput tailInput)

  /-- Argument companion for a normalized curried call.  Its demand list is
  aligned pointwise with the source argument list, while its exact input
  demand is the pointwise conjunction of the argument plans. -/
  inductive RawOriginCallPlan :
      Nat → List Expr → List OriginDemand → OriginEnvironmentDemand → Prop where
    | nil : RawOriginCallPlan operationalFuel [] []
        OriginEnvironmentDemand.none
    | cons
        (head : RawOriginRequestPlan operationalFuel expression demand
          headInput)
        (tail : RawOriginCallPlan operationalFuel expressions demands
          tailInput) :
        RawOriginCallPlan operationalFuel (expression :: expressions)
          (demand :: demands)
          (OriginEnvironmentDemand.both headInput tailInput)

end

/-- Context-indexed request-plan companion for the arity-zero `letE` rule.
`RawOriginRequestPlan` itself intentionally has no source-context index, so a
context-specific monomorphism premise cannot be added to its mutual recursor
without either forgetting the premise's context or changing every existing
plan.  This companion keeps the two ordinary child plans and the exact source
context together. -/
structure RawOriginLetArityZeroPlan
    (context : Context) (childFuel : Nat) (value body : Expr)
    (outputDemand : OriginDemand)
    (valueInput bodyInput : OriginEnvironmentDemand) : Prop where
  contextArityZero : ContextSchemeArityZero context
  valuePlan : RawOriginRequestPlan childFuel value (bodyInput 0) valueInput
  bodyPlan : RawOriginRequestPlan childFuel body outputDemand bodyInput

/-- Static/runtime type alignment required by the simple-matcher form of the
bounded `matchAll` bridge.  Product matchers need a separate product-matcher
boundary and are intentionally not hidden in this producer. -/
def RawOriginMatchAllMatcherRuntimeTypeProducer
    (signature : FrozenSignature) (staticFuel : Nat) (context : Context)
    (targetExpression matcherExpression : Expr) (pattern : Pattern)
    (bodyExpression : Expr) (supply next : Supply) : Prop :=
  ∀ {generatedTarget : Generated} {generatedPattern : GeneratedPattern}
    {generatedMatcher generatedBody : Generated},
    MatchAllElaboratesUsing (ElaboratesFuel signature staticFuel) signature
      context targetExpression matcherExpression pattern bodyExpression supply
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody) next →
    ∀ solution,
    (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
      generatedBody).SemanticSolution solution →
    ∃ capability,
      generatedMatcher.target.apply solution =
        .matcher capability (generatedTarget.target.apply solution)

/-- Search evidence retained by a raw `matchAll` plan.  The producer is tied
to the exact enclosing component derivation and emits only the evaluated
initial state; it contains no completed DFS result. -/
def RawOriginMatchAllInitialStateProducer
    (signature : FrozenSignature) (staticFuel childFuel bindingIndex : Nat)
    (context : Context) (sourceTargets : List Ty)
    (targetExpression matcherExpression : Expr) (pattern : Pattern)
    (bodyExpression : Expr) (supply next : Supply) : Prop :=
  ∀ {generatedTarget : Generated} {generatedPattern : GeneratedPattern}
    {generatedMatcher generatedBody : Generated},
    MatchAllElaboratesUsing (ElaboratesFuel signature staticFuel) signature
      context targetExpression matcherExpression pattern bodyExpression supply
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody) next →
    SignatureCompatible signature.base →
    ∀ solution,
    (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
      generatedBody).SemanticSolution solution →
    ∀ environment,
    FuelEnvironmentSafe bindingIndex environment
      (Ty.applyList solution sourceTargets) →
    EvaluatedTwoIndexInitialStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
      childFuel bindingIndex environment targetExpression matcherExpression
      pattern (Ty.applyList solution generatedPattern.bindings)

/-- Elaboration-indexed request plan for one bounded `matchAll`.  All dynamic
roles use `childFuel`; `bindingIndex` is retained for search answers and
`resultIndex` for body results.  The MNode-free proof records the exact task
shape later consumed by the G8--G10 bounded-DFS origin bridge. -/
structure RawOriginMatchAllPlan
    {signature : FrozenSignature} {staticFuel : Nat} {context : Context}
    {targetExpression matcherExpression : Expr} {pattern : Pattern}
    {bodyExpression : Expr} {supply : Supply} {generated : Generated}
    {next : Supply}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.matchAll targetExpression matcherExpression pattern bodyExpression)
      supply generated next)
    (childFuel bindingIndex resultIndex : Nat)
    (sourceTargets : List Ty)
    (targetInput matcherInput bodyInput : OriginEnvironmentDemand) : Prop where
  contextEq : context = sourceTargets.map Scheme.mono
  patternMNodeFree : pattern.MNodeFree
  targetPlan : RawOriginRequestPlan childFuel targetExpression
    (.fuel childFuel) targetInput
  matcherPlan : RawOriginRequestPlan childFuel matcherExpression
    (.fuel childFuel) matcherInput
  bodyPlan : RawOriginRequestPlan childFuel bodyExpression
    (.fuel resultIndex) bodyInput
  bodyInputCovered : ∀ position,
    OriginDemand.Le (bodyInput position) (.fuel bindingIndex)
  matcherRuntimeType : RawOriginMatchAllMatcherRuntimeTypeProducer signature
    staticFuel context targetExpression matcherExpression pattern bodyExpression
    supply next
  initialState : RawOriginMatchAllInitialStateProducer signature staticFuel
    childFuel bindingIndex context sourceTargets targetExpression
    matcherExpression pattern bodyExpression supply next

/-- Concrete task-issuance evidence retained after the target and matcher
evaluations succeed.  Its indices expose exactly the callback/search fuel and
answer types expected by the two-index bounded-DFS certificate family. -/
structure RawOriginMatchAllIssuedTask
    (childFuel bindingIndex : Nat) (environment : ValueEnvironment)
    (targetExpression matcherExpression : Expr) (pattern : Pattern)
    (bindingTypes : List Ty) (targetValue matcherValue : Value) : Prop where
  patternMNodeFree : pattern.MNodeFree
  targetSuccess : evalFuel childFuel environment targetExpression = .ok targetValue
  matcherSuccess : evalFuel childFuel environment matcherExpression = .ok matcherValue
  initialTyped : EvaluatedTwoIndexInitialStateTyping FuelEnvironmentSafe
    FuelEnvironmentSafe childFuel bindingIndex environment targetExpression
    matcherExpression pattern bindingTypes

def RawOriginMatchAllIssuedTask.task
    (issued : RawOriginMatchAllIssuedTask childFuel bindingIndex environment
      targetExpression matcherExpression pattern bindingTypes targetValue
      matcherValue) :
    TypePM.Source.M5CompletionArchitecture.BoundedDfsMatchingSearchTask :=
  TypePM.Source.M5CompletionArchitecture.BoundedDfsMatchingSearchTask.mk
    environment pattern issued.patternMNodeFree matcherValue targetValue

/-- Source-ordered plan aligned with one exact M4 ordinary-arm tail.  Every
arm retains its own binding types through `generatedPattern`, its own body
input demand, and its own initial-state producer. -/
inductive RawOriginMatchFirstTailPlan
    (signature : FrozenSignature) (staticFuel childFuel bindingIndex
      resultIndex : Nat)
    (context : Context) (sourceTargets : List Ty)
    (targetExpression matcherExpression : Expr) :
    ∀ {targetType matcherType expectedResult : Ty}
      {arms : List MatchFirstArm} {supply : Supply}
      {generated : MatchFirstTyping.GeneratedTail} {next : Supply},
      MatchFirstTyping.TailElaboratesUsing
        (ElaboratesFuel signature staticFuel) signature context targetType
        matcherType expectedResult arms supply generated next → Prop where
  | nil {targetType matcherType expectedResult supply} :
      RawOriginMatchFirstTailPlan signature staticFuel childFuel bindingIndex
        resultIndex context sourceTargets targetExpression matcherExpression
        (MatchFirstTyping.TailElaboratesUsing.nil (targetType := targetType)
          (matcherType := matcherType) (expectedResult := expectedResult)
          (supply := supply))
  | cons
      {targetType matcherType expectedResult pattern body arms supply
        generatedPattern afterPattern generatedBody afterBody generatedTail next}
      {patternElaboration : PatternElaboratesUsing
        (ElaboratesFuel signature staticFuel) signature context [] pattern []
        supply generatedPattern afterPattern}
      {bodyElaboration : ElaboratesFuel signature staticFuel
        (Pattern.extendContext generatedPattern.bindings context) body
        afterPattern generatedBody afterBody}
      {tailElaboration : MatchFirstTyping.TailElaboratesUsing
        (ElaboratesFuel signature staticFuel) signature context targetType
        matcherType expectedResult arms afterBody generatedTail next}
      {bodyInput : OriginEnvironmentDemand}
      (patternMNodeFree : pattern.MNodeFree)
      (bodyPlan : RawOriginRequestPlan childFuel body (.fuel resultIndex)
        bodyInput)
      (bodyInputCovered : ∀ position,
        OriginDemand.Le (bodyInput position) (.fuel bindingIndex))
      (initialState : ∀ solution,
        MatcherTyping.GeneratedPatternRuntimeSolution generatedPattern solution →
        ∀ environment,
        FuelEnvironmentSafe bindingIndex environment
          (Ty.applyList solution sourceTargets) →
        ∀ targetValue matcherValue,
        TwoIndexMatchingStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
          (evaluationAtomReducer (evalFuel childFuel)) childFuel bindingIndex
          ⟨[⟨pattern, matcherValue, targetValue⟩], environment, []⟩
          (Ty.applyList solution generatedPattern.bindings))
      (tailPlan : RawOriginMatchFirstTailPlan signature staticFuel childFuel
        bindingIndex resultIndex context sourceTargets targetExpression
        matcherExpression tailElaboration) :
      RawOriginMatchFirstTailPlan signature staticFuel childFuel bindingIndex
        resultIndex context sourceTargets targetExpression matcherExpression
        (MatchFirstTyping.TailElaboratesUsing.cons patternElaboration
          bodyElaboration tailElaboration)

/-- Static/runtime type alignment for the simple-matcher `matchFirst`
boundary.  Product matchers require their own runtime bridge and are not
silently admitted here. -/
def RawOriginMatchFirstMatcherRuntimeTypeProducer
    (signature : FrozenSignature) (staticFuel : Nat) (context : Context)
    (targetExpression matcherExpression : Expr) (arms : List MatchFirstArm)
    (fallbackExpression : Expr) (supply next : Supply) : Prop :=
  ∀ {generatedTarget generatedMatcher : Generated}
    {generatedArms : MatchFirstTyping.GeneratedArms},
    MatchFirstTyping.ElaboratesUsing (ElaboratesFuel signature staticFuel)
      signature context
      (.matchFirst targetExpression matcherExpression arms fallbackExpression)
      supply
      (MatchFirstTyping.Generated.fromMatchFirst generatedTarget
        generatedMatcher generatedArms) next →
    ∀ solution,
    (MatchFirstTyping.Generated.fromMatchFirst generatedTarget generatedMatcher
      generatedArms).SemanticSolution solution →
    ∃ capability,
      generatedMatcher.target.apply solution =
        .matcher capability (generatedTarget.target.apply solution)

/-- An elaboration-indexed, source-ordered `matchFirst` plan.  All children,
searches, and callbacks use `childFuel`; arm-local data remains in the exact
tail plan instead of being flattened into one uniform body context. -/
structure RawOriginMatchFirstPlan
    {signature : FrozenSignature} {staticFuel : Nat} {context : Context}
    {targetExpression matcherExpression fallbackExpression : Expr}
    {arms : List MatchFirstArm} {supply : Supply} {generated : Generated}
    {next : Supply}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.matchFirst targetExpression matcherExpression arms fallbackExpression)
      supply generated next)
    (childFuel bindingIndex resultIndex : Nat) (sourceTargets : List Ty)
    (targetInput matcherInput fallbackInput : OriginEnvironmentDemand) : Prop where
  contextEq : context = sourceTargets.map Scheme.mono
  targetPlan : RawOriginRequestPlan childFuel targetExpression
    (.fuel childFuel) targetInput
  matcherPlan : RawOriginRequestPlan childFuel matcherExpression
    (.fuel childFuel) matcherInput
  fallbackPlan : RawOriginRequestPlan childFuel fallbackExpression
    (.fuel resultIndex) fallbackInput
  matcherRuntimeType : RawOriginMatchFirstMatcherRuntimeTypeProducer signature
    staticFuel context targetExpression matcherExpression arms
    fallbackExpression supply next
  tailPlan : ∀ {generatedTarget generatedMatcher generatedFallback : Generated}
      {generatedTail : MatchFirstTyping.GeneratedTail}
      {afterTarget afterMatcher afterFallback : Supply},
    ∀ _targetElaboration : ElaboratesFuel signature staticFuel context
      targetExpression supply generatedTarget afterTarget,
    ∀ _matcherElaboration : ElaboratesFuel signature staticFuel context
      matcherExpression afterTarget generatedMatcher afterMatcher,
    ∀ _fallbackElaboration : ElaboratesFuel signature staticFuel context
      fallbackExpression afterMatcher generatedFallback afterFallback,
    ∀ tailElaboration : MatchFirstTyping.TailElaboratesUsing
      (ElaboratesFuel signature staticFuel) signature context
      generatedTarget.target generatedMatcher.target generatedFallback.target
      arms afterFallback generatedTail next,
    RawOriginMatchFirstTailPlan signature staticFuel childFuel bindingIndex
      resultIndex context sourceTargets targetExpression matcherExpression
      tailElaboration

/-- One source-arm task issued after the common-fuel target and matcher
evaluations succeed.  The task carries the exact arm-local binding types and
the MNode-free origin required by the later bounded-DFS origin bridge. -/
structure RawOriginMatchFirstIssuedTask
    (childFuel bindingIndex : Nat) (environment : ValueEnvironment)
    (targetExpression matcherExpression : Expr) (pattern : Pattern)
    (bindingTypes : List Ty) (targetValue matcherValue : Value) : Prop where
  patternMNodeFree : pattern.MNodeFree
  targetSuccess : evalFuel childFuel environment targetExpression = .ok targetValue
  matcherSuccess : evalFuel childFuel environment matcherExpression = .ok matcherValue
  initialTyped : TwoIndexMatchingStateTyping FuelEnvironmentSafe
    FuelEnvironmentSafe (evaluationAtomReducer (evalFuel childFuel)) childFuel
    bindingIndex ⟨[⟨pattern, matcherValue, targetValue⟩], environment, []⟩
    bindingTypes

def RawOriginMatchFirstIssuedTask.task
    (issued : RawOriginMatchFirstIssuedTask childFuel bindingIndex environment
      targetExpression matcherExpression pattern bindingTypes targetValue
      matcherValue) :
    TypePM.Source.M5CompletionArchitecture.BoundedDfsMatchingSearchTask :=
  TypePM.Source.M5CompletionArchitecture.BoundedDfsMatchingSearchTask.mk
    environment pattern issued.patternMNodeFree matcherValue targetValue

/-- Motive used by the mutual recursor.  It is stated separately so the same
kernel-checked handlers feed both projections of the mutual recursion. -/
private def RawOriginRequestCertificateMotive
    (operationalFuel : Nat) (expression : Expr)
    (outputDemand : OriginDemand) (inputDemand : OriginEnvironmentDemand)
    (_plan : RawOriginRequestPlan operationalFuel expression outputDemand inputDemand) :
    Prop :=
  ∀ {signature staticFuel context supply generated next},
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next) →
    Nonempty (ExactRawOriginRequestCertificate elaboration operationalFuel outputDemand
      inputDemand)

private def RawOriginItemsFuelCertificateMotive
    (operationalFuel : Nat) (expressions : List Expr) (resultIndex : Nat)
    (inputDemand : OriginEnvironmentDemand)
    (_plan : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
      inputDemand) : Prop :=
  ∀ {signature staticFuel context supply generated next},
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context expressions supply
      generated next) →
    Nonempty (ExactRawOriginItemsFuelCertificate elaboration operationalFuel
      resultIndex inputDemand)

private def RawOriginCallCertificateMotive
    (operationalFuel : Nat) (arguments : List Expr)
    (demands : List OriginDemand) (inputDemand : OriginEnvironmentDemand)
    (_plan : RawOriginCallPlan operationalFuel arguments demands inputDemand) :
    Prop :=
  ∀ {signature staticFuel context accumulated supply generated next},
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      accumulated arguments supply generated next) →
    Nonempty (ExactRawOriginCallCertificate call operationalFuel demands
      inputDemand)

namespace RawOriginRequestProducerHandlers

private theorem timeout : ∀ {expression outputDemand},
    RawOriginRequestCertificateMotive 0 expression outputDemand OriginEnvironmentDemand.none
      .timeout := by
  intro expression outputDemand signature staticFuel context supply generated
    next elaboration
  exact ⟨ExactRawOriginRequestCertificate.timeout elaboration _⟩

private theorem var : ∀ {operationalFuel position outputDemand},
    RawOriginRequestCertificateMotive operationalFuel (.var position) outputDemand
      (OriginEnvironmentDemand.single position outputDemand) .var := by
  intro operationalFuel position outputDemand signature staticFuel context
    supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel => exact ⟨ExactRawOriginRequestCertificate.var elaboration _ _⟩

private theorem litFuel : ∀ {operationalFuel literal resultIndex},
    RawOriginRequestCertificateMotive operationalFuel (.lit literal) (.fuel resultIndex)
      OriginEnvironmentDemand.none .litFuel := by
  intro operationalFuel literal resultIndex signature staticFuel context supply
    generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel => exact ⟨ExactRawOriginRequestCertificate.litFuel elaboration _ _⟩

private theorem litInt : ∀ {operationalFuel literal},
    RawOriginRequestCertificateMotive operationalFuel (.lit literal) .int
      OriginEnvironmentDemand.none .litInt := by
  intro operationalFuel literal signature staticFuel context supply generated
    next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      exact ⟨ExactRawOriginRequestCertificate.litInt elaboration _⟩

private theorem somethingFuel : ∀ {operationalFuel resultIndex},
    RawOriginRequestCertificateMotive operationalFuel .something (.fuel resultIndex)
      OriginEnvironmentDemand.none .somethingFuel := by
  intro operationalFuel resultIndex signature staticFuel context supply
    generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel => exact ⟨ExactRawOriginRequestCertificate.somethingFuel elaboration _ _⟩

private theorem ctor :
    ∀ {constructor demands outputDemand childFuel expressions input}
      (result : RawOriginConstructorResultPlan constructor demands outputDemand)
      (arguments : RawOriginCallPlan childFuel expressions demands input),
      RawOriginCallCertificateMotive childFuel expressions demands input
          arguments →
        RawOriginRequestCertificateMotive (childFuel + 1)
          (.ctor constructor expressions) outputDemand input
          (.ctor result arguments) := by
  intro constructor demands outputDemand childFuel expressions input result
    arguments argumentsIH signature staticFuel context supply generated next
    elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.ctor elaboration childFuel
        outputDemand demands input
      · intro scheme call
        exact argumentsIH call
      · intro compatible scheme lookup solution semantic call values
          expectedTypes callSemantic valuesSafe
        exact result.valueSafe compatible lookup semantic call callSemantic
          valuesSafe

private theorem prim :
    ∀ {operation demands outputDemand childFuel expressions input}
      (result : RawOriginPrimitiveResultPlan operation demands outputDemand)
      (arguments : RawOriginCallPlan childFuel expressions demands input),
      RawOriginCallCertificateMotive childFuel expressions demands input
          arguments →
        RawOriginRequestCertificateMotive (childFuel + 1)
          (.prim operation expressions) outputDemand input
          (.prim result arguments) := by
  intro operation demands outputDemand childFuel expressions input result
    arguments argumentsIH signature staticFuel context supply generated next
    elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.prim elaboration childFuel
        outputDemand demands input
      · intro scheme call
        exact argumentsIH call
      · intro compatible scheme lookup solution semantic call values
          expectedTypes callSemantic valuesSafe
        exact result.resultSafe compatible lookup semantic call callSemantic
          valuesSafe

private theorem primMap :
    ∀ {childFuel functionExpression argumentDemand resultDemand functionInput
        inputExpression inputInput}
      (functionPlan : RawOriginRequestPlan childFuel functionExpression
        (.plainCall childFuel argumentDemand resultDemand) functionInput)
      (inputPlan : RawOriginRequestPlan childFuel inputExpression
        (.listOf argumentDemand) inputInput),
      RawOriginRequestCertificateMotive childFuel functionExpression
          (.plainCall childFuel argumentDemand resultDemand) functionInput
          functionPlan →
        RawOriginRequestCertificateMotive childFuel inputExpression
            (.listOf argumentDemand) inputInput inputPlan →
          RawOriginRequestCertificateMotive (childFuel + 1)
            (.prim .map [functionExpression, inputExpression])
            (.listOf resultDemand)
            (OriginEnvironmentDemand.both functionInput inputInput)
            (.primMap functionPlan inputPlan) := by
  intro childFuel functionExpression argumentDemand resultDemand functionInput
    inputExpression inputInput functionPlan inputPlan functionIH inputIH
    signature staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.primMap elaboration childFuel
        argumentDemand resultDemand functionInput inputInput
      · intro childSupply generatedFunction afterFunction
          functionElaboration
        exact functionIH functionElaboration
      · intro childSupply generatedInput afterInput inputElaboration
        exact inputIH inputElaboration

private theorem ifE :
    ∀ {childFuel conditionExpression conditionInput thenExpression
        outputDemand thenInput elseExpression elseInput}
      (condition : RawOriginRequestPlan childFuel conditionExpression .bool
        conditionInput)
      (thenBranch : RawOriginRequestPlan childFuel thenExpression outputDemand
        thenInput)
      (elseBranch : RawOriginRequestPlan childFuel elseExpression outputDemand
        elseInput),
      RawOriginRequestCertificateMotive childFuel conditionExpression .bool
          conditionInput condition →
        RawOriginRequestCertificateMotive childFuel thenExpression outputDemand
            thenInput thenBranch →
          RawOriginRequestCertificateMotive childFuel elseExpression outputDemand
              elseInput elseBranch →
            RawOriginRequestCertificateMotive (childFuel + 1)
              (.ifE conditionExpression thenExpression elseExpression)
              outputDemand
              (OriginEnvironmentDemand.both conditionInput
                (OriginEnvironmentDemand.both thenInput elseInput))
              (.ifE condition thenBranch elseBranch) := by
  intro childFuel conditionExpression conditionInput thenExpression
    outputDemand thenInput elseExpression elseInput condition thenBranch
    elseBranch conditionIH thenIH elseIH signature staticFuel context supply
    generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.ifE elaboration childFuel
        outputDemand conditionInput thenInput elseInput
      · intro generatedCondition afterCondition conditionElaboration
        exact conditionIH conditionElaboration
      · intro afterCondition generatedThen afterThen
          thenElaboration
        exact thenIH thenElaboration
      · intro afterThen generatedElse afterElse elseElaboration
        exact elseIH elseElaboration

private theorem tuplePair :
    ∀ {childFuel leftExpression leftDemand leftInput rightExpression
        rightDemand rightInput}
      (left : RawOriginRequestPlan childFuel leftExpression leftDemand
        leftInput)
      (right : RawOriginRequestPlan childFuel rightExpression rightDemand
        rightInput),
      RawOriginRequestCertificateMotive childFuel leftExpression leftDemand
          leftInput left →
        RawOriginRequestCertificateMotive childFuel rightExpression rightDemand
            rightInput right →
          RawOriginRequestCertificateMotive (childFuel + 1)
            (.tuple [leftExpression, rightExpression])
            (.pairOf leftDemand rightDemand)
            (OriginEnvironmentDemand.both leftInput rightInput)
            (.tuplePair left right) := by
  intro childFuel leftExpression leftDemand leftInput rightExpression
    rightDemand rightInput left right leftIH rightIH signature staticFuel
    context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.tuplePair elaboration _ _ _ _ _
      · intro generatedLeft afterLeft leftElaboration
        exact leftIH leftElaboration
      · intro generatedLeft afterLeft generatedRight leftElaboration
          rightElaboration
        exact rightIH rightElaboration

private theorem tupleFuel : ∀ {childFuel expressions resultIndex input}
    (items : RawOriginItemsFuelPlan childFuel expressions resultIndex input),
    RawOriginItemsFuelCertificateMotive childFuel expressions resultIndex input
      items →
    RawOriginRequestCertificateMotive (childFuel + 1) (.tuple expressions)
      (.fuel resultIndex) input (.tupleFuel items) := by
  intro childFuel expressions resultIndex input items itemsIH signature
    staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.tupleFuel elaboration _ _ _
      intro generatedItems itemsElaboration
      exact itemsIH itemsElaboration

private theorem lamPlainCall :
    ∀ {bodyOperationalFuel body resultDemand bodyInput argumentDemand
        lambdaOperationalFuel}
      (bodyPlan : RawOriginRequestPlan bodyOperationalFuel body resultDemand bodyInput)
      (argumentCoversBody : OriginDemand.Le (bodyInput 0) argumentDemand),
      RawOriginRequestCertificateMotive bodyOperationalFuel body resultDemand bodyInput
          bodyPlan →
        RawOriginRequestCertificateMotive lambdaOperationalFuel (.lam body)
          (.plainCall (bodyOperationalFuel + 1) argumentDemand resultDemand)
          (OriginEnvironmentDemand.tail bodyInput)
          (.lamPlainCall bodyPlan argumentCoversBody) := by
  intro bodyOperationalFuel body resultDemand bodyInput argumentDemand
    lambdaOperationalFuel bodyPlan argumentCoversBody bodyIH signature
    staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.lamPlainCall elaboration _
      · intro generatedBody bodyElaboration
        exact bodyIH bodyElaboration
      · exact argumentCoversBody

private theorem lamZeroCall : ∀ {lambdaOperationalFuel body argumentDemand resultDemand},
    RawOriginRequestCertificateMotive lambdaOperationalFuel (.lam body)
      (.plainCall 0 argumentDemand resultDemand) OriginEnvironmentDemand.none
      .lamZeroCall := by
  intro lambdaOperationalFuel body argumentDemand resultDemand signature
    staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      exact ExactRawOriginRequestCertificate.lamZeroCall elaboration _ _ _

private theorem app :
    ∀ {childFuel function argumentDemand resultDemand functionInput argument
        argumentInput}
      (functionPlan : RawOriginRequestPlan childFuel function
        (.plainCall childFuel argumentDemand resultDemand) functionInput)
      (argumentPlan : RawOriginRequestPlan childFuel argument argumentDemand argumentInput),
      RawOriginRequestCertificateMotive childFuel function
          (.plainCall childFuel argumentDemand resultDemand) functionInput
          functionPlan →
        RawOriginRequestCertificateMotive childFuel argument argumentDemand argumentInput
            argumentPlan →
          RawOriginRequestCertificateMotive (childFuel + 1) (.app function argument)
            resultDemand (OriginEnvironmentDemand.both functionInput
              argumentInput)
            (.app functionPlan argumentPlan) := by
  intro childFuel function argumentDemand resultDemand functionInput argument
    argumentInput functionPlan argumentPlan functionIH argumentIH
    signature staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.app elaboration _ _
      · intro generatedFunction afterFunction generatedArgument afterArgument
          functionElaboration argumentElaboration
        exact functionIH functionElaboration
      · intro generatedFunction afterFunction generatedArgument afterArgument
          functionElaboration argumentElaboration
        exact argumentIH argumentElaboration

private theorem letUniversalInput :
    ∀ {childFuel value bodyInput valueInput body outputDemand}
      (valuePlan : RawOriginRequestPlan childFuel value (bodyInput 0)
        valueInput)
      (valueInputUniversal : ∀ position,
        OriginDemand.Universal (valueInput position))
      (bodyPlan : RawOriginRequestPlan childFuel body outputDemand bodyInput),
      RawOriginRequestCertificateMotive childFuel value (bodyInput 0)
          valueInput valuePlan →
        RawOriginRequestCertificateMotive childFuel body outputDemand bodyInput
            bodyPlan →
          RawOriginRequestCertificateMotive (childFuel + 1)
            (.letE value body) outputDemand
            (OriginEnvironmentDemand.tail bodyInput)
            (.letUniversalInput valuePlan valueInputUniversal bodyPlan) := by
  intro childFuel value bodyInput valueInput body outputDemand valuePlan
    valueInputUniversal bodyPlan valueIH bodyIH signature staticFuel context
    supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.letUniversalInput elaboration
        valueInput bodyInput valueInputUniversal
      · intro generatedValue afterValue valueElaboration
        exact valueIH valueElaboration
      · intro generatedValue afterValue valueElaboration valueClosure
          bodyGenerated bodyElaboration
        exact bodyIH bodyElaboration

private theorem both :
    ∀ {operationalFuel expression leftDemand leftInput rightDemand rightInput}
      (left : RawOriginRequestPlan operationalFuel expression leftDemand leftInput)
      (right : RawOriginRequestPlan operationalFuel expression rightDemand rightInput),
      RawOriginRequestCertificateMotive operationalFuel expression leftDemand leftInput left →
        RawOriginRequestCertificateMotive operationalFuel expression rightDemand rightInput
            right →
          RawOriginRequestCertificateMotive operationalFuel expression (.both leftDemand
            rightDemand) (OriginEnvironmentDemand.both leftInput rightInput)
            (.both left right) := by
  intro operationalFuel expression leftDemand leftInput rightDemand rightInput
    left right leftIH rightIH signature staticFuel context supply generated next
    elaboration
  obtain ⟨leftExact⟩ := leftIH elaboration
  obtain ⟨rightExact⟩ := rightIH elaboration
  exact ⟨ExactRawOriginRequestCertificate.both leftExact rightExact⟩

private theorem weaken :
    ∀ {operationalFuel expression availableDemand input requestedDemand}
      (available : RawOriginRequestPlan operationalFuel expression availableDemand input)
      (weaken : OriginDemand.Le requestedDemand availableDemand),
      RawOriginRequestCertificateMotive operationalFuel expression availableDemand input
          available →
        RawOriginRequestCertificateMotive operationalFuel expression requestedDemand input
          (.weaken available weaken) := by
  intro operationalFuel expression availableDemand input requestedDemand
    available weaken availableIH signature staticFuel context supply generated
    next elaboration
  obtain ⟨availableExact⟩ := availableIH elaboration
  exact ⟨ExactRawOriginRequestCertificate.weaken availableExact weaken⟩

private theorem universal :
    ∀ {operationalFuel expression availableDemand input requestedDemand}
      (available : RawOriginRequestPlan operationalFuel expression availableDemand input)
      (requested : OriginDemand.Universal requestedDemand),
      RawOriginRequestCertificateMotive operationalFuel expression availableDemand input
          available →
        RawOriginRequestCertificateMotive operationalFuel expression requestedDemand input
          (.universal available requested) := by
  intro operationalFuel expression availableDemand input requestedDemand
    available requested availableIH signature staticFuel context supply
    generated next elaboration
  obtain ⟨availableExact⟩ := availableIH elaboration
  exact ⟨ExactRawOriginRequestCertificate.reobserveUniversal availableExact requested⟩

private theorem strengthenInput :
    ∀ {operationalFuel expression outputDemand input stronger}
      (available : RawOriginRequestPlan operationalFuel expression outputDemand input)
      (covers : ∀ position,
        OriginDemand.Le (input position) (stronger position)),
      RawOriginRequestCertificateMotive operationalFuel expression outputDemand input
          available →
        RawOriginRequestCertificateMotive operationalFuel expression outputDemand stronger
          (.strengthenInput available covers) := by
  intro operationalFuel expression outputDemand input stronger available covers
    availableIH signature staticFuel context supply generated next elaboration
  obtain ⟨availableExact⟩ := availableIH elaboration
  exact ⟨ExactRawOriginRequestCertificate.strengthenInput availableExact _ covers⟩

private theorem nil : ∀ {operationalFuel resultIndex},
    RawOriginItemsFuelCertificateMotive operationalFuel [] resultIndex
      OriginEnvironmentDemand.none .nil := by
  intro operationalFuel resultIndex signature staticFuel context supply
    generated next elaboration
  exact ⟨ExactRawOriginItemsFuelCertificate.nil elaboration _ _⟩

private theorem cons :
    ∀ {operationalFuel expression resultIndex headInput expressions tailInput}
      (head : RawOriginRequestPlan operationalFuel expression (.fuel resultIndex)
        headInput)
      (tail : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
        tailInput),
      RawOriginRequestCertificateMotive operationalFuel expression (.fuel resultIndex)
          headInput head →
        RawOriginItemsFuelCertificateMotive operationalFuel expressions
            resultIndex tailInput tail →
          RawOriginItemsFuelCertificateMotive operationalFuel
            (expression :: expressions) resultIndex
            (OriginEnvironmentDemand.both headInput tailInput)
            (.cons head tail) := by
  intro operationalFuel expression resultIndex headInput expressions tailInput
    head tail headIH tailIH signature staticFuel context supply generated next
    elaboration
  apply ExactRawOriginItemsFuelCertificate.cons elaboration _ _ _ _
  · intro generatedHead afterHead headElaboration
    exact headIH headElaboration
  · intro afterHead generatedTail tailElaboration
    exact tailIH tailElaboration

private theorem callNil : ∀ {operationalFuel},
    RawOriginCallCertificateMotive operationalFuel [] []
      OriginEnvironmentDemand.none .nil := by
  intro operationalFuel signature staticFuel context accumulated supply
    generated next call
  exact ExactRawOriginCallCertificate.nil call operationalFuel

private theorem callCons :
    ∀ {operationalFuel expression demand headInput expressions demands
        tailInput}
      (head : RawOriginRequestPlan operationalFuel expression demand headInput)
      (tail : RawOriginCallPlan operationalFuel expressions demands tailInput),
      RawOriginRequestCertificateMotive operationalFuel expression demand
          headInput head →
        RawOriginCallCertificateMotive operationalFuel expressions demands
            tailInput tail →
          RawOriginCallCertificateMotive operationalFuel
            (expression :: expressions) (demand :: demands)
            (OriginEnvironmentDemand.both headInput tailInput)
            (.cons head tail) := by
  intro operationalFuel expression demand headInput expressions demands
    tailInput head tail headIH tailIH signature staticFuel context accumulated
    supply generated next call
  apply ExactRawOriginCallCertificate.cons call operationalFuel demand demands
    headInput tailInput
  · intro generatedArgument afterArgument headElaboration
    exact headIH headElaboration
  · intro generatedArgument afterArgument generated next tailCall
    exact tailIH tailCall

end RawOriginRequestProducerHandlers

theorem RawOriginRequestPlan.certificate
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand inputDemand) :
    RawOriginRequestCertificateMotive operationalFuel expression outputDemand inputDemand
      plan :=
  RawOriginRequestPlan.rec (motive_1 := RawOriginRequestCertificateMotive)
    (motive_2 := RawOriginItemsFuelCertificateMotive)
    (motive_3 := RawOriginCallCertificateMotive)
    RawOriginRequestProducerHandlers.timeout RawOriginRequestProducerHandlers.var RawOriginRequestProducerHandlers.litFuel
    RawOriginRequestProducerHandlers.litInt
    RawOriginRequestProducerHandlers.somethingFuel RawOriginRequestProducerHandlers.ctor
    RawOriginRequestProducerHandlers.prim
    RawOriginRequestProducerHandlers.primMap
    RawOriginRequestProducerHandlers.ifE
    RawOriginRequestProducerHandlers.tuplePair
    RawOriginRequestProducerHandlers.tupleFuel
    RawOriginRequestProducerHandlers.lamPlainCall RawOriginRequestProducerHandlers.lamZeroCall
    RawOriginRequestProducerHandlers.app RawOriginRequestProducerHandlers.letUniversalInput
    RawOriginRequestProducerHandlers.both
    RawOriginRequestProducerHandlers.weaken RawOriginRequestProducerHandlers.universal
    RawOriginRequestProducerHandlers.strengthenInput RawOriginRequestProducerHandlers.nil
    RawOriginRequestProducerHandlers.cons RawOriginRequestProducerHandlers.callNil
    RawOriginRequestProducerHandlers.callCons plan

theorem RawOriginItemsFuelPlan.certificate
    (plan : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
      inputDemand) :
    RawOriginItemsFuelCertificateMotive operationalFuel expressions resultIndex
      inputDemand
      plan :=
  RawOriginItemsFuelPlan.rec (motive_1 := RawOriginRequestCertificateMotive)
    (motive_2 := RawOriginItemsFuelCertificateMotive)
    (motive_3 := RawOriginCallCertificateMotive)
    RawOriginRequestProducerHandlers.timeout RawOriginRequestProducerHandlers.var RawOriginRequestProducerHandlers.litFuel
    RawOriginRequestProducerHandlers.litInt
    RawOriginRequestProducerHandlers.somethingFuel RawOriginRequestProducerHandlers.ctor
    RawOriginRequestProducerHandlers.prim
    RawOriginRequestProducerHandlers.primMap
    RawOriginRequestProducerHandlers.ifE
    RawOriginRequestProducerHandlers.tuplePair
    RawOriginRequestProducerHandlers.tupleFuel
    RawOriginRequestProducerHandlers.lamPlainCall RawOriginRequestProducerHandlers.lamZeroCall
    RawOriginRequestProducerHandlers.app RawOriginRequestProducerHandlers.letUniversalInput
    RawOriginRequestProducerHandlers.both
    RawOriginRequestProducerHandlers.weaken RawOriginRequestProducerHandlers.universal
    RawOriginRequestProducerHandlers.strengthenInput RawOriginRequestProducerHandlers.nil
    RawOriginRequestProducerHandlers.cons RawOriginRequestProducerHandlers.callNil
    RawOriginRequestProducerHandlers.callCons plan

theorem RawOriginCallPlan.certificate
    (plan : RawOriginCallPlan operationalFuel arguments demands inputDemand) :
    RawOriginCallCertificateMotive operationalFuel arguments demands inputDemand
      plan :=
  RawOriginCallPlan.rec (motive_1 := RawOriginRequestCertificateMotive)
    (motive_2 := RawOriginItemsFuelCertificateMotive)
    (motive_3 := RawOriginCallCertificateMotive)
    RawOriginRequestProducerHandlers.timeout RawOriginRequestProducerHandlers.var RawOriginRequestProducerHandlers.litFuel
    RawOriginRequestProducerHandlers.litInt
    RawOriginRequestProducerHandlers.somethingFuel RawOriginRequestProducerHandlers.ctor
    RawOriginRequestProducerHandlers.prim
    RawOriginRequestProducerHandlers.primMap
    RawOriginRequestProducerHandlers.ifE
    RawOriginRequestProducerHandlers.tuplePair
    RawOriginRequestProducerHandlers.tupleFuel
    RawOriginRequestProducerHandlers.lamPlainCall RawOriginRequestProducerHandlers.lamZeroCall
    RawOriginRequestProducerHandlers.app RawOriginRequestProducerHandlers.letUniversalInput
    RawOriginRequestProducerHandlers.both
    RawOriginRequestProducerHandlers.weaken RawOriginRequestProducerHandlers.universal
    RawOriginRequestProducerHandlers.strengthenInput RawOriginRequestProducerHandlers.nil
    RawOriginRequestProducerHandlers.cons RawOriginRequestProducerHandlers.callNil
    RawOriginRequestProducerHandlers.callCons plan

/-- A static request plan produces an exact certificate for every matching
raw M4 derivation.  In particular, the advertised input demand is not hidden
behind the existential field of `RawOriginRequestCertificate`. -/
theorem RawOriginRequestPlan.exactCertificate
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next) :
    Nonempty (ExactRawOriginRequestCertificate elaboration operationalFuel
      outputDemand inputDemand) :=
  plan.certificate elaboration

/-- Convert the source-ordered tail plan to the runtime arm certificate used
by `FuelEmbeddedMatchFirstRuntimeCertificate`. -/
theorem RawOriginMatchFirstTailPlan.runtimeSafe
    {targetType matcherType expectedResult : Ty}
    {arms : List MatchFirstArm} {supply : Supply}
    {generated : MatchFirstTyping.GeneratedTail} {next : Supply}
    {elaboration : MatchFirstTyping.TailElaboratesUsing
      (ElaboratesFuel signature staticFuel) signature context targetType
      matcherType expectedResult arms supply generated next}
    (plan : RawOriginMatchFirstTailPlan signature staticFuel childFuel
      bindingIndex resultIndex context sourceTargets targetExpression
      matcherExpression elaboration)
    (compatible : SignatureCompatible signature.base)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible : MonomorphicContextCompatible context
      (Ty.applyList solution sourceTargets) solution)
    (outerFuelSafe : FuelEnvironmentSafe bindingIndex environment
      (Ty.applyList solution sourceTargets))
    (fallbackSafe : FuelResultSafe resultIndex (expectedResult.apply solution)
      (evalFuel childFuel environment fallback)) :
    TwoIndexMatchFirstArmsSafe childFuel bindingIndex resultIndex environment
      targetValue matcherValue (expectedResult.apply solution) arms fallback := by
  induction plan generalizing solution environment targetValue matcherValue
      fallback with
  | nil => exact .nil fallbackSafe
  | @cons pattern body arms supply generatedPattern afterPattern generatedBody
      afterBody generatedTail next patternElaboration bodyElaboration
      tailElaboration bodyInput patternMNodeFree bodyPlan bodyInputCovered
      initialState tailPlan tailIH =>
      have patternSemantic :=
        semanticSolution_fromMatchFirst_armPattern semantic
      have bodySemantic := semanticSolution_fromMatchFirst_armBody semantic
      have restSemantic := semanticSolution_fromMatchFirst_rest semantic
      have bodyTargetEq :=
        semanticSolution_fromMatchFirst_bodyTarget semantic
      obtain ⟨bodyExact⟩ := bodyPlan.exactCertificate bodyElaboration
      have bodyContextCompatible : MonomorphicContextCompatible
          (Pattern.extendContext generatedPattern.bindings context)
          (Ty.applyList solution generatedPattern.bindings ++
            Ty.applyList solution sourceTargets) solution := by
        simpa [Pattern.extendContext] using
          monomorphicContextCompatible_prepend generatedPattern.bindings
            contextCompatible
      apply TwoIndexMatchFirstArmsSafe.cons
        (initialState solution patternSemantic environment outerFuelSafe
          targetValue matcherValue)
      · intro bindings bindingsSafe
        have combinedFuelSafe := bindingsSafe.append outerFuelSafe
        have bodyEnvironmentSafe := OriginEnvironmentSafe.mono
          (FuelEnvironmentSafe.toOriginEnvironmentSafe combinedFuelSafe)
          bodyInputCovered
        have bodyResult := bodyExact.certificate.preserves compatible solution
          bodySemantic (bindings ++ environment)
          (by simpa [bodyExact.input_eq] using
            bodyEnvironmentSafe.toSchemeOrigin bodyContextCompatible)
        rw [bodyTargetEq] at bodyResult
        exact bodyResult.toFuel
      · exact tailIH restSemantic contextCompatible outerFuelSafe fallbackSafe

/-- The dedicated `matchFirst` plan exposes one exact demand-parametric raw
certificate while retaining the source-ordered tail evidence for search task
issuance. -/
theorem RawOriginMatchFirstPlan.exactCertificate
    (plan : RawOriginMatchFirstPlan elaboration childFuel bindingIndex resultIndex
      sourceTargets targetInput matcherInput fallbackInput) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.fuel resultIndex)
      (OriginEnvironmentDemand.both targetInput
        (OriginEnvironmentDemand.both matcherInput
          (OriginEnvironmentDemand.both fallbackInput
            (OriginEnvironmentDemand.fuel (fun _ => bindingIndex)))))) := by
  apply ExactRawOriginRequestCertificate.matchFirst elaboration childFuel
    bindingIndex resultIndex sourceTargets plan.contextEq targetInput
    matcherInput fallbackInput
  · intro childSupply generatedTarget afterTarget targetElaboration
    exact plan.targetPlan.exactCertificate targetElaboration
  · intro childSupply generatedMatcher afterMatcher matcherElaboration
    exact plan.matcherPlan.exactCertificate matcherElaboration
  · intro childSupply generatedFallback afterFallback fallbackElaboration
    exact plan.fallbackPlan.exactCertificate fallbackElaboration
  · exact plan.matcherRuntimeType
  · intro generatedTarget generatedMatcher generatedFallback generatedTail
      afterTarget afterMatcher afterFallback targetElaboration
      matcherElaboration fallbackElaboration tailElaboration compatible
      solution semantic contextCompatible environment outerFuelSafe fallbackSafe
      targetValue matcherValue
    exact (plan.tailPlan targetElaboration matcherElaboration
      fallbackElaboration tailElaboration).runtimeSafe compatible semantic
      contextCompatible outerFuelSafe fallbackSafe

/-- The bounded `matchAll` companion assembles its three ordinary child
plans, simple-matcher runtime type, and evaluated initial-state producer into
one exact raw Origin certificate. -/
theorem RawOriginMatchAllPlan.exactCertificate
    (plan : RawOriginMatchAllPlan elaboration childFuel bindingIndex resultIndex
      sourceTargets targetInput matcherInput bodyInput) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.fuel resultIndex)
      (OriginEnvironmentDemand.both targetInput
        (OriginEnvironmentDemand.both matcherInput
          (OriginEnvironmentDemand.fuel (fun _ => bindingIndex))))) := by
  apply ExactRawOriginRequestCertificate.matchAll elaboration childFuel
    bindingIndex resultIndex sourceTargets plan.contextEq targetInput
    matcherInput bodyInput plan.bodyInputCovered
  · intro childSupply generatedTarget afterTarget targetElaboration
    exact plan.targetPlan.exactCertificate targetElaboration
  · intro childSupply generatedMatcher afterMatcher matcherElaboration
    exact plan.matcherPlan.exactCertificate matcherElaboration
  · intro bodyContext childSupply generatedBody afterBody bodyElaboration
    exact plan.bodyPlan.exactCertificate bodyElaboration
  · exact plan.matcherRuntimeType
  · exact plan.initialState

/-- Turn the retained initial-state producer into the concrete issued-task
record expected by the later G8--G10 origin bridge.  Callback fuel and search
fuel are both the plan's `childFuel`; no task or completed search is guessed
before the two operand evaluations succeed. -/
theorem RawOriginMatchAllPlan.issuedTask
    {elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.matchAll targetExpression matcherExpression pattern bodyExpression)
      supply generated next}
    (plan : RawOriginMatchAllPlan elaboration childFuel bindingIndex resultIndex
      sourceTargets targetInput matcherInput bodyInput)
    (components : MatchAllElaboratesUsing
      (ElaboratesFuel signature staticFuel) signature context targetExpression
      matcherExpression pattern bodyExpression supply
      (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
        generatedBody) next)
    (compatible : SignatureCompatible signature.base)
    (semantic : (Generated.fromMatchAll generatedTarget generatedPattern
      generatedMatcher generatedBody).SemanticSolution solution)
    (outerSafe : FuelEnvironmentSafe bindingIndex environment
      (Ty.applyList solution sourceTargets))
    (targetSuccess : evalFuel childFuel environment targetExpression =
      .ok targetValue)
    (matcherSuccess : evalFuel childFuel environment matcherExpression =
      .ok matcherValue) :
    RawOriginMatchAllIssuedTask childFuel bindingIndex environment
      targetExpression matcherExpression pattern
      (Ty.applyList solution generatedPattern.bindings) targetValue matcherValue :=
  ⟨plan.patternMNodeFree, targetSuccess, matcherSuccess,
    plan.initialState components compatible solution semantic environment
      outerSafe⟩

/-- The arity-zero `letE` companion produces an exact certificate whose
outer input is precisely the conjunction of the right-hand-side demand and
the body's free-environment demand. -/
theorem RawOriginLetArityZeroPlan.exactCertificate
    (plan : RawOriginLetArityZeroPlan context childFuel value body outputDemand
      valueInput bodyInput)
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.letE value body) supply generated next) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      outputDemand (OriginEnvironmentDemand.both valueInput
        (OriginEnvironmentDemand.tail bodyInput))) := by
  apply ExactRawOriginRequestCertificate.letArityZero elaboration valueInput
    bodyInput plan.contextArityZero
  · intro generatedValue afterValue valueElaboration
    exact plan.valuePlan.exactCertificate valueElaboration
  · intro generatedValue afterValue valueElaboration valueClosure
      bodyGenerated bodyElaboration
    exact plan.bodyPlan.exactCertificate bodyElaboration

/-- Tuple-field companion of `RawOriginRequestPlan.exactCertificate`. -/
theorem RawOriginItemsFuelPlan.exactCertificate
    (plan : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
      inputDemand)
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context expressions supply
      generated next) :
    Nonempty (ExactRawOriginItemsFuelCertificate elaboration operationalFuel
      resultIndex inputDemand) :=
  plan.certificate elaboration

/-- Curried-call companion of `RawOriginRequestPlan.exactCertificate`.
It connects the demand list to the normalized static call spine and the
evaluator's left-to-right argument traversal. -/
theorem RawOriginCallPlan.exactCertificate
    (plan : RawOriginCallPlan operationalFuel arguments demands inputDemand)
    (call : CallElaboratesUsing (ElaboratesFuel signature staticFuel) context
      accumulated arguments supply generated next) :
    Nonempty (ExactRawOriginCallCertificate call operationalFuel demands
      inputDemand) :=
  plan.certificate call

namespace RawOriginRequestPlan

/-- Reobserve any supported evaluation only for absence of `stuck`.  The
existing input demand is retained; at a closed root it is harmless because
the empty runtime environment satisfies every per-position demand. -/
def rootNone
    (plan : RawOriginRequestPlan operationalFuel expression availableDemand inputDemand) :
    RawOriginRequestPlan operationalFuel expression .none inputDemand :=
  .universal plan .none

/-- Closed-root no-stuck consequence.  The plan fixes operational fuel and
all environment demands before the later semantic solution is supplied. -/
theorem closedNoStuckOfElaboration
    (plan : RawOriginRequestPlan operationalFuel expression .none inputDemand)
    (compatible : SignatureCompatible signature.base)
    (elaboration : ElaboratesFuel signature staticFuel [] expression supply
      generated next)
    (semantic : generated.SemanticSolution solution) :
    (evalFuel operationalFuel [] expression).NotStuck := by
  obtain ⟨exact⟩ := plan.exactCertificate elaboration
  exact (exact.certificate.preserves compatible solution semantic []
    (SchemeOriginEnvironmentSafe.nil exact.certificate.inputDemand
      solution)).notStuck

/-- A closed public M4 typing supplies the principal raw derivation and a
semantic solution required by the plan.  Postcomposing the principal closure
with the typing instance transports the generated target to the requested
public result type. -/
theorem closedOriginResultSafe
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (compatible : SignatureCompatible signature.base)
    (typing : Typing signature [] expression target) :
    OriginResultSafe outputDemand target
      (evalFuel operationalFuel [] expression) := by
  rcases typing with
    ⟨principal, ⟨derivation⟩, later, targetEquality⟩
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  obtain ⟨exact⟩ := plan.exactCertificate elaboration
  let solution := Subst.compose later derivation.closure.substitution
  have semantic : derivation.generated.SemanticSolution solution :=
    semanticSolution_postcompose
      (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
        derivation.closure)
      later
  have safe := exact.certificate.preserves compatible solution semantic []
    (SchemeOriginEnvironmentSafe.nil exact.certificate.inputDemand solution)
  have targetApplied :
      derivation.generated.target.apply solution = target := by
    calc
      derivation.generated.target.apply solution =
          (derivation.generated.target.apply
            derivation.closure.substitution).apply later := by
        simp [solution, Ty.apply_compose]
      _ = derivation.closure.target.apply later := by
        rfl
      _ = principal.apply later := by
        rw [← derivation.target_eq]
      _ = target := targetEquality
  rw [targetApplied] at safe
  exact safe

/-- Every closed public M4 typing with a realizable request avoids `stuck` at
the plan's evaluator fuel. -/
theorem closedNeverStuck
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (compatible : SignatureCompatible signature.base)
    (typing : Typing signature [] expression target) :
    (evalFuel operationalFuel [] expression).NotStuck :=
  (plan.closedOriginResultSafe compatible typing).notStuck

end RawOriginRequestPlan

/-- A source expression has a realizable no-stuck request at every evaluator
fuel.  The input demand may depend on fuel but is always fixed before a later
semantic solution or runtime environment is supplied. -/
def RawOriginNoStuckSupported (expression : Expr) : Prop :=
  ∀ operationalFuel,
    ∃ inputDemand,
      RawOriginRequestPlan operationalFuel expression .none inputDemand

/-- A closed public M4 typing in the uniformly supported fragment avoids
`stuck` at every evaluator fuel. -/
theorem RawOriginNoStuckSupported.closedNeverStuck
    (supported : RawOriginNoStuckSupported expression)
    (compatible : SignatureCompatible signature.base)
    (typing : Typing signature [] expression target)
    (operationalFuel : Nat) :
    (evalFuel operationalFuel [] expression).NotStuck := by
  obtain ⟨inputDemand, plan⟩ := supported operationalFuel
  exact plan.closedNeverStuck compatible typing

end TypePM.Source.M4
