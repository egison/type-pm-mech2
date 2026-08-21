import TypePM.Source.M4MatchingAtomRuntimeBridge
import TypePM.Source.M4RecursiveMatcherTotalBridge

/-!
# Solved M4 `matchFirst` at the total-runtime boundary

This module turns the relational M4 rule for an explicit-fallback
`matchFirst` into the certificate consumed by common-fuel safety.  It covers
the executable built-in pattern fragment.  User-matcher dispatch and
constructor patterns deliberately remain outside this theorem.

The bridge keeps the dynamic evaluation order visible: the target and matcher
are typed once, before the source-ordered nonempty arm list.  Every arm body
has the fallback's solved result type, while the fallback itself is typed in
the original context.
-/

namespace TypePM.Source.MatchFirstTyping

open TypePM.Runtime
open TypePM.Source.M4.CompletenessArchitecture

/-- Direct runtime coverage for one ordinary arm.  The last field states the
only dynamic fact absent from source pattern elaboration: evaluating the
chosen built-in matcher produces the concrete matcher shape that implements
this pattern. -/
structure DirectArmRuntimeSupported
    (matcherExpression : Expr) (arm : MatchFirstArm) : Prop where
  pattern : MatcherTyping.DirectRuntimePatternSupported arm.pattern
  body : RuntimeSupported arm.body
  matcherShape : ∀ {fuel environment matcherValue},
    evalFuel fuel environment matcherExpression = .ok matcherValue →
      MatcherTyping.DirectPatternMatcherShape arm.pattern matcherValue

/-- Source-ordered coverage for all ordinary arms. -/
inductive DirectArmsRuntimeSupported (matcherExpression : Expr) :
    List MatchFirstArm → Prop where
  | nil : DirectArmsRuntimeSupported matcherExpression []
  | cons
      (head : DirectArmRuntimeSupported matcherExpression arm)
      (tail : DirectArmsRuntimeSupported matcherExpression arms) :
      DirectArmsRuntimeSupported matcherExpression (arm :: arms)

/-- Semantic solution for an ordinary-arm tail, which has no result field of
its own. -/
def GeneratedTail.SemanticSolution (generated : GeneratedTail)
    (solution : Subst) : Prop :=
  Solves solution generated.hard ∧
    ∀ obligation ∈ generated.pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)

/-- Semantic solution for the fallback-plus-arms block. -/
def GeneratedArms.SemanticSolution (generated : GeneratedArms)
    (solution : Subst) : Prop :=
  Solves solution generated.hard ∧
    ∀ obligation ∈ generated.pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)

/-- An M4 leaf in the existing structural runtime fragment has its solved raw
target as a runtime type. -/
theorem m4FuelRuntimeTyping
    (elaboration : M4.ElaboratesFuel signature fuel
      context expression supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : RuntimeSupported expression)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    RuntimeTyping expression (generated.target.apply solution) runtimeContext := by
  have sourceElaboration := elaboratesFuel_toM2_of_m2Fragment
    supported.toM2Fragment elaboration
  exact supported.elaboration_typing compatible.toSignatureCompatible
    sourceElaboration semantic contextCompatible

mutual

  /-- Direct patterns transport their embedded runtime-supported expression
  leaves from recursive M4 back to the independent M2 pattern relation used
  by the existing executable atom bridge. -/
  theorem patternElaborationToM2Direct
      (elaboration : PatternElaboratesUsing
        (M4.ElaboratesFuel signature fuel)
        signature context arguments pattern bindings
        supply generated next)
      (supported : MatcherTyping.DirectRuntimePatternSupported pattern) :
      PatternElaborates signature context arguments
        pattern bindings supply generated next := by
    cases elaboration with
    | var =>
        cases supported
        exact .var
    | wild =>
        cases supported
        exact .wild
    | value expressionElaboration =>
        cases supported with
        | value expressionSupported =>
            exact .value (elaboratesFuel_toM2_of_m2Fragment
              expressionSupported.toM2Fragment expressionElaboration)
    | ctor lookup arity fields =>
        cases supported with
        | ctor fieldsSupported =>
            exact .ctor lookup arity
              (patternsElaborationToM2Direct fields fieldsSupported)
    | tuple itemsElaboration =>
        cases supported with
        | tuple itemsSupported =>
            exact .tuple (patternsElaborationToM2Direct itemsElaboration
              itemsSupported)
    | and left right =>
        cases supported with
        | and leftSupported rightSupported =>
            exact .and (patternElaborationToM2Direct left leftSupported)
              (patternElaborationToM2Direct right rightSupported)
    | or left right bindingsEqual =>
        cases supported with
        | or leftSupported rightSupported =>
            exact .or (patternElaborationToM2Direct left leftSupported)
              (patternElaborationToM2Direct right rightSupported) bindingsEqual
    | embed lookup => cases supported
    | app lookup arity fields => cases supported

  /-- List counterpart of `patternElaborationToM2Direct`. -/
  theorem patternsElaborationToM2Direct
      (elaboration : PatternsElaborateUsing
        (M4.ElaboratesFuel signature fuel)
        signature context arguments patterns bindings
        supply generated next)
      (supported : MatcherTyping.DirectRuntimePatternsSupported patterns) :
      PatternsElaborate signature context arguments
        patterns bindings supply generated next := by
    cases elaboration with
    | nil =>
        cases supported
        exact .nil
    | cons head tail =>
        cases supported with
        | cons headSupported tailSupported =>
            exact .cons (patternElaborationToM2Direct head headSupported)
              (patternsElaborationToM2Direct tail tailSupported)

end

/-- Solving the block for one arm followed by a tail solves the pattern block
of that arm. -/
private theorem patternSemantic_of_tail
    {generatedTail : GeneratedTail}
    (semantic :
      (⟨(GeneratedTail.fromArm targetType matcherType expectedResult
            generatedPattern generatedBody).hard ++ generatedTail.hard,
          (GeneratedTail.fromArm targetType matcherType expectedResult
            generatedPattern generatedBody).pending ++ generatedTail.pending⟩ :
        GeneratedTail).SemanticSolution solution) :
    MatcherTyping.GeneratedPatternRuntimeSolution generatedPattern solution := by
  constructor
  · intro equation member
    exact semantic.1 equation (by
      simp [GeneratedTail.fromArm, member])
  · intro obligation member
    exact semantic.2 obligation (by
      simp [GeneratedTail.fromArm, member])

/-- Solving the block for one arm followed by a tail solves that arm body. -/
private theorem bodySemantic_of_tail
    {generatedTail : GeneratedTail}
    (semantic :
      (⟨(GeneratedTail.fromArm targetType matcherType expectedResult
            generatedPattern generatedBody).hard ++ generatedTail.hard,
          (GeneratedTail.fromArm targetType matcherType expectedResult
            generatedPattern generatedBody).pending ++ generatedTail.pending⟩ :
        GeneratedTail).SemanticSolution solution) :
    generatedBody.SemanticSolution solution := by
  constructor
  · intro equation member
    exact semantic.1 equation (by
      simp [GeneratedTail.fromArm, member])
  · intro obligation member
    exact semantic.2 obligation (by
      simp [GeneratedTail.fromArm, member])

/-- Solving the block for one arm followed by a tail also solves the tail. -/
private theorem restSemantic_of_tail
    {generatedTail : GeneratedTail}
    (semantic :
      (⟨(GeneratedTail.fromArm targetType matcherType expectedResult
            generatedPattern generatedBody).hard ++ generatedTail.hard,
          (GeneratedTail.fromArm targetType matcherType expectedResult
            generatedPattern generatedBody).pending ++ generatedTail.pending⟩ :
        GeneratedTail).SemanticSolution solution) :
    generatedTail.SemanticSolution solution := by
  constructor
  · intro equation member
    exact semantic.1 equation (by simp [member])
  · intro obligation member
    exact semantic.2 obligation (by simp [member])

/-- A solved relational ordinary-arm tail becomes the total source-ordered
runtime arm certificate. -/
theorem TailElaboratesUsing.toTotalMatchFirstArmsTyping
    (elaboration : TailElaboratesUsing
      (M4.ElaboratesFuel signature fuel)
      signature context targetType matcherType
      expectedResult arms supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : DirectArmsRuntimeSupported matcherExpression arms)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    TotalMatchFirstArmsTyping runtimeContext targetExpression matcherExpression
      (targetType.apply solution) capability (expectedResult.apply solution)
      arms := by
  induction elaboration with
  | nil =>
      cases supported
      exact .nil
  | @cons pattern body arms supply generatedPattern afterPattern generatedBody
      afterBody generatedTail next patternElaboration bodyElaboration
      tailElaboration tailInduction =>
      cases supported with
      | cons headSupported tailSupported =>
          have patternSemantic := patternSemantic_of_tail semantic
          have bodySemantic := bodySemantic_of_tail semantic
          have tailSemantic := restSemantic_of_tail semantic
          have patternElaborationM2 :=
            patternElaborationToM2Direct patternElaboration
              headSupported.pattern
          obtain ⟨bindingTypes, patternBinds, bindingsEq⟩ :=
            MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
              patternElaborationM2 compatible headSupported.pattern
              patternSemantic contextCompatible
          have patternTargetEq :
              generatedPattern.dual.target.apply solution =
                targetType.apply solution := by
            exact semantic.1
              (.ty generatedPattern.dual.target targetType) (by
              simp [GeneratedTail.fromArm])
          have bodyTargetEq :
              generatedBody.target.apply solution =
                expectedResult.apply solution := by
            exact semantic.1 (.ty generatedBody.target expectedResult) (by
              simp [GeneratedTail.fromArm])
          have bodyContextCompatible :=
            MatcherTyping.runtimeContextCompatible_extendPatternContext
              (bindings := generatedPattern.bindings) contextCompatible
          have bodyTyping := m4FuelRuntimeTyping bodyElaboration compatible
            headSupported.body bodySemantic bodyContextCompatible
          rw [bindingsEq] at bodyTyping
          rw [bodyTargetEq] at bodyTyping
          refine .cons ?_ (.core bodyTyping)
            (tailInduction tailSupported tailSemantic)
          intro atomFuel environment targetValue matcherValue environmentTyped
            targetSuccess matcherSuccess targetTyped matcherTyped
          have matcherShape := headSupported.matcherShape matcherSuccess
          rw [← patternTargetEq] at targetTyped
          exact .builtin
            (MatcherTyping.PatternBinds.toDirectMatchingAtomTyping
              patternBinds matcherShape targetTyped)

/-- The fallback-plus-arms semantic solution splits into the fallback block. -/
private theorem fallbackSemantic_of_arms
    (semantic : (GeneratedArms.fromFallback generatedFallback generatedTail).SemanticSolution
      solution) :
    generatedFallback.SemanticSolution solution := by
  constructor
  · intro equation member
    exact semantic.1 equation (by
      simp [GeneratedArms.fromFallback, member])
  · intro obligation member
    exact semantic.2 obligation (by
      simp [GeneratedArms.fromFallback, member])

/-- The fallback-plus-arms semantic solution splits into the ordinary tail. -/
private theorem tailSemantic_of_arms
    (semantic : (GeneratedArms.fromFallback generatedFallback generatedTail).SemanticSolution
      solution) :
    generatedTail.SemanticSolution solution := by
  constructor
  · intro equation member
    exact semantic.1 equation (by
      simp [GeneratedArms.fromFallback, member])
  · intro obligation member
    exact semantic.2 obligation (by
      simp [GeneratedArms.fromFallback, member])

/-- A solved nonempty arm relation supplies both the total arm loop and the
fallback typing under the unchanged runtime context. -/
theorem ArmsElaborateUsing.toTotalMatchFirstParts
    (elaboration : ArmsElaborateUsing
      (M4.ElaboratesFuel signature fuel)
      signature context targetType matcherType fallback
      arms supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : DirectArmsRuntimeSupported matcherExpression arms)
    (fallbackSupported : RuntimeSupported fallback)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    TotalMatchFirstArmsTyping runtimeContext targetExpression matcherExpression
        (targetType.apply solution) capability (generated.target.apply solution)
        arms ∧
      TotalCoreTyping fallback (generated.target.apply solution) runtimeContext := by
  cases elaboration with
  | @fromFallback first rest supply generatedFallback afterFallback
      generatedTail next fallbackElaboration armsElaboration =>
      have fallbackSemantic := fallbackSemantic_of_arms semantic
      have tailSemantic := tailSemantic_of_arms semantic
      exact ⟨
        armsElaboration.toTotalMatchFirstArmsTyping compatible supported
          tailSemantic contextCompatible,
        .core (m4FuelRuntimeTyping fallbackElaboration compatible
          fallbackSupported fallbackSemantic contextCompatible)⟩

/-- Component form of the built-in `matchFirst` bridge.  `matcherConversion`
is the producer view of the solved matcher expression: source elaboration
checks a matcher against slots, whereas common-fuel safety types the once-only
matcher expression at its matcher type. -/
theorem toTotalCoreTyping
    (targetElaboration : M4.ElaboratesFuel signature fuel
      context target supply generatedTarget afterTarget)
    (matcherElaboration : M4.ElaboratesFuel signature fuel
      context matcher afterTarget generatedMatcher afterMatcher)
    (armsElaboration : ArmsElaborateUsing
      (M4.ElaboratesFuel signature fuel)
      signature context generatedTarget.target
      generatedMatcher.target fallback arms afterMatcher generatedArms next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (targetSupported : RuntimeSupported target)
    (matcherSupported : RuntimeSupported matcher)
    (armsSupported : DirectArmsRuntimeSupported matcher arms)
    (fallbackSupported : RuntimeSupported fallback)
    (semantic : (Generated.fromMatchFirst generatedTarget generatedMatcher
      generatedArms).SemanticSolution solution)
    (matcherConversion : CheckConversion conversionClass
      (generatedMatcher.target.apply solution)
      (.matcher capability (generatedTarget.target.apply solution)))
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    TotalCoreTyping (.matchFirst target matcher arms fallback)
      (generatedArms.target.apply solution) runtimeContext := by
  have targetSemantic : generatedTarget.SemanticSolution solution := by
    constructor
    · intro equation member
      exact semantic.1 equation (by
        simp [Generated.fromMatchFirst, member])
    · intro obligation member
      exact semantic.2 obligation (by
        simp [Generated.fromMatchFirst, member])
  have matcherSemantic : generatedMatcher.SemanticSolution solution := by
    constructor
    · intro equation member
      exact semantic.1 equation (by
        simp [Generated.fromMatchFirst, member])
    · intro obligation member
      exact semantic.2 obligation (by
        simp [Generated.fromMatchFirst, member])
  have armsSemantic : generatedArms.SemanticSolution solution := by
    constructor
    · intro equation member
      exact semantic.1 equation (by
        simp [Generated.fromMatchFirst, member])
    · intro obligation member
      exact semantic.2 obligation (by
        simp [Generated.fromMatchFirst, member])
  have targetTyping := m4FuelRuntimeTyping targetElaboration compatible
    targetSupported targetSemantic contextCompatible
  have matcherRawTyping := m4FuelRuntimeTyping matcherElaboration compatible
    matcherSupported matcherSemantic contextCompatible
  have matcherTyping : RuntimeTyping matcher
      (.matcher capability (generatedTarget.target.apply solution))
      runtimeContext :=
    .checked matcherRawTyping matcherConversion
  obtain ⟨armsTyping, fallbackTyping⟩ :=
    armsElaboration.toTotalMatchFirstParts compatible armsSupported
      fallbackSupported armsSemantic contextCompatible
  exact .matchFirst (.core targetTyping) (.core matcherTyping) armsTyping
    fallbackTyping

/-- Full-relation endpoint for the primitive `something` matcher.  Its matcher
type is polymorphic in the target, so no separate producer conversion premise
is needed.  The relational `ArmsElaborateUsing.fromFallback` constructor makes
the source arm list nonempty. -/
theorem m4FuelSomethingMatchFirstToTotalCoreTyping
    (elaboration : M4.ElaboratesFuel signature (fuel + 1)
      context (.matchFirst target .something arms fallback) supply generated
      next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (targetSupported : RuntimeSupported target)
    (armsSupported : DirectArmsRuntimeSupported .something arms)
    (fallbackSupported : RuntimeSupported fallback)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    TotalCoreTyping (.matchFirst target .something arms fallback)
      (generated.target.apply solution) runtimeContext := by
  change ElaboratesUsing
    (M4.ElaboratesFuel signature fuel)
    signature context
    (.matchFirst target .something arms fallback) supply generated next at elaboration
  cases elaboration with
  | matchFirst targetElaboration matcherElaboration armsElaboration =>
      rename_i generatedTarget afterTarget generatedMatcher afterMatcher
        generatedArms
      have targetSemantic : generatedTarget.SemanticSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by
            simp [Generated.fromMatchFirst, member])
        · intro obligation member
          exact semantic.2 obligation (by
            simp [Generated.fromMatchFirst, member])
      have armsSemantic : generatedArms.SemanticSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by
            simp [Generated.fromMatchFirst, member])
        · intro obligation member
          exact semantic.2 obligation (by
            simp [Generated.fromMatchFirst, member])
      have targetTyping := m4FuelRuntimeTyping targetElaboration compatible
        targetSupported targetSemantic contextCompatible
      obtain ⟨armsTyping, fallbackTyping⟩ :=
        armsElaboration.toTotalMatchFirstParts compatible armsSupported
          fallbackSupported armsSemantic contextCompatible
      exact .matchFirst (.core targetTyping)
        (.core (.something (generatedTarget.target.apply solution)))
        armsTyping fallbackTyping

/-- Compatibility of an explicit runtime context with the exact principal
closure selected from a proof of `M4.PrincipalTyping`.  The closure
substitution is intentionally retained in this certificate: the inferred
result type alone does not determine how free source variables are
instantiated. -/
structure PrincipalRuntimeContextSupport
    (signature : FrozenSignature)
    (typing : M4.PrincipalTyping signature context
      expression principal)
    (runtimeContext : List Ty) : Prop where
  compatible : MonomorphicContextCompatible context runtimeContext
    (Classical.choice typing).closure.substitution

/-- Open-context principal endpoint for the direct-pattern `something`
fragment.  `contextSupport` ties the explicit runtime context to the hidden
principal closure selected from `typing`; no equality between source and
runtime contexts is guessed from the public result type. -/
theorem principalSomethingMatchFirstToTotalCoreTypingInContext
    (typing : M4.PrincipalTyping signature context
      (.matchFirst target .something arms fallback) principal)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (targetSupported : RuntimeSupported target)
    (armsSupported : DirectArmsRuntimeSupported .something arms)
    (fallbackSupported : RuntimeSupported fallback)
    (contextSupport : PrincipalRuntimeContextSupport signature typing
      runtimeContext) :
    TotalCoreTyping (.matchFirst target .something arms fallback)
      principal runtimeContext := by
  let derivation := Classical.choice typing
  rcases derivation.elaboration with ⟨fuel, elaboration⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at elaboration
  | succ fuel =>
      let solution := derivation.closure.substitution
      have semantic : derivation.generated.SemanticSolution solution :=
        TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
          derivation.closure
      have bridged := m4FuelSomethingMatchFirstToTotalCoreTyping
        elaboration compatible targetSupported armsSupported fallbackSupported
          semantic (by simpa [derivation] using contextSupport.compatible)
      rw [derivation.target_eq]
      simpa [PrincipalBlockClosure.target, solution] using bridged

/-- Closed-context specialization.  Source/runtime context correspondence is
canonical and therefore needs no separate premise; frozen-signature runtime
compatibility remains explicit. -/
theorem principalSomethingMatchFirstToTotalCoreTyping
    (typing : M4.PrincipalTyping signature []
      (.matchFirst target .something arms fallback) principal)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (targetSupported : RuntimeSupported target)
    (armsSupported : DirectArmsRuntimeSupported .something arms)
    (fallbackSupported : RuntimeSupported fallback) :
    TotalCoreTyping (.matchFirst target .something arms fallback)
      principal [] :=
  principalSomethingMatchFirstToTotalCoreTypingInContext typing compatible
    targetSupported armsSupported fallbackSupported
    ⟨MonomorphicContextCompatible.nil⟩

/-- Public-inference endpoint with an explicit runtime context.  The support
premise refers to the precise principal proof produced by infer soundness, so
its hidden closure substitution cannot silently drift. -/
theorem inferSomethingMatchFirstToTotalCoreTypingInContext
    (success : M4.infer signature context
      (.matchFirst target .something arms fallback) = some principal)
    (wellFormed : signature.WellFormed)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (targetSupported : RuntimeSupported target)
    (armsSupported : DirectArmsRuntimeSupported .something arms)
    (fallbackSupported : RuntimeSupported fallback)
    (contextSupport : PrincipalRuntimeContextSupport signature
      (M4.infer_success_principalTyping wellFormed success) runtimeContext) :
    TotalCoreTyping (.matchFirst target .something arms fallback)
      principal runtimeContext :=
  principalSomethingMatchFirstToTotalCoreTypingInContext
    (M4.infer_success_principalTyping wellFormed success) compatible
    targetSupported armsSupported fallbackSupported contextSupport

/-- Closed-context public-inference specialization. -/
theorem inferSomethingMatchFirstToTotalCoreTyping
    (success : M4.infer signature []
      (.matchFirst target .something arms fallback) = some principal)
    (wellFormed : signature.WellFormed)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (targetSupported : RuntimeSupported target)
    (armsSupported : DirectArmsRuntimeSupported .something arms)
    (fallbackSupported : RuntimeSupported fallback) :
    TotalCoreTyping (.matchFirst target .something arms fallback)
      principal [] :=
  inferSomethingMatchFirstToTotalCoreTypingInContext success wellFormed
    compatible targetSupported armsSupported fallbackSupported
    ⟨MonomorphicContextCompatible.nil⟩

end TypePM.Source.MatchFirstTyping
