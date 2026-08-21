import TypePM.Source.M4TwoIndexCanonicalAtomReducerBridge
import TypePM.Source.M5CompletionArchitecture
import TypePM.TwoIndexMatchAllSafety

/-!
# Origin-demand evaluation at the matching-search boundary

This module composes demand-indexed embedded evaluation with the general
two-index bounded DFS theorem.  The operational predecessor fuel is shared by
target evaluation, matcher evaluation, atom callbacks, DFS visits, and body
evaluation exactly as in `evalFuel`; the logical indices retained on search
bindings and requested from body results remain independent.

The certificates here are runtime-boundary records.  A full expression
producer may construct them from its M4 derivation and its chosen
`FuelEmbeddedExpressionCertificateFamily`; no completed-search equation is a
field.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Certificate-family coverage needed by one two-index atom callback.  The
embedded expression typing selects a fuel-leaf output certificate and proves
that the callback's stronger successor-index environment is sufficient for
the certificate's structural input demand. -/
def TwoIndexEmbeddedCertificateProducer
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (expressionTyping : EmbeddedExpressionTyping)
    (operationalFuel : Nat) : Prop :=
  ∀ {searchFuel residual bindingTypes environmentTypes expression target},
    expressionTyping (bindingTypes ++ environmentTypes) expression target →
      ∃ inputDemand,
        Certificate operationalFuel bindingTypes environmentTypes expression
          target (.fuel (searchFuel + residual)) inputDemand ∧
        ∀ {bindings environment},
          FuelEnvironmentSafe (searchFuel + 1 + residual)
            (bindings ++ environment) (bindingTypes ++ environmentTypes) →
          OriginEnvironmentSafe inputDemand (bindings ++ environment)
            (bindingTypes ++ environmentTypes)

/-- Demand-indexed embedded evaluation discharges the numeric callback
contract used by the two-index canonical reducer whenever the certificate
producer selects the corresponding fuel leaf. -/
theorem twoIndexEmbeddedEvaluatorSafe_of_fuelEmbedded
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evalFuel)
    (producer : TwoIndexEmbeddedCertificateProducer Certificate
      expressionTyping operationalFuel) :
    TwoIndexEmbeddedEvaluatorSafe expressionTyping
      (evalFuel operationalFuel) := by
  intro searchFuel residual environmentTypes bindingTypes environment bindings
    expression target environmentSafe expressionTyped
  obtain ⟨inputDemand, certificate, inputSafe⟩ := producer expressionTyped
  exact (evalSafe certificate (inputSafe environmentSafe)).toFuel

/-- S10 local-reducer endpoint: the expression certificate family and G5's
recursive canonical dispatch evidence meet at the exact callback fuel used by
bounded DFS. -/
theorem evaluationAtomReducer_recursiveCanonicalTypedSafe_of_fuelEmbedded
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evalFuel)
    (producer : TwoIndexEmbeddedCertificateProducer Certificate
      expressionTyping operationalFuel) :
    TwoIndexRelationalAtomReducerTypedSafe FuelEnvironmentSafe
      FuelEnvironmentSafe
      (M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping
        (evalFuel operationalFuel))
      (evaluationAtomReducer (evalFuel operationalFuel)) :=
  evaluationAtomReducer_m4TwoIndexRecursiveCanonicalTypedSafe
    (twoIndexEmbeddedEvaluatorSafe_of_fuelEmbedded evalSafe producer)

/-- Demand-indexed components for one `matchAll` evaluation step.  All child
expression certificates use `operationalFuel`, while the enclosing evaluator
step uses `operationalFuel + 1`. -/
structure FuelEmbeddedMatchAllRuntimeCertificate
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (operationalFuel bindingIndex resultIndex : Nat)
    (environmentTypes : List Ty) (environment : ValueEnvironment)
    (targetExpression matcherExpression : Source.Expr)
    (pattern : Source.Pattern) (bodyExpression : Source.Expr)
    (matcherTarget bodyTarget : Ty) (capability : Cap)
    (bindingTypes : List Ty) where
  targetInput : OriginEnvironmentDemand
  targetCertificate : Certificate operationalFuel [] environmentTypes
    targetExpression matcherTarget (.fuel operationalFuel) targetInput
  targetEnvironmentSafe : OriginEnvironmentSafe targetInput environment
    environmentTypes
  matcherInput : OriginEnvironmentDemand
  matcherCertificate : Certificate operationalFuel [] environmentTypes
    matcherExpression (.matcher capability matcherTarget)
    (.fuel operationalFuel) matcherInput
  matcherEnvironmentSafe : OriginEnvironmentSafe matcherInput environment
    environmentTypes
  initialTyped : EvaluatedTwoIndexInitialStateTyping FuelEnvironmentSafe
    FuelEnvironmentSafe operationalFuel bindingIndex environment
    targetExpression matcherExpression pattern bindingTypes
  bodyInput : OriginEnvironmentDemand
  bodyCertificate : Certificate operationalFuel bindingTypes environmentTypes
    bodyExpression bodyTarget (.fuel resultIndex) bodyInput
  bodyEnvironmentSafe : ∀ bindings,
    FuelEnvironmentSafe bindingIndex bindings bindingTypes →
      OriginEnvironmentSafe bodyInput (bindings ++ environment)
        (bindingTypes ++ environmentTypes)

/-- The fuel-leaf result observation exported by the `matchAll` boundary is
applicable to its list result type. -/
theorem FuelEmbeddedMatchAllRuntimeCertificate.outputDemandApplicable :
    TypePM.Source.M5CompletionArchitecture.FuelDemandApplicable
      resultIndex bodyTarget →
    TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable
      (.fuel resultIndex) (DataTypes.list bodyTarget) := by
  intro applicable
  cases resultIndex with
  | zero =>
      exact TypePM.Source.M5CompletionArchitecture.originDemandApplicable_fuel_zero _
  | succ index =>
      exact TypePM.Source.M5CompletionArchitecture.originDemandApplicable_fuel
        (.list applicable)

/-- S10 `matchAll` boundary.  The one operational predecessor is visibly the
same in all five dynamic roles: both operand evaluations, atom callbacks, DFS
visits, and every selected body evaluation. -/
theorem FuelEmbeddedMatchAllRuntimeCertificate.eval_originResultSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evalFuel)
    (certificate : FuelEmbeddedMatchAllRuntimeCertificate Certificate
      operationalFuel bindingIndex resultIndex environmentTypes environment
      targetExpression matcherExpression pattern bodyExpression matcherTarget
      bodyTarget capability bindingTypes) :
    OriginResultSafe (.fuel resultIndex) (DataTypes.list bodyTarget)
      (evalFuel (operationalFuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern
          bodyExpression)) := by
  have targetOriginSafe : OriginResultSafe (.fuel operationalFuel)
      matcherTarget (evalFuel operationalFuel environment targetExpression) := by
    simpa using evalSafe (bindings := []) (environment := environment)
      certificate.targetCertificate (by
      simpa using certificate.targetEnvironmentSafe)
  have matcherOriginSafe : OriginResultSafe (.fuel operationalFuel)
      (.matcher capability matcherTarget)
      (evalFuel operationalFuel environment matcherExpression) := by
    simpa using evalSafe (bindings := []) (environment := environment)
      certificate.matcherCertificate (by
      simpa using certificate.matcherEnvironmentSafe)
  have bodySafe : EvaluatedBindingBodySafeUnder
      (FuelEnvironmentSafe bindingIndex) operationalFuel resultIndex
      environment bindingTypes bodyExpression bodyTarget := by
    intro bindings bindingsSafe
    exact (evalSafe certificate.bodyCertificate
      (certificate.bodyEnvironmentSafe bindings bindingsSafe)).toFuel
  apply OriginResultSafe.ofFuel
  exact matchAllFuel_twoIndexSafe
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    targetOriginSafe.toFuel matcherOriginSafe.toFuel certificate.initialTyped
    bodySafe

/-- Per-binding preservation of an arbitrary structural result observation.
This is the demand-indexed counterpart of `EvaluatedBindingBodySafeUnder`:
the operational body fuel, the logical binding index, and the observation
requested from each body result remain independent. -/
def EvaluatedOriginBindingBodySafeUnder
    (bindingsInvariant : MatchingBindingsInvariant)
    (operationalFuel : Nat) (resultDemand : OriginDemand)
    (environment : ValueEnvironment) (bindingTypes : List Ty)
    (bodyExpression : Source.Expr) (bodyTarget : Ty) : Prop :=
  ∀ bindings,
    bindingsInvariant bindings bindingTypes →
      OriginResultSafe resultDemand bodyTarget
        (evalFuel operationalFuel (bindings ++ environment) bodyExpression)

private theorem traverseEvaluatedOriginBindingBodiesUnder
    (answersSafe : MatchingAnswersSafeWith bindingsInvariant answers
      bindingTypes)
    (bodySafe : EvaluatedOriginBindingBodySafeUnder bindingsInvariant
      operationalFuel resultDemand environment bindingTypes bodyExpression
      bodyTarget) :
    FuelResult.traverse
        (fun bindings =>
          evalFuel operationalFuel (bindings ++ environment) bodyExpression)
        answers = .timeout ∨
      ∃ values,
        FuelResult.traverse
            (fun bindings =>
              evalFuel operationalFuel (bindings ++ environment)
                bodyExpression)
            answers = .ok values ∧
          ∀ value ∈ values,
            OriginValueSafe resultDemand value bodyTarget := by
  induction answers with
  | nil => exact .inr ⟨[], rfl, by simp⟩
  | cons bindings answers induction =>
      have bindingsSafe := answersSafe bindings (by simp)
      have tailSafe : MatchingAnswersSafeWith bindingsInvariant answers
          bindingTypes := by
        intro candidate member
        exact answersSafe candidate (by simp [member])
      rcases bodySafe bindings bindingsSafe with bodyTimeout |
        ⟨value, bodySuccess, valueSafe⟩
      · exact .inl (by simp [FuelResult.traverse, bodyTimeout])
      · rcases induction tailSafe with tailTimeout |
          ⟨values, tailSuccess, valuesSafe⟩
        · exact .inl (by
            simp [FuelResult.traverse, bodySuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨value :: values, by
            simp [FuelResult.traverse, bodySuccess, tailSuccess,
              FuelResult.bind, FuelResult.map], by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact valueSafe
            · exact valuesSafe candidate member⟩

private theorem originValueSafe_buildList
    (itemsSafe : ∀ value ∈ values,
      OriginValueSafe elementDemand value elementType) :
    OriginValueSafe (.listOf elementDemand) (Value.buildList values)
      (DataTypes.list elementType) := by
  induction values with
  | nil => exact OriginValueSafe.listNil
  | cons head tail induction =>
      exact OriginValueSafe.listCons
        (itemsSafe head (by simp))
        (induction (by
          intro value member
          exact itemsSafe value (by simp [member])))

/-- General structural-demand `matchAll` rule.  Unlike the earlier S10
boundary, the body result is not restricted to a fuel leaf: any finite
`OriginDemand` is preserved elementwise and exported as `.listOf` that same
demand.  Search callback fuel and DFS fuel are still the one executable
predecessor `operationalFuel`. -/
theorem matchAllFuel_twoIndexOriginSafe
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (targetSafe : OriginResultSafe (.fuel operationalFuel) matcherTarget
      (evalFuel operationalFuel environment targetExpression))
    (matcherSafe : OriginResultSafe (.fuel operationalFuel)
      (.matcher capability matcherTarget)
      (evalFuel operationalFuel environment matcherExpression))
    (initialTyped : EvaluatedTwoIndexInitialStateTyping environmentInvariant
      bindingsInvariant operationalFuel bindingIndex environment
      targetExpression matcherExpression pattern bindingTypes)
    (bodySafe : EvaluatedOriginBindingBodySafeUnder
      (bindingsInvariant bindingIndex) operationalFuel resultDemand environment
      bindingTypes bodyExpression bodyTarget) :
    OriginResultSafe (.listOf resultDemand) (DataTypes.list bodyTarget)
      (evalFuel (operationalFuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern
          bodyExpression)) := by
  rcases targetSafe.toFuel with targetTimeout |
    ⟨targetValue, targetSuccess, _targetValueSafe⟩
  · exact .inl (by
      simp [evalFuel, targetTimeout, FuelResult.bind])
  · rcases matcherSafe.toFuel with matcherTimeout |
      ⟨matcherValue, matcherSuccess, _matcherValueSafe⟩
    · exact .inl (by
        simp [evalFuel, targetSuccess, matcherTimeout, FuelResult.bind])
    · have searchSafe := searchPatternFuel_twoIndexSafe
        environmentDownward bindingsDownward
        (initialTyped targetValue matcherValue targetSuccess matcherSuccess)
      rcases searchSafe with searchTimeout |
        ⟨answers, searchSuccess, answersSafe⟩
      · exact .inl (by
          simp [evalFuel, targetSuccess, matcherSuccess, searchTimeout,
            FuelResult.bind])
      · rcases traverseEvaluatedOriginBindingBodiesUnder answersSafe
          bodySafe with bodiesTimeout |
          ⟨values, bodiesSuccess, valuesSafe⟩
        · exact .inl (by
            simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
              bodiesTimeout, FuelResult.bind, FuelResult.map])
        · exact .inr ⟨Value.buildList values, by
            simp [evalFuel, targetSuccess, matcherSuccess, searchSuccess,
              bodiesSuccess, FuelResult.bind, FuelResult.map],
            originValueSafe_buildList valuesSafe⟩

/-- Demand-indexed components for one `matchAll` step.  This is the general
form of `FuelEmbeddedMatchAllRuntimeCertificate`: the selected body
certificate may request any applicable finite origin demand, and the outer
result observes a list of values satisfying that demand. -/
structure OriginEmbeddedMatchAllRuntimeCertificate
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (operationalFuel bindingIndex : Nat) (resultDemand : OriginDemand)
    (environmentTypes : List Ty) (environment : ValueEnvironment)
    (targetExpression matcherExpression : Source.Expr)
    (pattern : Source.Pattern) (bodyExpression : Source.Expr)
    (matcherTarget bodyTarget : Ty) (capability : Cap)
    (bindingTypes : List Ty) where
  targetInput : OriginEnvironmentDemand
  targetCertificate : Certificate operationalFuel [] environmentTypes
    targetExpression matcherTarget (.fuel operationalFuel) targetInput
  targetEnvironmentSafe : OriginEnvironmentSafe targetInput environment
    environmentTypes
  matcherInput : OriginEnvironmentDemand
  matcherCertificate : Certificate operationalFuel [] environmentTypes
    matcherExpression (.matcher capability matcherTarget)
    (.fuel operationalFuel) matcherInput
  matcherEnvironmentSafe : OriginEnvironmentSafe matcherInput environment
    environmentTypes
  initialTyped : EvaluatedTwoIndexInitialStateTyping FuelEnvironmentSafe
    FuelEnvironmentSafe operationalFuel bindingIndex environment
    targetExpression matcherExpression pattern bindingTypes
  bodyInput : OriginEnvironmentDemand
  bodyCertificate : Certificate operationalFuel bindingTypes environmentTypes
    bodyExpression bodyTarget resultDemand bodyInput
  bodyEnvironmentSafe : ∀ bindings,
    FuelEnvironmentSafe bindingIndex bindings bindingTypes →
      OriginEnvironmentSafe bodyInput (bindings ++ environment)
        (bindingTypes ++ environmentTypes)

theorem OriginEmbeddedMatchAllRuntimeCertificate.outputDemandApplicable
    (bodyApplicable :
      TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable
        resultDemand bodyTarget) :
    TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable
      (.listOf resultDemand) (DataTypes.list bodyTarget) := by
  simp only [TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable]
  exact ⟨bodyTarget, rfl, bodyApplicable⟩

/-- General S10 `matchAll` boundary with an arbitrary applicable observation
on every selected body result. -/
theorem OriginEmbeddedMatchAllRuntimeCertificate.eval_originResultSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evalFuel)
    (certificate : OriginEmbeddedMatchAllRuntimeCertificate Certificate
      operationalFuel bindingIndex resultDemand environmentTypes environment
      targetExpression matcherExpression pattern bodyExpression matcherTarget
      bodyTarget capability bindingTypes) :
    OriginResultSafe (.listOf resultDemand) (DataTypes.list bodyTarget)
      (evalFuel (operationalFuel + 1) environment
        (.matchAll targetExpression matcherExpression pattern
          bodyExpression)) := by
  have targetSafe := evalSafe (bindings := []) (environment := environment)
    certificate.targetCertificate (by
      simpa using certificate.targetEnvironmentSafe)
  have matcherSafe := evalSafe (bindings := []) (environment := environment)
    certificate.matcherCertificate (by
      simpa using certificate.matcherEnvironmentSafe)
  have bodySafe : EvaluatedOriginBindingBodySafeUnder
      (FuelEnvironmentSafe bindingIndex) operationalFuel resultDemand
      environment bindingTypes bodyExpression bodyTarget := by
    intro bindings bindingsSafe
    exact evalSafe certificate.bodyCertificate
      (certificate.bodyEnvironmentSafe bindings bindingsSafe)
  exact matchAllFuel_twoIndexOriginSafe
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
    targetSafe matcherSafe certificate.initialTyped bodySafe

/-- Search/body preservation for an already evaluated `matchFirst` arm list.
Every arm may contribute a different binding type list, while all searches,
arm bodies, and the fallback use one shared operational fuel. -/
inductive TwoIndexMatchFirstArmsSafe
    (operationalFuel bindingIndex resultIndex : Nat)
    (environment : ValueEnvironment) (targetValue matcherValue : Value)
    (resultTarget : Ty) : List Source.MatchFirstArm → Source.Expr → Prop where
  | nil
      (fallbackSafe : FuelResultSafe resultIndex resultTarget
        (evalFuel operationalFuel environment fallback)) :
      TwoIndexMatchFirstArmsSafe operationalFuel bindingIndex resultIndex
        environment targetValue matcherValue resultTarget [] fallback
  | cons
      (initialTyped : TwoIndexMatchingStateTyping FuelEnvironmentSafe
        FuelEnvironmentSafe (evaluationAtomReducer (evalFuel operationalFuel))
        operationalFuel bindingIndex
        ⟨[⟨arm.pattern, matcherValue, targetValue⟩], environment, []⟩
        bindingTypes)
      (bodySafe : ∀ bindings,
        FuelEnvironmentSafe bindingIndex bindings bindingTypes →
          FuelResultSafe resultIndex resultTarget
            (evalFuel operationalFuel (bindings ++ environment) arm.body))
      (tail : TwoIndexMatchFirstArmsSafe operationalFuel bindingIndex
        resultIndex environment targetValue matcherValue resultTarget arms
        fallback) :
      TwoIndexMatchFirstArmsSafe operationalFuel bindingIndex resultIndex
        environment targetValue matcherValue resultTarget (arm :: arms)
        fallback

/-- The ordinary source-ordered `matchFirst` arm loop is safe from two-index
initial states.  Empty searches advance, nonempty searches select the first
binding group, and neither case assumes an exact completed search result. -/
theorem TwoIndexMatchFirstArmsSafe.eval_safe
    (safe : TwoIndexMatchFirstArmsSafe operationalFuel bindingIndex resultIndex
      environment targetValue matcherValue resultTarget arms fallback) :
    FuelResultSafe resultIndex resultTarget
      (evalMatchFirstArmsFuel (evalFuel operationalFuel) operationalFuel
        environment targetValue matcherValue arms fallback) := by
  induction safe with
  | nil fallbackSafe => simpa using fallbackSafe
  | @cons arm arms fallback bindingTypes initialTyped bodySafe tail induction =>
      have searchSafe := searchPatternFuel_twoIndexSafe
        IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
        IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
        initialTyped
      rcases searchSafe with searchTimeout |
        ⟨answers, searchSuccess, answersSafe⟩
      · exact .inl (by
          simp [evalMatchFirstArmsFuel, searchTimeout, FuelResult.bind])
      · cases answers with
        | nil =>
            rcases induction with tailTimeout |
              ⟨value, tailSuccess, valueSafe⟩
            · exact .inl (by
                simp [evalMatchFirstArmsFuel, searchSuccess, tailTimeout,
                  FuelResult.bind])
            · exact .inr ⟨value, by
                simp [evalMatchFirstArmsFuel, searchSuccess, tailSuccess,
                  FuelResult.bind], valueSafe⟩
        | cons bindings remainingAnswers =>
            have bindingsSafe := answersSafe bindings (by simp)
            rcases bodySafe bindings bindingsSafe with bodyTimeout |
              ⟨value, bodySuccess, valueSafe⟩
            · exact .inl (by
                simp [evalMatchFirstArmsFuel, searchSuccess, bodyTimeout,
                  FuelResult.bind])
            · exact .inr ⟨value, by
                simp [evalMatchFirstArmsFuel, searchSuccess, bodySuccess,
                  FuelResult.bind], valueSafe⟩

/-- Runtime-boundary components for one `matchFirst` evaluator step.  The
target and matcher certificates establish no-stuck classification before the
source-ordered arm certificate takes over. -/
structure FuelEmbeddedMatchFirstRuntimeCertificate
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (operationalFuel bindingIndex resultIndex : Nat)
    (environmentTypes : List Ty) (environment : ValueEnvironment)
    (targetExpression matcherExpression : Source.Expr)
    (arms : List Source.MatchFirstArm) (fallbackExpression : Source.Expr)
    (matcherTarget resultTarget : Ty) (capability : Cap) where
  targetInput : OriginEnvironmentDemand
  targetCertificate : Certificate operationalFuel [] environmentTypes
    targetExpression matcherTarget (.fuel operationalFuel) targetInput
  targetEnvironmentSafe : OriginEnvironmentSafe targetInput environment
    environmentTypes
  matcherInput : OriginEnvironmentDemand
  matcherCertificate : Certificate operationalFuel [] environmentTypes
    matcherExpression (.matcher capability matcherTarget)
    (.fuel operationalFuel) matcherInput
  matcherEnvironmentSafe : OriginEnvironmentSafe matcherInput environment
    environmentTypes
  armsSafe : ∀ targetValue matcherValue,
    evalFuel operationalFuel environment targetExpression = .ok targetValue →
    evalFuel operationalFuel environment matcherExpression = .ok matcherValue →
      TwoIndexMatchFirstArmsSafe operationalFuel bindingIndex resultIndex
        environment targetValue matcherValue resultTarget arms
        fallbackExpression

/-- The fuel-leaf result observation exported by the `matchFirst` boundary is
applicable to the common arm/fallback result type. -/
theorem FuelEmbeddedMatchFirstRuntimeCertificate.outputDemandApplicable :
    TypePM.Source.M5CompletionArchitecture.FuelDemandApplicable
      resultIndex resultTarget →
    TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable
      (.fuel resultIndex) resultTarget :=
  TypePM.Source.M5CompletionArchitecture.originDemandApplicable_fuel

/-- S10 `matchFirst` boundary with the same predecessor fuel shared by both
operands, every arm search, atom callback, selected body, and fallback. -/
theorem FuelEmbeddedMatchFirstRuntimeCertificate.eval_originResultSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evalFuel)
    (certificate : FuelEmbeddedMatchFirstRuntimeCertificate Certificate
      operationalFuel bindingIndex resultIndex environmentTypes environment
      targetExpression matcherExpression arms fallbackExpression matcherTarget
      resultTarget capability) :
    OriginResultSafe (.fuel resultIndex) resultTarget
      (evalFuel (operationalFuel + 1) environment
        (.matchFirst targetExpression matcherExpression arms
          fallbackExpression)) := by
  have targetOriginSafe : OriginResultSafe (.fuel operationalFuel)
      matcherTarget (evalFuel operationalFuel environment targetExpression) := by
    simpa using evalSafe (bindings := []) (environment := environment)
      certificate.targetCertificate (by
      simpa using certificate.targetEnvironmentSafe)
  have matcherOriginSafe : OriginResultSafe (.fuel operationalFuel)
      (.matcher capability matcherTarget)
      (evalFuel operationalFuel environment matcherExpression) := by
    simpa using evalSafe (bindings := []) (environment := environment)
      certificate.matcherCertificate (by
      simpa using certificate.matcherEnvironmentSafe)
  have targetSafe := targetOriginSafe.toFuel
  have matcherSafe := matcherOriginSafe.toFuel
  rcases targetSafe with targetTimeout |
    ⟨targetValue, targetSuccess, targetValueSafe⟩
  · exact .inl (by simp [evalFuel, targetTimeout, FuelResult.bind])
  · rcases matcherSafe with matcherTimeout |
      ⟨matcherValue, matcherSuccess, matcherValueSafe⟩
    · exact .inl (by
        simp [evalFuel, targetSuccess, matcherTimeout, FuelResult.bind])
    · have armsSafe := (certificate.armsSafe targetValue matcherValue
          targetSuccess matcherSuccess).eval_safe
      rcases armsSafe with armsTimeout | ⟨value, armsSuccess, valueSafe⟩
      · exact .inl (by
          simp [evalFuel, targetSuccess, matcherSuccess, armsTimeout,
            FuelResult.bind])
      · exact .inr ⟨value, by
          simp [evalFuel, targetSuccess, matcherSuccess, armsSuccess,
            FuelResult.bind], OriginValueSafe.ofFuel valueSafe⟩

end TypePM.Runtime
