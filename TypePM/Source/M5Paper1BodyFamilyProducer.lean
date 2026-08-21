import TypePM.Source.M5Paper1ClosureRequestProducer
import TypePM.Source.M5Paper1ArityZeroLetProducer

/-!
# Raw-plan adapters for Paper-1 closure bodies

This module turns the search-free raw plan families into the body-certificate
interfaces consumed by the closed closure producers.  Applicability of every
requested body result and coverage of the lambda argument are explicit: a raw
plan family intentionally has no plan for an ill-shaped result demand.

For recursive bodies, safety of the runtime environment containing the
argument and recursive self is the only dynamic bridge retained as a premise.
The child elaboration, child semantic solution, and solved result-type
alignment are recovered from the outer `fixE` elaboration here.
-/

namespace TypePM.Source.M5Paper1BodyFamilyProducer

open TypePM.Runtime
open M5CompletionArchitecture
open M5Paper1SearchFreeStructuralProducer
open M5Paper1ArityZeroLetProducer
open M5Paper1ClosureRequestProducer

/-! ## Solution-parametric raw plan families -/

/-- A demand-only raw plan family.  Unlike `RawApplicablePlanFamily`, plan
selection does not inspect a type or semantic solution, so the same family can
be reused at every instance of a polymorphic closure. -/
structure RawTotalPlanFamily (expression : Expr) : Type where
  inputDemand : Nat → OriginDemand → OriginEnvironmentDemand
  plan : ∀ operationalFuel outputDemand,
    M4.RawOriginRequestPlan operationalFuel expression outputDemand
      (inputDemand operationalFuel outputDemand)

namespace RawTotalPlanFamily

/-- A variable forwards every observation to its selected environment
position and is therefore solution-parametric. -/
def var (position : Nat) : RawTotalPlanFamily (.var position) where
  inputDemand := fun _ outputDemand =>
    OriginEnvironmentDemand.single position outputDemand
  plan := by
    intro operationalFuel outputDemand
    exact .var

end RawTotalPlanFamily

structure SolutionParametricLambdaRawPlanConditions
    (bodyPlan : RawTotalPlanFamily body) : Prop where
  argumentCovers : ∀ bodyFuel argumentDemand resultDemand,
    OriginDemand.Le (bodyPlan.inputDemand bodyFuel resultDemand 0)
      argumentDemand

/-- Turn a demand-only body plan into the solution-parametric lambda family
used by the public polymorphic closure producer. -/
def solutionParametricLambdaCallBodyFamilyOfRawPlan
    (bodyPlan : RawTotalPlanFamily body)
    (conditions : SolutionParametricLambdaRawPlanConditions bodyPlan) :
    SolutionParametricLambdaCallBodyFamily signature body where
  bodyInput := fun bodyFuel _argumentDemand resultDemand =>
    bodyPlan.inputDemand bodyFuel resultDemand
  certificate := by
    intro bodyFuel argumentDemand resultDemand staticFuel supply generatedBody
      next bodyElaboration
    exact (bodyPlan.plan bodyFuel resultDemand).exactCertificate bodyElaboration
  argumentCovers := conditions.argumentCovers

/-! ## Lambda bodies -/

/-- The lambda argument must cover position zero of every selected body plan.
Result applicability is supplied call-by-call at the shared codomain index. -/
structure LambdaRawPlanConditions
    (bodyPlan : RawApplicablePlanFamily body bodyTarget) : Prop where
  argumentCovers : ∀ bodyFuel argumentDemand resultDemand domain,
    OriginDemandApplicable argumentDemand domain →
    OriginDemand.Le (bodyPlan.inputDemand bodyFuel resultDemand 0)
      argumentDemand

/-- Adapt one raw body-plan family to the exact extended-context certificates
required by a lambda. -/
def lambdaCallBodyFamilyOfRawPlan
    (bodyPlan : RawApplicablePlanFamily body bodyTarget)
    (conditions : LambdaRawPlanConditions bodyPlan) :
    LambdaCallBodyFamily signature body domain bodyTarget where
  bodyInput := fun bodyFuel _argumentDemand resultDemand =>
    bodyPlan.inputDemand bodyFuel resultDemand
  certificate := by
    intro bodyFuel argumentDemand resultDemand staticFuel supply generatedBody
      next argumentApplicable resultApplicable bodyElaboration
    exact (bodyPlan.plan bodyFuel resultDemand
      resultApplicable).exactCertificate
      bodyElaboration
  argumentCovers := conditions.argumentCovers

/-- Canonical `PlanScope` syntax reaches the same lambda adapter. -/
noncomputable def lambdaCallBodyFamilyOfPlanScope
    (scope : PlanScope body bodyTarget)
    (conditions : LambdaRawPlanConditions
      (RawApplicablePlanFamily.ofPlanScope scope)) :
    LambdaCallBodyFamily signature body domain bodyTarget :=
  lambdaCallBodyFamilyOfRawPlan
    (RawApplicablePlanFamily.ofPlanScope scope) conditions

/-! ## Recursive bodies -/

private theorem fromFix_semantic_parts
    (semantic : (Generated.fromFix domain codomain bodyGenerated).SemanticSolution
      solution) :
    bodyGenerated.SemanticSolution solution ∧
      Equation.Holds solution (.ty bodyGenerated.target codomain) := by
  constructor
  · constructor
    · intro equation membership
      exact semantic.1 equation (by simp [Generated.fromFix, membership])
    · intro obligation membership
      exact semantic.2 obligation (by
        simpa [Generated.fromFix] using membership)
  · exact semantic.1 _ (by simp [Generated.fromFix])

private theorem fixElaboration_parts
    (elaboration : FixElaboratesUsing
      (M4.ElaboratesFuel signature childStaticFuel) [] (.fixE body) supply
      generated next) :
    ∃ bodyGenerated,
      M4.ElaboratesFuel signature childStaticFuel
        (Fix.bodyContext (Fix.domain body supply) (Fix.codomain body supply) [])
        body (Fix.bodySupply body supply) bodyGenerated next ∧
      generated = Generated.fromFix (Fix.domain body supply)
        (Fix.codomain body supply) bodyGenerated := by
  cases elaboration with
  | fixE _direct bodyElaboration => exact ⟨_, bodyElaboration, rfl⟩

/-- The runtime-environment side condition for a demand-only recursive body
plan.  It is quantified over the outer semantic solution, so it does not fix
the recursive closure's domain or codomain. -/
def SolutionParametricRecursiveBodyEnvironmentSafe
    (signature : FrozenSignature)
    (bodyPlan : RawTotalPlanFamily body) : Prop :=
  ∀ {staticFuel supply generated next}
      (_elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
        supply generated next)
      bodyFuel argumentDemand resultDemand solution,
    generated.SemanticSolution solution →
      ∀ argument,
        OriginValueSafe argumentDemand argument
            ((Fix.domain body supply).apply solution) →
          SchemeOriginEnvironmentSafe
            (bodyPlan.inputDemand bodyFuel resultDemand) solution
            [argument, Value.recursiveClosure [] body]
            (Fix.bodyContext (Fix.domain body supply)
              (Fix.codomain body supply) [])

/-- A demand-only body plan yields recursive-body safety at every semantic
solution.  In particular, plan selection never inspects the solved codomain. -/
theorem solutionParametricPlainFixBodyOriginSafe_of_rawPlan
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (bodyPlan : RawTotalPlanFamily body)
    (recursiveEnvironmentSafe :
      SolutionParametricRecursiveBodyEnvironmentSafe signature bodyPlan)
    (elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
      supply generated next)
    (semantic : generated.SemanticSolution solution) :
    MatcherTyping.PlainFixBodyOriginSafe [] body
      ((Fix.domain body supply).apply solution)
      ((Fix.codomain body supply).apply solution)
      bodyFuel argumentDemand resultDemand := by
  intro argument argumentSafe
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ childStaticFuel =>
      have fixElaboration : FixElaboratesUsing
          (M4.ElaboratesFuel signature childStaticFuel) [] (.fixE body)
          supply generated next := by
        simpa only [M4.ElaboratesFuel] using elaboration
      obtain ⟨bodyGenerated, bodyElaboration, generatedEq⟩ :=
        fixElaboration_parts fixElaboration
      have parentSemantic : (Generated.fromFix (Fix.domain body supply)
          (Fix.codomain body supply) bodyGenerated).SemanticSolution
          solution := by
        rw [← generatedEq]
        exact semantic
      obtain ⟨bodySemantic, bodyEquation⟩ :=
        fromFix_semantic_parts parentSemantic
      obtain ⟨exactCertificate⟩ :=
        (bodyPlan.plan bodyFuel resultDemand).exactCertificate bodyElaboration
      have safe := exactCertificate.certificate.preserves
        compatible.toSignatureCompatible solution bodySemantic
        [argument, Value.recursiveClosure [] body]
        (by
          simpa [exactCertificate.input_eq] using
            recursiveEnvironmentSafe elaboration bodyFuel argumentDemand
              resultDemand solution semantic argument argumentSafe)
      simp only [Equation.Holds] at bodyEquation
      rw [bodyEquation] at safe
      exact safe

/-- Static and dynamic conditions for a solution-parametric ordinary
recursive closure. -/
structure SolutionParametricPlainFixRawPlanConditions
    (bodyPlan : RawTotalPlanFamily body) : Prop where
  bodyTyped : ∀ {staticFuel supply generated next}
      (_elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
        supply generated next) solution,
    generated.SemanticSolution solution →
      TotalRecursiveClosureBodyTyping
        [((Fix.domain body supply).apply solution),
          .fn ((Fix.domain body supply).apply solution)
            ((Fix.codomain body supply).apply solution)]
        body ((Fix.codomain body supply).apply solution)
  recursiveEnvironmentSafe :
    SolutionParametricRecursiveBodyEnvironmentSafe signature bodyPlan

/-- Adapt a demand-only raw body plan to the public solution-parametric
ordinary-`fixE` interface. -/
def solutionParametricPlainFixCallFamilyOfRawPlan
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (bodyPlan : RawTotalPlanFamily body)
    (conditions : SolutionParametricPlainFixRawPlanConditions bodyPlan) :
    SolutionParametricPlainFixCallFamily signature body where
  bodyTyped := conditions.bodyTyped
  bodySafe := by
    intro staticFuel supply generated next elaboration bodyFuel argumentDemand
      resultDemand solution semantic
    exact solutionParametricPlainFixBodyOriginSafe_of_rawPlan compatible
      bodyPlan conditions.recursiveEnvironmentSafe elaboration semantic

/-- The missing recursive component of a raw body plan: its selected input
demand must be safe for the actual argument/recursive-self environment. -/
def RecursiveBodyEnvironmentSafe
    (signature : FrozenSignature)
    (bodyPlan : RawApplicablePlanFamily body bodyTarget) : Prop :=
  ∀ {staticFuel supply generated next}
      (_elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
        supply generated next)
      bodyFuel argumentDemand resultDemand solution,
    generated.SemanticSolution solution →
      ∀ argument,
        OriginValueSafe argumentDemand argument
            ((Fix.domain body supply).apply solution) →
          SchemeOriginEnvironmentSafe
            (bodyPlan.inputDemand bodyFuel resultDemand) solution
            [argument, Value.recursiveClosure [] body]
            (Fix.bodyContext (Fix.domain body supply)
              (Fix.codomain body supply) [])

/-- A raw body plan plus recursive-environment safety yields the dynamic body
property required by an ordinary or matcher-root `fixE`. -/
theorem plainFixBodyOriginSafe_of_rawPlan
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (bodyPlan : RawApplicablePlanFamily body observedCodomain)
    (recursiveEnvironmentSafe : RecursiveBodyEnvironmentSafe
      signature bodyPlan)
    (observedResultApplicable : OriginDemandApplicable resultDemand
      observedCodomain)
    (elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
      supply generated next)
    (semantic : generated.SemanticSolution solution) :
    MatcherTyping.PlainFixBodyOriginSafe [] body
      ((Fix.domain body supply).apply solution)
      ((Fix.codomain body supply).apply solution)
      bodyFuel argumentDemand resultDemand := by
  intro argument argumentSafe
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ childStaticFuel =>
      have fixElaboration : FixElaboratesUsing
          (M4.ElaboratesFuel signature childStaticFuel) [] (.fixE body)
          supply generated next := by
        simpa only [M4.ElaboratesFuel] using elaboration
      obtain ⟨bodyGenerated, bodyElaboration, generatedEq⟩ :=
        fixElaboration_parts fixElaboration
      have parentSemantic : (Generated.fromFix (Fix.domain body supply)
          (Fix.codomain body supply) bodyGenerated).SemanticSolution
          solution := by
        rw [← generatedEq]
        exact semantic
      obtain ⟨bodySemantic, bodyEquation⟩ :=
        fromFix_semantic_parts parentSemantic
      obtain ⟨exactCertificate⟩ :=
        (bodyPlan.plan bodyFuel resultDemand
          observedResultApplicable).exactCertificate bodyElaboration
      have safe := exactCertificate.certificate.preserves
        compatible.toSignatureCompatible solution bodySemantic
        [argument, Value.recursiveClosure [] body]
        (by
          simpa [exactCertificate.input_eq] using
            recursiveEnvironmentSafe elaboration bodyFuel argumentDemand
              resultDemand solution semantic argument argumentSafe)
      simp only [Equation.Holds] at bodyEquation
      rw [bodyEquation] at safe
      exact safe

/-- Static and dynamic conditions for adapting one raw plan to an ordinary
recursive closure.  Total body typing remains separate from the recursive
self observation needed by the raw plan. -/
structure PlainFixRawPlanConditions
    (bodyPlan : RawApplicablePlanFamily body bodyTarget) : Prop where
  bodyTyped : ∀ {staticFuel supply generated next}
      (_elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
        supply generated next) solution,
    generated.SemanticSolution solution →
      TotalRecursiveClosureBodyTyping
        [((Fix.domain body supply).apply solution),
          .fn ((Fix.domain body supply).apply solution)
            ((Fix.codomain body supply).apply solution)]
        body ((Fix.codomain body supply).apply solution)
  recursiveEnvironmentSafe : RecursiveBodyEnvironmentSafe
    signature bodyPlan

def plainFixCallFamilyOfRawPlan
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (bodyPlan : RawApplicablePlanFamily body bodyTarget)
    (conditions : PlainFixRawPlanConditions bodyPlan) :
    PlainFixCallFamily signature body domain bodyTarget where
  bodyTyped := conditions.bodyTyped
  bodySafe := by
    intro staticFuel supply generated next elaboration bodyFuel argumentDemand
      resultDemand argumentApplicable resultApplicable solution semantic
    exact plainFixBodyOriginSafe_of_rawPlan compatible bodyPlan
      conditions.recursiveEnvironmentSafe resultApplicable elaboration semantic

noncomputable def plainFixCallFamilyOfPlanScope
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (scope : PlanScope body bodyTarget)
    (conditions : PlainFixRawPlanConditions
      (RawApplicablePlanFamily.ofPlanScope scope)) :
    PlainFixCallFamily signature body domain bodyTarget :=
  plainFixCallFamilyOfRawPlan compatible
    (RawApplicablePlanFamily.ofPlanScope scope) conditions

/-- Matcher-root specialization: S8 supplies total body typing, so only the
raw plan's recursive argument/self environment remains as an explicit bridge. -/
structure MatcherFixRawPlanConditions
    (bodyPlan : RawApplicablePlanFamily (.matcher clauses) bodyTarget) : Prop where
  recursiveEnvironmentSafe : RecursiveBodyEnvironmentSafe
    signature bodyPlan

/-- The solution-parametric matcher-root adapter needs only recursive body
environment safety; S8 supplies total matcher-body typing. -/
structure SolutionParametricMatcherFixRawPlanConditions
    (bodyPlan : RawTotalPlanFamily (.matcher clauses)) : Prop where
  recursiveEnvironmentSafe :
    SolutionParametricRecursiveBodyEnvironmentSafe signature bodyPlan

def solutionParametricMatcherFixCallFamilyOfRawPlan
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (bodyPlan : RawTotalPlanFamily (.matcher clauses))
    (conditions : SolutionParametricMatcherFixRawPlanConditions bodyPlan) :
    SolutionParametricMatcherFixCallFamily signature clauses where
  bodySafe := by
    intro staticFuel supply generated next elaboration bodyFuel argumentDemand
      resultDemand solution semantic
    exact solutionParametricPlainFixBodyOriginSafe_of_rawPlan compatible
      bodyPlan conditions.recursiveEnvironmentSafe elaboration semantic

def matcherFixCallFamilyOfRawPlan
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (bodyPlan : RawApplicablePlanFamily (.matcher clauses) bodyTarget)
    (conditions : MatcherFixRawPlanConditions bodyPlan) :
    MatcherFixCallFamily signature clauses domain bodyTarget where
  bodySafe := by
    intro staticFuel supply generated next elaboration bodyFuel argumentDemand
      resultDemand argumentApplicable resultApplicable solution semantic
    exact plainFixBodyOriginSafe_of_rawPlan compatible bodyPlan
      conditions.recursiveEnvironmentSafe resultApplicable elaboration semantic

noncomputable def matcherFixCallFamilyOfPlanScope
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (scope : PlanScope (.matcher clauses) bodyTarget)
    (conditions : MatcherFixRawPlanConditions
      (RawApplicablePlanFamily.ofPlanScope scope)) :
    MatcherFixCallFamily signature clauses domain bodyTarget :=
  matcherFixCallFamilyOfRawPlan compatible
    (RawApplicablePlanFamily.ofPlanScope scope) conditions

end TypePM.Source.M5Paper1BodyFamilyProducer
