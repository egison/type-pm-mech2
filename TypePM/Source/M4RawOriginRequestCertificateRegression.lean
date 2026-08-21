import TypePM.Source.M4RawOriginRequestCertificate
import TypePM.StepIndexedPaper1ListSafetyRegression

/-!
# Regressions for raw structural-demand certificates

The first regression composes the actual raw M4 derivation of
`(lambda x => x) (lambda x => x)`.  Its result is itself an integer identity
function, observed by a nested `plainCall` demand.  The safety theorem uses
only the raw certificates, the generated block's explicit semantic solution,
and the empty source/runtime environment relation.  It does not assume an
evaluator equation or whole-program no-stuck premise.

The second regression checks that the repository's actual Paper 1 user
matcher closure crosses matcher-to-slot checking conversion at positive
fuel.  Additional product regressions cover both product conversion forms.
-/

namespace TypePM.Source.M4.RawOriginRequestCertificateRegression

open TypePM.Runtime

def identityBody : Expr := .var 0

def identityGenerated (supply : Supply) : Generated :=
  ⟨.fn (.var ⟨supply.ty⟩) (.var ⟨supply.ty⟩), [], []⟩

theorem identityBodyElaboration (signature : FrozenSignature)
    (context : Context) (supply : Supply) :
    ElaboratesFuel signature 1
      (Scheme.mono (.var ⟨supply.ty⟩) :: context) identityBody
      (supply.nextTy 1) ⟨.var ⟨supply.ty⟩, [], []⟩
      (supply.nextTy 1) := by
  simp [ElaboratesFuel, identityBody, Scheme.mono, Scheme.instantiate,
    PolyTy.ofTy, PolyTy.openBound]

theorem identityElaboration (signature : FrozenSignature)
    (context : Context) (supply : Supply) :
    ElaboratesFuel signature 2 context (.lam identityBody) supply
      (identityGenerated supply) (supply.nextTy 1) := by
  simp only [ElaboratesFuel]
  exact ⟨⟨.var ⟨supply.ty⟩, [], []⟩,
    identityBodyElaboration signature context supply, rfl⟩

/-- No choice principle is needed: the smaller variable certificate and its
head-demand coverage travel together in `LambdaBodyRequest`. -/
theorem identityCertificate
    {generated : Generated} {next : Supply}
    (elaboration : ElaboratesFuel signature 2 context (.lam identityBody)
      supply generated next)
    (lambdaFuel bodyFuel : Nat) (demand : OriginDemand) :
    Nonempty (RawOriginRequestCertificate elaboration lambdaFuel
      (.plainCall (bodyFuel + 1) demand demand)) := by
  apply RawOriginRequestCertificate.lamPlainCall
    (staticFuel := 1) (bodyOperationalFuel := bodyFuel)
    (lambdaOperationalFuel := lambdaFuel)
    (argumentDemand := demand) (resultDemand := demand)
    elaboration
  intro generatedBody bodyElaboration
  let certificate := RawOriginRequestCertificate.var
    bodyElaboration bodyFuel demand
  refine ⟨⟨certificate, ?_⟩⟩
  have selected : certificate.inputDemand 0 = demand := by
    change (RawOriginRequestCertificate.var bodyElaboration bodyFuel demand).inputDemand
      0 = demand
    exact RawOriginRequestCertificate.var_inputDemand_selected
      bodyElaboration bodyFuel demand
  rw [selected]
  exact OriginDemand.Le.refl demand

/-- A future call to the function-valued result as integer identity. -/
def integerIdentityDemand : OriginDemand :=
  .plainCall 2 (.fuel 1) (.fuel 1)

def higherOrderApplication : Expr :=
  .app (.lam identityBody) (.lam identityBody)

def higherOrderGenerated : Generated :=
  Generated.fromApp (identityGenerated ⟨0, 0⟩)
    (identityGenerated ⟨1, 0⟩) (.var ⟨2⟩) (.var ⟨3⟩)

theorem higherOrderElaboration (signature : FrozenSignature) :
    ElaboratesFuel signature 3 [] higherOrderApplication ⟨0, 0⟩
      higherOrderGenerated ⟨4, 0⟩ := by
  simp only [ElaboratesFuel]
  exact ⟨identityGenerated ⟨0, 0⟩, ⟨1, 0⟩,
    identityGenerated ⟨1, 0⟩, ⟨2, 0⟩,
    identityElaboration signature [] ⟨0, 0⟩,
    identityElaboration signature [] ⟨1, 0⟩, rfl, rfl⟩

/-- The complete raw application certificate is composed from the two actual
raw lambda children.  Its argument demand contains a nested positive fuel
leaf and is transported through the solved checking conversion. -/
theorem higherOrderCertificate (signature : FrozenSignature) :
    Nonempty (RawOriginRequestCertificate
      (higherOrderElaboration signature) 3 integerIdentityDemand) := by
  apply RawOriginRequestCertificate.app
  · intro generatedFunction afterFunction generatedArgument afterArgument
      functionElaboration argumentElaboration
    exact identityCertificate functionElaboration 2 1 integerIdentityDemand
  · intro generatedFunction afterFunction generatedArgument afterArgument
      functionElaboration argumentElaboration
    exact identityCertificate argumentElaboration 2 1 (.fuel 1)

def integerFunction : Ty := .fn .int .int

def higherOrderSolution : Subst :=
  Subst.compose (Subst.singleTy ⟨3⟩ integerFunction)
    (Subst.compose (Subst.singleTy ⟨2⟩ integerFunction)
      (Subst.compose (Subst.singleTy ⟨1⟩ .int)
        (Subst.singleTy ⟨0⟩ integerFunction)))

theorem higherOrderSemantic :
    higherOrderGenerated.SemanticSolution higherOrderSolution := by
  constructor
  · intro equation membership
    simp [higherOrderGenerated, Generated.fromApp, identityGenerated] at membership
    subst equation
    simp [Equation.Holds, higherOrderSolution, integerFunction,
      Subst.singleTy, Subst.compose, Ty.apply]
  · intro obligation membership
    simp [higherOrderGenerated, Generated.fromApp, identityGenerated] at membership
    subst obligation
    refine ⟨.ordinary, ?_⟩
    simpa [higherOrderSolution, integerFunction, Subst.singleTy,
      Subst.compose, Ty.apply] using
      (CheckConversion.ordinary : CheckConversion .ordinary
        integerFunction integerFunction)

theorem higherOrderTargetApplied :
    higherOrderGenerated.target.apply higherOrderSolution = integerFunction := by
  simp [higherOrderGenerated, Generated.fromApp, higherOrderSolution,
    integerFunction, Subst.singleTy, Subst.compose, Ty.apply]

/-- Function-valued safety follows from the raw certificate, not an exact
evaluation result. -/
theorem higherOrderResultSafe (signature : FrozenSignature) :
    OriginResultSafe integerIdentityDemand integerFunction
      (evalFuel 3 [] higherOrderApplication) := by
  obtain ⟨certificate⟩ := higherOrderCertificate signature
  have safe := certificate.preserves higherOrderSolution higherOrderSemantic []
    (SchemeOriginEnvironmentSafe.nil certificate.inputDemand
      higherOrderSolution)
  simpa [higherOrderTargetApplied] using safe

theorem higherOrderNotStuck (signature : FrozenSignature) :
    (evalFuel 3 [] higherOrderApplication).NotStuck :=
  (higherOrderResultSafe signature).notStuck

/-- Exact success is checked only after the certificate-based safety theorem,
so neither the certificate nor `higherOrderResultSafe` can use this equation
as an oracle. -/
theorem higherOrderExact :
    evalFuel 3 [] higherOrderApplication =
      .ok (Value.plainClosure [] identityBody) := by
  rfl

namespace PositiveFuelConversionBoundary

open TypePM.Source.Paper1Programs
open TypePM.Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open TypePM.StepIndexedPaper1ListSafetyRegression

def actualMatcher : Value :=
  .matcherV [.something, listRecursiveClosure]
    listMatcherClauses listMatcherClauses

def actualMatcherSlot : Ty :=
  .slot (.con PatternFormer.list [.any]) (DataTypes.list .int)

theorem actualMatcher_sourceFuelSafe :
    FuelValueSafe 1 actualMatcher concreteListCodomain := by
  exact listMatcherClosure_concreteFuelValueSafe .something 1
    (fuelValueSafe_somethingSlot .int 1)

theorem actualMatcher_sourceOriginSafe :
    OriginValueSafe (.fuel 1) actualMatcher concreteListCodomain :=
  OriginValueSafe.ofFuel actualMatcher_sourceFuelSafe

theorem actualMatcher_conversion :
    CheckConversion .matcherToSlot concreteListCodomain actualMatcherSlot := by
  exact .matcherToSlot .equal

/-- A generated matcher now retains its matcher-specific certificate in the
slot layer, so positive fuel crosses matcher-to-slot conversion. -/
theorem actualMatcher_slotFuelSafe :
    FuelValueSafe 1 actualMatcher actualMatcherSlot :=
  FuelValueSafe.ofCheckConversion actualMatcher_conversion 1 actualMatcher
    actualMatcher_sourceFuelSafe

theorem actualMatcher_slotOriginSafe :
    OriginValueSafe (.fuel 1) actualMatcher actualMatcherSlot :=
  actualMatcher_sourceOriginSafe.ofCheckConversion actualMatcher_conversion

def actualMatcherDual : Dual :=
  ⟨.con PatternFormer.list [.any], DataTypes.list .int⟩

def actualMatcherProductSource : Ty :=
  .prod [concreteListCodomain]

def actualMatcherProductTarget : Ty :=
  .matcher (.prod [.con PatternFormer.list [.any]])
    (.prod [DataTypes.list .int])

def actualMatcherProductSlot : Ty :=
  .slot (.prod [.con PatternFormer.list [.any]])
    (.prod [DataTypes.list .int])

theorem actualMatcherProduct_sourceFuelSafe :
    FuelValueSafe 1 (.tuple [actualMatcher]) actualMatcherProductSource := by
  exact fuelValueSafe_tuple_of_environment 1 [actualMatcher]
    [concreteListCodomain]
    (FuelEnvironmentSafe.cons actualMatcher_sourceFuelSafe
      (FuelEnvironmentSafe.nil 1))

theorem actualMatcherProduct_conversion :
    CheckConversion .productMatcher actualMatcherProductSource
      actualMatcherProductTarget := by
  simpa [actualMatcherDual, actualMatcherProductSource, concreteListCodomain,
    actualMatcherProductTarget, Dual.matcherType, Dual.capabilities,
    Dual.targets] using
      (CheckConversion.productMatcher (duals := [actualMatcherDual]) (by simp))

theorem actualMatcherProductToSlot_conversion :
    CheckConversion .productMatcherToSlot actualMatcherProductSource
      actualMatcherProductSlot := by
  simpa [actualMatcherDual, actualMatcherProductSource, concreteListCodomain,
    actualMatcherProductSlot, Dual.matcherType, Dual.capabilities,
    Dual.targets] using
      (CheckConversion.productMatcherToSlot
        (duals := [actualMatcherDual]) (consumer := .prod
          [.con PatternFormer.list [.any]]) (by simp) CapabilityDemand.equal)

theorem actualMatcherProduct_targetFuelSafe :
    FuelValueSafe 1 (.tuple [actualMatcher]) actualMatcherProductTarget :=
  FuelValueSafe.ofCheckConversion actualMatcherProduct_conversion 1 _
    actualMatcherProduct_sourceFuelSafe

theorem actualMatcherProduct_slotFuelSafe :
    FuelValueSafe 1 (.tuple [actualMatcher]) actualMatcherProductSlot :=
  FuelValueSafe.ofCheckConversion actualMatcherProductToSlot_conversion 1 _
    actualMatcherProduct_sourceFuelSafe

/-- Arbitrary positive-fuel observations now cross all normalized checking
conversions. -/
theorem positiveFuel_unrestrictedConversion
    {value source expected conversionClass}
    (conversion : CheckConversion conversionClass source expected)
    (safe : OriginValueSafe (.fuel 1) value source) :
    OriginValueSafe (.fuel 1) value expected :=
  safe.ofCheckConversion conversion

end PositiveFuelConversionBoundary

end TypePM.Source.M4.RawOriginRequestCertificateRegression
