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

The second regression fixes the boundary of `OriginDemand.CheckStable` with
the repository's actual Paper 1 user matcher closure.  That value is safe at
positive fuel under matcher type and has a genuine matcher-to-slot checking
conversion, but positive-fuel safety at the slot type is impossible.  This
prevents a later application theorem from silently becoming unrestricted.
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
raw lambda children.  Its argument demand is check-stable because its outer
node is a function call; its positive fuel leaves occur strictly below it. -/
theorem higherOrderCertificate (signature : FrozenSignature) :
    Nonempty (RawOriginRequestCertificate
      (higherOrderElaboration signature) 3 integerIdentityDemand) := by
  apply RawOriginRequestCertificate.appOfCheckStable
    (argumentStable := .plainCall)
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

/-- The constructor list itself records that positive fuel is outside the
check-stable demand fragment. -/
theorem positiveFuel_notCheckStable :
    ¬ OriginDemand.CheckStable (.fuel 1) := by
  intro stable
  cases stable

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

/-- At positive fuel the slot target is impossible for this actual user
matcher cursor: the only slot constructor requires a built-in matcher proof. -/
theorem actualMatcher_not_slotFuelSafe :
    ¬ FuelValueSafe 1 actualMatcher actualMatcherSlot := by
  intro targetSafe
  generalize valueEq : actualMatcher = value at targetSafe
  generalize typeEq : actualMatcherSlot = targetType at targetSafe
  cases targetSafe <;>
    simp_all [actualMatcherSlot, TypePM.DataTypes.bool, TypePM.DataTypes.list]
  rename_i _ _ _ _ typing
  rw [← valueEq] at typing
  exact typing.notMatcherClosure

theorem actualMatcher_not_slotOriginSafe :
    ¬ OriginValueSafe (.fuel 1) actualMatcher actualMatcherSlot := by
  intro safe
  exact actualMatcher_not_slotFuelSafe safe.toFuel

/-- Consequently there can be no unrestricted positive-fuel transport across
all checking conversions. -/
theorem positiveFuel_unrestrictedConversion_false :
    ¬ (∀ {value source expected conversionClass},
      CheckConversion conversionClass source expected →
      OriginValueSafe (.fuel 1) value source →
      OriginValueSafe (.fuel 1) value expected) := by
  intro unrestricted
  exact actualMatcher_not_slotOriginSafe
    (unrestricted actualMatcher_conversion actualMatcher_sourceOriginSafe)

end PositiveFuelConversionBoundary

end TypePM.Source.M4.RawOriginRequestCertificateRegression
