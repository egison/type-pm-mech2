import TypePM.Source.M4OriginDemandSafety

/-!
# Closed higher-order structural-demand regression

This regression proves safety of
`(lambda f => f (lambda z => z)) (lambda g => g)`.  Its result is an integer
identity closure rather than a base literal.  Both the higher-order argument and the
returned closure are checked by nested call demands; the result additionally
carries a positive ordinary fuel observation, so the final theorem converts
the origin-aware certificate back to `FuelResultSafe 1` without using the
exact evaluator result.

The identity lambda passed inside the outer body is certified through an
actual raw M4 variable-body elaboration, `RawFuelCertificate.varWitness`, and
`RawFuelCertificate.plainCallSafe`.  The exact `.ok` result is stated only in
a separate theorem.

This remains a focused runtime/source bridge regression, not a general raw
M4 application or lambda producer.  Recursive functions, matchers, search,
and arbitrary nested origin demands in raw source environments remain open.
-/

namespace TypePM.Source.M4OriginDemandSafetyRegression

open TypePM.Runtime

def identityBody : Source.Expr :=
  .var 0

def identityValue : Value :=
  .plainClosure [] identityBody

def integerFunction : Ty :=
  .fn .int .int

def higherFunction : Ty :=
  .fn integerFunction integerFunction

/-- A future call to an integer identity closure. -/
def integerIdentityDemand : OriginDemand :=
  .plainCall 2 (.fuel 1) (.fuel 1)

/-- Observe both that the returned value can be called as integer identity
and that it has one ordinary fuel-safety layer. -/
def observableIntegerIdentityDemand : OriginDemand :=
  .both integerIdentityDemand (.fuel 1)

/-- The higher-order identity is itself callable, and its captured value is
also available at one ordinary fuel layer for the nested closure fixture. -/
def higherIdentityDemand : OriginDemand :=
  .both
    (.plainCall 3 observableIntegerIdentityDemand
      observableIntegerIdentityDemand)
    (.fuel 1)

private theorem identityValue_fuelSafe (index : Nat) (domain : Ty) :
    FuelValueSafe index identityValue (.fn domain domain) := by
  induction index with
  | zero => exact fuelValueSafe_zero _ _
  | succ index induction =>
      apply PositiveValueSafe.function induction
      · exact .plainClosure .nil
          (.expression (.core (.core (.var rfl))))
      · intro argument argumentSafe
        change FuelResultSafe index domain
          (evalFuel index [argument] identityBody)
        exact evalFuel_var_resultSafeWith rfl argumentSafe index

def identityBodyGenerated : Generated :=
  ⟨.int, [], []⟩

/-- Exact raw M4 derivation of the inner integer identity body.  The second
source-context entry represents the higher-order value captured when this
lambda is evaluated inside the outer body. -/
theorem identityBodyElaboration (signature : Source.FrozenSignature) :
    Source.M4.ElaboratesFuel signature 1
      [Source.Scheme.mono .int, Source.Scheme.mono higherFunction]
      identityBody ⟨0, 0⟩ identityBodyGenerated ⟨0, 0⟩ := by
  simp [Source.M4.ElaboratesFuel, identityBody, identityBodyGenerated,
    Source.Scheme.mono, Source.Scheme.instantiate, Source.PolyTy.ofTy,
    Source.PolyTy.openBound]

theorem identityBodySemantic :
    identityBodyGenerated.SemanticSolution Subst.id := by
  constructor <;> simp [identityBodyGenerated]

def identityBodyCertificate (signature : Source.FrozenSignature) :
    Source.M4.RawFuelCertificate (identityBodyElaboration signature) :=
  Source.M4.RawFuelCertificate.varWitness
    (identityBodyElaboration signature)

theorem identityBodyCertificate_argumentDemand
    (signature : Source.FrozenSignature) :
    (identityBodyCertificate signature).inputDemand 1 1 0 = 1 :=
  Source.M4.RawFuelCertificate.varWitness_inputDemand_selected
    (identityBodyElaboration signature) 1 1

theorem identityBodyCertificate_capturedDemand
    (signature : Source.FrozenSignature) :
    Source.M4.capturedDemand
      ((identityBodyCertificate signature).inputDemand 1 1) 0 = 0 := by
  exact Source.M4.RawFuelCertificate.varWitness_inputDemand_other
    (identityBodyElaboration signature) 1 1 1 (by omega)

private theorem capturedEnvironmentSafe
    (signature : Source.FrozenSignature) (functionValue : Value) :
    SchemeDemandEnvironmentSafe
      (Source.M4.capturedDemand
        ((identityBodyCertificate signature).inputDemand 1 1))
      Subst.id [functionValue] [Source.Scheme.mono higherFunction] := by
  have headSafe : SchemeFuelValueSafe 0 functionValue
      (Source.Scheme.mono higherFunction) Subst.id := by
    apply SchemeFuelValueSafe.ofMono
    simpa using fuelValueSafe_zero functionValue higherFunction
  have prefixSafe := SchemeDemandEnvironmentSafe.cons
    headSafe
    (SchemeDemandEnvironmentSafe.nil (fun _ => 0) Subst.id)
  apply prefixSafe.congr
  intro position positionLt
  cases position with
  | zero =>
      exact (identityBodyCertificate_capturedDemand signature).symm
  | succ position => simp at positionLt

def capturedIntegerIdentityValue (functionValue : Value) : Value :=
  .plainClosure [functionValue] identityBody

/-- The call part of the captured result is produced from the actual raw M4
body certificate rather than a hand-written evaluator equation. -/
theorem capturedIntegerIdentity_callSafe
    (signature : Source.FrozenSignature) (functionValue : Value) :
    OriginValueSafe integerIdentityDemand
      (capturedIntegerIdentityValue functionValue) integerFunction := by
  have sourceBridge :=
    (identityBodyCertificate signature).plainCallSafe
      identityBodySemantic 1 1
      (capturedEnvironmentSafe signature functionValue)
  rw [identityBodyCertificate_argumentDemand] at sourceBridge
  simpa [integerIdentityDemand, capturedIntegerIdentityValue,
    integerFunction, identityBodyGenerated,
    PlainCallDemand.toOriginDemand, Ty.apply] using
    sourceBridge

private theorem totalPlainFunctionTyping_of_fuelOne
    (safe : FuelValueSafe 1 value (.fn domain codomain)) :
    TotalPlainValueTyping value (.fn domain codomain) := by
  cases safe with
  | function _ typing _ => exact typing

/-- The ordinary fuel leaf of the captured identity uses only the ordinary
fuel leaf already required from the higher-order argument. -/
theorem capturedIntegerIdentity_fuelSafe
    (functionSafe : FuelValueSafe 1 functionValue higherFunction) :
    FuelValueSafe 1 (capturedIntegerIdentityValue functionValue)
      integerFunction := by
  apply PositiveValueSafe.function
    (fuelValueSafe_zero _ _)
  · exact .plainClosure
      (.cons (totalPlainFunctionTyping_of_fuelOne functionSafe) .nil)
      (.expression (.core (.core (.var rfl))))
  · intro argument _argumentSafe
    exact .inl rfl

theorem capturedIntegerIdentity_observableSafe
    (signature : Source.FrozenSignature) (functionValue : Value)
    (functionSafe : FuelValueSafe 1 functionValue higherFunction) :
    OriginValueSafe observableIntegerIdentityDemand
      (capturedIntegerIdentityValue functionValue) integerFunction := by
  apply OriginValueSafe.both
  · exact capturedIntegerIdentity_callSafe signature functionValue
  · exact OriginValueSafe.ofFuel
      (capturedIntegerIdentity_fuelSafe functionSafe)

/-- The same runtime identity closure is used at the higher-order type. -/
theorem higherIdentityValue_originSafe :
    OriginValueSafe higherIdentityDemand identityValue higherFunction := by
  apply OriginValueSafe.both
  · apply OriginValueSafe.plainClosure
    intro argument argumentSafe
    exact .inr ⟨argument, rfl, argumentSafe⟩
  · exact OriginValueSafe.ofFuel
      (identityValue_fuelSafe 1 integerFunction)

def outerBody : Source.Expr :=
  .app (.var 0) (.lam identityBody)

def outerValue : Value :=
  .plainClosure [] outerBody

def outerDemand : OriginDemand :=
  .plainCall 5 higherIdentityDemand observableIntegerIdentityDemand

/-- The outer call consumes a genuinely nested argument demand and returns a
closure carrying both a nested call demand and a fuel leaf. -/
theorem outerValue_originSafe (signature : Source.FrozenSignature) :
    OriginValueSafe outerDemand outerValue
      (.fn higherFunction integerFunction) := by
  apply OriginValueSafe.plainClosure
  intro functionValue functionSafe
  have functionResult : OriginResultSafe
      (.plainCall 3 observableIntegerIdentityDemand
        observableIntegerIdentityDemand)
      higherFunction
      (evalFuel 3 [functionValue] (.var 0)) :=
    .inr ⟨functionValue, rfl, functionSafe.bothLeft⟩
  have argumentResult : OriginResultSafe observableIntegerIdentityDemand
      integerFunction
      (evalFuel 3 [functionValue] (.lam identityBody)) :=
    .inr ⟨capturedIntegerIdentityValue functionValue, rfl,
      capturedIntegerIdentity_observableSafe signature functionValue
        functionSafe.bothRight.toFuel⟩
  have applied := evalFuel_app_origin
    (functionSafe := functionResult) (argumentSafe := argumentResult)
  simpa [outerBody] using applied

/-- Directly expose the function-valued, nested argument/result contract before
specializing it to the concrete closed program. -/
theorem outerValue_applySafe (signature : Source.FrozenSignature)
    (functionSafe : OriginValueSafe higherIdentityDemand
      functionValue higherFunction) :
    OriginResultSafe observableIntegerIdentityDemand integerFunction
      (applyFuel 5 outerValue functionValue) :=
  (outerValue_originSafe signature).apply functionSafe

def higherOrderApplication : Source.Expr :=
  .app (.lam outerBody) (.lam identityBody)

theorem higherOrderApplication_originSafe
    (signature : Source.FrozenSignature) :
    OriginResultSafe observableIntegerIdentityDemand integerFunction
      (evalFuel 6 [] higherOrderApplication) := by
  apply evalFuel_app_origin (argumentDemand := higherIdentityDemand)
  · exact .inr ⟨outerValue, rfl, outerValue_originSafe signature⟩
  · exact .inr ⟨identityValue, rfl, higherIdentityValue_originSafe⟩

/-- The nested result call contract remains available after evaluation. -/
theorem higherOrderApplication_resultCallable
    (signature : Source.FrozenSignature) :
    OriginResultSafe integerIdentityDemand integerFunction
      (evalFuel 6 [] higherOrderApplication) :=
  (higherOrderApplication_originSafe signature).bothLeft

/-- The independent fuel leaf converts the origin-aware proof back to the
existing step-indexed result relation. -/
theorem higherOrderApplication_fuelSafe
    (signature : Source.FrozenSignature) :
    FuelResultSafe 1 integerFunction
      (evalFuel 6 [] higherOrderApplication) :=
  (higherOrderApplication_originSafe signature).bothRight.toFuel

theorem higherOrderApplication_notStuck
    (signature : Source.FrozenSignature) :
    (evalFuel 6 [] higherOrderApplication).NotStuck :=
  (higherOrderApplication_fuelSafe signature).notStuck

/-- Exact execution is checked independently of every safety certificate. -/
theorem higherOrderApplication_exact :
    evalFuel 6 [] higherOrderApplication =
      .ok (capturedIntegerIdentityValue identityValue) := by
  rfl

end TypePM.Source.M4OriginDemandSafetyRegression
