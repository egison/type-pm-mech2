import TypePM.FiniteInputDemandSafety

/-!
# Regression for finite `letE`/application input demand

The closed fixtures use the fragment candidate
`leastLetApplicationInputIndex` at one concrete finite parent demand.  Their
child proofs are structural safety proofs for the source expressions; no
completed evaluation equation is supplied as a safety premise.
-/

namespace TypePM.Runtime.FiniteInputDemandSafetyRegression

/-- Publicly fix the first five values of the least additive fragment
reserve. -/
theorem leastLetApplicationReserve_firstFive :
    [leastLetApplicationReserve 0, leastLetApplicationReserve 1,
      leastLetApplicationReserve 2, leastLetApplicationReserve 3,
      leastLetApplicationReserve 4] = [0, 1, 2, 4, 8] := by
  decide

/-- Publicly fix the counterexample to the previous linear input index. -/
theorem linearInputIndex_rejected :
    ¬ LetComposableInputIndex
      (fun fuel resultIndex => fuel + resultIndex) :=
  linearInputIndex_not_letComposable

def identityScheme : Source.Scheme :=
  ⟨1, 0, .fn (.bound 0) (.bound 0), by
    simp [Source.PolyTy.WellScoped]⟩

def identityExpression : Source.Expr :=
  .lam (.var 0)

def identityValue : Value :=
  Value.plainClosure [] (.var 0)

def identityBody : Source.Expr :=
  .var 0

def identityLet : Source.Expr :=
  .letE identityExpression identityBody

def intFunction : Ty :=
  .fn .int .int

def bodyOccurrenceSupply : Source.Supply :=
  ⟨1, 0⟩

def occurrenceSolution : Subst :=
  Subst.singleTy ⟨1⟩ .int

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
          (evalFuel index [argument] (.var 0))
        exact evalFuel_var_resultSafeWith rfl argumentSafe index

private theorem identityValue_schemeFuelSafe (index : Nat) :
    SchemeFuelValueSafe index identityValue identityScheme
      occurrenceSolution := by
  intro supply
  simpa [identityScheme, Source.Scheme.instantiate,
    Source.PolyTy.openBound, Source.Scheme.boundTyInstance, Ty.apply] using
    identityValue_fuelSafe index
      ((Ty.var ⟨supply.ty⟩).apply occurrenceSolution)

private theorem bodyOccurrenceType :
    ((identityScheme.instantiate bodyOccurrenceSupply).1.apply
      occurrenceSolution) = intFunction := by
  simp [identityScheme, bodyOccurrenceSupply, occurrenceSolution,
    intFunction, Source.Scheme.instantiate, Source.PolyTy.openBound,
    Source.Scheme.boundTyInstance, Subst.singleTy, Ty.apply]

private theorem identityExpression_childSafe
    (fuel resultIndex : Nat) (supply : Source.Supply)
    {_environmentIndex : Nat}
    (_environmentSafe : SchemeFuelEnvironmentSafe _environmentIndex
      occurrenceSolution [] []) :
    FuelResultSafe resultIndex
      ((identityScheme.instantiate supply).1.apply occurrenceSolution)
      (evalFuel fuel [] identityExpression) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨identityValue, rfl,
        identityValue_schemeFuelSafe resultIndex supply⟩

private theorem requestedIndex_le_input (fuel resultIndex : Nat) :
    resultIndex ≤ leastLetApplicationInputIndex fuel resultIndex := by
  simp [leastLetApplicationInputIndex, additiveInputIndex]

private theorem identityBody_childSafe
    (fuel resultIndex : Nat) (value : Value)
    (environmentSafe : SchemeFuelEnvironmentSafe
      (leastLetApplicationInputIndex fuel resultIndex) occurrenceSolution
      [value] [identityScheme]) :
    FuelResultSafe resultIndex intFunction
      (evalFuel fuel [value] identityBody) := by
  have occurrenceSafe := environmentSafe.lookupFuelValueSafe
    0 rfl rfl bodyOccurrenceSupply
  have inputSafe : FuelValueSafe
      (leastLetApplicationInputIndex fuel resultIndex) value intFunction :=
    bodyOccurrenceType ▸ occurrenceSafe
  have resultSafe : FuelValueSafe resultIndex value intFunction :=
    inputSafe.mono (requestedIndex_le_input fuel resultIndex)
  simpa [identityBody, FuelResultSafe, FuelResultSafeWith] using
    (evalFuel_var_resultSafeWith rfl resultSafe fuel)

/-- The empty closed environment is supplied only at the concrete finite
parent demand used by this `letE` derivation. -/
private theorem identityLet_outerFinite
    (fuel resultIndex : Nat) :
    SchemeFuelEnvironmentSafe
      (leastLetApplicationInputIndex (fuel + 1) resultIndex)
      occurrenceSolution [] [] :=
  .nil

/-- A closed generalized identity `let` uses the finite-index composition
rule with the least `letE`/application candidate. -/
theorem identityLet_finiteSafe (fuel resultIndex : Nat) :
    FuelResultSafe resultIndex intFunction
      (evalFuel (fuel + 1) [] identityLet) := by
  simpa [identityLet] using
    (evalFuel_letE_schemeFiniteIndex
      (input := leastLetApplicationInputIndex)
      (laws := leastLetApplicationInputIndex_letComposable)
      (solution := occurrenceSolution)
      (environment := []) (sourceContext := [])
      (scheme := identityScheme)
      (valueExpression := identityExpression)
      (bodyExpression := identityBody)
      (bodyTarget := intFunction)
      (resultIndex := resultIndex)
      (outerSafe := identityLet_outerFinite fuel resultIndex)
      (valueIH := fun supply environmentSafe =>
        identityExpression_childSafe fuel
          (leastLetApplicationInputIndex fuel resultIndex)
          supply environmentSafe)
      (bodyIH := identityBody_childSafe fuel resultIndex))

/-- The finite `letE` regression reaches a successful value, so its safety
proof is not exercised only through the `timeout` alternative. -/
theorem identityLet_exact :
    evalFuel 2 [] identityLet = .ok identityValue := by
  rfl

/-- Fix one positive residual-index use of the finite parent-demand rule. -/
theorem identityLet_positiveResidualSafe :
    FuelResultSafe 3 intFunction (evalFuel 2 [] identityLet) :=
  identityLet_finiteSafe 1 3

theorem identityLet_neverStuck (fuel : Nat) :
    (evalFuel fuel [] identityLet).NotStuck := by
  cases fuel with
  | zero => trivial
  | succ fuel => exact (identityLet_finiteSafe fuel 0).notStuck

/-! ## Application fixture -/

def identityLiteralApplication : Source.Expr :=
  .app identityExpression (.lit 7)

private theorem intValue_fuelSafe (index : Nat) (literal : Int) :
    FuelValueSafe index (.int literal) .int := by
  induction index with
  | zero => exact fuelValueSafe_zero _ _
  | succ index induction => exact .int literal induction

private theorem identityFunction_childSafe
    (fuel resultIndex : Nat) {_environmentIndex : Nat}
    (environmentSafe : SchemeFuelEnvironmentSafe _environmentIndex
      occurrenceSolution [] []) :
    FuelResultSafe resultIndex intFunction
      (evalFuel fuel [] identityExpression) := by
  have safe := identityExpression_childSafe fuel resultIndex
    bodyOccurrenceSupply environmentSafe
  exact bodyOccurrenceType ▸ safe

private theorem literal_childSafe
    (fuel resultIndex : Nat) {_environmentIndex : Nat}
    (_environmentSafe : SchemeFuelEnvironmentSafe _environmentIndex
      occurrenceSolution [] []) :
    FuelResultSafe resultIndex .int (evalFuel fuel [] (.lit 7)) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨.int 7, rfl, intValue_fuelSafe resultIndex 7⟩

/-- Expression-level application composition is exercised with an identity
closure and integer literal for arbitrary operational fuel and requested
residual index. -/
theorem identityLiteralApplication_finiteSafe
    (fuel resultIndex : Nat) :
    FuelResultSafe resultIndex .int
      (evalFuel (fuel + 1) [] identityLiteralApplication) := by
  simpa [identityLiteralApplication, intFunction] using
    (evalFuel_app_schemeFiniteIndex
      (input := leastLetApplicationInputIndex)
      (laws := leastLetApplicationInputIndex_applicationComposable)
      (solution := occurrenceSolution)
      (environment := []) (sourceContext := [])
      (functionExpression := identityExpression)
      (argumentExpression := .lit 7)
      (domain := .int) (codomain := .int)
      (resultIndex := resultIndex)
      (outerSafe := (SchemeFuelEnvironmentSafe.nil :
        SchemeFuelEnvironmentSafe
          (leastLetApplicationInputIndex (fuel + 1) resultIndex)
          occurrenceSolution [] []))
      (functionIH := fun environmentSafe =>
        identityFunction_childSafe fuel
          (max fuel (resultIndex + 1)) environmentSafe)
      (argumentIH := fun environmentSafe =>
        literal_childSafe fuel
          (max fuel (resultIndex + 1) - 1) environmentSafe))

/-- The application regression reaches the integer result at its first
sufficient evaluator fuel. -/
theorem identityLiteralApplication_exact :
    evalFuel 3 [] identityLiteralApplication = .ok (.int 7) := by
  rfl

/-- Fix one positive residual-index use of expression-level application
composition. -/
theorem identityLiteralApplication_positiveResidualSafe :
    FuelResultSafe 4 .int
      (evalFuel 3 [] identityLiteralApplication) :=
  identityLiteralApplication_finiteSafe 2 4

theorem identityLiteralApplication_neverStuck (fuel : Nat) :
    (evalFuel fuel [] identityLiteralApplication).NotStuck := by
  cases fuel with
  | zero => trivial
  | succ fuel =>
      exact (identityLiteralApplication_finiteSafe fuel 0).notStuck

end TypePM.Runtime.FiniteInputDemandSafetyRegression
