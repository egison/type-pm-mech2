import TypePM.SchemeIndexedFuelSafety

/-!
# Regression for source-scheme-indexed fuel safety

The closed fixture evaluates a generalized identity `let`.  One fixed
substitution selects `Int → Int` and a matcher-function type at two distinct
source occurrence supplies while leaving every other variable alone.
The same identity closure satisfies the complete scheme family, so the
closed-first `letE` rule reaches no `stuck` result at any evaluator fuel.
-/

namespace TypePM.Runtime.SchemeIndexedFuelSafetyRegression

def identityScheme : Source.Scheme :=
  ⟨1, 0, .fn (.bound 0) (.bound 0), by
    simp [Source.PolyTy.WellScoped]⟩

def identityExpression : Source.Expr :=
  .lam (.var 0)

def identityValue : Value :=
  Value.plainClosure [] (.var 0)

def identityBody : Source.Expr :=
  .tuple [.var 0, .var 0]

def identityLet : Source.Expr :=
  .letE identityExpression identityBody

def matcherArgument : Ty :=
  .matcher .any .int

def intFunction : Ty :=
  .fn .int .int

def matcherFunction : Ty :=
  .fn matcherArgument matcherArgument

def twoOccurrenceResult : Ty :=
  .prod [intFunction, matcherFunction]

def firstOccurrenceSupply : Source.Supply :=
  ⟨1, 0⟩

def secondOccurrenceSupply : Source.Supply :=
  ⟨2, 0⟩

def occurrenceSolution : Subst :=
  Subst.compose
    (Subst.singleTy ⟨2⟩ matcherArgument)
    (Subst.singleTy ⟨1⟩ .int)

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

theorem identityValue_allFuelSchemeSafe :
    AllFuelSchemeValueSafe identityValue identityScheme
      occurrenceSolution := by
  intro index supply
  simpa [identityScheme, Source.Scheme.instantiate,
    Source.PolyTy.openBound, Source.Scheme.boundTyInstance, Ty.apply] using
    identityValue_fuelSafe index
      ((Ty.var ⟨supply.ty⟩).apply occurrenceSolution)

private theorem firstOccurrenceType :
    ((identityScheme.instantiate firstOccurrenceSupply).1.apply
      occurrenceSolution) = intFunction := by
  simp [identityScheme, firstOccurrenceSupply, occurrenceSolution,
    intFunction, matcherArgument, Source.Scheme.instantiate,
    Source.PolyTy.openBound, Source.Scheme.boundTyInstance, Subst.compose,
    Subst.singleTy, Ty.apply]

private theorem secondOccurrenceType :
    ((identityScheme.instantiate secondOccurrenceSupply).1.apply
      occurrenceSolution) = matcherFunction := by
  simp [identityScheme, secondOccurrenceSupply, occurrenceSolution,
    matcherFunction, matcherArgument, Source.Scheme.instantiate,
    Source.PolyTy.openBound, Source.Scheme.boundTyInstance, Subst.compose,
    Subst.singleTy, Ty.apply]

/-- The same scheme-indexed entry is safe at two distinct occurrence types
under one fixed enclosing substitution. -/
theorem identityValue_twoOccurrences (index : Nat) :
    FuelValueSafe index identityValue intFunction ∧
      FuelValueSafe index identityValue matcherFunction := by
  have first := identityValue_allFuelSchemeSafe.atIndexSupply index
    firstOccurrenceSupply
  have second := identityValue_allFuelSchemeSafe.atIndexSupply index
    secondOccurrenceSupply
  exact ⟨firstOccurrenceType ▸ first, secondOccurrenceType ▸ second⟩

theorem emptyEnvironment_allFuelSafe :
    AllFuelSchemeEnvironmentSafe occurrenceSolution [] [] :=
  AllFuelSchemeEnvironmentSafe.nil occurrenceSolution

private theorem identityEnvironmentSafe (index : Nat) :
    SchemeFuelEnvironmentSafe index occurrenceSolution [identityValue]
      [identityScheme] :=
  .cons (identityValue_allFuelSchemeSafe index) .nil

private theorem identityVariableElaboration
    (signature : Source.FrozenSignature) (supply : Source.Supply) :
    Source.M4.ElaboratesFuel signature 1 [identityScheme] (.var 0) supply
      ⟨(identityScheme.instantiate supply).1, [], []⟩
      (identityScheme.instantiate supply).2 := by
  simp [Source.M4.ElaboratesFuel]

/-- Two raw positive-fuel M4 variable derivations use the source scheme
family directly, with no protected runtime context or `IsInstance` premise. -/
theorem identityRawVariable_twoOccurrences
    (signature : Source.FrozenSignature) (operationalFuel index : Nat) :
    FuelResultSafe index intFunction
        (evalFuel operationalFuel [identityValue] (.var 0)) ∧
      FuelResultSafe index matcherFunction
        (evalFuel operationalFuel [identityValue] (.var 0)) := by
  have first := Source.M4.ElaboratesFuel.var_schemeFuelSafe
    (identityVariableElaboration signature firstOccurrenceSupply)
    (identityEnvironmentSafe index)
    (operationalFuel := operationalFuel)
  have second := Source.M4.ElaboratesFuel.var_schemeFuelSafe
    (identityVariableElaboration signature secondOccurrenceSupply)
    (identityEnvironmentSafe index)
    (operationalFuel := operationalFuel)
  exact ⟨firstOccurrenceType ▸ first, secondOccurrenceType ▸ second⟩

private theorem identityExpression_childSafe
    (fuel index : Nat) (supply : Source.Supply)
    (_environmentSafe : SchemeFuelEnvironmentSafe index occurrenceSolution
      [] []) :
    FuelResultSafe index
      ((identityScheme.instantiate supply).1.apply occurrenceSolution)
      (evalFuel fuel [] identityExpression) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨identityValue, rfl,
        identityValue_allFuelSchemeSafe.atIndexSupply index supply⟩

private theorem identityBody_childSafe
    (fuel resultIndex : Nat) (value : Value)
    (environmentSafe : AllFuelSchemeEnvironmentSafe occurrenceSolution
      [value] [identityScheme]) :
    FuelResultSafe resultIndex twoOccurrenceResult
      (evalFuel fuel [value] identityBody) := by
  have firstSafe : FuelValueSafe resultIndex value intFunction := by
    have occurrenceSafe := (environmentSafe resultIndex).lookupFuelValueSafe
      0 rfl rfl firstOccurrenceSupply
    exact firstOccurrenceType ▸ occurrenceSafe
  have secondSafe : FuelValueSafe resultIndex value matcherFunction := by
    have occurrenceSafe := (environmentSafe resultIndex).lookupFuelValueSafe
      0 rfl rfl secondOccurrenceSupply
    exact secondOccurrenceType ▸ occurrenceSafe
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          exact .inr ⟨.tuple [value, value], by rfl,
            by
              simpa [twoOccurrenceResult] using
                fuelValueSafe_tuple_of_environment resultIndex
                  [value, value] [intFunction, matcherFunction]
                  (.cons firstSafe
                    (.cons secondSafe
                      (FuelEnvironmentSafe.nil resultIndex)))⟩

/-- Closed-first `letE` composition invokes the RHS child proof at every
logical index and occurrence supply, then certifies the body from the extended
source-aligned environment. -/
theorem identityLet_safe (fuel resultIndex : Nat) :
    FuelResultSafe resultIndex twoOccurrenceResult
      (evalFuel (fuel + 1) [] identityLet) := by
  simpa [identityLet] using
    (evalFuel_letE_allFuelScheme_childSafe
      (solution := occurrenceSolution)
      (environment := []) (sourceContext := [])
      (scheme := identityScheme)
      (valueExpression := identityExpression)
      (bodyExpression := identityBody)
      (bodyTarget := twoOccurrenceResult)
      (resultIndex := resultIndex)
      (outerSafe := emptyEnvironment_allFuelSafe)
      (valueChildSafe := identityExpression_childSafe fuel)
      (bodyChildSafe := identityBody_childSafe fuel resultIndex))

/-- The closed polymorphic identity `let` cannot return `stuck` at any
evaluator fuel. -/
theorem identityLet_neverStuck (fuel : Nat) :
    (evalFuel fuel [] identityLet).NotStuck := by
  cases fuel with
  | zero => trivial
  | succ fuel => exact (identityLet_safe fuel 0).notStuck

end TypePM.Runtime.SchemeIndexedFuelSafetyRegression
