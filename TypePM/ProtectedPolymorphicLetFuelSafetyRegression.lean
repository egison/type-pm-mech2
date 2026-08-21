import TypePM.ProtectedPolymorphicLetFuelSafety

/-!
# Protected polymorphic `let` fuel-safety regression

The polymorphic identity closure supplies the all-instance, all-logical-index
right-hand-side postcondition consumed by the generic protected-`letE` rule.
Its body uses the one runtime entry at two distinct monotypes.
-/

namespace TypePM.Runtime.ProtectedPolymorphicIdentityRegression

def identityExpression : Source.Expr :=
  .lam (.var 0)

def identityValue : Value :=
  Value.plainClosure [] (.var 0)

def identityGeneral : Ty :=
  .fn (.var ⟨0⟩) (.var ⟨0⟩)

def intFunction : Ty :=
  .fn .int .int

def matcherArgument : Ty :=
  .matcher .any .int

def matcherFunction : Ty :=
  .fn matcherArgument matcherArgument

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

theorem identityValue_protected (index : Nat) :
    ProtectedFuelValueSafe index identityValue identityGeneral := by
  intro target instantiation
  obtain ⟨substitution, targetEq⟩ := instantiation
  rw [← targetEq]
  simpa [identityGeneral, Ty.apply] using
    identityValue_fuelSafe index (substitution.ty ⟨0⟩)

theorem identityValue_allFuelProtected :
    AllFuelProtectedValueSafe identityValue identityGeneral :=
  identityValue_protected

theorem intFunction_instance : IsInstance identityGeneral intFunction := by
  refine ⟨Subst.singleTy ⟨0⟩ .int, ?_⟩
  simp [identityGeneral, intFunction, Subst.singleTy, Ty.apply]

theorem matcherFunction_instance :
    IsInstance identityGeneral matcherFunction := by
  refine ⟨Subst.singleTy ⟨0⟩ matcherArgument, ?_⟩
  simp [identityGeneral, matcherFunction, matcherArgument, Subst.singleTy,
    Ty.apply]

theorem identityValue_twoAllFuelInstances :
    AllFuelValueSafe identityValue intFunction ∧
      AllFuelValueSafe identityValue matcherFunction :=
  ⟨identityValue_allFuelProtected.atInstance intFunction_instance,
    identityValue_allFuelProtected.atInstance matcherFunction_instance⟩

theorem identityEnvironment :
    ProtectedFuelEnvironmentSafe index [identityValue] [identityGeneral]
      [true] :=
  .consProtected (identityValue_protected index) .nil

/-- The same protected runtime entry projects at two distinct monotypes. -/
theorem identityEntry_twoInstances (index : Nat) :
    FuelValueSafe index identityValue intFunction ∧
      FuelValueSafe index identityValue matcherFunction := by
  have entry : ProtectedFuelEntrySafe index identityValue identityGeneral true :=
    (identityEnvironment (index := index)).lookupEntry 0 rfl rfl rfl
  exact ⟨entry.atInstance intFunction_instance,
    entry.atInstance matcherFunction_instance⟩

def twoInstanceBody : Source.Expr :=
  .tuple [.var 0, .var 0]

def twoInstanceResult : Ty :=
  .prod [intFunction, matcherFunction]

def identityLet : Source.Expr :=
  .letE identityExpression twoInstanceBody

private theorem identityExpression_allFuelProtectedSafe
    (operationalFuel : Nat) :
    FuelResultSafeWith
      (fun value => AllFuelProtectedValueSafe value identityGeneral)
      (evalFuel operationalFuel [] identityExpression) := by
  cases operationalFuel with
  | zero => exact .inl rfl
  | succ operationalFuel =>
      exact .inr ⟨identityValue, rfl, identityValue_allFuelProtected⟩

private theorem twoInstanceBody_safe
    (operationalFuel resultIndex : Nat) (value : Value)
    (valueSafe : ProtectedFuelValueSafe resultIndex value identityGeneral) :
    FuelResultSafe resultIndex twoInstanceResult
      (evalFuel operationalFuel [value] twoInstanceBody) := by
  have intSafe : FuelValueSafe resultIndex value intFunction :=
    valueSafe intFunction intFunction_instance
  have matcherSafe : FuelValueSafe resultIndex value matcherFunction :=
    valueSafe matcherFunction matcherFunction_instance
  cases operationalFuel with
  | zero => exact .inl rfl
  | succ operationalFuel =>
      cases operationalFuel with
      | zero => exact .inl rfl
      | succ operationalFuel =>
          exact .inr ⟨.tuple [value, value], by rfl,
            by
              simpa [twoInstanceResult] using
                fuelValueSafe_tuple_of_environment resultIndex
                  [value, value] [intFunction, matcherFunction]
                  (.cons intSafe
                    (.cons matcherSafe (FuelEnvironmentSafe.nil resultIndex)))⟩

/-- The all-index protected-`letE` rule specializes the right-hand side only
after the body chooses its logical result index, then supports two distinct
instances of the protected entry. -/
theorem identityLet_twoInstances_safe
    (operationalFuel resultIndex : Nat) :
    FuelResultSafe resultIndex twoInstanceResult
      (evalFuel (operationalFuel + 1) [] identityLet) := by
  apply evalFuel_letE_allFuelProtectedFuelSafe
    (bindingIndex := resultIndex)
    (runtimeContext := []) (provenance := [])
    (general := identityGeneral)
    (environmentSafe := ProtectedFuelEnvironmentSafe.nil)
    (valueSafe := identityExpression_allFuelProtectedSafe operationalFuel)
  intro value environmentSafe
  have entry : ProtectedFuelEntrySafe resultIndex value identityGeneral true :=
    environmentSafe.lookupEntry 0 rfl rfl rfl
  exact twoInstanceBody_safe operationalFuel resultIndex value
    (fun target instantiation => entry.atInstance instantiation)

/-- The polymorphic `let` fixture cannot produce the evaluator's `stuck`
result at any operational fuel. -/
theorem identityLet_neverStuck (fuel : Nat) :
    (evalFuel fuel [] identityLet).NotStuck := by
  cases fuel with
  | zero => trivial
  | succ operationalFuel =>
      exact (identityLet_twoInstances_safe operationalFuel 0).notStuck

end TypePM.Runtime.ProtectedPolymorphicIdentityRegression
