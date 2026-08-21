import TypePM.Source.M4ProtectedFuelContextBridge

/-!
# Regression for the protected fuel-indexed variable bridge

The ordinary fixture stores an integer at its exact monotype.  The protected
fixture stores one identity closure at a generalized function type, then uses
two source instantiation supplies under one shared later substitution to
recover the same runtime value at `Int → Int` and at a matcher function type.

These are the two branches of `ProtectedContextCompatible.lookup`; neither
regression assumes a completed evaluation equation.
-/

namespace TypePM.Source.M4ProtectedFuelContextBridgeRegression

open TypePM.Runtime

def ordinaryScheme : Scheme :=
  .mono .int

def ordinaryValue : Value :=
  .int 7

private theorem ordinaryContextCompatible :
    ProtectedContextCompatible [ordinaryScheme] [.int] [false] Subst.id := by
  simpa [ordinaryScheme, Ty.apply_id] using
    (ProtectedContextCompatible.mono
      (sourceTarget := Ty.int)
      (solution := Subst.id)
      ProtectedContextCompatible.nil)

private theorem ordinaryEnvironmentSafe (index : Nat) :
    ProtectedFuelEnvironmentSafe index [ordinaryValue] [.int] [false] :=
  .consOrdinary (fuelValueSafe_int 7 index) .nil

private theorem ordinaryVariableElaboration (signature : FrozenSignature) :
    M4.ElaboratesFuel signature 1 [ordinaryScheme] (.var 0)
      (⟨0, 0⟩ : Supply) ⟨.int, [], []⟩ (⟨0, 0⟩ : Supply) := by
  simp [M4.ElaboratesFuel, ordinaryScheme, Scheme.instantiate_mono]

/-- The ordinary branch recovers the exact monotype stored in the runtime
context. -/
theorem ordinary_lookupFuelValueSafe (index : Nat) :
    FuelValueSafe index ordinaryValue .int := by
  have safe := ordinaryContextCompatible.lookupFuelValueSafeOfValue
    (ordinaryEnvironmentSafe index) (position := 0)
    (supply := (⟨0, 0⟩ : Supply)) rfl rfl
  simpa [ordinaryScheme, Scheme.instantiate_mono, Ty.apply_id] using safe

/-- Variable evaluation preserves the ordinary entry's exact type for an
arbitrary evaluator fuel and an independent logical index. -/
theorem ordinary_evalFuel_var_safe (operationalFuel index : Nat) :
    FuelResultSafe index .int
      (evalFuel operationalFuel [ordinaryValue] (.var 0)) := by
  simpa [ordinaryScheme, Scheme.instantiate_mono, Ty.apply_id] using
    (evalFuel_var_protectedFuelSafe ordinaryContextCompatible
      (ordinaryEnvironmentSafe index) (position := 0)
      (supply := (⟨0, 0⟩ : Supply)) rfl operationalFuel)

/-- The raw positive-fuel M4 variable rule itself supplies the source lookup
needed by the ordinary dynamic endpoint. -/
theorem ordinary_elaboratesFuel_var_safe
    (signature : FrozenSignature) (operationalFuel index : Nat) :
    FuelResultSafe index .int
      (evalFuel operationalFuel [ordinaryValue] (.var 0)) := by
  simpa using
    (M4.ElaboratesFuel.var_protectedFuelSafe
      (ordinaryVariableElaboration signature)
      ordinaryContextCompatible (ordinaryEnvironmentSafe index)
      (operationalFuel := operationalFuel))

def identityScheme : Scheme :=
  ⟨1, 0, .fn (.bound 0) (.bound 0), by
    simp [PolyTy.WellScoped]⟩

def identityGeneral : Ty :=
  .fn (.var ⟨0⟩) (.var ⟨0⟩)

def identityValue : Value :=
  Value.plainClosure [] (.var 0)

def matcherArgument : Ty :=
  .matcher .any .int

def intFunction : Ty :=
  .fn .int .int

def matcherFunction : Ty :=
  .fn matcherArgument matcherArgument

def firstOccurrenceSupply : Supply :=
  ⟨1, 0⟩

def secondOccurrenceSupply : Supply :=
  ⟨2, 0⟩

/-- One shared substitution chooses independent monotypes for the two source
occurrence supplies.  The canonical runtime entry at variable zero remains
general. -/
def twoOccurrenceSolution : Subst :=
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

private theorem identityValue_protected (index : Nat) :
    ProtectedFuelValueSafe index identityValue identityGeneral := by
  intro target instantiation
  obtain ⟨substitution, targetEq⟩ := instantiation
  rw [← targetEq]
  simpa [identityGeneral, Ty.apply] using
    identityValue_fuelSafe index (substitution.ty ⟨0⟩)

private theorem identityContextCompatible :
    ProtectedContextCompatible [identityScheme] [identityGeneral] [true]
      twoOccurrenceSolution := by
  have compatible := ProtectedContextCompatible.pushCanonical
    (scheme := identityScheme)
    (canonicalSupply := (⟨0, 0⟩ : Supply))
    (solution := twoOccurrenceSolution)
    (sourceContext := []) (runtimeContext := []) (provenance := [])
    (by
      intro index membership
      simp [identityScheme, Scheme.freeTyVars, PolyTy.freeTyVars,
        dedupFirst, dedup] at membership)
    (by
      intro index membership
      simp [identityScheme, Scheme.freeCapVars, PolyTy.freeCapVars,
        dedupFirst, dedup] at membership)
    ProtectedContextCompatible.nil
  simpa [identityScheme, identityGeneral, Scheme.instantiate,
    Scheme.boundTyInstance, PolyTy.openBound] using compatible

private theorem identityEnvironmentSafe (index : Nat) :
    ProtectedFuelEnvironmentSafe index [identityValue] [identityGeneral]
      [true] :=
  .consProtected (identityValue_protected index) .nil

private theorem firstOccurrenceType :
    ((identityScheme.instantiate firstOccurrenceSupply).1.apply
      twoOccurrenceSolution) = intFunction := by
  simp [identityScheme, firstOccurrenceSupply, twoOccurrenceSolution,
    intFunction, matcherArgument, Scheme.instantiate, PolyTy.openBound,
    Scheme.boundTyInstance, Subst.compose, Subst.singleTy, Ty.apply]

private theorem secondOccurrenceType :
    ((identityScheme.instantiate secondOccurrenceSupply).1.apply
      twoOccurrenceSolution) = matcherFunction := by
  simp [identityScheme, secondOccurrenceSupply, twoOccurrenceSolution,
    matcherFunction, matcherArgument, Scheme.instantiate, PolyTy.openBound,
    Scheme.boundTyInstance, Subst.compose, Subst.singleTy, Ty.apply]

private theorem firstVariableElaboration (signature : FrozenSignature) :
    M4.ElaboratesFuel signature 1 [identityScheme] (.var 0)
      firstOccurrenceSupply
      ⟨(identityScheme.instantiate firstOccurrenceSupply).1, [], []⟩
      (identityScheme.instantiate firstOccurrenceSupply).2 := by
  simp [M4.ElaboratesFuel]

private theorem secondVariableElaboration (signature : FrozenSignature) :
    M4.ElaboratesFuel signature 1 [identityScheme] (.var 0)
      secondOccurrenceSupply
      ⟨(identityScheme.instantiate secondOccurrenceSupply).1, [], []⟩
      (identityScheme.instantiate secondOccurrenceSupply).2 := by
  simp [M4.ElaboratesFuel]

/-- The protected branch projects one runtime identity closure at two distinct
source occurrence types selected by one shared later substitution. -/
theorem protected_lookup_twoInstances (index : Nat) :
    FuelValueSafe index identityValue intFunction ∧
      FuelValueSafe index identityValue matcherFunction := by
  have first := identityContextCompatible.lookupFuelValueSafeOfValue
    (identityEnvironmentSafe index) (position := 0)
    (supply := firstOccurrenceSupply) rfl rfl
  have second := identityContextCompatible.lookupFuelValueSafeOfValue
    (identityEnvironmentSafe index) (position := 0)
    (supply := secondOccurrenceSupply) rfl rfl
  exact ⟨firstOccurrenceType ▸ first, secondOccurrenceType ▸ second⟩

/-- The same runtime variable evaluation is safe at both independently chosen
source instances.  Operational fuel remains independent of the logical
index. -/
theorem protected_evalFuel_var_twoInstances
    (operationalFuel index : Nat) :
    FuelResultSafe index intFunction
        (evalFuel operationalFuel [identityValue] (.var 0)) ∧
      FuelResultSafe index matcherFunction
        (evalFuel operationalFuel [identityValue] (.var 0)) := by
  have first := evalFuel_var_protectedFuelSafe identityContextCompatible
    (identityEnvironmentSafe index) (position := 0)
    (supply := firstOccurrenceSupply) rfl operationalFuel
  have second := evalFuel_var_protectedFuelSafe identityContextCompatible
    (identityEnvironmentSafe index) (position := 0)
    (supply := secondOccurrenceSupply) rfl operationalFuel
  exact ⟨firstOccurrenceType ▸ first, secondOccurrenceType ▸ second⟩

/-- Two actual raw M4 variable derivations, with distinct instantiation
supplies, reach the dynamic endpoint for the same protected runtime value. -/
theorem protected_elaboratesFuel_var_twoInstances
    (signature : FrozenSignature) (operationalFuel index : Nat) :
    FuelResultSafe index intFunction
        (evalFuel operationalFuel [identityValue] (.var 0)) ∧
      FuelResultSafe index matcherFunction
        (evalFuel operationalFuel [identityValue] (.var 0)) := by
  have first := M4.ElaboratesFuel.var_protectedFuelSafe
    (firstVariableElaboration signature)
    identityContextCompatible (identityEnvironmentSafe index)
    (operationalFuel := operationalFuel)
  have second := M4.ElaboratesFuel.var_protectedFuelSafe
    (secondVariableElaboration signature)
    identityContextCompatible (identityEnvironmentSafe index)
    (operationalFuel := operationalFuel)
  exact ⟨firstOccurrenceType ▸ first, secondOccurrenceType ▸ second⟩

end TypePM.Source.M4ProtectedFuelContextBridgeRegression
