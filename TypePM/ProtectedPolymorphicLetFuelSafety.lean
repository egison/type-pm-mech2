import TypePM.ValueIndexedStableFirstOrderSafety

/-!
# Fuel-indexed environments for protected polymorphic `let`

A generalized source `let` is represented by one monotype in the executable
runtime environment.  Its proof-only provenance bit records that the same
runtime value may be used at every substitution instance of that monotype.
This module gives that distinction a step-indexed dynamic meaning.

The logical index below is independent of evaluator fuel.  Certificates contain
neither completed evaluation equations nor completed search results.

The source-to-runtime producer that establishes the all-index right-hand-side
postcondition is deliberately outside this module: this module assumes that
postcondition rather than deriving it from source typing.  The rules below
consume it and extend the runtime environment at any chosen logical index.
-/

namespace TypePM.Runtime

/-- A protected runtime value is safe at every instance of its general type at
one caller-selected logical index. -/
def ProtectedFuelValueSafe (index : Nat) (value : Value) (general : Ty) : Prop :=
  ∀ target, IsInstance general target → FuelValueSafe index value target

namespace ProtectedFuelValueSafe

/-- Forget protection by selecting the identity substitution. -/
theorem atGeneral
    (safe : ProtectedFuelValueSafe index value general) :
    FuelValueSafe index value general :=
  safe general ⟨Subst.id, Ty.apply_id general⟩

end ProtectedFuelValueSafe

/-- A protected runtime value is safe at every instance and every logical
index.  This is the postcondition needed before a source-wide proof chooses the
logical index at which it continues through a polymorphic `let` body. -/
def AllFuelProtectedValueSafe (value : Value) (general : Ty) : Prop :=
  ∀ index, ProtectedFuelValueSafe index value general

namespace AllFuelProtectedValueSafe

theorem atIndex
    (safe : AllFuelProtectedValueSafe value general) (index : Nat) :
    ProtectedFuelValueSafe index value general :=
  safe index

theorem atInstance
    (safe : AllFuelProtectedValueSafe value general)
    (instantiation : IsInstance general target) :
    AllFuelValueSafe value target :=
  fun index => safe index target instantiation

end AllFuelProtectedValueSafe

/-- One pointwise runtime entry.  Ordinary entries retain their exact type;
protected entries retain the all-instance property above. -/
inductive ProtectedFuelEntrySafe (index : Nat) : Value → Ty → Bool → Prop where
  | ordinary (safe : FuelValueSafe index value target) :
      ProtectedFuelEntrySafe index value target false
  | allInstances (safe : ProtectedFuelValueSafe index value general) :
      ProtectedFuelEntrySafe index value general true

namespace ProtectedFuelEntrySafe

/-- Forget logical layers without changing the runtime value, type, or
provenance classification. -/
theorem mono
    (safe : ProtectedFuelEntrySafe larger value target isProtected)
    (smaller_le : smaller ≤ larger) :
    ProtectedFuelEntrySafe smaller value target isProtected := by
  cases safe with
  | ordinary valueSafe => exact .ordinary (valueSafe.mono smaller_le)
  | allInstances instances =>
      exact .allInstances (fun instanceTarget instantiation =>
        (instances instanceTarget instantiation).mono smaller_le)

theorem previous
    (safe : ProtectedFuelEntrySafe (index + 1) value target isProtected) :
    ProtectedFuelEntrySafe index value target isProtected :=
  safe.mono (Nat.le_succ index)

/-- Project the exact ordinary-entry certificate. -/
theorem ordinaryValue
    (safe : ProtectedFuelEntrySafe index value target false) :
    FuelValueSafe index value target := by
  cases safe with
  | ordinary valueSafe => exact valueSafe

/-- Instantiate a protected entry at one requested monotype. -/
theorem atInstance
    (safe : ProtectedFuelEntrySafe index value general true)
    (instantiation : IsInstance general target) :
    FuelValueSafe index value target := by
  cases safe with
  | allInstances instances => exact instances target instantiation

end ProtectedFuelEntrySafe

/-- Newest-first pointwise environment safety with a parallel provenance
mask.  The constructors enforce all three list lengths by construction. -/
inductive ProtectedFuelEnvironmentSafe (index : Nat) :
    List Value → List Ty → List Bool → Prop where
  | nil : ProtectedFuelEnvironmentSafe index [] [] []
  | consOrdinary
      (head : FuelValueSafe index value target)
      (tail : ProtectedFuelEnvironmentSafe index values targets provenance) :
      ProtectedFuelEnvironmentSafe index (value :: values) (target :: targets)
        (false :: provenance)
  | consProtected
      (head : ProtectedFuelValueSafe index value general)
      (tail : ProtectedFuelEnvironmentSafe index values targets provenance) :
      ProtectedFuelEnvironmentSafe index (value :: values) (general :: targets)
        (true :: provenance)

namespace ProtectedFuelEnvironmentSafe

theorem valueTypeLength
    (safe : ProtectedFuelEnvironmentSafe index values targets provenance) :
    values.length = targets.length := by
  induction safe with
  | nil => rfl
  | consOrdinary _ _ induction | consProtected _ _ induction =>
      simp [induction]

theorem typeProvenanceLength
    (safe : ProtectedFuelEnvironmentSafe index values targets provenance) :
    targets.length = provenance.length := by
  induction safe with
  | nil => rfl
  | consOrdinary _ _ induction | consProtected _ _ induction =>
      simp [induction]

/-- Pointwise lookup returns the runtime value and its provenance-sensitive
entry certificate. -/
theorem lookup
    (safe : ProtectedFuelEnvironmentSafe index values targets provenance)
    (position : Nat)
    (targetFound : targets[position]? = some target)
    (provenanceFound : provenance[position]? = some isProtected) :
    ∃ value,
      values[position]? = some value ∧
        ProtectedFuelEntrySafe index value target isProtected := by
  induction position generalizing values targets provenance target isProtected with
  | zero =>
      cases safe with
      | nil => simp at targetFound
      | consOrdinary head tail =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at targetFound provenanceFound ⊢
          subst target
          subst isProtected
          exact ⟨_, rfl, .ordinary head⟩
      | consProtected head tail =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at targetFound provenanceFound ⊢
          subst target
          subst isProtected
          exact ⟨_, rfl, .allInstances head⟩
  | succ position induction =>
      cases safe with
      | nil => simp at targetFound
      | consOrdinary head tail | consProtected head tail =>
          simp only [List.getElem?_cons_succ] at targetFound provenanceFound ⊢
          exact induction tail targetFound provenanceFound

/-- Lookup when the runtime value is already known. -/
theorem lookupEntry
    (safe : ProtectedFuelEnvironmentSafe index values targets provenance)
    (position : Nat)
    (valueFound : values[position]? = some value)
    (targetFound : targets[position]? = some target)
    (provenanceFound : provenance[position]? = some isProtected) :
    ProtectedFuelEntrySafe index value target isProtected := by
  obtain ⟨foundValue, found, entry⟩ :=
    safe.lookup position targetFound provenanceFound
  rw [valueFound] at found
  cases found
  exact entry

/-- The relation is downward closed in its logical index. -/
theorem mono
    (safe : ProtectedFuelEnvironmentSafe larger values targets provenance)
    (smaller_le : smaller ≤ larger) :
    ProtectedFuelEnvironmentSafe smaller values targets provenance := by
  induction safe with
  | nil => exact .nil
  | consOrdinary head tail induction =>
      exact .consOrdinary (head.mono smaller_le) induction
  | consProtected head tail induction =>
      exact .consProtected
        (fun target instantiation =>
          (head target instantiation).mono smaller_le)
        induction

theorem previous
    (safe : ProtectedFuelEnvironmentSafe (index + 1) values targets provenance) :
    ProtectedFuelEnvironmentSafe index values targets provenance :=
  safe.mono (Nat.le_succ index)

/-- Erase protection and provenance for consumers using the existing
fuel-indexed DFS environment relation.  A protected entry is viewed at its
general type via the identity substitution. -/
theorem toFuelEnvironmentSafe
    (safe : ProtectedFuelEnvironmentSafe index values targets provenance) :
    FuelEnvironmentSafe index values targets := by
  induction safe with
  | nil => exact FuelEnvironmentSafe.nil index
  | consOrdinary head tail induction =>
      exact .cons head induction
  | consProtected head tail induction =>
      exact .cons head.atGeneral induction

end ProtectedFuelEnvironmentSafe

/-- Generic `letE` composition for one protected generalized binding.

`operationalFuel` is shared by the executable right-hand side and body exactly
as required by `evalFuel`.  `bindingIndex` is the independent logical index of
the protected environment entry; `bodyPredicate` may retain a different result
index or another concrete postcondition. -/
theorem evalFuel_letE_protectedResultSafeWith
    (environmentSafe : ProtectedFuelEnvironmentSafe bindingIndex environment
      runtimeContext provenance)
    (valueSafe : FuelResultSafeWith
      (fun value => ProtectedFuelValueSafe bindingIndex value general)
      (evalFuel operationalFuel environment valueExpression))
    (bodySafe : ∀ value,
      ProtectedFuelEnvironmentSafe bindingIndex (value :: environment)
        (general :: runtimeContext) (true :: provenance) →
      FuelResultSafeWith bodyPredicate
        (evalFuel operationalFuel (value :: environment) bodyExpression)) :
    FuelResultSafeWith bodyPredicate
      (evalFuel (operationalFuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  apply evalFuel_letE_resultSafeWith valueSafe
  intro value valuePost
  exact bodySafe value (.consProtected valuePost environmentSafe)

/-- Fuel-indexed result specialization of the generic protected-`letE` rule.
Evaluation fuel, binding index, and result index remain separate arguments. -/
theorem evalFuel_letE_protectedFuelSafe
    (environmentSafe : ProtectedFuelEnvironmentSafe bindingIndex environment
      runtimeContext provenance)
    (valueSafe : FuelResultSafeWith
      (fun value => ProtectedFuelValueSafe bindingIndex value general)
      (evalFuel operationalFuel environment valueExpression))
    (bodySafe : ∀ value,
      ProtectedFuelEnvironmentSafe bindingIndex (value :: environment)
        (general :: runtimeContext) (true :: provenance) →
      FuelResultSafe resultIndex bodyTarget
        (evalFuel operationalFuel (value :: environment) bodyExpression)) :
    FuelResultSafe resultIndex bodyTarget
      (evalFuel (operationalFuel + 1) environment
        (.letE valueExpression bodyExpression)) :=
  evalFuel_letE_protectedResultSafeWith environmentSafe valueSafe bodySafe

/-- Conditional all-index entry point for a future source-wide proof: a protected
postcondition supplied for every logical index can be specialized after the
body chooses `bindingIndex`. -/
theorem evalFuel_letE_allFuelProtectedResultSafeWith
    (environmentSafe : ProtectedFuelEnvironmentSafe bindingIndex environment
      runtimeContext provenance)
    (valueSafe : FuelResultSafeWith
      (fun value => AllFuelProtectedValueSafe value general)
      (evalFuel operationalFuel environment valueExpression))
    (bodySafe : ∀ value,
      ProtectedFuelEnvironmentSafe bindingIndex (value :: environment)
        (general :: runtimeContext) (true :: provenance) →
      FuelResultSafeWith bodyPredicate
        (evalFuel operationalFuel (value :: environment) bodyExpression)) :
    FuelResultSafeWith bodyPredicate
      (evalFuel (operationalFuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  apply evalFuel_letE_protectedResultSafeWith environmentSafe
  · exact valueSafe.mono (fun value allIndices => allIndices bindingIndex)
  · exact bodySafe

/-- Fuel-indexed result specialization of the all-index protected-`letE`
entry point.  The result index is independent of both evaluator fuel and the
body environment's logical index. -/
theorem evalFuel_letE_allFuelProtectedFuelSafe
    (environmentSafe : ProtectedFuelEnvironmentSafe bindingIndex environment
      runtimeContext provenance)
    (valueSafe : FuelResultSafeWith
      (fun value => AllFuelProtectedValueSafe value general)
      (evalFuel operationalFuel environment valueExpression))
    (bodySafe : ∀ value,
      ProtectedFuelEnvironmentSafe bindingIndex (value :: environment)
        (general :: runtimeContext) (true :: provenance) →
      FuelResultSafe resultIndex bodyTarget
        (evalFuel operationalFuel (value :: environment) bodyExpression)) :
    FuelResultSafe resultIndex bodyTarget
      (evalFuel (operationalFuel + 1) environment
        (.letE valueExpression bodyExpression)) :=
  evalFuel_letE_allFuelProtectedResultSafeWith environmentSafe valueSafe bodySafe

end TypePM.Runtime
