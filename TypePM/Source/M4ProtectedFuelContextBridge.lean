import TypePM.ProtectedPolymorphicLetFuelSafety
import TypePM.Source.M4RecursiveElaboration
import TypePM.Source.PolymorphicLetRuntimeBridge

/-!
# M4 source contexts and protected fuel-indexed environments

`ProtectedContextCompatible` explains how one source scheme occurrence is
represented by a monotype and a provenance bit in the runtime context.
`ProtectedFuelEnvironmentSafe` gives the corresponding runtime value a
step-indexed dynamic certificate.  This module composes those two independent
relations at one variable lookup.

For an ordinary entry, source compatibility supplies equality with the exact
instantiated occurrence type.  For a protected entry, it supplies an
`IsInstance` witness and the dynamic relation validates every such instance.
The bridge contains no premise about a completed expression evaluation or
search result.
-/

namespace TypePM.Runtime

namespace ProtectedContextCompatible

/-- Recover step-indexed value safety at the concrete type selected by one
source-scheme occurrence.

The source context, runtime type context, value environment, and provenance
mask are joined only through their existing lookup relations.  In particular,
the theorem does not assume the value returned by evaluating the variable. -/
theorem lookupFuelValueSafe
    {sourceContext : Source.Context} {runtimeContext : List Ty}
    {provenance : List Bool} {solution : Subst}
    {index : Nat} {environment : ValueEnvironment}
    {position : Nat} {scheme : Source.Scheme} {supply : Source.Supply}
    (compatible : ProtectedContextCompatible sourceContext runtimeContext
      provenance solution)
    (environmentSafe : ProtectedFuelEnvironmentSafe index environment
      runtimeContext provenance)
    (sourceLookup : sourceContext[position]? = some scheme) :
    ∃ value,
      environment[position]? = some value ∧
        FuelValueSafe index value
          ((scheme.instantiate supply).1.apply solution) := by
  rcases compatible.lookup supply sourceLookup with ordinary | protectedCase
  · rcases ordinary with ⟨provenanceLookup, runtimeLookup⟩
    obtain ⟨value, valueLookup, entry⟩ :=
      environmentSafe.lookup position runtimeLookup provenanceLookup
    exact ⟨value, valueLookup, entry.ordinaryValue⟩
  · rcases protectedCase with
      ⟨general, provenanceLookup, runtimeLookup, instantiation⟩
    obtain ⟨value, valueLookup, entry⟩ :=
      environmentSafe.lookup position runtimeLookup provenanceLookup
    exact ⟨value, valueLookup, entry.atInstance instantiation⟩

/-- If the runtime value at the source-variable position is already known,
recover its certificate at the occurrence's instantiated source type. -/
theorem lookupFuelValueSafeOfValue
    {sourceContext : Source.Context} {runtimeContext : List Ty}
    {provenance : List Bool} {solution : Subst}
    {index : Nat} {environment : ValueEnvironment}
    {position : Nat} {scheme : Source.Scheme} {supply : Source.Supply}
    {value : Value}
    (compatible : ProtectedContextCompatible sourceContext runtimeContext
      provenance solution)
    (environmentSafe : ProtectedFuelEnvironmentSafe index environment
      runtimeContext provenance)
    (valueLookup : environment[position]? = some value)
    (sourceLookup : sourceContext[position]? = some scheme) :
    FuelValueSafe index value
      ((scheme.instantiate supply).1.apply solution) := by
  obtain ⟨foundValue, foundLookup, foundSafe⟩ :=
    compatible.lookupFuelValueSafe environmentSafe sourceLookup
      (supply := supply)
  rw [valueLookup] at foundLookup
  cases foundLookup
  exact foundSafe

end ProtectedContextCompatible

/-- Evaluate a source variable under aligned static and dynamic contexts.

Evaluator fuel is independent of the logical safety index: zero evaluator
fuel times out, while positive fuel returns the lookup value certified by
`ProtectedContextCompatible.lookupFuelValueSafe`. -/
theorem evalFuel_var_protectedFuelSafe
    {sourceContext : Source.Context} {runtimeContext : List Ty}
    {provenance : List Bool} {solution : Subst}
    {index : Nat} {environment : ValueEnvironment}
    {position : Nat} {scheme : Source.Scheme} {supply : Source.Supply}
    (compatible : ProtectedContextCompatible sourceContext runtimeContext
      provenance solution)
    (environmentSafe : ProtectedFuelEnvironmentSafe index environment
      runtimeContext provenance)
    (sourceLookup : sourceContext[position]? = some scheme)
    (operationalFuel : Nat) :
    FuelResultSafe index ((scheme.instantiate supply).1.apply solution)
      (evalFuel operationalFuel environment (.var position)) := by
  obtain ⟨value, valueLookup, valueSafe⟩ :=
    compatible.lookupFuelValueSafe environmentSafe sourceLookup
      (supply := supply)
  simpa [FuelResultSafe, FuelResultSafeWith] using
    (evalFuel_var_resultSafeWith valueLookup valueSafe operationalFuel)

end TypePM.Runtime

namespace TypePM.Source.M4

open TypePM.Runtime

/-- Complete the variable case of a future raw M4 runtime-certificate
induction.

The positive-fuel `ElaboratesFuel` rule supplies the source scheme lookup and
identifies `generated.target` with that occurrence's instantiated type.  The
same shared substitution is used by source/runtime context compatibility and
by the generated target in the conclusion.  No premise says that this shared
substitution solves a generated block, and no completed evaluation equation or
search result is required. -/
theorem ElaboratesFuel.var_protectedFuelSafe
    {signature : FrozenSignature} {staticFuel : Nat}
    {sourceContext : Context} {position : Nat} {supply next : Supply}
    {generated : Generated}
    {runtimeContext : List Ty} {provenance : List Bool}
    {solution : Subst} {logicalIndex operationalFuel : Nat}
    {environment : ValueEnvironment}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) sourceContext
      (.var position) supply generated next)
    (compatible : ProtectedContextCompatible sourceContext runtimeContext
      provenance solution)
    (environmentSafe : ProtectedFuelEnvironmentSafe logicalIndex environment
      runtimeContext provenance) :
    FuelResultSafe logicalIndex (generated.target.apply solution)
      (evalFuel operationalFuel environment (.var position)) := by
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨scheme, sourceLookup, generatedEq, _nextEq⟩ := elaboration
  rw [generatedEq]
  exact evalFuel_var_protectedFuelSafe compatible environmentSafe sourceLookup
    operationalFuel

end TypePM.Source.M4
