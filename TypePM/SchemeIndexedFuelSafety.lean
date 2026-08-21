import TypePM.ValueIndexedStableFirstOrderSafety
import TypePM.Source.M4RecursiveElaboration

/-!
# Source-scheme-indexed fuel safety

An open source context contains schemes, whereas the evaluator stores only
runtime values.  This module relates the two directly under one fixed
enclosing substitution.  Each entry varies only the bound variables selected
by `Scheme.instantiate`; free variables are interpreted by the same fixed
`solution` at every occurrence.

The relation quantifies over every `Supply` argument.  It does not claim that
all of them occur in one finite derivation or carry a separate freshness
proof; it is a sound sufficient family from which an actual elaboration supply
can be selected.

The logical index is independent of evaluator fuel.  The result-packaging and
`letE` rules below consume recursive child-safety callbacks for the evaluator's
actual result.  They do not assume an equation exposing a completed result or
store such an equation in a certificate.  The `letE` rules are conditional
composition infrastructure, not a class-wide source-to-runtime producer.
-/

namespace TypePM.Runtime

/-- A runtime value is safe at every supply-indexed occurrence type generated
from one scheme, with the enclosing substitution held fixed. -/
def SchemeFuelValueSafe (index : Nat) (value : Value)
    (scheme : Source.Scheme) (solution : Subst) : Prop :=
  ∀ supply,
    FuelValueSafe index value
      ((scheme.instantiate supply).1.apply solution)

namespace SchemeFuelValueSafe

/-- Lift an ordinary monotype certificate into its source monomorphic scheme.
This is the finite-index entry point used by lambda arguments and matching
bindings. -/
theorem ofMono
    (safe : FuelValueSafe index value (target.apply solution)) :
    SchemeFuelValueSafe index value (Source.Scheme.mono target) solution := by
  intro supply
  simpa using safe

theorem atSupply
    (safe : SchemeFuelValueSafe index value scheme solution)
    (supply : Source.Supply) :
    FuelValueSafe index value
      ((scheme.instantiate supply).1.apply solution) :=
  safe supply

theorem mono
    (safe : SchemeFuelValueSafe larger value scheme solution)
    (smaller_le : smaller ≤ larger) :
    SchemeFuelValueSafe smaller value scheme solution :=
  fun supply => (safe supply).mono smaller_le

theorem previous
    (safe : SchemeFuelValueSafe (index + 1) value scheme solution) :
    SchemeFuelValueSafe index value scheme solution :=
  safe.mono (Nat.le_succ index)

end SchemeFuelValueSafe

/-- Pointwise safety for a runtime environment and its exact source context.
The constructors enforce equal lengths by construction. -/
inductive SchemeFuelEnvironmentSafe (index : Nat) (solution : Subst) :
    List Value → Source.Context → Prop where
  | nil : SchemeFuelEnvironmentSafe index solution [] []
  | cons
      (head : SchemeFuelValueSafe index value scheme solution)
      (tail : SchemeFuelEnvironmentSafe index solution values context) :
      SchemeFuelEnvironmentSafe index solution (value :: values)
        (scheme :: context)

namespace SchemeFuelEnvironmentSafe

private theorem sourceScheme_mem_of_getElem?_eq_some
    {context : Source.Context} {position : Nat} {scheme : Source.Scheme}
    (lookup : context[position]? = some scheme) :
    scheme ∈ context := by
  induction context generalizing position with
  | nil => simp at lookup
  | cons head tail induction =>
      cases position with
      | zero =>
          simp at lookup
          subst scheme
          simp
      | succ position =>
          simp only [List.getElem?_cons_succ] at lookup
          exact List.mem_cons_of_mem head (induction lookup)

/-- Closing a source scheme by `block` does not change its executable
occurrence type under a solution of the enclosing context interface.  The
bound variables opened by `supply` are identical on both sides. -/
theorem instantiate_applyFree_apply_eq_of_interface
    {context : Source.Context} {scheme : Source.Scheme}
    (schemeMember : scheme ∈ context)
    (block solution : Subst)
    (solved : Solves solution (context.interfaceEquations block))
    (supply : Source.Supply) :
    ((scheme.applyFree block).instantiate supply).1.apply solution =
      (scheme.instantiate supply).1.apply solution := by
  have agree :=
    (context.solves_interfaceEquations_iff block solution).mp solved
  have bodyEquality :
      (scheme.body.applyFree block).applyFree solution =
        scheme.body.applyFree solution := by
    rw [Source.PolyTy.applyFree_compose]
    apply Source.PolyTy.applyFree_eq_of_agree
    · intro freeVariable membership
      exact (agree.1 freeVariable (by
        apply mem_dedupFirst.mpr
        exact List.mem_flatMap.mpr ⟨scheme, schemeMember,
          Source.Scheme.mem_freeTyVars.mpr membership⟩)).symm
    · intro freeVariable membership
      exact (agree.2 freeVariable (by
        apply mem_dedupFirst.mpr
        exact List.mem_flatMap.mpr ⟨scheme, schemeMember,
          Source.Scheme.mem_freeCapVars.mpr membership⟩)).symm
  unfold Source.Scheme.instantiate Source.Scheme.applyFree
  rw [← Source.PolyTy.openBound_applyFree,
    ← Source.PolyTy.openBound_applyFree, bodyEquality]

theorem valueContextLength
    (safe : SchemeFuelEnvironmentSafe index solution values context) :
    values.length = context.length := by
  induction safe with
  | nil => rfl
  | cons _ _ induction => simp [induction]

/-- Source lookup returns the aligned runtime value and its whole
scheme-occurrence family certificate. -/
theorem lookup
    (safe : SchemeFuelEnvironmentSafe index solution values context)
    (position : Nat)
    (sourceFound : context[position]? = some scheme) :
    ∃ value,
      values[position]? = some value ∧
        SchemeFuelValueSafe index value scheme solution := by
  induction position generalizing values context scheme with
  | zero =>
      cases safe with
      | nil => simp at sourceFound
      | cons head tail =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceFound ⊢
          subst scheme
          exact ⟨_, rfl, head⟩
  | succ position induction =>
      cases safe with
      | nil => simp at sourceFound
      | cons head tail =>
          simp only [List.getElem?_cons_succ] at sourceFound ⊢
          exact induction tail sourceFound

/-- Lookup when the runtime value is already known. -/
theorem lookupValue
    (safe : SchemeFuelEnvironmentSafe index solution values context)
    (position : Nat)
    (valueFound : values[position]? = some value)
    (sourceFound : context[position]? = some scheme) :
    SchemeFuelValueSafe index value scheme solution := by
  obtain ⟨foundValue, found, valueSafe⟩ := safe.lookup position sourceFound
  rw [valueFound] at found
  cases found
  exact valueSafe

/-- Lookup specialized to one supply-indexed source occurrence type. -/
theorem lookupFuelValueSafe
    (safe : SchemeFuelEnvironmentSafe index solution values context)
    (position : Nat)
    (valueFound : values[position]? = some value)
    (sourceFound : context[position]? = some scheme)
    (supply : Source.Supply) :
    FuelValueSafe index value
      ((scheme.instantiate supply).1.apply solution) :=
  (safe.lookupValue position valueFound sourceFound).atSupply supply

/-- The relation is downward closed in its logical index. -/
theorem mono
    (safe : SchemeFuelEnvironmentSafe larger solution values context)
    (smaller_le : smaller ≤ larger) :
    SchemeFuelEnvironmentSafe smaller solution values context := by
  induction safe with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (head.mono smaller_le) induction

theorem previous
    (safe : SchemeFuelEnvironmentSafe (index + 1) solution values context) :
    SchemeFuelEnvironmentSafe index solution values context :=
  safe.mono (Nat.le_succ index)

private theorem ofApplyFreeInterface_of_subset
    {outerContext : Source.Context}
    (safe : SchemeFuelEnvironmentSafe index solution values context)
    (subset : ∀ scheme, scheme ∈ context → scheme ∈ outerContext)
    (solved : Solves solution
      (outerContext.interfaceEquations block)) :
    SchemeFuelEnvironmentSafe index solution values
      (context.applyFree block) := by
  induction safe with
  | nil => exact .nil
  | @cons value scheme values context head tail induction =>
      have headSafe : SchemeFuelValueSafe index value
          (scheme.applyFree block) solution := by
        intro supply
        rw [instantiate_applyFree_apply_eq_of_interface
          (subset scheme (by simp)) block solution solved supply]
        exact head supply
      have tailSafe : SchemeFuelEnvironmentSafe index solution values
          (context.applyFree block) := by
        apply induction
        intro tailScheme membership
        exact subset tailScheme (by simp [membership])
      simpa only [Source.Context.applyFree, List.map] using
        SchemeFuelEnvironmentSafe.cons headSafe tailSafe

/-- Transport an aligned runtime environment to the body-tail context created
by source `let` generalization.  `solved` is purely static interface evidence;
the value environment and logical index are unchanged. -/
theorem ofApplyFreeInterface
    (safe : SchemeFuelEnvironmentSafe index solution environment
      sourceContext)
    (solved : Solves solution
      (sourceContext.interfaceEquations block)) :
    SchemeFuelEnvironmentSafe index solution environment
      (sourceContext.applyFree block) :=
  safe.ofApplyFreeInterface_of_subset (fun _ membership => membership) solved

/-- Lift an ordinary substituted monotype environment into the corresponding
source context of monomorphic schemes.  This retains a single finite logical
index and therefore also applies to lambda arguments and matching bindings. -/
theorem ofFuelEnvironmentSafeAppliedMonotypes
    (safe : FuelEnvironmentSafe index values
      (Ty.applyList solution targets)) :
    SchemeFuelEnvironmentSafe index solution values
      (targets.map Source.Scheme.mono) := by
  induction targets generalizing values with
  | nil =>
      have lengths := safe.1
      simp [Ty.applyList] at lengths
      subst values
      exact .nil
  | cons target targets induction =>
      cases values with
      | nil =>
          have lengths := safe.1
          simp [Ty.applyList] at lengths
      | cons value values =>
          obtain ⟨foundValue, found, headSafe⟩ := safe.2 0
            (target.apply solution) (by simp [Ty.applyList])
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst foundValue
          have tailSafe : FuelEnvironmentSafe index values
              (Ty.applyList solution targets) := by
            constructor
            · have lengths := safe.1
              simpa [Ty.applyList] using Nat.succ.inj lengths
            · intro position foundTarget targetFound
              obtain ⟨foundValue, valueFound, valueSafe⟩ := safe.2
                (position + 1) foundTarget (by
                  simpa [Ty.applyList] using targetFound)
              exact ⟨foundValue, by
                simpa only [List.getElem?_cons_succ] using valueFound,
                valueSafe⟩
          simpa only [List.map] using
            SchemeFuelEnvironmentSafe.cons
              (SchemeFuelValueSafe.ofMono headSafe)
              (induction tailSafe)

end SchemeFuelEnvironmentSafe

/-- Evaluate a source variable directly from the scheme-aligned environment.
No runtime monotype, provenance bit, or all-`IsInstance` certificate is
required. -/
theorem evalFuel_var_schemeFuelSafe
    {sourceContext : Source.Context} {solution : Subst}
    {index : Nat} {environment : ValueEnvironment}
    {position : Nat} {scheme : Source.Scheme} {supply : Source.Supply}
    (environmentSafe : SchemeFuelEnvironmentSafe index solution environment
      sourceContext)
    (sourceFound : sourceContext[position]? = some scheme)
    (operationalFuel : Nat) :
    FuelResultSafe index
      ((scheme.instantiate supply).1.apply solution)
      (evalFuel operationalFuel environment (.var position)) := by
  obtain ⟨value, valueFound, valueSafe⟩ :=
    environmentSafe.lookup position sourceFound
  simpa [FuelResultSafe, FuelResultSafeWith] using
    (evalFuel_var_resultSafeWith valueFound (valueSafe supply)
      operationalFuel)

/-- Package recursive safety proofs for the same deterministic result at each
supply-indexed occurrence type into one scheme-family result postcondition. -/
theorem schemeFuelResultSafeWith_of_forallSupply
    (pointwise : ∀ supply,
      FuelResultSafe index
        ((scheme.instantiate supply).1.apply solution) result) :
    FuelResultSafeWith
      (fun value => SchemeFuelValueSafe index value scheme solution)
      result := by
  cases resultEq : result with
  | timeout => exact .inl rfl
  | stuck =>
      have one := pointwise (⟨0, 0⟩ : Source.Supply)
      rcases one with timeout | ⟨value, success, _safe⟩
      · rw [resultEq] at timeout
        contradiction
      · rw [resultEq] at success
        contradiction
  | ok actual =>
      refine .inr ⟨actual, rfl, ?_⟩
      intro supply
      rcases pointwise supply with timeout | ⟨value, success, valueSafe⟩
      · rw [resultEq] at timeout
        contradiction
      · rw [resultEq] at success
        cases success
        exact valueSafe

/-- Scheme-aligned environment safety at every logical index.  The empty
top-level environment satisfies this relation for every substitution. -/
def AllFuelSchemeEnvironmentSafe (solution : Subst) (values : List Value)
    (context : Source.Context) : Prop :=
  ∀ index, SchemeFuelEnvironmentSafe index solution values context

namespace AllFuelSchemeEnvironmentSafe

theorem nil (solution : Subst) :
    AllFuelSchemeEnvironmentSafe solution [] [] :=
  fun _ => .nil

theorem atIndex
    (safe : AllFuelSchemeEnvironmentSafe solution values context)
    (index : Nat) :
    SchemeFuelEnvironmentSafe index solution values context :=
  safe index

end AllFuelSchemeEnvironmentSafe

/-- One source-scheme entry safe at every logical index. -/
def AllFuelSchemeValueSafe (value : Value) (scheme : Source.Scheme)
    (solution : Subst) : Prop :=
  ∀ index, SchemeFuelValueSafe index value scheme solution

namespace AllFuelSchemeValueSafe

theorem atIndex
    (safe : AllFuelSchemeValueSafe value scheme solution)
    (index : Nat) :
    SchemeFuelValueSafe index value scheme solution :=
  safe index

theorem atIndexSupply
    (safe : AllFuelSchemeValueSafe value scheme solution)
    (index : Nat) (supply : Source.Supply) :
    FuelValueSafe index value
      ((scheme.instantiate supply).1.apply solution) :=
  safe index supply

end AllFuelSchemeValueSafe

/-- Package recursive safety proofs for the same deterministic result at every
logical index and every supply-indexed scheme occurrence type. -/
theorem allFuelSchemeResultSafeWith_of_forallIndexSupply
    (pointwise : ∀ index supply,
      FuelResultSafe index
        ((scheme.instantiate supply).1.apply solution) result) :
    FuelResultSafeWith
      (fun value => AllFuelSchemeValueSafe value scheme solution)
      result := by
  cases resultEq : result with
  | timeout => exact .inl rfl
  | stuck =>
      have one := pointwise 0 (⟨0, 0⟩ : Source.Supply)
      rcases one with timeout | ⟨value, success, _safe⟩
      · rw [resultEq] at timeout
        contradiction
      · rw [resultEq] at success
        contradiction
  | ok actual =>
      refine .inr ⟨actual, rfl, ?_⟩
      intro index supply
      rcases pointwise index supply with timeout |
          ⟨value, success, valueSafe⟩
      · rw [resultEq] at timeout
        contradiction
      · rw [resultEq] at success
        cases success
        exact valueSafe

/-- Conditional closed-first `letE` composition from recursive child-safety
callbacks.  The right-hand-side callback is invoked for each logical index and
each supply-indexed scheme occurrence; it is not a premise about a selected
successful value. -/
theorem evalFuel_letE_allFuelScheme_childSafe
    (outerSafe : AllFuelSchemeEnvironmentSafe solution environment
      sourceContext)
    (valueChildSafe : ∀ index supply,
      SchemeFuelEnvironmentSafe index solution environment sourceContext →
        FuelResultSafe index
          ((scheme.instantiate supply).1.apply solution)
          (evalFuel fuel environment valueExpression))
    (bodyChildSafe : ∀ value,
      AllFuelSchemeEnvironmentSafe solution (value :: environment)
          (scheme :: sourceContext) →
        FuelResultSafe resultIndex bodyTarget
          (evalFuel fuel (value :: environment) bodyExpression)) :
    FuelResultSafe resultIndex bodyTarget
      (evalFuel (fuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  apply evalFuel_letE_resultSafeWith
    (boundPredicate := fun value =>
      AllFuelSchemeValueSafe value scheme solution)
  · apply allFuelSchemeResultSafeWith_of_forallIndexSupply
    intro index supply
    exact valueChildSafe index supply (outerSafe index)
  · intro value valueSafe
    apply bodyChildSafe value
    intro index
    exact .cons (valueSafe index) (outerSafe index)

/-- Conditional closed-first `letE` composition in the exact M4 context
shape.  `closeOuter` is a static context-transport callback; it contains no
evaluator outcome. -/
theorem evalFuel_letE_allFuelScheme_closedContext_childSafe
    (outerSafe : AllFuelSchemeEnvironmentSafe solution environment
      sourceContext)
    (closeOuter : ∀ index,
      SchemeFuelEnvironmentSafe index solution environment sourceContext →
        SchemeFuelEnvironmentSafe index solution environment closedContext)
    (valueChildSafe : ∀ index supply,
      SchemeFuelEnvironmentSafe index solution environment sourceContext →
        FuelResultSafe index
          ((scheme.instantiate supply).1.apply solution)
          (evalFuel fuel environment valueExpression))
    (bodyChildSafe : ∀ value,
      AllFuelSchemeEnvironmentSafe solution (value :: environment)
          (scheme :: closedContext) →
        FuelResultSafe resultIndex bodyTarget
          (evalFuel fuel (value :: environment) bodyExpression)) :
    FuelResultSafe resultIndex bodyTarget
      (evalFuel (fuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  apply evalFuel_letE_resultSafeWith
    (boundPredicate := fun value =>
      AllFuelSchemeValueSafe value scheme solution)
  · apply allFuelSchemeResultSafeWith_of_forallIndexSupply
    intro index supply
    exact valueChildSafe index supply (outerSafe index)
  · intro value valueSafe
    apply bodyChildSafe value
    intro index
    exact .cons (valueSafe index) (closeOuter index (outerSafe index))

/-- Conditional closed-first `letE` composition for the actual M4 body-tail
context.  The static interface solution itself supplies the context transport,
so callers need not postulate a separate `closeOuter` function. -/
theorem evalFuel_letE_allFuelScheme_applyFree_childSafe
    (outerSafe : AllFuelSchemeEnvironmentSafe solution environment
      sourceContext)
    (interfaceSolved : Solves solution
      (sourceContext.interfaceEquations block))
    (valueChildSafe : ∀ index supply,
      SchemeFuelEnvironmentSafe index solution environment sourceContext →
        FuelResultSafe index
          ((scheme.instantiate supply).1.apply solution)
          (evalFuel fuel environment valueExpression))
    (bodyChildSafe : ∀ value,
      AllFuelSchemeEnvironmentSafe solution (value :: environment)
          (scheme :: sourceContext.applyFree block) →
        FuelResultSafe resultIndex bodyTarget
          (evalFuel fuel (value :: environment) bodyExpression)) :
    FuelResultSafe resultIndex bodyTarget
      (evalFuel (fuel + 1) environment
        (.letE valueExpression bodyExpression)) := by
  apply evalFuel_letE_allFuelScheme_closedContext_childSafe
    (outerSafe := outerSafe)
    (closeOuter := fun _ safe =>
      safe.ofApplyFreeInterface interfaceSolved)
    (valueChildSafe := valueChildSafe)
    (bodyChildSafe := bodyChildSafe)

end TypePM.Runtime

namespace TypePM.Source.M4

open TypePM.Runtime

/-- Complete the raw positive-fuel M4 variable case using the exact source
scheme occurrence and the fixed enclosing solution.  The rule reads neither a
protected runtime type nor an `IsInstance` witness. -/
theorem ElaboratesFuel.var_schemeFuelSafe
    {signature : FrozenSignature} {staticFuel : Nat}
    {sourceContext : Context} {position : Nat} {supply next : Supply}
    {generated : Generated} {solution : Subst}
    {logicalIndex operationalFuel : Nat}
    {environment : ValueEnvironment}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) sourceContext
      (.var position) supply generated next)
    (environmentSafe : SchemeFuelEnvironmentSafe logicalIndex solution
      environment sourceContext) :
    FuelResultSafe logicalIndex (generated.target.apply solution)
      (evalFuel operationalFuel environment (.var position)) := by
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨scheme, sourceFound, generatedEq, _nextEq⟩ := elaboration
  rw [generatedEq]
  exact evalFuel_var_schemeFuelSafe environmentSafe sourceFound
    operationalFuel

end TypePM.Source.M4
