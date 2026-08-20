import TypePM.Source.M4CompletenessArchitecture
import TypePM.NoStuck

/-!
# Runtime bridge anchored at M4 typing

The runtime theorem was originally anchored only at the completed M2--M3
`Source.Typing` judgment.  This module gives M4 clients a genuine entrypoint:
for expressions in the shared M2--M3 syntax fragment, an M4 derivation is
transported to that completed judgment and then to runtime typing.  The
fragment premise is explicit; `fixE` and matcher-bearing expressions require
new bridge cases rather than an accidental claim through the older anchor.
This module also supplies that case for an ordinary `fixE` whose body lies in
the shared M2--M3 runtime fragment.  Matcher-root recursion remains separate.
-/

namespace TypePM.Source.M4

open TypePM.Source
open CompletenessArchitecture

namespace PrincipalTyping

/-- An M4 principal derivation in the shared M2--M3 syntax is also a principal
derivation of the completed source judgment. -/
theorem toM2_of_m2Fragment
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {target : Ty}
    (fragment : M2Fragment expression)
    (typing : M4.PrincipalTyping signature context expression target) :
    Source.PrincipalTyping signature.base context expression target := by
  rcases typing with ⟨derivation⟩
  exact ⟨
    { generated := derivation.generated
      next := derivation.next
      elaboration := CompletenessArchitecture.Elaborates.toM2_of_m2Fragment
        fragment derivation.elaboration
      closure := derivation.closure
      absorbing := derivation.absorbing
      target_eq := derivation.target_eq }⟩

private theorem fromFix_semantic_parts
    {domain codomain : Ty} {body : Generated} {solution : Subst}
    (semantic : (Generated.fromFix domain codomain body).SemanticSolution
      solution) :
    body.SemanticSolution solution ∧
      Equation.Holds solution (.ty body.target codomain) := by
  constructor
  · constructor
    · intro equation membership
      exact semantic.1 equation (by
        simp [Generated.fromFix, membership])
    · intro obligation membership
      exact semantic.2 obligation (by
        simpa [Generated.fromFix] using membership)
  · exact semantic.1 _ (by simp [Generated.fromFix])

private theorem fixElaboration_parts
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {body : Expr} {start next : Supply} {generated : Generated}
    (derivation : FixElaboratesUsing (M4.ElaboratesFuel signature fuel)
      context (.fixE body) start generated next) :
    ∃ generatedBody,
      M4.ElaboratesFuel signature fuel
        (Fix.bodyContext (Fix.domain body start) (Fix.codomain body start)
          context)
        body (Fix.bodySupply body start) generatedBody next ∧
      generated = Generated.fromFix (Fix.domain body start)
        (Fix.codomain body start) generatedBody := by
  cases derivation with
  | fixE _direct bodyElaboration =>
      exact ⟨_, bodyElaboration, rfl⟩

/-- A normally shaped M4 `fixE` whose body lies in the certified M2--M3
runtime fragment has a runtime typing.  This is the first genuinely M4-only
case of the state-erasure bridge. -/
theorem fixE_toRuntimeTyping_of_m2Body
    {signature : FrozenSignature} {body : Expr} {target : Ty}
    (typing : M4.PrincipalTyping signature [] (.fixE body) target)
    (fragment : M2Fragment body)
    (compatible : Runtime.SignatureCompatible signature.base)
    (supported : Runtime.RuntimeSupported body) :
    Runtime.RuntimeTyping (.fixE body) target := by
  rcases typing with ⟨derivation⟩
  rcases derivation.elaboration with ⟨fuel, fuelDerivation⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at fuelDerivation
  | succ fuel =>
    simp only [M4.ElaboratesFuel] at fuelDerivation
    obtain ⟨generatedBody, bodyElaboration, generated_eq⟩ :=
      fixElaboration_parts fuelDerivation
    let solution := derivation.closure.substitution
    have semantic : (Generated.fromFix
        (Fix.domain body (Context.initialSupply []))
        (Fix.codomain body (Context.initialSupply []))
        generatedBody).SemanticSolution solution := by
      rw [← generated_eq]
      exact TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
        derivation.closure
    obtain ⟨bodySemantic, bodyEquation⟩ :=
      fromFix_semantic_parts semantic
    have bodyM2 := elaboratesFuel_toM2_of_m2Fragment fragment bodyElaboration
    have bodyRuntime := supported.elaboration_typing compatible bodyM2
      bodySemantic
      (Runtime.MonomorphicContextCompatible.cons
        (Runtime.MonomorphicContextCompatible.cons
          Runtime.MonomorphicContextCompatible.nil))
    simp only [Equation.Holds] at bodyEquation
    rw [bodyEquation] at bodyRuntime
    have fixRuntime : Runtime.RuntimeTyping (.fixE body)
        (.fn ((Fix.domain body (Context.initialSupply [])).apply solution)
          ((Fix.codomain body (Context.initialSupply [])).apply solution)) := by
      simpa [Fix.bodyContext, Ty.apply] using
        Runtime.RuntimeTyping.fixE bodyRuntime
    rw [derivation.target_eq]
    simpa [PrincipalBlockClosure.target, generated_eq, Generated.fromFix,
      Ty.apply, solution] using fixRuntime

end PrincipalTyping

namespace Typing

/-- M4 typing conservatively extends the completed M2--M3 source typing on
their shared syntax. -/
theorem toM2_of_m2Fragment
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {target : Ty}
    (typing : M4.Typing signature context expression target)
    (fragment : M2Fragment expression) :
    Source.Typing signature.base context expression target := by
  rcases typing with ⟨principal, principalTyping, instantiation⟩
  exact ⟨principal,
    principalTyping.toM2_of_m2Fragment fragment,
    instantiation⟩

/-- State-erasure bridge whose public premise is M4 typing.  The two fragment
certificates state separately that the expression uses shared M2--M3 syntax
and lies in the currently certified runtime core. -/
theorem toRuntimeTyping_of_m2Fragment
    {signature : FrozenSignature} {expression : Expr} {target : Ty}
    (typing : M4.Typing signature [] expression target)
    (fragment : M2Fragment expression)
    (compatible : Runtime.SignatureCompatible signature.base)
    (supported : Runtime.RuntimeSupported expression) :
    Runtime.RuntimeTyping expression target :=
  (typing.toM2_of_m2Fragment fragment).toRuntimeTyping compatible supported

/-- No-stuck corollary for the M4-anchored shared fragment. -/
theorem neverStuck_of_m2Fragment
    {signature : FrozenSignature} {expression : Expr} {target : Ty}
    (typing : M4.Typing signature [] expression target)
    (fragment : M2Fragment expression)
    (compatible : Runtime.SignatureCompatible signature.base)
    (supported : Runtime.RuntimeSupported expression)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (typing.toM2_of_m2Fragment fragment).neverStuck compatible supported fuel

/-- Runtime bridge for an arbitrary substitution instance of a principal
ordinary `fixE` result. -/
theorem fixE_toRuntimeTyping_of_m2Body
    {signature : FrozenSignature} {body : Expr} {target : Ty}
    (typing : M4.Typing signature [] (.fixE body) target)
    (fragment : M2Fragment body)
    (compatible : Runtime.SignatureCompatible signature.base)
    (supported : Runtime.RuntimeSupported body) :
    Runtime.RuntimeTyping (.fixE body) target := by
  rcases typing with ⟨principal, principalTyping, instantiation⟩
  have principalRuntime := principalTyping.fixE_toRuntimeTyping_of_m2Body
    fragment compatible supported
  rcases instantiation with ⟨substitution, targetEquality⟩
  rw [← targetEquality]
  exact principalRuntime.apply substitution

/-- No-stuck corollary for ordinary M4 `fixE` expressions with certified
M2--M3 bodies. -/
theorem fixE_neverStuck_of_m2Body
    {signature : FrozenSignature} {body : Expr} {target : Ty}
    (typing : M4.Typing signature [] (.fixE body) target)
    (fragment : M2Fragment body)
    (compatible : Runtime.SignatureCompatible signature.base)
    (supported : Runtime.RuntimeSupported body)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] (.fixE body)).NotStuck :=
  Runtime.RuntimeTyping.neverStuck
    (typing.fixE_toRuntimeTyping_of_m2Body fragment compatible supported)
    fuel [] .nil

end Typing

/-- Executable M4 inference form of the shared-fragment no-stuck theorem. -/
theorem infer_neverStuck_of_m2Fragment
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    (compatible : Runtime.SignatureCompatible signature.base)
    {expression : Expr} {target : Ty}
    (success : M4.infer signature [] expression = some target)
    (fragment : M2Fragment expression)
    (supported : Runtime.RuntimeSupported expression)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (M4.infer_success_typing wellFormed success).neverStuck_of_m2Fragment
    fragment compatible supported fuel

/-- Executable inference form of the ordinary M4 `fixE` no-stuck theorem. -/
theorem infer_fixE_neverStuck_of_m2Body
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    (compatible : Runtime.SignatureCompatible signature.base)
    {body : Expr} {target : Ty}
    (success : M4.infer signature [] (.fixE body) = some target)
    (fragment : M2Fragment body)
    (supported : Runtime.RuntimeSupported body)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] (.fixE body)).NotStuck :=
  (M4.infer_success_typing wellFormed success).fixE_neverStuck_of_m2Body
    fragment compatible supported fuel

end TypePM.Source.M4
