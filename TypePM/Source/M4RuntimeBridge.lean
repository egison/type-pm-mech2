import TypePM.Source.M4CompletenessArchitecture
import TypePM.NoStuck

/-!
# Runtime bridge anchored at M4 typing

The runtime theorem was originally anchored only at the completed M2--M3
`Source.Typing` judgment.  This module gives M4 clients a genuine entrypoint:
for expressions in the shared M2--M3 syntax fragment, an M4 derivation is
transported to that completed judgment and then to runtime typing.  The
fragment premise is explicit; `fixE` and matcher-bearing expressions require
new runtime rules rather than an accidental claim through the older anchor.
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

end TypePM.Source.M4
