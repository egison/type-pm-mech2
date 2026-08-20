import TypePM.CoreSafety

/-!
# No-stuck corollaries for the certified runtime core

These are the theorem-5.8 endpoints currently justified by the runtime and
source layers.  Both quantify over every fuel amount; timeout remains an
ordinary bounded-evaluation outcome.
-/

namespace TypePM.Runtime

/-- Runtime-typing form of theorem 5.8 for the certified canonical core. -/
theorem RuntimeTyping.neverStuck
    (typing : RuntimeTyping expression target)
    (fuel : Nat) (environment : ValueEnvironment) :
    (evalFuel fuel environment expression).NotStuck :=
  (typing.coreSafety fuel environment).notStuck

end TypePM.Runtime

namespace TypePM.Source

namespace Typing

/-- **Theorem 5.8, certified core.**  A closed declaratively typed source
expression in the supported runtime core never produces `stuck`, for any
fuel. -/
theorem neverStuck
    {signature : Signature} {expression : Expr} {target : Ty}
    (typing : Typing signature [] expression target)
    (compatible : Runtime.SignatureCompatible signature)
    (supported : Runtime.RuntimeSupported expression)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (typing.coreSafety compatible supported fuel).notStuck

end Typing

namespace Inference

/-- Executable-inference form of theorem 5.8 for the certified core. -/
theorem infer_neverStuck
    {signature : Signature} (wellFormed : signature.WellFormed)
    (compatible : Runtime.SignatureCompatible signature)
    {expression : Expr} {target : Ty}
    (success : infer signature [] expression = some target)
    (supported : Runtime.RuntimeSupported expression)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (infer_success_typing wellFormed success).neverStuck compatible supported fuel

end Inference

end TypePM.Source
