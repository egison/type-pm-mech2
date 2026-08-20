import TypePM.Source.Elaboration
import TypePM.Source.PairDestructuring

/-!
# Pair-destructuring source regressions

These kernel-checked examples fix the two projection schemes and the nameless
binding order used by Paper 1's pair lambdas.  Runtime success is proved in a
separate M5 regression once the two primitive delta rules are connected.
-/

namespace TypePM.Source.PairDestructuringRegression

open TypePM

theorem pair_first_instantiation_exact :
    PrimitiveSchemes.pairFirst.instantiate ⟨7, 3⟩ =
      (.fn (.prod [.var ⟨7⟩, .var ⟨8⟩]) (.var ⟨7⟩), ⟨9, 3⟩) := by
  rfl

theorem pair_second_instantiation_exact :
    PrimitiveSchemes.pairSecond.instantiate ⟨7, 3⟩ =
      (.fn (.prod [.var ⟨7⟩, .var ⟨8⟩]) (.var ⟨8⟩), ⟨9, 3⟩) := by
  rfl

def pairIdentity : Expr :=
  Expr.pairDestructuringLambda (.tuple [.var 0, .var 1])

/-- The two nested `let` bindings put the first field at index zero, the
second field at index one, and retain the original pair at index two. -/
theorem pair_identity_expands_exactly :
    pairIdentity =
      .lam
        (.letE (.prim .pairSecond [.var 0])
          (.letE (.prim .pairFirst [.var 1])
            (.tuple [.var 0, .var 1]))) := by
  rfl

theorem pair_projection_arities_exact :
    PrimitiveSchemes.pairFirst.callArity = 1 ∧
      PrimitiveSchemes.pairSecond.callArity = 1 := by
  exact ⟨rfl, rfl⟩

theorem pair_projections_are_in_standard_signature :
    Paper1Signature.signature.lookupPrimitive .pairFirst =
        some PrimitiveSchemes.pairFirst ∧
      Paper1Signature.signature.lookupPrimitive .pairSecond =
        some PrimitiveSchemes.pairSecond := by
  exact ⟨rfl, rfl⟩

end TypePM.Source.PairDestructuringRegression
