import TypePM.NoStuck

/-!
# Runtime-typing and safety regressions

The examples exercise the complete source-to-runtime chain for the currently
certified ground-product core.
-/

namespace TypePM.RuntimeTypingRegression

open TypePM.Source TypePM.Runtime

def nestedTuple : Source.Expr :=
  .tuple [.lit 1, .tuple [.lit 2, .lit 3]]

def nestedTupleType : Ty :=
  .prod [.int, .prod [.int, .int]]

theorem nestedTuple_runtimeTyping :
    RuntimeTyping nestedTuple nestedTupleType := by
  exact .tuple (.cons (.lit 1)
    (.cons (.tuple (.cons (.lit 2) (.cons (.lit 3) .nil))) .nil))

theorem nestedTuple_supported : RuntimeSupported nestedTuple :=
  ⟨nestedTupleType, nestedTuple_runtimeTyping⟩

private theorem unify_nil_exact : unify [] = some Subst.id := by
  unfold unify
  rw [unifyLoop.eq_def]

private theorem close_empty (target : Ty) :
    inferGeneratedUsing unify ⟨target, [], []⟩ =
      some ⟨Subst.id, target⟩ := by
  simp [inferGeneratedUsing, saturateUsing, saturateLoop,
    unify_nil_exact, promoteUnder, residualEquations]

theorem infer_nestedTuple_exact :
    infer Paper1Signature.signature [] nestedTuple = some nestedTupleType := by
  have elaborated :
      elaborateRoot Paper1Signature.signature [] nestedTuple =
        some ⟨nestedTupleType, [], []⟩ := by
    simp [nestedTuple, nestedTupleType, elaborateRoot, elaborate,
      elaborateItems]
  simp [infer, elaborated, close_empty]

theorem nestedTuple_sourceTyping :
    Source.Typing Paper1Signature.signature [] nestedTuple nestedTupleType :=
  Inference.infer_success_typing Paper1Signature.wellFormed
    infer_nestedTuple_exact

/-- The theorem-5.6 bridge recovers the same structural runtime judgment from
the independent public source typing. -/
theorem nestedTuple_state_erasure :
    RuntimeTyping nestedTuple nestedTupleType :=
  nestedTuple_sourceTyping.toRuntimeTyping nestedTuple_supported

/-- Successful evaluation preserves the nested product type. -/
theorem nestedTuple_typed_result :
    TypedResult nestedTupleType (evalFuel 3 [] nestedTuple) :=
  nestedTuple_sourceTyping.coreSafety nestedTuple_supported 3

/-- Public inference success rules out runtime `stuck` at every fuel amount. -/
theorem inferred_nestedTuple_neverStuck (fuel : Nat) :
    (evalFuel fuel [] nestedTuple).NotStuck :=
  Inference.infer_neverStuck Paper1Signature.wellFormed
    infer_nestedTuple_exact nestedTuple_supported fuel

/-- The preservation endpoint identifies the exact runtime value type. -/
theorem nestedTuple_exact_valueTyping :
    ValueTyping
      (.tuple [.int 1, .tuple [.int 2, .int 3]]) nestedTupleType := by
  have typed := nestedTuple_typed_result
  rcases typed with timeout | ⟨value, success, valueTyping⟩
  · have evaluated :
        evalFuel 3 [] nestedTuple =
          .ok (.tuple [.int 1, .tuple [.int 2, .int 3]]) := by
      rfl
    rw [evaluated] at timeout
    contradiction
  · cases success
    exact valueTyping

/-- The runtime coverage invariant needed by `matchFirst` safety is visible at
the executable boundary: an empty arm list is stuck.  The M4 static
elaborator's exhaustiveness gate rejects this shape. -/
theorem matchFirst_empty_arms_is_stuck :
    evalFuel 3 [] (.matchFirst (.lit 1) .something []) = .stuck := by
  rfl

/-- The current theorem boundary is intentionally strict: even a harmless
identity application awaits closure/application preservation. -/
theorem identity_application_not_in_certified_core :
    ¬ RuntimeSupported (.app (.lam (.var 0)) (.lit 1)) := by
  intro supported
  rcases supported with ⟨target, typing⟩
  cases typing

end TypePM.RuntimeTypingRegression
