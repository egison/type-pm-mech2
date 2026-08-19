import TypePM.RuntimeTyping

/-!
# Conditional core safety

For the certified ground-product core, bounded evaluation has only two
outcomes: fuel exhaustion or a value of the source type.  This is stronger
than a bare no-`stuck` statement: the successful branch is a preservation
theorem, while the two constructors together are typed ready progress.
-/

namespace TypePM.Runtime

/-- A typed evaluation result is either ordinary fuel exhaustion or a
successfully produced value of the indicated type.  The definition records
the positive observations, rather than defining safety as inequality with
`stuck`. -/
def TypedResult (target : Ty) (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧ ValueTyping value target

/-- List-valued counterpart used by left-to-right tuple evaluation. -/
def TypedResults (targets : List Ty) (result : FuelResult (List Value)) : Prop :=
  result = .timeout ∨
    ∃ values, result = .ok values ∧ ValueTypings values targets

namespace TypedResult

/-- Typed ready progress, exposing the two possible evaluator observations. -/
theorem progress
    (typed : TypedResult target result) :
    result = .timeout ∨
      ∃ value, result = .ok value ∧ ValueTyping value target := by
  exact typed

/-- A typed result cannot be the runtime rule-coverage failure. -/
theorem notStuck (typed : TypedResult target result) : result.NotStuck := by
  rcases typed with timeout | ⟨value, success, _typing⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TypedResult

mutual

/-- **Theorem 5.7, certified core.**  Expression evaluation preserves the
runtime type, and every fuel-bounded evaluation is ready: it either times out
or produces a typed value. -/
theorem RuntimeTyping.coreSafety
    (typing : RuntimeTyping expression target)
    (fuel : Nat) (environment : ValueEnvironment) :
    TypedResult target (evalFuel fuel environment expression) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      cases typing with
      | lit => exact .inr ⟨_, rfl, .int _⟩
      | tuple items =>
          have children := items.coreSafety fuel environment
          rcases children with timeout | ⟨values, success, childrenTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
          · exact .inr ⟨.tuple values, by
              simp [evalFuel, success, FuelResult.map], .tuple childrenTyping⟩

/-- Mutual list preservation/progress used by tuple evaluation. -/
theorem RuntimeTypings.coreSafety
    (typing : RuntimeTypings expressions targets)
    (fuel : Nat) (environment : ValueEnvironment) :
    TypedResults targets
      (FuelResult.traverse (evalFuel fuel environment) expressions) := by
  cases typing with
  | nil => exact .inr ⟨[], rfl, .nil⟩
  | cons head tail =>
      have headResult := head.coreSafety fuel environment
      rcases headResult with headTimeout |
        ⟨headValue, headSuccess, headTyping⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · have tailResult := tail.coreSafety fuel environment
        rcases tailResult with tailTimeout |
          ⟨tailValues, tailSuccess, tailTyping⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            .cons headTyping tailTyping⟩

end

end TypePM.Runtime

namespace TypePM.Source

namespace Typing

/-- Source-facing form of conditional core safety.  It combines theorem 5.6's
state-erasure bridge with the mutual runtime preservation/progress theorem. -/
theorem coreSafety
    {signature : Signature} {expression : Expr} {target : Ty}
    (typing : Typing signature [] expression target)
    (supported : Runtime.RuntimeSupported expression)
    (fuel : Nat) :
    Runtime.TypedResult target (Runtime.evalFuel fuel [] expression) :=
  (typing.toRuntimeTyping supported).coreSafety fuel []

end Typing

end TypePM.Source
