import TypePM.Source.M4MatchFirstTyping
import TypePM.Source.M4FrozenSignatureRegression

/-!
# M4 single-result match regressions

`matchFirst` has ordinary matcher-driven arms and a separate mandatory
fallback, typed in the original context and independent of arm-local bindings.
At least one ordinary arm is required; a zero-arm form has no matching behavior
and should be written as its fallback expression instead.
-/

namespace TypePM.Source.M4MatchFirstTypingRegression

def signature : FrozenSignature := Paper1FrozenSignature.signature

/-- The source rule rejects a match with no ordinary arm. -/
theorem empty_arms_rejected :
    MatchFirstTyping.elaborate signature [] (.lit 1) (.lit 2) [] (.lit 7)
      ⟨0, 0⟩ = none := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.elaborateArmsUsing, TypePM.Source.elaborate]

def refutableArm : MatchFirstArm :=
  .mk (.value (.lit 1)) (.lit 11)

/-- A refutable final ordinary arm is accepted: result existence comes from
the separate fallback, not from a syntactic property of the last pattern. -/
theorem refutable_final_arm_accepted :
    MatchFirstTyping.elaborate signature [] (.lit 1) .something
      [refutableArm] (.lit 22) ⟨0, 0⟩ ≠ none := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.elaborateArmsUsing, MatchFirstTyping.elaborateTailUsing,
    MatchFirstTyping.elaborateTailUsingFuel, refutableArm,
    TypePM.Source.elaborate, elaboratePatternUsing, elaboratePatternUsingFuel,
    Pattern.extendContext, Supply.nextTy]

/-- The fallback is an ordinary expression checked in the original context. -/
theorem ill_scoped_fallback_rejected :
    MatchFirstTyping.elaborate signature [] (.lit 1) .something [refutableArm]
      (.var 0)
      ⟨0, 0⟩ = none := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.elaborateArmsUsing, TypePM.Source.elaborate]

def inconsistentArms : List MatchFirstArm :=
  [.mk .wild (.tuple [.lit 1])]

def inconsistentGenerated : Generated :=
  { target := .int
    hard := [.ty (.var ⟨1⟩) .int, .ty (.prod [.int]) .int]
    pending := [⟨.matcher .any (.var ⟨0⟩), .slot (.var ⟨0⟩) .int⟩] }

/-- Every ordinary arm body contributes an equality to the fallback's result
type; here the incompatible product body is recorded against `Int`. -/
theorem inconsistent_result_type_constraint_exact :
    MatchFirstTyping.elaborate signature [] (.lit 1) .something inconsistentArms
      (.lit 0) ⟨0, 0⟩ = some (inconsistentGenerated, ⟨2, 1⟩) := by
  simp [MatchFirstTyping.elaborate, MatchFirstTyping.elaborateUsing,
    MatchFirstTyping.elaborateArmsUsing, MatchFirstTyping.elaborateTailUsing,
    MatchFirstTyping.elaborateTailUsingFuel,
    MatchFirstTyping.GeneratedTail.fromArm,
    MatchFirstTyping.GeneratedArms.fromFallback,
    MatchFirstTyping.Generated.fromMatchFirst, inconsistentArms,
    inconsistentGenerated, TypePM.Source.elaborate, elaboratePatternUsing,
    elaboratePatternUsingFuel, Pattern.extendContext, elaborateItems,
    Supply.nextTy]

end TypePM.Source.M4MatchFirstTypingRegression
