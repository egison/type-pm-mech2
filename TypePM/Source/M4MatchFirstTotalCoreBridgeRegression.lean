import TypePM.Source.M4MatchFirstTotalCoreBridge
import TypePM.Source.M4RecursiveElaborationRegression

/-!
# Exact total-runtime regression for solved M4 `matchFirst`

The accepted one-arm explicit-fallback example is inferred by the public M4
entry point.  Its executable elaboration is converted to the relational M4
derivation, and the general bridge constructs the common-fuel safety
certificate without a hand-written arm typing proof.
-/

namespace TypePM.Source.M4MatchFirstTotalCoreBridgeRegression

open TypePM.Runtime
open TypePM.Source.MatchFirstTyping

private def solution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

private theorem semantic :
    M4RecursiveElaborationRegression.firstMatchGenerated.SemanticSolution
      solution := by
  constructor
  · intro equation member
    simp [M4RecursiveElaborationRegression.firstMatchGenerated] at member
    rcases member with rfl | rfl
    · rfl
    · rfl
  · intro obligation member
    simp [M4RecursiveElaborationRegression.firstMatchGenerated] at member
    subst obligation
    exact ⟨.matcherToSlot,
      CheckConversion.matcherToSlot CapabilityDemand.equal⟩

private theorem armsSupported :
    DirectArmsRuntimeSupported .something
      [.mk .wild (.lit 2)] := by
  exact DirectArmsRuntimeSupported.cons
    { pattern := .wild
      body := .lit
      matcherShape := by
        intro fuel environment matcherValue success
        cases fuel with
        | zero => simp [evalFuel] at success
        | succ fuel =>
            simp [evalFuel] at success
            subst matcherValue
            exact .somethingWild }
    DirectArmsRuntimeSupported.nil

private theorem fuelElaboration :
    M4.ElaboratesFuel Paper1FrozenSignature.signature
      (M4RecursiveElaborationRegression.firstMatch.complexity + 1) []
      M4RecursiveElaborationRegression.firstMatch ⟨0, 0⟩
      M4RecursiveElaborationRegression.firstMatchGenerated ⟨2, 1⟩ := by
  apply M4.elaborateFuel_sound Paper1FrozenSignature.wellFormed
  simpa [M4.elaborate] using
    M4RecursiveElaborationRegression.elaborate_match_first_exact

/-- The general relational bridge, rather than a hand-built arm certificate,
produces total runtime typing for the publicly inferred example. -/
theorem totalCoreTyping_from_solved_m4 :
    TotalCoreTyping M4RecursiveElaborationRegression.firstMatch .int [] := by
  have bridged := m4FuelSomethingMatchFirstToTotalCoreTyping
    (fuel := 8) fuelElaboration (.lit) armsSupported (.lit) semantic
    MonomorphicContextCompatible.nil
  simpa [M4RecursiveElaborationRegression.firstMatch,
    M4RecursiveElaborationRegression.firstMatchGenerated, solution, Ty.apply]
    using bridged

/-- Static acceptance remains anchored at the public M4 inference endpoint. -/
theorem publicInferAndRuntimeTyping :
    M4.infer Paper1FrozenSignature.signature []
        M4RecursiveElaborationRegression.firstMatch = some .int ∧
      M4.Typing Paper1FrozenSignature.signature []
        M4RecursiveElaborationRegression.firstMatch .int ∧
      TotalCoreTyping M4RecursiveElaborationRegression.firstMatch .int [] :=
  ⟨M4RecursiveElaborationRegression.infer_match_first_exact,
    M4RecursiveElaborationRegression.match_first_typing,
    totalCoreTyping_from_solved_m4⟩

theorem exactResult :
    evalFuel 3 [] M4RecursiveElaborationRegression.firstMatch =
      .ok (.int 2) := by
  with_unfolding_all rfl

/-- The public M4-accepted example cannot get stuck at any common fuel. -/
theorem neverStuck (fuel : Nat) :
    (evalFuel fuel [] M4RecursiveElaborationRegression.firstMatch).NotStuck :=
  totalCoreTyping_from_solved_m4.neverStuck fuel [] .nil

end TypePM.Source.M4MatchFirstTotalCoreBridgeRegression
