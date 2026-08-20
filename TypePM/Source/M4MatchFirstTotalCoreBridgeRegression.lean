import TypePM.Source.M4MatchFirstTotalCoreBridge
import TypePM.Source.M4RecursiveElaborationRegression
import TypePM.Runtime.EvaluationAdequacy

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

/-- Public inference now supplies the hidden relational derivation, fuel, and
semantic solution; the regression provides only the dynamic built-in support
that static M4 typing intentionally does not encode. -/
theorem totalCoreTyping_from_solved_m4 :
    TotalCoreTyping M4RecursiveElaborationRegression.firstMatch .int [] := by
  exact inferSomethingMatchFirstToTotalCoreTyping
    M4RecursiveElaborationRegression.infer_match_first_exact (.lit)
      armsSupported (.lit)

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

/-- The exact closed execution also witnesses the relational semantics. -/
theorem evaluatesResult :
    Eval [] M4RecursiveElaborationRegression.firstMatch (.int 2) :=
  evalFuel_sound exactResult

/-- The public M4-accepted example cannot get stuck at any common fuel. -/
theorem neverStuck (fuel : Nat) :
    (evalFuel fuel [] M4RecursiveElaborationRegression.firstMatch).NotStuck :=
  totalCoreTyping_from_solved_m4.neverStuck fuel [] .nil

/-! ## Monomorphic open context

The target, selected arm body, and fallback all read the same source variable.
The public inference result fixes the expression type, while the separate
support certificate connects the hidden principal substitution to the
explicit runtime context `[Int]`. -/

def openFirst : Expr :=
  .matchFirst (.var 0) .something [.mk .wild (.var 0)] (.var 0)

theorem elaborate_open_first_exact :
    M4.elaborate Paper1FrozenSignature.signature [.mono .int] openFirst
        (Context.initialSupply [.mono .int]) =
      some (M4RecursiveElaborationRegression.firstMatchGenerated, ⟨2, 1⟩) := by
  rfl'

theorem infer_open_first_exact :
    M4.infer Paper1FrozenSignature.signature [.mono .int] openFirst =
      some .int := by
  unfold M4.infer
  rw [elaborate_open_first_exact]
  exact M4RecursiveElaborationRegression.close_match_first_exact

private theorem openArmsSupported :
    DirectArmsRuntimeSupported .something [.mk .wild (.var 0)] := by
  exact .cons
    { pattern := .wild
      body := .var
      matcherShape := by
        intro fuel environment matcherValue success
        cases fuel with
        | zero => simp [evalFuel] at success
        | succ fuel =>
            simp [evalFuel] at success
            subst matcherValue
            exact .somethingWild }
    .nil

private theorem openRuntimeContextSupport :
    PrincipalRuntimeContextSupport
      (M4.infer_success_principalTyping Paper1FrozenSignature.wellFormed
        infer_open_first_exact) [.int] := by
  exact ⟨MonomorphicContextCompatible.cons MonomorphicContextCompatible.nil⟩

/-- Public inference plus a compatibility certificate for its exact hidden
principal closure yields total runtime typing in an explicit open context. -/
theorem totalCoreTyping_from_open_solved_m4 :
    TotalCoreTyping openFirst .int [.int] := by
  exact inferSomethingMatchFirstToTotalCoreTypingInContext
    infer_open_first_exact (.var) openArmsSupported (.var)
      openRuntimeContextSupport

theorem publicOpenInferAndRuntimeTyping :
    M4.infer Paper1FrozenSignature.signature [.mono .int] openFirst =
        some .int ∧
      M4.Typing Paper1FrozenSignature.signature [.mono .int] openFirst .int ∧
      TotalCoreTyping openFirst .int [.int] :=
  ⟨infer_open_first_exact,
    M4.infer_success_typing Paper1FrozenSignature.wellFormed
      infer_open_first_exact,
    totalCoreTyping_from_open_solved_m4⟩

theorem openExactResult :
    evalFuel 3 [.int 19] openFirst = .ok (.int 19) := by
  with_unfolding_all rfl

/-- The exact open-context execution also witnesses the relational
semantics. -/
theorem openEvaluatesResult : Eval [.int 19] openFirst (.int 19) :=
  evalFuel_sound openExactResult

/-- The open-context inferred example cannot get stuck at any common fuel
when the concrete environment has the certified runtime context. -/
theorem openNeverStuck (fuel : Nat) :
    (evalFuel fuel [.int 19] openFirst).NotStuck :=
  totalCoreTyping_from_open_solved_m4.neverStuck fuel [.int 19]
    (EnvironmentTyping.cons (.int 19) EnvironmentTyping.nil)

end TypePM.Source.M4MatchFirstTotalCoreBridgeRegression
