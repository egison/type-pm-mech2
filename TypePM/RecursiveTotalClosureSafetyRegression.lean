import TypePM.RecursiveTotalClosureSafety

/-!
# Recursive total-closure regression

The body of this recursive function is a matcher literal, so it has
`TotalCoreTyping` but no old `RuntimeTyping` derivation.  Applying the function
returns the matcher closure that captures both the argument and the recursive
closure itself.  This is the smallest exact witness for the proof-only
parallel environment layer.
-/

namespace TypePM.Runtime.RecursiveTotalClosureSafetyRegression

open TypePM.Source

def body : Source.Expr := .matcher []

def program : Source.Expr := .app (.fixE body) (.lit 7)

def resultType : Ty := .matcher .any .int

def functionType : Ty := .fn .int resultType

def expectedClosure : Value := Value.recursiveClosure [] body

def expectedValue : Value :=
  Value.matcherClosure [.int 7, expectedClosure] []

/-- The recursive body is outside old `RuntimeTyping` precisely because it is
a matcher literal, but it is a direct total-core term. -/
theorem body_totalCoreTyping :
    TotalCoreTyping body resultType [.int, functionType] := by
  exact .matcher RuntimeMatcherClausesTyping.nil

theorem body_totalRecursiveTyping :
    TotalRecursiveClosureBodyTyping [.int, functionType] body resultType := by
  exact .matcher TotalRuntimeMatcherClausesTyping.nil

theorem body_totalEnvironmentSafe :
    TotalEnvironmentSafe body resultType [.int, functionType] := by
  exact totalEnvironmentSafe_totalMatcher TotalRuntimeMatcherClausesTyping.nil

theorem closure_totalValueTyping :
    TotalValueTyping expectedClosure functionType := by
  exact .recursiveClosure TotalValueTypings.nil body_totalRecursiveTyping

/-- The parallel canonical-form theorem exposes the total-core recursive
body, rather than forcing it back into `RuntimeTyping`. -/
theorem closure_functionCanonical :
    (∃ environment context bodyExpression,
      expectedClosure = Value.plainClosure environment bodyExpression ∧
      TotalEnvironmentTyping environment context ∧
      TotalRecursiveClosureBodyTyping (.int :: context) bodyExpression
        resultType) ∨
    (∃ environment context bodyExpression,
      expectedClosure = Value.recursiveClosure environment bodyExpression ∧
      TotalEnvironmentTyping environment context ∧
      TotalRecursiveClosureBodyTyping (.int :: functionType :: context)
        bodyExpression resultType) :=
  closure_totalValueTyping.function_canonical

/-- Direct application preservation for the recursive closure itself. -/
theorem directApplication_totalTyped (fuel : Nat) :
    TotalTypedResult resultType
      (applyFuel fuel expectedClosure (.int 7)) := by
  exact applyFuel_recursiveClosure_totalTyped TotalValueTypings.nil
    body_totalRecursiveTyping body_totalEnvironmentSafe
    (.ordinary (.int 7)) fuel

theorem program_totalTyped (fuel : Nat) :
    TotalTypedResult resultType (evalFuel fuel [] program) := by
  exact evalFixApplication_totalTyped TotalValueTypings.nil
    body_totalRecursiveTyping body_totalEnvironmentSafe
    (totalEnvironmentSafe_lit 7) fuel

theorem program_neverStuck (fuel : Nat) :
    (evalFuel fuel [] program).NotStuck :=
  (program_totalTyped fuel).notStuck

/-- The exact result records the newest-first environment layout:
argument, recursive self, then the definition environment. -/
theorem program_exact :
    evalFuel 3 [] program = .ok expectedValue := by
  rfl

theorem expectedValue_totalTyping :
    TotalValueTyping expectedValue resultType := by
  exact .matcherClosure
    (.cons (.ordinary (.int 7))
      (.cons closure_totalValueTyping .nil))
    TotalRuntimeMatcherClausesTyping.nil ⟨[], by simp⟩

theorem exactEvaluation_typed :
    evalFuel 3 [] program = .ok expectedValue ∧
      TotalValueTyping expectedValue resultType :=
  ⟨program_exact, expectedValue_totalTyping⟩

end TypePM.Runtime.RecursiveTotalClosureSafetyRegression
