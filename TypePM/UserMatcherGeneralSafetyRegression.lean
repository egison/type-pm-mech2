import TypePM.UserMatcherGeneralSafety

/-!
# General user-matcher safety regressions

These examples instantiate the reusable theorem at zero, one, and two holes,
and exercise ordered clause fallthrough after a normal header mismatch.
-/

namespace TypePM.UserMatcherGeneralSafetyRegression

open TypePM.Source TypePM.Runtime

def CoreEmbeddedTyping : EmbeddedExpressionTyping :=
  fun context expression target => RuntimeTyping expression target context

theorem coreEvaluatorSafe (fuel : Nat) :
    EmbeddedEvaluatorSafe CoreEmbeddedTyping (evalFuel fuel) := by
  intro environmentTypes environment expression target environmentTyped
    expressionTyped
  exact expressionTyped.coreSafety fuel environment environmentTyped

def emptyProductListBody : Source.Expr :=
  .ctor DataCtor.cons [.tuple [], .ctor DataCtor.nil []]

def zeroHoleClause : Source.MatcherClause :=
  .mk .wild (.tuple []) [.mk .wild emptyProductListBody]

theorem zeroHoleClause_input_typed :
    RuntimeMatcherClauseInputTyping [] [] .int .wild zeroHoleClause := by
  apply RuntimeMatcherClauseInputTyping.mk
    (holes := []) (captureTypes := [])
  · exact .wild
  · exact .zero
  · exact .cons (.mk .wild
      (.listCons (.tuple .nil) (.listNil (.prod [])))) .nil
  · intro dispatch inspected
    simp [inspectPatternPattern] at inspected
    subst dispatch
    exact .nil

theorem zeroHoleClause_typedSafe :
    tryMatcherClause (evalFuel 3) [] [] .wild (.int 4) zeroHoleClause =
        .timeout ∨
      ∃ result,
        tryMatcherClause (evalFuel 3) [] [] .wild (.int 4) zeroHoleClause =
          .ok result ∧
        MatcherClauseResultTyping result := by
  exact tryMatcherClause_typedSafe (coreEvaluatorSafe 3) .nil .nil (.int 4)
    zeroHoleClause_input_typed

theorem oneHoleClause_input_typed :
    RuntimeMatcherClauseInputTyping [] [] .int .var
      singleHoleVariableClause := by
  apply RuntimeMatcherClauseInputTyping.mk
    (holes := [⟨.any, .int⟩]) (captureTypes := [])
  · exact .hole .any
  · exact .one (.checked (.something .int) (.matcherToSlot .equal))
  · exact .cons
      (.mk .var (singletonDecompositionBody_typed [] .int)) .nil
  · intro dispatch inspected
    simp [inspectPatternPattern] at inspected
    subst dispatch
    exact .nil

theorem oneHoleClause_typedSafe :
    tryMatcherClause (evalFuel 3) [] [] .var (.int 5)
        singleHoleVariableClause = .timeout ∨
      ∃ result,
        tryMatcherClause (evalFuel 3) [] [] .var (.int 5)
          singleHoleVariableClause = .ok result ∧
        MatcherClauseResultTyping result := by
  exact tryMatcherClause_typedSafe (coreEvaluatorSafe 3) .nil .nil (.int 5)
    oneHoleClause_input_typed

def pairProductListBody : Source.Expr :=
  .ctor DataCtor.cons
    [.tuple [.var 0, .var 0], .ctor DataCtor.nil []]

def twoHoleClause : Source.MatcherClause :=
  .mk (.ctor PatternCtor.cons [.hole, .hole])
    (.tuple [.something, .something])
    [.mk .var pairProductListBody]

def twoHolePattern : Source.Pattern :=
  .ctor PatternCtor.cons [.var, .wild]

theorem twoHoleClause_input_typed :
    RuntimeMatcherClauseInputTyping [] [] .int twoHolePattern twoHoleClause := by
  apply RuntimeMatcherClauseInputTyping.mk
    (holes := [⟨.any, .int⟩, ⟨.any, .int⟩]) (captureTypes := [])
  · apply RuntimePPatTyping.ctor
    exact RuntimePPatsTyping.cons (.hole .any)
      (RuntimePPatsTyping.cons (.hole .any) .nil)
  · apply RuntimeNextMatchersTyping.many
    exact RuntimeTypings.cons
      (.checked (.something .int) (.matcherToSlot .equal))
      (RuntimeTypings.cons
        (.checked (.something .int) (.matcherToSlot .equal)) .nil)
  · apply RuntimeMatcherArmsTyping.cons
    · apply RuntimeMatcherArmTyping.mk RuntimeDPatTyping.var
      exact .listCons
        (.tuple (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (.listNil (.prod [.int, .int]))
    · exact .nil
  · intro dispatch inspected
    simp [twoHolePattern, inspectPatternPattern, inspectPatternPatterns] at inspected
    subst dispatch
    exact .nil

theorem twoHoleClause_typedSafe :
    tryMatcherClause (evalFuel 3) [] [] twoHolePattern (.int 6)
        twoHoleClause = .timeout ∨
      ∃ result,
        tryMatcherClause (evalFuel 3) [] [] twoHolePattern (.int 6)
          twoHoleClause = .ok result ∧
        MatcherClauseResultTyping result := by
  exact tryMatcherClause_typedSafe (coreEvaluatorSafe 3) .nil .nil (.int 6)
    twoHoleClause_input_typed

def capturedMatcherClause : Source.MatcherClause :=
  .mk (.ctor PatternCtor.cons [.capture, .hole])
    (.var 0)
    [.mk .var singletonDecompositionBody]

def capturedMatcherPattern : Source.Pattern :=
  .ctor PatternCtor.cons [.value .something, .var]

theorem capturedMatcherClause_input_typed :
    RuntimeMatcherClauseInputTyping [] [] .int capturedMatcherPattern
      capturedMatcherClause := by
  apply RuntimeMatcherClauseInputTyping.mk
    (holes := [⟨.any, .int⟩])
    (captureTypes := [.matcher .any .int])
  · apply RuntimePPatTyping.ctor
    exact RuntimePPatsTyping.cons RuntimePPatTyping.capture
      (RuntimePPatsTyping.cons (.hole .any) .nil)
  · exact .one (.checked
      (RuntimeTyping.var (target := .matcher .any .int) rfl)
      (.matcherToSlot .equal))
  · exact .cons
      (.mk .var
        (singletonDecompositionBody_typed [.matcher .any .int] .int)) .nil
  · intro dispatch inspected
    simp [capturedMatcherPattern, inspectPatternPattern,
      inspectPatternPatterns] at inspected
    subst dispatch
    exact .cons (.something .int) .nil

/-- This instantiation requires the corrected next-matcher environment:
the next matcher is variable zero, namely the captured `something`. -/
theorem capturedMatcherClause_typedSafe :
    tryMatcherClause (evalFuel 3) [] [] capturedMatcherPattern (.int 7)
        capturedMatcherClause = .timeout ∨
      ∃ result,
        tryMatcherClause (evalFuel 3) [] [] capturedMatcherPattern (.int 7)
          capturedMatcherClause = .ok result ∧
        MatcherClauseResultTyping result := by
  exact tryMatcherClause_typedSafe (coreEvaluatorSafe 3) .nil .nil (.int 7)
    capturedMatcherClause_input_typed

theorem capturedMatcherClause_exact :
    tryMatcherClause (evalFuel 3) [] [] capturedMatcherPattern (.int 7)
        capturedMatcherClause =
      .ok (.hit [[⟨.var, .something, .int 7⟩]]) := by
  with_unfolding_all rfl

theorem orderedClauses_input_typed :
    RuntimeMatcherClausesInputTyping [] [] .int twoHolePattern
      [zeroHoleClause, twoHoleClause] := by
  exact .cons
    (by
      apply RuntimeMatcherClauseInputTyping.mk
        (holes := []) (captureTypes := [])
      · exact .wild
      · exact .zero
      · exact .cons (.mk .wild
          (.listCons (.tuple .nil) (.listNil (.prod [])))) .nil
      · intro dispatch inspected
        simp [twoHolePattern, inspectPatternPattern] at inspected)
    (.cons twoHoleClause_input_typed .nil)

theorem orderedClauses_typedSafe :
    dispatchMatcherClauses (evalFuel 3) [] []
        [zeroHoleClause, twoHoleClause] twoHolePattern (.int 6) = .timeout ∨
      ∃ result,
        dispatchMatcherClauses (evalFuel 3) [] []
          [zeroHoleClause, twoHoleClause] twoHolePattern (.int 6) = .ok result ∧
        MatcherClauseResultTyping result := by
  exact dispatchMatcherClauses_typedSafe (coreEvaluatorSafe 3)
    .nil .nil (.int 6) orderedClauses_input_typed

end TypePM.UserMatcherGeneralSafetyRegression
