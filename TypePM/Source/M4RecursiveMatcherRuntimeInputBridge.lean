import TypePM.Source.M4RecursiveMatcherInputBridge

/-!
# Runtime-leaf specialization of the recursive M4 input bridge

The capture-aware recursive bridge is callback-parametric.  When every
next-matcher expression and matcher-arm body lies in the executable
`RuntimeSupported` fragment, the same exact input derivation can be lowered
to the `RuntimeMatcherClausesInputTyping` certificate consumed by common-fuel
`TotalMatchingAtomTyping.user`.

This specialization retains the input pattern inspected by dispatch.  It
does not replace returned branches by arbitrary branches with matching erased
types.
-/

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

theorem MatcherClauseTotalInputElaboratesUsing.toRuntimeInputTyping_of_m4Fuel
    (input : MatcherClauseTotalInputElaboratesUsing
      (M4.ElaboratesFuel signature fuel) signature
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      solution atomEnvironmentTypes pattern context
      matcherTarget clause supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : MatcherClauseRuntimeExpressionsSupported clause)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClauseInputTyping atomEnvironmentTypes definitionTypes
      (matcherTarget.apply solution) pattern clause := by
  cases input with
  | mk shape headerElaboration nextElaboration armsElaboration captures =>
      rename_i header nextMatchers arms generatedHeader afterHeader generatedNext
        afterNext generatedArms
      cases supported with
      | mk nextSupported armsSupported =>
          have headerSolved : Solves solution generatedHeader.hard := by
            intro equation member
            exact semantic.1 equation (by simp [member])
          have nextSemantic : generatedNext.RuntimeSolution solution := by
            constructor
            · intro equation member
              exact semantic.1 equation (by simp [member])
            · intro obligation member
              exact semantic.2 obligation (by simp [member])
          have armsSemantic : generatedArms.checks.RuntimeSolution solution := by
            constructor
            · intro equation member
              exact semantic.1 equation (by simp [member])
            · intro obligation member
              exact semantic.2 obligation (by simp [member])
          have nextContextCompatible :=
            runtimeContextCompatible_extendPatternContext
              (bindings := generatedHeader.captures) contextCompatible
          exact .mk
            (headerElaboration.toRuntimePPatTyping headerSolved)
            (nextElaboration.toRuntimeNextMatchersTyping_of_m4Fuel compatible
              nextSupported nextSemantic nextContextCompatible)
            (armsElaboration.toRuntimeMatcherArmsTyping_of_m4Fuel compatible
              armsSupported armsSemantic contextCompatible)
            (by
              intro dispatch inspected
              exact captures inspected)

theorem MatcherClausesTotalInputElaborateUsing.toRuntimeInputTyping_of_m4Fuel
    (input : MatcherClausesTotalInputElaborateUsing
      (M4.ElaboratesFuel signature fuel) signature
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      solution atomEnvironmentTypes pattern context
      matcherTarget clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClausesInputTyping atomEnvironmentTypes definitionTypes
      (matcherTarget.apply solution) pattern clauses := by
  induction input with
  | nil => exact .nil
  | cons head tail induction =>
      cases supported with
      | cons headSupported tailSupported =>
          simp only [GeneratedChecks.runtimeSolution_append] at semantic
          exact .cons
            (head.toRuntimeInputTyping_of_m4Fuel compatible headSupported
              semantic.1 contextCompatible)
            (induction tailSupported semantic.2)

/-- Exact recursive-M4 literal input derivations with runtime-supported leaves
feed the non-parametric common-fuel user-matcher certificate. -/
theorem MatcherLiteralTotalInputElaboratesUsing.toRuntimeInputTyping_of_m4Fuel
    (input : MatcherLiteralTotalInputElaboratesUsing
      (M4.ElaboratesFuel signature fuel) signature
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      solution atomEnvironmentTypes pattern context clauses
      supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClausesInputTyping atomEnvironmentTypes definitionTypes
      ((Ty.var ⟨supply.ty⟩).apply solution) pattern clauses := by
  cases input with
  | mk checked clauses =>
      rename_i generatedClauses
      have clausesSemantic : generatedClauses.checks.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · exact semantic.2
      exact clauses.toRuntimeInputTyping_of_m4Fuel compatible supported
        clausesSemantic contextCompatible

end TypePM.Source.MatcherTyping
