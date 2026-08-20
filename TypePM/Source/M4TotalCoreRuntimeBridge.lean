import TypePM.CommonFuelSafety
import TypePM.Source.M4UserMatcherRuntimeBridge

/-!
# M4 matcher literals at the total-runtime boundary

This module connects a solved relational matcher literal under the fixed
Paper-1 signature to the `TotalCoreTyping` certificate consumed by the
common-fuel safety theorem.  Runtime coverage of the embedded next-matcher
expressions and arm bodies, and compatibility of the solved source context
with the monomorphic runtime context, remain explicit premises.
-/

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- A solved relational M4 matcher literal is a total-core expression.

The result type is the matcher target introduced at the literal's input
supply.  `MatcherLiteralElaborates.toRuntimeMatcherClausesTyping` discharges
the nontrivial clause, arm, and body obligations; `TotalCoreTyping.matcher`
then packages the resulting matcher closure certificate.
-/
theorem MatcherLiteralElaborates.toTotalCoreTyping
    (elaboration : MatcherLiteralElaborates Paper1FrozenSignature.signature
      context clauses supply generated next)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalCoreTyping (.matcher clauses)
      (.matcher .any ((Ty.var ⟨supply.ty⟩).apply solution))
      definitionTypes := by
  exact TotalCoreTyping.matcher
    (elaboration.toRuntimeMatcherClausesTyping supported semantic
      contextCompatible)

/-- A closed solved matcher literal is total at the representative selected
by any principal block closure for its generated constraints. -/
theorem MatcherLiteralElaborates.toTotalCoreTypingAtClosure
    (elaboration : MatcherLiteralElaborates Paper1FrozenSignature.signature
      [] clauses supply generated next)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (closure : PrincipalBlockClosure generated) :
    TotalCoreTyping (.matcher clauses)
      (.matcher .any ((Ty.var ⟨supply.ty⟩).apply closure.substitution)) [] := by
  exact elaboration.toTotalCoreTyping supported
    (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution closure)
    MonomorphicContextCompatible.nil

end TypePM.Source.MatcherTyping

namespace TypePM.Generated

/-- A later type substitution preserves a semantic solution.  This is the
constraint-level transport needed to instantiate a solved matcher target
without rebuilding its clause derivation. -/
theorem SemanticSolution.postcompose
    (semantic : TypePM.Generated.SemanticSolution generated earlier)
    (later : Subst) :
    TypePM.Generated.SemanticSolution generated
      (Subst.compose later earlier) := by
  constructor
  · exact solves_postcompose semantic.1 later
  · intro obligation membership
    obtain ⟨conversionClass, conversion⟩ :=
      semantic.2 obligation membership
    exact ⟨conversionClass, by
      simpa only [Ty.apply_compose] using
        TypePM.Runtime.CheckConversion.apply conversion later⟩

end TypePM.Generated

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- Closed matcher-literal bridge for any instance of the principal matcher
target.  The runtime matcher capability remains deliberately `.any`: the
runtime closure constructor does not claim the more precise source-side
capability inferred from matcher evidence. -/
theorem MatcherLiteralElaborates.toTotalCoreTypingAtTargetInstance
    (elaboration : MatcherLiteralElaborates Paper1FrozenSignature.signature
      [] clauses supply generated next)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (closure : PrincipalBlockClosure generated)
    (instantiation : IsInstance
      ((Ty.var ⟨supply.ty⟩).apply closure.substitution) target) :
    TotalCoreTyping (.matcher clauses) (.matcher .any target) [] := by
  obtain ⟨later, targetEquality⟩ := instantiation
  have semantic :=
    (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution closure).postcompose
      later
  have typed := elaboration.toTotalCoreTyping supported semantic
    MonomorphicContextCompatible.nil
  rw [← Ty.apply_compose, targetEquality] at typed
  exact typed

/-- Evaluation of a closed, solved relational matcher literal cannot get
stuck, at every instance of its principal matcher target. -/
theorem MatcherLiteralElaborates.neverStuckAtTargetInstance
    (elaboration : MatcherLiteralElaborates Paper1FrozenSignature.signature
      [] clauses supply generated next)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (closure : PrincipalBlockClosure generated)
    (instantiation : IsInstance
      ((Ty.var ⟨supply.ty⟩).apply closure.substitution) target)
    (fuel : Nat) :
    (evalFuel fuel [] (.matcher clauses)).NotStuck :=
  TotalCoreTyping.neverStuck
    (elaboration.toTotalCoreTypingAtTargetInstance supported closure instantiation)
    fuel [] .nil

end TypePM.Source.MatcherTyping
