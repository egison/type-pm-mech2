import TypePM.Source.M4OrdinaryCoherence
import TypePM.Source.M4FixCoherence
import TypePM.Source.M4MatcherCoherence
import TypePM.Source.M4MatchAllCoherence
import TypePM.Source.M4MatchFirstCoherence
import TypePM.Source.M4LetCoherence
import TypePM.Source.M4MatcherReplay
import TypePM.Source.M4MatchAllReplay
import TypePM.Source.M4MatchFirstReplay
import TypePM.Source.M4CompletionConsequences

/-!
# Completed M4 coherence, replay, and public consequences

This module is the unconditional endpoint of the M4 static development.  It
assembles the constructor-local coherence proofs by expression complexity,
uses the three pattern-bearing replay steps to connect every relational
derivation to the public elaborator, and then exposes completeness,
decidability, principality, and uniqueness without architecture parameters.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

/-- All independently valid M4 elaborations of the same source expression are
semantically coherent. -/
theorem fullM4Coherence : FullM4Coherence :=
  fullM4Coherence_of_steps ordinaryM4CoherenceStep fixCoherenceStep
    matcherCoherenceStep matchAllCoherenceStep matchFirstCoherenceStep
    m4LetTransportAndAssembly

/-- Every independently valid M4 elaboration is represented by a successful
run of the public executable elaborator. -/
theorem fullM4ExecutableReplay : FullM4ExecutableReplay :=
  fullM4ExecutableReplay_of_coherence_and_patternSteps fullM4Coherence
    matcherM4FuelReplayStep matchAllM4FuelReplayStep matchFirstM4FuelReplayStep

/-- The complete implementation inhabits the constructor-local coherence
boundary recorded by `M4CompletenessArchitecture`.  Keeping the conjunction
as a public theorem makes the architecture definition itself a regression
check rather than only documenting separately named components. -/
theorem m4CoherenceExtensionBoundary : M4CoherenceExtensionBoundary :=
  ⟨M4FreshRenaming.m4FreshRenamingTransport, ordinaryM4CoherenceStep,
    fixCoherenceStep, matcherCoherenceStep, matchAllCoherenceStep,
    matchFirstCoherenceStep, m4LetTransportAndAssembly⟩

/-- The complete normalization, replay, and coherence proofs also inhabit
the final 5.2--5.5 boundary as one checked conjunction. -/
theorem m4PrincipalityCompletionBoundary :
    M4PrincipalityCompletionBoundary := by
  let replay := fullM4FuelReplay_of_patternSteps fullM4Coherence
    matcherM4FuelReplayStep matchAllM4FuelReplayStep
      matchFirstM4FuelReplayStep
  exact ⟨m4FuelNormalization,
    m4LetClosureRepresentativeAgreement_of_fuelReplay replay,
    m4StructuralReplay_of_fuelReplay replay, fullM4Coherence⟩

/-- The public M4 elaborator computes a representative mutually instantiable
with every independently selected absorbing principal closure. -/
theorem wellFormedM4ElaborationPrincipalityComplete :
    WellFormedM4ElaborationPrincipalityComplete :=
  wellFormedM4ElaborationPrincipalityComplete_of_coherence_and_replay
    fullM4Coherence fullM4ExecutableReplay

end TypePM.Source.M4.CompletenessArchitecture

namespace TypePM.Source.M4

/-- Declarative M4 typing is complete for the public inference function. -/
theorem Typing.infer_isSome
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {target : Ty} (wellFormed : signature.WellFormed)
    (typing : Typing signature context expression target) :
    infer signature context expression ≠ none :=
  CompletenessArchitecture.Typing.infer_isSome_of_principalityComplete
    CompletenessArchitecture.wellFormedM4ElaborationPrincipalityComplete
    wellFormed typing

/-- Public M4 inference succeeds exactly when the independent declarative
typing relation assigns at least one result type. -/
theorem typable_iff_infer_isSome
    (signature : FrozenSignature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Typable signature context expression ↔
      infer signature context expression ≠ none :=
  typable_iff_infer_isSome_of_principalityComplete
    CompletenessArchitecture.wellFormedM4ElaborationPrincipalityComplete
    signature wellFormed context expression

/-- Declarative M4 typability is decidable through the public inference
function. -/
def typableDecidable
    (signature : FrozenSignature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Decidable (Typable signature context expression) :=
  typableDecidable_of_principalityComplete
    CompletenessArchitecture.wellFormedM4ElaborationPrincipalityComplete
    signature wellFormed context expression

/-- Any two blockwise-principal M4 typings of one expression have mutually
instantiable result types. -/
theorem principalCoherence
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    PrincipalCoherence signature context expression :=
  principalCoherence_of_fullM4 CompletenessArchitecture.fullM4Coherence
    wellFormed context expression

/-- Every successful public M4 inference result is globally principal. -/
theorem infer_success_principalResult
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer signature context expression = some target) :
    PrincipalResult signature context expression target :=
  infer_success_principalResult_of_fullM4
    CompletenessArchitecture.fullM4Coherence wellFormed success

/-- A blockwise-principal M4 result determines a successful public inference
result that is globally principal.  This is the premise-oriented companion
of `infer_success_principalResult`. -/
theorem infer_principalResult
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {principal : Ty}
    (principalTyping : PrincipalTyping signature context expression principal) :
    ∃ inferred,
      infer signature context expression = some inferred ∧
        PrincipalResult signature context expression inferred := by
  have reflexiveInstance : IsInstance principal principal :=
    ⟨Subst.id, Ty.apply_id principal⟩
  have sourceTyping : Typing signature context expression principal :=
    ⟨principal, principalTyping, reflexiveInstance⟩
  have succeeds : infer signature context expression ≠ none :=
    Typing.infer_isSome wellFormed sourceTyping
  cases result : infer signature context expression with
  | none => exact False.elim (succeeds result)
  | some inferred =>
      exact ⟨inferred, rfl,
        infer_success_principalResult wellFormed result⟩

/-- Principal M4 result types are unique up to finite renaming of ordinary
and capability variables. -/
theorem PrincipalTyping.finiteRenamingEq
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {left right : Ty}
    (leftPrincipal : PrincipalTyping signature context expression left)
    (rightPrincipal : PrincipalTyping signature context expression right) :
    FiniteRenamingEq left right :=
  PrincipalTyping.finiteRenamingEq_of_fullM4
    CompletenessArchitecture.fullM4Coherence wellFormed leftPrincipal
      rightPrincipal

end TypePM.Source.M4
