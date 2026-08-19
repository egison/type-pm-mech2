import TypePM.Source.FullM2ConditionalCompletion
import TypePM.Source.FullM2GraphAliasPresentation

/-!
# Unconditional completion of M2 source coherence

The finite visible closure graph supplies the derivation-aware `letE`
assembly bridge.  Together with the already completed ordinary source
constructors and closure alignment, this closes full M2 coherence and the
freshness-scoped principality theorem.
-/

namespace TypePM.Source

/-- The source-derived visible graph discharges the complete supported
whole-`let` assembly bridge. -/
theorem fullM2LetSupportedAssemblyBridge :
    FullM2LetSupportedAssemblyBridge :=
  fullM2LetSupportedAssemblyBridge_of_graphAliasPresentation
    fullM2LetGraphAliasPresentationComplete

/-- Any two well-formed relational elaborations of the same M2 source
expression have the common supported semantic comparison. -/
theorem fullM2CoherenceComplete : FullM2Coherence :=
  fullM2Coherence_of_letSupportedAssemblyBridge
    fullM2LetSupportedAssemblyBridge

/-- Public M2 elaboration is complete and principal under the standard
well-formed starting-supply condition. -/
theorem wellFormedElaborationPrincipalityComplete :
    WellFormedElaborationPrincipalityComplete :=
  wellFormedElaborationPrincipalityComplete_of_letSupportedAssemblyBridge
    fullM2LetSupportedAssemblyBridge

/-- Every declaratively typed M2 source program is accepted by public
inference. -/
theorem Typing.infer_isSome
    {signature : Signature} {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing signature context expression target) :
    infer signature context expression ≠ none :=
  typing.infer_isSome_of_wellFormedElaborationPrincipalityComplete
    wellFormedElaborationPrincipalityComplete

namespace Inference

/-- For a well-formed signature, public M2 inference succeeds exactly on
declaratively typable source programs. -/
theorem typable_iff_infer_isSome
    (signature : Signature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Typable signature context expression ↔
      infer signature context expression ≠ none :=
  typable_iff_infer_isSome_of_wellFormedElaborationPrincipalityComplete
    wellFormedElaborationPrincipalityComplete signature wellFormed context
      expression

/-- Declarative M2 typability is decidable by public inference. -/
def typableDecidable
    (signature : Signature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Decidable (Typable signature context expression) :=
  typableDecidable_of_wellFormedElaborationPrincipalityComplete
    wellFormedElaborationPrincipalityComplete signature wellFormed context
      expression

/-- Every successful public M2 inference result is globally principal. -/
theorem infer_success_principalResult
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer signature context expression = some target) :
    PrincipalResult signature context expression target :=
  infer_success_principalResult_of_wellFormedElaborationPrincipalityComplete
    wellFormedElaborationPrincipalityComplete wellFormed success

/-- A blockwise-principal declarative result yields the globally principal
result returned by public M2 inference. -/
theorem infer_principalResult
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {principal : Ty}
    (principalTyping :
      PrincipalTyping signature context expression principal) :
    ∃ inferred,
      infer signature context expression = some inferred ∧
        PrincipalResult signature context expression inferred :=
  infer_principalResult_of_wellFormedElaborationPrincipalityComplete
    wellFormedElaborationPrincipalityComplete wellFormed principalTyping

end Inference

namespace PrincipalTyping

/-- Any two blockwise-principal M2 source results differ only by a finite
renaming of variables occurring in their targets. -/
theorem finiteRenamingEq
    {signature : Signature} {context : Context} {expression : Expr}
    {left right : Ty}
    (leftPrincipal : PrincipalTyping signature context expression left)
    (rightPrincipal : PrincipalTyping signature context expression right) :
    FiniteRenamingEq left right :=
  finiteRenamingEq_of_wellFormedElaborationPrincipalityComplete
    wellFormedElaborationPrincipalityComplete leftPrincipal rightPrincipal

end PrincipalTyping

end TypePM.Source
