import TypePM.GeneratedStableSemanticAcceptance
import TypePM.Source.DirectLetComparison

/-!
# Branch-stable acceptance transport for source blocks

This module exposes the branch-stable characterization at the generated-block
relations used by M2.  Literal hard-equation equivalence plus identical
pending obligations is handled directly in the core module.  Source closure
representatives can also rename pending obligations, so their sufficient
transport invariant is the existing renaming-aware common core: one finite
renaming acts on hard and pending constraints together, and admissible fresh
aliases account for representative-sensitive interface equations.
-/

namespace TypePM.Source

private theorem exists_stableSemanticSolution_iff_of_blockAccepts_iff
    {left right : TypePM.Generated}
    (equivalent : BlockAccepts left ↔ BlockAccepts right) :
    (∃ witness : left.StableSemanticWitness,
        left.StableSemanticSolution witness) ↔
      ∃ witness : right.StableSemanticWitness,
        right.StableSemanticSolution witness := by
  rw [← left.blockAccepts_iff_exists_stableSemanticSolution,
    ← right.blockAccepts_iff_exists_stableSemanticSolution]
  exact equivalent

namespace ElaborationRenaming.Generated.RenamedBy

/-- Exact two-sort renaming preserves and reflects existence of a
branch-stable semantic solution. -/
theorem exists_stableSemanticSolution_iff
    {rho : VariableRenaming} {left right : TypePM.Generated}
    (related : ElaborationRenaming.Generated.RenamedBy rho left right) :
    (∃ witness : left.StableSemanticWitness,
        left.StableSemanticSolution witness) ↔
      ∃ witness : right.StableSemanticWitness,
        right.StableSemanticSolution witness :=
  exists_stableSemanticSolution_iff_of_blockAccepts_iff
    related.blockAccepts_iff

end ElaborationRenaming.Generated.RenamedBy

namespace DirectGeneratedComparisonCertificate

namespace RenamingAwareCommonCoreEquivalent

/-- A finite renaming of the complete block followed by admissible fresh
hard aliases transports branch-stable semantic acceptance. -/
theorem exists_stableSemanticSolution_iff
    {left right : TypePM.Generated}
    (equivalent : RenamingAwareCommonCoreEquivalent left right) :
    (∃ witness : left.StableSemanticWitness,
        left.StableSemanticSolution witness) ↔
      ∃ witness : right.StableSemanticWitness,
        right.StableSemanticSolution witness :=
  exists_stableSemanticSolution_iff_of_blockAccepts_iff
    equivalent.blockAccepts_iff

end RenamingAwareCommonCoreEquivalent

end DirectGeneratedComparisonCertificate

namespace ElaborationRenaming

/-- Branch-stable form of the general-pending interface endpoint.  The
`interfaceDifference` premise is the additional invariant required when two
principal closure representatives expose different literal interface
equations. -/
theorem fromLet_otherClosure_exists_stableSemanticSolution_iff_of_freshAliasSequence
    {valueGenerated : TypePM.Generated}
    (rho : VariableRenaming)
    (left : PrincipalBlockClosure valueGenerated)
    (right : PrincipalBlockClosure (renameGenerated rho valueGenerated))
    (context : Context) (body : TypePM.Generated)
    (interfaceDifference : FreshAliasSequence.CommonCoreEquivalent
      (TypePM.Source.Generated.fromLet
        ((renameContext rho context).interfaceEquations
          (renameClosure rho left).substitution)
        (renameGenerated rho body))
      (TypePM.Source.Generated.fromLet
        ((renameContext rho context).interfaceEquations right.substitution)
        (renameGenerated rho body))) :
    (∃ witness :
          (TypePM.Source.Generated.fromLet
            ((renameContext rho context).interfaceEquations
              (renameClosure rho left).substitution)
            (renameGenerated rho body)).StableSemanticWitness,
        (TypePM.Source.Generated.fromLet
          ((renameContext rho context).interfaceEquations
            (renameClosure rho left).substitution)
          (renameGenerated rho body)).StableSemanticSolution witness) ↔
      ∃ witness :
          (TypePM.Source.Generated.fromLet
            ((renameContext rho context).interfaceEquations right.substitution)
            (renameGenerated rho body)).StableSemanticWitness,
        (TypePM.Source.Generated.fromLet
          ((renameContext rho context).interfaceEquations right.substitution)
          (renameGenerated rho body)).StableSemanticSolution witness :=
  exists_stableSemanticSolution_iff_of_blockAccepts_iff
    (fromLet_otherClosure_blockAccepts_iff_of_freshAliasSequence
      rho left right context body interfaceDifference)

end ElaborationRenaming

end TypePM.Source
