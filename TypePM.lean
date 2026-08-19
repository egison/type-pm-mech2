import TypePM.Types
import TypePM.Syntax
import TypePM.Substitution
import TypePM.Checking
import TypePM.Typing
import TypePM.Fresh
import TypePM.Constraints
import TypePM.Generation
import TypePM.GenerationRelation
import TypePM.GenerationFreshness
import TypePM.FreeVars
import TypePM.Unification
import TypePM.UnificationCorrectness
import TypePM.UnificationTermination
import TypePM.Solver
import TypePM.SolverCertified
import TypePM.UnificationRegression
import TypePM.Resolution
import TypePM.ConversionPotential
import TypePM.Saturation
import TypePM.NoGuess
import TypePM.MGUEquivalence
import TypePM.SaturationUniqueness
import TypePM.Permutation
import TypePM.SourcePermutation
import TypePM.GenerationRenaming
import TypePM.ResolutionTransport
import TypePM.SaturationRenaming
import TypePM.BlockOrderInvariance
import TypePM.SaturationProcedure
import TypePM.SaturationProcedureCompleteness
import TypePM.Declarative
import TypePM.DeclarativeCoverage
import TypePM.InferenceProcedure
import TypePM.Inference
import TypePM.InferenceCompleteness
import TypePM.InferenceExactness
import TypePM.Principality
import TypePM.RenamingUniqueness
import TypePM.Regression
import TypePM.M1Examples
import TypePM.M1BoundaryRegression
import TypePM.BlockClosure
import TypePM.AbsorbingUnification
import TypePM.AbsorbingBlockClosure
import TypePM.Scheme
import TypePM.ContextInterface
import TypePM.ContextInterfaceRegression
import TypePM.SchemeTransport
import TypePM.GeneralizationTransport
import TypePM.BlockClosureTransport
import TypePM.Source.Syntax
import TypePM.Source.Elaboration
import TypePM.Source.M2Regression
import TypePM.AxiomAudit

/-!
# Type-PM

Independent mechanization of the new Type-PM design.  This root imports only
modules belonging to the new development.
-/
