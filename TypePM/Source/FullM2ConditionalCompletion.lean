import TypePM.Source.SupportedCertificateClosureAlignment
import TypePM.Source.FullM2Replay

/-!
# Final conditional M2 endpoints

This module factors the generic source induction, closure alignment, and
executable replay through the derivation-aware `FullM2LetAssemblyHandler` and
its supported-certificate bridge.  The source-derived construction of that
bridge is supplied by `FullM2Completion`.
-/

namespace TypePM.Source

/-- Any supported-certificate bridge closes full M2 coherence. -/
theorem fullM2Coherence_of_letSupportedAssemblyBridge
    (bridge : FullM2LetSupportedAssemblyBridge) :
    FullM2Coherence :=
  fullM2Coherence_of_supportedLetBridge
    supportedCertificateClosureAlignmentComplete bridge

/-- The same supported bridge closes freshness-safe principality
completeness. -/
theorem wellFormedElaborationPrincipalityComplete_of_letSupportedAssemblyBridge
    (bridge : FullM2LetSupportedAssemblyBridge) :
    WellFormedElaborationPrincipalityComplete :=
  wellFormedElaborationPrincipalityComplete_of_fullM2
    (fullM2Coherence_of_letSupportedAssemblyBridge bridge)

end TypePM.Source
