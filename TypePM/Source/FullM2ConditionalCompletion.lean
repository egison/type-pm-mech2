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

/-- The concrete generic closure theorem plus the already completed ordinary
step reduce full M2 to the derivation-aware `letE` assembly handler. -/
theorem fullM2Coherence_of_letAssemblyHandler
    (assemble : FullM2LetAssemblyHandler) :
    FullM2Coherence :=
  fullM2Coherence_of_letAssembly
    supportedCertificateClosureAlignmentComplete assemble

/-- Derivation-aware let assembly also yields the final freshness-safe
principality completeness theorem. -/
theorem wellFormedElaborationPrincipalityComplete_of_letAssemblyHandler
    (assemble : FullM2LetAssemblyHandler) :
    WellFormedElaborationPrincipalityComplete :=
  wellFormedElaborationPrincipalityComplete_of_fullM2
    (fullM2Coherence_of_letAssemblyHandler assemble)

end TypePM.Source
