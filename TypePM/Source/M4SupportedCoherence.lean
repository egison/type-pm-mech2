import TypePM.Source.M4SupplySupport

/-!
# Support-based closure upgrade for M4 coherence

The completed M2 closure-alignment construction does not inspect source
syntax.  Its actual inputs are a supported semantic comparison, a
well-formed starting supply, supply monotonicity, and a bound on the variables
of one generated block.  M4 proves the latter two facts directly, so this
module exposes the syntax-independent upgrade used by every M4 constructor.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source

/-- Constructor-compositional M4 coherence before adding the principal
closure alignment needed by an enclosing `let`. -/
def SupportedM4FuelPairProperty (expression : Expr) : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply} {leftFuel rightFuel : Nat},
    signature.WellFormed → start.WellFormedFor context →
      ElaboratesFuel signature leftFuel context expression start
          leftGenerated leftNext →
        ElaboratesFuel signature rightFuel context expression start
            rightGenerated rightNext →
          Nonempty (SupportedM2PairCoherence start leftNext rightNext
            leftGenerated rightGenerated)

/-- Add the future-fixing principal-closure alignment to a supported M4
comparison.  The M4 derivation supplies exactly the numeric support facts
required by the source-independent closure theorem. -/
theorem FullM2PairCoherence.ofM4Supported
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {start : Supply} {leftGenerated rightGenerated : Generated}
    {leftNext rightNext : Supply} {rightFuel : Nat}
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : start.WellFormedFor context)
    (rightElaboration : ElaboratesFuel signature rightFuel context expression
      start rightGenerated rightNext)
    (supported : SupportedM2PairCoherence start leftNext rightNext
      leftGenerated rightGenerated) :
    Nonempty (FullM2PairCoherence start leftNext rightNext
      leftGenerated rightGenerated context) := by
  cases supported.next_eq
  exact ⟨
    { next_eq := rfl
      certificate := supported.certificate
      closureAlignment := by
        intro leftClosure rightClosure leftAbsorbing rightAbsorbing
        exact supportedCertificateClosureAlignment_of_support wellFormed
          rightElaboration.supply_le_next
          ((rightElaboration.supportProvenance signatureWellFormed).below
            wellFormed rightElaboration.supply_le_next)
          supported.certificate leftClosure rightClosure
          leftAbsorbing rightAbsorbing }⟩

/-- A constructor-level supported proof automatically yields the full M4
fuel pair property. -/
theorem SupportedM4FuelPairProperty.toFull
    {expression : Expr} (supported : SupportedM4FuelPairProperty expression) :
    FullM4FuelPairProperty expression := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  obtain ⟨comparison⟩ := supported signatureWellFormed wellFormed
    leftElaboration rightElaboration
  exact FullM2PairCoherence.ofM4Supported signatureWellFormed wellFormed
    rightElaboration comparison

/-- Forget the principal-closure field while retaining the compositional
supported certificate. -/
theorem FullM4FuelPairProperty.toSupported
    {expression : Expr} (full : FullM4FuelPairProperty expression) :
    SupportedM4FuelPairProperty expression := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  obtain ⟨comparison⟩ := full signatureWellFormed wellFormed
    leftElaboration rightElaboration
  exact ⟨
    { next_eq := comparison.next_eq
      certificate := comparison.certificate }⟩

end TypePM.Source.M4.CompletenessArchitecture
