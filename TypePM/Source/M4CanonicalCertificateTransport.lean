import TypePM.Source.M5CompletionArchitecture

/-!
# Transport to the principal derivation recovered from public M4 inference

Public M4 inference returns only a type.  Its soundness theorem recovers a
proof-bearing principal derivation, chosen below once and named the canonical
derivation for that successful run.

The comparison theorem does not identify an arbitrary derivation with the
canonical derivation.  It retains `FullM2PairCoherence`, the existing relation
that records equal finishing supplies, a semantic comparison of the generated
blocks, and alignment of their absorbing principal closures.

The final boundary transports only closed runtime certificates.  Transport of
an arbitrary certificate family is not automatic: the caller must prove that
its family respects the explicit coherence and closure-alignment witnesses.
Open runtime contexts would additionally require transport of their type lists;
polymorphic contexts require a stronger context relation.  Neither extension is
claimed here.
-/

namespace TypePM.Source.M4

open TypePM.Source

/-- The proof-bearing principal derivation recovered from one successful run
of public M4 inference.  The definition is noncomputable only because public
inference returns a type rather than the derivation carried by its soundness
proof. -/
noncomputable def canonicalPrincipalTypingDerivation
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer signature context expression = some target) :
    PrincipalTypingDerivation signature context expression target :=
  Classical.choice (infer_success_principalTyping wellFormed success)

namespace PrincipalTypingDerivation

/-- Coherence and executable replay relate any independently selected
principal derivation to the derivation recovered from the successful public
inference run.  The full pair witness is retained because target-level mutual
instancehood alone loses the generated-block and closure information needed by
runtime certificates. -/
theorem coherentWithCanonical_of_coherence_and_replay
    (coherent : CompletenessArchitecture.FullM4Coherence)
    (replay : CompletenessArchitecture.FullM4ExecutableReplay)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {principal : Ty}
    (source :
      PrincipalTypingDerivation signature context expression principal) :
    ∃ inferred,
      ∃ success : infer signature context expression = some inferred,
        Nonempty
          (FullM2PairCoherence context.initialSupply source.next
            (canonicalPrincipalTypingDerivation wellFormed success).next
            source.generated
            (canonicalPrincipalTypingDerivation wellFormed success).generated
            context) := by
  have complete :
      CompletenessArchitecture.WellFormedM4ElaborationPrincipalityComplete :=
    CompletenessArchitecture.wellFormedM4ElaborationPrincipalityComplete_of_coherence_and_replay
      coherent replay
  have sourceTyping : Typing signature context expression principal :=
    ⟨principal, ⟨source⟩, Subst.id, Ty.apply_id principal⟩
  have succeeds : infer signature context expression ≠ none :=
    CompletenessArchitecture.Typing.infer_isSome_of_principalityComplete
      complete wellFormed sourceTyping
  have inferSuccess :
      ∃ inferred, infer signature context expression = some inferred := by
    cases result : infer signature context expression with
    | none => exact (succeeds result).elim
    | some inferred => exact ⟨inferred, rfl⟩
  obtain ⟨inferred, success⟩ := inferSuccess
  let canonical :=
    canonicalPrincipalTypingDerivation wellFormed success
  obtain ⟨pair⟩ := coherent expression wellFormed
    (Supply.wellFormedFor_initialSupply context)
    source.elaboration canonical.elaboration
  exact ⟨inferred, success, ⟨pair⟩⟩

/-- Completed M4 coherence and replay discharge the conditional comparison
theorem. -/
theorem coherentWithCanonical
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {principal : Ty}
    (source :
      PrincipalTypingDerivation signature context expression principal) :
    ∃ inferred,
      ∃ success : infer signature context expression = some inferred,
        Nonempty
          (FullM2PairCoherence context.initialSupply source.next
            (canonicalPrincipalTypingDerivation wellFormed success).next
            source.generated
            (canonicalPrincipalTypingDerivation wellFormed success).generated
            context) :=
  source.coherentWithCanonical_of_coherence_and_replay
    CompletenessArchitecture.fullM4Coherence
    CompletenessArchitecture.fullM4ExecutableReplay wellFormed

end PrincipalTypingDerivation

end TypePM.Source.M4

namespace TypePM.Source.ProvenancedFreshClosureAlignment

/-- Exact closure-target alignment lifted to the result types indexing the
two principal M4 derivations. -/
theorem principalTargets_exact
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {leftPrincipal rightPrincipal : Ty}
    (left : M4.PrincipalTypingDerivation signature context expression
      leftPrincipal)
    (right : M4.PrincipalTypingDerivation signature context expression
      rightPrincipal)
    (alignment : ProvenancedFreshClosureAlignment
      left.closure right.closure context left.next) :
    leftPrincipal.apply
        alignment.alignment.alignment.rho.substitution =
      rightPrincipal := by
  calc
    leftPrincipal.apply alignment.alignment.alignment.rho.substitution =
        left.closure.target.apply
          alignment.alignment.alignment.rho.substitution :=
      congrArg
        (fun target =>
          target.apply alignment.alignment.alignment.rho.substitution)
        left.target_eq
    _ = right.closure.target :=
      alignment.alignment.alignment.target_exact
    _ = rightPrincipal := right.target_eq.symm

/-- The same alignment makes the two derivation result types substitution
instances of one another. -/
theorem principalTargets_mutualInstances
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {leftPrincipal rightPrincipal : Ty}
    (left : M4.PrincipalTypingDerivation signature context expression
      leftPrincipal)
    (right : M4.PrincipalTypingDerivation signature context expression
      rightPrincipal)
    (alignment : ProvenancedFreshClosureAlignment
      left.closure right.closure context left.next) :
    IsInstance leftPrincipal rightPrincipal ∧
      IsInstance rightPrincipal leftPrincipal := by
  obtain ⟨forward, backward⟩ :=
    alignment.alignment.alignment.targets_mutualInstances
  constructor
  · obtain ⟨substitution, targetEquality⟩ := forward
    refine ⟨substitution, ?_⟩
    calc
      leftPrincipal.apply substitution =
          left.closure.target.apply substitution :=
        congrArg (fun target => target.apply substitution) left.target_eq
      _ = right.closure.target := targetEquality
      _ = rightPrincipal := right.target_eq.symm
  · obtain ⟨substitution, targetEquality⟩ := backward
    refine ⟨substitution, ?_⟩
    calc
      rightPrincipal.apply substitution =
          right.closure.target.apply substitution :=
        congrArg (fun target => target.apply substitution) right.target_eq
      _ = left.closure.target := targetEquality
      _ = leftPrincipal := left.target_eq.symm

end TypePM.Source.ProvenancedFreshClosureAlignment

namespace TypePM.Source.M5CompletionArchitecture

open TypePM.Source

/-- A closed runtime-certificate family respects M4 coherence when a full
generated-block comparison and its exact principal-closure alignment transport
the certificate between their endpoint derivations.  Both witnesses remain
explicit so a concrete family may use semantic block comparison as well as the
closed-context and target equalities stored by the alignment.

This is a required transport law, not an unconditional theorem about arbitrary
certificate families.  Both its source context and runtime type list are fixed
to `[]`; no open-context transport is hidden in this boundary. -/
def ClosedRuntimeCertificateRespectsCoherence
    (Certificate : RuntimeCertificateFamily) : Prop :=
  ∀ {signature : FrozenSignature} {expression : Expr}
      {leftPrincipal rightPrincipal : Ty}
      (left : M4.PrincipalTypingDerivation signature [] expression
        leftPrincipal)
      (right : M4.PrincipalTypingDerivation signature [] expression
        rightPrincipal)
      (_pair : FullM2PairCoherence (Context.initialSupply []) left.next
        right.next left.generated right.generated [])
      (_alignment : ProvenancedFreshClosureAlignment
        left.closure right.closure [] left.next),
    Certificate left [] → Certificate right []

private theorem isInstance_trans
    {first second third : Ty}
    (firstToSecond : IsInstance first second)
    (secondToThird : IsInstance second third) :
    IsInstance first third := by
  obtain ⟨firstSubstitution, firstEquality⟩ := firstToSecond
  obtain ⟨secondSubstitution, secondEquality⟩ := secondToThird
  refine ⟨Subst.compose secondSubstitution firstSubstitution, ?_⟩
  rw [← Ty.apply_compose, firstEquality, secondEquality]

/-- A coherence-respecting closed certificate on an arbitrary principal
derivation transports to the canonical public-inference derivation.  The
original instance witness is composed in the reverse coherence direction, so
the canonical principal type remains an instance source for the requested
typing result. -/
theorem closedCertificate_toCanonical_of_coherence_and_replay
    {Certificate : RuntimeCertificateFamily}
    (respects : ClosedRuntimeCertificateRespectsCoherence Certificate)
    (coherent : M4.CompletenessArchitecture.FullM4Coherence)
    (replay : M4.CompletenessArchitecture.FullM4ExecutableReplay)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {expression : Expr} {principal target : Ty}
    (source : M4.PrincipalTypingDerivation signature [] expression principal)
    (instantiation : IsInstance principal target)
    (certificate : Certificate source []) :
    ∃ inferred,
      ∃ success : M4.infer signature [] expression = some inferred,
        Certificate
            (M4.canonicalPrincipalTypingDerivation wellFormed success) [] ∧
          IsInstance inferred target := by
  obtain ⟨inferred, success, ⟨pair⟩⟩ :=
    source.coherentWithCanonical_of_coherence_and_replay
      coherent replay wellFormed
  let canonical :=
    M4.canonicalPrincipalTypingDerivation wellFormed success
  obtain ⟨alignment⟩ := pair.closureAlignment source.closure
    canonical.closure source.absorbing canonical.absorbing
  have canonicalCertificate : Certificate canonical [] :=
    respects source canonical pair alignment certificate
  have mutualInstances :=
    alignment.principalTargets_mutualInstances source canonical
  exact ⟨inferred, success, canonicalCertificate,
    isInstance_trans mutualInstances.2 instantiation⟩

/-- Completed M4 coherence and replay discharge the conditional closed
certificate transport theorem. -/
theorem closedCertificate_toCanonical
    {Certificate : RuntimeCertificateFamily}
    (respects : ClosedRuntimeCertificateRespectsCoherence Certificate)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {expression : Expr} {principal target : Ty}
    (source : M4.PrincipalTypingDerivation signature [] expression principal)
    (instantiation : IsInstance principal target)
    (certificate : Certificate source []) :
    ∃ inferred,
      ∃ success : M4.infer signature [] expression = some inferred,
        Certificate
            (M4.canonicalPrincipalTypingDerivation wellFormed success) [] ∧
          IsInstance inferred target :=
  closedCertificate_toCanonical_of_coherence_and_replay respects
    M4.CompletenessArchitecture.fullM4Coherence
    M4.CompletenessArchitecture.fullM4ExecutableReplay wellFormed source
      instantiation certificate

end TypePM.Source.M5CompletionArchitecture
