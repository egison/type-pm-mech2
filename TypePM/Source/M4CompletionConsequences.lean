import TypePM.Source.M4CompletenessArchitecture
import TypePM.RenamingUniqueness

/-!
# Public consequences of M4 completeness and coherence

This module keeps the user-facing consequences separate from the structural
coherence and replay developments.  Each theorem states exactly which of the
two completed architecture interfaces it consumes, so acceptance,
principality, and uniqueness do not need to be reproved after the remaining
constructor-local obligations are assembled.
-/

namespace TypePM.Source.M4

/-- An M4 source expression is typable when the independent declarative
relation assigns it at least one result type. -/
def Typable (signature : FrozenSignature) (context : Context)
    (expression : Expr) : Prop :=
  ∃ target, Typing signature context expression target

/-- All blockwise-principal M4 derivations of the same source expression have
mutually instantiable targets. -/
def PrincipalCoherence (signature : FrozenSignature) (context : Context)
    (expression : Expr) : Prop :=
  ∀ {left right},
    PrincipalTyping signature context expression left →
      PrincipalTyping signature context expression right →
        IsInstance left right ∧ IsInstance right left

/-- A result is globally principal when it is declaratively typable and every
other declarative result is its substitution instance. -/
def PrincipalResult (signature : FrozenSignature) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  Typing signature context expression target ∧
    ∀ other, Typing signature context expression other →
      IsInstance target other

private theorem isInstance_trans
    {first second third : Ty}
    (firstToSecond : IsInstance first second)
    (secondToThird : IsInstance second third) :
    IsInstance first third := by
  obtain ⟨firstSubstitution, firstEquality⟩ := firstToSecond
  obtain ⟨secondSubstitution, secondEquality⟩ := secondToThird
  refine ⟨Subst.compose secondSubstitution firstSubstitution, ?_⟩
  rw [← Ty.apply_compose, firstEquality, secondEquality]

/-- Fuel-level M4 coherence compares the targets selected by any two
blockwise-principal derivations. -/
theorem principalCoherence_of_fullM4
    (coherent : CompletenessArchitecture.FullM4Coherence)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    PrincipalCoherence signature context expression := by
  intro left right leftPrincipal rightPrincipal
  rcases leftPrincipal with
    ⟨⟨leftGenerated, leftNext, leftElaboration, leftClosure,
      leftAbsorbing, leftTarget⟩⟩
  rcases rightPrincipal with
    ⟨⟨rightGenerated, rightNext, rightElaboration, rightClosure,
      rightAbsorbing, rightTarget⟩⟩
  obtain ⟨pair⟩ := coherent expression wellFormed
    (Supply.wellFormedFor_initialSupply context) leftElaboration
      rightElaboration
  obtain ⟨leftToRight, rightToLeft⟩ :=
    pair.closureTargets_mutualInstances leftClosure rightClosure
      leftAbsorbing rightAbsorbing
  rw [leftTarget, rightTarget]
  exact ⟨leftToRight, rightToLeft⟩

/-- A successful public inference result is globally principal once full M4
coherence is available. -/
theorem infer_success_principalResult_of_fullM4
    (coherent : CompletenessArchitecture.FullM4Coherence)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer signature context expression = some target) :
    PrincipalResult signature context expression target := by
  refine ⟨infer_success_typing wellFormed success, ?_⟩
  intro other otherTyping
  obtain ⟨otherPrincipal, otherPrincipalTyping, principalToOther⟩ :=
    otherTyping
  have inferredToPrincipal :=
    (principalCoherence_of_fullM4 coherent wellFormed context expression
      (infer_success_principalTyping wellFormed success)
      otherPrincipalTyping).1
  exact isInstance_trans inferredToPrincipal principalToOther

/-- Any two blockwise-principal M4 results differ only by a finite renaming
of the ordinary and capability variables occurring in their targets. -/
theorem PrincipalTyping.finiteRenamingEq_of_fullM4
    (coherent : CompletenessArchitecture.FullM4Coherence)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {left right : Ty}
    (leftPrincipal : PrincipalTyping signature context expression left)
    (rightPrincipal : PrincipalTyping signature context expression right) :
    FiniteRenamingEq left right :=
  TypePM.finiteRenamingEq_of_mutualInstances
    (principalCoherence_of_fullM4 coherent wellFormed context expression
      leftPrincipal rightPrincipal)

/-- Under the completed per-derivation correspondence, public M4 inference
succeeds exactly for declaratively typable expressions. -/
theorem typable_iff_infer_isSome_of_principalityComplete
    (complete :
      CompletenessArchitecture.WellFormedM4ElaborationPrincipalityComplete)
    (signature : FrozenSignature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Typable signature context expression ↔
      infer signature context expression ≠ none := by
  constructor
  · rintro ⟨target, typing⟩
    exact CompletenessArchitecture.Typing.infer_isSome_of_principalityComplete
      complete wellFormed typing
  · intro succeeds
    cases success : infer signature context expression with
    | none => exact (succeeds success).elim
    | some target =>
        exact ⟨target, infer_success_typing wellFormed success⟩

/-- Declarative M4 typability is decided by the public inference function
once principality completeness has been assembled. -/
def typableDecidable_of_principalityComplete
    (complete :
      CompletenessArchitecture.WellFormedM4ElaborationPrincipalityComplete)
    (signature : FrozenSignature) (wellFormed : signature.WellFormed)
    (context : Context) (expression : Expr) :
    Decidable (Typable signature context expression) :=
  match success : infer signature context expression with
  | none => isFalse (by
      intro typable
      have succeeds :=
        (typable_iff_infer_isSome_of_principalityComplete complete signature
          wellFormed context expression).mp typable
      exact succeeds success)
  | some target =>
      isTrue ⟨target, infer_success_typing wellFormed success⟩

end TypePM.Source.M4
