import TypePM.Source.ElaborationCompleteness
import TypePM.RenamingUniqueness

/-!
# Global principality for scheme-aware source inference

The local `PrincipalTyping` witness records principal closure of every
constraint block.  The remaining global issue is coherence: different
choices of principal closures at nested `let` expressions must still give
mutually instantiable final types.  This file isolates that issue from the
public consequences of coherence.
-/

namespace TypePM.Source

/-- All blockwise-principal derivations of one source expression have
mutually instantiable targets. -/
def PrincipalCoherence (context : Context) (expression : Expr) : Prop :=
  ∀ {left right},
    PrincipalTyping context expression left →
      PrincipalTyping context expression right →
        IsInstance left right ∧ IsInstance right left

/-- A source type is globally principal when it is a typing and every other
source typing is its substitution instance. -/
def PrincipalResult
    (context : Context) (expression : Expr) (target : Ty) : Prop :=
  Typing context expression target ∧
    ∀ other, Typing context expression other → IsInstance target other

/-- One blockwise-principal witness agrees with the deterministic public
inference representative in both directions.  This is the narrow structural
statement that nested-`let` transport must establish. -/
def AgreesWithInference
    {context : Context} {expression : Expr} {target : Ty}
    (_typing : PrincipalTyping context expression target) : Prop :=
  ∃ inferred,
    infer context expression = some inferred ∧
      IsInstance inferred target ∧ IsInstance target inferred

private theorem isInstance_trans
    {first second third : Ty}
    (firstToSecond : IsInstance first second)
    (secondToThird : IsInstance second third) :
    IsInstance first third := by
  obtain ⟨firstSubstitution, firstEquality⟩ := firstToSecond
  obtain ⟨secondSubstitution, secondEquality⟩ := secondToThird
  refine ⟨Subst.compose secondSubstitution firstSubstitution, ?_⟩
  rw [← Ty.apply_compose, firstEquality, secondEquality]

/-- Agreement of every principal witness with executable inference implies
global source coherence.  Determinism of `infer` identifies the intermediate
representative used for the two witnesses. -/
theorem principalCoherence_of_inferenceAgreement
    {context : Context} {expression : Expr}
    (agreement : ∀ {target}
      (typing : PrincipalTyping context expression target),
        AgreesWithInference typing) :
    PrincipalCoherence context expression := by
  intro left right leftPrincipal rightPrincipal
  obtain ⟨leftInferred, leftSuccess, leftForward, leftBackward⟩ :=
    agreement leftPrincipal
  obtain ⟨rightInferred, rightSuccess, rightForward, rightBackward⟩ :=
    agreement rightPrincipal
  have inferredEquality : leftInferred = rightInferred := by
    rw [leftSuccess] at rightSuccess
    exact Option.some.inj rightSuccess
  subst rightInferred
  exact ⟨isInstance_trans leftBackward rightForward,
    isInstance_trans rightBackward leftForward⟩

/-- Let-free elaborations replay literally, so their only possible variation
comes from two principal closures of the same generated block. -/
theorem principalCoherence_of_letFree
    {context : Context} {expression : Expr}
    (letFree : LetFree expression) :
    PrincipalCoherence context expression := by
  intro left right leftPrincipal rightPrincipal
  rcases leftPrincipal with
    ⟨⟨leftGenerated, leftNext, leftElaboration, leftClosure,
      leftAbsorbing, leftTarget⟩⟩
  rcases rightPrincipal with
    ⟨⟨rightGenerated, rightNext, rightElaboration, rightClosure,
      rightAbsorbing, rightTarget⟩⟩
  have leftReplay := leftElaboration.replay_of_letFree letFree
  have rightReplay := rightElaboration.replay_of_letFree letFree
  rw [leftReplay] at rightReplay
  have pairEquality := Option.some.inj rightReplay
  injection pairEquality with generatedEquality nextEquality
  subst rightGenerated
  have closureInstances := leftClosure.targets_mutualInstances rightClosure
  rw [leftTarget, rightTarget]
  exact closureInstances

namespace PrincipalTyping

/-- Every let-free principal witness agrees mutually with the deterministic
public inference representative. -/
theorem agreesWithInference_of_letFree
    {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping context expression target)
    (letFree : LetFree expression) :
    AgreesWithInference principal := by
  have succeeds := principal.infer_isSome_of_letFree letFree
  cases success : infer context expression with
  | none => exact (succeeds success).elim
  | some inferred =>
      have instances := principalCoherence_of_letFree letFree
        (Inference.infer_success_principalTyping success) principal
      exact ⟨inferred, success, instances.1, instances.2⟩

end PrincipalTyping

namespace Inference

/-- The principal witness constructed directly from a successful executable
run agrees with that run by the identity substitution. -/
theorem infer_success_agreesWithInference
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer context expression = some target) :
    AgreesWithInference (infer_success_principalTyping success) := by
  exact ⟨target, success, ⟨Subst.id, by simp⟩, ⟨Subst.id, by simp⟩⟩

/-- Coherence turns a successful blockwise-principal inference result into a
type more general than every declarative source typing. -/
theorem infer_principal_of_coherence
    {context : Context} {expression : Expr} {principal target : Ty}
    (coherence : PrincipalCoherence context expression)
    (success : infer context expression = some principal)
    (typing : Typing context expression target) :
    IsInstance principal target := by
  obtain ⟨witness, witnessPrincipal, witnessToTarget⟩ := typing
  exact isInstance_trans
    (coherence (infer_success_principalTyping success) witnessPrincipal).1
    witnessToTarget

/-- Under source coherence, successful inference packages a globally
principal source result. -/
theorem infer_success_principalResult_of_coherence
    {context : Context} {expression : Expr} {target : Ty}
    (coherence : PrincipalCoherence context expression)
    (success : infer context expression = some target) :
    PrincipalResult context expression target := by
  exact ⟨infer_success_typing success,
    fun _ typing => infer_principal_of_coherence coherence success typing⟩

/-- Public inference is globally principal on the let-free source fragment. -/
theorem infer_success_principalResult_of_letFree
    {context : Context} {expression : Expr} {target : Ty}
    (letFree : LetFree expression)
    (success : infer context expression = some target) :
    PrincipalResult context expression target :=
  infer_success_principalResult_of_coherence
    (principalCoherence_of_letFree letFree) success

end Inference

namespace PrincipalTyping

/-- Coherence immediately compares two blockwise-principal witnesses. -/
theorem mutualInstances_of_coherence
    {context : Context} {expression : Expr} {left right : Ty}
    (coherence : PrincipalCoherence context expression)
    (leftPrincipal : PrincipalTyping context expression left)
    (rightPrincipal : PrincipalTyping context expression right) :
    IsInstance left right ∧ IsInstance right left :=
  coherence leftPrincipal rightPrincipal

/-- For the finite source type grammar, mutual instancehood strengthens to a
finite renaming of exactly the variables occurring in the two targets. -/
theorem finiteRenamingEq_of_coherence
    {context : Context} {expression : Expr} {left right : Ty}
    (coherence : PrincipalCoherence context expression)
    (leftPrincipal : PrincipalTyping context expression left)
    (rightPrincipal : PrincipalTyping context expression right) :
    FiniteRenamingEq left right :=
  TypePM.finiteRenamingEq_of_mutualInstances
    (coherence leftPrincipal rightPrincipal)

/-- Two blockwise-principal results for a let-free source expression differ
only by a finite renaming on their occurring variables. -/
theorem finiteRenamingEq_of_letFree
    {context : Context} {expression : Expr} {left right : Ty}
    (letFree : LetFree expression)
    (leftPrincipal : PrincipalTyping context expression left)
    (rightPrincipal : PrincipalTyping context expression right) :
    FiniteRenamingEq left right :=
  finiteRenamingEq_of_coherence
    (principalCoherence_of_letFree letFree)
    leftPrincipal rightPrincipal

end PrincipalTyping

end TypePM.Source
