import TypePM.Source.Elaboration
import TypePM.Runtime.EvalFuel

/-!
# Runtime typing for the closed ground-product core

The complete source language does not yet have a proved runtime-typing
interpretation.  In particular, source signatures are not currently related
to the fixed primitive implementation, and `matchFirst` and pattern-function
atoms still have explicit `stuck` branches in the evaluator.

This module establishes the first honest state-erasure boundary: closed
integer expressions and recursively nested tuples.  The judgment is
declarative and syntax directed; it does not mention `evalFuel`, `stuck`, or a
fuel amount.  Runtime values use a separate judgment with the same type
index.  Later modules prove preservation and progress for this core.
-/

namespace TypePM.Runtime

mutual

/-- Declarative runtime typing for the currently certified value core. -/
inductive ValueTyping : Value → Ty → Prop where
  | int (value : Int) : ValueTyping (.int value) .int
  | tuple (items : ValueTypings values targets) :
      ValueTyping (.tuple values) (.prod targets)

/-- Pointwise runtime typing for sibling values. -/
inductive ValueTypings : List Value → List Ty → Prop where
  | nil : ValueTypings [] []
  | cons (head : ValueTyping value target)
      (tail : ValueTypings values targets) :
      ValueTypings (value :: values) (target :: targets)

end

/-- Runtime environments are typed pointwise in newest-first order.  The
closed core below uses the empty instance, but the definition fixes the
environment convention needed by later closure work. -/
inductive EnvironmentTyping : ValueEnvironment → List Ty → Prop where
  | nil : EnvironmentTyping [] []
  | cons (head : ValueTyping value target)
      (tail : EnvironmentTyping environment context) :
      EnvironmentTyping (value :: environment) (target :: context)

mutual

/-- The source fragment for which runtime typing is currently derived from
`Source.Typing`: integer literals and recursively nested tuples. -/
inductive RuntimeTyping : Source.Expr → Ty → Prop where
  | lit (value : Int) : RuntimeTyping (.lit value) .int
  | tuple (items : RuntimeTypings expressions targets) :
      RuntimeTyping (.tuple expressions) (.prod targets)

/-- Pointwise runtime typing for sibling source expressions. -/
inductive RuntimeTypings : List Source.Expr → List Ty → Prop where
  | nil : RuntimeTypings [] []
  | cons (head : RuntimeTyping expression target)
      (tail : RuntimeTypings expressions targets) :
      RuntimeTypings (expression :: expressions) (target :: targets)

end

/-- A source expression lies in the certified runtime core, without exposing
its uniquely determined type in the premise of public bridge theorems. -/
def RuntimeSupported (expression : Source.Expr) : Prop :=
  ∃ target, RuntimeTyping expression target

mutual

theorem RuntimeTyping.apply_eq
    (typing : RuntimeTyping expression target) (substitution : Subst) :
    target.apply substitution = target := by
  cases typing with
  | lit => rfl
  | tuple items => simp [Ty.apply, RuntimeTypings.applyList_eq items substitution]

theorem RuntimeTypings.applyList_eq
    (typing : RuntimeTypings expressions targets) (substitution : Subst) :
    Ty.applyList substitution targets = targets := by
  cases typing with
  | nil => rfl
  | cons head tail =>
      simp [Ty.applyList, head.apply_eq substitution,
        tail.applyList_eq substitution]

end

mutual

/-- Ground-product elaboration emits exactly its runtime type and no
constraints; it also consumes no fresh names. -/
theorem RuntimeTyping.elaboration_exact
    (typing : RuntimeTyping expression target)
    (elaboration : Source.Elaborates signature context expression supply
      generated next) :
    generated = ⟨target, [], []⟩ ∧ next = supply := by
  cases typing with
  | lit =>
      cases elaboration
      exact ⟨rfl, rfl⟩
  | tuple items =>
      cases elaboration with
      | tuple itemElaboration =>
          obtain ⟨generatedEq, nextEq⟩ :=
            items.elaborationItems_exact itemElaboration
          subst generatedEq
          subst nextEq
          exact ⟨rfl, rfl⟩

/-- List counterpart of `RuntimeTyping.elaboration_exact`. -/
theorem RuntimeTypings.elaborationItems_exact
    (typing : RuntimeTypings expressions targets)
    (elaboration : Source.ElaboratesItems signature context expressions supply
      generated next) :
    generated = ⟨targets, [], []⟩ ∧ next = supply := by
  cases typing with
  | nil =>
      cases elaboration
      exact ⟨rfl, rfl⟩
  | cons head tail =>
      cases elaboration with
      | cons headElaboration tailElaboration =>
          obtain ⟨headGeneratedEq, afterHeadEq⟩ :=
            head.elaboration_exact headElaboration
          subst headGeneratedEq
          subst afterHeadEq
          obtain ⟨tailGeneratedEq, nextEq⟩ :=
            tail.elaborationItems_exact tailElaboration
          subst tailGeneratedEq
          subst nextEq
          exact ⟨rfl, rfl⟩

end

end TypePM.Runtime

namespace TypePM.Source

namespace Typing

/-- **Theorem 5.6, certified core (state erasure).**  A declaratively typed,
closed source expression in the ground-product core has the corresponding
runtime typing.  The source type cannot be changed by the instance closure,
because this core contains no type variables.

The `RuntimeSupported` premise is the precise current boundary.  Removing it
requires runtime-compatible declaration typing plus closure, primitive,
conditional, matcher-state, and search preservation. -/
theorem toRuntimeTyping
    {signature : Signature} {expression : Expr} {target : Ty}
    (typing : Typing signature [] expression target)
    (supported : Runtime.RuntimeSupported expression) :
    Runtime.RuntimeTyping expression target := by
  rcases supported with ⟨runtimeTarget, runtimeTyping⟩
  rcases typing with ⟨principal, principalTyping, instantiation⟩
  rcases principalTyping with ⟨derivation⟩
  rcases derivation with
    ⟨generated, next, elaboration, closure, _absorbing, principalEq⟩
  obtain ⟨generatedEq, _nextEq⟩ :=
    runtimeTyping.elaboration_exact elaboration
  subst generated
  have closureTargetEq : closure.target = runtimeTarget := by
    exact runtimeTyping.apply_eq closure.substitution
  have principalRuntimeEq : principal = runtimeTarget :=
    principalEq.trans closureTargetEq
  rcases instantiation with ⟨substitution, instanceEq⟩
  rw [principalRuntimeEq, runtimeTyping.apply_eq substitution] at instanceEq
  subst target
  exact runtimeTyping

end Typing

end TypePM.Source
