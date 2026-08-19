import TypePM.Source.Syntax
import TypePM.AbsorbingBlockClosure
import TypePM.ContextInterface
import TypePM.SolverCertified

/-!
# Scheme-aware nested source elaboration

Ordinary constructors collect one constraint block just as in M1, while a
`letE` closes its right-hand-side block completely before generalizing its
blockwise-principal result.  The substitution effect on free variables of the outer
context is returned as hard interface equations.  No unsolved right-hand-side
obligation crosses the `letE` boundary.
-/

namespace TypePM.Source

namespace Supply

/-- Componentwise upper bound for the two independent fresh-name supplies. -/
def join (left right : Supply) : Supply :=
  ⟨max left.ty right.ty, max left.cap right.cap⟩

def nextTy (supply : Supply) (count : Nat) : Supply :=
  ⟨supply.ty + count, supply.cap⟩

end Supply

namespace Generated

/-- Hide a closed right-hand-side block and expose only its effects together
with the body block. -/
def fromLet
    (effects : List Equation) (body : Generated) : Generated :=
  { target := body.target
    hard := effects ++ body.hard
    pending := body.pending }

end Generated

mutual

/-- Executable scheme-aware elaboration.  `letE` invokes the certified M1
block closer on the generated right-hand side before elaborating the body. -/
def elaborate (context : Context) :
    Expr → Supply → Option (Generated × Supply)
  | .var index, supply => do
      let scheme ← context[index]?
      let instantiated := scheme.instantiate supply
      pure (⟨instantiated.1, [], []⟩, instantiated.2)
  | .lit _, supply =>
      some (⟨.int, [], []⟩, supply)
  | .something, supply =>
      some
        (⟨.matcher .any (.var ⟨supply.ty⟩), [], []⟩,
          supply.nextTy 1)
  | .lam body, supply => do
      let domain : Ty := .var ⟨supply.ty⟩
      let (generatedBody, next) ←
        elaborate (.mono domain :: context) body (supply.nextTy 1)
      pure
        (⟨.fn domain generatedBody.target,
          generatedBody.hard, generatedBody.pending⟩, next)
  | .app function argument, supply => do
      let (generatedFunction, afterFunction) ←
        elaborate context function supply
      let (generatedArgument, afterArgument) ←
        elaborate context argument afterFunction
      let domain : Ty := .var ⟨afterArgument.ty⟩
      let target : Ty := .var ⟨afterArgument.ty + 1⟩
      pure
        (⟨target,
          generatedFunction.hard ++ generatedArgument.hard ++
            [.ty generatedFunction.target (.fn domain target)],
          generatedFunction.pending ++ generatedArgument.pending ++
            [⟨generatedArgument.target, domain⟩]⟩,
          afterArgument.nextTy 2)
  | .tuple items, supply => do
      let (generatedItems, next) ← elaborateItems context items supply
      pure
        (⟨.prod generatedItems.targets,
          generatedItems.hard, generatedItems.pending⟩, next)
  | .letE value body, supply => do
      let (generatedValue, afterValue) ← elaborate context value supply
      let closedValue ← inferGeneratedUsing unify generatedValue
      let closedContext := context.applyFree closedValue.substitution
      let generalized := closedContext.generalize closedValue.target
      let bodySupply := afterValue.join closedContext.initialSupply
      let (generatedBody, next) ←
        elaborate (generalized :: closedContext) body bodySupply
      pure
        (Generated.fromLet
          (context.interfaceEquations closedValue.substitution) generatedBody,
          next)

/-- List counterpart of `elaborate`. -/
def elaborateItems (context : Context) :
    List Expr → Supply → Option (GeneratedItems × Supply)
  | [], supply => some (⟨[], [], []⟩, supply)
  | item :: items, supply => do
      let (generatedItem, afterItem) ← elaborate context item supply
      let (generatedItems, next) ←
        elaborateItems context items afterItem
      pure
        (⟨generatedItem.target :: generatedItems.targets,
          generatedItem.hard ++ generatedItems.hard,
          generatedItem.pending ++ generatedItems.pending⟩,
          next)

end

mutual

/-- Declarative scheme-aware elaboration.  Its `letE` constructor contains a
`PrincipalBlockClosure`, never a call to the executable inference function. -/
inductive Elaborates :
    Context → Expr → Supply → Generated → Supply → Prop where
  | var {context index supply scheme}
      (lookup : context[index]? = some scheme) :
      Elaborates context (.var index) supply
        ⟨(scheme.instantiate supply).1, [], []⟩
        (scheme.instantiate supply).2
  | lit {context value supply} :
      Elaborates context (.lit value) supply ⟨.int, [], []⟩ supply
  | something {context supply} :
      Elaborates context .something supply
        ⟨.matcher .any (.var ⟨supply.ty⟩), [], []⟩
        (supply.nextTy 1)
  | lam {context body supply generatedBody next} :
      Elaborates (.mono (.var ⟨supply.ty⟩) :: context) body
        (supply.nextTy 1) generatedBody next →
      Elaborates context (.lam body) supply
        ⟨.fn (.var ⟨supply.ty⟩) generatedBody.target,
          generatedBody.hard, generatedBody.pending⟩ next
  | app {context function argument supply generatedFunction afterFunction
      generatedArgument afterArgument} :
      Elaborates context function supply generatedFunction afterFunction →
      Elaborates context argument afterFunction generatedArgument
        afterArgument →
      Elaborates context (.app function argument) supply
        ⟨.var ⟨afterArgument.ty + 1⟩,
          generatedFunction.hard ++ generatedArgument.hard ++
            [.ty generatedFunction.target
              (.fn (.var ⟨afterArgument.ty⟩)
                (.var ⟨afterArgument.ty + 1⟩))],
          generatedFunction.pending ++ generatedArgument.pending ++
            [⟨generatedArgument.target, .var ⟨afterArgument.ty⟩⟩]⟩
        (afterArgument.nextTy 2)
  | tuple {context items supply generatedItems next} :
      ElaboratesItems context items supply generatedItems next →
      Elaborates context (.tuple items) supply
        ⟨.prod generatedItems.targets,
          generatedItems.hard, generatedItems.pending⟩ next
  | letE {context value body supply generatedValue afterValue
      generatedBody next}
      (valueElaboration :
        Elaborates context value supply generatedValue afterValue)
      (closure : PrincipalBlockClosure generatedValue)
      (absorbing : closure.Absorbing)
      (bodyElaboration :
        Elaborates
          ((context.applyFree closure.substitution).generalize closure.target ::
            context.applyFree closure.substitution)
          body
          (afterValue.join
            (context.applyFree closure.substitution).initialSupply)
          generatedBody next) :
      Elaborates context (.letE value body) supply
        (Generated.fromLet
          (context.interfaceEquations closure.substitution) generatedBody)
        next

/-- Relational elaboration for sibling lists. -/
inductive ElaboratesItems :
    Context → List Expr → Supply → GeneratedItems → Supply → Prop where
  | nil {context supply} :
      ElaboratesItems context [] supply ⟨[], [], []⟩ supply
  | cons {context item items supply generatedItem afterItem generatedItems next} :
      Elaborates context item supply generatedItem afterItem →
      ElaboratesItems context items afterItem generatedItems next →
      ElaboratesItems context (item :: items) supply
        ⟨generatedItem.target :: generatedItems.targets,
          generatedItem.hard ++ generatedItems.hard,
          generatedItem.pending ++ generatedItems.pending⟩ next

end

mutual

/-- Executable elaboration is sound for the independent relational judgment. -/
theorem elaborate_sound
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (success : elaborate context expression supply = some (generated, next)) :
    Elaborates context expression supply generated next := by
  cases expression with
  | var index =>
      cases lookup : context[index]? with
      | none => simp [elaborate, lookup] at success
      | some scheme =>
          have equality :
              (Generated.mk (scheme.instantiate supply).1 [] [],
                (scheme.instantiate supply).2) = (generated, next) :=
            Option.some.inj (by simpa [elaborate, lookup] using success)
          injection equality with generatedEquality nextEquality
          subst generated
          subst next
          exact .var lookup
  | lit value =>
      have equality :
          (Generated.mk .int [] [], supply) = (generated, next) :=
        Option.some.inj (by simpa [elaborate] using success)
      injection equality with generatedEquality nextEquality
      subst generated
      subst next
      exact .lit
  | something =>
      have equality :
          (Generated.mk (.matcher .any (.var ⟨supply.ty⟩)) [] [],
            supply.nextTy 1) = (generated, next) :=
        Option.some.inj (by simpa [elaborate] using success)
      injection equality with generatedEquality nextEquality
      subst generated
      subst next
      exact .something
  | lam body =>
      cases bodyResult : elaborate
          (.mono (.var ⟨supply.ty⟩) :: context) body (supply.nextTy 1) with
      | none => simp [elaborate, bodyResult] at success
      | some result =>
          cases result with
          | mk generatedBody afterBody =>
              have equality :
                  (Generated.mk
                      (.fn (.var ⟨supply.ty⟩) generatedBody.target)
                      generatedBody.hard generatedBody.pending,
                    afterBody) = (generated, next) :=
                Option.some.inj
                  (by simpa [elaborate, bodyResult] using success)
              injection equality with generatedEquality nextEquality
              subst generated
              subst next
              exact .lam (elaborate_sound bodyResult)
  | app function argument =>
      cases functionResult : elaborate context function supply with
      | none => simp [elaborate, functionResult] at success
      | some functionOutput =>
          cases functionOutput with
          | mk generatedFunction afterFunction =>
              cases argumentResult :
                  elaborate context argument afterFunction with
              | none => simp [elaborate, functionResult, argumentResult] at success
              | some argumentOutput =>
                  cases argumentOutput with
                  | mk generatedArgument afterArgument =>
                      have equality :
                          (Generated.mk (.var ⟨afterArgument.ty + 1⟩)
                              (generatedFunction.hard ++
                                generatedArgument.hard ++
                                [.ty generatedFunction.target
                                  (.fn (.var ⟨afterArgument.ty⟩)
                                    (.var ⟨afterArgument.ty + 1⟩))])
                              (generatedFunction.pending ++
                                generatedArgument.pending ++
                                [⟨generatedArgument.target,
                                  .var ⟨afterArgument.ty⟩⟩]),
                            afterArgument.nextTy 2) = (generated, next) :=
                        Option.some.inj (by
                          simpa [elaborate, functionResult, argumentResult]
                            using success)
                      injection equality with generatedEquality nextEquality
                      subst generated
                      subst next
                      exact .app
                        (elaborate_sound functionResult)
                        (elaborate_sound argumentResult)
  | tuple items =>
      cases itemsResult : elaborateItems context items supply with
      | none => simp [elaborate, itemsResult] at success
      | some output =>
          cases output with
          | mk generatedItems afterItems =>
              have equality :
                  (Generated.mk (.prod generatedItems.targets)
                      generatedItems.hard generatedItems.pending,
                    afterItems) = (generated, next) :=
                Option.some.inj
                  (by simpa [elaborate, itemsResult] using success)
              injection equality with generatedEquality nextEquality
              subst generated
              subst next
              exact .tuple (elaborateItems_sound itemsResult)
  | letE value body =>
      cases valueResult : elaborate context value supply with
      | none => simp [elaborate, valueResult] at success
      | some valueOutput =>
          cases valueOutput with
          | mk generatedValue afterValue =>
              cases closureResult : inferGeneratedUsing unify generatedValue with
              | none => simp [elaborate, valueResult, closureResult] at success
              | some closedValue =>
                  let closedContext :=
                    context.applyFree closedValue.substitution
                  let generalized :=
                    closedContext.generalize closedValue.target
                  let bodySupply := afterValue.join closedContext.initialSupply
                  cases bodyResult : elaborate
                      (generalized :: closedContext) body bodySupply with
                  | none =>
                      simp [elaborate, valueResult, closureResult,
                        closedContext, generalized, bodySupply, bodyResult]
                        at success
                  | some bodyOutput =>
                      cases bodyOutput with
                      | mk generatedBody afterBody =>
                          have equality :
                              (Generated.fromLet
                                  (context.interfaceEquations
                                    closedValue.substitution)
                                  generatedBody,
                                afterBody) = (generated, next) :=
                            Option.some.inj (by
                              simpa [elaborate, valueResult, closureResult,
                                closedContext, generalized, bodySupply,
                                bodyResult] using success)
                          injection equality with generatedEquality nextEquality
                          subst generated
                          subst next
                          obtain ⟨closure, substitutionEquality,
                              targetEquality, absorbing⟩ :=
                            inferGeneratedUsing_absorbingPrincipalBlockClosure
                              unify_absorbingMGUSolver closureResult
                          have bodyResult' :
                              elaborate
                                ((Context.generalize
                                    (context.applyFree closure.substitution)
                                    closure.target) ::
                                  context.applyFree closure.substitution)
                                body
                                (afterValue.join
                                  (Context.initialSupply
                                    (context.applyFree
                                      closure.substitution))) =
                                some (generatedBody, afterBody) := by
                            simpa [closedContext, generalized, bodySupply,
                              substitutionEquality, targetEquality] using
                              bodyResult
                          simpa [substitutionEquality] using
                            (Elaborates.letE
                              (elaborate_sound valueResult) closure absorbing
                              (elaborate_sound bodyResult'))

/-- Executable list elaboration is sound. -/
theorem elaborateItems_sound
    {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (success : elaborateItems context expressions supply =
      some (generated, next)) :
    ElaboratesItems context expressions supply generated next := by
  cases expressions with
  | nil =>
      have equality :
          (GeneratedItems.mk [] [] [], supply) = (generated, next) :=
        Option.some.inj (by simpa [elaborateItems] using success)
      injection equality with generatedEquality nextEquality
      subst generated
      subst next
      exact .nil
  | cons item items =>
      cases itemResult : elaborate context item supply with
      | none => simp [elaborateItems, itemResult] at success
      | some itemOutput =>
          cases itemOutput with
          | mk generatedItem afterItem =>
              cases itemsResult : elaborateItems context items afterItem with
              | none =>
                  simp [elaborateItems, itemResult, itemsResult] at success
              | some itemsOutput =>
                  cases itemsOutput with
                  | mk generatedItems afterItems =>
                      have equality :
                          (GeneratedItems.mk
                              (generatedItem.target :: generatedItems.targets)
                              (generatedItem.hard ++ generatedItems.hard)
                              (generatedItem.pending ++ generatedItems.pending),
                            afterItems) = (generated, next) :=
                        Option.some.inj (by
                          simpa [elaborateItems, itemResult, itemsResult]
                            using success)
                      injection equality with generatedEquality nextEquality
                      subst generated
                      subst next
                      exact .cons
                        (elaborate_sound itemResult)
                        (elaborateItems_sound itemsResult)

end

/-- Elaborate a complete source expression above all names in its scheme
context. -/
def elaborateRoot (context : Context) (expression : Expr) :
    Option Generated :=
  (elaborate context expression context.initialSupply).map Prod.fst

/-- Public executable M2 inference skeleton. -/
def infer (context : Context) (expression : Expr) : Option Ty := do
  let generated ← elaborateRoot context expression
  let closed ← inferGeneratedUsing unify generated
  pure closed.target

/-- Independent evidence for one blockwise-principal result of a complete
source expression.  Nested `letE` right-hand sides are already hidden behind
the `PrincipalBlockClosure` witnesses inside `Elaborates`.  Global source
principality requires a separate coherence theorem between such witnesses. -/
structure PrincipalTypingDerivation
    (context : Context) (expression : Expr) (target : Ty) where
  generated : Generated
  next : Supply
  elaboration :
    Elaborates context expression context.initialSupply generated next
  closure : PrincipalBlockClosure generated
  absorbing : closure.Absorbing
  target_eq : target = closure.target

/-- The source expression has the indicated blockwise-principal result
according to the declarative elaboration and closure relations. -/
def PrincipalTyping
    (context : Context) (expression : Expr) (target : Ty) : Prop :=
  Nonempty (PrincipalTypingDerivation context expression target)

/-- Declarative source typing is the substitution-instance closure of a
blockwise-principal source elaboration witness.  This keeps arbitrary result types independent
of the executable representative selected by `infer`. -/
def Typing (context : Context) (expression : Expr) (target : Ty) : Prop :=
  ∃ principal,
    PrincipalTyping context expression principal ∧
      IsInstance principal target

namespace PrincipalTyping

/-- A blockwise-principal source result is itself a declarative source typing. -/
theorem toTyping
    {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping context expression target) :
    Typing context expression target := by
  exact ⟨target, principal, Subst.id, by simp⟩

/-- Every substitution instance of a fixed principal derivation is a source
typing.  This is the representative-local principality fact available before
different nested-closure representatives have been aligned. -/
theorem instance_typing
    {context : Context} {expression : Expr} {principal target : Ty}
    (principalTyping : PrincipalTyping context expression principal)
    (instantiation : IsInstance principal target) :
    Typing context expression target :=
  ⟨principal, principalTyping, instantiation⟩

end PrincipalTyping

namespace Inference

/-- Soundness of the executable M2 skeleton: a returned source type has an
independent relational elaboration and an absorbing block closure. -/
theorem infer_success_principalTyping
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer context expression = some target) :
    PrincipalTyping context expression target := by
  unfold infer at success
  cases elaborated : elaborate context expression context.initialSupply with
  | none => simp [elaborateRoot, elaborated] at success
  | some output =>
      cases output with
      | mk generated next =>
          simp only [elaborateRoot, elaborated, Option.map_some] at success
          change
            (inferGeneratedUsing unify generated).bind
              (fun closed => some closed.target) = some target at success
          cases closedResult : inferGeneratedUsing unify generated with
          | none => simp [closedResult] at success
          | some result =>
              simp only [closedResult, Option.bind_some,
                Option.some.injEq] at success
              subst target
              obtain ⟨closure, _, targetEquality, absorbing⟩ :=
                inferGeneratedUsing_absorbingPrincipalBlockClosure
                  unify_absorbingMGUSolver closedResult
              exact ⟨
                { generated := generated
                  next := next
                  elaboration := elaborate_sound elaborated
                  closure := closure
                  absorbing := absorbing
                  target_eq := targetEquality }⟩

/-- Public M2 inference soundness for the instance-closed declarative
`Typing` relation. -/
theorem infer_success_typing
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer context expression = some target) :
    Typing context expression target :=
  (infer_success_principalTyping success).toTyping

end Inference

end TypePM.Source
