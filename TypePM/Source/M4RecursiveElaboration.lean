import TypePM.Source.M4FixTyping
import TypePM.Source.M4MatcherTyping
import TypePM.Source.M4MatchFirstTyping

/-!
# Complete recursive M4 source elaboration

Every expression-valued position in the final source syntax is routed back
through the same elaborator.  The internal fuel is fixed from the syntax
complexity by the public entry point and exists only to make the higher-order
callback recursion structurally evident to Lean.
-/

namespace TypePM.Source.M4

open TypePM.Source

abbrev ExpressionElaborator :=
  Context → Expr → Supply → Option (Generated × Supply)

def elaborateItemsUsing (elaborateExpression : ExpressionElaborator)
    (context : Context) :
    List Expr → Supply → Option (GeneratedItems × Supply)
  | [], supply => some (⟨[], [], []⟩, supply)
  | item :: items, supply => do
      let (generatedItem, afterItem) ← elaborateExpression context item supply
      let (generatedItems, next) ←
        elaborateItemsUsing elaborateExpression context items afterItem
      pure (⟨generatedItem.target :: generatedItems.targets,
        generatedItem.hard ++ generatedItems.hard,
        generatedItem.pending ++ generatedItems.pending⟩, next)

def elaborateCallUsing (elaborateExpression : ExpressionElaborator)
    (context : Context) : Generated → List Expr → Supply →
      Option (Generated × Supply)
  | accumulated, [], supply => some (accumulated, supply)
  | accumulated, argument :: arguments, supply => do
      let (generatedArgument, afterArgument) ←
        elaborateExpression context argument supply
      let domain : Ty := .var ⟨afterArgument.ty⟩
      let target : Ty := .var ⟨afterArgument.ty + 1⟩
      elaborateCallUsing elaborateExpression context
        (Generated.fromApp accumulated generatedArgument domain target)
        arguments (afterArgument.nextTy 2)

/-- Fuel-indexed implementation.  Each source-expression edge consumes one
unit; sibling-list traversal does not. -/
def elaborateFuel (signature : FrozenSignature) :
    Nat → Context → Expr → Supply → Option (Generated × Supply)
  | 0, _, _, _ => none
  | fuel + 1, context, expression, supply =>
      let recur : ExpressionElaborator := elaborateFuel signature fuel
      match expression with
      | .var index => do
          let scheme ← context[index]?
          let instantiated := scheme.instantiate supply
          pure (⟨instantiated.1, [], []⟩, instantiated.2)
      | .lit _ => some (⟨.int, [], []⟩, supply)
      | .something => some
          (⟨.matcher .any (.var ⟨supply.ty⟩), [], []⟩, supply.nextTy 1)
      | .lam body => do
          let domain : Ty := .var ⟨supply.ty⟩
          let (generatedBody, next) ←
            recur (.mono domain :: context) body (supply.nextTy 1)
          pure (Generated.fromLam domain generatedBody, next)
      | .app function argument => do
          let (generatedFunction, afterFunction) ← recur context function supply
          let (generatedArgument, afterArgument) ←
            recur context argument afterFunction
          pure (Generated.fromApp generatedFunction generatedArgument
            (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩),
            afterArgument.nextTy 2)
      | .tuple items => do
          let (generatedItems, next) ← elaborateItemsUsing recur context items supply
          pure (⟨.prod generatedItems.targets, generatedItems.hard,
            generatedItems.pending⟩, next)
      | .letE value body => do
          let (generatedValue, afterValue) ← recur context value supply
          let closedValue ← inferGeneratedUsing unify generatedValue
          let closedContext := context.applyFree closedValue.substitution
          let generalized := closedContext.generalize closedValue.target
          let bodySupply := afterValue.join closedContext.initialSupply
          let (generatedBody, next) ←
            recur (generalized :: closedContext) body bodySupply
          pure (Generated.fromLet
            (context.interfaceEquations closedValue.substitution) generatedBody,
            next)
      | .ctor constructor arguments => do
          let scheme ← signature.base.lookupDataConstructor constructor
          if arguments.length = scheme.callArity then
            let instantiated := scheme.instantiate supply
            elaborateCallUsing recur context ⟨instantiated.1, [], []⟩ arguments
              instantiated.2
          else none
      | .prim operation arguments => do
          let scheme ← signature.base.lookupPrimitive operation
          if arguments.length = scheme.callArity then
            let instantiated := scheme.instantiate supply
            elaborateCallUsing recur context ⟨instantiated.1, [], []⟩ arguments
              instantiated.2
          else none
      | .ifE condition thenBranch elseBranch =>
          let instantiated := conditionalScheme.instantiate supply
          elaborateCallUsing recur context ⟨instantiated.1, [], []⟩
            [condition, thenBranch, elseBranch] instantiated.2
      | .fixE body => elaborateFixUsing recur context body supply
      | .matcher clauses =>
          MatcherTyping.elaborateMatcherLiteralUsing recur signature context
            clauses supply
      | .matchAll target matcher pattern body =>
          elaborateMatchAllUsing recur signature context target matcher pattern
            body supply
      | .matchFirst target matcher arms =>
          MatchFirstTyping.elaborateUsing recur signature context target matcher
            arms supply

/-- Public full-syntax elaborator. -/
def elaborate (signature : FrozenSignature) (context : Context)
    (expression : Expr) (supply : Supply) : Option (Generated × Supply) :=
  elaborateFuel signature (expression.complexity + 1) context expression supply

/-- Public full-syntax inference. -/
def infer (signature : FrozenSignature) (context : Context)
    (expression : Expr) : Option Ty := do
  let (generated, _) ← elaborate signature context expression context.initialSupply
  let closed ← inferGeneratedUsing unify generated
  pure closed.target

inductive ItemsElaborateUsing
    (ExpressionElaborates : Context → Expr → Supply → Generated → Supply → Prop)
    (context : Context) : List Expr → Supply → GeneratedItems → Supply → Prop where
  | nil {supply} : ItemsElaborateUsing ExpressionElaborates context [] supply
      ⟨[], [], []⟩ supply
  | cons {item items supply generatedItem afterItem generatedItems next}
      (head : ExpressionElaborates context item supply generatedItem afterItem)
      (tail : ItemsElaborateUsing ExpressionElaborates context items afterItem
        generatedItems next) :
      ItemsElaborateUsing ExpressionElaborates context (item :: items) supply
        ⟨generatedItem.target :: generatedItems.targets,
          generatedItem.hard ++ generatedItems.hard,
          generatedItem.pending ++ generatedItems.pending⟩ next

inductive CallElaboratesUsing
    (ExpressionElaborates : Context → Expr → Supply → Generated → Supply → Prop)
    (context : Context) : Generated → List Expr → Supply → Generated → Supply → Prop where
  | nil {accumulated supply} : CallElaboratesUsing ExpressionElaborates context
      accumulated [] supply accumulated supply
  | cons {accumulated argument arguments supply generatedArgument afterArgument
      generated next}
      (head : ExpressionElaborates context argument supply generatedArgument
        afterArgument)
      (tail : CallElaboratesUsing ExpressionElaborates context
        (Generated.fromApp accumulated generatedArgument
          (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
        arguments (afterArgument.nextTy 2) generated next) :
      CallElaboratesUsing ExpressionElaborates context accumulated
        (argument :: arguments) supply generated next

/-- Fuel-indexed independent relation.  It mentions only source lookups,
constraint constructors, solver certificates, and the component relations. -/
def ElaboratesFuel (signature : FrozenSignature) :
    Nat → Context → Expr → Supply → Generated → Supply → Prop
  | 0, _, _, _, _, _ => False
  | fuel + 1, context, expression, supply, generated, next =>
      let recur := ElaboratesFuel signature fuel
      match expression with
      | .var index => ∃ scheme, context[index]? = some scheme ∧
          generated = ⟨(scheme.instantiate supply).1, [], []⟩ ∧
          next = (scheme.instantiate supply).2
      | .lit _ => generated = ⟨.int, [], []⟩ ∧ next = supply
      | .something => generated =
          ⟨.matcher .any (.var ⟨supply.ty⟩), [], []⟩ ∧
          next = supply.nextTy 1
      | .lam body => ∃ generatedBody, recur
          (.mono (.var ⟨supply.ty⟩) :: context) body (supply.nextTy 1)
            generatedBody next ∧
          generated = Generated.fromLam (.var ⟨supply.ty⟩) generatedBody
      | .app function argument => ∃ generatedFunction afterFunction
          generatedArgument afterArgument,
          recur context function supply generatedFunction afterFunction ∧
          recur context argument afterFunction generatedArgument afterArgument ∧
          generated = Generated.fromApp generatedFunction generatedArgument
            (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩) ∧
          next = afterArgument.nextTy 2
      | .tuple items => ∃ generatedItems,
          ItemsElaborateUsing recur context items supply generatedItems next ∧
          generated = ⟨.prod generatedItems.targets, generatedItems.hard,
            generatedItems.pending⟩
      | .letE value body => ∃ generatedValue afterValue,
          recur context value supply generatedValue afterValue ∧
          ∃ closure : PrincipalBlockClosure generatedValue,
            ∃ generatedBody,
            closure.Absorbing ∧
            recur ((context.applyFree closure.substitution).generalize
                closure.target :: context.applyFree closure.substitution) body
              (afterValue.join
                (context.applyFree closure.substitution).initialSupply)
              generatedBody next ∧
            generated = Generated.fromLet
              (context.interfaceEquations closure.substitution) generatedBody
      | .ctor constructor arguments => ∃ scheme,
          signature.base.lookupDataConstructor constructor = some scheme ∧
          arguments.length = scheme.callArity ∧ scheme.Closed ∧
          CallElaboratesUsing recur context ⟨(scheme.instantiate supply).1,
            [], []⟩ arguments (scheme.instantiate supply).2 generated next
      | .prim operation arguments => ∃ scheme,
          signature.base.lookupPrimitive operation = some scheme ∧
          arguments.length = scheme.callArity ∧ scheme.Closed ∧
          CallElaboratesUsing recur context ⟨(scheme.instantiate supply).1,
            [], []⟩ arguments (scheme.instantiate supply).2 generated next
      | .ifE condition thenBranch elseBranch =>
          CallElaboratesUsing recur context
            ⟨(conditionalScheme.instantiate supply).1, [], []⟩
            [condition, thenBranch, elseBranch]
            (conditionalScheme.instantiate supply).2 generated next
      | .fixE body => FixElaboratesUsing recur context (.fixE body) supply
          generated next
      | .matcher clauses => MatcherTyping.MatcherLiteralElaboratesUsing recur
          MatcherTyping.PPatElaborates MatcherTyping.DPatElaborates
          signature context clauses supply
          generated next
      | .matchAll target matcher pattern body =>
          MatchAllElaboratesUsing recur signature context target matcher pattern
            body supply generated next
      | .matchFirst target matcher arms =>
          MatchFirstTyping.ElaboratesUsing recur signature context
            (.matchFirst target matcher arms) supply generated next

/-- Public declarative elaboration hides the structural fuel witness. -/
def Elaborates (signature : FrozenSignature) (context : Context)
    (expression : Expr) (supply : Supply) (generated : Generated)
    (next : Supply) : Prop :=
  ∃ fuel, ElaboratesFuel signature fuel context expression supply generated next

theorem elaborateItemsUsing_sound
    {elaborateExpression : ExpressionElaborator}
    {ExpressionElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {context items supply generated next}
    (success : elaborateItemsUsing elaborateExpression context items supply =
      some (generated, next)) :
    ItemsElaborateUsing ExpressionElaborates context items supply generated next := by
  induction items generalizing supply generated with
  | nil =>
      simp [elaborateItemsUsing] at success
      rcases success with ⟨rfl, rfl⟩
      exact .nil
  | cons item items induction =>
      cases headResult : elaborateExpression context item supply with
      | none => simp [elaborateItemsUsing, headResult] at success
      | some output =>
          rcases output with ⟨generatedItem, afterItem⟩
          cases tailResult : elaborateItemsUsing elaborateExpression context items
              afterItem with
          | none => simp [elaborateItemsUsing, headResult, tailResult] at success
          | some output =>
              rcases output with ⟨generatedItems, afterItems⟩
              simp [elaborateItemsUsing, headResult, tailResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .cons (expressionSound headResult) (induction tailResult)

theorem elaborateCallUsing_sound
    {elaborateExpression : ExpressionElaborator}
    {ExpressionElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {context accumulated arguments supply generated next}
    (success : elaborateCallUsing elaborateExpression context accumulated
      arguments supply = some (generated, next)) :
    CallElaboratesUsing ExpressionElaborates context accumulated arguments supply
      generated next := by
  induction arguments generalizing accumulated supply generated with
  | nil =>
      simp [elaborateCallUsing] at success
      rcases success with ⟨rfl, rfl⟩
      exact .nil
  | cons argument arguments induction =>
      cases headResult : elaborateExpression context argument supply with
      | none => simp [elaborateCallUsing, headResult] at success
      | some output =>
          rcases output with ⟨generatedArgument, afterArgument⟩
          exact .cons (expressionSound headResult) (induction (by
            simpa [elaborateCallUsing, headResult] using success))

/-- Soundness of the fuel-indexed executable against the independent
fuel-indexed relation. -/
theorem elaborateFuel_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed) :
    ∀ {fuel context expression supply generated next},
      elaborateFuel signature fuel context expression supply =
        some (generated, next) →
      ElaboratesFuel signature fuel context expression supply generated next := by
  intro fuel
  induction fuel with
  | zero =>
      intro context expression supply generated next success
      simp [elaborateFuel] at success
  | succ fuel induction =>
      intro context expression supply generated next success
      cases expression with
      | var index =>
          cases lookup : context[index]? with
          | none => simp [elaborateFuel, lookup] at success
          | some scheme =>
              simp [elaborateFuel, lookup] at success
              rcases success with ⟨rfl, rfl⟩
              exact ⟨scheme, lookup, rfl, rfl⟩
      | lit value =>
          simp [elaborateFuel] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      | something =>
          simp [elaborateFuel] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      | lam body =>
          cases bodyResult : elaborateFuel signature fuel
              (.mono (.var ⟨supply.ty⟩) :: context) body (supply.nextTy 1) with
          | none => simp [elaborateFuel, bodyResult] at success
          | some output =>
              rcases output with ⟨generatedBody, afterBody⟩
              simp [elaborateFuel, bodyResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact ⟨generatedBody, induction bodyResult, rfl⟩
      | app function argument =>
          cases functionResult : elaborateFuel signature fuel context function supply with
          | none => simp [elaborateFuel, functionResult] at success
          | some output =>
              rcases output with ⟨generatedFunction, afterFunction⟩
              cases argumentResult : elaborateFuel signature fuel context argument
                  afterFunction with
              | none => simp [elaborateFuel, functionResult, argumentResult] at success
              | some output =>
                  rcases output with ⟨generatedArgument, afterArgument⟩
                  simp [elaborateFuel, functionResult, argumentResult] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact ⟨generatedFunction, afterFunction, generatedArgument,
                    afterArgument, induction functionResult,
                    induction argumentResult, rfl, rfl⟩
      | tuple items =>
          cases itemsResult : elaborateItemsUsing (elaborateFuel signature fuel)
              context items supply with
          | none => simp [elaborateFuel, itemsResult] at success
          | some output =>
              rcases output with ⟨generatedItems, afterItems⟩
              simp [elaborateFuel, itemsResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact ⟨generatedItems,
                elaborateItemsUsing_sound induction itemsResult, rfl⟩
      | letE value body =>
          cases valueResult : elaborateFuel signature fuel context value supply with
          | none => simp [elaborateFuel, valueResult] at success
          | some output =>
              rcases output with ⟨generatedValue, afterValue⟩
              cases closureResult : inferGeneratedUsing unify generatedValue with
              | none => simp [elaborateFuel, valueResult, closureResult] at success
              | some closed =>
                  cases bodyResult : elaborateFuel signature fuel
                      ((context.applyFree closed.substitution).generalize
                          closed.target :: context.applyFree closed.substitution)
                      body
                      (afterValue.join
                        (context.applyFree closed.substitution).initialSupply) with
                  | none =>
                      simp [elaborateFuel, valueResult, closureResult, bodyResult]
                        at success
                  | some output =>
                      rcases output with ⟨generatedBody, afterBody⟩
                      simp [elaborateFuel, valueResult, closureResult, bodyResult]
                        at success
                      rcases success with ⟨rfl, rfl⟩
                      obtain ⟨closure, substitutionEquality, targetEquality,
                          absorbing⟩ :=
                        inferGeneratedUsing_absorbingPrincipalBlockClosure
                          unify_absorbingMGUSolver closureResult
                      have bodyResult' : elaborateFuel signature fuel
                          ((context.applyFree closure.substitution).generalize
                              closure.target ::
                            context.applyFree closure.substitution)
                          body
                          (afterValue.join
                            (context.applyFree
                              closure.substitution).initialSupply) =
                          some (generatedBody, afterBody) := by
                        simpa [substitutionEquality, targetEquality] using bodyResult
                      exact ⟨generatedValue, afterValue,
                        induction valueResult, closure, generatedBody, absorbing,
                        induction bodyResult', by simp [substitutionEquality]⟩
      | ctor constructor arguments =>
          cases lookup : signature.base.lookupDataConstructor constructor with
          | none => simp [elaborateFuel, lookup] at success
          | some scheme =>
              by_cases arity : arguments.length = scheme.callArity
              · cases callResult : elaborateCallUsing
                    (elaborateFuel signature fuel) context
                    ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                    (scheme.instantiate supply).2 with
                | none => simp [elaborateFuel, lookup, arity, callResult] at success
                | some output =>
                    rcases output with ⟨generatedCall, afterCall⟩
                    simp [elaborateFuel, lookup, arity, callResult] at success
                    rcases success with ⟨rfl, rfl⟩
                    exact ⟨scheme, lookup, arity,
                      wellFormed.baseWellFormed.dataConstructorClosed_of_lookup
                        lookup,
                      elaborateCallUsing_sound induction callResult⟩
              · simp [elaborateFuel, lookup, arity] at success
      | prim operation arguments =>
          cases lookup : signature.base.lookupPrimitive operation with
          | none => simp [elaborateFuel, lookup] at success
          | some scheme =>
              by_cases arity : arguments.length = scheme.callArity
              · cases callResult : elaborateCallUsing
                    (elaborateFuel signature fuel) context
                    ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                    (scheme.instantiate supply).2 with
                | none => simp [elaborateFuel, lookup, arity, callResult] at success
                | some output =>
                    rcases output with ⟨generatedCall, afterCall⟩
                    simp [elaborateFuel, lookup, arity, callResult] at success
                    rcases success with ⟨rfl, rfl⟩
                    exact ⟨scheme, lookup, arity,
                      wellFormed.baseWellFormed.primitiveClosed_of_lookup lookup,
                      elaborateCallUsing_sound induction callResult⟩
              · simp [elaborateFuel, lookup, arity] at success
      | ifE condition thenBranch elseBranch =>
          exact elaborateCallUsing_sound induction (by
            simpa [elaborateFuel] using success)
      | fixE body =>
          exact elaborateFixUsing_sound induction (by
            simpa [elaborateFuel] using success)
      | matcher clauses =>
          exact MatcherTyping.elaborateMatcherLiteralUsing_sound induction (by
            simpa [elaborateFuel] using success)
      | matchAll target matcher pattern body =>
          exact elaborateMatchAllUsing_sound induction wellFormed (by
            simpa [elaborateFuel] using success)
      | matchFirst target matcher arms =>
          exact MatchFirstTyping.elaborateUsing_sound induction wellFormed (by
            simpa [elaborateFuel] using success)

/-- Public executable elaboration is sound. -/
theorem elaborate_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context expression supply generated next}
    (success : elaborate signature context expression supply =
      some (generated, next)) :
    Elaborates signature context expression supply generated next :=
  ⟨expression.complexity + 1,
    elaborateFuel_sound wellFormed (by simpa [elaborate] using success)⟩

structure PrincipalTypingDerivation
    (signature : FrozenSignature) (context : Context) (expression : Expr)
    (target : Ty) where
  generated : Generated
  next : Supply
  elaboration : Elaborates signature context expression context.initialSupply
    generated next
  closure : PrincipalBlockClosure generated
  absorbing : closure.Absorbing
  target_eq : target = closure.target

def PrincipalTyping (signature : FrozenSignature) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  Nonempty (PrincipalTypingDerivation signature context expression target)

/-- Full M4 typing is the substitution-instance closure of an independently
elaborated and certified principal constraint block. -/
def Typing (signature : FrozenSignature) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  ∃ principal, PrincipalTyping signature context expression principal ∧
    IsInstance principal target

theorem infer_success_principalTyping
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context expression target}
    (success : infer signature context expression = some target) :
    PrincipalTyping signature context expression target := by
  unfold infer at success
  cases elaborated : elaborate signature context expression context.initialSupply with
  | none => simp [elaborated] at success
  | some output =>
      rcases output with ⟨generated, next⟩
      cases closedResult : inferGeneratedUsing unify generated with
      | none => simp [elaborated, closedResult] at success
      | some closed =>
          simp [elaborated, closedResult] at success
          subst target
          obtain ⟨closure, _, targetEquality, absorbing⟩ :=
            inferGeneratedUsing_absorbingPrincipalBlockClosure
              unify_absorbingMGUSolver closedResult
          exact ⟨⟨generated, next, elaborate_sound wellFormed elaborated,
            closure, absorbing, targetEquality⟩⟩

theorem infer_success_typing
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context expression target}
    (success : infer signature context expression = some target) :
    Typing signature context expression target := by
  exact ⟨target, infer_success_principalTyping wellFormed success,
    Subst.id, by simp⟩

end TypePM.Source.M4
