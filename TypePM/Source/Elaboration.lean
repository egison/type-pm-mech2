import TypePM.Source.Syntax
import TypePM.Signature
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

/-- The exact generated block built around a lambda body. -/
def fromLam (domain : Ty) (body : Generated) : Generated :=
  ⟨.fn domain body.target, body.hard, body.pending⟩

/-- The ordinary application constraint shape.  Constructor, primitive, and
conditional calls are left folds of this same operation. -/
def fromApp (function argument : Generated) (domain target : Ty) : Generated :=
  ⟨target,
    function.hard ++ argument.hard ++
      [.ty function.target (.fn domain target)],
    function.pending ++ argument.pending ++
      [⟨argument.target, domain⟩]⟩

/-- Hide a closed right-hand-side block and expose only its effects together
with the body block. -/
def fromLet
    (effects : List Equation) (body : Generated) : Generated :=
  { target := body.target
    hard := effects ++ body.hard
    pending := body.pending }

end Generated

namespace Scheme

/-- Number of curried arguments before the final result. -/
def callArity (scheme : Scheme) : Nat :=
  let rec go : PolyTy → Nat
    | .fn _ result => go result + 1
    | _ => 0
  go scheme.body

end Scheme

/-- Closed internal type scheme used to elaborate a conditional as an
ordinary three-argument call. -/
def conditionalScheme : Scheme :=
  ⟨1, 0,
    .fn PolyDataTypes.bool
      (.fn (.bound 0) (.fn (.bound 0) (.bound 0))), by
    simp [PolyDataTypes.bool, PolyTy.WellScoped]⟩

theorem conditionalScheme_closed : conditionalScheme.Closed := by
  constructor <;> rfl

mutual

/-- Syntax-node measure shared by mutually recursive source elaborators and
the direct M4 syntax. -/
def Expr.complexity : Expr → Nat
  | .var _ | .lit _ | .something => 1
  | .lam body => body.complexity + 1
  | .app function argument =>
      function.complexity + argument.complexity + 1
  | .tuple items | .ctor _ items | .prim _ items =>
      Expr.listComplexity items + 1
  | .letE value body => value.complexity + body.complexity + 1
  | .ifE condition thenBranch elseBranch =>
      condition.complexity + thenBranch.complexity +
        elseBranch.complexity + 4
  | .fixE body => body.complexity + 1
  | .matcher clauses => MatcherClause.listComplexity clauses + 1
  | .matchAll target matcher pattern body =>
      target.complexity + matcher.complexity + pattern.complexity +
        body.complexity + 1

def Expr.listComplexity : List Expr → Nat
  | [] => 0
  | item :: items => item.complexity + Expr.listComplexity items + 1

/-- Complexity of a pattern, including embedded value expressions. -/
def Pattern.complexity : Pattern → Nat
  | .var | .wild | .embed _ => 1
  | .value expression => expression.complexity + 1
  | .ctor _ fields | .tuple fields | .app _ fields =>
      Pattern.listComplexity fields + 1

def Pattern.listComplexity : List Pattern → Nat
  | [] => 0
  | pattern :: patterns =>
      pattern.complexity + Pattern.listComplexity patterns + 1

/-- Complexity of a matcher clause includes all source expressions stored in
its next-matcher expression and ordered arms. -/
def MatcherClause.complexity : MatcherClause → Nat
  | .mk _ nextMatchers arms =>
      nextMatchers.complexity + MatcherArm.listComplexity arms + 1

def MatcherClause.listComplexity : List MatcherClause → Nat
  | [] => 0
  | clause :: clauses =>
      clause.complexity + MatcherClause.listComplexity clauses + 1

def MatcherArm.complexity : MatcherArm → Nat
  | .mk _ body => body.complexity + 1

def MatcherArm.listComplexity : List MatcherArm → Nat
  | [] => 0
  | arm :: arms => arm.complexity + MatcherArm.listComplexity arms + 1

end

@[simp] theorem Expr.complexity_var (index : Nat) :
    (Expr.var index).complexity = 1 := rfl
@[simp] theorem Expr.complexity_lit (value : Int) :
    (Expr.lit value).complexity = 1 := rfl
@[simp] theorem Expr.complexity_something : Expr.something.complexity = 1 := rfl
@[simp] theorem Expr.complexity_lam (body : Expr) :
    (Expr.lam body).complexity = body.complexity + 1 := rfl
@[simp] theorem Expr.complexity_app (function argument : Expr) :
    (Expr.app function argument).complexity =
      function.complexity + argument.complexity + 1 := rfl
@[simp] theorem Expr.complexity_tuple (items : List Expr) :
    (Expr.tuple items).complexity = Expr.listComplexity items + 1 := rfl
@[simp] theorem Expr.complexity_letE (value body : Expr) :
    (Expr.letE value body).complexity =
      value.complexity + body.complexity + 1 := rfl
@[simp] theorem Expr.complexity_ctor (constructor : DataCtor) (items : List Expr) :
    (Expr.ctor constructor items).complexity = Expr.listComplexity items + 1 := rfl
@[simp] theorem Expr.complexity_prim (operation : PrimOp) (items : List Expr) :
    (Expr.prim operation items).complexity = Expr.listComplexity items + 1 := rfl
@[simp] theorem Expr.complexity_ifE (condition thenBranch elseBranch : Expr) :
    (Expr.ifE condition thenBranch elseBranch).complexity =
      condition.complexity + thenBranch.complexity +
        elseBranch.complexity + 4 := rfl
@[simp] theorem Expr.complexity_fixE (body : Expr) :
    (Expr.fixE body).complexity = body.complexity + 1 := rfl
@[simp] theorem Expr.complexity_matcher (clauses : List MatcherClause) :
    (Expr.matcher clauses).complexity =
      MatcherClause.listComplexity clauses + 1 := rfl
@[simp] theorem Expr.complexity_matchAll
    (target matcher : Expr) (pattern : Pattern) (body : Expr) :
    (Expr.matchAll target matcher pattern body).complexity =
      target.complexity + matcher.complexity + pattern.complexity +
        body.complexity + 1 := rfl
@[simp] theorem Expr.listComplexity_nil : Expr.listComplexity [] = 0 := rfl
@[simp] theorem Expr.listComplexity_cons (item : Expr) (items : List Expr) :
    Expr.listComplexity (item :: items) =
      item.complexity + Expr.listComplexity items + 1 := rfl

@[simp] theorem Pattern.complexity_var : Pattern.var.complexity = 1 := rfl
@[simp] theorem Pattern.complexity_wild : Pattern.wild.complexity = 1 := rfl
@[simp] theorem Pattern.complexity_value (expression : Expr) :
    (Pattern.value expression).complexity = expression.complexity + 1 := rfl
@[simp] theorem Pattern.complexity_ctor
    (constructor : PatternCtor) (fields : List Pattern) :
    (Pattern.ctor constructor fields).complexity =
      Pattern.listComplexity fields + 1 := rfl
@[simp] theorem Pattern.complexity_tuple (items : List Pattern) :
    (Pattern.tuple items).complexity = Pattern.listComplexity items + 1 := rfl
@[simp] theorem Pattern.complexity_embed (index : Nat) :
    (Pattern.embed index).complexity = 1 := rfl
@[simp] theorem Pattern.complexity_app
    (function : PatternFunName) (arguments : List Pattern) :
    (Pattern.app function arguments).complexity =
      Pattern.listComplexity arguments + 1 := rfl
@[simp] theorem Pattern.listComplexity_nil : Pattern.listComplexity [] = 0 := rfl
@[simp] theorem Pattern.listComplexity_cons
    (pattern : Pattern) (patterns : List Pattern) :
    Pattern.listComplexity (pattern :: patterns) =
      pattern.complexity + Pattern.listComplexity patterns + 1 := rfl

@[simp] theorem MatcherClause.complexity_mk
    (header : PPat) (nextMatchers : Expr) (arms : List MatcherArm) :
    (MatcherClause.mk header nextMatchers arms).complexity =
      nextMatchers.complexity + MatcherArm.listComplexity arms + 1 := rfl
@[simp] theorem MatcherClause.listComplexity_nil :
    MatcherClause.listComplexity [] = 0 := rfl
@[simp] theorem MatcherClause.listComplexity_cons
    (clause : MatcherClause) (clauses : List MatcherClause) :
    MatcherClause.listComplexity (clause :: clauses) =
      clause.complexity + MatcherClause.listComplexity clauses + 1 := rfl

@[simp] theorem MatcherArm.complexity_mk (header : DPat) (body : Expr) :
    (MatcherArm.mk header body).complexity = body.complexity + 1 := rfl
@[simp] theorem MatcherArm.listComplexity_nil :
    MatcherArm.listComplexity [] = 0 := rfl
@[simp] theorem MatcherArm.listComplexity_cons
    (arm : MatcherArm) (arms : List MatcherArm) :
    MatcherArm.listComplexity (arm :: arms) =
      arm.complexity + MatcherArm.listComplexity arms + 1 := rfl

mutual

/-- Executable scheme-aware elaboration.  `letE` invokes the certified M1
block closer on the generated right-hand side before elaborating the body. -/
def elaborate (signature : Signature) (context : Context) :
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
        elaborate signature (.mono domain :: context) body (supply.nextTy 1)
      pure
        (⟨.fn domain generatedBody.target,
          generatedBody.hard, generatedBody.pending⟩, next)
  | .app function argument, supply => do
      let (generatedFunction, afterFunction) ←
        elaborate signature context function supply
      let (generatedArgument, afterArgument) ←
        elaborate signature context argument afterFunction
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
      let (generatedItems, next) ← elaborateItems signature context items supply
      pure
        (⟨.prod generatedItems.targets,
          generatedItems.hard, generatedItems.pending⟩, next)
  | .letE value body, supply => do
      let (generatedValue, afterValue) ← elaborate signature context value supply
      let closedValue ← inferGeneratedUsing unify generatedValue
      let closedContext := context.applyFree closedValue.substitution
      let generalized := closedContext.generalize closedValue.target
      let bodySupply := afterValue.join closedContext.initialSupply
      let (generatedBody, next) ←
        elaborate signature (generalized :: closedContext) body bodySupply
      pure
        (Generated.fromLet
          (context.interfaceEquations closedValue.substitution) generatedBody,
          next)
  | .ctor constructor arguments, supply => do
      let scheme ← signature.lookupDataConstructor constructor
      if arguments.length = scheme.callArity then
        let instantiated := scheme.instantiate supply
        elaborateCall signature context
          ⟨instantiated.1, [], []⟩ arguments instantiated.2
      else
        none
  | .prim operation arguments, supply => do
      let scheme ← signature.lookupPrimitive operation
      if arguments.length = scheme.callArity then
        let instantiated := scheme.instantiate supply
        elaborateCall signature context
          ⟨instantiated.1, [], []⟩ arguments instantiated.2
      else
        none
  | .ifE condition thenBranch elseBranch, supply =>
      let instantiated := conditionalScheme.instantiate supply
      elaborateCall signature context ⟨instantiated.1, [], []⟩
        [condition, thenBranch, elseBranch] instantiated.2
  | .fixE _, _ => none
  | .matcher _, _ => none
  | .matchAll _ _ _ _, _ => none
termination_by expression => expression.complexity * 3 + 2
decreasing_by all_goals simp_wf <;> omega

/-- List counterpart of `elaborate`. -/
def elaborateItems (signature : Signature) (context : Context) :
    List Expr → Supply → Option (GeneratedItems × Supply)
  | [], supply => some (⟨[], [], []⟩, supply)
  | item :: items, supply => do
      let (generatedItem, afterItem) ← elaborate signature context item supply
      let (generatedItems, next) ←
        elaborateItems signature context items afterItem
      pure
        (⟨generatedItem.target :: generatedItems.targets,
          generatedItem.hard ++ generatedItems.hard,
          generatedItem.pending ++ generatedItems.pending⟩,
          next)
termination_by expressions => Expr.listComplexity expressions * 3 + 1
decreasing_by all_goals simp_wf <;> omega

/-- Elaborate a fixed-arity call by repeatedly applying the ordinary
application constraint shape. -/
def elaborateCall (signature : Signature) (context : Context) :
    Generated → List Expr → Supply → Option (Generated × Supply)
  | accumulated, [], supply => some (accumulated, supply)
  | accumulated, argument :: arguments, supply => do
      let (generatedArgument, afterArgument) ←
        elaborate signature context argument supply
      let domain : Ty := .var ⟨afterArgument.ty⟩
      let target : Ty := .var ⟨afterArgument.ty + 1⟩
      elaborateCall signature context
        (Generated.fromApp accumulated generatedArgument domain target)
        arguments (afterArgument.nextTy 2)
termination_by _ arguments _ => Expr.listComplexity arguments * 3
decreasing_by all_goals simp_wf <;> omega

end

mutual

/-- Declarative scheme-aware elaboration.  Its `letE` constructor contains a
`PrincipalBlockClosure`, never a call to the executable inference function. -/
inductive Elaborates :
    Signature → Context → Expr → Supply → Generated → Supply → Prop where
  | var {signature context index supply scheme}
      (lookup : context[index]? = some scheme) :
      Elaborates signature context (.var index) supply
        ⟨(scheme.instantiate supply).1, [], []⟩
        (scheme.instantiate supply).2
  | lit {signature context value supply} :
      Elaborates signature context (.lit value) supply ⟨.int, [], []⟩ supply
  | something {signature context supply} :
      Elaborates signature context .something supply
        ⟨.matcher .any (.var ⟨supply.ty⟩), [], []⟩
        (supply.nextTy 1)
  | lam {signature context body supply generatedBody next} :
      Elaborates signature (.mono (.var ⟨supply.ty⟩) :: context) body
        (supply.nextTy 1) generatedBody next →
      Elaborates signature context (.lam body) supply
        ⟨.fn (.var ⟨supply.ty⟩) generatedBody.target,
          generatedBody.hard, generatedBody.pending⟩ next
  | app {signature context function argument supply generatedFunction afterFunction
      generatedArgument afterArgument} :
      Elaborates signature context function supply generatedFunction afterFunction →
      Elaborates signature context argument afterFunction generatedArgument
        afterArgument →
      Elaborates signature context (.app function argument) supply
        ⟨.var ⟨afterArgument.ty + 1⟩,
          generatedFunction.hard ++ generatedArgument.hard ++
            [.ty generatedFunction.target
              (.fn (.var ⟨afterArgument.ty⟩)
                (.var ⟨afterArgument.ty + 1⟩))],
          generatedFunction.pending ++ generatedArgument.pending ++
            [⟨generatedArgument.target, .var ⟨afterArgument.ty⟩⟩]⟩
        (afterArgument.nextTy 2)
  | tuple {signature context items supply generatedItems next} :
      ElaboratesItems signature context items supply generatedItems next →
      Elaborates signature context (.tuple items) supply
        ⟨.prod generatedItems.targets,
          generatedItems.hard, generatedItems.pending⟩ next
  | letE {signature context value body supply generatedValue afterValue
      generatedBody next}
      (valueElaboration :
        Elaborates signature context value supply generatedValue afterValue)
      (closure : PrincipalBlockClosure generatedValue)
      (absorbing : closure.Absorbing)
      (bodyElaboration :
        Elaborates signature
          ((context.applyFree closure.substitution).generalize closure.target ::
            context.applyFree closure.substitution)
          body
          (afterValue.join
            (context.applyFree closure.substitution).initialSupply)
          generatedBody next) :
      Elaborates signature context (.letE value body) supply
        (Generated.fromLet
          (context.interfaceEquations closure.substitution) generatedBody)
        next
  | ctor {signature context constructor arguments scheme supply generated next}
      (lookup : signature.lookupDataConstructor constructor = some scheme)
      (arity : arguments.length = scheme.callArity)
      (closed : scheme.Closed)
      (call : ElaboratesCall signature context
        ⟨(scheme.instantiate supply).1, [], []⟩ arguments
        (scheme.instantiate supply).2 generated next) :
      Elaborates signature context (.ctor constructor arguments) supply
        generated next
  | prim {signature context operation arguments scheme supply generated next}
      (lookup : signature.lookupPrimitive operation = some scheme)
      (arity : arguments.length = scheme.callArity)
      (closed : scheme.Closed)
      (call : ElaboratesCall signature context
        ⟨(scheme.instantiate supply).1, [], []⟩ arguments
        (scheme.instantiate supply).2 generated next) :
      Elaborates signature context (.prim operation arguments) supply
        generated next
  | ifE {signature context condition thenBranch elseBranch supply generated next}
      (call : ElaboratesCall signature context
        ⟨(conditionalScheme.instantiate supply).1, [], []⟩
        [condition, thenBranch, elseBranch]
        (conditionalScheme.instantiate supply).2 generated next) :
      Elaborates signature context (.ifE condition thenBranch elseBranch)
        supply generated next

/-- Relational elaboration for sibling lists. -/
inductive ElaboratesItems :
    Signature → Context → List Expr → Supply → GeneratedItems → Supply → Prop where
  | nil {signature context supply} :
      ElaboratesItems signature context [] supply ⟨[], [], []⟩ supply
  | cons {signature context item items supply generatedItem afterItem generatedItems next} :
      Elaborates signature context item supply generatedItem afterItem →
      ElaboratesItems signature context items afterItem generatedItems next →
      ElaboratesItems signature context (item :: items) supply
        ⟨generatedItem.target :: generatedItems.targets,
          generatedItem.hard ++ generatedItems.hard,
          generatedItem.pending ++ generatedItems.pending⟩ next

/-- Relational counterpart of `elaborateCall`. -/
inductive ElaboratesCall :
    Signature → Context → Generated → List Expr → Supply →
      Generated → Supply → Prop where
  | nil {signature context accumulated supply} :
      ElaboratesCall signature context accumulated [] supply
        accumulated supply
  | cons {signature context accumulated argument arguments supply
      generatedArgument afterArgument generated next} :
      Elaborates signature context argument supply generatedArgument
        afterArgument →
      ElaboratesCall signature context
        (Generated.fromApp accumulated generatedArgument
          (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩))
        arguments (afterArgument.nextTy 2) generated next →
      ElaboratesCall signature context accumulated (argument :: arguments)
        supply generated next

end

mutual

/-- Executable elaboration is sound for the independent relational judgment. -/
theorem elaborate_sound
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (success : elaborate signature context expression supply = some (generated, next)) :
    Elaborates signature context expression supply generated next := by
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
      cases bodyResult : elaborate signature
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
              exact .lam (elaborate_sound wellFormed bodyResult)
  | app function argument =>
      cases functionResult : elaborate signature context function supply with
      | none => simp [elaborate, functionResult] at success
      | some functionOutput =>
          cases functionOutput with
          | mk generatedFunction afterFunction =>
              cases argumentResult :
                  elaborate signature context argument afterFunction with
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
                        (elaborate_sound wellFormed functionResult)
                        (elaborate_sound wellFormed argumentResult)
  | tuple items =>
      cases itemsResult : elaborateItems signature context items supply with
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
              exact .tuple (elaborateItems_sound wellFormed itemsResult)
  | letE value body =>
      cases valueResult : elaborate signature context value supply with
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
                  cases bodyResult : elaborate signature
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
                              elaborate signature
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
                              (elaborate_sound wellFormed valueResult) closure absorbing
                              (elaborate_sound wellFormed bodyResult'))
  | ctor constructor arguments =>
      cases lookup : signature.lookupDataConstructor constructor with
      | none => simp [elaborate, lookup] at success
      | some scheme =>
          by_cases arity : arguments.length = scheme.callArity
          · cases callResult : elaborateCall signature context
                ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                (scheme.instantiate supply).2 with
            | none => simp [elaborate, lookup, arity, callResult] at success
            | some output =>
                cases output with
                | mk generatedCall afterCall =>
                    have equality :
                        (generatedCall, afterCall) = (generated, next) :=
                      Option.some.inj (by
                        simpa [elaborate, lookup, arity, callResult]
                          using success)
                    injection equality with generatedEquality nextEquality
                    subst generated
                    subst next
                    exact .ctor lookup arity
                      (wellFormed.dataConstructorClosed_of_lookup lookup)
                      (elaborateCall_sound wellFormed callResult)
          · simp [elaborate, lookup, arity] at success
  | prim operation arguments =>
      cases lookup : signature.lookupPrimitive operation with
      | none => simp [elaborate, lookup] at success
      | some scheme =>
          by_cases arity : arguments.length = scheme.callArity
          · cases callResult : elaborateCall signature context
                ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                (scheme.instantiate supply).2 with
            | none => simp [elaborate, lookup, arity, callResult] at success
            | some output =>
                cases output with
                | mk generatedCall afterCall =>
                    have equality :
                        (generatedCall, afterCall) = (generated, next) :=
                      Option.some.inj (by
                        simpa [elaborate, lookup, arity, callResult]
                          using success)
                    injection equality with generatedEquality nextEquality
                    subst generated
                    subst next
                    exact .prim lookup arity
                      (wellFormed.primitiveClosed_of_lookup lookup)
                      (elaborateCall_sound wellFormed callResult)
          · simp [elaborate, lookup, arity] at success
  | ifE condition thenBranch elseBranch =>
      cases callResult : elaborateCall signature context
          ⟨(conditionalScheme.instantiate supply).1, [], []⟩
          [condition, thenBranch, elseBranch]
          (conditionalScheme.instantiate supply).2 with
      | none => simp [elaborate, callResult] at success
      | some output =>
          cases output with
          | mk generatedCall afterCall =>
              have equality :
                  (generatedCall, afterCall) = (generated, next) :=
                Option.some.inj (by
                  simpa [elaborate, callResult] using success)
              injection equality with generatedEquality nextEquality
              subst generated
              subst next
              exact .ifE (elaborateCall_sound wellFormed callResult)
  | fixE body => simp [elaborate] at success
  | matcher clauses => simp [elaborate] at success
  | matchAll target matcher pattern body => simp [elaborate] at success
termination_by expression.complexity * 3 + 2
decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

/-- Executable list elaboration is sound. -/
theorem elaborateItems_sound
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (success : elaborateItems signature context expressions supply =
      some (generated, next)) :
    ElaboratesItems signature context expressions supply generated next := by
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
      cases itemResult : elaborate signature context item supply with
      | none => simp [elaborateItems, itemResult] at success
      | some itemOutput =>
          cases itemOutput with
          | mk generatedItem afterItem =>
              cases itemsResult : elaborateItems signature context items afterItem with
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
                        (elaborate_sound wellFormed itemResult)
                        (elaborateItems_sound wellFormed itemsResult)
termination_by Expr.listComplexity expressions * 3 + 1
decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

/-- Executable call elaboration is sound. -/
theorem elaborateCall_sound
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {accumulated generated : Generated}
    {expressions : List Expr} {supply next : Supply}
    (success : elaborateCall signature context accumulated expressions supply =
      some (generated, next)) :
    ElaboratesCall signature context accumulated expressions supply
      generated next := by
  cases expressions with
  | nil =>
      have equality : (accumulated, supply) = (generated, next) :=
        Option.some.inj (by simpa [elaborateCall] using success)
      injection equality with generatedEquality nextEquality
      subst generated
      subst next
      exact .nil
  | cons argument arguments =>
      cases argumentResult : elaborate signature context argument supply with
      | none => simp [elaborateCall, argumentResult] at success
      | some output =>
          cases output with
          | mk generatedArgument afterArgument =>
              let nextAccumulated := Generated.fromApp accumulated
                generatedArgument (.var ⟨afterArgument.ty⟩)
                (.var ⟨afterArgument.ty + 1⟩)
              cases restResult : elaborateCall signature context nextAccumulated
                  arguments (afterArgument.nextTy 2) with
              | none =>
                  simp [elaborateCall, argumentResult, nextAccumulated,
                    restResult] at success
              | some restOutput =>
                  cases restOutput with
                  | mk generatedRest afterRest =>
                      have equality :
                          (generatedRest, afterRest) = (generated, next) :=
                        Option.some.inj (by
                          simpa [elaborateCall, argumentResult,
                            nextAccumulated, restResult] using success)
                      injection equality with generatedEquality nextEquality
                      subst generated
                      subst next
                      exact .cons
                        (elaborate_sound wellFormed argumentResult)
                        (by
                          simpa [nextAccumulated] using
                            elaborateCall_sound wellFormed restResult)
termination_by Expr.listComplexity expressions * 3
decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

end

/-- Elaborate a complete source expression above all names in its scheme
context. -/
def elaborateRoot (signature : Signature) (context : Context) (expression : Expr) :
    Option Generated :=
  (elaborate signature context expression context.initialSupply).map Prod.fst

/-- Public executable M2 inference skeleton. -/
def infer (signature : Signature) (context : Context) (expression : Expr) : Option Ty := do
  let generated ← elaborateRoot signature context expression
  let closed ← inferGeneratedUsing unify generated
  pure closed.target

/-- Independent evidence for one blockwise-principal result of a complete
source expression.  Nested `letE` right-hand sides are already hidden behind
the `PrincipalBlockClosure` witnesses inside `Elaborates`.  Global source
principality requires a separate coherence theorem between such witnesses. -/
structure PrincipalTypingDerivation
    (signature : Signature) (context : Context) (expression : Expr) (target : Ty) where
  generated : Generated
  next : Supply
  elaboration :
    Elaborates signature context expression context.initialSupply generated next
  closure : PrincipalBlockClosure generated
  absorbing : closure.Absorbing
  target_eq : target = closure.target

/-- The source expression has the indicated blockwise-principal result
according to the declarative elaboration and closure relations. -/
def PrincipalTyping
    (signature : Signature) (context : Context) (expression : Expr)
    (target : Ty) : Prop :=
  Nonempty (PrincipalTypingDerivation signature context expression target)

/-- Declarative source typing is the substitution-instance closure of a
blockwise-principal source elaboration witness.  This keeps arbitrary result types independent
of the executable representative selected by `infer`. -/
def Typing (signature : Signature) (context : Context)
    (expression : Expr) (target : Ty) : Prop :=
  ∃ principal,
    PrincipalTyping signature context expression principal ∧
      IsInstance principal target

namespace PrincipalTyping

/-- A blockwise-principal source result is itself a declarative source typing. -/
theorem toTyping
    {signature : Signature} {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping signature context expression target) :
    Typing signature context expression target := by
  exact ⟨target, principal, Subst.id, by simp⟩

/-- Every substitution instance of a fixed principal derivation is a source
typing.  This is the representative-local principality fact available before
different nested-closure representatives have been aligned. -/
theorem instance_typing
    {signature : Signature} {context : Context} {expression : Expr} {principal target : Ty}
    (principalTyping : PrincipalTyping signature context expression principal)
    (instantiation : IsInstance principal target) :
    Typing signature context expression target :=
  ⟨principal, principalTyping, instantiation⟩

end PrincipalTyping

namespace Inference

/-- Soundness of the executable M2 skeleton: a returned source type has an
independent relational elaboration and an absorbing block closure. -/
theorem infer_success_principalTyping
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer signature context expression = some target) :
    PrincipalTyping signature context expression target := by
  unfold infer at success
  cases elaborated : elaborate signature context expression context.initialSupply with
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
                  elaboration := elaborate_sound wellFormed elaborated
                  closure := closure
                  absorbing := absorbing
                  target_eq := targetEquality }⟩

/-- Public M2 inference soundness for the instance-closed declarative
`Typing` relation. -/
theorem infer_success_typing
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {target : Ty}
    (success : infer signature context expression = some target) :
    Typing signature context expression target :=
  (infer_success_principalTyping wellFormed success).toTyping

end Inference

end TypePM.Source
