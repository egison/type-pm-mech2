import TypePM.Source.Elaboration
import TypePM.Source.FrozenSignature

/-!
# M4 user-pattern and match-site elaboration

This module is the first typed M4 layer above the M3 expression elaborator.
It keeps the M3 entry point stable while giving user patterns and `matchAll`
their own executable and relational judgments.  Embedded value expressions,
the target, matcher, and body are elaborated by the already verified M3
expression layer.  Consequently nested matcher literals and recursive M4
expressions remain a later checkpoint, rather than being silently accepted.

Pattern bindings are stored in left-to-right source order.  The same order is
prepended to an expression context, so source-order nameless index zero refers
to the first pattern binder.  A value pattern therefore sees precisely the
bindings produced to its left.
-/

namespace TypePM.Source

/-- Pattern arguments supplied to a named pattern function. -/
abbrev PatternContext := List Dual

/-- Constraints, synthesized dual, and accumulated left-to-right bindings
produced by one user pattern. -/
structure GeneratedPattern where
  dual : Dual
  bindings : List Ty
  hard : List Equation
  pending : List CheckObligation
deriving Repr

/-- List counterpart of `GeneratedPattern`. -/
structure GeneratedPatterns where
  duals : List Dual
  bindings : List Ty
  hard : List Equation
  pending : List CheckObligation
deriving Repr

namespace Pattern

/-- Put accumulated pattern bindings before the ordinary source context,
without generalizing any of them. -/
def extendContext (bindings : List Ty) (context : Context) : Context :=
  bindings.map Scheme.mono ++ context

/-- Equality constraints connecting synthesized child duals to a frozen
dual scheme's fields.  Both target and capability flow through the stored
interface; no pattern-function body is consulted. -/
def fieldEquations (actual expected : List Dual) : List Equation :=
  (List.zipWith (fun child field =>
    [.ty child.target field.target,
      .cap child.capability field.capability]) actual expected).flatten

end Pattern

abbrev M4ExpressionElaborator :=
  Context → Expr → Supply → Option (Generated × Supply)

abbrev M4ExpressionElaborationRelation :=
  Context → Expr → Supply → Generated → Supply → Prop

mutual

/-- Callback-parametric pattern synthesis.  In particular, a value pattern is
elaborated by the same expression layer as its enclosing match. -/
def elaboratePatternUsingFuel
    (elaborateExpression : M4ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (arguments : PatternContext) :
    Nat → Pattern → List Ty → Supply → Option (GeneratedPattern × Supply)
  | 0, _, _, _ => none
  | _ + 1, .var, bindings, supply =>
      let dual : Dual :=
        { capability := .var ⟨supply.cap⟩
          target := .var ⟨supply.ty⟩ }
      some (⟨dual, bindings ++ [dual.target], [], []⟩,
        ⟨supply.ty + 1, supply.cap + 1⟩)
  | _ + 1, .wild, bindings, supply =>
      some (⟨(⟨.var ⟨supply.cap⟩, .var ⟨supply.ty⟩⟩ : Dual),
        bindings, [], []⟩, ⟨supply.ty + 1, supply.cap + 1⟩)
  | _ + 1, .value expression, bindings, supply => do
      let (generated, afterExpression) ← elaborateExpression
        (Pattern.extendContext bindings context) expression supply
      pure (⟨(⟨.var ⟨afterExpression.cap⟩, generated.target⟩ : Dual),
        bindings, generated.hard, generated.pending⟩,
        ⟨afterExpression.ty, afterExpression.cap + 1⟩)
  | fuel + 1, .ctor constructor fields, bindings, supply => do
      let scheme ← signature.lookupPatternConstructor constructor
      if fields.length = scheme.fields.length then
        let instantiated := scheme.instantiate supply
        let (generatedFields, next) ← elaboratePatternsUsingFuel
          elaborateExpression signature context arguments fuel fields bindings
          instantiated.2
        pure (⟨instantiated.1.result, generatedFields.bindings,
          generatedFields.hard ++ Pattern.fieldEquations generatedFields.duals
            instantiated.1.fields, generatedFields.pending⟩, next)
      else none
  | fuel + 1, .tuple items, bindings, supply => do
      let (generatedItems, next) ← elaboratePatternsUsingFuel elaborateExpression
        signature context arguments fuel items bindings supply
      pure (⟨(⟨.prod (Dual.capabilities generatedItems.duals),
        .prod (Dual.targets generatedItems.duals)⟩ : Dual),
        generatedItems.bindings, generatedItems.hard,
        generatedItems.pending⟩, next)
  | _ + 1, .embed index, bindings, supply => do
      let dual ← arguments[index]?
      pure (⟨dual, bindings, [], []⟩, supply)
  | fuel + 1, .app function fields, bindings, supply => do
      let scheme ← signature.lookupPatternFunction function
      if fields.length = scheme.fields.length then
        let instantiated := scheme.instantiate supply
        let (generatedFields, next) ← elaboratePatternsUsingFuel
          elaborateExpression signature context arguments fuel fields bindings
          instantiated.2
        pure (⟨instantiated.1.result, generatedFields.bindings,
          generatedFields.hard ++ Pattern.fieldEquations generatedFields.duals
            instantiated.1.fields, generatedFields.pending⟩, next)
      else none
def elaboratePatternsUsingFuel
    (elaborateExpression : M4ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (arguments : PatternContext) :
    Nat → List Pattern → List Ty → Supply → Option (GeneratedPatterns × Supply)
  | 0, _, _, _ => none
  | _ + 1, [], bindings, supply => some (⟨[], bindings, [], []⟩, supply)
  | fuel + 1, pattern :: patterns, bindings, supply => do
      let (generatedPattern, afterPattern) ← elaboratePatternUsingFuel
        elaborateExpression signature context arguments fuel pattern bindings supply
      let (generatedPatterns, next) ← elaboratePatternsUsingFuel
        elaborateExpression signature context arguments fuel patterns
        generatedPattern.bindings afterPattern
      pure (⟨generatedPattern.dual :: generatedPatterns.duals,
        generatedPatterns.bindings,
        generatedPattern.hard ++ generatedPatterns.hard,
        generatedPattern.pending ++ generatedPatterns.pending⟩, next)
end

/-- Kernel-computable callback-parametric pattern synthesis. -/
def elaboratePatternUsing
    (elaborateExpression : M4ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (arguments : PatternContext) (pattern : Pattern) (bindings : List Ty)
    (supply : Supply) : Option (GeneratedPattern × Supply) :=
  elaboratePatternUsingFuel elaborateExpression signature context arguments
    (pattern.complexity * 2 + 1) pattern bindings supply

/-- Kernel-computable left-to-right pattern-list synthesis. -/
def elaboratePatternsUsing
    (elaborateExpression : M4ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (arguments : PatternContext) (patterns : List Pattern) (bindings : List Ty)
    (supply : Supply) : Option (GeneratedPatterns × Supply) :=
  elaboratePatternsUsingFuel elaborateExpression signature context arguments
    (Pattern.listComplexity patterns * 2 + 1) patterns bindings supply

mutual

/-- Executable user-pattern synthesis.  `bindings` contains exactly the
binders produced by patterns to the left of the current one. -/
def elaboratePattern
    (signature : FrozenSignature) (context : Context)
    (arguments : PatternContext) :
    Pattern → List Ty → Supply → Option (GeneratedPattern × Supply)
  | .var, bindings, supply =>
      let dual : Dual :=
        { capability := .var ⟨supply.cap⟩
          target := .var ⟨supply.ty⟩ }
      some
        (⟨dual, bindings ++ [dual.target], [], []⟩,
          ⟨supply.ty + 1, supply.cap + 1⟩)
  | .wild, bindings, supply =>
      some
        (⟨(⟨.var ⟨supply.cap⟩, .var ⟨supply.ty⟩⟩ : Dual),
          bindings, [], []⟩,
          ⟨supply.ty + 1, supply.cap + 1⟩)
  | .value expression, bindings, supply => do
      let (generated, afterExpression) ←
        elaborate signature.base (Pattern.extendContext bindings context)
          expression supply
      pure
        (⟨(⟨.var ⟨afterExpression.cap⟩, generated.target⟩ : Dual),
          bindings, generated.hard, generated.pending⟩,
          ⟨afterExpression.ty, afterExpression.cap + 1⟩)
  | .ctor constructor fields, bindings, supply => do
      let scheme ← signature.lookupPatternConstructor constructor
      if fields.length = scheme.fields.length then
        let instantiated := scheme.instantiate supply
        let (generatedFields, next) ←
          elaboratePatterns signature context arguments fields bindings
            instantiated.2
        pure
          (⟨instantiated.1.result, generatedFields.bindings,
            generatedFields.hard ++
              Pattern.fieldEquations generatedFields.duals
                instantiated.1.fields,
            generatedFields.pending⟩,
            next)
      else
        none
  | .tuple items, bindings, supply => do
      let (generatedItems, next) ←
        elaboratePatterns signature context arguments items bindings supply
      pure
        (⟨(⟨.prod (Dual.capabilities generatedItems.duals),
            .prod (Dual.targets generatedItems.duals)⟩ : Dual),
          generatedItems.bindings, generatedItems.hard,
          generatedItems.pending⟩,
          next)
  | .embed index, bindings, supply => do
      let dual ← arguments[index]?
      pure (⟨dual, bindings, [], []⟩, supply)
  | .app function fields, bindings, supply => do
      let scheme ← signature.lookupPatternFunction function
      if fields.length = scheme.fields.length then
        let instantiated := scheme.instantiate supply
        let (generatedFields, next) ←
          elaboratePatterns signature context arguments fields bindings
            instantiated.2
        pure
          (⟨instantiated.1.result, generatedFields.bindings,
            generatedFields.hard ++
              Pattern.fieldEquations generatedFields.duals
                instantiated.1.fields,
            generatedFields.pending⟩,
            next)
      else
        none
termination_by pattern => pattern.complexity * 2 + 1
decreasing_by all_goals simp_wf <;> omega

/-- Left-to-right list synthesis. -/
def elaboratePatterns
    (signature : FrozenSignature) (context : Context)
    (arguments : PatternContext) :
    List Pattern → List Ty → Supply → Option (GeneratedPatterns × Supply)
  | [], bindings, supply => some (⟨[], bindings, [], []⟩, supply)
  | pattern :: patterns, bindings, supply => do
      let (generatedPattern, afterPattern) ←
        elaboratePattern signature context arguments pattern bindings supply
      let (generatedPatterns, next) ←
        elaboratePatterns signature context arguments patterns
          generatedPattern.bindings afterPattern
      pure
        (⟨generatedPattern.dual :: generatedPatterns.duals,
          generatedPatterns.bindings,
          generatedPattern.hard ++ generatedPatterns.hard,
          generatedPattern.pending ++ generatedPatterns.pending⟩,
          next)
termination_by patterns => Pattern.listComplexity patterns * 2
decreasing_by all_goals simp_wf <;> omega

end

/-- Assemble the constraints for a `matchAll` after all five components have
been synthesized.  The target agreement is an equality.  Matcher use is a
directional checking obligation whose expected side is an explicit matcher
slot. -/
def Generated.fromMatchAll
    (target : Generated) (pattern : GeneratedPattern)
    (matcher body : Generated) : Generated :=
  { target := DataTypes.list body.target
    hard := target.hard ++ [.ty pattern.dual.target target.target] ++
      pattern.hard ++ matcher.hard ++ body.hard
    pending := target.pending ++ pattern.pending ++ matcher.pending ++
      [⟨matcher.target, .slot pattern.dual.capability target.target⟩] ++
        body.pending }

/-- Callback-parametric `matchAll`; all four expression positions, including
expressions embedded in the pattern, use `elaborateExpression`. -/
def elaborateMatchAllUsing
    (elaborateExpression : M4ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (pattern : Pattern) (body : Expr)
    (supply : Supply) : Option (Generated × Supply) := do
  let (generatedTarget, afterTarget) ← elaborateExpression context target supply
  let (generatedPattern, afterPattern) ← elaboratePatternUsing
    elaborateExpression signature context [] pattern [] afterTarget
  let (generatedMatcher, afterMatcher) ←
    elaborateExpression context matcher afterPattern
  let (generatedBody, next) ← elaborateExpression
    (Pattern.extendContext generatedPattern.bindings context) body afterMatcher
  pure (Generated.fromMatchAll generatedTarget generatedPattern
    generatedMatcher generatedBody, next)

/-- Executable typing of one `matchAll` node.  This is intentionally a
separate M4 entry point while recursive matcher literals are unfinished. -/
def elaborateMatchAll
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (pattern : Pattern) (body : Expr)
    (supply : Supply) : Option (Generated × Supply) := do
  let (generatedTarget, afterTarget) ←
    elaborate signature.base context target supply
  let (generatedPattern, afterPattern) ←
    elaboratePattern signature context [] pattern [] afterTarget
  let (generatedMatcher, afterMatcher) ←
    elaborate signature.base context matcher afterPattern
  let (generatedBody, next) ←
    elaborate signature.base
      (Pattern.extendContext generatedPattern.bindings context)
      body afterMatcher
  pure
    (Generated.fromMatchAll generatedTarget generatedPattern
      generatedMatcher generatedBody,
      next)

/-- Close the constraints of a synthesized user pattern.  This auxiliary
entry point is useful for testing failures that arise only during solving,
such as the occurs check. -/
def inferPattern
    (signature : FrozenSignature) (context : Context)
    (arguments : PatternContext) (pattern : Pattern) : Option Dual := do
  let (generated, _) ← elaboratePattern signature context arguments pattern []
    context.initialSupply
  let closed ← inferGeneratedUsing unify
    ⟨generated.dual.target, generated.hard, generated.pending⟩
  pure
    { capability := generated.dual.capability.apply closed.substitution.cap
      target := closed.target }

/-- Public executable type inference for one M4 match site. -/
def inferMatchAll
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (pattern : Pattern) (body : Expr) : Option Ty := do
  let (generated, _) ← elaborateMatchAll signature context target matcher
    pattern body context.initialSupply
  let closed ← inferGeneratedUsing unify generated
  pure closed.target

mutual

/-- Relational pattern synthesis parameterized by the relation used for
embedded value expressions. -/
inductive PatternElaboratesUsing
    (ExpressionElaborates : M4ExpressionElaborationRelation) :
    FrozenSignature → Context → PatternContext → Pattern → List Ty →
      Supply → GeneratedPattern → Supply → Prop where
  | var {signature context arguments bindings supply} :
      PatternElaboratesUsing ExpressionElaborates signature context arguments
        .var bindings supply
        ⟨⟨.var ⟨supply.cap⟩, .var ⟨supply.ty⟩⟩,
          bindings ++ [.var ⟨supply.ty⟩], [], []⟩
        ⟨supply.ty + 1, supply.cap + 1⟩
  | wild {signature context arguments bindings supply} :
      PatternElaboratesUsing ExpressionElaborates signature context arguments
        .wild bindings supply
        ⟨(⟨.var ⟨supply.cap⟩, .var ⟨supply.ty⟩⟩ : Dual),
          bindings, [], []⟩ ⟨supply.ty + 1, supply.cap + 1⟩
  | value {signature context arguments expression bindings supply generated
      afterExpression} :
      ExpressionElaborates (Pattern.extendContext bindings context) expression
        supply generated afterExpression →
      PatternElaboratesUsing ExpressionElaborates signature context arguments
        (.value expression) bindings supply
        ⟨(⟨.var ⟨afterExpression.cap⟩, generated.target⟩ : Dual),
          bindings, generated.hard, generated.pending⟩
        ⟨afterExpression.ty, afterExpression.cap + 1⟩
  | ctor {signature context arguments constructor fields bindings supply
      scheme generatedFields next}
      (lookup : signature.lookupPatternConstructor constructor = some scheme)
      (arity : fields.length = scheme.fields.length)
      (fieldsElaboration : PatternsElaborateUsing ExpressionElaborates signature
        context arguments fields bindings (scheme.instantiate supply).2
        generatedFields next) :
      PatternElaboratesUsing ExpressionElaborates signature context arguments
        (.ctor constructor fields) bindings supply
        ⟨(scheme.instantiate supply).1.result, generatedFields.bindings,
          generatedFields.hard ++ Pattern.fieldEquations generatedFields.duals
            (scheme.instantiate supply).1.fields,
          generatedFields.pending⟩ next
  | tuple {signature context arguments items bindings supply generatedItems next}
      (itemsElaboration : PatternsElaborateUsing ExpressionElaborates signature
        context arguments items bindings supply generatedItems next) :
      PatternElaboratesUsing ExpressionElaborates signature context arguments
        (.tuple items) bindings supply
        ⟨(⟨.prod (Dual.capabilities generatedItems.duals),
          .prod (Dual.targets generatedItems.duals)⟩ : Dual),
          generatedItems.bindings, generatedItems.hard,
          generatedItems.pending⟩ next
  | embed {signature context arguments index bindings supply dual}
      (lookup : arguments[index]? = some dual) :
      PatternElaboratesUsing ExpressionElaborates signature context arguments
        (.embed index) bindings supply ⟨dual, bindings, [], []⟩ supply
  | app {signature context arguments function fields bindings supply scheme
      generatedFields next}
      (lookup : signature.lookupPatternFunction function = some scheme)
      (arity : fields.length = scheme.fields.length)
      (fieldsElaboration : PatternsElaborateUsing ExpressionElaborates signature
        context arguments fields bindings (scheme.instantiate supply).2
        generatedFields next) :
      PatternElaboratesUsing ExpressionElaborates signature context arguments
        (.app function fields) bindings supply
        ⟨(scheme.instantiate supply).1.result, generatedFields.bindings,
          generatedFields.hard ++ Pattern.fieldEquations generatedFields.duals
            (scheme.instantiate supply).1.fields,
          generatedFields.pending⟩ next

inductive PatternsElaborateUsing
    (ExpressionElaborates : M4ExpressionElaborationRelation) :
    FrozenSignature → Context → PatternContext → List Pattern → List Ty →
      Supply → GeneratedPatterns → Supply → Prop where
  | nil {signature context arguments bindings supply} :
      PatternsElaborateUsing ExpressionElaborates signature context arguments
        [] bindings supply ⟨[], bindings, [], []⟩ supply
  | cons {signature context arguments pattern patterns bindings supply
      generatedPattern afterPattern generatedPatterns next}
      (head : PatternElaboratesUsing ExpressionElaborates signature context
        arguments pattern bindings supply generatedPattern afterPattern)
      (tail : PatternsElaborateUsing ExpressionElaborates signature context
        arguments patterns generatedPattern.bindings afterPattern
        generatedPatterns next) :
      PatternsElaborateUsing ExpressionElaborates signature context arguments
        (pattern :: patterns) bindings supply
        ⟨generatedPattern.dual :: generatedPatterns.duals,
          generatedPatterns.bindings,
          generatedPattern.hard ++ generatedPatterns.hard,
          generatedPattern.pending ++ generatedPatterns.pending⟩ next

end

/-- Callback-parametric relational mirror of `matchAll`. -/
inductive MatchAllElaboratesUsing
    (ExpressionElaborates : M4ExpressionElaborationRelation)
    (signature : FrozenSignature) (context : Context) :
    Expr → Expr → Pattern → Expr → Supply → Generated → Supply → Prop where
  | mk {target matcher pattern body supply generatedTarget afterTarget
      generatedPattern afterPattern generatedMatcher afterMatcher generatedBody next}
      (targetElaboration : ExpressionElaborates context target supply
        generatedTarget afterTarget)
      (patternElaboration : PatternElaboratesUsing ExpressionElaborates signature
        context [] pattern [] afterTarget generatedPattern afterPattern)
      (matcherElaboration : ExpressionElaborates context matcher afterPattern
        generatedMatcher afterMatcher)
      (bodyElaboration : ExpressionElaborates
        (Pattern.extendContext generatedPattern.bindings context) body
        afterMatcher generatedBody next) :
      MatchAllElaboratesUsing ExpressionElaborates signature context target
        matcher pattern body supply
        (Generated.fromMatchAll generatedTarget generatedPattern generatedMatcher
          generatedBody) next

mutual

/-- Independent relational user-pattern synthesis. -/
inductive PatternElaborates :
    FrozenSignature → Context → PatternContext → Pattern → List Ty →
      Supply → GeneratedPattern → Supply → Prop where
  | var {signature context arguments bindings supply} :
      PatternElaborates signature context arguments .var bindings supply
        ⟨⟨.var ⟨supply.cap⟩, .var ⟨supply.ty⟩⟩,
          bindings ++ [.var ⟨supply.ty⟩], [], []⟩
        ⟨supply.ty + 1, supply.cap + 1⟩
  | wild {signature context arguments bindings supply} :
      PatternElaborates signature context arguments .wild bindings supply
        ⟨(⟨.var ⟨supply.cap⟩, .var ⟨supply.ty⟩⟩ : Dual),
          bindings, [], []⟩
        ⟨supply.ty + 1, supply.cap + 1⟩
  | value {signature context arguments expression bindings supply
      generated afterExpression} :
      Elaborates signature.base (Pattern.extendContext bindings context)
        expression supply generated afterExpression →
      PatternElaborates signature context arguments (.value expression)
        bindings supply
        ⟨(⟨.var ⟨afterExpression.cap⟩, generated.target⟩ : Dual),
          bindings, generated.hard, generated.pending⟩
        ⟨afterExpression.ty, afterExpression.cap + 1⟩
  | ctor {signature context arguments constructor fields bindings supply
      scheme generatedFields next}
      (lookup : signature.lookupPatternConstructor constructor = some scheme)
      (arity : fields.length = scheme.fields.length)
      (fieldsElaboration :
        PatternsElaborate signature context arguments fields bindings
          (scheme.instantiate supply).2 generatedFields next) :
      PatternElaborates signature context arguments (.ctor constructor fields)
        bindings supply
        ⟨(scheme.instantiate supply).1.result, generatedFields.bindings,
          generatedFields.hard ++
            Pattern.fieldEquations generatedFields.duals
              (scheme.instantiate supply).1.fields,
          generatedFields.pending⟩ next
  | tuple {signature context arguments items bindings supply generatedItems next}
      (itemsElaboration :
        PatternsElaborate signature context arguments items bindings supply
          generatedItems next) :
      PatternElaborates signature context arguments (.tuple items) bindings
        supply
        ⟨(⟨.prod (Dual.capabilities generatedItems.duals),
            .prod (Dual.targets generatedItems.duals)⟩ : Dual),
          generatedItems.bindings, generatedItems.hard,
          generatedItems.pending⟩ next
  | embed {signature context arguments index bindings supply dual}
      (lookup : arguments[index]? = some dual) :
      PatternElaborates signature context arguments (.embed index) bindings
        supply ⟨dual, bindings, [], []⟩ supply
  | app {signature context arguments function fields bindings supply scheme
      generatedFields next}
      (lookup : signature.lookupPatternFunction function = some scheme)
      (arity : fields.length = scheme.fields.length)
      (fieldsElaboration :
        PatternsElaborate signature context arguments fields bindings
          (scheme.instantiate supply).2 generatedFields next) :
      PatternElaborates signature context arguments (.app function fields)
        bindings supply
        ⟨(scheme.instantiate supply).1.result, generatedFields.bindings,
          generatedFields.hard ++
            Pattern.fieldEquations generatedFields.duals
              (scheme.instantiate supply).1.fields,
          generatedFields.pending⟩ next

/-- Relational left-to-right list synthesis. -/
inductive PatternsElaborate :
    FrozenSignature → Context → PatternContext → List Pattern →
      List Ty → Supply → GeneratedPatterns → Supply → Prop where
  | nil {signature context arguments bindings supply} :
      PatternsElaborate signature context arguments [] bindings supply
        ⟨[], bindings, [], []⟩ supply
  | cons {signature context arguments pattern patterns bindings supply
      generatedPattern afterPattern generatedPatterns next} :
      PatternElaborates signature context arguments pattern bindings supply
        generatedPattern afterPattern →
      PatternsElaborate signature context arguments patterns
        generatedPattern.bindings afterPattern generatedPatterns next →
      PatternsElaborate signature context arguments (pattern :: patterns)
        bindings supply
        ⟨generatedPattern.dual :: generatedPatterns.duals,
          generatedPatterns.bindings,
          generatedPattern.hard ++ generatedPatterns.hard,
          generatedPattern.pending ++ generatedPatterns.pending⟩ next

end

/-- Independent relational rule for one match site. -/
inductive MatchAllElaborates
    (signature : FrozenSignature) (context : Context) :
    Expr → Expr → Pattern → Expr → Supply → Generated → Supply → Prop where
  | mk {target matcher pattern body supply generatedTarget afterTarget
      generatedPattern afterPattern generatedMatcher afterMatcher
      generatedBody next}
      (targetElaboration : Elaborates signature.base context target supply
        generatedTarget afterTarget)
      (patternElaboration : PatternElaborates signature context [] pattern []
        afterTarget generatedPattern afterPattern)
      (matcherElaboration : Elaborates signature.base context matcher afterPattern
        generatedMatcher afterMatcher)
      (bodyElaboration : Elaborates signature.base
        (Pattern.extendContext generatedPattern.bindings context)
        body afterMatcher generatedBody next) :
      MatchAllElaborates signature context target matcher pattern body supply
        (Generated.fromMatchAll generatedTarget generatedPattern
          generatedMatcher generatedBody)
        next

mutual

/-- Executable pattern synthesis is sound for the relational judgment. -/
theorem elaboratePattern_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {arguments : PatternContext} {pattern : Pattern}
    {bindings : List Ty} {supply next : Supply}
    {generated : GeneratedPattern}
    (success : elaboratePattern signature context arguments pattern bindings supply =
      some (generated, next)) :
    PatternElaborates signature context arguments pattern bindings supply
      generated next := by
  cases pattern with
  | var =>
      simp [elaboratePattern] at success
      rcases success with ⟨rfl, rfl⟩
      exact .var
  | wild =>
      simp [elaboratePattern] at success
      rcases success with ⟨rfl, rfl⟩
      exact .wild
  | value expression =>
      cases expressionResult : elaborate signature.base
          (Pattern.extendContext bindings context) expression supply with
      | none => simp [elaboratePattern, expressionResult] at success
      | some output =>
          cases output with
          | mk generatedExpression afterExpression =>
              have equality :
                  (⟨(⟨.var ⟨afterExpression.cap⟩,
                      generatedExpression.target⟩ : Dual),
                      bindings, generatedExpression.hard,
                      generatedExpression.pending⟩,
                    ⟨afterExpression.ty, afterExpression.cap + 1⟩) =
                    (generated, next) :=
                Option.some.inj (by
                  simpa [elaboratePattern, expressionResult] using success)
              injection equality with generatedEquality nextEquality
              subst generated
              subst next
              exact .value
                (elaborate_sound wellFormed.baseWellFormed expressionResult)
  | ctor constructor fields =>
      cases lookup : signature.lookupPatternConstructor constructor with
      | none => simp [elaboratePattern, lookup] at success
      | some scheme =>
          by_cases arity : fields.length = scheme.fields.length
          · cases fieldsResult : elaboratePatterns signature context arguments
                fields bindings (scheme.instantiate supply).2 with
            | none => simp [elaboratePattern, lookup, arity, fieldsResult] at success
            | some output =>
                cases output with
                | mk generatedFields afterFields =>
                    simp [elaboratePattern, lookup, arity, fieldsResult]
                      at success
                    rcases success with ⟨rfl, rfl⟩
                    exact .ctor lookup arity
                      (elaboratePatterns_sound wellFormed fieldsResult)
          · simp [elaboratePattern, lookup, arity] at success
  | tuple items =>
      cases itemsResult : elaboratePatterns signature context arguments items
          bindings supply with
      | none => simp [elaboratePattern, itemsResult] at success
      | some output =>
          cases output with
          | mk generatedItems afterItems =>
              simp [elaboratePattern, itemsResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .tuple (elaboratePatterns_sound wellFormed itemsResult)
  | embed index =>
      cases lookup : arguments[index]? with
      | none => simp [elaboratePattern, lookup] at success
      | some dual =>
          have equality : (⟨dual, bindings, [], []⟩, supply) =
              (generated, next) := Option.some.inj (by
            simpa [elaboratePattern, lookup] using success)
          injection equality with generatedEquality nextEquality
          subst generated
          subst next
          exact .embed lookup
  | app function fields =>
      cases lookup : signature.lookupPatternFunction function with
      | none => simp [elaboratePattern, lookup] at success
      | some scheme =>
          by_cases arity : fields.length = scheme.fields.length
          · cases fieldsResult : elaboratePatterns signature context arguments
                fields bindings (scheme.instantiate supply).2 with
            | none => simp [elaboratePattern, lookup, arity, fieldsResult] at success
            | some output =>
                cases output with
                | mk generatedFields afterFields =>
                    simp [elaboratePattern, lookup, arity, fieldsResult]
                      at success
                    rcases success with ⟨rfl, rfl⟩
                    exact .app lookup arity
                      (elaboratePatterns_sound wellFormed fieldsResult)
          · simp [elaboratePattern, lookup, arity] at success
termination_by pattern.complexity * 2 + 1
decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

/-- Executable pattern-list synthesis is sound. -/
theorem elaboratePatterns_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {arguments : PatternContext} {patterns : List Pattern}
    {bindings : List Ty} {supply next : Supply}
    {generated : GeneratedPatterns}
    (success : elaboratePatterns signature context arguments patterns bindings supply =
      some (generated, next)) :
    PatternsElaborate signature context arguments patterns bindings supply
      generated next := by
  cases patterns with
  | nil =>
      have equality : (⟨[], bindings, [], []⟩, supply) =
          (generated, next) := Option.some.inj (by
        simpa [elaboratePatterns] using success)
      injection equality with generatedEquality nextEquality
      subst generated
      subst next
      exact .nil
  | cons pattern patterns =>
      cases patternResult : elaboratePattern signature context arguments pattern
          bindings supply with
      | none => simp [elaboratePatterns, patternResult] at success
      | some output =>
          cases output with
          | mk generatedPattern afterPattern =>
              cases patternsResult : elaboratePatterns signature context arguments
                  patterns generatedPattern.bindings afterPattern with
              | none =>
                  simp [elaboratePatterns, patternResult, patternsResult] at success
              | some restOutput =>
                  cases restOutput with
                  | mk generatedPatterns afterPatterns =>
                      simp [elaboratePatterns, patternResult, patternsResult]
                        at success
                      rcases success with ⟨rfl, rfl⟩
                      exact .cons
                        (elaboratePattern_sound wellFormed patternResult)
                        (elaboratePatterns_sound wellFormed patternsResult)
termination_by Pattern.listComplexity patterns * 2
decreasing_by all_goals simp_wf <;> subst_vars <;> simp <;> omega

end


/-- Executable match-site elaboration is sound. -/
theorem elaborateMatchAll_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {target matcher : Expr} {pattern : Pattern} {body : Expr}
    {supply next : Supply} {generated : Generated}
    (success : elaborateMatchAll signature context target matcher pattern body supply =
      some (generated, next)) :
    MatchAllElaborates signature context target matcher pattern body supply
      generated next := by
  cases targetResult : elaborate signature.base context target supply with
  | none => simp [elaborateMatchAll, targetResult] at success
  | some targetOutput =>
      rcases targetOutput with ⟨generatedTarget, afterTarget⟩
      cases patternResult : elaboratePattern signature context [] pattern []
          afterTarget with
      | none => simp [elaborateMatchAll, targetResult, patternResult] at success
      | some patternOutput =>
          rcases patternOutput with ⟨generatedPattern, afterPattern⟩
          cases matcherResult : elaborate signature.base context matcher
              afterPattern with
          | none =>
              simp [elaborateMatchAll, targetResult, patternResult,
                matcherResult] at success
          | some matcherOutput =>
              rcases matcherOutput with ⟨generatedMatcher, afterMatcher⟩
              cases bodyResult : elaborate signature.base
                  (Pattern.extendContext generatedPattern.bindings context)
                  body afterMatcher with
              | none =>
                  simp [elaborateMatchAll, targetResult, patternResult,
                    matcherResult, bodyResult] at success
              | some bodyOutput =>
                  rcases bodyOutput with ⟨generatedBody, afterBody⟩
                  simp [elaborateMatchAll, targetResult, patternResult,
                    matcherResult, bodyResult] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact .mk
                    (elaborate_sound wellFormed.baseWellFormed targetResult)
                    (elaboratePattern_sound wellFormed patternResult)
                    (elaborate_sound wellFormed.baseWellFormed matcherResult)
                    (elaborate_sound wellFormed.baseWellFormed bodyResult)

mutual

theorem elaboratePatternUsingFuel_sound
    {elaborateExpression : M4ExpressionElaborator}
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {arguments : PatternContext} {pattern : Pattern}
    {bindings : List Ty} {supply next : Supply} {generated : GeneratedPattern}
    (success : elaboratePatternUsingFuel elaborateExpression signature context
      arguments fuel pattern bindings supply = some (generated, next)) :
    PatternElaboratesUsing ExpressionElaborates signature context arguments
      pattern bindings supply generated next := by
  cases fuel with
  | zero => simp [elaboratePatternUsingFuel] at success
  | succ fuel =>
    cases pattern with
    | var =>
        simp [elaboratePatternUsingFuel] at success
        rcases success with ⟨rfl, rfl⟩
        exact .var
    | wild =>
        simp [elaboratePatternUsingFuel] at success
        rcases success with ⟨rfl, rfl⟩
        exact .wild
    | value expression =>
        cases expressionResult : elaborateExpression
            (Pattern.extendContext bindings context) expression supply with
        | none => simp [elaboratePatternUsingFuel, expressionResult] at success
        | some output =>
            rcases output with ⟨generatedExpression, afterExpression⟩
            simp [elaboratePatternUsingFuel, expressionResult] at success
            rcases success with ⟨rfl, rfl⟩
            exact .value (expressionSound expressionResult)
    | ctor constructor fields =>
        cases lookup : signature.lookupPatternConstructor constructor with
        | none => simp [elaboratePatternUsingFuel, lookup] at success
        | some scheme =>
            by_cases arity : fields.length = scheme.fields.length
            · cases fieldsResult : elaboratePatternsUsingFuel elaborateExpression
                  signature context arguments fuel fields bindings
                  (scheme.instantiate supply).2 with
              | none =>
                  simp [elaboratePatternUsingFuel, lookup, arity, fieldsResult] at success
              | some output =>
                  rcases output with ⟨generatedFields, afterFields⟩
                  simp [elaboratePatternUsingFuel, lookup, arity, fieldsResult] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact .ctor lookup arity
                    (elaboratePatternsUsingFuel_sound expressionSound wellFormed
                      fieldsResult)
            · simp [elaboratePatternUsingFuel, lookup, arity] at success
    | tuple items =>
        cases itemsResult : elaboratePatternsUsingFuel elaborateExpression signature
            context arguments fuel items bindings supply with
        | none => simp [elaboratePatternUsingFuel, itemsResult] at success
        | some output =>
            rcases output with ⟨generatedItems, afterItems⟩
            simp [elaboratePatternUsingFuel, itemsResult] at success
            rcases success with ⟨rfl, rfl⟩
            exact .tuple (elaboratePatternsUsingFuel_sound expressionSound wellFormed
              itemsResult)
    | embed index =>
        cases lookup : arguments[index]? with
        | none => simp [elaboratePatternUsingFuel, lookup] at success
        | some dual =>
            simp [elaboratePatternUsingFuel, lookup] at success
            rcases success with ⟨rfl, rfl⟩
            exact .embed lookup
    | app function fields =>
        cases lookup : signature.lookupPatternFunction function with
        | none => simp [elaboratePatternUsingFuel, lookup] at success
        | some scheme =>
            by_cases arity : fields.length = scheme.fields.length
            · cases fieldsResult : elaboratePatternsUsingFuel elaborateExpression
                  signature context arguments fuel fields bindings
                  (scheme.instantiate supply).2 with
              | none =>
                  simp [elaboratePatternUsingFuel, lookup, arity, fieldsResult] at success
              | some output =>
                  rcases output with ⟨generatedFields, afterFields⟩
                  simp [elaboratePatternUsingFuel, lookup, arity, fieldsResult] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact .app lookup arity
                    (elaboratePatternsUsingFuel_sound expressionSound wellFormed
                      fieldsResult)
            · simp [elaboratePatternUsingFuel, lookup, arity] at success
termination_by fuel

theorem elaboratePatternsUsingFuel_sound
    {elaborateExpression : M4ExpressionElaborator}
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {arguments : PatternContext} {patterns : List Pattern}
    {bindings : List Ty} {supply next : Supply} {generated : GeneratedPatterns}
    (success : elaboratePatternsUsingFuel elaborateExpression signature context
      arguments fuel patterns bindings supply = some (generated, next)) :
    PatternsElaborateUsing ExpressionElaborates signature context arguments
      patterns bindings supply generated next := by
  cases fuel with
  | zero => simp [elaboratePatternsUsingFuel] at success
  | succ fuel =>
    cases patterns with
    | nil =>
        simp [elaboratePatternsUsingFuel] at success
        rcases success with ⟨rfl, rfl⟩
        exact .nil
    | cons pattern patterns =>
        cases patternResult : elaboratePatternUsingFuel elaborateExpression signature
            context arguments fuel pattern bindings supply with
        | none => simp [elaboratePatternsUsingFuel, patternResult] at success
        | some output =>
            rcases output with ⟨generatedPattern, afterPattern⟩
            cases patternsResult : elaboratePatternsUsingFuel elaborateExpression
                signature context arguments fuel patterns generatedPattern.bindings
                afterPattern with
            | none =>
                simp [elaboratePatternsUsingFuel, patternResult, patternsResult] at success
            | some rest =>
                rcases rest with ⟨generatedPatterns, afterPatterns⟩
                simp [elaboratePatternsUsingFuel, patternResult, patternsResult] at success
                rcases success with ⟨rfl, rfl⟩
                exact .cons
                  (elaboratePatternUsingFuel_sound expressionSound wellFormed
                    patternResult)
                  (elaboratePatternsUsingFuel_sound expressionSound wellFormed
                    patternsResult)
termination_by fuel
end

theorem elaboratePatternUsing_sound
    {elaborateExpression : M4ExpressionElaborator}
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {arguments : PatternContext} {pattern : Pattern}
    {bindings : List Ty} {supply next : Supply} {generated : GeneratedPattern}
    (success : elaboratePatternUsing elaborateExpression signature context
      arguments pattern bindings supply = some (generated, next)) :
    PatternElaboratesUsing ExpressionElaborates signature context arguments
      pattern bindings supply generated next :=
  elaboratePatternUsingFuel_sound expressionSound wellFormed success

theorem elaboratePatternsUsing_sound
    {elaborateExpression : M4ExpressionElaborator}
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {arguments : PatternContext} {patterns : List Pattern}
    {bindings : List Ty} {supply next : Supply} {generated : GeneratedPatterns}
    (success : elaboratePatternsUsing elaborateExpression signature context
      arguments patterns bindings supply = some (generated, next)) :
    PatternsElaborateUsing ExpressionElaborates signature context arguments
      patterns bindings supply generated next :=
  elaboratePatternsUsingFuel_sound expressionSound wellFormed success

theorem elaborateMatchAllUsing_sound
    {elaborateExpression : M4ExpressionElaborator}
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {target matcher : Expr} {pattern : Pattern} {body : Expr}
    {supply next : Supply} {generated : Generated}
    (success : elaborateMatchAllUsing elaborateExpression signature context
      target matcher pattern body supply = some (generated, next)) :
    MatchAllElaboratesUsing ExpressionElaborates signature context target matcher
      pattern body supply generated next := by
  cases targetResult : elaborateExpression context target supply with
  | none => simp [elaborateMatchAllUsing, targetResult] at success
  | some output =>
      rcases output with ⟨generatedTarget, afterTarget⟩
      cases patternResult : elaboratePatternUsing elaborateExpression signature
          context [] pattern [] afterTarget with
      | none => simp [elaborateMatchAllUsing, targetResult, patternResult] at success
      | some output =>
          rcases output with ⟨generatedPattern, afterPattern⟩
          cases matcherResult : elaborateExpression context matcher afterPattern with
          | none =>
              simp [elaborateMatchAllUsing, targetResult, patternResult,
                matcherResult] at success
          | some output =>
              rcases output with ⟨generatedMatcher, afterMatcher⟩
              cases bodyResult : elaborateExpression
                  (Pattern.extendContext generatedPattern.bindings context) body
                  afterMatcher with
              | none =>
                  simp [elaborateMatchAllUsing, targetResult, patternResult,
                    matcherResult, bodyResult] at success
              | some output =>
                  rcases output with ⟨generatedBody, afterBody⟩
                  simp [elaborateMatchAllUsing, targetResult, patternResult,
                    matcherResult, bodyResult] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact .mk (expressionSound targetResult)
                    (elaboratePatternUsing_sound expressionSound wellFormed
                      patternResult)
                    (expressionSound matcherResult)
                    (expressionSound bodyResult)

end TypePM.Source
