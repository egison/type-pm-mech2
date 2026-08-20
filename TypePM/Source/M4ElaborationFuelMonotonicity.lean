import TypePM.Source.M4RecursiveElaboration

/-!
# Monotonicity of M4 elaboration fuel

The fuel attached to `M4.ElaboratesFuel` is only a recursion bound.  This
module proves that increasing it preserves every derivation, including the
expression callbacks nested in patterns, matcher clauses, and `matchFirst`
arms.
-/

namespace TypePM.Source

namespace M4

theorem ItemsElaborateUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      ElaboratesFuel signature sourceFuel context expression start generated finish →
      ElaboratesFuel signature targetFuel context expression start generated finish)
    {context items start generated finish}
    (bound : Expr.listComplexity items ≤ targetFuel)
    (derivation : ItemsElaborateUsing (ElaboratesFuel signature sourceFuel)
      context items start generated finish) :
    ItemsElaborateUsing (ElaboratesFuel signature targetFuel) context items start
      generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons item items start generatedItem afterItem generatedItems finish head tail ih =>
      exact .cons (normalize (by simp at bound ⊢; omega) head)
        (ih (by simp at bound ⊢; omega))

theorem CallElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      ElaboratesFuel signature sourceFuel context expression start generated finish →
      ElaboratesFuel signature targetFuel context expression start generated finish)
    {context accumulated arguments start generated finish}
    (bound : Expr.listComplexity arguments ≤ targetFuel)
    (derivation : CallElaboratesUsing (ElaboratesFuel signature sourceFuel)
      context accumulated arguments start generated finish) :
    CallElaboratesUsing (ElaboratesFuel signature targetFuel) context accumulated
      arguments start generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons accumulated argument arguments start generatedArgument afterArgument
      generated finish head tail ih =>
      exact .cons (normalize (by simp at bound ⊢; omega) head)
        (ih (by simp at bound ⊢; omega))

theorem ItemsElaborateUsing.map
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {context items start generated finish}
    (derivation : ItemsElaborateUsing left context items start generated finish) :
    ItemsElaborateUsing right context items start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction => exact .cons (transport head) induction

theorem CallElaboratesUsing.map
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {context accumulated arguments start generated finish}
    (derivation : CallElaboratesUsing left context accumulated arguments start
      generated finish) :
    CallElaboratesUsing right context accumulated arguments start generated
      finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction => exact .cons (transport head) induction

end M4

theorem FixElaboratesUsing.map
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {context expression start generated finish}
    (derivation : FixElaboratesUsing left context expression start generated
      finish) :
    FixElaboratesUsing right context expression start generated finish := by
  cases derivation with
  | fixE direct body => exact .fixE direct (transport body)

theorem FixElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context body start generated finish}
    (bound : body.complexity + 1 ≤ targetFuel)
    (derivation : FixElaboratesUsing (M4.ElaboratesFuel signature sourceFuel)
      context (.fixE body) start generated finish) :
    FixElaboratesUsing (M4.ElaboratesFuel signature targetFuel) context
      (.fixE body) start generated finish := by
  cases derivation with
  | fixE direct bodyElaboration =>
      exact .fixE direct (normalize bound bodyElaboration)

mutual

theorem PatternElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context arguments pattern bindings start generated finish}
    (bound : pattern.complexity ≤ targetFuel)
    (derivation : PatternElaboratesUsing (M4.ElaboratesFuel signature sourceFuel)
      signature context arguments pattern bindings start generated finish) :
    PatternElaboratesUsing (M4.ElaboratesFuel signature targetFuel) signature
      context arguments pattern bindings start generated finish := by
  cases derivation with
  | var => exact .var
  | wild => exact .wild
  | value expression =>
      exact .value (normalize (by simpa using bound) expression)
  | ctor lookup arity fields =>
      exact .ctor lookup arity
        (PatternsElaborateUsing.normalizeFuel normalize
          (by simp only [Pattern.complexity_ctor] at bound; omega) fields)
  | tuple items =>
      exact .tuple (PatternsElaborateUsing.normalizeFuel normalize
        (by simp only [Pattern.complexity_tuple] at bound; omega) items)
  | and left right =>
      exact .and
        (PatternElaboratesUsing.normalizeFuel normalize (by
          simp only [Pattern.complexity_and] at bound
          omega) left)
        (PatternElaboratesUsing.normalizeFuel normalize (by
          simp only [Pattern.complexity_and] at bound
          omega) right)
  | or left right bindingsEqual =>
      exact .or
        (PatternElaboratesUsing.normalizeFuel normalize (by
          simp only [Pattern.complexity_or] at bound
          omega) left)
        (PatternElaboratesUsing.normalizeFuel normalize (by
          simp only [Pattern.complexity_or] at bound
          omega) right)
        bindingsEqual
  | embed lookup => exact .embed lookup
  | app lookup arity fields =>
      exact .app lookup arity
        (PatternsElaborateUsing.normalizeFuel normalize
          (by simp only [Pattern.complexity_app] at bound; omega) fields)

theorem PatternsElaborateUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context arguments patterns bindings start generated finish}
    (bound : Pattern.listComplexity patterns ≤ targetFuel)
    (derivation : PatternsElaborateUsing (M4.ElaboratesFuel signature sourceFuel)
      signature context arguments patterns bindings start generated finish) :
    PatternsElaborateUsing (M4.ElaboratesFuel signature targetFuel) signature
      context arguments patterns bindings start generated finish := by
  cases derivation with
  | nil => exact .nil
  | @cons pattern patterns bindings start generatedPattern afterPattern
      generatedPatterns finish head tail =>
      exact .cons
        (PatternElaboratesUsing.normalizeFuel normalize (by
          simp only [Pattern.listComplexity_cons] at bound
          omega) head)
        (PatternsElaborateUsing.normalizeFuel normalize (by
          simp only [Pattern.listComplexity_cons] at bound
          omega) tail)

end

mutual

theorem PatternElaboratesUsing.map
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context arguments pattern bindings start generated finish}
    (derivation : PatternElaboratesUsing left signature context arguments pattern
      bindings start generated finish) :
    PatternElaboratesUsing right signature context arguments pattern bindings
      start generated finish := by
  cases derivation with
  | var => exact .var
  | wild => exact .wild
  | value expression => exact .value (transport expression)
  | ctor lookup arity fields =>
      exact .ctor lookup arity (PatternsElaborateUsing.map transport fields)
  | tuple items => exact .tuple (PatternsElaborateUsing.map transport items)
  | and left right =>
      exact .and (PatternElaboratesUsing.map transport left)
        (PatternElaboratesUsing.map transport right)
  | or left right bindingsEqual =>
      exact .or (PatternElaboratesUsing.map transport left)
        (PatternElaboratesUsing.map transport right) bindingsEqual
  | embed lookup => exact .embed lookup
  | app lookup arity fields =>
      exact .app lookup arity (PatternsElaborateUsing.map transport fields)

theorem PatternsElaborateUsing.map
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context arguments patterns bindings start generated finish}
    (derivation : PatternsElaborateUsing left signature context arguments patterns
      bindings start generated finish) :
    PatternsElaborateUsing right signature context arguments patterns bindings
      start generated finish := by
  cases derivation with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (PatternElaboratesUsing.map transport head)
        (PatternsElaborateUsing.map transport tail)

end

theorem MatchAllElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context target matcher pattern body start generated finish}
    (targetBound : target.complexity + 1 ≤ targetFuel)
    (matcherBound : matcher.complexity + 1 ≤ targetFuel)
    (patternBound : pattern.complexity ≤ targetFuel)
    (bodyBound : body.complexity + 1 ≤ targetFuel)
    (derivation : MatchAllElaboratesUsing
      (M4.ElaboratesFuel signature sourceFuel) signature context target matcher
      pattern body start generated finish) :
    MatchAllElaboratesUsing (M4.ElaboratesFuel signature targetFuel) signature
      context target matcher pattern body start generated finish := by
  cases derivation with
  | mk targetElaboration patternElaboration matcherElaboration bodyElaboration =>
      exact .mk (normalize targetBound targetElaboration)
        (PatternElaboratesUsing.normalizeFuel normalize patternBound
          patternElaboration)
        (normalize matcherBound matcherElaboration)
        (normalize bodyBound bodyElaboration)

theorem MatchAllElaboratesUsing.map
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context target matcher pattern body start generated finish}
    (derivation : MatchAllElaboratesUsing left signature context target matcher
      pattern body start generated finish) :
    MatchAllElaboratesUsing right signature context target matcher pattern body
      start generated finish := by
  cases derivation with
  | mk target pattern matcher body =>
      exact .mk (transport target) (PatternElaboratesUsing.map transport pattern)
        (transport matcher) (transport body)

namespace MatcherTyping

theorem CheckedExpressionElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context expression expected start generated finish}
    (bound : expression.complexity + 1 ≤ targetFuel)
    (derivation : CheckedExpressionElaboratesUsing
      (M4.ElaboratesFuel signature sourceFuel) context expression expected start
      generated finish) :
    CheckedExpressionElaboratesUsing (M4.ElaboratesFuel signature targetFuel)
      context expression expected start generated finish := by
  cases derivation with
  | mk expression => exact .mk (normalize bound expression)

theorem NextMatcherItemsElaborateUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context items holes start generated finish}
    (bound : Expr.listComplexity items ≤ targetFuel)
    (derivation : NextMatcherItemsElaborateUsing
      (M4.ElaboratesFuel signature sourceFuel) context items holes start generated
      finish) :
    NextMatcherItemsElaborateUsing (M4.ElaboratesFuel signature targetFuel)
      context items holes start generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons item items hole holes start generatedItem afterItem generatedItems
      finish head tail ih =>
      exact .cons (head.normalizeFuel normalize (by
        simp only [Expr.listComplexity_cons] at bound
        omega)) (ih (by
          simp only [Expr.listComplexity_cons] at bound
          omega))

theorem NextMatchersElaborateUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context expression holes start generated finish}
    (bound : expression.complexity + 1 ≤ targetFuel)
    (derivation : NextMatchersElaborateUsing
      (M4.ElaboratesFuel signature sourceFuel) context expression holes start
      generated finish) :
    NextMatchersElaborateUsing (M4.ElaboratesFuel signature targetFuel) context
      expression holes start generated finish := by
  cases derivation with
  | zero checked => exact .zero (checked.normalizeFuel normalize bound)
  | one checked => exact .one (checked.normalizeFuel normalize bound)
  | many components =>
      exact .many (components.normalizeFuel normalize (by
        simp only [Expr.complexity_tuple] at bound
        omega))

theorem MatcherArmElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context captures matcherTarget holes arm start generated finish}
    (bound : arm.complexity ≤ targetFuel)
    (derivation : MatcherArmElaboratesUsing
      (M4.ElaboratesFuel signature sourceFuel) DPatElaborates signature context
      captures matcherTarget holes arm start generated finish) :
    MatcherArmElaboratesUsing (M4.ElaboratesFuel signature targetFuel)
      DPatElaborates signature context captures matcherTarget holes arm start
      generated finish := by
  cases derivation with
  | mk header body =>
      exact .mk header (body.normalizeFuel normalize (by
        simpa only [MatcherArm.complexity_mk] using bound))

theorem MatcherArmsElaborateUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context captures matcherTarget holes arms start generated finish}
    (bound : MatcherArm.listComplexity arms ≤ targetFuel)
    (derivation : MatcherArmsElaborateUsing
      (M4.ElaboratesFuel signature sourceFuel) DPatElaborates signature context
      captures matcherTarget holes arms start generated finish) :
    MatcherArmsElaborateUsing (M4.ElaboratesFuel signature targetFuel)
      DPatElaborates signature context captures matcherTarget holes arms start
      generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons arm arms start generatedArm afterArm generatedArms finish head tail ih =>
      exact .cons (head.normalizeFuel normalize (by
        simp only [MatcherArm.listComplexity_cons] at bound
        omega)) (ih (by
          simp only [MatcherArm.listComplexity_cons] at bound
          omega))

theorem MatcherClauseElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context matcherTarget clause start generated finish}
    (bound : clause.complexity ≤ targetFuel)
    (derivation : MatcherClauseElaboratesUsing
      (M4.ElaboratesFuel signature sourceFuel) PPatElaborates DPatElaborates
      signature context matcherTarget clause start generated finish) :
    MatcherClauseElaboratesUsing (M4.ElaboratesFuel signature targetFuel)
      PPatElaborates DPatElaborates signature context matcherTarget clause start
      generated finish := by
  cases derivation with
  | mk shape header next arms =>
      exact .mk shape header (next.normalizeFuel normalize (by
        simp only [MatcherClause.complexity_mk] at bound
        omega)) (arms.normalizeFuel normalize (by
          simp only [MatcherClause.complexity_mk] at bound
          omega))

theorem MatcherClausesElaborateUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context matcherTarget clauses start generated finish}
    (bound : MatcherClause.listComplexity clauses ≤ targetFuel)
    (derivation : MatcherClausesElaborateUsing
      (M4.ElaboratesFuel signature sourceFuel) PPatElaborates DPatElaborates
      signature context matcherTarget clauses start generated finish) :
    MatcherClausesElaborateUsing (M4.ElaboratesFuel signature targetFuel)
      PPatElaborates DPatElaborates signature context matcherTarget clauses start
      generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons clause clauses start generatedClause afterClause generatedClauses
      finish head tail ih =>
      exact .cons (head.normalizeFuel normalize (by
        simp only [MatcherClause.listComplexity_cons] at bound
        omega)) (ih (by
          simp only [MatcherClause.listComplexity_cons] at bound
          omega))

theorem MatcherLiteralElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context clauses start generated finish}
    (bound : MatcherClause.listComplexity clauses ≤ targetFuel)
    (derivation : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel signature sourceFuel) PPatElaborates DPatElaborates
      signature context clauses start generated finish) :
    MatcherLiteralElaboratesUsing (M4.ElaboratesFuel signature targetFuel)
      PPatElaborates DPatElaborates signature context clauses start generated
      finish := by
  cases derivation with
  | mk checked clauses =>
      exact .mk checked (clauses.normalizeFuel normalize bound)

theorem CheckedExpressionElaboratesUsing.map
    {left right : ExpressionElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {context expression expected start generated finish}
    (derivation : CheckedExpressionElaboratesUsing left context expression
      expected start generated finish) :
    CheckedExpressionElaboratesUsing right context expression expected start
      generated finish := by
  cases derivation with
  | mk expression => exact .mk (transport expression)

theorem NextMatcherItemsElaborateUsing.map
    {left right : ExpressionElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {context items holes start generated finish}
    (derivation : NextMatcherItemsElaborateUsing left context items holes start
      generated finish) :
    NextMatcherItemsElaborateUsing right context items holes start generated
      finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (head.map transport) induction

theorem NextMatchersElaborateUsing.map
    {left right : ExpressionElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {context expression holes start generated finish}
    (derivation : NextMatchersElaborateUsing left context expression holes start
      generated finish) :
    NextMatchersElaborateUsing right context expression holes start generated
      finish := by
  cases derivation with
  | zero checked => exact .zero (checked.map transport)
  | one checked => exact .one (checked.map transport)
  | many components => exact .many (components.map transport)

theorem MatcherArmElaboratesUsing.map
    {left right : ExpressionElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context captures matcherTarget holes arm start generated finish}
    (derivation : MatcherArmElaboratesUsing left dpatRelation signature context
      captures matcherTarget holes arm start generated finish) :
    MatcherArmElaboratesUsing right dpatRelation signature context captures
      matcherTarget holes arm start generated finish := by
  cases derivation with
  | mk header body => exact .mk header (body.map transport)

theorem MatcherArmsElaborateUsing.map
    {left right : ExpressionElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context captures matcherTarget holes arms start generated finish}
    (derivation : MatcherArmsElaborateUsing left dpatRelation signature context
      captures matcherTarget holes arms start generated finish) :
    MatcherArmsElaborateUsing right dpatRelation signature context captures
      matcherTarget holes arms start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction => exact .cons (head.map transport) induction

theorem MatcherClauseElaboratesUsing.map
    {left right : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context matcherTarget clause start generated finish}
    (derivation : MatcherClauseElaboratesUsing left ppatRelation dpatRelation
      signature context matcherTarget clause start generated finish) :
    MatcherClauseElaboratesUsing right ppatRelation dpatRelation signature
      context matcherTarget clause start generated finish := by
  cases derivation with
  | mk shape header next arms =>
      exact .mk shape header (next.map transport) (arms.map transport)

theorem MatcherClausesElaborateUsing.map
    {left right : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context matcherTarget clauses start generated finish}
    (derivation : MatcherClausesElaborateUsing left ppatRelation dpatRelation
      signature context matcherTarget clauses start generated finish) :
    MatcherClausesElaborateUsing right ppatRelation dpatRelation signature
      context matcherTarget clauses start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction => exact .cons (head.map transport) induction

theorem MatcherLiteralElaboratesUsing.map
    {left right : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context clauses start generated finish}
    (derivation : MatcherLiteralElaboratesUsing left ppatRelation dpatRelation
      signature context clauses start generated finish) :
    MatcherLiteralElaboratesUsing right ppatRelation dpatRelation signature
      context clauses start generated finish := by
  cases derivation with
  | mk checked clauses => exact .mk checked (clauses.map transport)

end MatcherTyping

namespace MatchFirstTyping

theorem TailElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context targetType matcherType expectedResult arms start generated finish}
    (bound : MatchFirstArm.listComplexity arms ≤ targetFuel)
    (derivation : TailElaboratesUsing (M4.ElaboratesFuel signature sourceFuel)
      signature context targetType matcherType expectedResult arms start generated
      finish) :
    TailElaboratesUsing (M4.ElaboratesFuel signature targetFuel) signature context
      targetType matcherType expectedResult arms start generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons pattern body arms start generatedPattern afterPattern generatedBody
      afterBody generatedTail finish patternElaboration bodyElaboration
      tailElaboration ih =>
      have armBound : pattern.complexity + body.complexity + 1 ≤ targetFuel := by
        simp only [MatchFirstArm.listComplexity_cons,
          MatchFirstArm.complexity_mk] at bound
        omega
      exact .cons
        (PatternElaboratesUsing.normalizeFuel normalize (by omega)
          patternElaboration)
        (normalize (by omega) bodyElaboration)
        (ih (by
          simp only [MatchFirstArm.listComplexity_cons] at bound
          omega))

theorem ArmsElaborateUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context targetType matcherType arms start generated finish}
    (bound : MatchFirstArm.listComplexity arms ≤ targetFuel)
    (derivation : ArmsElaborateUsing (M4.ElaboratesFuel signature sourceFuel)
      signature context targetType matcherType arms start generated finish) :
    ArmsElaborateUsing (M4.ElaboratesFuel signature targetFuel) signature context
      targetType matcherType arms start generated finish := by
  cases derivation with
  | @cons pattern body arms start generatedPattern afterPattern generatedBody
      afterBody generatedTail finish patternElaboration bodyElaboration tail =>
      have armBound : pattern.complexity + body.complexity + 1 ≤ targetFuel := by
        simp only [MatchFirstArm.listComplexity_cons,
          MatchFirstArm.complexity_mk] at bound
        omega
      exact .cons
        (PatternElaboratesUsing.normalizeFuel normalize (by omega)
          patternElaboration)
        (normalize (by omega) bodyElaboration)
        (tail.normalizeFuel normalize (by
          simp only [MatchFirstArm.listComplexity_cons] at bound
          omega))

theorem ElaboratesUsing.normalizeFuel
    {signature : FrozenSignature} {sourceFuel targetFuel : Nat}
    (normalize : ∀ {context expression start generated finish},
      expression.complexity + 1 ≤ targetFuel →
      M4.ElaboratesFuel signature sourceFuel context expression start generated finish →
      M4.ElaboratesFuel signature targetFuel context expression start generated finish)
    {context target matcher arms start generated finish}
    (targetBound : target.complexity + 1 ≤ targetFuel)
    (matcherBound : matcher.complexity + 1 ≤ targetFuel)
    (armsBound : MatchFirstArm.listComplexity arms ≤ targetFuel)
    (derivation : ElaboratesUsing (M4.ElaboratesFuel signature sourceFuel)
      signature context (.matchFirst target matcher arms) start generated finish) :
    ElaboratesUsing (M4.ElaboratesFuel signature targetFuel) signature context
      (.matchFirst target matcher arms) start generated finish := by
  cases derivation with
  | matchFirst exhaustive targetElaboration matcherElaboration armsElaboration =>
      exact .matchFirst exhaustive (normalize targetBound targetElaboration)
        (normalize matcherBound matcherElaboration)
        (armsElaboration.normalizeFuel normalize armsBound)

theorem TailElaboratesUsing.map
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context targetType matcherType expectedResult arms start generated
      finish}
    (derivation : TailElaboratesUsing left signature context targetType
      matcherType expectedResult arms start generated finish) :
    TailElaboratesUsing right signature context targetType matcherType
      expectedResult arms start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons pattern body tail induction =>
      exact .cons (PatternElaboratesUsing.map transport pattern)
        (transport body) induction

theorem ArmsElaborateUsing.map
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context targetType matcherType arms start generated finish}
    (derivation : ArmsElaborateUsing left signature context targetType matcherType
      arms start generated finish) :
    ArmsElaborateUsing right signature context targetType matcherType arms start
      generated finish := by
  cases derivation with
  | cons pattern body tail =>
      exact .cons (PatternElaboratesUsing.map transport pattern)
        (transport body) (tail.map transport)

theorem ElaboratesUsing.map
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression start generated finish},
      left context expression start generated finish →
        right context expression start generated finish)
    {signature context expression start generated finish}
    (derivation : ElaboratesUsing left signature context expression start
      generated finish) :
    ElaboratesUsing right signature context expression start generated finish := by
  cases derivation with
  | matchFirst exhaustive target matcher arms =>
      exact .matchFirst exhaustive (transport target) (transport matcher)
        (arms.map transport)

end MatchFirstTyping

namespace M4

/-- Increasing the structural fuel preserves an M4 relational elaboration. -/
theorem ElaboratesFuel.mono
    {signature : FrozenSignature} {smaller larger : Nat} {context : Context}
    {expression : Expr} {start finish : Supply} {generated : Generated}
    (fuel_le : smaller ≤ larger)
    (derivation : ElaboratesFuel signature smaller context expression start
      generated finish) :
    ElaboratesFuel signature larger context expression start generated finish := by
  induction smaller generalizing larger context expression start generated finish with
  | zero => simp [ElaboratesFuel] at derivation
  | succ smaller induction =>
      cases larger with
      | zero => omega
      | succ larger =>
          have childFuelLe : smaller ≤ larger := Nat.succ_le_succ_iff.mp fuel_le
          have transport := fun {context expression start generated finish}
              (child : ElaboratesFuel signature smaller context expression start
                generated finish) =>
            induction childFuelLe child
          cases expression <;> simp only [ElaboratesFuel] at derivation ⊢
          · exact derivation
          · exact derivation
          · exact derivation
          · obtain ⟨body, bodyDerivation, equality⟩ := derivation
            exact ⟨body, transport bodyDerivation, equality⟩
          · obtain ⟨function, afterFunction, argument, afterArgument,
              functionDerivation, argumentDerivation, generatedEquality,
              finishEquality⟩ := derivation
            exact ⟨function, afterFunction, argument, afterArgument,
              transport functionDerivation, transport argumentDerivation,
              generatedEquality, finishEquality⟩
          · obtain ⟨items, itemsDerivation, equality⟩ := derivation
            exact ⟨items, itemsDerivation.map transport, equality⟩
          · obtain ⟨value, afterValue, valueDerivation, closure, body,
              absorbing, bodyDerivation, equality⟩ := derivation
            exact ⟨value, afterValue, transport valueDerivation, closure, body,
              absorbing, transport bodyDerivation, equality⟩
          · obtain ⟨scheme, lookup, arity, closed, call⟩ := derivation
            exact ⟨scheme, lookup, arity, closed, call.map transport⟩
          · obtain ⟨scheme, lookup, arity, closed, call⟩ := derivation
            exact ⟨scheme, lookup, arity, closed, call.map transport⟩
          · exact derivation.map transport
          · exact derivation.map transport
          · exact derivation.map transport
          · exact derivation.map transport
          · exact derivation.map transport

/-- Every arbitrary-fuel derivation can be truncated to the public
syntax-complexity fuel.  The proof normalizes each callback expression first
and then uses monotonicity only to reach the fuel supplied by its parent. -/
theorem ElaboratesFuel.normalize
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {start finish : Supply} {generated : Generated}
    (derivation : ElaboratesFuel signature fuel context expression start
      generated finish) :
    ElaboratesFuel signature (expression.complexity + 1) context expression
      start generated finish := by
  induction fuel generalizing context expression start generated finish with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel induction =>
      cases expression <;> simp only [ElaboratesFuel] at derivation ⊢
      · exact derivation
      · exact derivation
      · exact derivation
      · obtain ⟨generatedBody, bodyDerivation, equality⟩ := derivation
        exact ⟨generatedBody, induction bodyDerivation, equality⟩
      · obtain ⟨generatedFunction, afterFunction, generatedArgument,
          afterArgument, functionDerivation, argumentDerivation,
          generatedEquality, finishEquality⟩ := derivation
        exact ⟨generatedFunction, afterFunction, generatedArgument,
          afterArgument,
          (induction functionDerivation).mono (by
            simp only [Expr.complexity_app]
            omega),
          (induction argumentDerivation).mono (by
            simp only [Expr.complexity_app]
            omega),
          generatedEquality, finishEquality⟩
      · obtain ⟨generatedItems, itemsDerivation, equality⟩ := derivation
        exact ⟨generatedItems,
          itemsDerivation.normalizeFuel
            (fun bound child => (induction child).mono bound) (by
              simp only [Expr.complexity_tuple]
              omega),
          equality⟩
      · obtain ⟨generatedValue, afterValue, valueDerivation, closure,
          generatedBody, absorbing, bodyDerivation, equality⟩ := derivation
        exact ⟨generatedValue, afterValue,
          (induction valueDerivation).mono (by
            simp only [Expr.complexity_letE]
            omega), closure, generatedBody,
          absorbing, (induction bodyDerivation).mono (by
            simp only [Expr.complexity_letE]
            omega), equality⟩
      · obtain ⟨scheme, lookup, arity, closed, call⟩ := derivation
        exact ⟨scheme, lookup, arity, closed,
          call.normalizeFuel
            (fun bound child => (induction child).mono bound) (by
              simp only [Expr.complexity_ctor]
              omega)⟩
      · obtain ⟨scheme, lookup, arity, closed, call⟩ := derivation
        exact ⟨scheme, lookup, arity, closed,
          call.normalizeFuel
            (fun bound child => (induction child).mono bound) (by
              simp only [Expr.complexity_prim]
              omega)⟩
      · exact derivation.normalizeFuel
          (fun bound child => (induction child).mono bound) (by
            simp only [Expr.complexity_ifE, Expr.listComplexity_cons,
              Expr.listComplexity_nil]
            omega)
      · exact derivation.normalizeFuel
          (fun bound child => (induction child).mono bound) (by
            simp only [Expr.complexity_fixE]
            omega)
      · exact derivation.normalizeFuel
          (fun bound child => (induction child).mono bound) (by
            simp only [Expr.complexity_matcher]
            omega)
      · exact derivation.normalizeFuel
          (fun bound child => (induction child).mono bound)
          (by simp only [Expr.complexity_matchAll]; omega)
          (by simp only [Expr.complexity_matchAll]; omega)
          (by simp only [Expr.complexity_matchAll]; omega)
          (by simp only [Expr.complexity_matchAll]; omega)
      · exact derivation.normalizeFuel
          (fun bound child => (induction child).mono bound)
          (by simp only [Expr.complexity_matchFirst]; omega)
          (by simp only [Expr.complexity_matchFirst]; omega)
          (by simp only [Expr.complexity_matchFirst]; omega)

/-- Hiding the fuel witness does not enlarge the relation: the public
existential relation is exactly the relation at the syntax-complexity fuel
chosen by the executable elaborator. -/
theorem Elaborates.iff_at_complexity
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {start finish : Supply} {generated : Generated} :
    Elaborates signature context expression start generated finish ↔
      ElaboratesFuel signature (expression.complexity + 1) context expression
        start generated finish := by
  constructor
  · rintro ⟨fuel, derivation⟩
    exact derivation.normalize
  · intro derivation
    exact ⟨expression.complexity + 1, derivation⟩

/-- A derivation can be replayed at the public syntax-complexity fuel whenever
that fuel is at least its original witness. -/
theorem ElaboratesFuel.at_complexity
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {start finish : Supply} {generated : Generated}
    (fuel_le : fuel ≤ expression.complexity + 1)
    (derivation : ElaboratesFuel signature fuel context expression start
      generated finish) :
    ElaboratesFuel signature (expression.complexity + 1) context expression
      start generated finish :=
  derivation.mono fuel_le

end M4

end TypePM.Source
