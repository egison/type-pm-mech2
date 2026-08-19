import TypePM.Source.M4MatchFirstTyping

/-!
# Paper 1 source programs

This module records the displayed seven-clause `multiset` definition as the
actual final `Source` syntax.  It contains no callback oracle and no shortened
runtime primitive standing in for the matcher body.

`multisetDefinition` is open in exactly one outer value, the already defined
`list` matcher constructor.  Entering `fixE` then places the element matcher
at index zero, the recursive `multiset` function at index one, and that outer
`list` function at index two.  Matcher-arm data variables and pattern-pattern
captures are prepended by the operational semantics in source order.
-/

namespace TypePM.Source.Paper1Programs

open TypePM.Source

/-- Source-level constructor encoding of an ordinary finite list. -/
def sourceList : List Expr → Expr
  | [] => .ctor DataCtor.nil []
  | head :: tail => .ctor DataCtor.cons [head, sourceList tail]

def unit : Expr := .tuple []

private def nilPattern : Pattern := .ctor PatternCtor.nil []

private def consPattern (head tail : Pattern) : Pattern :=
  .ctor PatternCtor.cons [head, tail]

private def joinPattern (left right : Pattern) : Pattern :=
  .ctor PatternCtor.join [left, right]

/-! ## Clause 1: `[] as ()` -/

def nilClause : MatcherClause :=
  .mk (.ctor PatternCtor.nil []) (.tuple [])
    [.mk (.ctor DataCtor.nil []) (sourceList [unit]),
      .mk .wild (sourceList [])]

/-! ## Clause 2: `$ :: _ as m` -/

def headOnlyClause : MatcherClause :=
  .mk (.ctor PatternCtor.cons [.hole, .wild]) (.var 0)
    [.mk .var (.var 0)]

/-! ## Clause 3: `#$value :: $ as multiset m` -/

def valueConsClause : MatcherClause :=
  .mk (.ctor PatternCtor.cons [.capture, .hole])
    (.app (.var 1) (.var 0))
    [.mk .var
      (.ifE (.prim .member [.var 1, .var 0])
        (sourceList [.prim .deleteFirst [.var 1, .var 0]])
        (sourceList []))]

/-! ## Clause 4: `$ :: $ as (m, multiset m)` -/

def generalConsBody : Expr :=
  .matchAll (.var 0) (.app (.var 3) (.var 1))
    (joinPattern .var (consPattern .var .var))
    (.tuple [.var 1, .prim .append [.var 0, .var 2]])

def generalConsClause : MatcherClause :=
  .mk (.ctor PatternCtor.cons [.hole, .hole])
    (.tuple [.var 0, .app (.var 1) (.var 0)])
    [.mk .var generalConsBody]

/-! ## Clause 5: `$ ++ $ as (multiset m, multiset m)` -/

def splitTailResults : Expr :=
  .matchAll (.var 1) (.app (.var 3) (.var 2))
    (joinPattern .var .var) (.tuple [.var 0, .var 1])

/-- `\(heads,tails) -> (heads, current :: tails)`.

Inside the desugared `matchFirst`, indices zero and one are the tuple fields;
the current list head is index four. -/
def putCurrentRight : Expr :=
  Expr.tuplePatternLambda
    (.tuple [.var 0,
      .ctor DataCtor.cons [.var 4, .var 1]])

/-- `\(heads,tails) -> (current :: heads, tails)`. -/
def putCurrentLeft : Expr :=
  Expr.tuplePatternLambda
    (.tuple [.ctor DataCtor.cons [.var 4, .var 0],
      .var 1])

def joinConsBody : Expr :=
  .letE splitTailResults
    (.prim .append
      [.prim .map [putCurrentRight, .var 0],
        .prim .map [putCurrentLeft, .var 0]])

def joinClause : MatcherClause :=
  .mk (.ctor PatternCtor.join [.hole, .hole])
    (.tuple
      [.app (.var 1) (.var 0),
        .app (.var 1) (.var 0)])
    [.mk (.ctor DataCtor.nil [])
        (sourceList [.tuple [sourceList [], sourceList []]]),
      .mk (.ctor DataCtor.cons [.var, .var]) joinConsBody]

/-! ## Clause 6: `#$value as ()` -/

def wholeValueTarget : Expr := .tuple [.var 1, .var 0]

def wholeValueMatcher : Expr :=
  .tuple
    [.app (.var 4) (.var 2),
      .app (.var 3) (.var 2)]

def wholeValueSuccess : Expr := sourceList [unit]

def wholeValuePattern : Pattern :=
  .tuple
    [consPattern .var .var,
      consPattern (.value (.var 0)) (.value (.var 1))]

def wholeValueBody : Expr :=
  .matchFirst wholeValueTarget wholeValueMatcher
    [.mk (.tuple [nilPattern, nilPattern]) wholeValueSuccess,
      .mk wholeValuePattern wholeValueSuccess,
      .mk (.tuple [.wild, .wild]) (sourceList [])]

def wholeValueClause : MatcherClause :=
  .mk .capture (.tuple []) [.mk .var wholeValueBody]

/-! ## Clause 7: catch-all `$ as something` -/

def catchAllClause : MatcherClause :=
  .mk .hole .something [.mk .var (sourceList [.var 0])]

/-- The exact source-ordered clause list displayed in Paper 1. -/
def multisetClauses : List MatcherClause :=
  [nilClause, headOnlyClause, valueConsClause, generalConsClause,
    joinClause, wholeValueClause, catchAllClause]

/-- `multiset` as a unary recursive function, open in the outer `list`
matcher constructor at source index zero. -/
def multisetDefinition : Expr := .fixE (.matcher multisetClauses)

/-- A closed two-argument form useful for end-to-end execution: the first
argument supplies `list`, and the second supplies the element matcher `m`. -/
def multisetWithListArgument : Expr := .lam multisetDefinition

/-! ## Source-defined library `list` matcher

Paper 1 treats `list` as a library matcher.  The executable regressions keep
that dependency in the source language instead of replacing it with a hidden
multiset primitive.  The final catch-all delegates variable, wildcard, and
value patterns to `something`; the structural clauses handle `nil` and
`cons` in source order. -/

def listMatcherNilClause : MatcherClause := nilClause

def listMatcherConsClause : MatcherClause :=
  .mk (.ctor PatternCtor.cons [.hole, .hole])
    (.tuple [.var 0, .app (.var 1) (.var 0)])
    [.mk (.ctor DataCtor.cons [.var, .var])
      (sourceList [.tuple [.var 0, .var 1]])]

def listSplitTailResults : Expr :=
  .matchAll (.var 1) (.app (.var 3) (.var 2))
    (joinPattern .var .var) (.tuple [.var 0, .var 1])

def putCurrentAtPrefixEnd : Expr :=
  Expr.tuplePatternLambda
    (.tuple [.ctor DataCtor.cons [.var 4, .var 0], .var 1])

def listJoinConsBody : Expr :=
  .letE listSplitTailResults
    (.prim .append
      [sourceList
        [.tuple
          [sourceList [],
            .ctor DataCtor.cons [.var 1, .var 2]]],
        .prim .map [putCurrentAtPrefixEnd, .var 0]])

/-- Prefix/suffix splits in increasing prefix length. -/
def listMatcherJoinClause : MatcherClause :=
  .mk (.ctor PatternCtor.join [.hole, .hole])
    (.tuple
      [.app (.var 1) (.var 0),
        .app (.var 1) (.var 0)])
    [.mk (.ctor DataCtor.nil [])
        (sourceList [.tuple [sourceList [], sourceList []]]),
      .mk (.ctor DataCtor.cons [.var, .var]) listJoinConsBody]

def listMatcherCatchAllClause : MatcherClause := catchAllClause

def listMatcherClauses : List MatcherClause :=
  [listMatcherNilClause, listMatcherConsClause, listMatcherJoinClause,
    listMatcherCatchAllClause]

/-- Closed unary library matcher constructor `list`. -/
def listMatcherDefinition : Expr := .fixE (.matcher listMatcherClauses)

/-- Closed Paper-1 `multiset` constructor with its source-defined `list`
dependency supplied. -/
def closedMultisetDefinition : Expr :=
  .app multisetWithListArgument listMatcherDefinition

/-- The concrete `multiset something` matcher used by several listings. -/
def multisetSomething : Expr := .app closedMultisetDefinition .something

theorem multiset_clause_count : multisetClauses.length = 7 := by
  rfl

theorem list_matcher_clause_count : listMatcherClauses.length = 4 := by
  rfl

theorem multiset_clause_shapes_checked :
    MatcherClause.checkShapes Paper1FrozenSignature.signature
      multisetClauses = true := by
  simp [MatcherClause.checkShapes, MatcherClause.toShape, MatcherArm.toHeader,
    MatcherClauseShapes.check, MatcherClauseShapes.catchAllLast,
    MatcherClauseShapes.isCatchAll, MatcherClauseShape.check,
    MatcherArmHeader.check, MatcherArmHeader.canonical,
    HoleConvention.ofCount, PPat.shapeOK, PPat.shapesOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
    DPat.constructorArity?, multisetClauses, nilClause, headOnlyClause,
    valueConsClause, generalConsClause, joinClause, wholeValueClause,
    catchAllClause, ConstructorSchemes.listNil, ConstructorSchemes.listCons,
    ListPatternSchemes.nil, ListPatternSchemes.cons, ListPatternSchemes.join,
    PolyDataTypes.list]

theorem list_matcher_clause_shapes_checked :
    MatcherClause.checkShapes Paper1FrozenSignature.signature
      listMatcherClauses = true := by
  simp [MatcherClause.checkShapes, MatcherClause.toShape, MatcherArm.toHeader,
    MatcherClauseShapes.check, MatcherClauseShapes.catchAllLast,
    MatcherClauseShapes.isCatchAll, MatcherClauseShape.check,
    MatcherArmHeader.check, MatcherArmHeader.canonical,
    HoleConvention.ofCount, PPat.shapeOK, PPat.shapesOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
    DPat.constructorArity?, listMatcherClauses, listMatcherNilClause,
    listMatcherConsClause, listMatcherJoinClause, listMatcherCatchAllClause,
    nilClause,
    catchAllClause, ConstructorSchemes.listNil, ConstructorSchemes.listCons,
    ListPatternSchemes.nil, ListPatternSchemes.cons, ListPatternSchemes.join,
    PolyDataTypes.list]

end TypePM.Source.Paper1Programs
