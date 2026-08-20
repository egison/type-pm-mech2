import TypePM.Source.Elaboration
import TypePM.Source.M4MatcherClauseShapeRegression

/-!
# M4 direct-syntax regressions

These examples make every final M4 source constructor concrete and connect an
actual matcher clause to its expression-free shape.  The M3 expression entry
point remains deliberately closed to `fixE`, matcher literals, `matchAll`,
and `matchFirst`.
`M4Elaboration` now supplies separate executable and relational pattern and
single-match-site judgments; recursive M4 expression elaboration remains a
later checkpoint.
-/

namespace TypePM.Source.M4SyntaxRegression

def successorPatternFunction : PatternFunName := ⟨"successor"⟩

def nestedPattern : Pattern :=
  .tuple
    [ .var,
      .wild,
      .value (.prim PrimOp.add [.var 0, .lit 1]),
      .ctor PatternCtor.cons [.embed 0, .app successorPatternFunction [.var]] ]

def catchAllArm : MatcherArm :=
  .mk (.tuple [.var, .wild]) (.var 0)

def catchAllClause : MatcherClause :=
  .mk .hole (.tuple [.something]) [catchAllArm]

def matcherExpression : Expr :=
  .matcher [catchAllClause]

def matchAllExpression : Expr :=
  .matchAll (.tuple [.lit 1, .lit 2]) matcherExpression nestedPattern (.var 0)

def recursiveMatcherExpression : Expr :=
  .fixE matcherExpression

/-- Actual clause syntax erases to canonical, nameless header metadata. -/
theorem catchAllClause_shape_exact :
    catchAllClause.toShape =
      { header := .hole
        holeConvention := .one
        arms := [MatcherArmHeader.canonical (.tuple [.var, .wild])] } := by
  simp [catchAllClause, catchAllArm, MatcherClause.toShape, MatcherArm.toHeader,
    HoleConvention.ofCount, PPat.holeCount]

/-- The direct clause-list checker reuses the execution-free checker and
accepts a canonical last catch-all. -/
theorem catchAllClause_shape_checked :
    MatcherClause.checkShapes Paper1FrozenSignature.signature
      [catchAllClause] = true := by
  simp [MatcherClause.checkShapes, catchAllClause, catchAllArm,
    MatcherClause.toShape,
    MatcherArm.toHeader, MatcherClauseShapes.check,
    MatcherClauseShapes.catchAllLast, MatcherClauseShapes.isCatchAll,
    MatcherClauseShape.check, MatcherArmHeader.check,
    MatcherArmHeader.canonical, HoleConvention.ofCount, PPat.shapeOK,
    PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, PPat.holeCount, DPat.shapeOK, DPat.shapesOK,
    DPat.bindingCount, DPat.bindingsInSourceOrder]

theorem elaborate_fixE_none
    (signature : Signature) (context : Context) (body : Expr)
    (supply : Supply) :
    elaborate signature context (.fixE body) supply = none := by
  simp [elaborate]

theorem elaborate_matcher_none
    (signature : Signature) (context : Context) (clauses : List MatcherClause)
    (supply : Supply) :
    elaborate signature context (.matcher clauses) supply = none := by
  simp [elaborate]

/-- The older M3 entry point stays honest; M4 clients use
`elaborateMatchAll` instead. -/
theorem elaborate_matchAll_none
    (signature : Signature) (context : Context) (target matcher : Expr)
    (pattern : Pattern) (body : Expr) (supply : Supply) :
    elaborate signature context (.matchAll target matcher pattern body)
      supply = none := by
  simp [elaborate]

theorem elaborate_matchFirst_none
    (signature : Signature) (context : Context) (target matcher : Expr)
    (arms : List MatchFirstArm) (fallback : Expr) (supply : Supply) :
    elaborate signature context (.matchFirst target matcher arms fallback) supply =
      none := by
  simp [elaborate]

/-- There is no declarative constructor that could disguise an unimplemented
M4 typing rule. -/
theorem fixE_not_relationally_elaborated
    (signature : Signature) (context : Context) (body : Expr)
    (supply next : Supply) (generated : Generated) :
    ¬ Elaborates signature context (.fixE body) supply generated next := by
  intro derivation
  cases derivation

theorem matcher_not_relationally_elaborated
    (signature : Signature) (context : Context) (clauses : List MatcherClause)
    (supply next : Supply) (generated : Generated) :
    ¬ Elaborates signature context (.matcher clauses) supply generated next := by
  intro derivation
  cases derivation

theorem matchAll_not_relationally_elaborated
    (signature : Signature) (context : Context) (target matcher : Expr)
    (pattern : Pattern) (body : Expr) (supply next : Supply)
    (generated : Generated) :
    ¬ Elaborates signature context (.matchAll target matcher pattern body)
      supply generated next := by
  intro derivation
  cases derivation

theorem matchFirst_not_relationally_elaborated
    (signature : Signature) (context : Context) (target matcher : Expr)
    (arms : List MatchFirstArm) (fallback : Expr) (supply next : Supply)
    (generated : Generated) :
    ¬ Elaborates signature context (.matchFirst target matcher arms fallback)
      supply generated next := by
  intro derivation
  cases derivation

end TypePM.Source.M4SyntaxRegression
