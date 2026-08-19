import TypePM.Source.MatcherClauseShape

/-!
# Source syntax through M4

The public source language is separate from the verified M1 let-free block
syntax.  This avoids treating a polymorphic context as a monomorphic M1
context while retaining all M1 constraint and solver infrastructure.  The
four declarations below form one direct, mutually recursive abstract syntax
tree: matcher literals contain clauses, clause bodies contain expressions,
and value patterns contain expressions.  There is intentionally no opaque
extension node.
-/

namespace TypePM.Source

mutual

  /-- Source expressions through M4.  M5 execution is defined over this final
  constructor set and does not extend the source language. -/
  inductive Expr where
    | var (index : Nat)
    | lit (value : Int)
    | something
    | lam (body : Expr)
    | app (function argument : Expr)
    | tuple (items : List Expr)
    | letE (value body : Expr)
    | ctor (constructor : DataCtor) (arguments : List Expr)
    | prim (operation : PrimOp) (arguments : List Expr)
    | ifE (condition thenBranch elseBranch : Expr)
    | fixE (body : Expr)
    | matcher (clauses : List MatcherClause)
    | matchAll (target matcher : Expr) (pattern : Pattern) (body : Expr)
  deriving Repr

  /-- A source pattern.  `embed index` refers to a pattern argument by its
  nameless source-order index. -/
  inductive Pattern where
    | var
    | wild
    | value (expression : Expr)
    | ctor (constructor : PatternCtor) (fields : List Pattern)
    | tuple (items : List Pattern)
    | embed (index : Nat)
    | app (function : PatternFunName) (arguments : List Pattern)
  deriving Repr

  /-- One matcher clause.  Captures in `header` are made available to
  `nextMatchers` in left-to-right source order; the clause's data-pattern arms
  are likewise ordered. -/
  inductive MatcherClause where
    | mk (header : PPat) (nextMatchers : Expr) (arms : List MatcherArm)
  deriving Repr

  /-- One ordered data-pattern arm and its source expression body.  Variables
  in `header` are nameless and bind the body in left-to-right source order. -/
  inductive MatcherArm where
    | mk (header : DPat) (body : Expr)
  deriving Repr

end

namespace MatcherArm

def header : MatcherArm → DPat
  | .mk header _ => header

def body : MatcherArm → Expr
  | .mk _ body => body

/-- The execution-free header metadata corresponding to an actual arm. -/
def toHeader : MatcherArm → MatcherArmHeader
  | .mk header _ => .canonical header

@[simp] theorem toHeader_pattern (arm : MatcherArm) :
    arm.toHeader.pattern = arm.header := by
  cases arm
  rfl

@[simp] theorem toHeader_bindingOrder (arm : MatcherArm) :
    arm.toHeader.bindingOrder = arm.header.bindingsInSourceOrder := by
  cases arm
  rfl

end MatcherArm

namespace MatcherClause

def header : MatcherClause → PPat
  | .mk header _ _ => header

def nextMatchers : MatcherClause → Expr
  | .mk _ nextMatchers _ => nextMatchers

def arms : MatcherClause → List MatcherArm
  | .mk _ _ arms => arms

/-- Erase clause expressions to the already checked execution-free shape.
The hole convention and binding orders are derived rather than user supplied,
so the two representations cannot disagree on those fields. -/
def toShape : MatcherClause → MatcherClauseShape
  | .mk header _ arms =>
      { header := header
        holeConvention := HoleConvention.ofCount header.holeCount
        arms := arms.map MatcherArm.toHeader }

/-- Check the expression-free shape of a complete ordered clause list.  This
does not type-check or execute any stored expression. -/
def checkShapes
    (signature : FrozenSignature) (clauses : List MatcherClause) : Bool :=
  MatcherClauseShapes.check signature (clauses.map toShape)

@[simp] theorem toShape_header (clause : MatcherClause) :
    clause.toShape.header = clause.header := by
  cases clause
  rfl

@[simp] theorem toShape_holeConvention (clause : MatcherClause) :
    clause.toShape.holeConvention =
      HoleConvention.ofCount clause.header.holeCount := by
  cases clause
  rfl

@[simp] theorem toShape_arms (clause : MatcherClause) :
    clause.toShape.arms = clause.arms.map MatcherArm.toHeader := by
  cases clause
  rfl

end MatcherClause

end TypePM.Source
