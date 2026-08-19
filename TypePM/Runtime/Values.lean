import TypePM.Source.Syntax
import TypePM.Runtime.Environment
import TypePM.Runtime.GroundValue

/-!
# Runtime values

This module implements the complete type-erased value grammar from Paper 1.
A function closure records whether it is recursive, its body, and the
newest-first environment present when it was created.  A matcher closure
records its definition environment, the original ordered clause list, and
the suffix not yet tried.  Keeping both clause lists makes source-order
dispatch explicit and lets later runtime typing identify the checked matcher
literal.

`structuralEq` is deliberately narrower than equality of Lean values.  It is
structural only on integers, constructor applications, and tuples, and is
false for closures, matcher closures, and `something`, exactly as required by
value-pattern matching.  It never compares or deduplicates matcher branches.
-/

namespace TypePM.Runtime

/-- Whether a function closure was created by `lam` or `fixE`.  With nameless
source syntax a Boolean-like tag is sufficient: recursive application puts
the closure itself at the de Bruijn position reserved by `fixE`. -/
inductive ClosureKind where
  | plain
  | recursive
deriving Repr, DecidableEq

/-- Type-erased runtime values for all M5 source forms. -/
inductive Value where
  | int (value : Int)
  | data (constructor : DataCtor) (arguments : List Value)
  | tuple (items : List Value)
  | closure (kind : ClosureKind) (environment : List Value)
      (body : Source.Expr)
  | matcherV (environment : List Value)
      (original remaining : List Source.MatcherClause)
  | something
deriving Repr

/-- The concrete runtime environment used by expression evaluation. -/
abbrev ValueEnvironment := Environment Value

namespace Value

/-- Construct a non-recursive function closure. -/
def plainClosure (environment : ValueEnvironment)
    (body : Source.Expr) : Value :=
  .closure .plain environment body

/-- Construct a recursive function closure. -/
def recursiveClosure (environment : ValueEnvironment)
    (body : Source.Expr) : Value :=
  .closure .recursive environment body

/-- Construct a fresh matcher closure.  No clause has been tried, so the
remaining suffix is initially the whole source-ordered definition. -/
def matcherClosure (environment : ValueEnvironment)
    (clauses : List Source.MatcherClause) : Value :=
  .matcherV environment clauses clauses

/-- Advance a matcher cursor by one source clause.  Non-matchers and matcher
closures with no remaining clause have no successor. -/
def advanceMatcher : Value → Option Value
  | .matcherV environment original (_ :: remaining) =>
      some (.matcherV environment original remaining)
  | _ => none

/-- The matcher cursor is a suffix of the original source clause list. -/
def MatcherCursorValid : Value → Prop
  | .matcherV _ original remaining =>
      ∃ tried, original = tried ++ remaining
  | _ => False

theorem matcherClosure_cursorValid
    (environment : ValueEnvironment)
    (clauses : List Source.MatcherClause) :
    (matcherClosure environment clauses).MatcherCursorValid := by
  exact ⟨[], rfl⟩

theorem advanceMatcher_cursorValid
    {value next : Value}
    (valid : value.MatcherCursorValid)
    (advanced : value.advanceMatcher = some next) :
    next.MatcherCursorValid := by
  cases value with
  | matcherV environment original remaining =>
      cases remaining with
      | nil => simp [advanceMatcher] at advanced
      | cons clause rest =>
          simp only [advanceMatcher, Option.some.injEq] at advanced
          subst next
          rcases valid with ⟨tried, originalEq⟩
          exact ⟨tried ++ [clause], by simp [originalEq, List.append_assoc]⟩
  | _ => simp [advanceMatcher] at advanced

mutual

  /-- Paper-1 structural equality on values. -/
  def structuralEq : Value → Value → Bool
    | .int left, .int right => left == right
    | .data leftConstructor leftArguments,
        .data rightConstructor rightArguments =>
        leftConstructor == rightConstructor &&
          structuralEqList leftArguments rightArguments
    | .tuple leftItems, .tuple rightItems =>
        structuralEqList leftItems rightItems
    | _, _ => false

  /-- Left-to-right structural comparison of child sequences. -/
  def structuralEqList : List Value → List Value → Bool
    | [], [] => true
    | left :: leftTail, right :: rightTail =>
        structuralEq left right && structuralEqList leftTail rightTail
    | _, _ => false

end

@[simp] theorem structuralEq_int (left right : Int) :
    structuralEq (.int left) (.int right) = (left == right) := by
  rfl

@[simp] theorem structuralEq_closure_false
    (kind : ClosureKind) (environment : ValueEnvironment)
    (body : Source.Expr) (other : Value) :
    structuralEq (.closure kind environment body) other = false := by
  rfl

@[simp] theorem structuralEq_matcherV_false
    (environment : ValueEnvironment)
    (original remaining : List Source.MatcherClause) (other : Value) :
    structuralEq (.matcherV environment original remaining) other = false := by
  rfl

@[simp] theorem structuralEq_something_false (other : Value) :
    structuralEq .something other = false := by
  rfl

mutual

  /-- Embed a closed ground datum into the complete runtime value type. -/
  def ofGround : GroundValue → Value
    | .int value => .int value
    | .data constructor arguments =>
        .data constructor (groundValuesToValues arguments)
    | .tuple items => .tuple (groundValuesToValues items)

  /-- Embed a finite ground child sequence, preserving its order. -/
  def groundValuesToValues : GroundValues → List Value
    | .nil => []
    | .cons head tail => ofGround head :: groundValuesToValues tail

end

mutual

  /-- Every embedded ground value is structurally equal to itself.  This is
  separate from Lean equality because the corresponding statement is false
  for the three non-ground runtime forms. -/
  theorem structuralEq_ofGround_self : ∀ value : GroundValue,
      structuralEq (ofGround value) (ofGround value) = true
    | .int value => by simp [ofGround]
    | .data constructor arguments => by
        simp [ofGround, structuralEq,
          structuralEqList_groundValues_self arguments]
    | .tuple items => by
        simp [ofGround, structuralEq,
          structuralEqList_groundValues_self items]

  theorem structuralEqList_groundValues_self : ∀ values : GroundValues,
      structuralEqList (groundValuesToValues values)
        (groundValuesToValues values) = true
    | .nil => rfl
    | .cons head tail => by
        simp [groundValuesToValues, structuralEqList,
          structuralEq_ofGround_self head,
          structuralEqList_groundValues_self tail]

end

mutual

  /-- Project a complete runtime value to the closed ground fragment.  The
  projection fails on closures, matcher closures, and `something`, including
  when one occurs below a data constructor or tuple. -/
  def toGround? : Value → Option GroundValue
    | .int value => some (.int value)
    | .data constructor arguments =>
        (valuesToGroundValues? arguments).map (.data constructor)
    | .tuple items =>
        (valuesToGroundValues? items).map GroundValue.tuple
    | .closure _ _ _ | .matcherV _ _ _ | .something => none

  /-- Project a left-to-right sequence of complete values to ground children. -/
  def valuesToGroundValues? : List Value → Option GroundValues
    | [] => some .nil
    | head :: tail => do
        let groundHead ← toGround? head
        let groundTail ← valuesToGroundValues? tail
        pure (.cons groundHead groundTail)

end

mutual

  theorem toGround?_ofGround : ∀ value : GroundValue,
      toGround? (ofGround value) = some value
    | .int _ => rfl
    | .data constructor arguments => by
        simp [ofGround, toGround?,
          valuesToGroundValues?_groundValuesToValues arguments]
    | .tuple items => by
        simp [ofGround, toGround?,
          valuesToGroundValues?_groundValuesToValues items]

  theorem valuesToGroundValues?_groundValuesToValues :
      ∀ values : GroundValues,
        valuesToGroundValues? (groundValuesToValues values) = some values
    | .nil => rfl
    | .cons head tail => by
        simp [groundValuesToValues, valuesToGroundValues?,
          toGround?_ofGround head,
          valuesToGroundValues?_groundValuesToValues tail]

end

theorem ofGround_injective : Function.Injective ofGround := by
  intro left right equality
  have projected := congrArg toGround? equality
  simpa [toGround?_ofGround] using projected

/-- Runtime lookup is exactly ordinary newest-first environment lookup. -/
theorem lookup_iff_getElem?
    (environment : ValueEnvironment) (index : Nat) (value : Value) :
    Lookup environment index value ↔ environment[index]? = some value := by
  exact (getElem?_eq_some_iff_lookup environment index value).symm

end Value

end TypePM.Runtime
