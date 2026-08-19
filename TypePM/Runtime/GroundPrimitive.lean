import TypePM.Primitive
import TypePM.Runtime.FuelResult
import TypePM.Runtime.GroundValue
import TypePM.Runtime.OrderedChoiceAdequacy

/-!
# Executable ground primitive fragments

These functions execute only the closed data fragment represented by
`GroundValue`.  They are primitive delta rules, not an evaluator for
`Source.Expr`.  In particular, `map` receives the later evaluator's function
application as a callback because `GroundValue` deliberately has no closures.

Malformed arity, a non-integer argument to `add`, and a non-list argument to a
list primitive return `FuelResult.stuck`.  A `map` callback's `timeout` or
`stuck` result is propagated without being confused with malformed data.
-/

namespace TypePM.Runtime

namespace GroundPrimitive

open GroundValue FuelResult

/-- Execute integer addition on exactly two integer arguments. -/
def evalAdd : List GroundValue → FuelResult GroundValue
  | [.int left, .int right] => .ok (.int (left + right))
  | _ => .stuck

/-- Execute list append on two canonical list encodings. -/
def evalAppend : List GroundValue → FuelResult GroundValue
  | [left, right] =>
      match left.viewList, right.viewList with
      | some leftItems, some rightItems =>
          .ok (buildList (leftItems ++ rightItems))
      | _, _ => .stuck
  | _ => .stuck

/-- Test structural membership in a canonical list encoding. -/
def evalMember : List GroundValue → FuelResult GroundValue
  | [needle, target] =>
      match target.viewList with
      | some items => .ok (ofBool (needle ∈ items))
      | none => .stuck
  | _ => .stuck

/-- Remove the first structurally equal occurrence.  As in Egison's
`deleteFirst`, absence leaves the list unchanged; the paper's multiset clause
uses `member` first and turns absence into ordinary matching failure. -/
def evalDeleteFirst : List GroundValue → FuelResult GroundValue
  | [needle, target] =>
      match target.viewList with
      | some items =>
          match deleteFirst? needle items with
          | some rest => .ok (buildList rest)
          | none => .ok (buildList items)
      | none => .stuck
  | _ => .stuck

/-- Apply the supplied callback from left to right and preserve list order. -/
def evalMap (apply : GroundValue → FuelResult GroundValue) :
    List GroundValue → FuelResult GroundValue
  | [target] =>
      match target.viewList with
      | some items => FuelResult.map buildList (FuelResult.traverse apply items)
      | none => .stuck
  | _ => .stuck

/-- Dispatch the five `PrimOp` names on the ground-data fragment. -/
def eval (apply : GroundValue → FuelResult GroundValue) :
    PrimOp → List GroundValue → FuelResult GroundValue
  | .add => evalAdd
  | .append => evalAppend
  | .member => evalMember
  | .deleteFirst => evalDeleteFirst
  | .map => evalMap apply

@[simp] theorem eval_add (apply) : eval apply .add = evalAdd := rfl
@[simp] theorem eval_append (apply) : eval apply .append = evalAppend := rfl
@[simp] theorem eval_member (apply) : eval apply .member = evalMember := rfl
@[simp] theorem eval_deleteFirst (apply) :
    eval apply .deleteFirst = evalDeleteFirst := rfl
@[simp] theorem eval_map (apply) : eval apply .map = evalMap apply := rfl

end GroundPrimitive

end TypePM.Runtime
