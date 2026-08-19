import TypePM.Runtime.Values

/-!
# Runtime list and product conventions

Matcher clauses communicate through ordinary constructor-encoded lists.  A
clause with zero holes uses the empty tuple as its element, one hole uses a
scalar directly, and two or more holes use an exact-arity tuple.  These total
decoders make malformed runtime values explicit instead of silently changing
the clause shape.
-/

namespace TypePM.Runtime

namespace Value

/-- Canonical empty list in the complete runtime value type. -/
def nilValue : Value := .data DataCtor.nil []

/-- Canonical list cell in the complete runtime value type. -/
def consValue (head tail : Value) : Value :=
  .data DataCtor.cons [head, tail]

/-- Encode a host list while preserving element order. -/
def buildList : List Value → Value
  | [] => nilValue
  | head :: tail => consValue head (buildList tail)

/-- Decode a canonical proper list whose elements may be arbitrary values. -/
def viewList : Value → Option (List Value)
  | .data constructor [] =>
      if constructor = DataCtor.nil then some [] else none
  | .data constructor [head, tail] =>
      if constructor = DataCtor.cons then
        (viewList tail).map (head :: ·)
      else
        none
  | _ => none
termination_by value => sizeOf value

@[simp] theorem viewList_buildList (items : List Value) :
    viewList (buildList items) = some items := by
  induction items with
  | nil => simp [buildList, nilValue, viewList, DataCtor.nil]
  | cons head tail ih =>
      simp [buildList, consValue, viewList, ih]

end Value

/-- Decode the `tuple_k` convention used for next matchers and decomposition
elements. -/
def decodeProduct (arity : Nat) (value : Value) : Option (List Value) :=
  match arity with
  | 0 =>
      match value with
      | .tuple [] => some []
      | _ => none
  | 1 => some [value]
  | arity@(_ + 2) =>
      match value with
      | .tuple items => if items.length = arity then some items else none
      | _ => none

/-- Decode every element of a canonical list using the exact product
convention for a matcher clause's hole count. -/
def decodeDecompositions (arity : Nat) (value : Value) :
    Option (List (List Value)) := do
  let candidates ← value.viewList
  candidates.mapM (decodeProduct arity)

@[simp] theorem decodeProduct_zero_empty :
    decodeProduct 0 (.tuple []) = some [] := by
  rfl

@[simp] theorem decodeProduct_one (value : Value) :
    decodeProduct 1 value = some [value] := by
  rfl

theorem decodeProduct_many_exact
    {arity : Nat} (atLeastTwo : 2 ≤ arity)
    (items : List Value) (length : items.length = arity) :
    decodeProduct arity (.tuple items) = some items := by
  cases arity with
  | zero => omega
  | succ arity =>
      cases arity with
      | zero => omega
      | succ arity =>
          simp [decodeProduct, length]

end TypePM.Runtime
