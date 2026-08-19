import TypePM.Names

/-!
# Ground data values

`GroundValue` is the recursive, closed data fragment needed to execute the
paper's list primitives before the full M5 evaluator exists.  It contains
integers, data-constructor applications, and tuples.  In particular, it does
not claim to represent functions, closures, matchers, or matching states;
those require the later expression and matching semantics.
-/

namespace TypePM.Runtime

/- Closed data and its finite child sequences are mutually recursive so that
structural equality remains executable. -/
mutual
  /-- A closed integer, data-constructor application, or tuple. -/
  inductive GroundValue where
    | int (value : Int)
    | data (constructor : DataCtor) (arguments : GroundValues)
    | tuple (items : GroundValues)

  /-- A finite sequence of children inside a ground value. -/
  inductive GroundValues where
    | nil
    | cons (head : GroundValue) (tail : GroundValues)
end

deriving instance Repr, DecidableEq for GroundValue, GroundValues

namespace GroundValues

/-- Convert an ordinary Lean list to a ground child sequence. -/
def ofList : List GroundValue → GroundValues
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

/-- Expose a ground child sequence as an ordinary Lean list. -/
def toList : GroundValues → List GroundValue
  | .nil => []
  | .cons head tail => head :: toList tail

@[simp] theorem toList_ofList (items : List GroundValue) :
    toList (ofList items) = items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [ofList, toList, ih]

end GroundValues

namespace GroundValue

/-- Apply a data constructor to an ordinary list of ground arguments. -/
def dataValue (constructor : DataCtor)
    (arguments : List GroundValue) : GroundValue :=
  .data constructor (GroundValues.ofList arguments)

/-- Build a ground tuple from an ordinary list of items. -/
def tupleValue (items : List GroundValue) : GroundValue :=
  .tuple (GroundValues.ofList items)

/-- Canonical encoding of the Boolean value `true`. -/
def trueValue : GroundValue := dataValue DataCtor.true []

/-- Canonical encoding of the Boolean value `false`. -/
def falseValue : GroundValue := dataValue DataCtor.false []

/-- Build a canonical Boolean data value. -/
def ofBool : Bool → GroundValue
  | true => trueValue
  | false => falseValue

/-- Recognize exactly the two canonical Boolean encodings.  Every ground value
has an explicit result; non-Booleans and malformed constructor applications
return `none`. -/
def viewBool : GroundValue → Option Bool
  | .data constructor .nil =>
      if constructor = DataCtor.true then some true
      else if constructor = DataCtor.false then some false
      else none
  | _ => none

/-- Canonical empty-list encoding. -/
def nilValue : GroundValue := dataValue DataCtor.nil []

/-- Canonical nonempty-list encoding. -/
def consValue (head tail : GroundValue) : GroundValue :=
  dataValue DataCtor.cons [head, tail]

/-- Encode a host list as canonical `nil`/`cons` ground data. -/
def buildList : List GroundValue → GroundValue
  | [] => nilValue
  | head :: tail => consValue head (buildList tail)

/-- Decode canonical `nil`/`cons` ground data.  The function is total as a
Lean function and reports malformed spines with `none`, including incorrect
constructor arities and improper tails. -/
def viewList : GroundValue → Option (List GroundValue)
  | .data constructor .nil =>
      if constructor = DataCtor.nil then some [] else none
  | .data constructor (.cons head (.cons tail .nil)) =>
      if constructor = DataCtor.cons then
        (viewList tail).map (head :: ·)
      else
        none
  | _ => none
termination_by value => sizeOf value

@[simp] theorem viewBool_ofBool (value : Bool) :
    viewBool (ofBool value) = some value := by
  cases value <;> rfl

@[simp] theorem viewList_buildList (items : List GroundValue) :
    viewList (buildList items) = some items := by
  induction items with
  | nil => simp [buildList, nilValue, dataValue, viewList, DataCtor.nil,
      GroundValues.ofList]
  | cons head tail ih =>
      simp [buildList, consValue, dataValue, viewList, GroundValues.ofList, ih]

end GroundValue

end TypePM.Runtime
