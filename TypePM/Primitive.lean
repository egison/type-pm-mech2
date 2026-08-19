import TypePM.Names

/-!
# Names of primitive operations

The primitive-operation vocabulary is finite.  This module only fixes its
names; typing schemes and evaluation rules belong to later M3 and M5 modules.
-/

namespace TypePM

/-- Primitive operations used by the paper programs. -/
inductive PrimOp where
  | add
  | append
  | member
  | deleteFirst
  | map
deriving Repr, DecidableEq

namespace PrimOp

/-- Stable source spelling for each primitive operation. -/
def name : PrimOp → String
  | .add => "add"
  | .append => "append"
  | .member => "member"
  | .deleteFirst => "deleteFirst"
  | .map => "map"

instance : ToString PrimOp where
  toString := name

/-- Enumeration used by later finite signature checks. -/
def all : List PrimOp := [.add, .append, .member, .deleteFirst, .map]

theorem all_exact :
    all = [.add, .append, .member, .deleteFirst, .map] := by
  rfl

theorem all_pairwise_distinct : List.Pairwise (· ≠ ·) all := by
  decide

theorem toString_add : toString add = "add" := by
  rfl

theorem toString_append : toString append = "append" := by
  rfl

theorem toString_member : toString member = "member" := by
  rfl

theorem toString_deleteFirst : toString deleteFirst = "deleteFirst" := by
  rfl

theorem toString_map : toString map = "map" := by
  rfl

end PrimOp

end TypePM
