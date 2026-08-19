import TypePM.Constructors
import TypePM.Primitive

/-!
# Canonical primitive-operation schemes
-/

namespace TypePM.Source

namespace PrimitiveSchemes

open PolyDataTypes

def add : Scheme :=
  ⟨0, 0, .fn .int (.fn .int .int), by
    simp [PolyTy.WellScoped]⟩

def append : Scheme :=
  ⟨1, 0,
    .fn (PolyDataTypes.list (.bound 0))
      (.fn (PolyDataTypes.list (.bound 0))
        (PolyDataTypes.list (.bound 0))), by
    simp [PolyDataTypes.list, PolyTy.WellScoped]⟩

def member : Scheme :=
  ⟨1, 0,
    .fn (.bound 0)
      (.fn (PolyDataTypes.list (.bound 0)) PolyDataTypes.bool), by
    simp [PolyDataTypes.list, PolyDataTypes.bool, PolyTy.WellScoped]⟩

def deleteFirst : Scheme :=
  ⟨1, 0,
    .fn (.bound 0)
      (.fn (PolyDataTypes.list (.bound 0))
        (PolyDataTypes.list (.bound 0))), by
    simp [PolyDataTypes.list, PolyTy.WellScoped]⟩

def map : Scheme :=
  ⟨2, 0,
    .fn (.fn (.bound 0) (.bound 1))
      (.fn (PolyDataTypes.list (.bound 0))
        (PolyDataTypes.list (.bound 1))), by
    simp [PolyDataTypes.list, PolyTy.WellScoped]⟩

def ofPrimOp : PrimOp → Scheme
  | .add => add
  | .append => append
  | .member => member
  | .deleteFirst => deleteFirst
  | .map => map

@[simp] theorem ofPrimOp_add : ofPrimOp .add = add := rfl
@[simp] theorem ofPrimOp_append : ofPrimOp .append = append := rfl
@[simp] theorem ofPrimOp_member : ofPrimOp .member = member := rfl
@[simp] theorem ofPrimOp_deleteFirst :
    ofPrimOp .deleteFirst = deleteFirst := rfl
@[simp] theorem ofPrimOp_map : ofPrimOp .map = map := rfl

end PrimitiveSchemes

end TypePM.Source
