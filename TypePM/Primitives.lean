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

/-- First projection from a heterogeneous pair. -/
def pairFirst : Scheme :=
  ⟨2, 0,
    .fn (.prod [.bound 0, .bound 1]) (.bound 0), by
    simp [PolyTy.WellScoped]⟩

/-- Second projection from a heterogeneous pair. -/
def pairSecond : Scheme :=
  ⟨2, 0,
    .fn (.prod [.bound 0, .bound 1]) (.bound 1), by
    simp [PolyTy.WellScoped]⟩

def ofPrimOp : PrimOp → Scheme
  | .add => add
  | .append => append
  | .member => member
  | .deleteFirst => deleteFirst
  | .map => map
  | .pairFirst => pairFirst
  | .pairSecond => pairSecond

theorem instantiate_add (supply : Supply) :
    add.instantiate supply =
      (.fn .int (.fn .int .int), supply) := by
  cases supply
  rfl

theorem instantiate_append (supply : Supply) :
    append.instantiate supply =
      (.fn (TypePM.DataTypes.list (.var ⟨supply.ty⟩))
        (.fn (TypePM.DataTypes.list (.var ⟨supply.ty⟩))
          (TypePM.DataTypes.list (.var ⟨supply.ty⟩))),
        ⟨supply.ty + 1, supply.cap⟩) := by
  cases supply
  rfl

theorem instantiate_member (supply : Supply) :
    member.instantiate supply =
      (.fn (.var ⟨supply.ty⟩)
        (.fn (TypePM.DataTypes.list (.var ⟨supply.ty⟩))
          TypePM.DataTypes.bool),
        ⟨supply.ty + 1, supply.cap⟩) := by
  cases supply
  rfl

theorem instantiate_deleteFirst (supply : Supply) :
    deleteFirst.instantiate supply =
      (.fn (.var ⟨supply.ty⟩)
        (.fn (TypePM.DataTypes.list (.var ⟨supply.ty⟩))
          (TypePM.DataTypes.list (.var ⟨supply.ty⟩))),
        ⟨supply.ty + 1, supply.cap⟩) := by
  cases supply
  rfl

theorem instantiate_map (supply : Supply) :
    map.instantiate supply =
      (.fn (.fn (.var ⟨supply.ty⟩) (.var ⟨supply.ty + 1⟩))
        (.fn (TypePM.DataTypes.list (.var ⟨supply.ty⟩))
          (TypePM.DataTypes.list (.var ⟨supply.ty + 1⟩))),
        ⟨supply.ty + 2, supply.cap⟩) := by
  cases supply
  rfl

theorem instantiate_pairFirst (supply : Supply) :
    pairFirst.instantiate supply =
      (.fn (.prod [.var ⟨supply.ty⟩, .var ⟨supply.ty + 1⟩])
        (.var ⟨supply.ty⟩),
        ⟨supply.ty + 2, supply.cap⟩) := by
  cases supply
  rfl

theorem instantiate_pairSecond (supply : Supply) :
    pairSecond.instantiate supply =
      (.fn (.prod [.var ⟨supply.ty⟩, .var ⟨supply.ty + 1⟩])
        (.var ⟨supply.ty + 1⟩),
        ⟨supply.ty + 2, supply.cap⟩) := by
  cases supply
  rfl

@[simp] theorem ofPrimOp_add : ofPrimOp .add = add := rfl
@[simp] theorem ofPrimOp_append : ofPrimOp .append = append := rfl
@[simp] theorem ofPrimOp_member : ofPrimOp .member = member := rfl
@[simp] theorem ofPrimOp_deleteFirst :
    ofPrimOp .deleteFirst = deleteFirst := rfl
@[simp] theorem ofPrimOp_map : ofPrimOp .map = map := rfl
@[simp] theorem ofPrimOp_pairFirst : ofPrimOp .pairFirst = pairFirst := rfl
@[simp] theorem ofPrimOp_pairSecond : ofPrimOp .pairSecond = pairSecond := rfl

end PrimitiveSchemes

end TypePM.Source
