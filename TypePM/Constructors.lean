import TypePM.DataTypes

/-!
# Canonical data-constructor schemes

The schemes are closed: all polymorphism is represented by bound position
zero, never by a free unification variable.
-/

namespace TypePM.Source

namespace ConstructorSchemes

open PolyDataTypes

def boolTrue : Scheme :=
  ⟨0, 0, PolyDataTypes.bool, by
    simp [PolyDataTypes.bool, PolyTy.WellScoped]⟩

def boolFalse : Scheme :=
  ⟨0, 0, PolyDataTypes.bool, by
    simp [PolyDataTypes.bool, PolyTy.WellScoped]⟩

def listNil : Scheme :=
  ⟨1, 0, PolyDataTypes.list (.bound 0), by
    simp [PolyDataTypes.list, PolyTy.WellScoped]⟩

def listCons : Scheme :=
  ⟨1, 0,
    .fn (.bound 0)
      (.fn (PolyDataTypes.list (.bound 0))
        (PolyDataTypes.list (.bound 0))), by
    simp [PolyDataTypes.list, PolyTy.WellScoped]⟩

@[simp] theorem instantiate_boolTrue (supply : Supply) :
    boolTrue.instantiate supply = (TypePM.DataTypes.bool, supply) := by
  cases supply
  rfl

@[simp] theorem instantiate_boolFalse (supply : Supply) :
    boolFalse.instantiate supply = (TypePM.DataTypes.bool, supply) := by
  cases supply
  rfl

@[simp] theorem instantiate_listNil (supply : Supply) :
    listNil.instantiate supply =
      (TypePM.DataTypes.list (.var ⟨supply.ty⟩),
        ⟨supply.ty + 1, supply.cap⟩) := by
  cases supply
  rfl

@[simp] theorem instantiate_listCons (supply : Supply) :
    listCons.instantiate supply =
      (.fn (.var ⟨supply.ty⟩)
        (.fn (TypePM.DataTypes.list (.var ⟨supply.ty⟩))
          (TypePM.DataTypes.list (.var ⟨supply.ty⟩))),
        ⟨supply.ty + 1, supply.cap⟩) := by
  cases supply
  rfl

end ConstructorSchemes

end TypePM.Source
