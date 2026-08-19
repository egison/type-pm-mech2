import TypePM.Scheme

/-!
# Canonical data types

The paper uses Boolean and list data types throughout M3--M5.  These
abbreviations keep their canonical result forms in one place, for both
monotypes and position-bound scheme bodies.
-/

namespace TypePM

namespace DataTypes

def bool : Ty := .data DataFormer.bool []

def list (element : Ty) : Ty := .data DataFormer.list [element]

end DataTypes

namespace Source.PolyDataTypes

def bool : PolyTy := .data DataFormer.bool []

def list (element : PolyTy) : PolyTy :=
  .data DataFormer.list [element]

end Source.PolyDataTypes

@[simp] theorem Source.PolyDataTypes.open_bool
    (boundTy : Nat → Ty) (boundCap : Nat → Cap) :
    Source.PolyDataTypes.bool.openBound boundTy boundCap = DataTypes.bool := by
  rfl

@[simp] theorem Source.PolyDataTypes.open_list
    (element : Source.PolyTy)
    (boundTy : Nat → Ty) (boundCap : Nat → Cap) :
    (Source.PolyDataTypes.list element).openBound boundTy boundCap =
      DataTypes.list (element.openBound boundTy boundCap) := by
  rfl

end TypePM
