import TypePM.Syntax

/-!
# Fresh ordinary type variables

M1 allocates only ordinary type variables.  Capability variables remain part
of the type language but are never guessed by the M1 generator.
-/

namespace TypePM

mutual

/-- First natural-number index strictly above every ordinary type variable in
the given type. -/
def Ty.nextVar : Ty → Nat
  | .var index => index.index + 1
  | .int => 0
  | .fn domain codomain => max domain.nextVar codomain.nextVar
  | .prod items => Ty.nextVarList items
  | .matcher _ target => target.nextVar
  | .slot _ target => target.nextVar

def Ty.nextVarList : List Ty → Nat
  | [] => 0
  | item :: items => max item.nextVar (Ty.nextVarList items)

end

/-- Root supply for a monomorphic context. -/
def Context.nextVar (context : Context) : Nat :=
  Ty.nextVarList context

end TypePM

