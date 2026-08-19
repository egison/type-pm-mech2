import TypePM.Types

/-!
# Variables occurring in M1 types

The two variable sorts are inspected separately.  These executable Boolean
tests are used by the occurs checks of the first-order unifier.
-/

namespace TypePM

mutual

/-- Whether a capability variable occurs in a capability. -/
def Cap.occurs (needle : CapVar) : Cap → Bool
  | .any => false
  | .var index => decide (index = needle)
  | .prod items => Cap.occursList needle items
  | .con _ arguments => Cap.occursList needle arguments

/-- List counterpart of `Cap.occurs`. -/
def Cap.occursList (needle : CapVar) : List Cap → Bool
  | [] => false
  | item :: items => item.occurs needle || Cap.occursList needle items

end

mutual

/-- Whether an ordinary type variable occurs in a type. -/
def Ty.occursTy (needle : TyVar) : Ty → Bool
  | .var index => decide (index = needle)
  | .int => false
  | .fn domain codomain => domain.occursTy needle || codomain.occursTy needle
  | .prod items => Ty.occursTyList needle items
  | .data _ arguments => Ty.occursTyList needle arguments
  | .matcher _ target => target.occursTy needle
  | .slot _ target => target.occursTy needle

/-- List counterpart of `Ty.occursTy`. -/
def Ty.occursTyList (needle : TyVar) : List Ty → Bool
  | [] => false
  | item :: items => item.occursTy needle || Ty.occursTyList needle items

end

mutual

/-- Whether a capability variable occurs anywhere inside a type. -/
def Ty.occursCap (needle : CapVar) : Ty → Bool
  | .var _ => false
  | .int => false
  | .fn domain codomain => domain.occursCap needle || codomain.occursCap needle
  | .prod items => Ty.occursCapList needle items
  | .data _ arguments => Ty.occursCapList needle arguments
  | .matcher capability target =>
      capability.occurs needle || target.occursCap needle
  | .slot capability target =>
      capability.occurs needle || target.occursCap needle

/-- List counterpart of `Ty.occursCap`. -/
def Ty.occursCapList (needle : CapVar) : List Ty → Bool
  | [] => false
  | item :: items => item.occursCap needle || Ty.occursCapList needle items

end

end TypePM
