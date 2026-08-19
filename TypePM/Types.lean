import Std

/-!
# Type-PM types used by the independent development

Only constructors needed by the M0 fragment are present.  Function types and
the remaining source language are introduced by later milestones.
-/

namespace TypePM

/-- Capability variables and ordinary type variables are different Lean
types, not two aliases for natural numbers. -/
structure CapVar where
  index : Nat
deriving Repr, DecidableEq

structure TyVar where
  index : Nat
deriving Repr, DecidableEq

/-- Capabilities describe the input shapes consumed by matchers. -/
inductive Cap where
  | any
  | var (index : CapVar)
  | prod (items : List Cap)
deriving Repr

/-- M0 types.  Matcher and slot capabilities form a separate variable sort. -/
inductive Ty where
  | var (index : TyVar)
  | int
  | prod (items : List Ty)
  | matcher (capability : Cap) (target : Ty)
  | slot (capability : Cap) (target : Ty)
deriving Repr

/-- One capability/target pair used by product checking conversions. -/
structure Dual where
  capability : Cap
  target : Ty
deriving Repr

def Dual.matcherType (dual : Dual) : Ty :=
  .matcher dual.capability dual.target

def Dual.capabilities (duals : List Dual) : List Cap :=
  duals.map Dual.capability

def Dual.targets (duals : List Dual) : List Ty :=
  duals.map Dual.target

end TypePM
