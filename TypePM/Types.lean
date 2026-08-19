import TypePM.Names

/-!
# Type-PM types used by the independent development

Only constructors needed through the current milestone are present.  Data,
polymorphic schemes, and matcher-specific source forms are introduced later.
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
  | con (former : PatternFormer) (arguments : List Cap)
deriving Repr

/-- Types through M1.  Matcher and slot capabilities use a variable sort
separate from ordinary type variables. -/
inductive Ty where
  | var (index : TyVar)
  | int
  | fn (domain codomain : Ty)
  | prod (items : List Ty)
  | data (former : DataFormer) (arguments : List Ty)
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
