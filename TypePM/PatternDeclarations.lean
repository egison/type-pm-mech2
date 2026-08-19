import TypePM.Primitives

/-!
# Pattern-constructor declarations

A `DualScheme` quantifies both ordinary targets and the capabilities demanded
by its holes.  Its result records the capability exported by the pattern
constructor together with the data type on which it operates.
-/

namespace TypePM.Source

structure PolyDual where
  capability : PolyCap
  target : PolyTy
deriving Repr

def PolyDual.WellScoped
    (tyArity capArity : Nat) (dual : PolyDual) : Prop :=
  dual.capability.WellScoped capArity ∧
    dual.target.WellScoped tyArity capArity

def PolyDual.openBound
    (boundTy : Nat → Ty) (boundCap : Nat → Cap)
    (dual : PolyDual) : Dual :=
  { capability := dual.capability.openBound boundCap
    target := dual.target.openBound boundTy boundCap }

structure DualScheme where
  tyArity : Nat
  capArity : Nat
  fields : List PolyDual
  result : PolyDual
  fieldsWellScoped :
    ∀ field ∈ fields, field.WellScoped tyArity capArity
  resultWellScoped : result.WellScoped tyArity capArity
deriving Repr

namespace DualScheme

structure Instantiation where
  fields : List Dual
  result : Dual
deriving Repr

def WellFormed (scheme : DualScheme) : Prop :=
  (∀ field ∈ scheme.fields,
      field.WellScoped scheme.tyArity scheme.capArity) ∧
    scheme.result.WellScoped scheme.tyArity scheme.capArity

theorem wellFormed (scheme : DualScheme) : scheme.WellFormed :=
  ⟨scheme.fieldsWellScoped, scheme.resultWellScoped⟩

def instantiate (scheme : DualScheme) (supply : Supply) :
    Instantiation × Supply :=
  let boundTy := fun position =>
    Ty.var (Scheme.boundTyInstance supply position)
  let boundCap := fun position =>
    Cap.var (Scheme.boundCapInstance supply position)
  ( { fields := scheme.fields.map (PolyDual.openBound boundTy boundCap)
      result := scheme.result.openBound boundTy boundCap },
    ⟨supply.ty + scheme.tyArity, supply.cap + scheme.capArity⟩ )

@[simp] theorem instantiate_next_ty (scheme : DualScheme) (supply : Supply) :
    (scheme.instantiate supply).2.ty = supply.ty + scheme.tyArity := rfl

@[simp] theorem instantiate_next_cap
    (scheme : DualScheme) (supply : Supply) :
    (scheme.instantiate supply).2.cap = supply.cap + scheme.capArity := rfl

def freeTyVars (scheme : DualScheme) : List TyVar :=
  dedupFirst <|
    (scheme.fields.flatMap fun field => field.target.freeTyVars) ++
      scheme.result.target.freeTyVars

def freeCapVars (scheme : DualScheme) : List CapVar :=
  dedupFirst <|
    (scheme.fields.flatMap fun field =>
      field.capability.freeCapVars ++ field.target.freeCapVars) ++
      scheme.result.capability.freeCapVars ++
        scheme.result.target.freeCapVars

def Closed (scheme : DualScheme) : Prop :=
  scheme.freeTyVars = [] ∧ scheme.freeCapVars = []

end DualScheme

namespace ListPatternSchemes

open PolyDataTypes

def nil : DualScheme :=
  { tyArity := 1
    capArity := 1
    fields := []
    result :=
      { capability := .con PatternFormer.list [.bound 0]
        target := PolyDataTypes.list (.bound 0) }
    fieldsWellScoped := by simp
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyDataTypes.list,
        PolyCap.WellScoped, PolyTy.WellScoped] }

def cons : DualScheme :=
  { tyArity := 1
    capArity := 1
    fields :=
      [ { capability := .bound 0, target := .bound 0 },
        { capability := .con PatternFormer.list [.bound 0],
          target := PolyDataTypes.list (.bound 0) } ]
    result :=
      { capability := .con PatternFormer.list [.bound 0]
        target := PolyDataTypes.list (.bound 0) }
    fieldsWellScoped := by
      intro field member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [PolyDual.WellScoped, PolyDataTypes.list,
          PolyCap.WellScoped, PolyTy.WellScoped]
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyDataTypes.list,
        PolyCap.WellScoped, PolyTy.WellScoped] }

def join : DualScheme :=
  { tyArity := 1
    capArity := 1
    fields :=
      [ { capability := .con PatternFormer.list [.bound 0],
          target := PolyDataTypes.list (.bound 0) },
        { capability := .con PatternFormer.list [.bound 0],
          target := PolyDataTypes.list (.bound 0) } ]
    result :=
      { capability := .con PatternFormer.list [.bound 0]
        target := PolyDataTypes.list (.bound 0) }
    fieldsWellScoped := by
      intro field member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [PolyDual.WellScoped, PolyDataTypes.list,
          PolyCap.WellScoped, PolyTy.WellScoped]
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyDataTypes.list,
        PolyCap.WellScoped, PolyTy.WellScoped] }

def all : List (PatternCtor × DualScheme) :=
  [(.nil, nil), (.cons, cons), (.join, join)]

theorem all_names : all.map Prod.fst =
    [PatternCtor.nil, PatternCtor.cons, PatternCtor.join] := by
  rfl

end ListPatternSchemes

end TypePM.Source
