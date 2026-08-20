import TypePM.PatternDeclarations

/-!
# Finite M3 signatures

The five declaration categories remain separate.  `Signature.WellFormed`
checks duplicate freedom and closure of every stored scheme; later M4/M5
checks can extend this boundary without changing the declaration lookup API.
-/

namespace TypePM.Source

namespace Scheme

def Closed (scheme : Scheme) : Prop :=
  scheme.freeTyVars = [] ∧ scheme.freeCapVars = []

end Scheme

structure DataFormerDeclaration where
  former : DataFormer
  arity : Nat
deriving Repr

structure PatternFormerDeclaration where
  former : PatternFormer
  arity : Nat
deriving Repr

structure DataConstructorDeclaration where
  constructor : DataCtor
  scheme : Scheme
deriving Repr

structure PatternConstructorDeclaration where
  constructor : PatternCtor
  scheme : DualScheme
deriving Repr

structure PrimitiveDeclaration where
  operation : PrimOp
  scheme : Scheme
deriving Repr

structure Signature where
  dataFormers : List DataFormerDeclaration
  dataConstructors : List DataConstructorDeclaration
  patternFormers : List PatternFormerDeclaration
  patternConstructors : List PatternConstructorDeclaration
  primitives : List PrimitiveDeclaration
deriving Repr

namespace Signature

/-- Peel constructor arguments until the data result at the end of a curried
constructor scheme is reached. -/
def constructorResult? : PolyTy → Option (DataFormer × Nat)
  | .fn _ result => constructorResult? result
  | .data former arguments => some (former, arguments.length)
  | _ => none

/-- Pattern results are data types directly, rather than curried constructor
types. -/
def patternTargetResult? : PolyTy → Option (DataFormer × Nat)
  | .data former arguments => some (former, arguments.length)
  | _ => none

def patternCapabilityResult? : PolyCap → Option (PatternFormer × Nat)
  | .con former arguments => some (former, arguments.length)
  | _ => none

def lookupDataFormer (signature : Signature) (name : DataFormer) :
    Option Nat :=
  match signature.dataFormers.find? (fun declaration =>
      declaration.former = name) with
  | some declaration => some declaration.arity
  | none => none

def lookupDataConstructor (signature : Signature) (name : DataCtor) :
    Option Scheme :=
  match signature.dataConstructors.find? (fun declaration =>
      declaration.constructor = name) with
  | some declaration => some declaration.scheme
  | none => none

def lookupPatternFormer (signature : Signature) (name : PatternFormer) :
    Option Nat :=
  match signature.patternFormers.find? (fun declaration =>
      declaration.former = name) with
  | some declaration => some declaration.arity
  | none => none

def lookupPatternConstructor
    (signature : Signature) (name : PatternCtor) : Option DualScheme :=
  match signature.patternConstructors.find? (fun declaration =>
      declaration.constructor = name) with
  | some declaration => some declaration.scheme
  | none => none

def lookupPrimitive (signature : Signature) (operation : PrimOp) :
    Option Scheme :=
  match signature.primitives.find? (fun declaration =>
      declaration.operation = operation) with
  | some declaration => some declaration.scheme
  | none => none

structure WellFormed (signature : Signature) : Prop where
  dataFormerNodup :
    (signature.dataFormers.map DataFormerDeclaration.former).Nodup
  dataConstructorNodup :
    (signature.dataConstructors.map
      DataConstructorDeclaration.constructor).Nodup
  patternFormerNodup :
    (signature.patternFormers.map PatternFormerDeclaration.former).Nodup
  patternConstructorNodup :
    (signature.patternConstructors.map
      PatternConstructorDeclaration.constructor).Nodup
  primitiveNodup :
    (signature.primitives.map PrimitiveDeclaration.operation).Nodup
  dataConstructorClosed : ∀ declaration ∈ signature.dataConstructors,
    declaration.scheme.Closed
  patternConstructorClosed :
    ∀ declaration ∈ signature.patternConstructors,
      declaration.scheme.Closed
  primitiveClosed : ∀ declaration ∈ signature.primitives,
    declaration.scheme.Closed
  dataConstructorResult : ∀ declaration ∈ signature.dataConstructors,
    ∃ former arity,
      constructorResult? declaration.scheme.body = some (former, arity) ∧
        signature.lookupDataFormer former = some arity
  patternConstructorTarget :
    ∀ declaration ∈ signature.patternConstructors,
      ∃ former arity,
        patternTargetResult? declaration.scheme.result.target =
            some (former, arity) ∧
          signature.lookupDataFormer former = some arity
  patternConstructorCapability :
    ∀ declaration ∈ signature.patternConstructors,
      ∃ former arity,
        patternCapabilityResult? declaration.scheme.result.capability =
            some (former, arity) ∧
          signature.lookupPatternFormer former = some arity
  primitiveCanonical : ∀ declaration ∈ signature.primitives,
    declaration.scheme = PrimitiveSchemes.ofPrimOp declaration.operation

namespace WellFormed

theorem dataConstructorClosed_of_lookup
    {signature : Signature} (wellFormed : signature.WellFormed)
    {constructor : DataCtor} {scheme : Scheme}
    (lookup : signature.lookupDataConstructor constructor = some scheme) :
    scheme.Closed := by
  unfold lookupDataConstructor at lookup
  split at lookup
  next declaration found =>
    simp only [Option.some.injEq] at lookup
    subst scheme
    exact wellFormed.dataConstructorClosed declaration
      (List.mem_of_find?_eq_some found)
  next => simp at lookup

theorem primitiveClosed_of_lookup
    {signature : Signature} (wellFormed : signature.WellFormed)
    {operation : PrimOp} {scheme : Scheme}
    (lookup : signature.lookupPrimitive operation = some scheme) :
    scheme.Closed := by
  unfold lookupPrimitive at lookup
  split at lookup
  next declaration found =>
    simp only [Option.some.injEq] at lookup
    subst scheme
    exact wellFormed.primitiveClosed declaration
      (List.mem_of_find?_eq_some found)
  next => simp at lookup

end WellFormed

end Signature

namespace Paper1Signature

def dataFormers : List DataFormerDeclaration :=
  [⟨DataFormer.bool, 0⟩, ⟨DataFormer.list, 1⟩]

def dataConstructors : List DataConstructorDeclaration :=
  [ ⟨DataCtor.true, ConstructorSchemes.boolTrue⟩,
    ⟨DataCtor.false, ConstructorSchemes.boolFalse⟩,
    ⟨DataCtor.nil, ConstructorSchemes.listNil⟩,
    ⟨DataCtor.cons, ConstructorSchemes.listCons⟩ ]

def patternFormers : List PatternFormerDeclaration :=
  [⟨PatternFormer.list, 1⟩]

def patternConstructors : List PatternConstructorDeclaration :=
  [ ⟨PatternCtor.nil, ListPatternSchemes.nil⟩,
    ⟨PatternCtor.cons, ListPatternSchemes.cons⟩,
    ⟨PatternCtor.join, ListPatternSchemes.join⟩ ]

def primitives : List PrimitiveDeclaration :=
  [ ⟨PrimOp.add, PrimitiveSchemes.add⟩,
    ⟨PrimOp.append, PrimitiveSchemes.append⟩,
    ⟨PrimOp.member, PrimitiveSchemes.member⟩,
    ⟨PrimOp.deleteFirst, PrimitiveSchemes.deleteFirst⟩,
    ⟨PrimOp.map, PrimitiveSchemes.map⟩,
    ⟨PrimOp.pairFirst, PrimitiveSchemes.pairFirst⟩,
    ⟨PrimOp.pairSecond, PrimitiveSchemes.pairSecond⟩ ]

/-- The standard declaration list covers every primitive exactly once and in
the stable enumeration order. -/
theorem primitive_operations_exact :
    primitives.map PrimitiveDeclaration.operation = PrimOp.all := by
  rfl

def signature : Signature :=
  { dataFormers := dataFormers
    dataConstructors := dataConstructors
    patternFormers := patternFormers
    patternConstructors := patternConstructors
    primitives := primitives }

private theorem constructorSchemes_closed :
    ∀ declaration ∈ dataConstructors, declaration.scheme.Closed := by
  intro declaration member
  simp only [dataConstructors, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    constructor <;> rfl

private theorem patternSchemes_closed :
    ∀ declaration ∈ patternConstructors,
      declaration.scheme.Closed := by
  intro declaration member
  simp only [patternConstructors, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl <;>
    constructor <;> rfl

private theorem primitiveSchemes_closed :
    ∀ declaration ∈ primitives, declaration.scheme.Closed := by
  intro declaration member
  simp only [primitives, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> rfl

private theorem constructor_results_valid :
    ∀ declaration ∈ dataConstructors,
      ∃ former arity,
        Signature.constructorResult? declaration.scheme.body =
            some (former, arity) ∧
          signature.lookupDataFormer former = some arity := by
  intro declaration member
  simp only [dataConstructors, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨DataFormer.bool, 0, rfl, rfl⟩
  · exact ⟨DataFormer.bool, 0, rfl, rfl⟩
  · exact ⟨DataFormer.list, 1, rfl, rfl⟩
  · exact ⟨DataFormer.list, 1, rfl, rfl⟩

private theorem pattern_targets_valid :
    ∀ declaration ∈ patternConstructors,
      ∃ former arity,
        Signature.patternTargetResult? declaration.scheme.result.target =
            some (former, arity) ∧
          signature.lookupDataFormer former = some arity := by
  intro declaration member
  simp only [patternConstructors, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl <;>
    exact ⟨DataFormer.list, 1, rfl, rfl⟩

private theorem pattern_capabilities_valid :
    ∀ declaration ∈ patternConstructors,
      ∃ former arity,
        Signature.patternCapabilityResult?
            declaration.scheme.result.capability = some (former, arity) ∧
          signature.lookupPatternFormer former = some arity := by
  intro declaration member
  simp only [patternConstructors, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl <;>
    exact ⟨PatternFormer.list, 1, rfl, rfl⟩

private theorem primitives_canonical :
    ∀ declaration ∈ primitives,
      declaration.scheme =
        PrimitiveSchemes.ofPrimOp declaration.operation := by
  intro declaration member
  simp only [primitives, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem wellFormed : signature.WellFormed := by
  exact
    { dataFormerNodup := by decide
      dataConstructorNodup := by decide
      patternFormerNodup := by decide
      patternConstructorNodup := by decide
      primitiveNodup := by decide
      dataConstructorClosed := constructorSchemes_closed
      patternConstructorClosed := patternSchemes_closed
      primitiveClosed := primitiveSchemes_closed
      dataConstructorResult := constructor_results_valid
      patternConstructorTarget := pattern_targets_valid
      patternConstructorCapability := pattern_capabilities_valid
      primitiveCanonical := primitives_canonical }

@[simp] theorem lookup_bool :
    signature.lookupDataFormer DataFormer.bool = some 0 := by
  rfl

@[simp] theorem lookup_list :
    signature.lookupDataFormer DataFormer.list = some 1 := by
  rfl

@[simp] theorem lookup_true :
    signature.lookupDataConstructor DataCtor.true =
      some ConstructorSchemes.boolTrue := by
  rfl

@[simp] theorem lookup_false :
    signature.lookupDataConstructor DataCtor.false =
      some ConstructorSchemes.boolFalse := by
  rfl

@[simp] theorem lookup_data_nil :
    signature.lookupDataConstructor DataCtor.nil =
      some ConstructorSchemes.listNil := by
  rfl

@[simp] theorem lookup_data_cons :
    signature.lookupDataConstructor DataCtor.cons =
      some ConstructorSchemes.listCons := by
  rfl

@[simp] theorem lookup_pattern_nil :
    signature.lookupPatternConstructor PatternCtor.nil =
      some ListPatternSchemes.nil := by
  rfl

@[simp] theorem lookup_pattern_cons :
    signature.lookupPatternConstructor PatternCtor.cons =
      some ListPatternSchemes.cons := by
  rfl

@[simp] theorem lookup_pattern_join :
    signature.lookupPatternConstructor PatternCtor.join =
      some ListPatternSchemes.join := by
  rfl

@[simp] theorem lookup_primitive (operation : PrimOp) :
    signature.lookupPrimitive operation =
      some (PrimitiveSchemes.ofPrimOp operation) := by
  cases operation <;> rfl

end Paper1Signature

end TypePM.Source
