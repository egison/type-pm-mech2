import TypePM.Signature

/-!
# Frozen source signatures

A frozen signature is the boundary between declaration checking and source
elaboration.  Pattern-function bodies are deliberately absent here: after a
declaration has been checked, later phases consume only its name and closed
dual scheme.
-/

namespace TypePM.Source

/-- The public information retained from a checked pattern-function
declaration. -/
structure PatternFunctionDeclaration where
  name : PatternFunName
  scheme : DualScheme
deriving Repr

/-- A declaration signature together with the checked interfaces of pattern
functions. -/
structure FrozenSignature where
  base : Signature
  patternFunctions : List PatternFunctionDeclaration
deriving Repr

namespace FrozenSignature

def lookupPatternFunction
    (signature : FrozenSignature) (name : PatternFunName) :
    Option DualScheme :=
  match signature.patternFunctions.find? (fun declaration =>
      declaration.name = name) with
  | some declaration => some declaration.scheme
  | none => none

def lookupDataFormer (signature : FrozenSignature) (name : DataFormer) :
    Option Nat :=
  signature.base.lookupDataFormer name

def lookupDataConstructor
    (signature : FrozenSignature) (name : DataCtor) : Option Scheme :=
  signature.base.lookupDataConstructor name

def lookupPatternFormer
    (signature : FrozenSignature) (name : PatternFormer) : Option Nat :=
  signature.base.lookupPatternFormer name

def lookupPatternConstructor
    (signature : FrozenSignature) (name : PatternCtor) : Option DualScheme :=
  signature.base.lookupPatternConstructor name

def lookupPrimitive
    (signature : FrozenSignature) (operation : PrimOp) : Option Scheme :=
  signature.base.lookupPrimitive operation

/-- Properties checked before a signature is exposed to source elaboration.
`DualScheme.WellFormed` records bound-index scope, while `DualScheme.Closed`
rules out unbound free type and capability names. -/
structure WellFormed (signature : FrozenSignature) : Prop where
  baseWellFormed : signature.base.WellFormed
  patternFunctionNodup :
    (signature.patternFunctions.map PatternFunctionDeclaration.name).Nodup
  patternFunctionClosed :
    ∀ declaration ∈ signature.patternFunctions, declaration.scheme.Closed
  patternFunctionWellFormed :
    ∀ declaration ∈ signature.patternFunctions, declaration.scheme.WellFormed

theorem lookupPatternFunction_unique
    (signature : FrozenSignature) (name : PatternFunName)
    {left right : DualScheme}
    (leftLookup : signature.lookupPatternFunction name = some left)
    (rightLookup : signature.lookupPatternFunction name = some right) :
    left = right := by
  exact Option.some.inj (leftLookup.symm.trans rightLookup)

private theorem lookupPatternFunction_declaration
    (signature : FrozenSignature) (name : PatternFunName) (scheme : DualScheme)
    (lookup : signature.lookupPatternFunction name = some scheme) :
    ∃ declaration ∈ signature.patternFunctions,
      declaration.name = name ∧ declaration.scheme = scheme := by
  unfold lookupPatternFunction at lookup
  generalize foundEquality : signature.patternFunctions.find? (fun declaration =>
      declaration.name = name) = found at lookup
  cases found with
  | none => contradiction
  | some declaration =>
      have member : declaration ∈ signature.patternFunctions :=
        List.mem_of_find?_eq_some foundEquality
      have nameEquality : declaration.name = name :=
        of_decide_eq_true
          (List.find?_some
            (p := fun item : PatternFunctionDeclaration =>
              decide (item.name = name)) foundEquality)
      cases Option.some.inj lookup
      exact ⟨declaration, member, nameEquality, rfl⟩

theorem lookupPatternFunction_closed
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {name : PatternFunName} {scheme : DualScheme}
    (lookup : signature.lookupPatternFunction name = some scheme) :
    scheme.Closed := by
  obtain ⟨declaration, member, _, rfl⟩ :=
    lookupPatternFunction_declaration signature name scheme lookup
  exact wellFormed.patternFunctionClosed declaration member

theorem lookupPatternFunction_wellFormed
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {name : PatternFunName} {scheme : DualScheme}
    (lookup : signature.lookupPatternFunction name = some scheme) :
    scheme.WellFormed := by
  obtain ⟨declaration, member, _, rfl⟩ :=
    lookupPatternFunction_declaration signature name scheme lookup
  exact wellFormed.patternFunctionWellFormed declaration member

end FrozenSignature

namespace Paper1FrozenSignature

/-- Paper 1 has no named pattern-function declarations at this milestone. -/
def signature : FrozenSignature :=
  { base := Paper1Signature.signature
    patternFunctions := [] }

theorem wellFormed : signature.WellFormed := by
  exact
    { baseWellFormed := Paper1Signature.wellFormed
      patternFunctionNodup := by simp [signature]
      patternFunctionClosed := by simp [signature]
      patternFunctionWellFormed := by simp [signature] }

@[simp] theorem lookup_pattern_function (name : PatternFunName) :
    signature.lookupPatternFunction name = none := by
  rfl

@[simp] theorem lookup_bool :
    signature.lookupDataFormer DataFormer.bool = some 0 := by
  rfl

@[simp] theorem lookup_list :
    signature.lookupDataFormer DataFormer.list = some 1 := by
  rfl

@[simp] theorem lookup_pattern_list :
    signature.lookupPatternFormer PatternFormer.list = some 1 := by
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

@[simp] theorem lookup_pairFirst :
    signature.lookupPrimitive PrimOp.pairFirst =
      some PrimitiveSchemes.pairFirst := by
  rfl

@[simp] theorem lookup_pairSecond :
    signature.lookupPrimitive PrimOp.pairSecond =
      some PrimitiveSchemes.pairSecond := by
  rfl

end Paper1FrozenSignature

end TypePM.Source
