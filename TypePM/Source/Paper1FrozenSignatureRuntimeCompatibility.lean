import TypePM.Source.FrozenSignatureRuntimeCompatibility

/-!
# Paper-1 frozen-signature runtime compatibility

The Paper-1 fixture discharges the generic frozen-signature runtime contract.
Its closed-world constructor classification lives here, beside the concrete
signature, rather than in a generically named runtime bridge.
-/

namespace TypePM.Source.Paper1FrozenSignature

/-- A successful data-constructor lookup in the Paper-1 fixture is one of the
four constructors implemented by runtime value typing. -/
theorem dataConstructor_lookup_cases
    {constructor : DataCtor} {scheme : Scheme}
    (lookup : signature.lookupDataConstructor constructor = some scheme) :
    (constructor = DataCtor.true ∧ scheme = ConstructorSchemes.boolTrue) ∨
    (constructor = DataCtor.false ∧ scheme = ConstructorSchemes.boolFalse) ∨
    (constructor = DataCtor.nil ∧ scheme = ConstructorSchemes.listNil) ∨
    (constructor = DataCtor.cons ∧ scheme = ConstructorSchemes.listCons) := by
  by_cases isTrue : DataCtor.true = constructor
  · subst constructor
    simp [lookup_true] at lookup
    exact .inl ⟨rfl, lookup.symm⟩
  · by_cases isFalse : DataCtor.false = constructor
    · subst constructor
      simp [lookup_false] at lookup
      exact .inr (.inl ⟨rfl, lookup.symm⟩)
    · by_cases isNil : DataCtor.nil = constructor
      · subst constructor
        simp [lookup_data_nil] at lookup
        exact .inr (.inr (.inl ⟨rfl, lookup.symm⟩))
      · have isCons : DataCtor.cons = constructor := by
          by_cases isCons : DataCtor.cons = constructor
          · exact isCons
          · have impossible : False := by
              unfold FrozenSignature.lookupDataConstructor at lookup
              unfold Signature.lookupDataConstructor at lookup
              simp [signature, Paper1Signature.signature,
                Paper1Signature.dataConstructors, isTrue, isFalse, isNil,
                isCons] at lookup
            exact impossible.elim
        subst constructor
        simp [lookup_data_cons] at lookup
        exact .inr (.inr (.inr ⟨rfl, lookup.symm⟩))

/-- The Paper-1 frozen signature covers every constructor visible to source
elaboration with the corresponding runtime constructor typing. -/
theorem runtimeCompatible :
    Runtime.FrozenSignatureRuntimeCompatible signature := by
  refine
    { toSignatureCompatible := Runtime.paper1SignatureCompatible
      dataConstructorTyping := ?_ }
  intro constructor scheme supply fieldTypes resultType lookup peel
  rcases dataConstructor_lookup_cases lookup with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Scheme.callArity, ConstructorSchemes.boolTrue] at peel
    rcases peel with ⟨rfl, rfl⟩
    exact Runtime.RuntimeDataConstructorTyping.boolTrue
  · simp [Scheme.callArity, ConstructorSchemes.boolFalse] at peel
    rcases peel with ⟨rfl, rfl⟩
    exact Runtime.RuntimeDataConstructorTyping.boolFalse
  · simp [Scheme.callArity, ConstructorSchemes.listNil] at peel
    rcases peel with ⟨rfl, rfl⟩
    exact Runtime.RuntimeDataConstructorTyping.listNil (.var ⟨supply.ty⟩)
  · simp [Scheme.callArity, ConstructorSchemes.listCons] at peel
    rcases peel with ⟨rfl, rfl⟩
    exact Runtime.RuntimeDataConstructorTyping.listCons (.var ⟨supply.ty⟩)

end TypePM.Source.Paper1FrozenSignature
