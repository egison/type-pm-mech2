import TypePM.RuntimeTyping
import TypePM.Source.M4MatcherTyping

/-!
# Runtime compatibility for frozen source signatures

This module records the runtime obligations of an arbitrary frozen source
signature.  Compatibility with the evaluator's built-in declarations is not
enough on its own: every data-constructor declaration that source elaboration
can find must also produce a constructor typing supported by the runtime.

The constructor callback below is intentionally expressed at the instantiated,
curried-type boundary consumed by M4 data-pattern elaboration.  It does not
enumerate constructor names.  Every constructor visible through lookup must be
supported by `RuntimeDataConstructorTyping`; with the current fixed evaluator,
an unsupported additional declaration therefore cannot satisfy this contract.
-/

namespace TypePM.Runtime

/-- A frozen source signature agrees with the fixed runtime declarations, and
every successful data-constructor lookup is covered by runtime constructor
typing after its declared arguments have been peeled from one instantiation. -/
structure FrozenSignatureRuntimeCompatible
    (signature : Source.FrozenSignature) : Prop
    extends SignatureCompatible signature.base where
  dataConstructorTyping :
    ∀ {constructor : DataCtor} {scheme : Source.Scheme}
      {supply : Source.Supply} {fieldTypes : List Ty} {resultType : Ty},
      signature.lookupDataConstructor constructor = some scheme →
      Source.MatcherTyping.peelFunctionExact scheme.callArity
          (scheme.instantiate supply).1 = some (fieldTypes, resultType) →
      RuntimeDataConstructorTyping constructor fieldTypes resultType

/-- Runtime constructor typing is stable under a simultaneous type and
capability substitution. -/
theorem RuntimeDataConstructorTyping.apply
    (typing : RuntimeDataConstructorTyping constructor fieldTypes resultType)
    (substitution : Subst) :
    RuntimeDataConstructorTyping constructor
      (Ty.applyList substitution fieldTypes) (resultType.apply substitution) := by
  cases typing with
  | boolTrue =>
      simpa [Ty.apply, Ty.applyList, DataTypes.bool] using
        (RuntimeDataConstructorTyping.boolTrue :
          RuntimeDataConstructorTyping DataCtor.true [] DataTypes.bool)
  | boolFalse =>
      simpa [Ty.apply, Ty.applyList, DataTypes.bool] using
        (RuntimeDataConstructorTyping.boolFalse :
          RuntimeDataConstructorTyping DataCtor.false [] DataTypes.bool)
  | listNil element =>
      simpa [Ty.apply, Ty.applyList, DataTypes.list] using
        RuntimeDataConstructorTyping.listNil (element.apply substitution)
  | listCons element =>
      simpa [Ty.apply, Ty.applyList, DataTypes.list] using
        RuntimeDataConstructorTyping.listCons (element.apply substitution)

/-- Consume the generic frozen-signature contract in the exact solved shape
needed by an M4 data-pattern constructor. -/
theorem FrozenSignatureRuntimeCompatible.dataConstructorTyping_of_m4
    {signature : Source.FrozenSignature}
    (compatible : FrozenSignatureRuntimeCompatible signature)
    {constructor : DataCtor} {scheme : Source.Scheme} {supply : Source.Supply}
    {arity : Nat} {fieldTypes : List Ty} {resultType expected : Ty}
    (lookup : signature.lookupDataConstructor constructor = some scheme)
    (fieldArity : arity = scheme.callArity)
    (peel : Source.MatcherTyping.peelFunctionExact arity
      (scheme.instantiate supply).1 = some (fieldTypes, resultType))
    (resultSolved :
      (Equation.ty resultType expected).Holds solution) :
    RuntimeDataConstructorTyping constructor
      (Ty.applyList solution fieldTypes) (expected.apply solution) := by
  rw [fieldArity] at peel
  have typing := compatible.dataConstructorTyping lookup peel
  simp only [Equation.Holds] at resultSolved
  rw [← resultSolved]
  exact typing.apply solution

end TypePM.Runtime
