import TypePM.OriginDemandSafety
import TypePM.Source.M4RawFiniteDemandCertificate

/-!
# Raw M4 bridge to structural source-origin demands

An exact numeric `M4.RawFuelCertificate` determines the finite ordinary-fuel
requirements of a plain lambda body before a semantic solution is supplied.
This module embeds those numeric argument and result requirements as `fuel`
leaves in the structural runtime demand tree.

The bridge contains no completed evaluator equation and no whole-program
safety premise.  Its scope is exactly the body expressions already carrying
a `RawFuelCertificate`; it is not a general raw M4 application or lambda
producer.  A general producer will need source-environment demands whose
entries are arbitrary `OriginDemand` trees rather than only numeric leaves.
-/

namespace TypePM.Source.M4

open TypePM.Runtime

/-- The exact tail demand on a plain lambda's captured environment. -/
def capturedDemand (demand : FuelDemand) : FuelDemand :=
  fun position => demand (position + 1)

/-- An exact numeric raw body certificate produces one source-origin call
contract with fuel leaves.  The argument index is the body's position-zero
demand; it is not identified with the result demand or operational fuel. -/
theorem RawFuelCertificate.plainCallSafe
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {body : Expr} {bodySupply next : Supply}
    {generatedBody : Generated} {solution : Subst} {domain : Ty}
    {bodyElaboration : ElaboratesFuel signature staticFuel
      (Source.Scheme.mono domain :: context) body bodySupply generatedBody
      next}
    {environment : ValueEnvironment}
    (bodyCertificate : RawFuelCertificate bodyElaboration)
    (semantic : generatedBody.SemanticSolution solution)
    (callFuel resultIndex : Nat)
    (capturedSafe : SchemeDemandEnvironmentSafe
      (capturedDemand
        (bodyCertificate.inputDemand callFuel resultIndex))
      solution environment context) :
    OriginValueSafe
      (PlainCallDemand.toOriginDemand
        ⟨callFuel + 1,
          bodyCertificate.inputDemand callFuel resultIndex 0,
          resultIndex⟩)
      (Value.plainClosure environment body)
      (.fn (domain.apply solution)
        (generatedBody.target.apply solution)) := by
  apply OriginValueSafe.plainClosure
  intro argument argumentSafe
  apply OriginResultSafe.ofFuel
  apply bodyCertificate.preserves solution semantic callFuel resultIndex
    (argument :: environment)
  have pushed := SchemeDemandEnvironmentSafe.cons
    (SchemeFuelValueSafe.ofMono argumentSafe.toFuel) capturedSafe
  apply pushed.congr
  intro position _positionLt
  cases position with
  | zero => rfl
  | succ position => rfl

end TypePM.Source.M4
