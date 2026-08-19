import TypePM.Source.GeneratedSupportBounds

/-!
# Stability of the fresh-name supply at a source `let`

An absorbing principal block closure is localized to the finite support of
the generated value block.  If that support comes either from the outer
context or from names allocated while elaborating the value, closing the
value cannot introduce a name beyond the supply returned by that
elaboration.  Consequently the defensive supply join at the `let` body is
equal to the returned value supply.
-/

namespace TypePM.Source

namespace PrincipalBlockClosure

/-- Closing a value block whose support has source provenance keeps the
substituted outer context below the value elaboration's finishing supply. -/
theorem closedContext_initialSupply_le
    {context : Context} {start finish : Supply} {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing)
    (provenance :
      GeneratedSupportProvenance context start finish generated)
    (wellFormed : start.WellFormedFor context)
    (increases : start.Le finish) :
    (context.applyFree closure.substitution).initialSupply.Le finish := by
  apply Context.applyFree_initialSupply_le_of_localized
    (closure.localized_of_absorbing absorbing) context finish
  · exact Supply.le_trans wellFormed increases
  · exact provenance.below wellFormed increases

/-- The `let` body starts exactly at the finishing supply of its value once
the value closure is known to be localized. -/
theorem letBodySupply_eq
    {context : Context} {start finish : Supply} {generated : Generated}
    (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing)
    (provenance :
      GeneratedSupportProvenance context start finish generated)
    (wellFormed : start.WellFormedFor context)
    (increases : start.Le finish) :
    finish.join (context.applyFree closure.substitution).initialSupply =
      finish :=
  Supply.letBodySupply_eq _ _
    (closedContext_initialSupply_le closure absorbing provenance
      wellFormed increases)

end PrincipalBlockClosure

namespace Elaborates

/-- Source elaboration supplies the provenance and monotonicity premises
needed by the generic closure lemma, so the body-side join of every
well-scoped `let` value is redundant. -/
theorem letBodySupply_eq
    {signature : Signature} {context : Context} {value : Expr} {start afterValue : Supply}
    {generatedValue : Generated}
    (valueElaboration :
      Elaborates signature context value start generatedValue afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (wellFormed : start.WellFormedFor context) :
    afterValue.join
        (context.applyFree closure.substitution).initialSupply =
      afterValue :=
  Supply.letBodySupply_eq _ _
    (valueElaboration.closedContext_initialSupply_le closure absorbing
      wellFormed)

end Elaborates

end TypePM.Source
