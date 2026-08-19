import TypePM.Source.EntailedAlignment

/-!
# Structural source composition from entailed `letE` certificates

Raw `EntailedGeneratedAlignment` cannot be the result of the full source
induction: the source-derived counterexample has two `letE` blocks whose hard
worklists do not have the same solution set until an asymmetric fresh alias
is added.  The correct compositional endpoint is therefore the existing
scoped contextual comparison, while the sole `letE` premise is strengthened
to an `EntailedAlignmentCertificate`.

The ordinary constructor induction is exactly
`Elaborates.scopedComparison`; reusing it here is intentional.  Its mutual
recursor covers expressions, expression lists, and accumulated calls, and
already discharges the lambda, application, tuple, constructor, primitive,
conditional, item-list, and call freshness side conditions.
-/

namespace TypePM.Source

namespace EntailedElaborationComposition

/-- The result form used at a generated-expression boundary. -/
def Result (start leftNext rightNext : Supply)
    (left right : Generated) : Prop :=
  leftNext = rightNext ∧
    Nonempty
      (DirectGeneratedComparisonCertificate.DirectContextualGeneratedComparisonCertificate
        start leftNext left right)

/-- Repackage the existing scoped comparison without losing its hidden-name
interval. -/
theorem result_of_scoped
    {start leftNext rightNext : Supply} {left right : Generated}
    (comparison : ScopedGeneratedComparison start leftNext rightNext
      left right) :
    Result start leftNext rightNext left right := by
  obtain ⟨nextEquality, hidden, hiddenFresh, related⟩ := comparison
  subst rightNext
  exact ⟨rfl, ⟨
    { hidden := hidden
      hiddenFresh := hiddenFresh
      normalize := by
        intro frame frameAvoids
        exact related frame frameAvoids }⟩⟩

/-- All non-`letE` constructors are discharged by structural composition;
the `letE` case alone is supplied by `EntailedLetAlignmentHandler`. -/
theorem elaborates
    (letHandler : EntailedAlignmentCertificate.EntailedLetAlignmentHandler)
    {signature : Signature} {context : Context} {expression : Expr}
    {start : Supply} {leftGenerated rightGenerated : Generated}
    {leftNext rightNext : Supply}
    (leftElaboration : Elaborates signature context expression start
      leftGenerated leftNext)
    (rightElaboration : Elaborates signature context expression start
      rightGenerated rightNext)
    (wellFormed : start.WellFormedFor context) :
    Result start leftNext rightNext leftGenerated rightGenerated := by
  apply result_of_scoped
  exact Elaborates.scopedComparison
    (EntailedAlignmentCertificate.letComparisonHandler letHandler)
    leftElaboration rightElaboration wellFormed

/-- List counterpart.  The underlying mutual induction also covers every
accumulated constructor/primitive/conditional call. -/
theorem elaboratesItems
    (letHandler : EntailedAlignmentCertificate.EntailedLetAlignmentHandler)
    {signature : Signature} {context : Context} {expressions : List Expr}
    {start : Supply} {leftItems rightItems : GeneratedItems}
    {leftNext rightNext : Supply}
    (leftElaboration : ElaboratesItems signature context expressions start
      leftItems leftNext)
    (rightElaboration : ElaboratesItems signature context expressions start
      rightItems rightNext)
    (wellFormed : start.WellFormedFor context) :
    ScopedItemsComparison start leftNext rightNext leftItems rightItems :=
  ElaboratesItems.scopedComparison
    (EntailedAlignmentCertificate.letComparisonHandler letHandler)
    leftElaboration rightElaboration wellFormed

end EntailedElaborationComposition

end TypePM.Source
