import TypePM.Source.M4TwoIndexUserMatcherReducerBridge

/-!
# M4 pattern evidence as two-index branch work

M4 pattern elaboration determines the source-ordered types contributed by a
delegated pattern list.  Actual matcher dispatch determines the concrete atoms
and preserves that pattern list, but the existing structural runtime theorem
in this repository also records value typing for every delegated target.  That
evidence is not available when the target is an actual recursive closure.

This module separates those concerns.  A `PatternsBind` derivation supplies
only M4's static binding behavior.  A bounded local obligation relates each
concrete delegated atom to a caller-selected two-index atom relation at the
corresponding M4 target type.  These inputs structurally generate
predecessor-indexed branch work and hence a
`TwoIndexPatternDispatchCertificate`.

The producer does not assume structural `EnvironmentTyping` or `ValueTyping`
for runtime values.  It also has no premise about successor-state typing, a
complete search result, or whole-expression evaluator safety.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- The local obligation for one concrete delegated atom at one exact positive
DFS index.  M4 supplies only the pattern's static binding behavior; the caller
relates the actual matcher/target pair to its selected atom relation.

No typing judgment for the atom's runtime matcher or target value is included. -/
structure M4TwoIndexMatchingAtomObligation
    (atomRelation : TwoIndexMatchingAtomRelation)
    (expressionTyping : EmbeddedExpressionTyping)
    (searchFuel residual : Nat) (environmentTypes bindingTypes : List Ty)
    (atom : MatchingAtom) (pattern : Pattern) (targetType : Ty)
    (newBindings : List Ty) : Prop where
  patternTyped : PatternBinds expressionTyping environmentTypes bindingTypes
    pattern targetType newBindings
  atomSafe : atom.pattern = pattern ∧
    atomRelation searchFuel residual environmentTypes bindingTypes atom
      newBindings

/-- Finite M4-guided branch obligations.  At zero, the list is traversed only
to retain M4's binding and pattern indices; no atom-safety premise is needed.
At a positive index, the head uses exactly that index and the tail is checked
at its strict predecessor. -/
inductive M4TwoIndexMatchingBranchObligations
    (atomRelation : TwoIndexMatchingAtomRelation)
    (expressionTyping : EmbeddedExpressionTyping) :
    Nat → Nat → List Ty → List Ty → List MatchingAtom →
      List Pattern → List Ty → List Ty → Prop where
  | nil : M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
      searchFuel residual environmentTypes bindingTypes [] [] [] []
  | zero
      (head : PatternBinds expressionTyping environmentTypes bindingTypes
        pattern targetType headBindings)
      (patternPreserved : atom.pattern = pattern)
      (tail : M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
        0 residual environmentTypes (bindingTypes ++ headBindings) atoms
        patterns targetTypes tailBindings) :
      M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
        0 residual environmentTypes bindingTypes (atom :: atoms)
        (pattern :: patterns) (targetType :: targetTypes)
        (headBindings ++ tailBindings)
  | cons
      (head : M4TwoIndexMatchingAtomObligation atomRelation expressionTyping
        (searchFuel + 1) residual environmentTypes bindingTypes atom pattern
        targetType headBindings)
      (tail : M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
        searchFuel residual environmentTypes (bindingTypes ++ headBindings)
        atoms patterns targetTypes tailBindings) :
      M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
        (searchFuel + 1) residual environmentTypes bindingTypes (atom :: atoms)
        (pattern :: patterns) (targetType :: targetTypes)
        (headBindings ++ tailBindings)

namespace M4TwoIndexMatchingBranchObligations

/-- Erase the M4 indices while retaining exactly the bounded caller-selected
branch work consumed by the two-index state producer. -/
theorem toRelationalTwoIndexMatchingBranchTyping
    (typing : M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
      searchFuel residual environmentTypes bindingTypes branch patterns
      targetTypes newBindings) :
    RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel residual
      environmentTypes bindingTypes branch newBindings := by
  induction typing with
  | nil => exact .nil
  | zero head patternPreserved tail induction => exact .zero (by simp)
  | cons head tail induction => exact .cons head.atomSafe.2 induction

/-- Every bounded obligation retains the exact common source-pattern list
stored by its concrete branch. -/
theorem patterns_eq
    (typing : M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
      searchFuel residual environmentTypes bindingTypes branch patterns
      targetTypes newBindings) :
    branch.map (fun atom => atom.pattern) = patterns := by
  induction typing with
  | nil => rfl
  | zero head patternPreserved tail induction =>
      simp [patternPreserved, induction]
  | cons head tail induction => simp [head.atomSafe.1, induction]

end M4TwoIndexMatchingBranchObligations

namespace TwoIndexPatternDispatchCertificate

/-- Successful exact dispatch is converted from finite M4-guided local atom
obligations.  Every branch is produced structurally;
the caller never supplies a successor-state certificate. -/
theorem hitOfM4BranchObligations
    (atomsSafe : ∀ branch ∈ branches,
      M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
        searchFuel residual environmentTypes bindingTypes branch patterns
        targetTypes newBindings) :
    TwoIndexPatternDispatchCertificate
      (relationalTwoIndexMatchingBranchRelation atomRelation) searchFuel
      residual environmentTypes bindingTypes newBindings
      (.ok (.hit branches)) := by
  apply TwoIndexPatternDispatchCertificate.hit
  · intro branch branchMember
    exact (atomsSafe branch branchMember).patterns_eq
  · intro branch branchMember
    exact (atomsSafe branch branchMember).toRelationalTwoIndexMatchingBranchTyping

end TwoIndexPatternDispatchCertificate

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- Single-pattern form used by a matcher clause whose successful dispatch
delegates one pattern position per branch.  It is the direct connection from
one solved M4 `PatternElaborates` derivation to caller-selected two-index
branch work. -/
theorem PatternElaborates.toSingletonTwoIndexDispatch
    (elaboration : PatternElaborates signature context
      arguments pattern bindings supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : DirectRuntimePatternSupported pattern)
    (semantic : GeneratedPatternRuntimeSolution generated solution)
    (contextCompatible :
      MonomorphicContextCompatible context environmentTypes solution)
    (atomsSafe : ∀ {newBindings},
      PatternBinds
          (fun runtimeContext expression target =>
            RuntimeTyping expression target runtimeContext)
          environmentTypes (Ty.applyList solution bindings) pattern
          (generated.dual.target.apply solution) newBindings →
        ∀ branch ∈ branches,
          M4TwoIndexMatchingBranchObligations atomRelation
            (fun runtimeContext expression target =>
              RuntimeTyping expression target runtimeContext)
            searchFuel residual environmentTypes
            (Ty.applyList solution bindings) branch [pattern]
            [generated.dual.target.apply solution] newBindings) :
    ∃ newBindings,
      TwoIndexPatternDispatchCertificate
        (relationalTwoIndexMatchingBranchRelation atomRelation) searchFuel
        residual environmentTypes (Ty.applyList solution bindings) newBindings
        (.ok (.hit branches)) ∧
      Ty.applyList solution generated.bindings =
        Ty.applyList solution bindings ++ newBindings := by
  obtain ⟨newBindings, patternTyped, bindingsEq⟩ :=
    TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
      elaboration compatible supported semantic contextCompatible
  exact ⟨newBindings,
    TwoIndexPatternDispatchCertificate.hitOfM4BranchObligations
      (atomsSafe patternTyped),
    bindingsEq⟩

/-- In the non-recursive case, the pattern-indexed branch evidence already
produced by M4 dispatch can be passed to the bounded caller obligation for the
same concrete branch.  The resulting two-index certificate itself retains only
the M4 pattern index and caller-selected atom relation. -/
theorem PatternIndexedDelegatedMatchingBranchesTyping.toTwoIndexDispatch
    (indexed : PatternIndexedDelegatedMatchingBranchesTyping patterns holes
      branches)
    (atomsSafe : ∀ branch ∈ branches,
      PatternIndexedDelegatedMatchingAtomsTyping branch patterns holes →
      M4TwoIndexMatchingBranchObligations atomRelation expressionTyping
        searchFuel residual environmentTypes bindingTypes branch patterns
        targetTypes newBindings) :
    TwoIndexPatternDispatchCertificate
      (relationalTwoIndexMatchingBranchRelation atomRelation) searchFuel
      residual environmentTypes bindingTypes newBindings
      (.ok (.hit branches)) := by
  apply TwoIndexPatternDispatchCertificate.hitOfM4BranchObligations
  intro branch branchMember
  exact atomsSafe branch branchMember
    (indexed.indexed_member branch branchMember)

/-- Direct-fragment M4 pattern elaboration chooses the source-ordered binding
types for an actual successful dispatch.  The only runtime-specific premise
is a pointwise obligation for each concrete atom at the corresponding M4
target type.

This corollary deliberately stops at a hit already classified by its exact
source patterns.  It does not invoke evaluator safety or the existing
structural M4 runtime dispatcher in this repository, so recursive-closure
callers need not manufacture structural typing for their runtime environment,
matcher, target, or answer. -/
theorem PatternsElaborate.toTwoIndexDispatch
    (elaboration : PatternsElaborate signature context
      arguments patterns bindings supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : DirectRuntimePatternsSupported patterns)
    (semantic : GeneratedPatternsRuntimeSolution generated solution)
    (contextCompatible :
      MonomorphicContextCompatible context environmentTypes solution)
    (atomsSafe : ∀ {newBindings},
      PatternsBind
          (fun runtimeContext expression target =>
            RuntimeTyping expression target runtimeContext)
          environmentTypes (Ty.applyList solution bindings) patterns
          (Ty.applyList solution (Dual.targets generated.duals)) newBindings →
        ∀ branch ∈ branches,
          M4TwoIndexMatchingBranchObligations atomRelation
            (fun runtimeContext expression target =>
              RuntimeTyping expression target runtimeContext)
            searchFuel residual environmentTypes
            (Ty.applyList solution bindings) branch patterns
            (Ty.applyList solution (Dual.targets generated.duals))
            newBindings) :
    ∃ newBindings,
      TwoIndexPatternDispatchCertificate
        (relationalTwoIndexMatchingBranchRelation atomRelation) searchFuel
        residual environmentTypes (Ty.applyList solution bindings) newBindings
        (.ok (.hit branches)) ∧
      Ty.applyList solution generated.bindings =
        Ty.applyList solution bindings ++ newBindings := by
  obtain ⟨newBindings, patternsTyped, bindingsEq⟩ :=
    TypePM.Source.MatcherTyping.PatternsElaborate.toDirectRuntimePatternsBind
      elaboration compatible supported semantic contextCompatible
  exact ⟨newBindings,
    TwoIndexPatternDispatchCertificate.hitOfM4BranchObligations
      (atomsSafe patternsTyped),
    bindingsEq⟩

end TypePM.Source.MatcherTyping
