import TypePM.FuelUserMatcherGeneralSafety
import TypePM.Source.M4TwoIndexBuiltinAtomProducer

/-!
# Canonical two-index reduction for built-in and user matcher atoms

This module closes one user-matcher layer over an arbitrary delegated atom
relation.  The closure contains the delegated relation itself, canonical M4
built-in evidence, and user-matcher atoms whose exact clause dispatch is
certified in the delegated relation.  Iterating the closure therefore handles
nested user matchers without fixing a concrete program, completed search, or
fuel value.

The fuel-indexed user-matcher lemmas expose safety of the concrete delegated
branches.  The conversion lemmas below combine that evidence with M4
`PatternsBind` derivations before constructing the two-index dispatch
certificate consumed by the local reducer theorem.
-/

namespace TypePM.Runtime

open TypePM.Source
open TypePM.Source.MatcherTyping

namespace RelationalTwoIndexMatchingBranchTyping

/-- Structural branch typing is monotone in its selected atom relation. -/
theorem map
    (embedding : ∀ {searchFuel residual environmentTypes bindingTypes atom
        newBindings},
      sourceRelation searchFuel residual environmentTypes bindingTypes atom
        newBindings →
      targetRelation searchFuel residual environmentTypes bindingTypes atom
        newBindings)
    (typing : RelationalTwoIndexMatchingBranchTyping sourceRelation searchFuel
      residual environmentTypes bindingTypes atoms newBindings) :
    RelationalTwoIndexMatchingBranchTyping targetRelation searchFuel residual
      environmentTypes bindingTypes atoms newBindings := by
  induction typing with
  | zero nonempty => exact .zero nonempty
  | nil => exact .nil
  | cons head tail induction => exact .cons (embedding head) induction

end RelationalTwoIndexMatchingBranchTyping

namespace FuelDelegatedMatchingAtomsSafe

/-- Delegated atom safety may be weakened pointwise to a smaller logical
index. -/
theorem mono
    (safe : FuelDelegatedMatchingAtomsSafe larger atoms holes)
    (smaller_le : smaller ≤ larger) :
    FuelDelegatedMatchingAtomsSafe smaller atoms holes := by
  induction safe with
  | nil => exact .nil
  | cons matcher target tail induction =>
      exact .cons (matcher.mono smaller_le) (target.mono smaller_le) induction

private theorem toM4TwoIndexBranchObligations_zero
    (safe : FuelDelegatedMatchingAtomsSafe fuel atoms holes)
    (patternsPreserved : atoms.map (fun atom => atom.pattern) = patterns)
    (patternsTyped : PatternsBind expressionTyping environmentTypes
      bindingTypes patterns (Dual.targets holes) newBindings) :
    M4TwoIndexMatchingBranchObligations delegatedRelation expressionTyping
      0 residual environmentTypes bindingTypes atoms patterns
      (Dual.targets holes) newBindings := by
  induction safe generalizing bindingTypes patterns newBindings with
  | nil =>
      cases patternsTyped
      exact .nil
  | @cons matcherValue targetValue tailAtoms tailHoles actualPattern hole
      matcherSafe targetSafe tailSafe induction =>
      cases patternsTyped with
      | cons headTyped tailTyped =>
          simp only [List.map_cons, List.cons.injEq] at patternsPreserved
          obtain ⟨headEq, tailEq⟩ := patternsPreserved
          subst actualPattern
          exact .zero headTyped rfl (induction tailEq tailTyped)

/-- Fuel-safe delegated atoms and the corresponding M4 pattern-list binding
derivation generate bounded branch obligations.  The pointwise premise is the
only place where a caller chooses how a fuel-safe matcher/target pair enters
the delegated atom relation. -/
theorem toM4TwoIndexBranchObligations
    (safe : FuelDelegatedMatchingAtomsSafe
      (searchFuel + 1 + residual) atoms holes)
    (patternsPreserved : atoms.map (fun atom => atom.pattern) = patterns)
    (patternsTyped : PatternsBind expressionTyping environmentTypes
      bindingTypes patterns (Dual.targets holes) newBindings)
    (atomSafe : ∀ {atomFuel bindingTypes pattern matcherValue targetValue}
        {hole : Dual} {headBindings},
      PatternBinds expressionTyping environmentTypes bindingTypes pattern
        hole.target headBindings →
      FuelValueSafe (atomFuel + residual) matcherValue
        (.slot hole.capability hole.target) →
      FuelValueSafe (atomFuel + residual) targetValue hole.target →
      delegatedRelation atomFuel residual environmentTypes bindingTypes
        ⟨pattern, matcherValue, targetValue⟩ headBindings) :
    M4TwoIndexMatchingBranchObligations delegatedRelation expressionTyping
      searchFuel residual environmentTypes bindingTypes atoms patterns
      (Dual.targets holes) newBindings := by
  induction searchFuel generalizing bindingTypes atoms holes patterns
      newBindings with
  | zero =>
      exact toM4TwoIndexBranchObligations_zero safe patternsPreserved
        patternsTyped
  | succ searchFuel induction =>
      cases safe with
      | nil =>
          cases patternsTyped
          exact .nil
      | @cons matcherValue targetValue tailAtoms tailHoles actualPattern hole
          matcherSafe targetSafe tailSafe =>
          cases patternsTyped with
          | cons headTyped tailTyped =>
              simp only [List.map_cons, List.cons.injEq] at patternsPreserved
              obtain ⟨headEq, tailEq⟩ := patternsPreserved
              subst actualPattern
              apply M4TwoIndexMatchingBranchObligations.cons
              · exact ⟨headTyped, rfl,
                  atomSafe headTyped
                    (matcherSafe.mono (by omega))
                    (targetSafe.mono (by omega))⟩
              · apply induction
                  (tailSafe.mono (by omega)) tailEq tailTyped

end FuelDelegatedMatchingAtomsSafe

namespace FuelDelegatedMatchingBranchesSafe

/-- Project fuel-indexed delegated-atom safety for an actual returned branch. -/
theorem member
    (safe : FuelDelegatedMatchingBranchesSafe fuel holes branches)
    (branchMember : branch ∈ branches) :
    FuelDelegatedMatchingAtomsSafe fuel branch holes := by
  induction safe with
  | nil => simp at branchMember
  | cons head tail induction =>
      simp only [List.mem_cons] at branchMember
      rcases branchMember with rfl | branchMember
      · exact head
      · exact induction branchMember

/-- A fuel-safe successful user dispatch becomes the exact two-index dispatch
certificate once M4 supplies the common pattern binding derivation and the
caller embeds every delegated matcher/target pair in its atom relation. -/
theorem toTwoIndexPatternDispatchCertificate
    (safe : FuelDelegatedMatchingBranchesSafe
      (searchFuel + 1 + residual) holes branches)
    (patternsPreserved : ∀ branch ∈ branches,
      branch.map (fun atom => atom.pattern) = patterns)
    (patternsTyped : PatternsBind expressionTyping environmentTypes
      bindingTypes patterns (Dual.targets holes) newBindings)
    (atomSafe : ∀ {atomFuel bindingTypes pattern matcherValue targetValue}
        {hole : Dual} {headBindings},
      PatternBinds expressionTyping environmentTypes bindingTypes pattern
        hole.target headBindings →
      FuelValueSafe (atomFuel + residual) matcherValue
        (.slot hole.capability hole.target) →
      FuelValueSafe (atomFuel + residual) targetValue hole.target →
      delegatedRelation atomFuel residual environmentTypes bindingTypes
        ⟨pattern, matcherValue, targetValue⟩ headBindings) :
    TwoIndexPatternDispatchCertificate
      (relationalTwoIndexMatchingBranchRelation delegatedRelation) searchFuel
      residual environmentTypes bindingTypes newBindings (.ok (.hit branches)) := by
  apply TwoIndexPatternDispatchCertificate.hit patternsPreserved
  intro branch branchMember
  exact (safe.member branchMember).toM4TwoIndexBranchObligations
    (patternsPreserved branch branchMember) patternsTyped atomSafe |>
      M4TwoIndexMatchingBranchObligations.toRelationalTwoIndexMatchingBranchTyping

end FuelDelegatedMatchingBranchesSafe

/-- Close a delegated atom relation under canonical M4 built-ins and one
fuel-indexed user-matcher dispatch step.  A user certificate is uniform in
the concrete atom environment; its only environment premise is the indexed
safety supplied by `TwoIndexRelationalAtomReducerTypedSafe`.

The successful delegated branches live in `delegatedRelation` at the strict
predecessor search index. -/
inductive M4TwoIndexCanonicalMatchingAtomEvidence
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value)
    (delegatedRelation : TwoIndexMatchingAtomRelation) :
    TwoIndexMatchingAtomRelation where
  | delegated
      (typed : delegatedRelation searchFuel residual environmentTypes
        bindingTypes atom newBindings) :
      M4TwoIndexCanonicalMatchingAtomEvidence expressionTyping eval
        delegatedRelation searchFuel residual environmentTypes bindingTypes
        atom newBindings
  | builtin
      (typed : M4BuiltinTwoIndexMatchingAtomEvidence expressionTyping
        searchFuel residual environmentTypes bindingTypes atom newBindings) :
      M4TwoIndexCanonicalMatchingAtomEvidence expressionTyping eval
        delegatedRelation searchFuel residual environmentTypes bindingTypes
        atom newBindings
  | user
      (dispatchable : MatcherDispatchable pattern)
      (dispatchTyped : ∀ {runtimeFuel atomEnvironment},
        FuelEnvironmentSafe runtimeFuel atomEnvironment
          (bindingTypes ++ environmentTypes) →
        TwoIndexPatternDispatchCertificate
          (relationalTwoIndexMatchingBranchRelation delegatedRelation)
          searchFuel residual environmentTypes bindingTypes newBindings
          (dispatchMatcherClauses eval atomEnvironment matcherEnvironment
            remainingClauses pattern target)) :
      M4TwoIndexCanonicalMatchingAtomEvidence expressionTyping eval
        delegatedRelation (searchFuel + 1) residual environmentTypes
        bindingTypes
        ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
          target⟩
        newBindings


/-- The canonical one-layer closure is downward closed whenever its delegated
relation is downward closed. -/
theorem m4TwoIndexCanonicalMatchingAtomEvidence_downwardClosed
    (delegatedDownward :
      TwoIndexMatchingAtomRelation.DownwardClosed delegatedRelation) :
    TwoIndexMatchingAtomRelation.DownwardClosed
      (M4TwoIndexCanonicalMatchingAtomEvidence expressionTyping eval
        delegatedRelation) := by
  intro searchFuel residual environmentTypes bindingTypes atom newBindings typed
  cases typed with
  | delegated delegatedTyped =>
      exact .delegated (delegatedDownward delegatedTyped)
  | builtin builtinTyped =>
      exact .builtin
        (m4BuiltinTwoIndexMatchingAtomEvidence_downwardClosed builtinTyped)
  | user dispatchable dispatchTyped =>
      apply M4TwoIndexCanonicalMatchingAtomEvidence.user dispatchable
      intro runtimeFuel atomEnvironment environmentSafe
      exact (dispatchTyped environmentSafe).previous
        (relationalTwoIndexMatchingBranchRelation_downwardClosed
          delegatedDownward)

/-- Local preservation for the canonical built-in/user closure.  The
delegated relation supplies its own local reducer law; built-ins use the M4
canonical theorem; and user atoms consume only their exact dispatch
certificate. -/
theorem evaluationAtomReducer_m4TwoIndexCanonicalTypedSafe
    (evalSafe : TwoIndexEmbeddedEvaluatorSafe expressionTyping eval)
    (delegatedReducerSafe : TwoIndexRelationalAtomReducerTypedSafe
      FuelEnvironmentSafe FuelEnvironmentSafe delegatedRelation
      (evaluationAtomReducer eval)) :
    TwoIndexRelationalAtomReducerTypedSafe FuelEnvironmentSafe
      FuelEnvironmentSafe
      (M4TwoIndexCanonicalMatchingAtomEvidence expressionTyping eval
        delegatedRelation)
      (evaluationAtomReducer eval) := by
  intro searchFuel residual environmentTypes bindingTypes environment bindings
    atom newBindings environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | delegated delegatedTyped =>
      rcases delegatedReducerSafe environmentTyped bindingsTyped
          delegatedTyped with timeout | ⟨reduction, success, reductionTyped⟩
      · exact .inl timeout
      · refine .inr ⟨reduction, success, ?_⟩
        cases reductionTyped with
        | intro immediateTypes immediateTyped branchesTyped =>
            exact .intro immediateTypes immediateTyped (by
              intro branch branchMember
              obtain ⟨delayedTypes, branchTyped, bindingsEq⟩ :=
                branchesTyped branch branchMember
              exact ⟨delayedTypes,
                branchTyped.map (fun typed =>
                  M4TwoIndexCanonicalMatchingAtomEvidence.delegated typed),
                bindingsEq⟩)
  | builtin builtinTyped =>
      rcases evaluationAtomReducer_m4BuiltinTwoIndexTypedSafe evalSafe
          environmentTyped bindingsTyped builtinTyped with
        timeout | ⟨reduction, success, reductionTyped⟩
      · exact .inl timeout
      · refine .inr ⟨reduction, success, ?_⟩
        cases reductionTyped with
        | intro immediateTypes immediateTyped branchesTyped =>
            exact .intro immediateTypes immediateTyped (by
              intro branch branchMember
              obtain ⟨delayedTypes, branchTyped, bindingsEq⟩ :=
                branchesTyped branch branchMember
              exact ⟨delayedTypes,
                branchTyped.map (fun typed =>
                  M4TwoIndexCanonicalMatchingAtomEvidence.builtin typed),
                bindingsEq⟩)
  | user dispatchable dispatchTyped =>
      rename_i pattern matcherEnvironment remainingClauses target original
      have atomEnvironmentSafe : FuelEnvironmentSafe
          (searchFuel + 1 + residual) (bindings ++ environment)
          (bindingTypes ++ environmentTypes) :=
        bindingsTyped.append environmentTyped
      have classified := dispatchTyped atomEnvironmentSafe
      generalize dispatchEq :
          dispatchMatcherClauses eval (bindings ++ environment)
            matcherEnvironment remainingClauses pattern target = dispatchResult
        at classified
      have builtinMiss := reduceBuiltinAtom_matcherV_miss eval
        (bindings ++ environment) matcherEnvironment original remainingClauses
        pattern target dispatchable
      cases classified with
      | timeout =>
          exact .inl (by
            unfold evaluationAtomReducer combineAtomReducers
            rw [builtinMiss]
            simp only [FuelResult.bind]
            simpa [reduceMatcherAtom] using
              congrArg (FuelResult.map clauseResultToAtomReduction) dispatchEq)
      | hit patternsPreserved branchesRelated =>
          rename_i branches patterns
          let reduction : AtomReduction := ⟨branches, []⟩
          refine .inr ⟨reduction, ?_, ?_⟩
          · unfold evaluationAtomReducer combineAtomReducers
            rw [builtinMiss]
            simp only [FuelResult.bind]
            simpa [reduceMatcherAtom, reduction, clauseResultToAtomReduction]
              using congrArg (FuelResult.map clauseResultToAtomReduction)
                dispatchEq
          · exact .intro [] (.nil _) (by
              intro branch branchMember
              exact ⟨newBindings,
                by simpa using
                  (branchesRelated branch branchMember).map (fun typed =>
                    M4TwoIndexCanonicalMatchingAtomEvidence.delegated typed),
                rfl⟩)

mutual

  /-- Fixed canonical atom relation for arbitrary recursive user-matcher
  depth.  A user atom carries dispatch certificates at every predecessor
  index no larger than its current search bound, so downward closure does not
  require a finite manual nesting depth. -/
  inductive M4TwoIndexRecursiveCanonicalMatchingAtomEvidence
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      TwoIndexMatchingAtomRelation where
    | builtin
        (typed : M4BuiltinTwoIndexMatchingAtomEvidence expressionTyping
          searchFuel residual environmentTypes bindingTypes atom newBindings) :
        M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping eval
          searchFuel residual environmentTypes bindingTypes atom newBindings
    | user
        (dispatchable : MatcherDispatchable pattern)
        (dispatchTyped : ∀ {branchFuel runtimeFuel atomEnvironment},
          branchFuel ≤ searchFuel →
          FuelEnvironmentSafe runtimeFuel atomEnvironment
            (bindingTypes ++ environmentTypes) →
          M4TwoIndexRecursiveCanonicalPatternDispatchCertificate
            expressionTyping eval branchFuel residual environmentTypes
            bindingTypes newBindings
            (dispatchMatcherClauses eval atomEnvironment matcherEnvironment
              remainingClauses pattern target)) :
        M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping eval
          (searchFuel + 1) residual environmentTypes bindingTypes
          ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
            target⟩
          newBindings

  /-- Structural branch work for the fixed recursive canonical relation. -/
  inductive M4TwoIndexRecursiveCanonicalBranchTyping
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      Nat → Nat → List Ty → List Ty → List MatchingAtom → List Ty → Prop where
    | zero
        (nonempty : atoms ≠ []) :
        M4TwoIndexRecursiveCanonicalBranchTyping expressionTyping eval 0
          residual environmentTypes bindingTypes atoms newBindings
    | nil :
        M4TwoIndexRecursiveCanonicalBranchTyping expressionTyping eval
          searchFuel residual environmentTypes bindingTypes [] []
    | cons
        (head : M4TwoIndexRecursiveCanonicalMatchingAtomEvidence
          expressionTyping eval (searchFuel + 1) residual environmentTypes
          bindingTypes atom headBindings)
        (tail : M4TwoIndexRecursiveCanonicalBranchTyping expressionTyping eval
          searchFuel residual environmentTypes (bindingTypes ++ headBindings)
          atoms tailBindings) :
        M4TwoIndexRecursiveCanonicalBranchTyping expressionTyping eval
          (searchFuel + 1) residual environmentTypes bindingTypes
          (atom :: atoms) (headBindings ++ tailBindings)

  /-- Exact timeout-or-hit dispatch certificate whose successful branches are
  recursively canonical at the selected predecessor index. -/
  inductive M4TwoIndexRecursiveCanonicalPatternDispatchCertificate
      (expressionTyping : EmbeddedExpressionTyping)
      (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
      Nat → Nat → List Ty → List Ty → List Ty →
        FuelResult (DispatchResult MatchingBranches) → Prop where
    | timeout :
        M4TwoIndexRecursiveCanonicalPatternDispatchCertificate expressionTyping
          eval searchFuel residual environmentTypes bindingTypes newBindings
          .timeout
    | hit
        (patternsPreserved : ∀ branch ∈ branches,
          branch.map (fun atom => atom.pattern) = patterns)
        (branchesTyped : ∀ branch ∈ branches,
          M4TwoIndexRecursiveCanonicalBranchTyping expressionTyping eval
            searchFuel residual environmentTypes bindingTypes branch
            newBindings) :
        M4TwoIndexRecursiveCanonicalPatternDispatchCertificate expressionTyping
          eval searchFuel residual environmentTypes bindingTypes newBindings
          (.ok (.hit branches))

end

namespace M4TwoIndexRecursiveCanonicalBranchTyping

/-- Erase the mutually defined branch certificate to the generic relational
branch relation used by the two-index DFS theorem. -/
theorem toRelational
    (typing : M4TwoIndexRecursiveCanonicalBranchTyping expressionTyping eval
      searchFuel residual environmentTypes bindingTypes atoms newBindings) :
    RelationalTwoIndexMatchingBranchTyping
      (M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping eval)
      searchFuel residual environmentTypes bindingTypes atoms newBindings := by
  induction searchFuel generalizing bindingTypes atoms newBindings with
  | zero =>
      cases typing with
      | zero nonempty => exact .zero nonempty
      | nil => exact .nil
  | succ searchFuel induction =>
      cases typing with
      | nil => exact .nil
      | cons head tail => exact .cons head (induction tail)

/-- Repackage generic relational work for the fixed canonical atom relation. -/
theorem ofRelational
    (typing : RelationalTwoIndexMatchingBranchTyping
      (M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping eval)
      searchFuel residual environmentTypes bindingTypes atoms newBindings) :
    M4TwoIndexRecursiveCanonicalBranchTyping expressionTyping eval searchFuel
      residual environmentTypes bindingTypes atoms newBindings := by
  induction typing with
  | zero nonempty => exact .zero nonempty
  | nil => exact .nil
  | cons head tail induction => exact .cons head induction

end M4TwoIndexRecursiveCanonicalBranchTyping

namespace M4TwoIndexRecursiveCanonicalPatternDispatchCertificate

/-- Convert the generic dispatch vocabulary specialized to the fixed
canonical relation into its mutually recursive certificate. -/
theorem ofTwoIndex
    (typing : TwoIndexPatternDispatchCertificate
      (relationalTwoIndexMatchingBranchRelation
        (M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping eval))
      searchFuel residual environmentTypes bindingTypes newBindings result) :
    M4TwoIndexRecursiveCanonicalPatternDispatchCertificate expressionTyping
      eval searchFuel residual environmentTypes bindingTypes newBindings
      result := by
  cases typing with
  | timeout => exact .timeout
  | hit patternsPreserved branchesRelated =>
      exact .hit patternsPreserved (by
        intro branch branchMember
        exact M4TwoIndexRecursiveCanonicalBranchTyping.ofRelational
          (branchesRelated branch branchMember))

end M4TwoIndexRecursiveCanonicalPatternDispatchCertificate

/-- The fixed recursive canonical relation is downward closed at every search
index.  The uniform bounded dispatch field is simply restricted to the
smaller predecessor range. -/
theorem m4TwoIndexRecursiveCanonicalMatchingAtomEvidence_downwardClosed :
    TwoIndexMatchingAtomRelation.DownwardClosed
      (M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping eval) := by
  intro searchFuel residual environmentTypes bindingTypes atom newBindings typed
  cases typed with
  | builtin builtinTyped =>
      exact .builtin
        (m4BuiltinTwoIndexMatchingAtomEvidence_downwardClosed builtinTyped)
  | user dispatchable dispatchTyped =>
      apply M4TwoIndexRecursiveCanonicalMatchingAtomEvidence.user dispatchable
      intro branchFuel runtimeFuel atomEnvironment branchLe environmentSafe
      exact dispatchTyped (Nat.le_trans branchLe (Nat.le_succ _)) environmentSafe

/-- G6 fixed point: the combined evaluator preserves the recursive canonical
relation for arbitrary search fuel.  Every recursive user branch is already
certified at the strict predecessor index by the mutual dispatch relation. -/
theorem evaluationAtomReducer_m4TwoIndexRecursiveCanonicalTypedSafe
    (evalSafe : TwoIndexEmbeddedEvaluatorSafe expressionTyping eval) :
    TwoIndexRelationalAtomReducerTypedSafe FuelEnvironmentSafe
      FuelEnvironmentSafe
      (M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping eval)
      (evaluationAtomReducer eval) := by
  intro searchFuel residual environmentTypes bindingTypes environment bindings
    atom newBindings environmentTyped bindingsTyped atomTyped
  cases atomTyped with
  | builtin builtinTyped =>
      rcases evaluationAtomReducer_m4BuiltinTwoIndexTypedSafe evalSafe
          environmentTyped bindingsTyped builtinTyped with
        timeout | ⟨reduction, success, reductionTyped⟩
      · exact .inl timeout
      · refine .inr ⟨reduction, success, ?_⟩
        cases reductionTyped with
        | intro immediateTypes immediateTyped branchesTyped =>
            exact .intro immediateTypes immediateTyped (by
              intro branch branchMember
              obtain ⟨delayedTypes, branchTyped, bindingsEq⟩ :=
                branchesTyped branch branchMember
              exact ⟨delayedTypes,
                branchTyped.map (fun typed =>
                  M4TwoIndexRecursiveCanonicalMatchingAtomEvidence.builtin
                    typed),
                bindingsEq⟩)
  | user dispatchable dispatchTyped =>
      rename_i pattern matcherEnvironment remainingClauses target original
      have atomEnvironmentSafe : FuelEnvironmentSafe
          (searchFuel + 1 + residual) (bindings ++ environment)
          (bindingTypes ++ environmentTypes) :=
        bindingsTyped.append environmentTyped
      have classified := dispatchTyped (Nat.le_refl searchFuel)
        atomEnvironmentSafe
      generalize dispatchEq :
          dispatchMatcherClauses eval (bindings ++ environment)
            matcherEnvironment remainingClauses pattern target = dispatchResult
        at classified
      have builtinMiss := reduceBuiltinAtom_matcherV_miss eval
        (bindings ++ environment) matcherEnvironment original remainingClauses
        pattern target dispatchable
      cases classified with
      | timeout =>
          exact .inl (by
            unfold evaluationAtomReducer combineAtomReducers
            rw [builtinMiss]
            simp only [FuelResult.bind]
            simpa [reduceMatcherAtom] using
              congrArg (FuelResult.map clauseResultToAtomReduction) dispatchEq)
      | hit patternsPreserved branchesTyped =>
          rename_i branches patterns
          let reduction : AtomReduction := ⟨branches, []⟩
          refine .inr ⟨reduction, ?_, ?_⟩
          · unfold evaluationAtomReducer combineAtomReducers
            rw [builtinMiss]
            simp only [FuelResult.bind]
            simpa [reduceMatcherAtom, reduction, clauseResultToAtomReduction]
              using congrArg (FuelResult.map clauseResultToAtomReduction)
                dispatchEq
          · exact .intro [] (.nil _) (by
              intro branch branchMember
              exact ⟨newBindings, by simpa using
                (branchesTyped branch branchMember).toRelational, rfl⟩)

/-- G5--G6 bridge: ordered clause certificates with a declarative final
catch-all construct one recursive canonical user atom.  The caller supplies
only the M4-guided conversion of the fuel-safe concrete branches; dispatch
classification itself comes from `FuelMatcherClausesCertificates`.

`operationalFuel` is fixed for every embedded clause evaluation, while
`branchFuel` ranges over all predecessor DFS indices required by recursive
canonical closure. -/
theorem M4TwoIndexRecursiveCanonicalMatchingAtomEvidence.userOfOrderedClauses
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (dispatchable : MatcherDispatchable pattern)
    (targetTyped : ValueTyping target matcherTarget)
    (finalCatchAll : MatcherTyping.FinalCatchAll remainingClauses)
    (clausesCertificates : ∀ {branchFuel runtimeFuel atomEnvironment},
      branchFuel ≤ searchFuel →
      FuelEnvironmentSafe runtimeFuel atomEnvironment
        (bindingTypes ++ environmentTypes) →
      FuelMatcherClausesCertificates Certificate operationalFuel
        (branchFuel + residual) (bindingTypes ++ environmentTypes)
        definitionTypes matcherTarget atomEnvironment matcherEnvironment
        pattern target remainingClauses)
    (branchesCanonical : ∀ {branchFuel holes branches},
      FuelDelegatedMatchingBranchesSafe (branchFuel + residual + 1) holes
        branches →
      ∃ patterns,
        (∀ branch ∈ branches,
          branch.map (fun atom => atom.pattern) = patterns) ∧
        ∀ branch ∈ branches,
          M4TwoIndexRecursiveCanonicalBranchTyping expressionTyping
            (evaluate operationalFuel) branchFuel residual environmentTypes
            bindingTypes branch newBindings) :
    M4TwoIndexRecursiveCanonicalMatchingAtomEvidence expressionTyping
      (evaluate operationalFuel) (searchFuel + 1) residual environmentTypes
      bindingTypes
      ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
        target⟩
      newBindings := by
  apply M4TwoIndexRecursiveCanonicalMatchingAtomEvidence.user dispatchable
  intro branchFuel runtimeFuel atomEnvironment branchLe atomEnvironmentSafe
  have certificates := clausesCertificates branchLe atomEnvironmentSafe
  rcases certificates.dispatch_fuelSafe_of_finalCatchAll
      (evaluate := evaluate) evalSafe targetTyped finalCatchAll with
    timeout | ⟨branches, holes, success, branchesSafe⟩
  · rw [timeout]
    exact .timeout
  · rw [success]
    obtain ⟨patterns, patternsPreserved, branchesTyped⟩ :=
      branchesCanonical (by simpa [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using branchesSafe)
    exact .hit patternsPreserved branchesTyped

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- Solved M4 pattern-list elaboration and fuel-safe delegated branches jointly
produce the exact two-index dispatch certificate.  The equality premise only
aligns the runtime holes retained by user dispatch with the solved M4 target
types; matcher capabilities remain available to the pointwise atom premise. -/
theorem PatternsElaborate.toFuelDelegatedTwoIndexDispatch
    (elaboration : PatternsElaborate signature context arguments patterns
      bindings supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : DirectRuntimePatternsSupported patterns)
    (semantic : GeneratedPatternsRuntimeSolution generated solution)
    (contextCompatible :
      MonomorphicContextCompatible context environmentTypes solution)
    (branchesSafe : FuelDelegatedMatchingBranchesSafe
      (searchFuel + 1 + residual) holes branches)
    (targetTypesEq :
      Ty.applyList solution (Dual.targets generated.duals) =
        Dual.targets holes)
    (patternsPreserved : ∀ branch ∈ branches,
      branch.map (fun atom => atom.pattern) = patterns)
    (atomSafe : ∀ {atomFuel bindingTypes pattern matcherValue targetValue}
        {hole : Dual} {headBindings},
      PatternBinds
          (fun runtimeContext expression target =>
            RuntimeTyping expression target runtimeContext)
          environmentTypes bindingTypes pattern hole.target headBindings →
      FuelValueSafe (atomFuel + residual) matcherValue
        (.slot hole.capability hole.target) →
      FuelValueSafe (atomFuel + residual) targetValue hole.target →
      delegatedRelation atomFuel residual environmentTypes bindingTypes
        ⟨pattern, matcherValue, targetValue⟩ headBindings) :
    ∃ newBindings,
      TwoIndexPatternDispatchCertificate
        (relationalTwoIndexMatchingBranchRelation delegatedRelation) searchFuel
        residual environmentTypes (Ty.applyList solution bindings) newBindings
        (.ok (.hit branches)) ∧
      Ty.applyList solution generated.bindings =
        Ty.applyList solution bindings ++ newBindings := by
  apply PatternsElaborate.toTwoIndexDispatch elaboration compatible supported
    semantic contextCompatible
  intro newBindings patternsTyped branch branchMember
  have alignedPatternsTyped : PatternsBind
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes (Ty.applyList solution bindings) patterns
      (Dual.targets holes) newBindings := by
    rw [← targetTypesEq]
    exact patternsTyped
  simpa [targetTypesEq] using
    (branchesSafe.member branchMember).toM4TwoIndexBranchObligations
      (patternsPreserved branch branchMember) alignedPatternsTyped atomSafe

end TypePM.Source.MatcherTyping
