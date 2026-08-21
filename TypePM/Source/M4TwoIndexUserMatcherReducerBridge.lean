import TypePM.TwoIndexMatchingSearchSafety
import TypePM.Source.M4PatternIndexedRecursiveDispatchBridge

/-!
# Relation-parametric two-index user-matcher reduction

`TwoIndexMatchingSearchSafety` consumes local reducer certificates, while the
existing structural M4 pattern-indexed dispatch relation fixes successful
branch work to a judgment whose built-in cases use structural `ValueTyping`.
That prevents a positive-index branch from binding an actual recursive
closure even when the closure is safe in the caller's logical relation.

This module separates three proof layers:

* a caller-selected atom relation, indexed independently by DFS visits and a
  retained logical index;
* a structural branch-work relation generated from that atom relation;
* an exact dispatch certificate retaining membership in the actual returned
  branch list and the common pattern list stored by each branch.

A local reducer law turns structural branch work into two-index state typing.
The user-dispatch conversion then combines each actual returned branch with
the pre-existing tail and invokes that producer at the strict predecessor
search index.  No premise contains a complete-search result or an already
constructed successor-state certificate.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- A caller-selected relation for one atom.  Its first index is the number of
DFS state visits available to the atom; its second is the logical index that
must remain on a completed answer. -/
abbrev TwoIndexMatchingAtomRelation :=
  Nat → Nat → List Ty → List Ty → MatchingAtom → List Ty → Prop

namespace TwoIndexMatchingAtomRelation

/-- One available DFS visit may be forgotten without changing the retained
logical index. -/
def DownwardClosed (atomRelation : TwoIndexMatchingAtomRelation) : Prop :=
  ∀ {searchFuel residual environmentTypes bindingTypes atom newBindings},
    atomRelation (searchFuel + 2) residual environmentTypes bindingTypes atom
      newBindings →
    atomRelation (searchFuel + 1) residual environmentTypes bindingTypes atom
      newBindings

end TwoIndexMatchingAtomRelation

/-- Pending branch work generated structurally from a caller-selected atom
relation.  At index zero nonempty work is not inspected.  At a positive index
the head consumes the current visit and the tail is checked at the strict
predecessor. -/
inductive RelationalTwoIndexMatchingBranchTyping
    (atomRelation : TwoIndexMatchingAtomRelation) :
    Nat → Nat → List Ty → List Ty → List MatchingAtom → List Ty → Prop where
  | zero
      (nonempty : atoms ≠ []) :
      RelationalTwoIndexMatchingBranchTyping atomRelation 0 residual
        environmentTypes bindingTypes atoms newBindings
  | nil :
      RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel residual
        environmentTypes bindingTypes [] []
  | cons
      (head : atomRelation (searchFuel + 1) residual environmentTypes
        bindingTypes atom headBindings)
      (tail : RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel
        residual environmentTypes (bindingTypes ++ headBindings) atoms
        tailBindings) :
      RelationalTwoIndexMatchingBranchTyping atomRelation (searchFuel + 1)
        residual environmentTypes bindingTypes (atom :: atoms)
        (headBindings ++ tailBindings)

namespace RelationalTwoIndexMatchingBranchTyping

/-- Branch work is downward closed whenever the selected atom relation is. -/
theorem previous
    (downward : TwoIndexMatchingAtomRelation.DownwardClosed atomRelation)
    (typing : RelationalTwoIndexMatchingBranchTyping atomRelation
      (searchFuel + 1) residual environmentTypes bindingTypes atoms
      newBindings) :
    RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel residual
      environmentTypes bindingTypes atoms newBindings := by
  induction searchFuel generalizing bindingTypes atoms newBindings with
  | zero =>
      cases typing with
      | nil => exact .nil
      | cons head tail => exact .zero (by simp)
  | succ searchFuel induction =>
      cases typing with
      | nil => exact .nil
      | cons head tail => exact .cons (downward head) (induction tail)

/-- Concatenate returned branch work before an existing tail at one search
index.  The right side is weakened once for every atom consumed on the left. -/
theorem append
    (downward : TwoIndexMatchingAtomRelation.DownwardClosed atomRelation) :
    ∀ searchFuel {bindingTypes leftAtoms leftBindings},
      RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel residual
        environmentTypes bindingTypes leftAtoms leftBindings →
      ∀ {rightAtoms rightBindings},
        RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel residual
          environmentTypes (bindingTypes ++ leftBindings) rightAtoms
          rightBindings →
        RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel residual
          environmentTypes bindingTypes (leftAtoms ++ rightAtoms)
          (leftBindings ++ rightBindings) := by
  intro searchFuel
  induction searchFuel with
  | zero =>
      intro bindingTypes leftAtoms leftBindings left rightAtoms rightBindings
        right
      cases left with
      | zero nonempty => exact .zero (by simp [nonempty])
      | nil => simpa using right
  | succ searchFuel induction =>
      intro bindingTypes leftAtoms leftBindings left rightAtoms rightBindings
        right
      cases left with
      | nil => simpa using right
      | cons head tail =>
          rename_i atom headBindings atoms tailBindings
          have right' : RelationalTwoIndexMatchingBranchTyping atomRelation
              searchFuel residual environmentTypes
              ((bindingTypes ++ headBindings) ++ tailBindings) rightAtoms
              rightBindings := by
            simpa [List.append_assoc] using right.previous downward
          have combined := induction tail right'
          simpa [List.append_assoc] using
            (RelationalTwoIndexMatchingBranchTyping.cons head combined)

end RelationalTwoIndexMatchingBranchTyping

/-- General callable shape for a caller-selected two-index branch relation. -/
abbrev TwoIndexMatchingBranchRelation :=
  Nat → Nat → List Ty → List Ty → MatchingBranch → List Ty → Prop

namespace TwoIndexMatchingBranchRelation

/-- Forget one branch search visit while retaining the logical index. -/
def SearchDownwardClosed
    (branchRelation : TwoIndexMatchingBranchRelation) : Prop :=
  ∀ {searchFuel residual environmentTypes bindingTypes branch newBindings},
    branchRelation (searchFuel + 1) residual environmentTypes bindingTypes
      branch newBindings →
    branchRelation searchFuel residual environmentTypes bindingTypes branch
      newBindings

end TwoIndexMatchingBranchRelation

/-- The structural branch relation generated by a selected atom relation. -/
def relationalTwoIndexMatchingBranchRelation
    (atomRelation : TwoIndexMatchingAtomRelation) :
    TwoIndexMatchingBranchRelation :=
  fun searchFuel residual environmentTypes bindingTypes branch newBindings =>
    RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel residual
      environmentTypes bindingTypes branch newBindings

theorem relationalTwoIndexMatchingBranchRelation_downwardClosed
    (downward : TwoIndexMatchingAtomRelation.DownwardClosed atomRelation) :
    TwoIndexMatchingBranchRelation.SearchDownwardClosed
      (relationalTwoIndexMatchingBranchRelation atomRelation) := by
  intro searchFuel residual environmentTypes bindingTypes branch newBindings
    typed
  exact typed.previous downward

/-- Preservation data for one successful local reduction.  Immediate
bindings are safe at the successor state's logical index, and every actual
reduction branch carries structural work at the predecessor search index. -/
inductive TwoIndexRelationalAtomReductionTyping
    (atomRelation : TwoIndexMatchingAtomRelation)
    (bindingsInvariant : IndexedMatchingInvariant)
    (searchFuel residual : Nat)
    (environmentTypes bindingTypes expectedBindings : List Ty)
    (reduction : AtomReduction) : Prop where
  | intro
      (immediateTypes : List Ty)
      (immediateTyped : bindingsInvariant (searchFuel + residual)
        reduction.bindings immediateTypes)
      (branchesTyped : ∀ branch ∈ reduction.branches,
        ∃ delayedTypes,
          RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel
            residual environmentTypes (bindingTypes ++ immediateTypes) branch
            delayedTypes ∧
          immediateTypes ++ delayedTypes = expectedBindings) :
      TwoIndexRelationalAtomReductionTyping atomRelation bindingsInvariant
        searchFuel residual environmentTypes bindingTypes expectedBindings
        reduction

/-- Local timeout-or-hit preservation for the selected atom relation.  The
law consumes current environment and bindings at `searchFuel + 1 + residual`
and returns only immediate branch work at `searchFuel`. -/
def TwoIndexRelationalAtomReducerTypedSafe
    (environmentInvariant bindingsInvariant : IndexedMatchingInvariant)
    (atomRelation : TwoIndexMatchingAtomRelation)
    (reduceAtom : AtomReducer) : Prop :=
  ∀ {searchFuel residual environmentTypes bindingTypes environment bindings
      atom newBindings},
    environmentInvariant (searchFuel + 1 + residual) environment
      environmentTypes →
    bindingsInvariant (searchFuel + 1 + residual) bindings bindingTypes →
    atomRelation (searchFuel + 1) residual environmentTypes bindingTypes atom
      newBindings →
    reduceAtom (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) ∧
        TwoIndexRelationalAtomReductionTyping atomRelation bindingsInvariant
          searchFuel residual environmentTypes bindingTypes newBindings
          reduction

namespace RelationalTwoIndexMatchingBranchTyping

/-- Structural branch work produces the state certificate consumed by the
generic two-index DFS theorem.  This is the only recursive producer: every
recursive call is made at the strict predecessor search index. -/
theorem toTwoIndexState
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (bindingsAppend :
      IndexedMatchingInvariant.AppendClosed bindingsInvariant)
    (atomDownward :
      TwoIndexMatchingAtomRelation.DownwardClosed atomRelation)
    (reducerSafe : TwoIndexRelationalAtomReducerTypedSafe
      environmentInvariant bindingsInvariant atomRelation reduceAtom)
    (environmentTyped : environmentInvariant (searchFuel + residual)
      environment environmentTypes)
    (bindingsTyped : bindingsInvariant (searchFuel + residual) bindings
      bindingTypes)
    (workTyped : RelationalTwoIndexMatchingBranchTyping atomRelation searchFuel
      residual environmentTypes bindingTypes work futureBindings) :
    TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
      reduceAtom searchFuel residual ⟨work, environment, bindings⟩
      (bindingTypes ++ futureBindings) := by
  induction searchFuel generalizing environment bindings bindingTypes work
      futureBindings with
  | zero => exact .zero
  | succ searchFuel induction =>
      cases workTyped with
      | nil =>
          simpa using
            (TwoIndexMatchingStateTyping.yield environmentTyped bindingsTyped)
      | cons headTyped tailTyped =>
          rename_i atom headBindings atoms tailBindings
          apply TwoIndexMatchingStateTyping.reduce environmentTyped
            bindingsTyped
          rcases reducerSafe environmentTyped bindingsTyped headTyped with
            timeout | ⟨reduction, reduced, reductionTyped⟩
          · exact .timeout timeout
          · cases reductionTyped with
            | intro immediateTypes immediateTyped branchesTyped =>
                apply TwoIndexAtomReducerCertificate.hit reduction reduced
                intro successor successorMember
                simp only [MatchingState.successors] at successorMember
                rcases List.mem_map.mp successorMember with
                  ⟨branch, branchMember, rfl⟩
                obtain ⟨delayedTypes, branchTyped, bindingEq⟩ :=
                  branchesTyped branch branchMember
                have branchAndTail :=
                  RelationalTwoIndexMatchingBranchTyping.append atomDownward
                    searchFuel branchTyped (by
                      simpa [List.append_assoc, bindingEq] using tailTyped)
                have environmentAtSuccessor : environmentInvariant
                    (searchFuel + residual) environment environmentTypes :=
                  IndexedMatchingInvariant.DownwardClosed.mono
                    environmentDownward environmentTyped (by omega)
                have bindingsAtSuccessor : bindingsInvariant
                    (searchFuel + residual) bindings bindingTypes :=
                  IndexedMatchingInvariant.DownwardClosed.mono
                    bindingsDownward bindingsTyped (by omega)
                have newBindingsTyped :=
                  bindingsAppend bindingsAtSuccessor immediateTyped
                have successorTyped := induction environmentAtSuccessor
                  newBindingsTyped branchAndTail
                have answerEq :
                    (bindingTypes ++ immediateTypes) ++
                        (delayedTypes ++ tailBindings) =
                      bindingTypes ++ (headBindings ++ tailBindings) := by
                  simp only [List.append_assoc]
                  rw [← List.append_assoc immediateTypes delayedTypes,
                    bindingEq]
                rw [answerEq] at successorTyped
                exact successorTyped

end RelationalTwoIndexMatchingBranchTyping

/-- Exact timeout-or-hit classification of one actual matcher dispatch.  A
hit retains both the common source-pattern list and relation evidence for
each member of the concrete returned branch list. -/
inductive TwoIndexPatternDispatchCertificate
    (branchRelation : TwoIndexMatchingBranchRelation)
    (searchFuel residual : Nat)
    (environmentTypes bindingTypes newBindings : List Ty) :
    FuelResult (DispatchResult MatchingBranches) → Prop where
  | timeout :
      TwoIndexPatternDispatchCertificate branchRelation searchFuel residual
        environmentTypes bindingTypes newBindings .timeout
  | hit
      (patternsPreserved : ∀ branch ∈ branches,
        branch.map (fun atom => atom.pattern) = patterns)
      (branchesRelated : ∀ branch ∈ branches,
        branchRelation searchFuel residual environmentTypes bindingTypes
          branch newBindings) :
      TwoIndexPatternDispatchCertificate branchRelation searchFuel residual
        environmentTypes bindingTypes newBindings (.ok (.hit branches))

namespace TwoIndexPatternDispatchCertificate

/-- Project both retained source-pattern equality and caller relation evidence
for one member of the actual successful branch list. -/
theorem member
    (typing : TwoIndexPatternDispatchCertificate branchRelation searchFuel
      residual environmentTypes bindingTypes newBindings
      (.ok (.hit branches)))
    (branchMember : branch ∈ branches) :
    ∃ patterns,
      branch.map (fun atom => atom.pattern) = patterns ∧
      branchRelation searchFuel residual environmentTypes bindingTypes branch
        newBindings := by
  cases typing with
  | hit patternsPreserved branchesRelated =>
      exact ⟨_, patternsPreserved branch branchMember,
        branchesRelated branch branchMember⟩

/-- Dispatch certificates forget one branch-search visit exactly when the
selected branch relation does; the retained logical index is unchanged. -/
theorem previous
    (downward :
      TwoIndexMatchingBranchRelation.SearchDownwardClosed branchRelation)
    (typing : TwoIndexPatternDispatchCertificate branchRelation
      (searchFuel + 1) residual environmentTypes bindingTypes newBindings
      result) :
    TwoIndexPatternDispatchCertificate branchRelation searchFuel residual
      environmentTypes bindingTypes newBindings result := by
  cases typing with
  | timeout => exact .timeout
  | hit patternsPreserved branchesRelated =>
      exact .hit patternsPreserved (by
        intro branch branchMember
        exact downward (branchesRelated branch branchMember))

/-- Convert one exact user dispatch into a local two-index reducer
certificate.  Successors are produced from branch work plus the independently
typed remaining work; no successor-state certificate is a premise. -/
theorem toTwoIndexUserMatcherAtomCertificate
    (dispatchTyped : TwoIndexPatternDispatchCertificate
      (relationalTwoIndexMatchingBranchRelation atomRelation) searchFuel
      residual environmentTypes bindingTypes newBindings
      (dispatchMatcherClauses eval (bindings ++ environment)
        matcherEnvironment remainingClauses pattern target))
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (bindingsAppend :
      IndexedMatchingInvariant.AppendClosed bindingsInvariant)
    (atomDownward :
      TwoIndexMatchingAtomRelation.DownwardClosed atomRelation)
    (reducerSafe : TwoIndexRelationalAtomReducerTypedSafe
      environmentInvariant bindingsInvariant atomRelation
      (evaluationAtomReducer eval))
    (environmentTyped : environmentInvariant (searchFuel + 1 + residual)
      environment environmentTypes)
    (bindingsTyped : bindingsInvariant (searchFuel + 1 + residual) bindings
      bindingTypes)
    (builtinMiss :
      reduceBuiltinAtom eval (bindings ++ environment)
        ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
          target⟩ = .ok .miss)
    (remainingTyped : RelationalTwoIndexMatchingBranchTyping atomRelation
      searchFuel residual environmentTypes (bindingTypes ++ newBindings)
      remaining tailBindings) :
    TwoIndexAtomReducerCertificate environmentInvariant bindingsInvariant
      (evaluationAtomReducer eval) searchFuel residual environment bindings
      ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
        target⟩ remaining
      (bindingTypes ++ (newBindings ++ tailBindings)) := by
  generalize dispatchEq :
      dispatchMatcherClauses eval (bindings ++ environment)
        matcherEnvironment remainingClauses pattern target = dispatchResult
    at dispatchTyped
  cases dispatchTyped with
  | timeout =>
      exact .timeout (by
        unfold evaluationAtomReducer combineAtomReducers
        rw [builtinMiss]
        simp only [FuelResult.bind]
        simpa [reduceMatcherAtom] using
          congrArg (FuelResult.map clauseResultToAtomReduction) dispatchEq)
  | hit patternsPreserved branchesRelated =>
      rename_i branches patterns
      let reduction : AtomReduction := ⟨branches, []⟩
      apply TwoIndexAtomReducerCertificate.hit reduction
      · unfold evaluationAtomReducer combineAtomReducers
        rw [builtinMiss]
        simp only [FuelResult.bind]
        simpa [reduceMatcherAtom, reduction, clauseResultToAtomReduction] using
          congrArg (FuelResult.map clauseResultToAtomReduction) dispatchEq
      · intro successor successorMember
        simp only [MatchingState.successors] at successorMember
        rcases List.mem_map.mp successorMember with
          ⟨branch, branchMember, rfl⟩
        have branchTyped := branchesRelated branch branchMember
        have branchAndRemaining :=
          RelationalTwoIndexMatchingBranchTyping.append atomDownward searchFuel
            branchTyped remainingTyped
        have environmentAtSuccessor : environmentInvariant
            (searchFuel + residual) environment environmentTypes :=
          IndexedMatchingInvariant.DownwardClosed.mono environmentDownward
            environmentTyped (by omega)
        have bindingsAtSuccessor : bindingsInvariant
            (searchFuel + residual) bindings bindingTypes :=
          IndexedMatchingInvariant.DownwardClosed.mono bindingsDownward
            bindingsTyped (by omega)
        have successorTyped := branchAndRemaining.toTwoIndexState
          environmentDownward bindingsDownward bindingsAppend atomDownward
          reducerSafe environmentAtSuccessor bindingsAtSuccessor
        simpa [MatchingState.continueWith, reduction] using successorTyped

/-- Package the same local preservation as the current user-matcher state. -/
theorem toTwoIndexUserMatcherStateTyping
    (dispatchTyped : TwoIndexPatternDispatchCertificate
      (relationalTwoIndexMatchingBranchRelation atomRelation) searchFuel
      residual environmentTypes bindingTypes newBindings
      (dispatchMatcherClauses eval (bindings ++ environment)
        matcherEnvironment remainingClauses pattern target))
    (environmentDownward :
      IndexedMatchingInvariant.DownwardClosed environmentInvariant)
    (bindingsDownward :
      IndexedMatchingInvariant.DownwardClosed bindingsInvariant)
    (bindingsAppend :
      IndexedMatchingInvariant.AppendClosed bindingsInvariant)
    (atomDownward :
      TwoIndexMatchingAtomRelation.DownwardClosed atomRelation)
    (reducerSafe : TwoIndexRelationalAtomReducerTypedSafe
      environmentInvariant bindingsInvariant atomRelation
      (evaluationAtomReducer eval))
    (environmentTyped : environmentInvariant (searchFuel + 1 + residual)
      environment environmentTypes)
    (bindingsTyped : bindingsInvariant (searchFuel + 1 + residual) bindings
      bindingTypes)
    (builtinMiss :
      reduceBuiltinAtom eval (bindings ++ environment)
        ⟨pattern, .matcherV matcherEnvironment original remainingClauses,
          target⟩ = .ok .miss)
    (remainingTyped : RelationalTwoIndexMatchingBranchTyping atomRelation
      searchFuel residual environmentTypes (bindingTypes ++ newBindings)
      remaining tailBindings) :
    TwoIndexMatchingStateTyping environmentInvariant bindingsInvariant
      (evaluationAtomReducer eval) (searchFuel + 1) residual
      ⟨⟨pattern, .matcherV matcherEnvironment original remainingClauses,
        target⟩ :: remaining, environment, bindings⟩
      (bindingTypes ++ (newBindings ++ tailBindings)) := by
  exact .reduce environmentTyped bindingsTyped
    (dispatchTyped.toTwoIndexUserMatcherAtomCertificate environmentDownward
      bindingsDownward bindingsAppend atomDownward reducerSafe
      environmentTyped bindingsTyped builtinMiss remainingTyped)

end TwoIndexPatternDispatchCertificate

end TypePM.Runtime
