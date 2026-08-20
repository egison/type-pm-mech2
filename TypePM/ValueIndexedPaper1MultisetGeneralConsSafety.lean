import TypePM.ValueIndexedPaper1MultisetHeadConsSafety
import TypePM.Source.M4Paper1MultisetSearchSafety

/-!
# Direct all-fuel safety for the Paper 1 multiset general-cons clause

This module follows the actual fourth clause of the seven-clause Paper 1
matcher.  Its header is `$ :: $`; the selected body uses the source-defined
recursive `list` matcher to enumerate one chosen element and the remaining
multiset.  The proofs classify every callback bound through the first success
at 26 directly, then prove arbitrary-search-fuel safety at each of those
callback bounds.  No successful search run or fuel monotonicity is used.
-/

namespace TypePM.ValueIndexedPaper1MultisetGeneralConsSafety

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open Source.MatcherTyping.M4Paper1MultisetSearchSafety
open ValueIndexedPaper1MultisetHeadConsSafety

theorem nilClause_generalCons_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      multisetConsPattern multisetConsTarget nilClause = .ok .miss := by
  rfl

theorem headOnlyClause_generalCons_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      multisetConsPattern multisetConsTarget headOnlyClause = .ok .miss := by
  rfl

theorem valueConsClause_generalCons_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      multisetConsPattern multisetConsTarget valueConsClause = .ok .miss := by
  rfl

set_option maxRecDepth 100000 in
theorem generalConsClause_try_directThrough26 :
    ∀ fuel, fuel ≤ 26 → ∀ atomEnvironment,
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetConsPattern
        multisetConsTarget generalConsClause = .timeout ∨
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetConsPattern
        multisetConsTarget generalConsClause =
          .ok (.hit multisetConsBranches)
  | 0, _, _ => .inl (by with_unfolding_all rfl)
  | 1, _, _ => .inl (by with_unfolding_all rfl)
  | 2, _, _ => .inl (by with_unfolding_all rfl)
  | 3, _, _ => .inl (by with_unfolding_all rfl)
  | 4, _, _ => .inl (by with_unfolding_all rfl)
  | 5, _, _ => .inl (by with_unfolding_all rfl)
  | 6, _, _ => .inl (by with_unfolding_all rfl)
  | 7, _, _ => .inl (by with_unfolding_all rfl)
  | 8, _, _ => .inl (by with_unfolding_all rfl)
  | 9, _, _ => .inl (by with_unfolding_all rfl)
  | 10, _, _ => .inl (by with_unfolding_all rfl)
  | 11, _, _ => .inl (by with_unfolding_all rfl)
  | 12, _, _ => .inl (by with_unfolding_all rfl)
  | 13, _, _ => .inl (by with_unfolding_all rfl)
  | 14, _, _ => .inl (by with_unfolding_all rfl)
  | 15, _, _ => .inl (by with_unfolding_all rfl)
  | 16, _, _ => .inl (by with_unfolding_all rfl)
  | 17, _, _ => .inl (by with_unfolding_all rfl)
  | 18, _, _ => .inl (by with_unfolding_all rfl)
  | 19, _, _ => .inl (by with_unfolding_all rfl)
  | 20, _, _ => .inl (by with_unfolding_all rfl)
  | 21, _, _ => .inl (by with_unfolding_all rfl)
  | 22, _, _ => .inl (by with_unfolding_all rfl)
  | 23, _, _ => .inl (by with_unfolding_all rfl)
  | 24, _, _ => .inl (by with_unfolding_all rfl)
  | 25, _, _ => .inl (by with_unfolding_all rfl)
  | 26, _, _ => .inr (by with_unfolding_all rfl)
  | _ + 27, bound, _ => by omega

set_option maxRecDepth 100000 in
/-- Every callback bound below 26 times out while evaluating the selected
general-cons clause.  Together with `generalCons_dispatch_exact26`, this
formally identifies 26 as the first successful dispatch bound. -/
theorem generalConsClause_timeout_before26 :
    ∀ fuel, fuel < 26 → ∀ atomEnvironment,
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetConsPattern
        multisetConsTarget generalConsClause = .timeout
  | 0, _, _ => by with_unfolding_all rfl
  | 1, _, _ => by with_unfolding_all rfl
  | 2, _, _ => by with_unfolding_all rfl
  | 3, _, _ => by with_unfolding_all rfl
  | 4, _, _ => by with_unfolding_all rfl
  | 5, _, _ => by with_unfolding_all rfl
  | 6, _, _ => by with_unfolding_all rfl
  | 7, _, _ => by with_unfolding_all rfl
  | 8, _, _ => by with_unfolding_all rfl
  | 9, _, _ => by with_unfolding_all rfl
  | 10, _, _ => by with_unfolding_all rfl
  | 11, _, _ => by with_unfolding_all rfl
  | 12, _, _ => by with_unfolding_all rfl
  | 13, _, _ => by with_unfolding_all rfl
  | 14, _, _ => by with_unfolding_all rfl
  | 15, _, _ => by with_unfolding_all rfl
  | 16, _, _ => by with_unfolding_all rfl
  | 17, _, _ => by with_unfolding_all rfl
  | 18, _, _ => by with_unfolding_all rfl
  | 19, _, _ => by with_unfolding_all rfl
  | 20, _, _ => by with_unfolding_all rfl
  | 21, _, _ => by with_unfolding_all rfl
  | 22, _, _ => by with_unfolding_all rfl
  | 23, _, _ => by with_unfolding_all rfl
  | 24, _, _ => by with_unfolding_all rfl
  | 25, _, _ => by with_unfolding_all rfl
  | _ + 26, bound, _ => by omega

set_option maxRecDepth 100000 in
theorem generalCons_dispatch_exact26 (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel 26) atomEnvironment
      closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
      multisetConsTarget = .ok (.hit multisetConsBranches) := by
  with_unfolding_all rfl

/-- The actual seven-clause dispatcher also times out at every callback bound
below 26: the first three headers miss and the selected fourth clause times
out before any later clause can be visited. -/
theorem generalCons_dispatch_timeout_before26
    (bound : callbackFuel < 26) (atomEnvironment : ValueEnvironment) :
    dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
      closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
      multisetConsTarget = .timeout := by
  have timeout := generalConsClause_timeout_before26 callbackFuel bound
    atomEnvironment
  simp [multisetClauses, dispatchMatcherClauses, firstHit,
    nilClause_generalCons_miss, headOnlyClause_generalCons_miss,
    valueConsClause_generalCons_miss, timeout]

/-- Direct evaluation through the formally identified first successful
callback bound: `generalCons_dispatch_timeout_before26` exposes the strict
timeout result below 26, and bound 26 returns the three source-ordered
branches.  This statement uses neither an eventual-success theorem nor fuel
monotonicity. -/
theorem generalCons_dispatch_directThrough26 :
    ∀ fuel, fuel ≤ 26 → ∀ atomEnvironment,
      dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
        multisetConsTarget = .timeout ∨
      dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
        multisetConsTarget = .ok (.hit multisetConsBranches) := by
  intro fuel bound atomEnvironment
  rcases generalConsClause_try_directThrough26 fuel bound atomEnvironment with
    timeout | success
  · exact .inl (by
      simp [multisetClauses, dispatchMatcherClauses, firstHit,
        nilClause_generalCons_miss, headOnlyClause_generalCons_miss,
        valueConsClause_generalCons_miss, timeout])
  · exact .inr (by
      simp [multisetClauses, dispatchMatcherClauses, firstHit,
        nilClause_generalCons_miss, headOnlyClause_generalCons_miss,
        valueConsClause_generalCons_miss, success])

def variableBranches (target : Value) : MatchingBranches :=
  [[⟨.var, .something, target⟩]]

theorem nilClause_variable_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment)
    (target : Value) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      .var target nilClause = .ok .miss := by
  rfl

theorem headOnlyClause_variable_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment)
    (target : Value) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      .var target headOnlyClause = .ok .miss := by
  rfl

theorem valueConsClause_variable_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment)
    (target : Value) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      .var target valueConsClause = .ok .miss := by
  rfl

theorem generalConsClause_variable_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment)
    (target : Value) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      .var target generalConsClause = .ok .miss := by
  rfl

theorem joinClause_variable_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment)
    (target : Value) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      .var target joinClause = .ok .miss := by
  rfl

theorem wholeValueClause_variable_miss
    (fuel : Nat) (atomEnvironment matcherEnvironment : ValueEnvironment)
    (target : Value) :
    tryMatcherClause (evalFuel fuel) atomEnvironment matcherEnvironment
      .var target wholeValueClause = .ok .miss := by
  rfl

theorem catchAllClause_variable_try :
    ∀ fuel atomEnvironment target,
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment .var target catchAllClause = .timeout ∨
      tryMatcherClause (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment .var target catchAllClause =
          .ok (.hit (variableBranches target))
  | 0, _, _ => .inl rfl
  | 1, _, _ => .inl (by with_unfolding_all rfl)
  | 2, _, _ => .inr (by
      simp [tryMatcherClause, catchAllClause, variableBranches,
        closedMultisetMatcherEnvironment, evalFuel, firstHit, tryMatcherArm,
        buildMatchingBranches, decodeDecompositions,
        inspectPatternPattern,
        matchValueDataPattern, FuelResult.traverse, decodeProduct,
        zipMatchingAtoms, closeMatcherArmsResult, sourceList,
        Value.viewList])
  | _ + 3, _, _ => .inr (by
      simp [tryMatcherClause, catchAllClause, variableBranches,
        closedMultisetMatcherEnvironment, evalFuel, firstHit, tryMatcherArm,
        buildMatchingBranches, decodeDecompositions,
        inspectPatternPattern,
        matchValueDataPattern, FuelResult.traverse, decodeProduct,
        zipMatchingAtoms, closeMatcherArmsResult, sourceList,
        Value.viewList])

/-- A variable delegated back to the recursive multiset cursor reaches the
seventh catch-all clause.  This is classified directly for every callback
fuel; no recursive list computation is involved on this path. -/
theorem variable_dispatch_allFuel :
    ∀ fuel atomEnvironment target,
      dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses .var target = .timeout ∨
      dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses .var target =
          .ok (.hit (variableBranches target)) := by
  intro fuel atomEnvironment target
  rcases catchAllClause_variable_try fuel atomEnvironment target with
    timeout | success
  · exact .inl (by
      simp [multisetClauses, dispatchMatcherClauses, firstHit,
        nilClause_variable_miss, headOnlyClause_variable_miss,
        valueConsClause_variable_miss, generalConsClause_variable_miss,
        joinClause_variable_miss, wholeValueClause_variable_miss, timeout])
  · exact .inr (by
      simp [multisetClauses, dispatchMatcherClauses, firstHit,
        nilClause_variable_miss, headOnlyClause_variable_miss,
        valueConsClause_variable_miss, generalConsClause_variable_miss,
        joinClause_variable_miss, wholeValueClause_variable_miss, success])

theorem variable_recursiveAtomTyping
    (targetTyped : ValueTyping target targetType) :
    RecursiveTotalMatchingAtomTyping expressionTyping (evalFuel callbackFuel)
      environmentTypes bindingTypes
      ⟨.var, closedMultisetMatcherValue, target⟩ [targetType] := by
  apply RecursiveTotalMatchingAtomTyping.patternIndexedUser
  · intro atomEnvironment
    simp [reduceBuiltinAtom]
  · intro atomEnvironment _
    rcases variable_dispatch_allFuel callbackFuel atomEnvironment target with
      timeout | success
    · rw [timeout]
      exact .timeout
    · rw [success]
      exact .hit (patterns := [.var]) (by
        intro branch member
        simp only [variableBranches, List.mem_singleton] at member
        subst branch
        rfl) (by
        intro branch member
        simp only [variableBranches, List.mem_singleton] at member
        subst branch
        exact .cons (.builtin (.somethingVar targetTyped)) .nil)

private theorem intList_itemsValueTyping : ∀ literals : List Int,
    ListValueTypings (literals.map Value.int) .int
  | [] => .nil
  | literal :: literals =>
      .cons (.int literal) (intList_itemsValueTyping literals)

private theorem intList_valueTyping (literals : List Int) :
    ValueTyping (Value.buildList (literals.map Value.int))
      (DataTypes.list .int) :=
  .list (intList_itemsValueTyping literals)

theorem multisetConsBranch_recursiveTyping
    (branch : MatchingBranch) (member : branch ∈ multisetConsBranches) :
    RecursiveTotalMatchingAtomsTyping expressionTyping (evalFuel callbackFuel)
      environmentTypes bindingTypes branch [.int, DataTypes.list .int] := by
  simp only [multisetConsBranches, List.mem_cons] at member
  rcases member with rfl | member
  · exact .cons (.builtin (.somethingVar (.int 1)))
      (.cons (variable_recursiveAtomTyping
        (by simpa using intList_valueTyping [2, 3])) .nil)
  · rcases member with rfl | member
    · exact .cons (.builtin (.somethingVar (.int 2)))
        (.cons (variable_recursiveAtomTyping
          (by simpa using intList_valueTyping [1, 3])) .nil)
    · rcases member with rfl | member
      · exact .cons (.builtin (.somethingVar (.int 3)))
          (.cons (variable_recursiveAtomTyping
            (by simpa using intList_valueTyping [1, 2])) .nil)
      · simp at member

/-- At the first successful callback bound, the actual fourth-clause hit is
accepted by the recursive reducer.  The first atom binds the chosen integer;
the second atom delegates the preserved variable pattern back to the exact
recursive multiset cursor, whose catch-all path was classified at every
callback fuel above. -/
theorem generalCons_patternIndexedRecursiveDispatchTyping26
    (atomEnvironment : ValueEnvironment) :
    PatternIndexedRecursiveDispatchTyping expressionTyping (evalFuel 26)
      environmentTypes bindingTypes [.int, DataTypes.list .int]
      (dispatchMatcherClauses (evalFuel 26) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
        multisetConsTarget) := by
  rw [generalCons_dispatch_exact26]
  exact .hit (patterns := [.var, .var])
    multisetCons_dispatch_preserves_source_patterns
    (multisetConsBranch_recursiveTyping (callbackFuel := 26))

/-- Direct recursive dispatch typing at every callback bound up to and
including the first success.  Bounds below 26 are timeout cases; bound 26
uses the exact three branches in source order. -/
theorem generalCons_patternIndexedRecursiveDispatchTyping_directThrough26
    (bound : callbackFuel ≤ 26) (atomEnvironment : ValueEnvironment) :
    PatternIndexedRecursiveDispatchTyping expressionTyping
      (evalFuel callbackFuel) environmentTypes bindingTypes
      [.int, DataTypes.list .int]
      (dispatchMatcherClauses (evalFuel callbackFuel) atomEnvironment
        closedMultisetMatcherEnvironment multisetClauses multisetConsPattern
        multisetConsTarget) := by
  rcases generalCons_dispatch_directThrough26 callbackFuel bound
      atomEnvironment with timeout | success
  · rw [timeout]
    exact .timeout
  · rw [success]
    exact .hit (patterns := [.var, .var])
      multisetCons_dispatch_preserves_source_patterns
      (multisetConsBranch_recursiveTyping (callbackFuel := callbackFuel))

theorem generalCons_recursiveAtomTyping26 :
    RecursiveTotalMatchingAtomTyping expressionTyping (evalFuel 26)
      environmentTypes bindingTypes
      ⟨multisetConsPattern, closedMultisetMatcherValue,
        multisetConsTarget⟩ [.int, DataTypes.list .int] := by
  apply RecursiveTotalMatchingAtomTyping.patternIndexedUser
  · intro atomEnvironment
    simp [multisetConsPattern, reduceBuiltinAtom]
  · intro atomEnvironment _
    exact generalCons_patternIndexedRecursiveDispatchTyping26 atomEnvironment

theorem generalCons_recursiveAtomTyping_directThrough26
    (bound : callbackFuel ≤ 26) :
    RecursiveTotalMatchingAtomTyping expressionTyping (evalFuel callbackFuel)
      environmentTypes bindingTypes
      ⟨multisetConsPattern, closedMultisetMatcherValue,
        multisetConsTarget⟩ [.int, DataTypes.list .int] := by
  apply RecursiveTotalMatchingAtomTyping.patternIndexedUser
  · intro atomEnvironment
    simp [multisetConsPattern, reduceBuiltinAtom]
  · intro atomEnvironment _
    exact generalCons_patternIndexedRecursiveDispatchTyping_directThrough26
      bound atomEnvironment

abbrev CoreExpressionTyping : EmbeddedExpressionTyping :=
  fun context expression target => TotalCoreTyping expression target context

/-- Direct arbitrary-DFS-fuel safety for the real P1-L05 constructor pattern.
The expression callback is fixed at the first directly computed successful
bound 26; the search fuel is wholly arbitrary and no successful search run or
fuel-monotonicity theorem is used. -/
theorem multisetCons_search_recursiveTypedSafe26 (searchFuel : Nat) :
    TypedMatchingSearchResult [.int, DataTypes.list .int]
      (searchPatternFuel (evalFuel 26) searchFuel [] multisetConsPattern
        closedMultisetMatcherValue multisetConsTarget) := by
  exact searchPatternFuel_recursiveTotalTypedSafe
    (expressionTyping := CoreExpressionTyping) (eval := evalFuel 26)
    (evalFuel_totalCore_embeddedSafe 26) .nil
    (generalCons_recursiveAtomTyping26
      (expressionTyping := CoreExpressionTyping)
      (environmentTypes := []) (bindingTypes := [])) searchFuel

theorem multisetCons_search_recursiveTypedSafe_directThrough26
    (bound : callbackFuel ≤ 26) (searchFuel : Nat) :
    TypedMatchingSearchResult [.int, DataTypes.list .int]
      (searchPatternFuel (evalFuel callbackFuel) searchFuel []
        multisetConsPattern closedMultisetMatcherValue multisetConsTarget) := by
  exact searchPatternFuel_recursiveTotalTypedSafe
    (expressionTyping := CoreExpressionTyping) (eval := evalFuel callbackFuel)
    (evalFuel_totalCore_embeddedSafe callbackFuel) .nil
    (generalCons_recursiveAtomTyping_directThrough26
      (expressionTyping := CoreExpressionTyping)
      (environmentTypes := []) (bindingTypes := []) bound) searchFuel

theorem multisetCons_search_recursiveNeverStuck_directThrough26
    (bound : callbackFuel ≤ 26) (searchFuel : Nat) :
    (searchPatternFuel (evalFuel callbackFuel) searchFuel []
      multisetConsPattern closedMultisetMatcherValue
      multisetConsTarget).NotStuck := by
  rcases multisetCons_search_recursiveTypedSafe_directThrough26 bound searchFuel
    with timeout | ⟨answers, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

theorem multisetCons_search_recursiveNeverStuck26 (searchFuel : Nat) :
    (searchPatternFuel (evalFuel 26) searchFuel [] multisetConsPattern
      closedMultisetMatcherValue multisetConsTarget).NotStuck := by
  rcases multisetCons_search_recursiveTypedSafe26 searchFuel with timeout |
    ⟨answers, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

/-!
## Exact remaining boundary

The callback theorem intentionally stops at 26, the first successful bound.
For callback bounds above 26 the fourth-clause body runs the recursive
source-defined `list` join matcher.  Extending the direct classification
requires an all-callback structural theorem for that inner join search.  The
existing list-join certificate starts from one fixed successful search and
uses fuel monotonicity, so importing it here would reintroduce precisely the
evidence this module is meant to eliminate.  In contrast, DFS search fuel is
already arbitrary in the theorems above.
-/

end TypePM.ValueIndexedPaper1MultisetGeneralConsSafety
