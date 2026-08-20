import TypePM.Runtime.PatternFunctionMatching
import TypePM.Source.Paper1Programs
import TypePM.Source.M4PatternFunctionPairRegression

/-!
# Scoped pattern-function runtime regressions

The main regression is the Paper-2 `pair` pattern under the exact source
`multiset` matcher.  Its body binds a private variable, compares that value
through a value pattern, and exports only its two argument patterns.  The four
ordered results are the search tree printed in Paper 2.
-/

namespace TypePM.Runtime.PatternFunctionMatchingRegression

open TypePM.Source
open TypePM.Source.Paper1Programs
open TypePM.Source.M4PatternFunctionPairRegression

/-- `$outer :: pair $inner _`.  The outer variable is bound before the MNode;
the inner variable is bound when the first embedded parameter is exported. -/
def pairPattern : Pattern :=
  .ctor PatternCtor.cons [.var, .app pairName [.var, .wild]]

def target : Value :=
  Value.buildList [.int 1, .int 2, .int 1, .int 3]

def expectedBindings : List (List Value) :=
  [[.int 2, .int 1], [.int 2, .int 1],
   [.int 3, .int 1], [.int 3, .int 1]]

/-- Evaluate the real seven-clause source multiset matcher, then run scoped
matching.  No matcher oracle or precomputed decomposition is used. -/
def pairSearch : FuelResult (List (List Value)) :=
  FuelResult.bind (evalFuel 50 [] multisetSomething) fun matcher =>
    searchPatternFunctionsFuel definitions (evalFuel 50) 200 []
      pairPattern matcher target

set_option maxRecDepth 100000 in
theorem pair_search_exact : pairSearch = .ok expectedBindings := by
  with_unfolding_all rfl

/-- The exact result contains two surrounding bindings per success; the
body-private variable is absent. -/
theorem pair_private_binding_does_not_escape :
    ∀ bindings ∈ expectedBindings, bindings.length = 2 := by
  intro bindings member
  simp [expectedBindings] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

/-- A pattern-function application is expanded before a catch-all matcher can
see it.  The first step is therefore an isolated node. -/
theorem application_has_priority_over_matcher_dispatch :
    stepPatternFunctionState definitions
      (evaluationAtomReducer (evalFuel 10))
      ⟨[.atom ⟨.app pairName [.var, .wild], .something, .int 1⟩], [], []⟩ =
      .ok (.expand
        [⟨[.node
            [.atom ⟨pairDefinition.body, .something, .int 1⟩]
            [] [] [.var, .wild]], [], []⟩]) := by
  rfl

/-- Exporting an embedded parameter keeps the MNode's private bindings inside
the continuation node and leaves the outer bindings unchanged. -/
theorem parameter_export_keeps_private_bindings :
    stepPatternFunctionState definitions
      (evaluationAtomReducer (evalFuel 10))
      ⟨[.node
          [.atom ⟨.embed 0, .something, .int 7⟩]
          [] [.int 99] [.var]], [], [.int 4]⟩ =
      .ok (.expand
        [⟨[.atom ⟨.var, .something, .int 7⟩,
            .node [] [] [.int 99] [.var]],
          [], [.int 4]⟩]) := by
  rfl

/-- Completing the node discards its private binding and resumes with the
unchanged outer binding. -/
theorem node_completion_discards_private_bindings :
    stepPatternFunctionState definitions
      (evaluationAtomReducer (evalFuel 10))
      ⟨[.node [] [] [.int 99] []], [], [.int 4]⟩ =
      .ok (.expand [⟨[], [], [.int 4]⟩]) := by
  rfl

theorem pair_search_has_structural_depth_first_derivation :
    ∃ matcher,
      evalFuel 50 [] multisetSomething = .ok matcher ∧
      DepthFirst
        (stepPatternFunctionState definitions
          (evaluationAtomReducer (evalFuel 50)))
        [⟨[.atom ⟨pairPattern, matcher, target⟩], [], []⟩]
        expectedBindings := by
  have exactRun := pair_search_exact
  unfold pairSearch at exactRun
  rw [FuelResult.bind_eq_ok_iff] at exactRun
  rcases exactRun with ⟨matcher, matcherSuccess, searchSuccess⟩
  exact ⟨matcher, matcherSuccess,
    depthFirstFuel_sound _ searchSuccess⟩

end TypePM.Runtime.PatternFunctionMatchingRegression
