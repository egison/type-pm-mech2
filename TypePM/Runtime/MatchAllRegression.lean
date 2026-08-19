import TypePM.Runtime.EvaluationCompleteness

/-!
# Integrated `matchAll` regressions

These examples cross the whole boundary: expression evaluation, atom
reduction, ordered search, binding-group environments, and result-body
evaluation.  Matcher-clause examples use executable source expressions rather
than a callback oracle.
-/

namespace TypePM.Runtime.MatchAllRegression

open TypePM.Source

private def sourceList : List Expr → Expr
  | [] => .ctor DataCtor.nil []
  | head :: tail => .ctor DataCtor.cons [head, sourceList tail]

def somethingVariable : Expr :=
  .matchAll (.lit 7) .something .var (.var 0)

def somethingValueMismatch : Expr :=
  .matchAll (.lit 7) .something (.value (.lit 8)) (.lit 0)

/-- Paper 1, P1-L14: `matchAll 5 as something with #1` is well formed at
runtime and produces no result, rather than getting stuck. -/
def paperIntegerValueMismatch : Expr :=
  .matchAll (.lit 5) .something (.value (.lit 1)) (.lit 0)

theorem something_variable_evaluates_body_under_binding :
    evalFuel 3 [] somethingVariable =
      .ok (Value.buildList [.int 7]) := by
  rfl

theorem something_value_mismatch_is_empty_not_stuck :
    evalFuel 3 [] somethingValueMismatch = .ok Value.nilValue := by
  rfl

theorem paper_integer_value_mismatch_is_empty_not_stuck :
    evalFuel 3 [] paperIntegerValueMismatch = .ok Value.nilValue := by
  rfl

/-- A head-shaped clause returns two equal-position alternatives.  The later
catch-all clause must not run after that hit. -/
def headClause : MatcherClause :=
  .mk (.ctor PatternCtor.cons [.hole, .wild]) .something
    [.mk .var (sourceList [.lit 1, .lit 1])]

/-- The fallback delegates its one hole to `something`, passing the complete
target through exactly once. -/
def catchAllClause : MatcherClause :=
  .mk .hole .something [.mk .var (sourceList [.var 0])]

def simpleMatcher : Expr := .matcher [headClause, catchAllClause]

def headMatch : Expr :=
  .matchAll (.lit 99) simpleMatcher
    (.ctor PatternCtor.cons [.var, .wild]) (.var 0)

def catchAllMatch : Expr :=
  .matchAll (.lit 42) simpleMatcher .var (.var 0)

private theorem list11_eval :
    Eval [.int 99] (sourceList [.lit 1, .lit 1])
      (Value.buildList [.int 1, .int 1]) := by
  exact .ctor (.cons .lit (.cons (.ctor (.cons .lit
    (.cons (.ctor .nil) .nil))) .nil))

private theorem listTarget_eval :
    Eval [.int 42] (sourceList [.var 0])
      (Value.buildList [.int 42]) := by
  exact .ctor (.cons (.var (Lookup.head _ _))
    (.cons (.ctor .nil) .nil))

private theorem head_atom_reduces :
    EvalAtomReduces []
      ⟨.ctor PatternCtor.cons [.var, .wild],
        Value.matcherClosure [] [headClause, catchAllClause], .int 99⟩
      ⟨[[⟨.var, .something, .int 1⟩],
        [⟨.var, .something, .int 1⟩]], []⟩ := by
  apply EvalAtomReduces.matcher
  apply EvalMatcherClausesDispatch.hit
  apply EvalMatcherClauseDispatches.matched
  · exact .ctor (.cons .hole (.cons .wild .nil))
  · exact .nil
  · apply EvalMatcherArmsDispatch.hit
    refine EvalMatcherArmDispatches.hit
      (dataValues := [.int 99])
      (decompositionValue := Value.buildList [.int 1, .int 1])
      (decompositions := [[.int 1], [.int 1]])
      (matcherProduct := .something)
      (matchers := [.something]) ?_ ?_ ?_ ?_ ?_ ?_
    · exact .var
    · exact list11_eval
    · simp [PatternDispatch.append, PatternDispatch.empty,
        decodeDecompositions, decodeProduct, Value.buildList,
        Value.nilValue, Value.consValue, Value.viewList]
    · exact .something
    · rfl
    · rfl

private theorem catch_all_atom_reduces :
    EvalAtomReduces []
      ⟨.var, Value.matcherClosure [] [headClause, catchAllClause], .int 42⟩
      ⟨[[⟨.var, .something, .int 42⟩]], []⟩ := by
  apply EvalAtomReduces.matcher
  apply EvalMatcherClausesDispatch.skip
  · exact .miss rfl
  · apply EvalMatcherClausesDispatch.hit
    apply EvalMatcherClauseDispatches.matched
    · exact .hole
    · exact .nil
    · apply EvalMatcherArmsDispatch.hit
      refine EvalMatcherArmDispatches.hit
        (dataValues := [.int 42])
        (decompositionValue := Value.buildList [.int 42])
        (decompositions := [[.int 42]])
        (matcherProduct := .something)
        (matchers := [.something]) ?_ ?_ ?_ ?_ ?_ ?_
      · exact .var
      · exact listTarget_eval
      · simp [decodeDecompositions, decodeProduct, Value.buildList,
          Value.nilValue, Value.consValue, Value.viewList]
      · exact .something
      · rfl
      · rfl

private theorem head_matching_search :
    EvalMatchingSearch
      [⟨[⟨.ctor PatternCtor.cons [.var, .wild],
          Value.matcherClosure [] [headClause, catchAllClause], .int 99⟩],
        [], []⟩] [[.int 1], [.int 1]] := by
  apply EvalMatchingSearch.expand head_atom_reduces
  apply EvalMatchingSearch.expand EvalAtomReduces.somethingVar
  apply EvalMatchingSearch.yield
  apply EvalMatchingSearch.expand EvalAtomReduces.somethingVar
  exact .yield .nil

private theorem catch_all_matching_search :
    EvalMatchingSearch
      [⟨[⟨.var, Value.matcherClosure [] [headClause, catchAllClause],
          .int 42⟩], [], []⟩] [[.int 42]] := by
  apply EvalMatchingSearch.expand catch_all_atom_reduces
  apply EvalMatchingSearch.expand EvalAtomReduces.somethingVar
  exact .yield .nil

theorem matcher_closure_head_preserves_duplicate_branches :
    Eval [] headMatch (Value.buildList [.int 1, .int 1]) :=
  .matchAll .lit .matcher head_matching_search
    (.cons (.var (Lookup.head _ _))
      (.cons (.var (Lookup.head _ _)) .nil))

theorem matcher_closure_falls_through_to_catch_all :
    Eval [] catchAllMatch (Value.buildList [.int 42]) :=
  .matchAll .lit .matcher catch_all_matching_search
    (.cons (.var (Lookup.head _ _)) .nil)

theorem integrated_head_execution_has_finite_fuel :
    ∃ fuel, evalFuel fuel [] headMatch =
      .ok (Value.buildList [.int 1, .int 1]) :=
  matcher_closure_head_preserves_duplicate_branches.complete

theorem integrated_derivation_has_finite_fuel
    (derivation : Eval [] catchAllMatch (Value.buildList [.int 42])) :
    ∃ fuel, evalFuel fuel [] catchAllMatch =
      .ok (Value.buildList [.int 42]) :=
  derivation.complete

theorem zero_fuel_is_timeout :
    evalFuel 0 [] somethingVariable = .timeout := by
  rfl

theorem unbound_target_is_stuck :
    evalFuel 5 [] (.matchAll (.var 0) .something .wild (.lit 0)) =
      .stuck := by
  rfl

/-- Pattern-function atom reduction is deliberately still outside M5's
implemented rule set.  The integrated evaluator preserves that coverage gap
as `stuck`; it does not turn it into normal match failure. -/
theorem pattern_function_atom_is_stuck :
    evalFuel 5 []
      (.matchAll (.lit 1) .something
        (.app ⟨"unimplemented"⟩ []) (.lit 0)) = .stuck := by
  rfl

end TypePM.Runtime.MatchAllRegression
