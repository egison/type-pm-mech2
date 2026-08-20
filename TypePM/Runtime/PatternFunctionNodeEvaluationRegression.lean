import TypePM.Runtime.PatternFunctionNodeEvaluation
import TypePM.Source.Paper1Programs
import TypePM.Source.M4PatternFunctionPairRegression

/-!
# Whole-expression regressions for scoped pattern-function evaluation

These programs combine Paper 2's general `pair` pattern function with the
actual seven-clause source `multiset` matcher.  Unlike the lower-level search
regression, target evaluation, matcher construction, MNode search, and result
body evaluation all run through one public expression evaluator.
-/

namespace TypePM.Runtime.PatternFunctionNodeEvaluationRegression

open TypePM.Source
open TypePM.Source.Paper1Programs
open TypePM.Source.M4PatternFunctionPairRegression

def pairPattern : Pattern :=
  .ctor PatternCtor.cons [.var, .app pairName [.var, .wild]]

def pairTarget : Source.Expr :=
  sourceList [.lit 1, .lit 2, .lit 1, .lit 3]

/-- `matchAll [1,2,1,3] as multiset something with
    $outer :: pair $inner _ -> (outer, inner)`. -/
def pairProgram : Source.Expr :=
  .matchAll pairTarget multisetSomething pairPattern
    (.tuple [.var 1, .var 0])

def expectedPairs : Value :=
  Value.buildList
    [.tuple [.int 1, .int 2], .tuple [.int 1, .int 2],
     .tuple [.int 1, .int 3], .tuple [.int 1, .int 3]]

set_option maxRecDepth 100000 in
theorem pair_program_executes_exact :
    evalPatternFunctionNodesFuel definitions 250 [] pairProgram =
      .ok expectedPairs := by
  with_unfolding_all rfl

/-- The public checked entry point executes the same whole program, with the
runtime definition table explicitly connected to the frozen source
interface. -/
theorem pair_checked_program_executes_exact :
    evalCheckedPatternFunctionNodesFuel signature definitions definitions_agree
        250 [] pairProgram = .ok expectedPairs := by
  exact pair_program_executes_exact

/-- The successful whole-expression run contains an inductive `DepthFirst`
derivation over the executable MNode state-step function used to produce its
four body environments. -/
theorem pair_program_has_step_function_depth_first_derivation :
    ∃ targetValue matcherValue bindingGroups,
      evalPatternFunctionNodesFuel definitions 249 [] pairTarget =
          .ok targetValue ∧
      evalPatternFunctionNodesFuel definitions 249 [] multisetSomething =
          .ok matcherValue ∧
      searchPatternFunctionsFuel definitions
          (evalPatternFunctionNodesFuel definitions 249) 249 [] pairPattern
          matcherValue targetValue = .ok bindingGroups ∧
      DepthFirst
        (stepPatternFunctionState definitions
          (evaluationAtomReducer
            (evalPatternFunctionNodesFuel definitions 249)))
        [⟨[.atom ⟨pairPattern, matcherValue, targetValue⟩], [], []⟩]
        bindingGroups := by
  rcases evalCheckedPatternFunctionNodesFuel_matchAll_search_sound
      definitions_agree pair_checked_program_executes_exact with
    ⟨targetValue, matcherValue, bindingGroups, _values, targetSuccess,
      matcherSuccess, searchSuccess, searchDerivation, _bodySuccess, _resultEq⟩
  exact ⟨targetValue, matcherValue, bindingGroups, targetSuccess,
    matcherSuccess, searchSuccess, searchDerivation⟩

/-- The same MNode search is used by core single-result matching; only the
first successful binding group is consumed. -/
def pairFirstProgram : Source.Expr :=
  .matchFirst pairTarget multisetSomething
    [⟨pairPattern, .tuple [.var 1, .var 0]⟩] (.lit 99)

set_option maxRecDepth 100000 in
theorem pair_first_program_executes_exact :
    evalPatternFunctionNodesFuel definitions 250 [] pairFirstProgram =
      .ok (.tuple [.int 1, .int 2]) := by
  with_unfolding_all rfl

/-! ## Ordinary-fragment simulation -/

/-- This nested ordinary pattern checks that `MNodeFree` traverses match arms,
value-pattern expressions, and result bodies, even though the executable
simulation below deliberately stops before matching search. -/
def nestedOrdinaryMatch : Source.Expr :=
  .matchFirst (.lit 1) .something [⟨.value (.lit 1), .lit 2⟩] (.lit 3)

theorem nested_ordinary_match_is_mnode_free : nestedOrdinaryMatch.MNodeFree := by
  with_unfolding_all rfl

/-- A representative evaluator-independent program with sequencing, a
non-callback primitive, variables, and tuple construction. -/
def independentProgram : Source.Expr :=
  .letE (.prim .add [.lit 1, .lit 2]) (.tuple [.var 0, .lit 4])

theorem independent_program_fragment :
    independentProgram.EvaluatorIndependent := by
  exact .letE
    (.prim (by decide) (.cons .lit (.cons .lit .nil)))
    (.tuple (.cons .var (.cons .lit .nil)))

theorem independent_program_simulates_ordinary_evaluation :
    evalPatternFunctionNodesFuel definitions 8 [] independentProgram =
      evalFuel 8 [] independentProgram :=
  evaluatorIndependent_nodeEvaluation_eq_evalFuel independent_program_fragment
    definitions 8 []

/-- The equality theorem transfers the ordinary evaluator's adequacy result,
not merely its computed output. -/
theorem independent_program_has_big_step_derivation :
    Eval [] independentProgram (.tuple [.int 3, .int 4]) := by
  apply evaluatorIndependent_nodeEvaluation_sound
    (definitions := definitions) (fuel := 8) independent_program_fragment
  with_unfolding_all rfl

end TypePM.Runtime.PatternFunctionNodeEvaluationRegression
