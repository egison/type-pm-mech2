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

/-- The same MNode search is used by derived single-result matching; only the
first successful binding group is consumed. -/
def pairFirstProgram : Source.Expr :=
  .matchFirst pairTarget multisetSomething
    [⟨pairPattern, .tuple [.var 1, .var 0]⟩]

set_option maxRecDepth 100000 in
theorem pair_first_program_executes_exact :
    evalPatternFunctionNodesFuel definitions 250 [] pairFirstProgram =
      .ok (.tuple [.int 1, .int 2]) := by
  with_unfolding_all rfl

end TypePM.Runtime.PatternFunctionNodeEvaluationRegression
