import TypePM.Runtime.PatternFunctionMatching
import TypePM.Runtime.EvaluationAdequacy
import TypePM.Source.PatternFunctionExpansion

/-!
# Expression evaluation with scoped pattern-function nodes

The earlier `evalPatternFunctionsFuel` expands only the inline-safe source
fragment before evaluation.  General pattern functions may bind private
variables, so they instead require the isolated `MatchingTree.node` runtime
rule.  This module threads the runtime definition table through the ordinary
evaluator and replaces only the matching search used by `matchAll` and
`matchFirst`.  Its checked public entry point additionally requires proof that
every table entry has a canonical-instance source check and every frozen
declaration has a runtime body with the same name.

This is an executable semantics.  Its successful matching search is linked to
an inductive `DepthFirst` derivation over the executable state-step function;
the structural state-step witness is proved separately.  A general
preservation theorem for this evaluator is deliberately not claimed here.
-/

namespace TypePM.Runtime

open TypePM.Source

end TypePM.Runtime

namespace TypePM.Source

/-- The complete source expression contains no pattern-function application
and no embedded pattern parameter.  This is defined through the existing
structural expander with an empty definition table: that traversal checks
lambda and fix bodies, value-pattern expressions, matcher clause callbacks,
and all `matchFirst` arms rather than only the outer match pattern. -/
def Expr.MNodeFree (expression : Expr) : Prop :=
  PatternFunctionExpansion.expandExpr [] expression = some expression

/-- The complete pattern contains neither an application nor an embedded
parameter; value-pattern expressions are checked recursively. -/
def Pattern.MNodeFree (pattern : Pattern) : Prop :=
  PatternFunctionExpansion.expandPattern [] pattern = some pattern

/-- Matcher clauses are MNode-free exactly when their next-matcher expressions
and every data-arm body are recursively MNode-free. -/
def MatcherClause.MNodeFree (clause : MatcherClause) : Prop :=
  PatternFunctionExpansion.expandClause [] clause = some clause

/-- A matcher data arm is MNode-free when its body is recursively MNode-free. -/
def MatcherArm.MNodeFree (arm : MatcherArm) : Prop :=
  PatternFunctionExpansion.expandArm [] arm = some arm

/-- A single-result match arm checks both its pattern and body recursively. -/
def MatchFirstArm.MNodeFree (arm : MatchFirstArm) : Prop :=
  PatternFunctionExpansion.expandMatchFirstArm [] arm = some arm

theorem Pattern.MNodeFree.not_app
    {pattern : Pattern} {name : PatternFunName} {arguments : List Pattern}
    (free : pattern.MNodeFree) : pattern ≠ .app name arguments := by
  intro equality
  subst pattern
  simp [Pattern.MNodeFree, PatternFunctionExpansion.expandPattern,
    PatternFunctionDefinitions.lookup] at free

theorem Pattern.MNodeFree.not_embed
    {pattern : Pattern} {index : Nat}
    (free : pattern.MNodeFree) : pattern ≠ .embed index := by
  intro equality
  subst pattern
  simp [Pattern.MNodeFree, PatternFunctionExpansion.expandPattern] at free

mutual

  /-- The largest structurally useful subfragment whose two evaluators can be
  compared without an invariant on runtime closure environments.  It excludes
  precisely the four expression cases that invoke evaluator callbacks or matching
  search (`app`, primitive `map`, and the two match forms).  Inert lambda,
  fix, and matcher bodies still carry the full recursive `MNodeFree` check. -/
  inductive Expr.EvaluatorIndependent : Expr → Prop where
    | var : Expr.EvaluatorIndependent (.var index)
    | lit : Expr.EvaluatorIndependent (.lit literal)
    | something : Expr.EvaluatorIndependent .something
    | lam (bodyFree : body.MNodeFree) :
        Expr.EvaluatorIndependent (.lam body)
    | tuple (itemsFree : ExprListEvaluatorIndependent items) :
        Expr.EvaluatorIndependent (.tuple items)
    | letE
        (valueFree : valueExpression.EvaluatorIndependent)
        (bodyFree : body.EvaluatorIndependent) :
        Expr.EvaluatorIndependent (.letE valueExpression body)
    | ctor (argumentsFree : ExprListEvaluatorIndependent arguments) :
        Expr.EvaluatorIndependent (.ctor constructor arguments)
    | prim
        (notMap : operation ≠ .map)
        (argumentsFree : ExprListEvaluatorIndependent arguments) :
        Expr.EvaluatorIndependent (.prim operation arguments)
    | ifE
        (conditionFree : condition.EvaluatorIndependent)
        (thenFree : thenBranch.EvaluatorIndependent)
        (elseFree : elseBranch.EvaluatorIndependent) :
        Expr.EvaluatorIndependent (.ifE condition thenBranch elseBranch)
    | fixE (bodyFree : body.MNodeFree) :
        Expr.EvaluatorIndependent (.fixE body)
    | matcher (literalFree : (Expr.matcher clauses).MNodeFree) :
        Expr.EvaluatorIndependent (.matcher clauses)

  /-- Source-ordered expression-list companion of `EvaluatorIndependent`. -/
  inductive ExprListEvaluatorIndependent : List Expr → Prop where
    | nil : ExprListEvaluatorIndependent []
    | cons
        (headFree : head.EvaluatorIndependent)
        (tailFree : ExprListEvaluatorIndependent tail) :
        ExprListEvaluatorIndependent (head :: tail)

end

mutual

  /-- The evaluator-independent predicate is a genuine subfragment of the
  recursively checked MNode-free language. -/
  theorem Expr.EvaluatorIndependent.mnodeFree
      {expression : Expr}
      (independent : expression.EvaluatorIndependent) : expression.MNodeFree := by
    cases independent with
    | var => simp [Expr.MNodeFree, PatternFunctionExpansion.expandExpr]
    | lit => simp [Expr.MNodeFree, PatternFunctionExpansion.expandExpr]
    | something => simp [Expr.MNodeFree, PatternFunctionExpansion.expandExpr]
    | lam bodyFree =>
        unfold Expr.MNodeFree at bodyFree ⊢
        simp only [PatternFunctionExpansion.expandExpr]
        rw [bodyFree]
        rfl
    | tuple itemsFree =>
        unfold Expr.MNodeFree
        simp only [PatternFunctionExpansion.expandExpr]
        rw [itemsFree.expand_empty]
        rfl
    | letE valueFree bodyFree =>
        unfold Expr.MNodeFree
        simp only [PatternFunctionExpansion.expandExpr]
        rw [valueFree.mnodeFree, bodyFree.mnodeFree]
        rfl
    | ctor argumentsFree =>
        unfold Expr.MNodeFree
        simp only [PatternFunctionExpansion.expandExpr]
        rw [argumentsFree.expand_empty]
        rfl
    | prim _ argumentsFree =>
        unfold Expr.MNodeFree
        simp only [PatternFunctionExpansion.expandExpr]
        rw [argumentsFree.expand_empty]
        rfl
    | ifE conditionFree thenFree elseFree =>
        unfold Expr.MNodeFree
        simp only [PatternFunctionExpansion.expandExpr]
        rw [conditionFree.mnodeFree, thenFree.mnodeFree, elseFree.mnodeFree]
        rfl
    | fixE bodyFree =>
        unfold Expr.MNodeFree at bodyFree ⊢
        simp only [PatternFunctionExpansion.expandExpr]
        rw [bodyFree]
        rfl
    | matcher literalFree => exact literalFree

  /-- Empty-table expansion fixes every evaluator-independent expression list. -/
  theorem ExprListEvaluatorIndependent.expand_empty
      {expressions : List Expr}
      (independent : ExprListEvaluatorIndependent expressions) :
      PatternFunctionExpansion.expandExprList [] expressions = some expressions := by
    cases independent with
    | nil => simp [PatternFunctionExpansion.expandExprList]
    | cons headFree tailFree =>
        simp only [PatternFunctionExpansion.expandExprList]
        rw [headFree.mnodeFree, tailFree.expand_empty]
        rfl

end

end TypePM.Source

namespace TypePM.Runtime

open TypePM.Source

/-- On an ordinary, recursively MNode-free pattern, the scoped head step is
definitionally the ordinary atom-reducer step.  This is the core commuting
lemma needed by a future full search simulation; the remaining obligation is
to prove that matcher reductions preserve MNode-freedom of every generated
branch and callback value. -/
theorem stepPatternFunctionHead_mnodeFree_atom
    (free : atom.pattern.MNodeFree) :
    stepPatternFunctionHead definitions reduceAtom (.atom atom) remaining
        environment bindings =
      FuelResult.bind (reduceAtom (bindings ++ environment) atom) fun result =>
        match result with
        | .miss => .stuck
        | .hit reduction =>
            .ok (continueTreeAtom remaining environment bindings reduction) := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern <;>
    simp only [stepPatternFunctionHead]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (free.not_embed rfl)
  · exact False.elim (free.not_app rfl)

/-- Execute core single-result matching with the scoped pattern-function
search.  Source-arm order and first-result selection agree with
`evalMatchFirstArmsFuel`; only the search engine is extended with MNodes. -/
def evalPatternFunctionNodeArmsFuel
    (definitions : PatternFunctionDefinitions)
    (evaluate : ValueEnvironment → Source.Expr → FuelResult Value)
    (fuel : Nat) (environment : ValueEnvironment)
    (target matcher : Value) :
    List Source.MatchFirstArm → Source.Expr → FuelResult Value
  | [], fallback => evaluate environment fallback
  | arm :: rest, fallback =>
      FuelResult.bind
        (searchPatternFunctionsFuel definitions evaluate fuel environment
          arm.pattern matcher target)
        fun bindingGroups =>
          match bindingGroups with
          | [] => evalPatternFunctionNodeArmsFuel definitions evaluate fuel
              environment target matcher rest fallback
          | bindings :: _ => evaluate (bindings ++ environment) arm.body

mutual

  /-- Fuel-bounded call-by-value evaluation using scoped MNode search for
  pattern-function applications inside `matchAll` and `matchFirst`.
  Every other expression clause is the corresponding `evalFuel` clause. -/
  def evalPatternFunctionNodesFuel
      (definitions : PatternFunctionDefinitions) :
      Nat → ValueEnvironment → Source.Expr → FuelResult Value
    | 0, _, _ => .timeout
    | fuel + 1, environment, expression =>
        match expression with
        | .var index =>
            match environment[index]? with
            | some value => .ok value
            | none => .stuck
        | .lit literal => .ok (.int literal)
        | .something => .ok .something
        | .lam body => .ok (Value.plainClosure environment body)
        | .app function argument =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment function)
              fun functionValue =>
                FuelResult.bind
                  (evalPatternFunctionNodesFuel definitions fuel environment argument)
                  fun argumentValue =>
                    applyPatternFunctionNodesFuel definitions fuel functionValue
                      argumentValue
        | .tuple items =>
            FuelResult.map Value.tuple
              (FuelResult.traverse
                (evalPatternFunctionNodesFuel definitions fuel environment) items)
        | .letE valueExpression body =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment
                valueExpression)
              fun value =>
                evalPatternFunctionNodesFuel definitions fuel
                  (value :: environment) body
        | .ctor constructor arguments =>
            FuelResult.map (Value.data constructor)
              (FuelResult.traverse
                (evalPatternFunctionNodesFuel definitions fuel environment)
                arguments)
        | .prim operation arguments =>
            FuelResult.bind
              (FuelResult.traverse
                (evalPatternFunctionNodesFuel definitions fuel environment)
                arguments)
              (evalPrimitive
                (applyPatternFunctionNodesFuel definitions fuel) operation)
        | .ifE condition thenBranch elseBranch =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment condition)
              fun conditionValue =>
                match conditionValue with
                | .data constructor [] =>
                    if constructor = DataCtor.true then
                      evalPatternFunctionNodesFuel definitions fuel environment
                        thenBranch
                    else if constructor = DataCtor.false then
                      evalPatternFunctionNodesFuel definitions fuel environment
                        elseBranch
                    else
                      .stuck
                | _ => .stuck
        | .fixE body => .ok (Value.recursiveClosure environment body)
        | .matcher clauses => .ok (Value.matcherClosure environment clauses)
        | .matchAll target matcher pattern body =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment target)
              fun targetValue =>
                FuelResult.bind
                  (evalPatternFunctionNodesFuel definitions fuel environment matcher)
                  fun matcherValue =>
                    FuelResult.bind
                      (searchPatternFunctionsFuel definitions
                        (evalPatternFunctionNodesFuel definitions fuel) fuel
                        environment pattern matcherValue targetValue)
                      fun bindingGroups =>
                        FuelResult.map Value.buildList
                          (FuelResult.traverse
                            (fun bindings =>
                              evalPatternFunctionNodesFuel definitions fuel
                                (bindings ++ environment) body)
                            bindingGroups)
        | .matchFirst target matcher arms fallback =>
            FuelResult.bind
              (evalPatternFunctionNodesFuel definitions fuel environment target)
              fun targetValue =>
                FuelResult.bind
                  (evalPatternFunctionNodesFuel definitions fuel environment matcher)
                  fun matcherValue =>
                    evalPatternFunctionNodeArmsFuel definitions
                      (evalPatternFunctionNodesFuel definitions fuel) fuel
                      environment targetValue matcherValue arms fallback

  /-- Application companion of `evalPatternFunctionNodesFuel`. -/
  def applyPatternFunctionNodesFuel
      (definitions : PatternFunctionDefinitions) :
      Nat → Value → Value → FuelResult Value
    | 0, _, _ => .timeout
    | fuel + 1, .closure .plain definitionEnvironment body, argument =>
        evalPatternFunctionNodesFuel definitions fuel
          (argument :: definitionEnvironment) body
    | fuel + 1,
        closure@(.closure .recursive definitionEnvironment body), argument =>
        evalPatternFunctionNodesFuel definitions fuel
          (argument :: closure :: definitionEnvironment) body
    | _ + 1, _, _ => .stuck

end

private theorem evalPrimitive_callback_irrelevant
    (notMap : operation ≠ PrimOp.map)
    (left right : Value → Value → FuelResult Value) :
    evalPrimitive left operation arguments =
      evalPrimitive right operation arguments := by
  cases operation with
  | map => exact (notMap rfl).elim
  | add =>
      rcases arguments with _ | ⟨first, tail⟩
      · rfl
      rcases tail with _ | ⟨second, tail⟩
      · cases first <;> rfl
      rcases tail with _ | ⟨third, tail⟩
      · cases first <;> cases second <;> rfl
      · cases first <;> cases second <;> rfl
  | append =>
      rcases arguments with _ | ⟨first, tail⟩
      · rfl
      rcases tail with _ | ⟨second, tail⟩
      · rfl
      rcases tail with _ | ⟨third, tail⟩ <;> rfl
  | member =>
      rcases arguments with _ | ⟨first, tail⟩
      · rfl
      rcases tail with _ | ⟨second, tail⟩
      · rfl
      rcases tail with _ | ⟨third, tail⟩ <;> rfl
  | deleteFirst =>
      rcases arguments with _ | ⟨first, tail⟩
      · rfl
      rcases tail with _ | ⟨second, tail⟩
      · rfl
      rcases tail with _ | ⟨third, tail⟩ <;> rfl
  | pairFirst =>
      change (match arguments with
        | [.tuple [first, _second]] => FuelResult.ok first
        | _ => FuelResult.stuck) =
        (match arguments with
        | [.tuple [first, _second]] => FuelResult.ok first
        | _ => FuelResult.stuck)
      rfl
  | pairSecond =>
      change (match arguments with
        | [.tuple [_first, second]] => FuelResult.ok second
        | _ => FuelResult.stuck) =
        (match arguments with
        | [.tuple [_first, second]] => FuelResult.ok second
        | _ => FuelResult.stuck)
      rfl

mutual

  /-- Exact evaluator simulation on the structurally evaluator-independent
  part of the MNode-free language.  The definition table is irrelevant on
  this fragment. -/
  theorem evaluatorIndependent_nodeEvaluation_eq_evalFuel
      (free : expression.EvaluatorIndependent)
      (definitions : PatternFunctionDefinitions) (fuel : Nat)
      (environment : ValueEnvironment) :
      evalPatternFunctionNodesFuel definitions fuel environment expression =
        evalFuel fuel environment expression := by
    cases fuel with
    | zero => rfl
    | succ fuel =>
        cases free with
        | var => rfl
        | lit => rfl
        | something => rfl
        | lam => rfl
        | tuple itemsFree =>
            change FuelResult.map Value.tuple
                (FuelResult.traverse
                  (evalPatternFunctionNodesFuel definitions fuel environment) _) =
              FuelResult.map Value.tuple
                (FuelResult.traverse (evalFuel fuel environment) _)
            rw [evaluatorIndependent_nodeEvaluation_traverse_eq_evalFuel
              itemsFree definitions fuel environment]
        | letE valueFree bodyFree =>
            change FuelResult.bind
                (evalPatternFunctionNodesFuel definitions fuel environment _)
                (fun value => evalPatternFunctionNodesFuel definitions fuel
                  (value :: environment) _) =
              FuelResult.bind (evalFuel fuel environment _)
                (fun value => evalFuel fuel (value :: environment) _)
            rw [evaluatorIndependent_nodeEvaluation_eq_evalFuel valueFree]
            congr 1
            funext value
            exact evaluatorIndependent_nodeEvaluation_eq_evalFuel bodyFree
              definitions fuel (value :: environment)
        | ctor argumentsFree =>
            change FuelResult.map (Value.data _)
                (FuelResult.traverse
                  (evalPatternFunctionNodesFuel definitions fuel environment) _) =
              FuelResult.map (Value.data _)
                (FuelResult.traverse (evalFuel fuel environment) _)
            rw [evaluatorIndependent_nodeEvaluation_traverse_eq_evalFuel
              argumentsFree definitions fuel environment]
        | prim notMap argumentsFree =>
            change FuelResult.bind
                (FuelResult.traverse
                  (evalPatternFunctionNodesFuel definitions fuel environment) _)
                (evalPrimitive
                  (applyPatternFunctionNodesFuel definitions fuel) _) =
              FuelResult.bind
                (FuelResult.traverse (evalFuel fuel environment) _)
                (evalPrimitive (applyFuel fuel) _)
            rw [evaluatorIndependent_nodeEvaluation_traverse_eq_evalFuel
              argumentsFree definitions fuel environment]
            congr 1
            exact funext fun _ =>
              evalPrimitive_callback_irrelevant notMap _ _
        | ifE conditionFree thenFree elseFree =>
            change FuelResult.bind
                (evalPatternFunctionNodesFuel definitions fuel environment _)
                (fun conditionValue => match conditionValue with
                  | .data constructor [] =>
                      if constructor = DataCtor.true then
                        evalPatternFunctionNodesFuel definitions fuel environment _
                      else if constructor = DataCtor.false then
                        evalPatternFunctionNodesFuel definitions fuel environment _
                      else .stuck
                  | _ => .stuck) =
              FuelResult.bind (evalFuel fuel environment _)
                (fun conditionValue => match conditionValue with
                  | .data constructor [] =>
                      if constructor = DataCtor.true then
                        evalFuel fuel environment _
                      else if constructor = DataCtor.false then
                        evalFuel fuel environment _
                      else .stuck
                  | _ => .stuck)
            rw [evaluatorIndependent_nodeEvaluation_eq_evalFuel conditionFree]
            congr 1
            funext conditionValue
            cases conditionValue with
            | data constructor arguments =>
                cases arguments with
                | nil =>
                    by_cases isTrue : constructor = DataCtor.true
                    · simp only [isTrue, if_pos]
                      exact evaluatorIndependent_nodeEvaluation_eq_evalFuel
                        thenFree definitions fuel environment
                    · by_cases isFalse : constructor = DataCtor.false
                      · simp only [isFalse, if_pos]
                        exact evaluatorIndependent_nodeEvaluation_eq_evalFuel
                          elseFree definitions fuel environment
                      · simp [isTrue, isFalse]
                | cons head tail => rfl
            | int | tuple | closure | matcherV | something => rfl
        | fixE => rfl
        | matcher => rfl

  /-- Left-to-right traversal companion of
  `nodeEvaluation_eq_evalFuel`. -/
  theorem evaluatorIndependent_nodeEvaluation_traverse_eq_evalFuel
      (free : Source.ExprListEvaluatorIndependent expressions)
      (definitions : PatternFunctionDefinitions) (fuel : Nat)
      (environment : ValueEnvironment) :
      FuelResult.traverse
          (evalPatternFunctionNodesFuel definitions fuel environment)
          expressions =
        FuelResult.traverse (evalFuel fuel environment) expressions := by
    cases free with
    | nil => rfl
    | cons headFree tailFree =>
        simp only [FuelResult.traverse]
        rw [evaluatorIndependent_nodeEvaluation_eq_evalFuel headFree,
          evaluatorIndependent_nodeEvaluation_traverse_eq_evalFuel tailFree]

end


/-- Adequacy transfers from the ordinary evaluator on the proved simulation
fragment: every successful scoped-node evaluation has an ordinary big-step
derivation. -/
theorem evaluatorIndependent_nodeEvaluation_sound
    (free : expression.EvaluatorIndependent)
    (success : evalPatternFunctionNodesFuel definitions fuel environment
      expression = .ok value) :
    Eval environment expression value := by
  rw [evaluatorIndependent_nodeEvaluation_eq_evalFuel free] at success
  exact evalFuel_sound success

/-- Public entry point for scoped pattern-function evaluation.  The
`agreement` argument certifies that every executable definition has a
canonical-instance source check and that every frozen declaration has a body
with the same name.  The proof does not change execution; it prevents callers
from silently pairing the evaluator with an unrelated runtime table. -/
def evalCheckedPatternFunctionNodesFuel
    (signature : FrozenSignature) (definitions : PatternFunctionDefinitions)
    (_agreement : definitions.Agree signature)
    (fuel : Nat) (environment : ValueEnvironment) (expression : Source.Expr) :
    FuelResult Value :=
  evalPatternFunctionNodesFuel definitions fuel environment expression


/-- Successful execution of a top-level `matchAll` exposes a successful
scoped search with an inductive depth-first derivation over the executable
state-step function, followed by the ordinary left-to-right evaluation of all
selected bodies. -/
theorem evalPatternFunctionNodesFuel_matchAll_search_sound
    (success :
      evalPatternFunctionNodesFuel definitions (fuel + 1) environment
        (.matchAll target matcher pattern body) = .ok result) :
    ∃ targetValue matcherValue bindingGroups values,
      evalPatternFunctionNodesFuel definitions fuel environment target =
          .ok targetValue ∧
      evalPatternFunctionNodesFuel definitions fuel environment matcher =
          .ok matcherValue ∧
      searchPatternFunctionsFuel definitions
          (evalPatternFunctionNodesFuel definitions fuel) fuel environment
          pattern matcherValue targetValue = .ok bindingGroups ∧
      DepthFirst
        (stepPatternFunctionState definitions
          (evaluationAtomReducer
            (evalPatternFunctionNodesFuel definitions fuel)))
        [⟨[.atom ⟨pattern, matcherValue, targetValue⟩], environment, []⟩]
        bindingGroups ∧
      FuelResult.traverse
          (fun bindings => evalPatternFunctionNodesFuel definitions fuel
            (bindings ++ environment) body)
          bindingGroups = .ok values ∧
      result = Value.buildList values := by
  rw [evalPatternFunctionNodesFuel.eq_def] at success
  simp only at success
  rw [FuelResult.bind_eq_ok_iff] at success
  rcases success with ⟨targetValue, targetSuccess, success⟩
  rw [FuelResult.bind_eq_ok_iff] at success
  rcases success with ⟨matcherValue, matcherSuccess, success⟩
  rw [FuelResult.bind_eq_ok_iff] at success
  rcases success with ⟨bindingGroups, searchSuccess, success⟩
  rw [FuelResult.map_eq_ok_iff] at success
  rcases success with ⟨values, bodySuccess, resultEq⟩
  exact ⟨targetValue, matcherValue, bindingGroups, values, targetSuccess,
    matcherSuccess, searchSuccess,
    searchPatternFunctionsFuel_sound definitions _ searchSuccess,
    bodySuccess, resultEq.symm⟩

/-- A successful checked entry-point run of `matchAll` exposes the same
inductive depth-first derivation as the raw evaluator.  Source/runtime table
agreement is an interface precondition and does not alter execution. -/
theorem evalCheckedPatternFunctionNodesFuel_matchAll_search_sound
    (agreement : definitions.Agree signature)
    (success :
      evalCheckedPatternFunctionNodesFuel signature definitions agreement
        (fuel + 1) environment (.matchAll target matcher pattern body) =
        .ok result) :
    ∃ targetValue matcherValue bindingGroups values,
      evalPatternFunctionNodesFuel definitions fuel environment target =
          .ok targetValue ∧
      evalPatternFunctionNodesFuel definitions fuel environment matcher =
          .ok matcherValue ∧
      searchPatternFunctionsFuel definitions
          (evalPatternFunctionNodesFuel definitions fuel) fuel environment
          pattern matcherValue targetValue = .ok bindingGroups ∧
      DepthFirst
        (stepPatternFunctionState definitions
          (evaluationAtomReducer
            (evalPatternFunctionNodesFuel definitions fuel)))
        [⟨[.atom ⟨pattern, matcherValue, targetValue⟩], environment, []⟩]
        bindingGroups ∧
      FuelResult.traverse
          (fun bindings => evalPatternFunctionNodesFuel definitions fuel
            (bindings ++ environment) body)
          bindingGroups = .ok values ∧
      result = Value.buildList values := by
  exact evalPatternFunctionNodesFuel_matchAll_search_sound success

end TypePM.Runtime
