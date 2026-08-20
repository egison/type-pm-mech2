import TypePM.TotalPlainClosureSafety
import TypePM.Source.Paper1Programs

/-!
# Regression: a plain lambda captures a total recursive environment

The captured recursive closure has a matcher-literal body, so the old
`ValueTyping`/`EnvironmentTyping` route cannot justify the surrounding plain
closure.  The extended relation types that closure and proves application,
`letE`, and `map` no-stuck without a hand-built evaluation assumption.
-/

namespace TypePM.TotalPlainClosureSafetyRegression

open TypePM.Runtime

def recursiveMatcher : Value :=
  Value.recursiveClosure [] (.matcher [])

def recursiveMatcherType : Ty :=
  .fn .int (.matcher .any .int)

theorem recursiveMatcher_totalTyped :
    TotalValueTyping recursiveMatcher recursiveMatcherType := by
  exact .recursiveClosure .nil (.matcher .nil)

def capturedEnvironment : ValueEnvironment := [recursiveMatcher]

def capturedContext : List Ty := [recursiveMatcherType]

theorem capturedEnvironment_totalPlainTyped :
    TotalPlainEnvironmentTyping capturedEnvironment capturedContext := by
  exact .cons (.existing recursiveMatcher_totalTyped) .nil

private theorem identityBodyTyped (context : List Ty) :
    TotalRecursiveClosureBodyTyping (.int :: context) (.var 0) .int := by
  exact .expression (.core (.core (.var rfl)))

private theorem identityBodySafe (context : List Ty) :
    TotalPlainEnvironmentSafe (.var 0) .int (.int :: context) :=
  totalPlainEnvironmentSafe_var rfl

def capturedIdentityApplication : Source.Expr :=
  .app (.lam (.var 0)) (.lit 7)

theorem capturedIdentityApplication_safe :
    TotalPlainEnvironmentSafe capturedIdentityApplication .int
      capturedContext := by
  exact totalPlainEnvironmentSafe_app
    (totalPlainFunctionEnvironmentSafe_lam
      (identityBodyTyped capturedContext) (identityBodySafe capturedContext))
    (totalPlainEnvironmentSafe_lit 7)

theorem capturedIdentityApplication_exact :
    evalFuel 3 capturedEnvironment capturedIdentityApplication = .ok (.int 7) := by
  rfl

theorem capturedIdentityApplication_neverStuck (fuel : Nat) :
    (evalFuel fuel capturedEnvironment capturedIdentityApplication).NotStuck :=
  (capturedIdentityApplication_safe fuel capturedEnvironment
    capturedEnvironment_totalPlainTyped).notStuck

def capturedIdentityLet : Source.Expr :=
  .letE (.lam (.var 0)) (.var 0)

theorem capturedIdentityLet_safe :
    TotalPlainEnvironmentSafe capturedIdentityLet (.fn .int .int)
      capturedContext := by
  apply totalPlainEnvironmentSafe_letE
  · exact totalPlainEnvironmentSafe_lam
      (identityBodyTyped capturedContext) (identityBodySafe capturedContext)
  · exact totalPlainEnvironmentSafe_var rfl

theorem capturedIdentityLet_exact :
    evalFuel 2 capturedEnvironment capturedIdentityLet =
      .ok (Value.plainClosure capturedEnvironment (.var 0)) := by
  rfl

theorem capturedIdentityLet_neverStuck (fuel : Nat) :
    (evalFuel fuel capturedEnvironment capturedIdentityLet).NotStuck :=
  (capturedIdentityLet_safe fuel capturedEnvironment
    capturedEnvironment_totalPlainTyped).notStuck

def mapEnvironment : ValueEnvironment :=
  [Value.buildList [.int 1, .int 2], recursiveMatcher]

def mapContext : List Ty :=
  [TypePM.DataTypes.list .int, recursiveMatcherType]

theorem mapEnvironment_totalPlainTyped :
    TotalPlainEnvironmentTyping mapEnvironment mapContext := by
  exact .cons
    (.list (.cons (.existing (.ordinary (.int 1)))
      (.cons (.existing (.ordinary (.int 2))) .nil)))
    (.cons (.existing recursiveMatcher_totalTyped) .nil)

def capturedIdentityMap : Source.Expr :=
  .prim PrimOp.map [.lam (.var 0), .var 0]

theorem capturedIdentityMap_safe :
    TotalPlainEnvironmentSafe capturedIdentityMap
      (TypePM.DataTypes.list .int) mapContext := by
  exact totalPlainEnvironmentSafe_map
    (totalPlainFunctionEnvironmentSafe_lam
      (identityBodyTyped mapContext) (identityBodySafe mapContext))
    (totalPlainEnvironmentSafe_var rfl)

theorem capturedIdentityMap_exact :
    evalFuel 4 mapEnvironment capturedIdentityMap =
      .ok (Value.buildList [.int 1, .int 2]) := by
  with_unfolding_all rfl

theorem capturedIdentityMap_neverStuck (fuel : Nat) :
    (evalFuel fuel mapEnvironment capturedIdentityMap).NotStuck :=
  (capturedIdentityMap_safe fuel mapEnvironment
    mapEnvironment_totalPlainTyped).notStuck

/-! ## Paper 1 list-join body with explicit recursive boundaries -/

def listType (element : Ty) : Ty :=
  TypePM.DataTypes.list element

def splitPairType (element : Ty) : Ty :=
  .prod [listType element, listType element]

def splitResultsType (element : Ty) : Ty :=
  listType (splitPairType element)

def listJoinContext (element matcherArgument : Ty)
    (capability : Cap) : List Ty :=
  [element, listType element, matcherArgument,
    .fn matcherArgument (.matcher capability (listType element))]

def listJoinPattern : Source.Pattern :=
  .ctor PatternCtor.join [.var, .var]

private theorem listSplitTailResults_eq :
    TypePM.Source.Paper1Programs.listSplitTailResults =
      .matchAll (.var 1) (.app (.var 3) (.var 2)) listJoinPattern
        (.tuple [.var 0, .var 1]) := by
  with_unfolding_all rfl

private theorem listSplitBody_safe
    (element matcherArgument : Ty) (capability : Cap) :
    TotalPlainEnvironmentSafe (.tuple [.var 0, .var 1])
      (splitPairType element)
      ([listType element, listType element] ++
        listJoinContext element matcherArgument capability) := by
  apply totalPlainEnvironmentSafe_tuple
  exact .cons (totalPlainEnvironmentSafe_var rfl)
    (.cons (totalPlainEnvironmentSafe_var rfl) .nil)

/-- The `matchAll` in the real list matcher join clause is safe once two
genuinely dynamic facts are supplied separately: the recursive self value is
safe to apply, and its returned matcher performs a typed search for the exact
join pattern. -/
theorem listSplitTailResults_safe
    (selfCallSafe : TotalPlainFunctionLookupSafe 3 matcherArgument
      (.matcher capability (listType element))
      (listJoinContext element matcherArgument capability))
    (searchSafe : TotalPlainPatternSearchSafe listJoinPattern
      (listType element) capability
      [listType element, listType element]
      (listJoinContext element matcherArgument capability)) :
    TotalPlainEnvironmentSafe
      TypePM.Source.Paper1Programs.listSplitTailResults
      (splitResultsType element)
      (listJoinContext element matcherArgument capability) := by
  rw [listSplitTailResults_eq]
  have matcherSafe : TotalPlainEnvironmentSafe
      (.app (.var 3) (.var 2))
      (.matcher capability (listType element))
      (listJoinContext element matcherArgument capability) := by
    exact totalPlainEnvironmentSafe_app
      (totalPlainFunctionEnvironmentSafe_var selfCallSafe)
      (totalPlainEnvironmentSafe_var rfl)
  simpa [splitResultsType, listType] using
    totalPlainEnvironmentSafe_matchAll
      (totalPlainEnvironmentSafe_var (index := 1) rfl)
      matcherSafe searchSafe
      (listSplitBody_safe element matcherArgument capability)

private def putCurrentBody : Source.Expr :=
  .letE (.prim PrimOp.pairSecond [.var 0])
    (.letE (.prim PrimOp.pairFirst [.var 1])
      (.tuple [
        .ctor DataCtor.cons [.var 4, .var 0],
        .var 1]))

private theorem putCurrentBody_typed
    (element matcherArgument : Ty) (capability : Cap) :
    TotalRecursiveClosureBodyTyping
      (splitPairType element :: splitResultsType element ::
        listJoinContext element matcherArgument capability)
      putCurrentBody (splitPairType element) := by
  let closureContext := splitResultsType element ::
    listJoinContext element matcherArgument capability
  let lambdaContext := splitPairType element :: closureContext
  let afterSecond := listType element :: lambdaContext
  let afterFirst := listType element :: afterSecond
  have pairArgument : RuntimeTyping (.var 0) (splitPairType element)
      lambdaContext := .var rfl
  have secondProjection : RuntimeTyping
      (.prim PrimOp.pairSecond [.var 0]) (listType element)
      lambdaContext := .pairSecond pairArgument
  have pairAfterSecond : RuntimeTyping (.var 1) (splitPairType element)
      afterSecond := .var rfl
  have firstProjection : RuntimeTyping
      (.prim PrimOp.pairFirst [.var 1]) (listType element)
      afterSecond := .pairFirst pairAfterSecond
  have currentHead : RuntimeTyping (.var 4) element afterFirst := .var rfl
  have prefixTyped : RuntimeTyping (.var 0) (listType element) afterFirst :=
    .var rfl
  have suffixTyped : RuntimeTyping (.var 1) (listType element) afterFirst :=
    .var rfl
  have resultBody : RuntimeTyping
      (.tuple [.ctor DataCtor.cons [.var 4, .var 0], .var 1])
      (splitPairType element) afterFirst := by
    exact .tuple
      (.cons (.listCons currentHead prefixTyped) (.cons suffixTyped .nil))
  have runtimeBody : RuntimeTyping putCurrentBody (splitPairType element)
      lambdaContext := by
    simpa [putCurrentBody, afterFirst, afterSecond] using
      RuntimeTyping.letE secondProjection
        (RuntimeTyping.letE firstProjection resultBody)
  exact .expression (.core (.core (by
    simpa [lambdaContext, closureContext] using runtimeBody)))

private theorem putCurrentBody_safe
    (element matcherArgument : Ty) (capability : Cap) :
    TotalPlainEnvironmentSafe putCurrentBody (splitPairType element)
      (splitPairType element :: splitResultsType element ::
        listJoinContext element matcherArgument capability) := by
  apply totalPlainEnvironmentSafe_letE
  · exact totalPlainEnvironmentSafe_pairSecond
      (totalPlainEnvironmentSafe_var rfl)
  · apply totalPlainEnvironmentSafe_letE
    · exact totalPlainEnvironmentSafe_pairFirst
        (totalPlainEnvironmentSafe_var (index := 1) rfl)
    · apply totalPlainEnvironmentSafe_tuple
      exact .cons
        (totalPlainEnvironmentSafe_listCons
          (totalPlainEnvironmentSafe_var (index := 4) rfl)
          (totalPlainEnvironmentSafe_var rfl))
        (.cons (totalPlainEnvironmentSafe_var (index := 1) rfl) .nil)

private theorem putCurrentAtPrefixEnd_functionSafe
    (element matcherArgument : Ty) (capability : Cap) :
    TotalPlainFunctionEnvironmentSafe
      TypePM.Source.Paper1Programs.putCurrentAtPrefixEnd
      (splitPairType element) (splitPairType element)
      (splitResultsType element ::
        listJoinContext element matcherArgument capability) := by
  simpa [TypePM.Source.Paper1Programs.putCurrentAtPrefixEnd,
    Source.Expr.pairDestructuringLambda, putCurrentBody] using
    totalPlainFunctionEnvironmentSafe_lam
      (putCurrentBody_typed element matcherArgument capability)
      (putCurrentBody_safe element matcherArgument capability)

private theorem listJoinBase_safe
    (element matcherArgument : Ty) (capability : Cap) :
    TotalPlainEnvironmentSafe
      (TypePM.Source.Paper1Programs.sourceList
        [.tuple [TypePM.Source.Paper1Programs.sourceList [],
          .ctor DataCtor.cons [.var 1, .var 2]]])
      (splitResultsType element)
      (splitResultsType element ::
        listJoinContext element matcherArgument capability) := by
  simp only [TypePM.Source.Paper1Programs.sourceList]
  apply totalPlainEnvironmentSafe_listCons
  · apply totalPlainEnvironmentSafe_tuple
    exact .cons totalPlainEnvironmentSafe_listNil
      (.cons
        (totalPlainEnvironmentSafe_listCons
          (totalPlainEnvironmentSafe_var (index := 1) rfl)
          (totalPlainEnvironmentSafe_var (index := 2) rfl))
        .nil)
  · exact totalPlainEnvironmentSafe_listNil

/-- All non-recursive structure of the real `listJoinConsBody` is now
discharged.  The only explicit dynamic premises are the recursive self-call
and the exact join-pattern search performed by the matcher it returns. -/
theorem listJoinConsBody_safe
    (selfCallSafe : TotalPlainFunctionLookupSafe 3 matcherArgument
      (.matcher capability (listType element))
      (listJoinContext element matcherArgument capability))
    (searchSafe : TotalPlainPatternSearchSafe listJoinPattern
      (listType element) capability
      [listType element, listType element]
      (listJoinContext element matcherArgument capability)) :
    TotalPlainEnvironmentSafe
      TypePM.Source.Paper1Programs.listJoinConsBody
      (splitResultsType element)
      (listJoinContext element matcherArgument capability) := by
  rw [show TypePM.Source.Paper1Programs.listJoinConsBody =
      .letE TypePM.Source.Paper1Programs.listSplitTailResults
        (.prim PrimOp.append
          [TypePM.Source.Paper1Programs.sourceList
            [.tuple [TypePM.Source.Paper1Programs.sourceList [],
              .ctor DataCtor.cons [.var 1, .var 2]]],
            .prim PrimOp.map
              [TypePM.Source.Paper1Programs.putCurrentAtPrefixEnd, .var 0]])
      by rfl]
  apply totalPlainEnvironmentSafe_letE
  · exact listSplitTailResults_safe selfCallSafe searchSafe
  · apply totalPlainEnvironmentSafe_append
    · exact listJoinBase_safe element matcherArgument capability
    · exact totalPlainEnvironmentSafe_map
        (putCurrentAtPrefixEnd_functionSafe element matcherArgument capability)
        (totalPlainEnvironmentSafe_var rfl)

theorem listJoinConsBody_neverStuck
    (selfCallSafe : TotalPlainFunctionLookupSafe 3 matcherArgument
      (.matcher capability (listType element))
      (listJoinContext element matcherArgument capability))
    (searchSafe : TotalPlainPatternSearchSafe listJoinPattern
      (listType element) capability
      [listType element, listType element]
      (listJoinContext element matcherArgument capability))
    (environmentTyped : TotalPlainEnvironmentTyping environment
      (listJoinContext element matcherArgument capability))
    (fuel : Nat) :
    (evalFuel fuel environment
      TypePM.Source.Paper1Programs.listJoinConsBody).NotStuck :=
  (listJoinConsBody_safe selfCallSafe searchSafe fuel environment
    environmentTyped).notStuck

end TypePM.TotalPlainClosureSafetyRegression
