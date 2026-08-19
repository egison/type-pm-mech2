import TypePM.Runtime.Values

/-!
# Regressions for complete runtime values

These examples cover every value constructor, newest-first lookup, matcher
cursor order, Paper-1 structural equality, and the bridge to `GroundValue`.
They do not claim expression evaluation, matcher dispatch, or search.
-/

namespace TypePM.Runtime.ValuesRegression

open TypePM.Runtime
open Value GroundValue

private def emptyClauses : List Source.MatcherClause := []

private def oneClause : Source.MatcherClause :=
  .mk .hole .something [.mk .var (.var 0)]

private def secondClause : Source.MatcherClause :=
  .mk .wild .something [.mk .wild (.lit 0)]

private def twoClauses : List Source.MatcherClause :=
  [oneClause, secondClause]

private def listValue (items : List Value) : Value :=
  items.foldr
    (fun head tail => .data DataCtor.cons [head, tail])
    (.data DataCtor.nil [])

theorem every_runtime_constructor_is_available :
    let environment : ValueEnvironment := [.int 7]
    let values : List Value :=
      [ .int 1,
        .data DataCtor.nil [],
        .tuple [.int 1, .int 2],
        plainClosure environment (.var 0),
        recursiveClosure environment (.var 1),
        matcherClosure environment emptyClauses,
        .something ]
    values.length = 7 := by
  rfl

theorem newest_first_value_lookup_exact :
    ([Value.int 30, .int 20, .int 10] : ValueEnvironment)[1]? =
      some (.int 20) := by
  rfl

theorem newest_first_value_lookup_relational :
    Lookup ([Value.int 30, .int 20, .int 10] : ValueEnvironment) 2
      (.int 10) := by
  exact (Value.lookup_iff_getElem? _ _ _).mpr rfl

theorem fresh_matcher_keeps_both_clause_lists :
    matcherClosure [.int 9] twoClauses =
      .matcherV [.int 9] twoClauses twoClauses := by
  rfl

theorem matcher_advance_is_source_ordered :
    advanceMatcher (matcherClosure [.int 9] twoClauses) =
      some (.matcherV [.int 9] twoClauses [secondClause]) := by
  rfl

theorem matcher_cursor_initially_valid :
    (matcherClosure [.int 9] twoClauses).MatcherCursorValid := by
  exact matcherClosure_cursorValid _ _

theorem matcher_cursor_remains_valid_after_advance
    {next : Value}
    (advanced :
      advanceMatcher (matcherClosure [.int 9] twoClauses) = some next) :
    next.MatcherCursorValid := by
  exact advanceMatcher_cursorValid
    (matcherClosure_cursorValid _ _) advanced

theorem integer_structural_equality_succeeds :
    structuralEq (.int 42) (.int 42) = true := by
  rfl

theorem constructor_structural_equality_succeeds :
    structuralEq (listValue [.int 1, .int 2])
      (listValue [.int 1, .int 2]) = true := by
  rfl

theorem constructor_structural_mismatch_fails :
    structuralEq (listValue [.int 1, .int 2])
      (listValue [.int 1, .int 3]) = false := by
  rfl

theorem tuple_arity_mismatch_fails :
    structuralEq (.tuple [.int 1]) (.tuple [.int 1, .int 2]) = false := by
  rfl

/-- Paper-1 structural equality is false on a closure even when both sides
are the same Lean term. -/
theorem closure_is_not_structurally_equal_to_itself :
    let closure := plainClosure [] (.var 0)
    structuralEq closure closure = false := by
  rfl

/-- Matcher values are likewise deliberately outside structural equality. -/
theorem matcher_is_not_structurally_equal_to_itself :
    let matcher := matcherClosure [] emptyClauses
    structuralEq matcher matcher = false := by
  rfl

/-- `something` is a matcher capability, not a first-order equality witness. -/
theorem something_is_not_structurally_equal_to_itself :
    structuralEq .something .something = false := by
  rfl

private def groundExample : GroundValue :=
  tupleValue
    [.int 4, buildList [.int 5, dataValue DataCtor.nil []]]

theorem ground_embedding_exact :
    ofGround groundExample =
      .tuple
        [ .int 4,
          .data DataCtor.cons
            [ .int 5,
              .data DataCtor.cons
                [.data DataCtor.nil [], .data DataCtor.nil []] ] ] := by
  rfl

theorem ground_roundtrip_exact :
    toGround? (ofGround groundExample) = some groundExample := by
  exact toGround?_ofGround groundExample

theorem ground_embedding_is_injective :
    ofGround (buildList [.int 1]) = ofGround (buildList [.int 2]) → False := by
  intro equal
  have groundEqual := ofGround_injective equal
  cases groundEqual

theorem closure_projection_is_rejected :
    toGround? (plainClosure [] (.var 0)) = none := by
  rfl

theorem nested_matcher_projection_is_rejected :
    toGround?
      (.data DataCtor.cons
        [matcherClosure [] emptyClauses, .data DataCtor.nil []]) = none := by
  rfl

end TypePM.Runtime.ValuesRegression
