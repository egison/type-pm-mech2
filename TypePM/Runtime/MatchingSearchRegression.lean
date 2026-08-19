import TypePM.Runtime.MatchingSearch

/-!
# Matching-state and ordered-search regressions
-/

namespace TypePM.Runtime.MatchingSearchRegression

open TypePM.Source

def literalEval (_ : ValueEnvironment) : Expr → FuelResult Value
  | .lit value => .ok (.int value)
  | _ => .stuck

def builtinReducer : ValueEnvironment → MatchingAtom →
    FuelResult (DispatchResult AtomReduction) :=
  reduceBuiltinAtom literalEval

def one : Value := .int 1
def two : Value := .int 2

theorem variable_match_search_exact :
    searchMatchingFuel builtinReducer 2
        ⟨[⟨.var, .something, one⟩], [], []⟩ =
      .ok [[one]] := by
  rfl

theorem value_mismatch_returns_no_answers :
    searchMatchingFuel builtinReducer 1
        ⟨[⟨.value (.lit 1), .something, two⟩], [], []⟩ =
      .ok [] := by
  rfl

theorem tuple_work_and_bindings_preserve_runtime_order :
    searchMatchingFuel builtinReducer 4
        ⟨[⟨.tuple [.var, .wild],
            .tuple [.something, .something], .tuple [one, two]⟩],
          [], []⟩ =
      .ok [[one]] := by
  rfl

theorem two_variable_bindings_remain_in_source_order :
    searchMatchingFuel builtinReducer 4
        ⟨[⟨.tuple [.var, .var],
            .tuple [.something, .something], .tuple [one, two]⟩],
          [], []⟩ =
      .ok [[one, two]] := by
  rfl

def lookupEval (environment : ValueEnvironment) : Expr → FuelResult Value
  | .var index =>
      match environment[index]? with
      | some value => .ok value
      | none => .stuck
  | _ => .stuck

def lookupReducer : ValueEnvironment → MatchingAtom →
    FuelResult (DispatchResult AtomReduction) :=
  reduceBuiltinAtom lookupEval

theorem later_value_pattern_reads_earlier_binding :
    searchMatchingFuel lookupReducer 3
        ⟨[⟨.var, .something, one⟩,
            ⟨.value (.var 0), .something, one⟩], [], []⟩ =
      .ok [[one]] := by
  rfl

/-- Two equal-position branches remain two answers; search never deduplicates. -/
def duplicateReducer (_ : ValueEnvironment) (_ : MatchingAtom) :
    FuelResult (DispatchResult AtomReduction) :=
  .ok (.hit ⟨[[], []], [one]⟩)

theorem duplicate_branches_remain_distinct :
    searchMatchingFuel duplicateReducer 3
        ⟨[⟨.wild, .something, one⟩], [], []⟩ =
      .ok [[one], [one]] := by
  rfl

def missingReducer (_ : ValueEnvironment) (_ : MatchingAtom) :
    FuelResult (DispatchResult AtomReduction) :=
  .ok .miss

theorem unhandled_atom_is_stuck :
    stepMatchingState missingReducer
        ⟨[⟨.wild, .something, one⟩], [], []⟩ =
      .stuck := by
  rfl

def failureReducer (_ : ValueEnvironment) (_ : MatchingAtom) :
    FuelResult (DispatchResult AtomReduction) :=
  .ok (.hit .failure)

theorem normal_failure_is_not_stuck :
    searchMatchingFuel failureReducer 1
        ⟨[⟨.wild, .something, one⟩], [], []⟩ =
      .ok [] := by
  rfl

theorem successful_search_has_depth_first_derivation :
    DepthFirst (stepMatchingState builtinReducer)
      [⟨[⟨.var, .something, one⟩], [], []⟩] [[one]] := by
  exact searchMatchingFuel_sound _ variable_match_search_exact

end TypePM.Runtime.MatchingSearchRegression
