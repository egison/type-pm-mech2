import TypePM.Source.Syntax

/-!
# Primitive pattern-pattern dispatch

A matcher clause first compares its `PPat` header with the user's source
pattern.  This module implements the syntax-only part of that dispatch:
holes retain their source patterns, captures retain the expressions inside
value patterns, and constructor fields are traversed left to right.  Capture
expressions are evaluated later by the expression evaluator under the
matcher's saved environment.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Syntax extracted from a successful primitive pattern-pattern match. -/
structure PatternDispatch where
  holes : List Pattern
  captures : List Expr
deriving Repr

namespace PatternDispatch

def empty : PatternDispatch := ⟨[], []⟩

def append (left right : PatternDispatch) : PatternDispatch :=
  ⟨left.holes ++ right.holes, left.captures ++ right.captures⟩

end PatternDispatch

mutual

  /-- Match one matcher-clause header against one source pattern. -/
  def inspectPatternPattern : PPat → Pattern → Option PatternDispatch
    | .hole, pattern => some ⟨[pattern], []⟩
    | .wild, .wild => some .empty
    | .wild, _ => none
    | .capture, .value expression => some ⟨[], [expression]⟩
    | .capture, _ => none
    | .ctor expected fields, .ctor actual patterns =>
        if expected = actual then
          inspectPatternPatterns fields patterns
        else
          none
    | .ctor _ _, _ => none

  /-- Match equal-length field sequences in left-to-right source order. -/
  def inspectPatternPatterns :
      List PPat → List Pattern → Option PatternDispatch
    | [], [] => some .empty
    | header :: headers, pattern :: patterns => do
        let headResult ← inspectPatternPattern header pattern
        let tailResult ← inspectPatternPatterns headers patterns
        pure (headResult.append tailResult)
    | _, _ => none

end

mutual

  /-- Independent structural specification of primitive pattern dispatch. -/
  inductive PatternPatternMatches :
      PPat → Pattern → PatternDispatch → Prop where
    | hole : PatternPatternMatches .hole pattern ⟨[pattern], []⟩
    | wild : PatternPatternMatches .wild .wild .empty
    | capture :
        PatternPatternMatches .capture (.value expression)
          ⟨[], [expression]⟩
    | ctor
        (fields : PatternPatternsMatch headers patterns result) :
        PatternPatternMatches (.ctor constructor headers)
          (.ctor constructor patterns) result

  /-- Independent structural specification of field-sequence dispatch. -/
  inductive PatternPatternsMatch :
      List PPat → List Pattern → PatternDispatch → Prop where
    | nil : PatternPatternsMatch [] [] .empty
    | cons
        (head : PatternPatternMatches header pattern headResult)
        (tail : PatternPatternsMatch headers patterns tailResult) :
        PatternPatternsMatch (header :: headers) (pattern :: patterns)
          (headResult.append tailResult)

end

mutual

  theorem inspectPatternPattern_sound
      {header : PPat} {pattern : Pattern} {result : PatternDispatch}
      (success : inspectPatternPattern header pattern = some result) :
      PatternPatternMatches header pattern result := by
    cases header with
    | hole =>
        cases success
        exact .hole
    | wild =>
        cases pattern <;> simp only [inspectPatternPattern] at success
        case wild =>
          cases success
          exact .wild
        all_goals cases success
    | capture =>
        cases pattern <;> simp only [inspectPatternPattern] at success
        case value expression =>
          cases success
          exact .capture
        all_goals cases success
    | ctor expected fields =>
        cases pattern <;> simp only [inspectPatternPattern] at success
        case ctor actual patterns =>
          split at success
          next equal =>
            subst actual
            exact .ctor (inspectPatternPatterns_sound success)
          next unequal => contradiction
        all_goals cases success

  theorem inspectPatternPatterns_sound
      {headers : List PPat} {patterns : List Pattern}
      {result : PatternDispatch}
      (success : inspectPatternPatterns headers patterns = some result) :
      PatternPatternsMatch headers patterns result := by
    cases headers with
    | nil =>
        cases patterns with
        | nil =>
            cases success
            exact .nil
        | cons pattern patterns =>
            simp [inspectPatternPatterns] at success
    | cons header headers =>
        cases patterns with
        | nil => simp [inspectPatternPatterns] at success
        | cons pattern patterns =>
            cases headSuccess : inspectPatternPattern header pattern with
            | none =>
                simp [inspectPatternPatterns, headSuccess] at success
            | some headResult =>
                cases tailSuccess : inspectPatternPatterns headers patterns with
                | none =>
                    simp [inspectPatternPatterns, headSuccess, tailSuccess]
                      at success
                | some tailResult =>
                    simp [inspectPatternPatterns, headSuccess, tailSuccess]
                      at success
                    subst result
                    exact .cons (inspectPatternPattern_sound headSuccess)
                      (inspectPatternPatterns_sound tailSuccess)

end

mutual

  theorem PatternPatternMatches.complete
      {header : PPat} {pattern : Pattern} {result : PatternDispatch}
      (derivation : PatternPatternMatches header pattern result) :
      inspectPatternPattern header pattern = some result := by
    cases derivation with
    | hole | wild | capture => rfl
    | ctor fields =>
        simp [inspectPatternPattern, PatternPatternsMatch.complete fields]

  theorem PatternPatternsMatch.complete
      {headers : List PPat} {patterns : List Pattern}
      {result : PatternDispatch}
      (derivation : PatternPatternsMatch headers patterns result) :
      inspectPatternPatterns headers patterns = some result := by
    cases derivation with
    | nil => rfl
    | cons head tail =>
        simp [inspectPatternPatterns, PatternPatternMatches.complete head,
          PatternPatternsMatch.complete tail]

end

theorem inspectPatternPattern_eq_some_iff
    {header : PPat} {pattern : Pattern} {result : PatternDispatch} :
    inspectPatternPattern header pattern = some result ↔
      PatternPatternMatches header pattern result :=
  ⟨inspectPatternPattern_sound, PatternPatternMatches.complete⟩

mutual

  /-- Runtime extraction agrees with the static hole and capture counts. -/
  theorem PatternPatternMatches.counts
      {header : PPat} {pattern : Pattern} {result : PatternDispatch}
      (derivation : PatternPatternMatches header pattern result) :
      result.holes.length = header.holeCount ∧
        result.captures.length = header.captureCount := by
    cases derivation with
    | hole | wild | capture => simp [PPat.holeCount, PPat.captureCount,
        PatternDispatch.empty]
    | ctor fields =>
        simpa [PPat.holeCount, PPat.captureCount] using
          PatternPatternsMatch.counts fields

  theorem PatternPatternsMatch.counts
      {headers : List PPat} {patterns : List Pattern}
      {result : PatternDispatch}
      (derivation : PatternPatternsMatch headers patterns result) :
      result.holes.length = (headers.map PPat.holeCount).sum ∧
        result.captures.length = (headers.map PPat.captureCount).sum := by
    cases derivation with
    | nil => simp [PatternDispatch.empty]
    | cons head tail =>
        have headCounts := PatternPatternMatches.counts head
        have tailCounts := PatternPatternsMatch.counts tail
        constructor <;>
          simp [PatternDispatch.append, headCounts, tailCounts]

end

end TypePM.Runtime
