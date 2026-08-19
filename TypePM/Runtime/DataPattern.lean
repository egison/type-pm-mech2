import TypePM.Runtime.GroundValue
import TypePM.Source.MatcherPattern

/-!
# Ground data-pattern matching

Matcher-clause arms use `Source.DPat` to inspect the result of a clause body.
This module gives that first-order fragment an executable matcher and an
independent relational specification.  Bindings are returned in left-to-right
source order; constructor and tuple arities must agree exactly.
-/

namespace TypePM.Runtime

open TypePM.Source

mutual

  /-- Match one data pattern against a closed ground value. -/
  def matchDataPattern : DPat → GroundValue → Option (List GroundValue)
    | .var, value => some [value]
    | .wild, _ => some []
    | .ctor expected fields, .data actual arguments =>
        if expected = actual then
          matchDataPatterns fields arguments.toList
        else
          none
    | .tuple patterns, .tuple values =>
        matchDataPatterns patterns values.toList
    | _, _ => none

  /-- Match equal-length sequences and concatenate bindings in source order. -/
  def matchDataPatterns :
      List DPat → List GroundValue → Option (List GroundValue)
    | [], [] => some []
    | pattern :: patterns, value :: values => do
        let headBindings ← matchDataPattern pattern value
        let tailBindings ← matchDataPatterns patterns values
        pure (headBindings ++ tailBindings)
    | _, _ => none

end

mutual

  /-- Relational specification of one successful data-pattern match. -/
  inductive DataPatternMatches :
      DPat → GroundValue → List GroundValue → Prop where
    | var : DataPatternMatches .var value [value]
    | wild : DataPatternMatches .wild value []
    | ctor
        (fields : DataPatternsMatch patterns arguments.toList bindings) :
        DataPatternMatches (.ctor constructor patterns)
          (.data constructor arguments) bindings
    | tuple
        (items : DataPatternsMatch patterns values.toList bindings) :
        DataPatternMatches (.tuple patterns) (.tuple values) bindings

  /-- Relational specification of equal-length sequence matching. -/
  inductive DataPatternsMatch :
      List DPat → List GroundValue → List GroundValue → Prop where
    | nil : DataPatternsMatch [] [] []
    | cons
        (head : DataPatternMatches pattern value headBindings)
        (tail : DataPatternsMatch patterns values tailBindings) :
        DataPatternsMatch (pattern :: patterns) (value :: values)
          (headBindings ++ tailBindings)

end

mutual

  /-- Executable success produces the corresponding structural derivation. -/
  theorem matchDataPattern_sound
      {pattern : DPat} {value : GroundValue} {bindings : List GroundValue}
      (success : matchDataPattern pattern value = some bindings) :
      DataPatternMatches pattern value bindings := by
    cases pattern <;> cases value <;>
      simp only [matchDataPattern] at success
    case var.int value | var.data constructor arguments |
        var.tuple values =>
      cases success
      exact .var
    case wild.int value | wild.data constructor arguments |
        wild.tuple values =>
      cases success
      exact .wild
    case ctor.data expected patterns actual arguments =>
      split at success
      next equal =>
        subst actual
        exact .ctor (matchDataPatterns_sound success)
      next unequal => contradiction
    case ctor.int => cases success
    case ctor.tuple => cases success
    case tuple.tuple patterns values =>
      exact .tuple (matchDataPatterns_sound success)
    case tuple.int => cases success
    case tuple.data => cases success

  /-- Sequence execution preserves the structural binding order. -/
  theorem matchDataPatterns_sound
      {patterns : List DPat} {values : List GroundValue}
      {bindings : List GroundValue}
      (success : matchDataPatterns patterns values = some bindings) :
      DataPatternsMatch patterns values bindings := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            cases success
            exact .nil
        | cons value values => simp [matchDataPatterns] at success
    | cons pattern patterns =>
        cases values with
        | nil => simp [matchDataPatterns] at success
        | cons value values =>
            cases headSuccess : matchDataPattern pattern value with
            | none => simp [matchDataPatterns, headSuccess] at success
            | some headBindings =>
                cases tailSuccess : matchDataPatterns patterns values with
                | none =>
                    simp [matchDataPatterns, headSuccess, tailSuccess] at success
                | some tailBindings =>
                    simp [matchDataPatterns, headSuccess, tailSuccess] at success
                    subst bindings
                    exact .cons (matchDataPattern_sound headSuccess)
                      (matchDataPatterns_sound tailSuccess)

end

mutual

  /-- Every structural data-pattern derivation is executed successfully. -/
  theorem DataPatternMatches.complete
      {pattern : DPat} {value : GroundValue} {bindings : List GroundValue}
      (derivation : DataPatternMatches pattern value bindings) :
      matchDataPattern pattern value = some bindings := by
    cases derivation with
    | var => rfl
    | wild => rfl
    | ctor fields =>
        simp [matchDataPattern, DataPatternsMatch.complete fields]
    | tuple items =>
        exact DataPatternsMatch.complete items

  /-- Every structural sequence derivation is executed successfully. -/
  theorem DataPatternsMatch.complete
      {patterns : List DPat} {values : List GroundValue}
      {bindings : List GroundValue}
      (derivation : DataPatternsMatch patterns values bindings) :
      matchDataPatterns patterns values = some bindings := by
    cases derivation with
    | nil => rfl
    | cons head tail =>
        simp [matchDataPatterns, DataPatternMatches.complete head,
          DataPatternsMatch.complete tail]

end

/-- Executable and relational data-pattern matching agree exactly. -/
theorem matchDataPattern_eq_some_iff
    {pattern : DPat} {value : GroundValue} {bindings : List GroundValue} :
    matchDataPattern pattern value = some bindings ↔
      DataPatternMatches pattern value bindings :=
  ⟨matchDataPattern_sound, DataPatternMatches.complete⟩

mutual

  /-- Successful matching returns exactly the statically counted bindings. -/
  theorem DataPatternMatches.bindings_length
      {pattern : DPat} {value : GroundValue} {bindings : List GroundValue}
      (derivation : DataPatternMatches pattern value bindings) :
      bindings.length = pattern.bindingCount := by
    cases derivation with
    | var | wild => simp [DPat.bindingCount]
    | ctor fields | tuple fields =>
        simpa [DPat.bindingCount] using
          DataPatternsMatch.bindings_length fields

  /-- Sequence matching preserves the sum of the component binding counts. -/
  theorem DataPatternsMatch.bindings_length
      {patterns : List DPat} {values bindings : List GroundValue}
      (derivation : DataPatternsMatch patterns values bindings) :
      bindings.length = (patterns.map DPat.bindingCount).sum := by
    cases derivation with
    | nil => rfl
    | cons head tail =>
        simp [DataPatternMatches.bindings_length head,
          DataPatternsMatch.bindings_length tail]

end

end TypePM.Runtime
