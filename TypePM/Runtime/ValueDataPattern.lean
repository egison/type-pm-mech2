import TypePM.Runtime.Values
import TypePM.Source.MatcherPattern

/-!
# Runtime-value data-pattern matching

Data-pattern variables and wildcards may receive any runtime value, including
closures and matcher values.  Constructor and tuple patterns remain strictly
structural and require exact arity.  This is the full-value counterpart of
the earlier closed-ground matcher.
-/

namespace TypePM.Runtime

open TypePM.Source

mutual

  def matchValueDataPattern : DPat → Value → Option (List Value)
    | .var, value => some [value]
    | .wild, _ => some []
    | .ctor expected fields, .data actual arguments =>
        if expected = actual then
          matchValueDataPatterns fields arguments
        else
          none
    | .tuple patterns, .tuple values =>
        matchValueDataPatterns patterns values
    | _, _ => none

  def matchValueDataPatterns :
      List DPat → List Value → Option (List Value)
    | [], [] => some []
    | pattern :: patterns, value :: values => do
        let headBindings ← matchValueDataPattern pattern value
        let tailBindings ← matchValueDataPatterns patterns values
        pure (headBindings ++ tailBindings)
    | _, _ => none

end

mutual

  inductive ValueDataPatternMatches :
      DPat → Value → List Value → Prop where
    | var : ValueDataPatternMatches .var value [value]
    | wild : ValueDataPatternMatches .wild value []
    | ctor
        (fields : ValueDataPatternsMatch patterns arguments bindings) :
        ValueDataPatternMatches (.ctor constructor patterns)
          (.data constructor arguments) bindings
    | tuple
        (items : ValueDataPatternsMatch patterns values bindings) :
        ValueDataPatternMatches (.tuple patterns) (.tuple values) bindings

  inductive ValueDataPatternsMatch :
      List DPat → List Value → List Value → Prop where
    | nil : ValueDataPatternsMatch [] [] []
    | cons
        (head : ValueDataPatternMatches pattern value headBindings)
        (tail : ValueDataPatternsMatch patterns values tailBindings) :
        ValueDataPatternsMatch (pattern :: patterns) (value :: values)
          (headBindings ++ tailBindings)

end

mutual

  theorem matchValueDataPattern_sound
      {pattern : DPat} {value : Value} {bindings : List Value}
      (success : matchValueDataPattern pattern value = some bindings) :
      ValueDataPatternMatches pattern value bindings := by
    cases pattern <;> cases value <;>
      simp only [matchValueDataPattern] at success
    case var.int | var.data | var.tuple | var.closure | var.matcherV |
        var.something =>
      cases success
      exact .var
    case wild.int | wild.data | wild.tuple | wild.closure | wild.matcherV |
        wild.something =>
      cases success
      exact .wild
    case ctor.data expected patterns actual arguments =>
      split at success
      next equal =>
        subst actual
        exact .ctor (matchValueDataPatterns_sound success)
      next unequal => contradiction
    case tuple.tuple patterns values =>
      exact .tuple (matchValueDataPatterns_sound success)
    all_goals cases success

  theorem matchValueDataPatterns_sound
      {patterns : List DPat} {values bindings : List Value}
      (success : matchValueDataPatterns patterns values = some bindings) :
      ValueDataPatternsMatch patterns values bindings := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            cases success
            exact .nil
        | cons value values =>
            simp [matchValueDataPatterns] at success
    | cons pattern patterns =>
        cases values with
        | nil => simp [matchValueDataPatterns] at success
        | cons value values =>
            cases headSuccess : matchValueDataPattern pattern value with
            | none =>
                simp [matchValueDataPatterns, headSuccess] at success
            | some headBindings =>
                cases tailSuccess : matchValueDataPatterns patterns values with
                | none =>
                    simp [matchValueDataPatterns, headSuccess, tailSuccess]
                      at success
                | some tailBindings =>
                    simp [matchValueDataPatterns, headSuccess, tailSuccess]
                      at success
                    subst bindings
                    exact .cons (matchValueDataPattern_sound headSuccess)
                      (matchValueDataPatterns_sound tailSuccess)

end

mutual

  theorem ValueDataPatternMatches.complete
      {pattern : DPat} {value : Value} {bindings : List Value}
      (derivation : ValueDataPatternMatches pattern value bindings) :
      matchValueDataPattern pattern value = some bindings := by
    cases derivation with
    | var | wild => rfl
    | ctor fields =>
        simp [matchValueDataPattern, ValueDataPatternsMatch.complete fields]
    | tuple items =>
        exact ValueDataPatternsMatch.complete items

  theorem ValueDataPatternsMatch.complete
      {patterns : List DPat} {values bindings : List Value}
      (derivation : ValueDataPatternsMatch patterns values bindings) :
      matchValueDataPatterns patterns values = some bindings := by
    cases derivation with
    | nil => rfl
    | cons head tail =>
        simp [matchValueDataPatterns, ValueDataPatternMatches.complete head,
          ValueDataPatternsMatch.complete tail]

end

theorem matchValueDataPattern_eq_some_iff
    {pattern : DPat} {value : Value} {bindings : List Value} :
    matchValueDataPattern pattern value = some bindings ↔
      ValueDataPatternMatches pattern value bindings :=
  ⟨matchValueDataPattern_sound, ValueDataPatternMatches.complete⟩

mutual

  theorem ValueDataPatternMatches.bindings_length
      {pattern : DPat} {value : Value} {bindings : List Value}
      (derivation : ValueDataPatternMatches pattern value bindings) :
      bindings.length = pattern.bindingCount := by
    cases derivation with
    | var | wild => simp [DPat.bindingCount]
    | ctor fields | tuple fields =>
        simpa [DPat.bindingCount] using
          ValueDataPatternsMatch.bindings_length fields

  theorem ValueDataPatternsMatch.bindings_length
      {patterns : List DPat} {values bindings : List Value}
      (derivation : ValueDataPatternsMatch patterns values bindings) :
      bindings.length = (patterns.map DPat.bindingCount).sum := by
    cases derivation with
    | nil => rfl
    | cons head tail =>
        simp [ValueDataPatternMatches.bindings_length head,
          ValueDataPatternsMatch.bindings_length tail]

end

end TypePM.Runtime
