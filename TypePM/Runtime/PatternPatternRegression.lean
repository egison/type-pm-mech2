import TypePM.Runtime.PatternPattern
import TypePM.Source.M4MatcherPatternRegression

/-!
# Primitive pattern-pattern dispatch regressions

Each of the seven multiset matcher headers is exercised independently at the
syntax-dispatch boundary.  These are not yet complete matcher-clause or
`matchAll` execution tests: captured expressions still have to be evaluated,
and the selected arm body still has to produce decompositions.
-/

namespace TypePM.Runtime.PatternPatternRegression

open TypePM.Source
open TypePM.Source.M4MatcherPatternRegression

def oneExpr : Expr := .lit 1

def nilPattern : Pattern := .ctor PatternCtor.nil []

def consPattern : Pattern :=
  .ctor PatternCtor.cons [.var, .wild]

def valueConsPattern : Pattern :=
  .ctor PatternCtor.cons [.value oneExpr, .var]

def joinPattern : Pattern :=
  .ctor PatternCtor.join [.var, .wild]

theorem nil_header_dispatch_exact :
    inspectPatternPattern nilHeader nilPattern =
      some ⟨[], []⟩ := by
  rfl

theorem head_only_header_dispatch_exact :
    inspectPatternPattern headOnlyHeader consPattern =
      some ⟨[.var], []⟩ := by
  rfl

theorem value_cons_header_dispatch_exact :
    inspectPatternPattern valueConsHeader valueConsPattern =
      some ⟨[.var], [oneExpr]⟩ := by
  rfl

theorem general_cons_header_dispatch_exact :
    inspectPatternPattern generalConsHeader consPattern =
      some ⟨[.var, .wild], []⟩ := by
  rfl

theorem join_header_dispatch_exact :
    inspectPatternPattern joinHeader joinPattern =
      some ⟨[.var, .wild], []⟩ := by
  rfl

theorem whole_value_header_dispatch_exact :
    inspectPatternPattern wholeValueHeader (.value oneExpr) =
      some ⟨[], [oneExpr]⟩ := by
  rfl

theorem catch_all_header_dispatches_once :
    inspectPatternPattern catchAllHeader consPattern =
      some ⟨[consPattern], []⟩ := by
  rfl

theorem constructor_mismatch_is_failure :
    inspectPatternPattern nilHeader consPattern = none := by
  rfl

theorem constructor_arity_mismatch_is_failure :
    inspectPatternPattern headOnlyHeader
      (.ctor PatternCtor.cons [.var]) = none := by
  rfl

def CountsAgree
    (header : PPat) (result : PatternDispatch) : Prop :=
  result.holes.length = header.holeCount ∧
    result.captures.length = header.captureCount

theorem all_seven_successes_have_static_counts :
    CountsAgree nilHeader ⟨[], []⟩ ∧
      CountsAgree headOnlyHeader ⟨[.var], []⟩ ∧
      CountsAgree valueConsHeader ⟨[.var], [oneExpr]⟩ ∧
      CountsAgree generalConsHeader ⟨[.var, .wild], []⟩ ∧
      CountsAgree joinHeader ⟨[.var, .wild], []⟩ ∧
      CountsAgree wholeValueHeader ⟨[], [oneExpr]⟩ ∧
      CountsAgree catchAllHeader ⟨[consPattern], []⟩ := by
  simp [CountsAgree, nilHeader, headOnlyHeader, valueConsHeader,
    generalConsHeader, joinHeader, wholeValueHeader, catchAllHeader,
    PPat.holeCount, PPat.captureCount]

end TypePM.Runtime.PatternPatternRegression
