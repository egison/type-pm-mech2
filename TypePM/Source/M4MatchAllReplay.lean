import TypePM.Source.M4StructuralReplay
import TypePM.Source.M4PatternReplay

/-!
# Executable replay for M4 multi-result matching

The four expression positions of `matchAll` are replayed in source order.
Child coherence aligns their finishing supplies when a recursive `letE`
chooses a different principal representative.  Pattern replay additionally
preserves the binding interface used to type and execute the body.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source

/-- Multi-result matching preserves non-exact fuel-local replay. -/
theorem matchAllM4FuelReplayStep : MatchAllM4FuelReplayStep := by
  intro target matcher pattern body coherent replay
  intro signature fuel context supply next generated derivation
    signatureWellFormed wellFormed
  cases fuel with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel =>
      simp only [ElaboratesFuel] at derivation
      have tracked := M4FreshRenaming.MatchAllElaboratesUsing.trackContextSupport
        signatureWellFormed wellFormed derivation
      cases tracked with
      | @mk generatedTarget afterTarget generatedPattern afterPattern
          generatedMatcher afterMatcher generatedBody finish targetDerivation
          patternDerivation matcherDerivation bodyDerivation =>
          obtain ⟨computedTarget, computedAfterTarget, targetExecutable,
              computedTargetDerivation⟩ :=
            replay target (by
              simp only [Expr.complexity_matchAll]
              omega) targetDerivation.2 signatureWellFormed targetDerivation.1
          obtain ⟨targetComparison⟩ := coherent target (by
            simp only [Expr.complexity_matchAll]
            omega) signatureWellFormed targetDerivation.1 targetDerivation.2
              computedTargetDerivation
          cases targetComparison.next_eq
          have emptyArguments : VariablesSupportProvenance context supply
              afterTarget (dualUnificationVars []) := by
            intro candidate member
            simp [dualUnificationVars] at member
          have emptyBindings : VariablesSupportProvenance context supply
              afterTarget (Ty.unificationVarsList []) := by
            intro candidate member
            simp [Ty.unificationVarsList] at member
          have rawPatternDerivation : PatternElaboratesUsing
              (ElaboratesFuel signature fuel) signature context [] pattern []
                afterTarget generatedPattern afterPattern :=
            PatternElaboratesUsing.map (fun child => child.2)
              patternDerivation
          obtain ⟨computedPattern, computedAfterPattern, patternExecutable,
              computedPatternDerivation, patternNextEquality,
              patternBindingsEquality⟩ :=
            executablePatternFuelReplay coherent replay signatureWellFormed
              wellFormed emptyArguments emptyBindings
              targetDerivation.2.supply_le_next (by
                simp only [Expr.complexity_matchAll]
                omega) rawPatternDerivation
          cases patternNextEquality
          rw [patternBindingsEquality] at bodyDerivation
          obtain ⟨computedMatcher, computedAfterMatcher, matcherExecutable,
              computedMatcherDerivation⟩ :=
            replay matcher (by
              simp only [Expr.complexity_matchAll]
              omega) matcherDerivation.2 signatureWellFormed
                matcherDerivation.1
          obtain ⟨matcherComparison⟩ := coherent matcher (by
            simp only [Expr.complexity_matchAll]
            omega) signatureWellFormed matcherDerivation.1 matcherDerivation.2
              computedMatcherDerivation
          cases matcherComparison.next_eq
          obtain ⟨computedBody, computedNext, bodyExecutable,
              computedBodyDerivation⟩ :=
            replay body (by
              simp only [Expr.complexity_matchAll]
              omega) bodyDerivation.2 signatureWellFormed bodyDerivation.1
          have targetExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel context target supply =
                some (computedTarget, afterTarget) := by
            simpa [M4.elaborateFuel] using targetExecutable
          have patternExecutableUsing :
              elaboratePatternUsing
                  (M4.elaborateFuelUsing unify signature fuel) signature context
                  [] pattern [] afterTarget =
                some (computedPattern, afterPattern) := by
            simpa [M4.elaborateFuel] using patternExecutable
          have matcherExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel context matcher
                  afterPattern = some (computedMatcher, afterMatcher) := by
            simpa [M4.elaborateFuel] using matcherExecutable
          have bodyExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel
                  (Pattern.extendContext computedPattern.bindings context) body
                  afterMatcher = some (computedBody, computedNext) := by
            simpa [M4.elaborateFuel] using bodyExecutable
          exact ⟨_, computedNext,
            by simp [M4.elaborateFuel, M4.elaborateFuelUsing,
              elaborateMatchAllUsing, targetExecutableUsing,
              patternExecutableUsing, matcherExecutableUsing,
              bodyExecutableUsing],
            .mk computedTargetDerivation computedPatternDerivation
              computedMatcherDerivation computedBodyDerivation⟩

end TypePM.Source.M4.CompletenessArchitecture
