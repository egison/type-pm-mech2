import TypePM.Source.M4StructuralReplay
import TypePM.Source.M4PatternReplay

/-!
# Executable replay for M4 ordered single-result matching

Recursive expression callbacks may choose different principal representatives.
Replay therefore keeps relational witnesses for the executable results and
uses child coherence only to align the supplies at source-order boundaries.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source
open MatchFirstTyping

/-- Executable replay of the arms after the first arm.  The three surrounding
types are deliberately inputs for the replayed run: they may differ from the
representatives in the original relational derivation. -/
def ExecutableM4MatchFirstTailFuelReplay
    (signature : FrozenSignature) (fuel tailFuel : Nat) (context : Context)
    (targetType matcherType expectedResult : Ty) (arms : List MatchFirstArm)
    (supply : Supply) : Prop :=
  ∃ generated next,
    elaborateTailUsingFuel (M4.elaborateFuel signature fuel) signature context
        targetType matcherType expectedResult tailFuel arms supply =
          some (generated, next) ∧
      TailElaboratesUsing (ElaboratesFuel signature fuel) signature context
        targetType matcherType expectedResult arms supply generated next

/-- Executable replay of a nonempty match-first arm list. -/
def ExecutableM4MatchFirstArmsFuelReplay
    (signature : FrozenSignature) (fuel : Nat) (context : Context)
    (targetType matcherType : Ty) (arms : List MatchFirstArm)
    (supply : Supply) : Prop :=
  ∃ generated next,
    elaborateArmsUsing (M4.elaborateFuel signature fuel) signature context
        targetType matcherType arms supply = some (generated, next) ∧
      ArmsElaborateUsing (ElaboratesFuel signature fuel) signature context
        targetType matcherType arms supply generated next

private theorem list_length_lt_twice_complexity_add_one
    (arms : List MatchFirstArm) :
    arms.length < MatchFirstArm.listComplexity arms * 2 + 1 := by
  induction arms with
  | nil => simp
  | cons arm arms induction =>
      simp only [List.length_cons, MatchFirstArm.listComplexity_cons]
      omega

private theorem executableMatchFirstTailFuelReplay_of_tracked
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel tailFuel : Nat} {context : Context}
    {originalTargetType originalMatcherType originalExpectedResult : Ty}
    {targetType matcherType expectedResult : Ty}
    {arms : List MatchFirstArm} {supply next : Supply}
    {generated : GeneratedTail}
    (signatureWellFormed : signature.WellFormed)
    (bound : MatchFirstArm.listComplexity arms < limit)
    (enoughFuel : arms.length < tailFuel)
    (derivation : TailElaboratesUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) signature context
      originalTargetType originalMatcherType originalExpectedResult arms supply
      generated next) :
    ExecutableM4MatchFirstTailFuelReplay signature fuel tailFuel context
      targetType matcherType expectedResult arms supply := by
  cases tailFuel with
  | zero => simp at enoughFuel
  | succ tailFuel =>
      cases derivation with
      | nil =>
          exact ⟨_, _, by simp [elaborateTailUsingFuel], .nil⟩
      | @cons pattern body arms supply generatedPattern afterPattern
          generatedBody afterBody generatedTail next patternDerivation
          bodyDerivation tailDerivation =>
          obtain ⟨computedPattern, computedAfterPattern, patternExecutable,
              computedPatternDerivation, patternNextEquality,
              patternBindingsEquality⟩ :=
            executablePatternFuelReplay_of_tracked coherent replay
              signatureWellFormed (by
                simp only [MatchFirstArm.listComplexity_cons,
                  MatchFirstArm.complexity_mk] at bound
                omega) patternDerivation
          cases patternNextEquality
          rw [patternBindingsEquality] at bodyDerivation
          obtain ⟨computedBody, computedAfterBody, bodyExecutable,
              computedBodyDerivation⟩ :=
            replay body (by
              simp only [MatchFirstArm.listComplexity_cons,
                MatchFirstArm.complexity_mk] at bound
              omega) bodyDerivation.2 signatureWellFormed bodyDerivation.1
          obtain ⟨bodyComparison⟩ := coherent body (by
            simp only [MatchFirstArm.listComplexity_cons,
              MatchFirstArm.complexity_mk] at bound
            omega) signatureWellFormed bodyDerivation.1 bodyDerivation.2
              computedBodyDerivation
          cases bodyComparison.next_eq
          obtain ⟨computedTail, computedNext, tailExecutable,
              computedTailDerivation⟩ :=
            executableMatchFirstTailFuelReplay_of_tracked
              (tailFuel := tailFuel) coherent replay signatureWellFormed (by
                simp only [MatchFirstArm.listComplexity_cons] at bound
                omega) (by
                  simp only [List.length_cons] at enoughFuel
                  omega) tailDerivation
          exact ⟨_, computedNext,
            by simp [elaborateTailUsingFuel, patternExecutable, bodyExecutable,
              tailExecutable],
            .cons computedPatternDerivation computedBodyDerivation
              computedTailDerivation⟩
termination_by arms.length

private theorem executableMatchFirstArmsFuelReplay_of_tracked
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {originalTargetType originalMatcherType targetType matcherType : Ty}
    {arms : List MatchFirstArm} {supply next : Supply}
    {generated : GeneratedArms}
    (signatureWellFormed : signature.WellFormed)
    (bound : MatchFirstArm.listComplexity arms < limit)
    (derivation : ArmsElaborateUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) signature context
      originalTargetType originalMatcherType arms supply generated next) :
    ExecutableM4MatchFirstArmsFuelReplay signature fuel context targetType
      matcherType arms supply := by
  cases derivation with
  | @cons pattern body arms supply generatedPattern afterPattern generatedBody
      afterBody generatedTail next patternDerivation bodyDerivation
      tailDerivation =>
      obtain ⟨computedPattern, computedAfterPattern, patternExecutable,
          computedPatternDerivation, patternNextEquality,
          patternBindingsEquality⟩ :=
        executablePatternFuelReplay_of_tracked coherent replay
          signatureWellFormed (by
            simp only [MatchFirstArm.listComplexity_cons,
              MatchFirstArm.complexity_mk] at bound
            omega) patternDerivation
      cases patternNextEquality
      rw [patternBindingsEquality] at bodyDerivation
      obtain ⟨computedBody, computedAfterBody, bodyExecutable,
          computedBodyDerivation⟩ :=
        replay body (by
          simp only [MatchFirstArm.listComplexity_cons,
            MatchFirstArm.complexity_mk] at bound
          omega) bodyDerivation.2 signatureWellFormed bodyDerivation.1
      obtain ⟨bodyComparison⟩ := coherent body (by
        simp only [MatchFirstArm.listComplexity_cons,
          MatchFirstArm.complexity_mk] at bound
        omega) signatureWellFormed bodyDerivation.1 bodyDerivation.2
          computedBodyDerivation
      cases bodyComparison.next_eq
      obtain ⟨computedTail, computedNext, tailExecutable,
          computedTailDerivation⟩ :=
        executableMatchFirstTailFuelReplay_of_tracked coherent replay
          signatureWellFormed (by
            simp only [MatchFirstArm.listComplexity_cons] at bound
            omega) (list_length_lt_twice_complexity_add_one arms)
          tailDerivation
      exact ⟨_, computedNext,
        by simp [elaborateArmsUsing, patternExecutable, bodyExecutable,
          elaborateTailUsing, tailExecutable],
        .cons computedPatternDerivation computedBodyDerivation
          computedTailDerivation⟩

/-- Ordered single-result matching preserves non-exact fuel-local replay. -/
theorem matchFirstM4FuelReplayStep : MatchFirstM4FuelReplayStep := by
  intro target matcher arms coherent replay
  intro signature fuel context supply next generated derivation
    signatureWellFormed wellFormed
  cases fuel with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel =>
      simp only [ElaboratesFuel] at derivation
      have tracked :=
        M4FreshRenaming.MatchFirstTyping.ElaboratesUsing.trackContextSupport
          signatureWellFormed wellFormed derivation
      cases tracked with
      | @matchFirst _ _ _ _ generatedTarget afterTarget generatedMatcher
          afterMatcher generatedArms finish exhaustive targetDerivation
          matcherDerivation armsDerivation =>
          have exhaustiveCheck : armsExhaustive arms = true :=
            (exhaustive_iff_armsExhaustive arms).1 exhaustive
          obtain ⟨computedTarget, computedAfterTarget, targetExecutable,
              computedTargetDerivation⟩ :=
            replay target (by
              simp only [Expr.complexity_matchFirst]
              omega) targetDerivation.2 signatureWellFormed targetDerivation.1
          obtain ⟨targetComparison⟩ := coherent target (by
            simp only [Expr.complexity_matchFirst]
            omega) signatureWellFormed targetDerivation.1 targetDerivation.2
              computedTargetDerivation
          cases targetComparison.next_eq
          obtain ⟨computedMatcher, computedAfterMatcher, matcherExecutable,
              computedMatcherDerivation⟩ :=
            replay matcher (by
              simp only [Expr.complexity_matchFirst]
              omega) matcherDerivation.2 signatureWellFormed matcherDerivation.1
          obtain ⟨matcherComparison⟩ := coherent matcher (by
            simp only [Expr.complexity_matchFirst]
            omega) signatureWellFormed matcherDerivation.1 matcherDerivation.2
              computedMatcherDerivation
          cases matcherComparison.next_eq
          obtain ⟨computedArms, computedNext, armsExecutable,
              computedArmsDerivation⟩ :=
            executableMatchFirstArmsFuelReplay_of_tracked coherent replay
              signatureWellFormed (by
                simp only [Expr.complexity_matchFirst]
                omega) armsDerivation
          have targetExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel context target supply =
                some (computedTarget, afterTarget) := by
            simpa [M4.elaborateFuel] using targetExecutable
          have matcherExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel context matcher
                  afterTarget = some (computedMatcher, afterMatcher) := by
            simpa [M4.elaborateFuel] using matcherExecutable
          have armsExecutableUsing :
              elaborateArmsUsing
                  (M4.elaborateFuelUsing unify signature fuel) signature context
                  computedTarget.target computedMatcher.target arms afterMatcher =
                some (computedArms, computedNext) := by
            simpa [M4.elaborateFuel] using armsExecutable
          exact ⟨_, computedNext,
            by simp [M4.elaborateFuel, M4.elaborateFuelUsing,
              MatchFirstTyping.elaborateUsing, exhaustiveCheck,
              targetExecutableUsing, matcherExecutableUsing,
              armsExecutableUsing],
            .matchFirst exhaustive computedTargetDerivation
              computedMatcherDerivation computedArmsDerivation⟩

end TypePM.Source.M4.CompletenessArchitecture
