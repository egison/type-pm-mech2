import TypePM.Source.M4StructuralReplay

/-!
# Executable replay for M4 user patterns

User-pattern elaboration is parameterized by an expression callback.  This
module replays that callback at every value-pattern expression and preserves
the finishing supply and binding interface needed by the next pattern or by
an enclosing match arm.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source

/-- Executable replay of one pattern, including the supply and binding
interface needed for source-ordered continuation. -/
def ExecutableM4PatternFuelReplay
    (signature : FrozenSignature) (fuel : Nat) (context : Context)
    (arguments : PatternContext) (pattern : Pattern) (bindings : List Ty)
    (supply : Supply) (generated : GeneratedPattern) (next : Supply) : Prop :=
  ∃ computed computedNext,
    elaboratePatternUsing (M4.elaborateFuel signature fuel) signature context
        arguments pattern bindings supply = some (computed, computedNext) ∧
      PatternElaboratesUsing (ElaboratesFuel signature fuel) signature context
        arguments pattern bindings supply computed computedNext ∧
      next = computedNext ∧ generated.bindings = computed.bindings

/-- Executable replay of a source-ordered pattern list. -/
def ExecutableM4PatternsFuelReplay
    (signature : FrozenSignature) (fuel : Nat) (context : Context)
    (arguments : PatternContext) (patterns : List Pattern) (bindings : List Ty)
    (supply : Supply) (generated : GeneratedPatterns) (next : Supply) : Prop :=
  ∃ computed computedNext,
    elaboratePatternsUsing (M4.elaborateFuel signature fuel) signature context
        arguments patterns bindings supply = some (computed, computedNext) ∧
      PatternsElaborateUsing (ElaboratesFuel signature fuel) signature context
        arguments patterns bindings supply computed computedNext ∧
      next = computedNext ∧ generated.bindings = computed.bindings

private def ExecutableM4PatternUsingFuelReplay
    (signature : FrozenSignature) (fuel patternFuel : Nat) (context : Context)
    (arguments : PatternContext) (pattern : Pattern) (bindings : List Ty)
    (supply : Supply) (generated : GeneratedPattern) (next : Supply) : Prop :=
  ∃ computed computedNext,
    elaboratePatternUsingFuel (M4.elaborateFuel signature fuel) signature context
        arguments patternFuel pattern bindings supply =
          some (computed, computedNext) ∧
      PatternElaboratesUsing (ElaboratesFuel signature fuel) signature context
        arguments pattern bindings supply computed computedNext ∧
      next = computedNext ∧ generated.bindings = computed.bindings

private def ExecutableM4PatternsUsingFuelReplay
    (signature : FrozenSignature) (fuel patternFuel : Nat) (context : Context)
    (arguments : PatternContext) (patterns : List Pattern) (bindings : List Ty)
    (supply : Supply) (generated : GeneratedPatterns) (next : Supply) : Prop :=
  ∃ computed computedNext,
    elaboratePatternsUsingFuel (M4.elaborateFuel signature fuel) signature
        context arguments patternFuel patterns bindings supply =
          some (computed, computedNext) ∧
      PatternsElaborateUsing (ElaboratesFuel signature fuel) signature context
        arguments patterns bindings supply computed computedNext ∧
      next = computedNext ∧ generated.bindings = computed.bindings

mutual

private theorem executablePatternUsingFuelReplay_of_tracked
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel patternFuel : Nat} {context : Context}
    {arguments : PatternContext} {pattern : Pattern} {bindings : List Ty}
    {supply next : Supply} {generated : GeneratedPattern}
    (signatureWellFormed : signature.WellFormed)
    (bound : pattern.complexity < limit)
    (enoughFuel : pattern.complexity < patternFuel)
    (derivation : PatternElaboratesUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) signature context
      arguments pattern bindings supply generated next) :
    ExecutableM4PatternUsingFuelReplay signature fuel patternFuel context
      arguments pattern bindings supply generated next := by
  cases patternFuel with
  | zero => simp at enoughFuel
  | succ patternFuel =>
   cases derivation with
  | var =>
      exact ⟨_, _, by simp [elaboratePatternUsingFuel], .var, rfl, rfl⟩
  | wild =>
      exact ⟨_, _, by simp [elaboratePatternUsingFuel], .wild, rfl, rfl⟩
  | @value expression bindings supply generatedExpression afterExpression
      expressionDerivation =>
      obtain ⟨computedExpression, computedAfterExpression, executable,
          computedDerivation⟩ :=
        replay expression (by
          simp only [Pattern.complexity_value] at bound
          omega) expressionDerivation.2 signatureWellFormed
          expressionDerivation.1
      obtain ⟨comparison⟩ := coherent expression (by
        simp only [Pattern.complexity_value] at bound
        omega) signatureWellFormed expressionDerivation.1
          expressionDerivation.2 computedDerivation
      cases comparison.next_eq
      exact ⟨_, _, by simp [elaboratePatternUsingFuel, executable],
        .value computedDerivation, rfl, rfl⟩
  | @ctor constructor fields bindings supply scheme generatedFields finish
      lookup arity fieldsDerivation =>
      obtain ⟨computedFields, computedFinish, executable, computedDerivation,
          nextEquality, bindingsEquality⟩ :=
        executablePatternsUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay
          signatureWellFormed (by
            simp only [Pattern.complexity_ctor] at bound
            omega) (by
              simp only [Pattern.complexity_ctor] at enoughFuel
              omega) fieldsDerivation
      exact ⟨_, computedFinish,
        by simp [elaboratePatternUsingFuel, lookup, arity, executable],
        .ctor lookup arity computedDerivation, nextEquality, bindingsEquality⟩
  | @tuple items bindings supply generatedItems finish itemsDerivation =>
      obtain ⟨computedItems, computedFinish, executable, computedDerivation,
          nextEquality, bindingsEquality⟩ :=
        executablePatternsUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay
          signatureWellFormed (by
            simp only [Pattern.complexity_tuple] at bound
            omega) (by
              simp only [Pattern.complexity_tuple] at enoughFuel
              omega) itemsDerivation
      exact ⟨_, computedFinish,
        by simp [elaboratePatternUsingFuel, executable],
        .tuple computedDerivation, nextEquality, bindingsEquality⟩
  | @and left right bindings supply generatedLeft afterLeft generatedRight finish
      leftDerivation rightDerivation =>
      obtain ⟨computedLeft, computedAfterLeft, leftExecutable,
          computedLeftDerivation, leftNextEquality, leftBindingsEquality⟩ :=
        executablePatternUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay signatureWellFormed
          (by
            simp only [Pattern.complexity_and] at bound
            omega) (by
              simp only [Pattern.complexity_and] at enoughFuel
              omega) leftDerivation
      cases leftNextEquality
      rw [leftBindingsEquality] at rightDerivation
      obtain ⟨computedRight, computedFinish, rightExecutable,
          computedRightDerivation, rightNextEquality, rightBindingsEquality⟩ :=
        executablePatternUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay signatureWellFormed
          (by
            simp only [Pattern.complexity_and] at bound
            omega) (by
              simp only [Pattern.complexity_and] at enoughFuel
              omega) rightDerivation
      exact ⟨_, computedFinish,
        by simp [elaboratePatternUsingFuel, leftExecutable, rightExecutable],
        .and computedLeftDerivation computedRightDerivation,
        rightNextEquality, rightBindingsEquality⟩
  | @or left right bindings supply generatedLeft afterLeft generatedRight finish
      checks leftDerivation rightDerivation checksComputed =>
      obtain ⟨computedLeft, computedAfterLeft, leftExecutable,
          computedLeftDerivation, leftNextEquality, leftBindingsEquality⟩ :=
        executablePatternUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay signatureWellFormed
          (by
            simp only [Pattern.complexity_or] at bound
            omega) (by
              simp only [Pattern.complexity_or] at enoughFuel
              omega) leftDerivation
      cases leftNextEquality
      obtain ⟨computedRight, computedFinish, rightExecutable,
          computedRightDerivation, rightNextEquality, rightBindingsEquality⟩ :=
        executablePatternUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay signatureWellFormed
          (by
            simp only [Pattern.complexity_or] at bound
            omega) (by
              simp only [Pattern.complexity_or] at enoughFuel
              omega) rightDerivation
      rw [leftBindingsEquality, rightBindingsEquality] at checksComputed
      exact ⟨_, computedFinish,
        by simp [elaboratePatternUsingFuel, leftExecutable, rightExecutable,
          checksComputed],
        .or computedLeftDerivation computedRightDerivation checksComputed,
        rightNextEquality, leftBindingsEquality⟩
  | @embed index bindings supply selected lookup =>
      exact ⟨_, _, by simp [elaboratePatternUsingFuel, lookup], .embed lookup,
        rfl, rfl⟩
  | @app function fields bindings supply scheme generatedFields finish lookup
      arity fieldsDerivation =>
      obtain ⟨computedFields, computedFinish, executable, computedDerivation,
          nextEquality, bindingsEquality⟩ :=
        executablePatternsUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay
          signatureWellFormed (by
            simp only [Pattern.complexity_app] at bound
            omega) (by
              simp only [Pattern.complexity_app] at enoughFuel
              omega) fieldsDerivation
      exact ⟨_, computedFinish,
        by simp [elaboratePatternUsingFuel, lookup, arity, executable],
        .app lookup arity computedDerivation, nextEquality, bindingsEquality⟩
termination_by pattern.complexity * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

private theorem executablePatternsUsingFuelReplay_of_tracked
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel patternFuel : Nat} {context : Context}
    {arguments : PatternContext} {patterns : List Pattern} {bindings : List Ty}
    {supply next : Supply} {generated : GeneratedPatterns}
    (signatureWellFormed : signature.WellFormed)
    (bound : Pattern.listComplexity patterns < limit)
    (enoughFuel : Pattern.listComplexity patterns < patternFuel)
    (derivation : PatternsElaborateUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) signature context
      arguments patterns bindings supply generated next) :
    ExecutableM4PatternsUsingFuelReplay signature fuel patternFuel context
      arguments patterns bindings supply generated next := by
  cases patternFuel with
  | zero => simp at enoughFuel
  | succ patternFuel =>
   cases derivation with
  | nil =>
      exact ⟨_, _, by simp [elaboratePatternsUsingFuel], .nil, rfl, rfl⟩
  | @cons pattern patterns bindings supply generatedPattern afterPattern
      generatedPatterns finish head tail =>
      obtain ⟨computedPattern, computedAfterPattern, headExecutable,
          computedHead, headNextEquality, headBindingsEquality⟩ :=
        executablePatternUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay signatureWellFormed
          (by
            simp only [Pattern.listComplexity_cons] at bound
            omega) (by
              simp only [Pattern.listComplexity_cons] at enoughFuel
              omega) head
      cases headNextEquality
      rw [headBindingsEquality] at tail
      obtain ⟨computedPatterns, computedFinish, tailExecutable,
          computedTail, tailNextEquality, tailBindingsEquality⟩ :=
        executablePatternsUsingFuelReplay_of_tracked (patternFuel := patternFuel)
          coherent replay signatureWellFormed
          (by
            simp only [Pattern.listComplexity_cons] at bound
            omega) (by
              simp only [Pattern.listComplexity_cons] at enoughFuel
              omega) tail
      exact ⟨_, computedFinish,
        by simp [elaboratePatternsUsingFuel, headExecutable, tailExecutable],
        .cons computedHead computedTail, tailNextEquality,
        tailBindingsEquality⟩
termination_by Pattern.listComplexity patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [Pattern.listComplexity]
  all_goals omega

end

/-- Replay a pattern derivation whose expression leaves already carry
well-formed-context evidence. -/
theorem executablePatternFuelReplay_of_tracked
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {arguments : PatternContext} {pattern : Pattern} {bindings : List Ty}
    {supply next : Supply} {generated : GeneratedPattern}
    (signatureWellFormed : signature.WellFormed)
    (bound : pattern.complexity < limit)
    (derivation : PatternElaboratesUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) signature context
      arguments pattern bindings supply generated next) :
    ExecutableM4PatternFuelReplay signature fuel context arguments pattern
      bindings supply generated next := by
  simpa [ExecutableM4PatternFuelReplay,
    ExecutableM4PatternUsingFuelReplay, elaboratePatternUsing] using
    (executablePatternUsingFuelReplay_of_tracked coherent replay
      signatureWellFormed bound (by omega) derivation)

/-- Tracked list counterpart of `executablePatternFuelReplay_of_tracked`. -/
theorem executablePatternsFuelReplay_of_tracked
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {arguments : PatternContext} {patterns : List Pattern} {bindings : List Ty}
    {supply next : Supply} {generated : GeneratedPatterns}
    (signatureWellFormed : signature.WellFormed)
    (bound : Pattern.listComplexity patterns < limit)
    (derivation : PatternsElaborateUsing
      (M4FreshRenaming.WellFormedFuelLeaf signature fuel) signature context
      arguments patterns bindings supply generated next) :
    ExecutableM4PatternsFuelReplay signature fuel context arguments patterns
      bindings supply generated next := by
  simpa [ExecutableM4PatternsFuelReplay,
    ExecutableM4PatternsUsingFuelReplay, elaboratePatternsUsing] using
    (executablePatternsUsingFuelReplay_of_tracked coherent replay
      signatureWellFormed bound (by omega) derivation)

/-- Replay one pattern whose syntax is bounded by an enclosing expression.
Context-support tracking provides well-formedness at every embedded expression
callback. -/
theorem executablePatternFuelReplay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {outerStart supply next : Supply} {arguments : PatternContext}
    {pattern : Pattern} {bindings : List Ty} {generated : GeneratedPattern}
    (signatureWellFormed : signature.WellFormed)
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart supply
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart supply
      (Ty.unificationVarsList bindings))
    (outerToSupply : outerStart.Le supply)
    (bound : pattern.complexity < limit)
    (derivation : PatternElaboratesUsing (ElaboratesFuel signature fuel)
      signature context arguments pattern bindings supply generated next) :
    ExecutableM4PatternFuelReplay signature fuel context arguments pattern
      bindings supply generated next := by
  apply executablePatternFuelReplay_of_tracked coherent replay
    signatureWellFormed bound
  exact M4FreshRenaming.PatternElaboratesUsing.trackContextSupportEarly
    signatureWellFormed contextWellFormed argumentsSupport bindingsSupport
    outerToSupply derivation

/-- List counterpart of `executablePatternFuelReplay`. -/
theorem executablePatternsFuelReplay
    {limit : Nat}
    (coherent : ∀ expression, expression.complexity < limit →
      FullM4FuelPairProperty expression)
    (replay : ∀ expression, expression.complexity < limit →
      M4FuelReplayProperty expression)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {outerStart supply next : Supply} {arguments : PatternContext}
    {patterns : List Pattern} {bindings : List Ty}
    {generated : GeneratedPatterns}
    (signatureWellFormed : signature.WellFormed)
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart supply
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart supply
      (Ty.unificationVarsList bindings))
    (outerToSupply : outerStart.Le supply)
    (bound : Pattern.listComplexity patterns < limit)
    (derivation : PatternsElaborateUsing (ElaboratesFuel signature fuel)
      signature context arguments patterns bindings supply generated next) :
    ExecutableM4PatternsFuelReplay signature fuel context arguments patterns
      bindings supply generated next := by
  apply executablePatternsFuelReplay_of_tracked coherent replay
    signatureWellFormed bound
  exact M4FreshRenaming.PatternsElaborateUsing.trackContextSupportEarly
    signatureWellFormed contextWellFormed argumentsSupport bindingsSupport
    outerToSupply derivation

end TypePM.Source.M4.CompletenessArchitecture
