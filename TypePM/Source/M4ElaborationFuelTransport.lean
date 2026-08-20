import TypePM.Source.M4RecursiveElaboration

/-!
# Transport of successful M4 elaboration runs

These lemmas replay a successful callback-parametric elaboration with a
second callback.  They are used to turn a kernel-computed run whose `let`
solver is `unifyWithFuel` into an exact run of the public `unify`-based
elaborator.
-/

namespace TypePM.Source.M4

def ElaboratorSuccessTransport
    (sourceElaborator targetElaborator : ExpressionElaborator) : Prop :=
  ∀ {context expression supply generated next},
    sourceElaborator context expression supply = some (generated, next) →
      targetElaborator context expression supply = some (generated, next)

theorem elaborateItemsUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator) :
    ∀ {context items supply generated next},
      elaborateItemsUsing sourceElaborator context items supply = some (generated, next) →
        elaborateItemsUsing targetElaborator context items supply = some (generated, next) := by
  intro context items supply generated next success
  induction items generalizing supply generated next with
  | nil =>
      simpa [elaborateItemsUsing] using success
  | cons item items induction =>
      cases headResult : sourceElaborator context item supply with
      | none => simp [elaborateItemsUsing, headResult] at success
      | some output =>
          rcases output with ⟨generatedItem, afterItem⟩
          have headTo := transport headResult
          cases tailResult : elaborateItemsUsing sourceElaborator context items afterItem with
          | none => simp [elaborateItemsUsing, headResult, tailResult] at success
          | some output =>
              rcases output with ⟨generatedItems, afterItems⟩
              have tailTo := induction tailResult
              simp [elaborateItemsUsing, headResult, tailResult] at success
              simpa [elaborateItemsUsing, headTo, tailTo] using success

theorem elaborateCallUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator) :
    ∀ {context accumulated arguments supply generated next},
      elaborateCallUsing sourceElaborator context accumulated arguments supply =
          some (generated, next) →
        elaborateCallUsing targetElaborator context accumulated arguments supply =
          some (generated, next) := by
  intro context accumulated arguments supply generated next success
  induction arguments generalizing accumulated supply generated next with
  | nil =>
      simpa [elaborateCallUsing] using success
  | cons argument arguments induction =>
      cases headResult : sourceElaborator context argument supply with
      | none => simp [elaborateCallUsing, headResult] at success
      | some output =>
          rcases output with ⟨generatedArgument, afterArgument⟩
          have headTo := transport headResult
          have tailTo := induction (by
            simpa [elaborateCallUsing, headResult] using success)
          simpa [elaborateCallUsing, headTo] using tailTo

mutual

theorem elaboratePatternUsingFuel_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature : FrozenSignature} {context : Context}
    {arguments : PatternContext} {fuel : Nat} {pattern : Pattern}
    {bindings : List Ty} {supply next : Supply} {generated : GeneratedPattern}
    (success : elaboratePatternUsingFuel sourceElaborator signature context arguments fuel
      pattern bindings supply = some (generated, next)) :
    elaboratePatternUsingFuel targetElaborator signature context arguments fuel pattern
      bindings supply = some (generated, next) := by
  cases fuel with
  | zero => simp [elaboratePatternUsingFuel] at success
  | succ fuel =>
      cases pattern with
      | var => simpa [elaboratePatternUsingFuel] using success
      | wild => simpa [elaboratePatternUsingFuel] using success
      | value expression =>
          cases expressionResult : sourceElaborator (Pattern.extendContext bindings context)
              expression supply with
          | none => simp [elaboratePatternUsingFuel, expressionResult] at success
          | some output =>
              rcases output with ⟨generatedExpression, afterExpression⟩
              have expressionTo := transport expressionResult
              simp [elaboratePatternUsingFuel, expressionResult] at success
              simpa [elaboratePatternUsingFuel, expressionTo] using success
      | ctor constructor fields =>
          cases lookup : signature.lookupPatternConstructor constructor with
          | none => simp [elaboratePatternUsingFuel, lookup] at success
          | some scheme =>
              by_cases arity : fields.length = scheme.fields.length
              · cases fieldsResult : elaboratePatternsUsingFuel sourceElaborator signature
                    context arguments fuel fields bindings
                    (scheme.instantiate supply).2 with
                | none =>
                    simp [elaboratePatternUsingFuel, lookup, arity, fieldsResult]
                      at success
                | some output =>
                    rcases output with ⟨generatedFields, afterFields⟩
                    have fieldsTo := elaboratePatternsUsingFuel_success_transport
                      transport fieldsResult
                    simp [elaboratePatternUsingFuel, lookup, arity, fieldsResult]
                      at success
                    simpa [elaboratePatternUsingFuel, lookup, arity, fieldsTo]
                      using success
              · simp [elaboratePatternUsingFuel, lookup, arity] at success
      | tuple items =>
          cases itemsResult : elaboratePatternsUsingFuel sourceElaborator signature context
              arguments fuel items bindings supply with
          | none => simp [elaboratePatternUsingFuel, itemsResult] at success
          | some output =>
              rcases output with ⟨generatedItems, afterItems⟩
              have itemsTo := elaboratePatternsUsingFuel_success_transport
                transport itemsResult
              simp [elaboratePatternUsingFuel, itemsResult] at success
              simpa [elaboratePatternUsingFuel, itemsTo] using success
      | embed index =>
          simpa [elaboratePatternUsingFuel] using success
      | app function fields =>
          cases lookup : signature.lookupPatternFunction function with
          | none => simp [elaboratePatternUsingFuel, lookup] at success
          | some scheme =>
              by_cases arity : fields.length = scheme.fields.length
              · cases fieldsResult : elaboratePatternsUsingFuel sourceElaborator signature
                    context arguments fuel fields bindings
                    (scheme.instantiate supply).2 with
                | none =>
                    simp [elaboratePatternUsingFuel, lookup, arity, fieldsResult]
                      at success
                | some output =>
                    rcases output with ⟨generatedFields, afterFields⟩
                    have fieldsTo := elaboratePatternsUsingFuel_success_transport
                      transport fieldsResult
                    simp [elaboratePatternUsingFuel, lookup, arity, fieldsResult]
                      at success
                    simpa [elaboratePatternUsingFuel, lookup, arity, fieldsTo]
                      using success
              · simp [elaboratePatternUsingFuel, lookup, arity] at success
termination_by fuel

theorem elaboratePatternsUsingFuel_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature : FrozenSignature} {context : Context}
    {arguments : PatternContext} {fuel : Nat} {patterns : List Pattern}
    {bindings : List Ty} {supply next : Supply} {generated : GeneratedPatterns}
    (success : elaboratePatternsUsingFuel sourceElaborator signature context arguments fuel
      patterns bindings supply = some (generated, next)) :
    elaboratePatternsUsingFuel targetElaborator signature context arguments fuel patterns
      bindings supply = some (generated, next) := by
  cases fuel with
  | zero => simp [elaboratePatternsUsingFuel] at success
  | succ fuel =>
      cases patterns with
      | nil => simpa [elaboratePatternsUsingFuel] using success
      | cons pattern patterns =>
          cases patternResult : elaboratePatternUsingFuel sourceElaborator signature context
              arguments fuel pattern bindings supply with
          | none => simp [elaboratePatternsUsingFuel, patternResult] at success
          | some output =>
              rcases output with ⟨generatedPattern, afterPattern⟩
              have patternTo := elaboratePatternUsingFuel_success_transport
                transport patternResult
              cases patternsResult : elaboratePatternsUsingFuel sourceElaborator signature
                  context arguments fuel patterns generatedPattern.bindings
                  afterPattern with
              | none =>
                  simp [elaboratePatternsUsingFuel, patternResult, patternsResult]
                    at success
              | some rest =>
                  rcases rest with ⟨generatedPatterns, afterPatterns⟩
                  have patternsTo := elaboratePatternsUsingFuel_success_transport
                    transport patternsResult
                  simp [elaboratePatternsUsingFuel, patternResult, patternsResult]
                    at success
                  simpa [elaboratePatternsUsingFuel, patternTo, patternsTo]
                    using success
termination_by fuel

end

theorem elaboratePatternUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature context arguments pattern bindings supply generated next}
    (success : elaboratePatternUsing sourceElaborator signature context arguments pattern
      bindings supply = some (generated, next)) :
    elaboratePatternUsing targetElaborator signature context arguments pattern bindings supply =
      some (generated, next) :=
  elaboratePatternUsingFuel_success_transport transport success

end TypePM.Source.M4

namespace TypePM.Source.MatcherTyping

open M4

theorem elaborateCheckedExpressionUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {context expression expected supply generated next}
    (success : elaborateCheckedExpressionUsing sourceElaborator context expression
      expected supply = some (generated, next)) :
    elaborateCheckedExpressionUsing targetElaborator context expression expected
      supply = some (generated, next) := by
  cases expressionResult : sourceElaborator context expression supply with
  | none => simp [elaborateCheckedExpressionUsing, expressionResult] at success
  | some output =>
      rcases output with ⟨generatedExpression, afterExpression⟩
      have expressionTo := transport expressionResult
      simp [elaborateCheckedExpressionUsing, expressionResult] at success
      simpa [elaborateCheckedExpressionUsing, expressionTo] using success

theorem elaborateNextMatcherItemsUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator) :
    ∀ {context items holes supply generated next},
      elaborateNextMatcherItemsUsing sourceElaborator context items holes supply =
          some (generated, next) →
        elaborateNextMatcherItemsUsing targetElaborator context items holes supply =
          some (generated, next) := by
  intro context items holes supply generated next success
  induction items generalizing holes supply generated next with
  | nil =>
      cases holes with
      | nil =>
          simp [elaborateNextMatcherItemsUsing] at success ⊢
          exact success
      | cons _ _ => simp [elaborateNextMatcherItemsUsing] at success
  | cons item items induction =>
      cases holes with
      | nil => simp [elaborateNextMatcherItemsUsing] at success
      | cons hole holes =>
          cases headResult : elaborateCheckedExpressionUsing sourceElaborator
              context item (.slot hole.capability hole.target) supply with
          | none =>
              simp [elaborateNextMatcherItemsUsing, headResult] at success
          | some output =>
              rcases output with ⟨generatedItem, afterItem⟩
              have headTo := elaborateCheckedExpressionUsing_success_transport
                transport headResult
              cases tailResult : elaborateNextMatcherItemsUsing sourceElaborator
                  context items holes afterItem with
              | none =>
                  simp [elaborateNextMatcherItemsUsing, headResult, tailResult]
                    at success
              | some output =>
                  rcases output with ⟨generatedItems, afterItems⟩
                  have tailTo := induction tailResult
                  simp [elaborateNextMatcherItemsUsing, headResult, tailResult]
                    at success
                  simpa [elaborateNextMatcherItemsUsing, headTo, tailTo]
                    using success

theorem elaborateNextMatchersUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {context expression holes supply generated next}
    (success : elaborateNextMatchersUsing sourceElaborator context expression
      holes supply = some (generated, next)) :
    elaborateNextMatchersUsing targetElaborator context expression holes supply =
      some (generated, next) := by
  cases holes with
  | nil =>
      cases expression with
      | tuple items =>
          cases items with
          | nil =>
              exact elaborateCheckedExpressionUsing_success_transport transport
                (sourceElaborator := sourceElaborator)
                (targetElaborator := targetElaborator)
                (by simpa [elaborateNextMatchersUsing] using success)
          | cons item items => simp [elaborateNextMatchersUsing] at success
      | _ => simp [elaborateNextMatchersUsing] at success
  | cons first rest =>
      cases rest with
      | nil =>
          exact elaborateCheckedExpressionUsing_success_transport transport
            (sourceElaborator := sourceElaborator)
            (targetElaborator := targetElaborator)
            (by simpa [elaborateNextMatchersUsing] using success)
      | cons second rest =>
          cases expression with
          | tuple items =>
              exact elaborateNextMatcherItemsUsing_success_transport transport
                (by simpa [elaborateNextMatchersUsing] using success)
          | _ => simp [elaborateNextMatchersUsing] at success

theorem elaborateMatcherArmUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature context captures matcherTarget holes arm supply generated next}
    (success : elaborateMatcherArmUsing sourceElaborator signature context captures
      matcherTarget holes arm supply = some (generated, next)) :
    elaborateMatcherArmUsing targetElaborator signature context captures
      matcherTarget holes arm supply = some (generated, next) := by
  cases arm with
  | mk header body =>
      cases headerResult : elaborateDPat signature header matcherTarget supply with
      | none => simp [elaborateMatcherArmUsing, headerResult] at success
      | some output =>
          rcases output with ⟨generatedHeader, afterHeader⟩
          cases bodyResult : elaborateCheckedExpressionUsing sourceElaborator
              (Pattern.extendContext generatedHeader.bindings
                (Pattern.extendContext captures context))
              body (DataTypes.list (holeProductTarget holes)) afterHeader with
          | none =>
              simp [elaborateMatcherArmUsing, headerResult, bodyResult] at success
          | some output =>
              rcases output with ⟨generatedBody, afterBody⟩
              have bodyTo := elaborateCheckedExpressionUsing_success_transport
                transport bodyResult
              simp [elaborateMatcherArmUsing, headerResult, bodyResult] at success
              simpa [elaborateMatcherArmUsing, headerResult, bodyTo] using success

theorem elaborateMatcherArmsUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator) :
    ∀ {signature context captures matcherTarget holes arms supply generated next},
      elaborateMatcherArmsUsing sourceElaborator signature context captures
          matcherTarget holes arms supply = some (generated, next) →
        elaborateMatcherArmsUsing targetElaborator signature context captures
          matcherTarget holes arms supply = some (generated, next) := by
  intro signature context captures matcherTarget holes arms supply generated next
    success
  induction arms generalizing supply generated next with
  | nil => simpa [elaborateMatcherArmsUsing] using success
  | cons arm arms induction =>
      cases headResult : elaborateMatcherArmUsing sourceElaborator signature
          context captures matcherTarget holes arm supply with
      | none => simp [elaborateMatcherArmsUsing, headResult] at success
      | some output =>
          rcases output with ⟨generatedArm, afterArm⟩
          have headTo := elaborateMatcherArmUsing_success_transport transport
            headResult
          cases tailResult : elaborateMatcherArmsUsing sourceElaborator signature
              context captures matcherTarget holes arms afterArm with
          | none =>
              simp [elaborateMatcherArmsUsing, headResult, tailResult] at success
          | some output =>
              rcases output with ⟨generatedArms, afterArms⟩
              have tailTo := induction tailResult
              simp [elaborateMatcherArmsUsing, headResult, tailResult] at success
              simpa [elaborateMatcherArmsUsing, headTo, tailTo] using success

theorem elaborateMatcherClauseUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature context matcherTarget clause supply generated next}
    (success : elaborateMatcherClauseUsing sourceElaborator signature context
      matcherTarget clause supply = some (generated, next)) :
    elaborateMatcherClauseUsing targetElaborator signature context matcherTarget
      clause supply = some (generated, next) := by
  cases clause with
  | mk header nextMatchers arms =>
      by_cases shape : (MatcherClause.mk header nextMatchers arms).toShape.check
          signature
      · cases headerResult : elaboratePPat signature header matcherTarget none
            supply with
        | none =>
            simp [elaborateMatcherClauseUsing, shape, headerResult,
              MatcherClause.header, MatcherClause.nextMatchers,
              MatcherClause.arms] at success
        | some output =>
            rcases output with ⟨generatedHeader, afterHeader⟩
            cases nextResult : elaborateNextMatchersUsing sourceElaborator
                (Pattern.extendContext generatedHeader.captures context)
                nextMatchers generatedHeader.holes afterHeader with
            | none =>
                simp [elaborateMatcherClauseUsing, shape, headerResult,
                  nextResult, MatcherClause.header, MatcherClause.nextMatchers,
                  MatcherClause.arms] at success
            | some output =>
                rcases output with ⟨generatedNext, afterNext⟩
                have nextTo := elaborateNextMatchersUsing_success_transport
                  transport nextResult
                cases armsResult : elaborateMatcherArmsUsing sourceElaborator
                    signature context generatedHeader.captures matcherTarget
                    generatedHeader.holes arms afterNext with
                | none =>
                    simp [elaborateMatcherClauseUsing, shape, headerResult,
                      nextResult, armsResult, MatcherClause.header,
                      MatcherClause.nextMatchers, MatcherClause.arms] at success
                | some output =>
                    rcases output with ⟨generatedArms, afterArms⟩
                    have armsTo := elaborateMatcherArmsUsing_success_transport
                      transport armsResult
                    simp [elaborateMatcherClauseUsing, shape, headerResult,
                      nextResult, armsResult, MatcherClause.header,
                      MatcherClause.nextMatchers, MatcherClause.arms] at success
                    simpa [elaborateMatcherClauseUsing, shape, headerResult,
                      nextTo, armsTo, MatcherClause.header,
                      MatcherClause.nextMatchers, MatcherClause.arms] using success
      · simp [elaborateMatcherClauseUsing, shape] at success

theorem elaborateMatcherClausesUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator) :
    ∀ {signature context matcherTarget clauses supply generated next},
      elaborateMatcherClausesUsing sourceElaborator signature context matcherTarget
          clauses supply = some (generated, next) →
        elaborateMatcherClausesUsing targetElaborator signature context matcherTarget
          clauses supply = some (generated, next) := by
  intro signature context matcherTarget clauses supply generated next success
  induction clauses generalizing supply generated next with
  | nil => simpa [elaborateMatcherClausesUsing] using success
  | cons clause clauses induction =>
      cases headResult : elaborateMatcherClauseUsing sourceElaborator signature
          context matcherTarget clause supply with
      | none => simp [elaborateMatcherClausesUsing, headResult] at success
      | some output =>
          rcases output with ⟨generatedClause, afterClause⟩
          have headTo := elaborateMatcherClauseUsing_success_transport transport
            headResult
          cases tailResult : elaborateMatcherClausesUsing sourceElaborator signature
              context matcherTarget clauses afterClause with
          | none =>
              simp [elaborateMatcherClausesUsing, headResult, tailResult] at success
          | some output =>
              rcases output with ⟨generatedClauses, afterClauses⟩
              have tailTo := induction tailResult
              simp [elaborateMatcherClausesUsing, headResult, tailResult] at success
              simpa [elaborateMatcherClausesUsing, headTo, tailTo] using success

theorem elaborateMatcherLiteralUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature context clauses supply generated next}
    (success : elaborateMatcherLiteralUsing sourceElaborator signature context
      clauses supply = some (generated, next)) :
    elaborateMatcherLiteralUsing targetElaborator signature context clauses supply =
      some (generated, next) := by
  by_cases checked : staticChecks signature clauses
  · cases clausesResult : elaborateMatcherClausesUsing sourceElaborator signature
        context (.var ⟨supply.ty⟩) clauses
        ⟨supply.ty + 1, supply.cap + 1⟩ with
    | none =>
        simp [elaborateMatcherLiteralUsing, checked, clausesResult] at success
    | some output =>
        rcases output with ⟨generatedClauses, afterClauses⟩
        have clausesTo := elaborateMatcherClausesUsing_success_transport
          transport clausesResult
        simp [elaborateMatcherLiteralUsing, checked, clausesResult] at success
        simpa [elaborateMatcherLiteralUsing, checked, clausesTo] using success
  · simp [elaborateMatcherLiteralUsing, checked] at success

end TypePM.Source.MatcherTyping

namespace TypePM.Source.MatchFirstTyping

open M4

theorem elaborateTailUsingFuel_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator) :
    ∀ {signature context targetType matcherType expectedResult fuel arms supply
        generated next},
      elaborateTailUsingFuel sourceElaborator signature context targetType matcherType
          expectedResult fuel arms supply = some (generated, next) →
        elaborateTailUsingFuel targetElaborator signature context targetType matcherType
          expectedResult fuel arms supply = some (generated, next) := by
  intro signature context targetType matcherType expectedResult fuel arms supply
    generated next success
  induction fuel generalizing arms supply generated next with
  | zero => simp [elaborateTailUsingFuel] at success
  | succ fuel induction =>
      cases arms with
      | nil => simpa [elaborateTailUsingFuel] using success
      | cons arm arms =>
          cases arm with
          | mk pattern body =>
              cases patternResult : elaboratePatternUsing sourceElaborator signature
                  context [] pattern [] supply with
              | none => simp [elaborateTailUsingFuel, patternResult] at success
              | some output =>
                  rcases output with ⟨generatedPattern, afterPattern⟩
                  have patternTo := M4.elaboratePatternUsing_success_transport
                    transport patternResult
                  cases bodyResult : sourceElaborator
                      (Pattern.extendContext generatedPattern.bindings context)
                      body afterPattern with
                  | none =>
                      simp [elaborateTailUsingFuel, patternResult, bodyResult]
                        at success
                  | some output =>
                      rcases output with ⟨generatedBody, afterBody⟩
                      have bodyTo := transport bodyResult
                      cases tailResult : elaborateTailUsingFuel sourceElaborator
                          signature context targetType matcherType expectedResult
                          fuel arms afterBody with
                      | none =>
                          simp [elaborateTailUsingFuel, patternResult, bodyResult,
                            tailResult] at success
                      | some output =>
                          rcases output with ⟨generatedTail, afterTail⟩
                          have tailTo := induction tailResult
                          simp [elaborateTailUsingFuel, patternResult, bodyResult,
                            tailResult] at success
                          simpa [elaborateTailUsingFuel, patternTo, bodyTo, tailTo]
                            using success

theorem elaborateTailUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature context targetType matcherType expectedResult arms supply
      generated next}
    (success : elaborateTailUsing sourceElaborator signature context targetType
      matcherType expectedResult arms supply = some (generated, next)) :
    elaborateTailUsing targetElaborator signature context targetType matcherType
      expectedResult arms supply = some (generated, next) :=
  elaborateTailUsingFuel_success_transport transport success

theorem elaborateArmsUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature context targetType matcherType arms supply generated next}
    (success : elaborateArmsUsing sourceElaborator signature context targetType
      matcherType arms supply = some (generated, next)) :
    elaborateArmsUsing targetElaborator signature context targetType matcherType
      arms supply = some (generated, next) := by
  cases arms with
  | nil => simp [elaborateArmsUsing] at success
  | cons arm arms =>
      cases arm with
      | mk pattern body =>
          cases patternResult : elaboratePatternUsing sourceElaborator signature
              context [] pattern [] supply with
          | none => simp [elaborateArmsUsing, patternResult] at success
          | some output =>
              rcases output with ⟨generatedPattern, afterPattern⟩
              have patternTo := M4.elaboratePatternUsing_success_transport
                transport patternResult
              cases bodyResult : sourceElaborator
                  (Pattern.extendContext generatedPattern.bindings context)
                  body afterPattern with
              | none =>
                  simp [elaborateArmsUsing, patternResult, bodyResult] at success
              | some output =>
                  rcases output with ⟨generatedBody, afterBody⟩
                  have bodyTo := transport bodyResult
                  cases tailResult : elaborateTailUsing sourceElaborator signature
                      context targetType matcherType generatedBody.target arms
                      afterBody with
                  | none =>
                      simp [elaborateArmsUsing, patternResult, bodyResult,
                        tailResult] at success
                  | some output =>
                      rcases output with ⟨generatedTail, afterTail⟩
                      have tailTo := elaborateTailUsing_success_transport transport
                        tailResult
                      simp [elaborateArmsUsing, patternResult, bodyResult,
                        tailResult] at success
                      simpa [elaborateArmsUsing, patternTo, bodyTo, tailTo]
                        using success

theorem elaborateUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature context target matcher arms supply generated next}
    (success : elaborateUsing sourceElaborator signature context target matcher
      arms supply = some (generated, next)) :
    elaborateUsing targetElaborator signature context target matcher arms supply =
      some (generated, next) := by
  by_cases exhaustive : armsExhaustive arms
  · cases targetResult : sourceElaborator context target supply with
    | none => simp [elaborateUsing, exhaustive, targetResult] at success
    | some output =>
        rcases output with ⟨generatedTarget, afterTarget⟩
        have targetTo := transport targetResult
        cases matcherResult : sourceElaborator context matcher afterTarget with
        | none =>
            simp [elaborateUsing, exhaustive, targetResult, matcherResult]
              at success
        | some output =>
            rcases output with ⟨generatedMatcher, afterMatcher⟩
            have matcherTo := transport matcherResult
            cases armsResult : elaborateArmsUsing sourceElaborator signature
                context generatedTarget.target generatedMatcher.target arms
                afterMatcher with
            | none =>
                simp [elaborateUsing, exhaustive, targetResult, matcherResult,
                  armsResult] at success
            | some output =>
                rcases output with ⟨generatedArms, afterArms⟩
                have armsTo := elaborateArmsUsing_success_transport transport
                  armsResult
                simp [elaborateUsing, exhaustive, targetResult, matcherResult,
                  armsResult] at success
                simpa [elaborateUsing, exhaustive, targetTo, matcherTo, armsTo]
                  using success
  · simp [elaborateUsing, exhaustive] at success

end TypePM.Source.MatchFirstTyping

namespace TypePM.Source.M4

theorem elaborateFixUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {context body supply generated next}
    (success : elaborateFixUsing sourceElaborator context body supply =
      some (generated, next)) :
    elaborateFixUsing targetElaborator context body supply =
      some (generated, next) := by
  by_cases direct : DirectSelf.check 1 body
  · cases bodyResult : sourceElaborator
        (Fix.bodyContext (Fix.domain body supply) (Fix.codomain body supply)
          context)
        body (Fix.bodySupply body supply) with
    | none => simp [elaborateFixUsing, direct, bodyResult] at success
    | some output =>
        rcases output with ⟨generatedBody, afterBody⟩
        have bodyTo := transport bodyResult
        simp [elaborateFixUsing, direct, bodyResult] at success
        simpa [elaborateFixUsing, direct, bodyTo] using success
  · simp [elaborateFixUsing, direct] at success

theorem elaborateMatchAllUsing_success_transport
    {sourceElaborator targetElaborator : ExpressionElaborator}
    (transport : ElaboratorSuccessTransport sourceElaborator targetElaborator)
    {signature context target matcher pattern body supply generated next}
    (success : elaborateMatchAllUsing sourceElaborator signature context target
      matcher pattern body supply = some (generated, next)) :
    elaborateMatchAllUsing targetElaborator signature context target matcher
      pattern body supply = some (generated, next) := by
  cases targetResult : sourceElaborator context target supply with
  | none => simp [elaborateMatchAllUsing, targetResult] at success
  | some output =>
      rcases output with ⟨generatedTarget, afterTarget⟩
      have targetTo := transport targetResult
      cases patternResult : elaboratePatternUsing sourceElaborator signature
          context [] pattern [] afterTarget with
      | none =>
          simp [elaborateMatchAllUsing, targetResult, patternResult] at success
      | some output =>
          rcases output with ⟨generatedPattern, afterPattern⟩
          have patternTo := elaboratePatternUsing_success_transport transport
            patternResult
          cases matcherResult : sourceElaborator context matcher afterPattern with
          | none =>
              simp [elaborateMatchAllUsing, targetResult, patternResult,
                matcherResult] at success
          | some output =>
              rcases output with ⟨generatedMatcher, afterMatcher⟩
              have matcherTo := transport matcherResult
              cases bodyResult : sourceElaborator
                  (Pattern.extendContext generatedPattern.bindings context)
                  body afterMatcher with
              | none =>
                  simp [elaborateMatchAllUsing, targetResult, patternResult,
                    matcherResult, bodyResult] at success
              | some output =>
                  rcases output with ⟨generatedBody, afterBody⟩
                  have bodyTo := transport bodyResult
                  simp [elaborateMatchAllUsing, targetResult, patternResult,
                    matcherResult, bodyResult] at success
                  simpa [elaborateMatchAllUsing, targetTo, patternTo, matcherTo,
                    bodyTo] using success

theorem elaborateFuelUsing_success_transport
    {solveSource solveTarget : List Equation → Option Subst}
    (solverTransport : ∀ {equations substitution},
      solveSource equations = some substitution →
        solveTarget equations = some substitution)
    {signature : FrozenSignature} :
    ∀ {fuel context expression supply generated next},
      elaborateFuelUsing solveSource signature fuel context expression supply =
          some (generated, next) →
        elaborateFuelUsing solveTarget signature fuel context expression supply =
          some (generated, next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro context expression supply generated next success
      simp [elaborateFuelUsing] at success
  | succ fuel induction =>
      intro context expression supply generated next success
      have recurTransport : ElaboratorSuccessTransport
          (elaborateFuelUsing solveSource signature fuel)
          (elaborateFuelUsing solveTarget signature fuel) := by
        intro recurContext recurExpression recurSupply recurGenerated recurNext
          recurSuccess
        exact induction recurSuccess
      cases expression with
      | var index =>
          simpa [elaborateFuelUsing] using success
      | lit value =>
          simpa [elaborateFuelUsing] using success
      | something =>
          simpa [elaborateFuelUsing] using success
      | lam body =>
          cases bodyResult : elaborateFuelUsing solveSource signature fuel
              (.mono (.var ⟨supply.ty⟩) :: context) body (supply.nextTy 1) with
          | none => simp [elaborateFuelUsing, bodyResult] at success
          | some output =>
              rcases output with ⟨generatedBody, afterBody⟩
              have bodyTo := induction bodyResult
              simp [elaborateFuelUsing, bodyResult] at success
              simpa [elaborateFuelUsing, bodyTo] using success
      | app function argument =>
          cases functionResult : elaborateFuelUsing solveSource signature fuel
              context function supply with
          | none => simp [elaborateFuelUsing, functionResult] at success
          | some output =>
              rcases output with ⟨generatedFunction, afterFunction⟩
              have functionTo := induction functionResult
              cases argumentResult : elaborateFuelUsing solveSource signature fuel
                  context argument afterFunction with
              | none =>
                  simp [elaborateFuelUsing, functionResult, argumentResult]
                    at success
              | some output =>
                  rcases output with ⟨generatedArgument, afterArgument⟩
                  have argumentTo := induction argumentResult
                  simp [elaborateFuelUsing, functionResult, argumentResult]
                    at success
                  simpa [elaborateFuelUsing, functionTo, argumentTo] using success
      | tuple items =>
          cases itemsResult : elaborateItemsUsing
              (elaborateFuelUsing solveSource signature fuel) context items
              supply with
          | none => simp [elaborateFuelUsing, itemsResult] at success
          | some output =>
              rcases output with ⟨generatedItems, afterItems⟩
              have itemsTo := elaborateItemsUsing_success_transport
                (sourceElaborator :=
                  elaborateFuelUsing solveSource signature fuel)
                (targetElaborator :=
                  elaborateFuelUsing solveTarget signature fuel)
                recurTransport itemsResult
              simp [elaborateFuelUsing, itemsResult] at success
              simpa [elaborateFuelUsing, itemsTo] using success
      | letE value body =>
          cases valueResult : elaborateFuelUsing solveSource signature fuel context
              value supply with
          | none => simp [elaborateFuelUsing, valueResult] at success
          | some output =>
              rcases output with ⟨generatedValue, afterValue⟩
              have valueTo := induction valueResult
              cases closureResult : inferGeneratedUsing solveSource generatedValue with
              | none =>
                  simp [elaborateFuelUsing, valueResult, closureResult] at success
              | some closed =>
                  have closureTo := inferGeneratedUsing_success_transport
                    solverTransport closureResult
                  cases bodyResult : elaborateFuelUsing solveSource signature fuel
                      ((context.applyFree closed.substitution).generalize
                          closed.target :: context.applyFree closed.substitution)
                      body (afterValue.join
                        (context.applyFree closed.substitution).initialSupply) with
                  | none =>
                      simp [elaborateFuelUsing, valueResult, closureResult,
                        bodyResult] at success
                  | some output =>
                      rcases output with ⟨generatedBody, afterBody⟩
                      have bodyTo := induction bodyResult
                      simp [elaborateFuelUsing, valueResult, closureResult,
                        bodyResult] at success
                      simpa [elaborateFuelUsing, valueTo, closureTo, bodyTo]
                        using success
      | ctor constructor arguments =>
          cases lookup : signature.base.lookupDataConstructor constructor with
          | none => simp [elaborateFuelUsing, lookup] at success
          | some scheme =>
              by_cases arity : arguments.length = scheme.callArity
              · have transported := elaborateCallUsing_success_transport
                    (sourceElaborator :=
                      elaborateFuelUsing solveSource signature fuel)
                    (targetElaborator :=
                      elaborateFuelUsing solveTarget signature fuel)
                    recurTransport
                    (by simpa [elaborateFuelUsing, lookup, arity] using success)
                simpa [elaborateFuelUsing, lookup, arity] using transported
              · simp [elaborateFuelUsing, lookup, arity] at success
      | prim operation arguments =>
          cases lookup : signature.base.lookupPrimitive operation with
          | none => simp [elaborateFuelUsing, lookup] at success
          | some scheme =>
              by_cases arity : arguments.length = scheme.callArity
              · have transported := elaborateCallUsing_success_transport
                    (sourceElaborator :=
                      elaborateFuelUsing solveSource signature fuel)
                    (targetElaborator :=
                      elaborateFuelUsing solveTarget signature fuel)
                    recurTransport
                    (by simpa [elaborateFuelUsing, lookup, arity] using success)
                simpa [elaborateFuelUsing, lookup, arity] using transported
              · simp [elaborateFuelUsing, lookup, arity] at success
      | ifE condition thenBranch elseBranch =>
          exact elaborateCallUsing_success_transport recurTransport
            (by simpa [elaborateFuelUsing] using success)
      | fixE body =>
          have transported := elaborateFixUsing_success_transport
            (sourceElaborator := elaborateFuelUsing solveSource signature fuel)
            (targetElaborator := elaborateFuelUsing solveTarget signature fuel)
            recurTransport (by simpa [elaborateFuelUsing] using success)
          simpa [elaborateFuelUsing] using transported
      | matcher clauses =>
          exact MatcherTyping.elaborateMatcherLiteralUsing_success_transport
            recurTransport (by simpa [elaborateFuelUsing] using success)
      | matchAll target matcher pattern body =>
          exact elaborateMatchAllUsing_success_transport recurTransport
            (by simpa [elaborateFuelUsing] using success)
      | matchFirst target matcher arms =>
          exact MatchFirstTyping.elaborateUsing_success_transport recurTransport
            (by simpa [elaborateFuelUsing] using success)

theorem elaborateFuel_success_of_solverFuel_success
    {solverFuel fuel : Nat} {signature context expression supply generated next}
    (success : elaborateFuelUsing (unifyWithFuel solverFuel) signature fuel context
      expression supply = some (generated, next)) :
    elaborateFuel signature fuel context expression supply =
      some (generated, next) := by
  exact elaborateFuelUsing_success_transport unify_eq_of_unifyWithFuel_success
    success

end TypePM.Source.M4
