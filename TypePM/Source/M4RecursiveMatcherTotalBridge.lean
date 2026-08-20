import TypePM.Source.M4TotalCoreRuntimeBridge
import TypePM.Source.M4CompletenessArchitecture
import TypePM.TotalUserMatcherSafety

/-!
# Fuel-indexed M4 matcher literals at the total-runtime boundary

This module anchors the matcher-literal runtime bridge at the recursive M4
expression relation.  For the first sound fragment, every next-matcher and arm
body must still lie in `RuntimeSupported`; those leaves can be translated from
`M4.ElaboratesFuel` to the completed M2 relation and then to `RuntimeTyping`.
The enclosing matcher literal itself is nevertheless a genuine M4-only source
form and is packaged as `TotalCoreTyping`.

The final section states the remaining recursive boundary explicitly.  A body
containing `matchAll` or `matchFirst` has `TotalCoreTyping`, not
`RuntimeTyping`, while `ValueTyping.matcherClosure` and runtime clause dispatch
currently store `RuntimeMatcherClausesTyping`.  Closing that boundary requires
a total clause/value certificate used mutually by dispatch safety; it cannot
be obtained by erasing a recursive body to the old runtime judgment.
-/

namespace TypePM.Runtime

open TypePM.Source.M4.CompletenessArchitecture

mutual

  theorem RuntimeSupported.toM2Fragment
      (supported : RuntimeSupported expression) : M2Fragment expression := by
    cases supported with
    | var => exact .var _
    | lit => exact .lit _
    | something => exact .something
    | boolTrue => exact .ctor .nil
    | boolFalse => exact .ctor .nil
    | listNil => exact .ctor .nil
    | listCons head tail =>
        exact .ctor (.cons head.toM2Fragment
          (.cons tail.toM2Fragment .nil))
    | tuple items => exact .tuple items.toM2FragmentList
    | lam body => exact .lam body.toM2Fragment
    | app function argument =>
        exact .app function.toM2Fragment argument.toM2Fragment
    | add left right =>
        exact .prim (.cons left.toM2Fragment
          (.cons right.toM2Fragment .nil))
    | append left right =>
        exact .prim (.cons left.toM2Fragment
          (.cons right.toM2Fragment .nil))
    | member needle target =>
        exact .prim (.cons needle.toM2Fragment
          (.cons target.toM2Fragment .nil))
    | deleteFirst needle target =>
        exact .prim (.cons needle.toM2Fragment
          (.cons target.toM2Fragment .nil))
    | map function target =>
        exact .prim (.cons function.toM2Fragment
          (.cons target.toM2Fragment .nil))
    | pairFirst pair => exact .prim (.cons pair.toM2Fragment .nil)
    | pairSecond pair => exact .prim (.cons pair.toM2Fragment .nil)
    | ifE condition thenBranch elseBranch =>
        exact .ifE condition.toM2Fragment thenBranch.toM2Fragment
          elseBranch.toM2Fragment

  theorem RuntimeSupporteds.toM2FragmentList
      (supported : RuntimeSupporteds expressions) : M2FragmentList expressions := by
    cases supported with
    | nil => exact .nil
    | cons head tail =>
        exact .cons head.toM2Fragment tail.toM2FragmentList

end

end TypePM.Runtime

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime
open TypePM.Source.M4.CompletenessArchitecture

/-- A callback-parametric solved-leaf bridge.  It is strictly weaker than
assuming matcher-clause safety: it translates each concrete checked M4 leaf
from its derivation, solved checks, and context correspondence. -/
structure SolvedM4CheckedExpressionBridge
    (expressionTyping : EmbeddedExpressionTyping) : Prop where
  checked : ∀ {fuel context expression expected supply generated next solution
      runtimeContext},
    CheckedExpressionElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      context expression expected supply generated next →
    generated.RuntimeSolution solution →
    MonomorphicContextCompatible context runtimeContext solution →
    expressionTyping runtimeContext expression (expected.apply solution)
  tuple : ∀ {context expressions targets},
    RuntimeCaptureExpressionsTyping expressionTyping context expressions targets →
    expressionTyping context (.tuple expressions) (.prod targets)

/-- A checked recursive-M4 leaf in the old runtime fragment erases to runtime
typing after its generated checks are solved. -/
theorem CheckedExpressionElaboratesUsing.toRuntimeTyping_of_m4Fuel
    (elaboration : CheckedExpressionElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      context expression expected supply generated next)
    (supported : RuntimeSupported expression)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    RuntimeTyping expression (expected.apply solution) runtimeContext := by
  cases elaboration with
  | @mk sourceGenerated _ sourceElaboration =>
      have sourceSemantic : Generated.SemanticSolution sourceGenerated solution := by
        constructor
        · exact semantic.1
        · intro obligation member
          exact semantic.2 obligation (by
            simp [GeneratedChecks.checked, member])
      have sourceM2 := elaboratesFuel_toM2_of_m2Fragment
        supported.toM2Fragment sourceElaboration
      have sourceTyping := supported.elaboration_typing
        paper1SignatureCompatible sourceM2 sourceSemantic contextCompatible
      obtain ⟨conversionClass, conversion⟩ := semantic.2
        ⟨sourceGenerated.target, expected⟩ (by
          simp [GeneratedChecks.checked])
      exact .checked sourceTyping conversion

theorem NextMatcherItemsElaborateUsing.toRuntimeTypings_of_m4Fuel
    (elaboration : NextMatcherItemsElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      context expressions holes supply generated next)
    (supported : RuntimeSupporteds expressions)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    RuntimeTypings expressions (solvedHoleSlotTypes solution holes)
      runtimeContext := by
  induction elaboration with
  | nil =>
      cases supported
      exact .nil
  | cons head tail tailInduction =>
      cases supported with
      | cons headSupported tailSupported =>
          simp only [GeneratedChecks.runtimeSolution_append] at semantic
          have headTyping := head.toRuntimeTyping_of_m4Fuel headSupported
            semantic.1 contextCompatible
          have tailTyping := tailInduction tailSupported semantic.2
          simpa [solvedHoleSlotTypes, RuntimeDual.apply, Ty.apply] using
            RuntimeTypings.cons headTyping tailTyping

theorem NextMatchersElaborateUsing.toRuntimeNextMatchersTyping_of_m4Fuel
    (elaboration : NextMatchersElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      context expression holes supply generated next)
    (supported : RuntimeSupported expression)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    RuntimeNextMatchersTyping runtimeContext expression
      (holes.map (RuntimeDual.apply solution)) := by
  cases elaboration with
  | zero checked => exact .zero
  | one checked =>
      apply RuntimeNextMatchersTyping.one
      simpa [RuntimeDual.apply, Ty.apply] using
        checked.toRuntimeTyping_of_m4Fuel supported semantic contextCompatible
  | many components =>
      cases supported with
      | tuple itemsSupported =>
          apply RuntimeNextMatchersTyping.many
          simpa [solvedHoleSlotTypes] using
            components.toRuntimeTypings_of_m4Fuel itemsSupported semantic
              contextCompatible

theorem MatcherArmElaboratesUsing.toRuntimeMatcherArmTyping_of_m4Fuel
    (elaboration : MatcherArmElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) DPatElaborates
      Paper1FrozenSignature.signature context captures matcherTarget holes arm
      supply generated next)
    (supported : RuntimeSupported arm.body)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherArmTyping definitionTypes (Ty.applyList solution captures)
      (matcherTarget.apply solution) (holes.map (RuntimeDual.apply solution))
      arm := by
  cases elaboration with
  | mk headerElaboration bodyElaboration =>
      rename_i header body generatedHeader afterHeader generatedBody
      have headerSolved : Solves solution generatedHeader.hard := by
        intro equation member
        exact semantic.1 equation (by simp [member])
      have bodySemantic : generatedBody.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · exact semantic.2
      have captureContextCompatible :=
        runtimeContextCompatible_extendPatternContext
          (bindings := captures) contextCompatible
      have bodyContextCompatible :=
        runtimeContextCompatible_extendPatternContext
          (bindings := generatedHeader.bindings) captureContextCompatible
      have bodyTyping := bodyElaboration.toRuntimeTyping_of_m4Fuel supported
        bodySemantic bodyContextCompatible
      apply RuntimeMatcherArmTyping.mk
        (headerElaboration.toRuntimeDPatTyping headerSolved)
      simpa [DataTypes.list, Ty.apply, Ty.applyList, List.append_assoc] using
        bodyTyping

theorem MatcherArmsElaborateUsing.toRuntimeMatcherArmsTyping_of_m4Fuel
    (elaboration : MatcherArmsElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) DPatElaborates
      Paper1FrozenSignature.signature context captures matcherTarget holes arms
      supply generated next)
    (supported : MatcherArmBodiesRuntimeSupported arms)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherArmsTyping definitionTypes (Ty.applyList solution captures)
      (matcherTarget.apply solution) (holes.map (RuntimeDual.apply solution))
      arms := by
  induction elaboration with
  | nil => exact .nil
  | cons head tail tailInduction =>
      cases supported with
      | cons headSupported tailSupported =>
          simp only [GeneratedChecks.runtimeSolution_append] at semantic
          exact .cons
            (head.toRuntimeMatcherArmTyping_of_m4Fuel headSupported semantic.1
              contextCompatible)
            (tailInduction tailSupported semantic.2)

theorem MatcherClauseElaboratesUsing.toRuntimeMatcherClauseTyping_of_m4Fuel
    (elaboration : MatcherClauseElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) PPatElaborates
      DPatElaborates Paper1FrozenSignature.signature context matcherTarget clause
      supply generated next)
    (supported : MatcherClauseRuntimeExpressionsSupported clause)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClauseTyping definitionTypes (matcherTarget.apply solution)
      clause := by
  cases elaboration with
  | mk shape headerElaboration nextElaboration armsElaboration =>
      rename_i header nextMatcher arms generatedHeader afterHeader generatedNext
        afterNext generatedArms
      cases supported with
      | mk nextSupported armsSupported =>
          have headerSolved : Solves solution generatedHeader.hard := by
            intro equation member
            exact semantic.1 equation (by simp [member])
          have nextSemantic : generatedNext.RuntimeSolution solution := by
            constructor
            · intro equation member
              exact semantic.1 equation (by simp [member])
            · intro obligation member
              exact semantic.2 obligation (by simp [member])
          have armsSemantic : generatedArms.checks.RuntimeSolution solution := by
            constructor
            · intro equation member
              exact semantic.1 equation (by simp [member])
            · intro obligation member
              exact semantic.2 obligation (by simp [member])
          have nextContextCompatible :=
            runtimeContextCompatible_extendPatternContext
              (bindings := generatedHeader.captures) contextCompatible
          exact .mk
            (headerElaboration.toRuntimePPatTyping headerSolved)
            (nextElaboration.toRuntimeNextMatchersTyping_of_m4Fuel nextSupported
              nextSemantic nextContextCompatible)
            (armsElaboration.toRuntimeMatcherArmsTyping_of_m4Fuel armsSupported
              armsSemantic contextCompatible)

theorem MatcherClausesElaborateUsing.toRuntimeMatcherClausesTyping_of_m4Fuel
    (elaboration : MatcherClausesElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) PPatElaborates
      DPatElaborates Paper1FrozenSignature.signature context matcherTarget clauses
      supply generated next)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClausesTyping definitionTypes (matcherTarget.apply solution)
      clauses := by
  induction elaboration with
  | nil => exact .nil
  | cons head tail tailInduction =>
      cases supported with
      | cons headSupported tailSupported =>
          simp only [GeneratedChecks.runtimeSolution_append] at semantic
          exact .cons
            (head.toRuntimeMatcherClauseTyping_of_m4Fuel headSupported semantic.1
              contextCompatible)
            (tailInduction tailSupported semantic.2)

/-! ## Callback-parametric recursive clause bridge -/

theorem NextMatcherItemsElaborateUsing.toTotalExpressionTypings_of_m4Fuel
    (elaboration : NextMatcherItemsElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      context expressions holes supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    RuntimeCaptureExpressionsTyping expressionTyping runtimeContext expressions
      (holes.map (fun hole => .slot
        (hole.capability.apply solution.cap) (hole.target.apply solution))) := by
  induction elaboration with
  | nil => exact .nil
  | cons head tail induction =>
      simp only [GeneratedChecks.runtimeSolution_append] at semantic
      exact .cons (by
        simpa [RuntimeDual.apply, Ty.apply] using
          bridge.checked head semantic.1 contextCompatible)
        (induction semantic.2)

theorem NextMatchersElaborateUsing.toTotalRuntimeNextMatchersTyping_of_m4Fuel
    (elaboration : NextMatchersElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
      context expression holes supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    TotalRuntimeNextMatchersTyping expressionTyping runtimeContext expression
      (holes.map (RuntimeDual.apply solution)) := by
  constructor
  cases elaboration with
  | zero checked =>
      simpa [runtimeMatcherProductTarget, runtimeProductTarget,
        RuntimeDual.apply, Ty.apply, Ty.applyList] using
        bridge.checked checked semantic contextCompatible
  | one checked =>
      simpa [runtimeMatcherProductTarget, runtimeProductTarget,
        RuntimeDual.apply, Ty.apply] using
        bridge.checked checked semantic contextCompatible
  | @many items first second rest itemSupply itemGenerated itemNext components =>
      apply bridge.tuple
      have targetsEq :
          ((first :: second :: rest).map (RuntimeDual.apply solution)).map
              (fun hole => Ty.slot hole.capability hole.target) =
            (first :: second :: rest).map (fun hole =>
              Ty.slot (hole.capability.apply solution.cap)
                (hole.target.apply solution)) := by
        simp [List.map_map, Function.comp_def, RuntimeDual.apply]
      change RuntimeCaptureExpressionsTyping expressionTyping runtimeContext items
        (((first :: second :: rest).map (RuntimeDual.apply solution)).map
          (fun hole => Ty.slot hole.capability hole.target))
      rw [targetsEq]
      exact components.toTotalExpressionTypings_of_m4Fuel bridge semantic
        contextCompatible

theorem MatcherArmElaboratesUsing.toTotalRuntimeMatcherArmTyping_of_m4Fuel
    (elaboration : MatcherArmElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) DPatElaborates
      Paper1FrozenSignature.signature context captures matcherTarget holes arm
      supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalRuntimeMatcherArmTyping expressionTyping definitionTypes
      (Ty.applyList solution captures) (matcherTarget.apply solution)
      (holes.map (RuntimeDual.apply solution)) arm := by
  cases elaboration with
  | mk headerElaboration bodyElaboration =>
      rename_i header body generatedHeader afterHeader generatedBody
      have headerSolved : Solves solution generatedHeader.hard := by
        intro equation member
        exact semantic.1 equation (by simp [member])
      have bodySemantic : generatedBody.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · exact semantic.2
      have captureContextCompatible :=
        runtimeContextCompatible_extendPatternContext
          (bindings := captures) contextCompatible
      have bodyContextCompatible :=
        runtimeContextCompatible_extendPatternContext
          (bindings := generatedHeader.bindings) captureContextCompatible
      apply TotalRuntimeMatcherArmTyping.mk
        (headerElaboration.toRuntimeDPatTyping headerSolved)
      simpa [DataTypes.list, Ty.apply, Ty.applyList, List.append_assoc,
        runtimeHoleProductTarget, RuntimeDual.apply] using
        bridge.checked bodyElaboration bodySemantic bodyContextCompatible

theorem MatcherArmsElaborateUsing.toTotalRuntimeMatcherArmsTyping_of_m4Fuel
    (elaboration : MatcherArmsElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) DPatElaborates
      Paper1FrozenSignature.signature context captures matcherTarget holes arms
      supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalRuntimeMatcherArmsTyping expressionTyping definitionTypes
      (Ty.applyList solution captures) (matcherTarget.apply solution)
      (holes.map (RuntimeDual.apply solution)) arms := by
  induction elaboration with
  | nil => exact .nil
  | cons head tail induction =>
      simp only [GeneratedChecks.runtimeSolution_append] at semantic
      exact .cons
        (head.toTotalRuntimeMatcherArmTyping_of_m4Fuel bridge semantic.1
          contextCompatible)
        (induction semantic.2)

theorem MatcherClauseElaboratesUsing.toTotalRuntimeMatcherClauseTyping_of_m4Fuel
    (elaboration : MatcherClauseElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) PPatElaborates
      DPatElaborates Paper1FrozenSignature.signature context matcherTarget clause
      supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalRuntimeMatcherClauseTyping expressionTyping definitionTypes
      (matcherTarget.apply solution) clause := by
  cases elaboration with
  | mk shape headerElaboration nextElaboration armsElaboration =>
      rename_i header nextMatcher arms generatedHeader afterHeader generatedNext
        afterNext generatedArms
      have headerSolved : Solves solution generatedHeader.hard := by
        intro equation member
        exact semantic.1 equation (by simp [member])
      have nextSemantic : generatedNext.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · intro obligation member
          exact semantic.2 obligation (by simp [member])
      have armsSemantic : generatedArms.checks.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · intro obligation member
          exact semantic.2 obligation (by simp [member])
      have nextContextCompatible :=
        runtimeContextCompatible_extendPatternContext
          (bindings := generatedHeader.captures) contextCompatible
      exact .mk
        (headerElaboration.toRuntimePPatTyping headerSolved)
        (nextElaboration.toTotalRuntimeNextMatchersTyping_of_m4Fuel bridge
          nextSemantic nextContextCompatible)
        (armsElaboration.toTotalRuntimeMatcherArmsTyping_of_m4Fuel bridge
          armsSemantic contextCompatible)

theorem MatcherClausesElaborateUsing.toTotalRuntimeMatcherClausesTyping_of_m4Fuel
    (elaboration : MatcherClausesElaborateUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) PPatElaborates
      DPatElaborates Paper1FrozenSignature.signature context matcherTarget clauses
      supply generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalRuntimeMatcherClausesTyping expressionTyping definitionTypes
      (matcherTarget.apply solution) clauses := by
  induction elaboration with
  | nil => exact .nil
  | cons head tail induction =>
      simp only [GeneratedChecks.runtimeSolution_append] at semantic
      exact .cons
        (head.toTotalRuntimeMatcherClauseTyping_of_m4Fuel bridge semantic.1
          contextCompatible)
        (induction semantic.2)

/-- Recursive-M4 matcher literal bridge.  Unlike the earlier runtime-fragment
endpoint, this stores the caller's recursive expression judgment in the
closure certificate and therefore admits `matchAll`/`matchFirst` leaves. -/
theorem MatcherLiteralElaboratesUsing.toTotalMatcherClausesTyping_of_m4Fuel
    (elaboration : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) PPatElaborates
      DPatElaborates Paper1FrozenSignature.signature context clauses supply
      generated next)
    (bridge : SolvedM4CheckedExpressionBridge expressionTyping)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalRuntimeMatcherClausesTyping expressionTyping definitionTypes
      ((Ty.var ⟨supply.ty⟩).apply solution) clauses := by
  cases elaboration with
  | mk checked clausesElaboration =>
      rename_i generatedClauses
      have clausesSemantic :
          generatedClauses.checks.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · exact semantic.2
      exact clausesElaboration
        |>.toTotalRuntimeMatcherClausesTyping_of_m4Fuel bridge clausesSemantic
          contextCompatible

/-- Fixed-signature recursive-M4 matcher literal bridge for runtime-supported
leaves.  This removes the old M3 matcher-elaboration anchor without claiming
that recursive matching bodies are ordinary `RuntimeTyping`. -/
theorem MatcherLiteralElaboratesUsing.toTotalCoreTyping_of_m4Fuel
    (elaboration : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel) PPatElaborates
      DPatElaborates Paper1FrozenSignature.signature context clauses supply
      generated next)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    TotalCoreTyping (.matcher clauses)
      (.matcher .any ((Ty.var ⟨supply.ty⟩).apply solution))
      definitionTypes := by
  cases elaboration with
  | mk checked clausesElaboration =>
      rename_i generatedClauses
      have clausesSemantic :
          generatedClauses.checks.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · exact semantic.2
      exact .matcher
        (clausesElaboration.toRuntimeMatcherClausesTyping_of_m4Fuel supported
          clausesSemantic contextCompatible)

theorem MatcherLiteralElaboratesUsing.neverStuck_of_m4Fuel
    (elaboration : MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel Paper1FrozenSignature.signature elaborationFuel)
      PPatElaborates DPatElaborates Paper1FrozenSignature.signature [] clauses
      supply generated next)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.SemanticSolution solution)
    (fuel : Nat) :
    (evalFuel fuel [] (.matcher clauses)).NotStuck :=
  (elaboration.toTotalCoreTyping_of_m4Fuel supported semantic
    MonomorphicContextCompatible.nil).neverStuck fuel [] .nil

end TypePM.Source.MatcherTyping
