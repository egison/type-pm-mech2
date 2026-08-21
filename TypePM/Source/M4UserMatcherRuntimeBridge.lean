import TypePM.Source.M4MatcherTyping
import TypePM.Source.FrozenSignatureRuntimeCompatibility
import TypePM.UserMatcherGeneralSafety

/-!
# M4 user-matcher certificates at the runtime boundary

This module translates solved relational M4 matcher-pattern elaborations under
a runtime-compatible frozen signature into evaluator-facing certificates.
It does not infer runtime expression typing from arbitrary M4 expressions;
arm and clause bridges below keep that premise explicit.
-/

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- The same M4 lookup/opening evidence in the public scheme-instance shape
used by later static bridges. -/
theorem runtimeDataConstructorSchemeInstance_of_m4
    {signature : FrozenSignature}
    (compatible : FrozenSignatureRuntimeCompatible signature)
    {constructor : DataCtor} {scheme : Scheme} {supply : Supply}
    {arity : Nat} {fieldTypes : List Ty} {resultType expected : Ty}
    (lookup : signature.lookupDataConstructor constructor = some scheme)
    (fieldArity : arity = scheme.callArity)
    (peel : peelFunctionExact arity (scheme.instantiate supply).1 =
      some (fieldTypes, resultType))
    (resultSolved :
      (Equation.ty resultType expected).Holds solution) :
    RuntimeDataConstructorSchemeInstance constructor
      (Ty.applyList solution fieldTypes) (expected.apply solution) :=
  (compatible.dataConstructorTyping_of_m4 lookup fieldArity peel
    resultSolved).schemeInstance

private theorem tyApplyList_append (left right : List Ty) :
    Ty.applyList solution (left ++ right) =
      Ty.applyList solution left ++ Ty.applyList solution right := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp [Ty.applyList, induction]

mutual

  /-- A solved M4 pattern-pattern elaboration is an evaluator-facing header
  certificate.  Mapping preserves the left-to-right hole and capture order. -/
  theorem PPatElaborates.toRuntimePPatTyping
      (elaboration : PPatElaborates signature pattern
        expectedTarget expectedCapability supply generated next)
      (solved : Solves solution generated.hard) :
      RuntimePPatTyping pattern (expectedTarget.apply solution)
        (generated.holes.map (RuntimeDual.apply solution))
        (Ty.applyList solution generated.captures) := by
    cases elaboration with
    | hole =>
        simpa [RuntimeDual.apply, Ty.applyList] using
          (RuntimePPatTyping.hole
            ((Cap.var ⟨supply.cap⟩).apply solution.cap) :
            RuntimePPatTyping .hole (expectedTarget.apply solution)
              [⟨(Cap.var ⟨supply.cap⟩).apply solution.cap,
                expectedTarget.apply solution⟩] [])
    | wild =>
        simpa [Ty.applyList] using
          (RuntimePPatTyping.wild :
            RuntimePPatTyping .wild (expectedTarget.apply solution) [] [])
    | capture =>
        simpa [Ty.applyList] using
          (RuntimePPatTyping.capture :
            RuntimePPatTyping .capture (expectedTarget.apply solution) []
              [expectedTarget.apply solution])
    | ctor lookup arity fieldsElaboration =>
        apply RuntimePPatTyping.ctor
        exact PPatsElaborate.toRuntimePPatsTyping fieldsElaboration (by
          intro equation member
          exact solved equation (by simp [member]))

  /-- List counterpart of `PPatElaborates.toRuntimePPatTyping`; field targets,
  holes, and captures all retain source order. -/
  theorem PPatsElaborate.toRuntimePPatsTyping
      (elaboration : PPatsElaborate signature patterns
        expected supply generated next)
      (solved : Solves solution generated.hard) :
      RuntimePPatsTyping patterns
        (Ty.applyList solution (Dual.targets expected))
        (generated.holes.map (RuntimeDual.apply solution))
        (Ty.applyList solution generated.captures) := by
    cases elaboration with
    | nil =>
        simpa [Dual.targets, Ty.applyList] using
          (RuntimePPatsTyping.nil : RuntimePPatsTyping [] [] [] [])
    | cons head tail =>
        simp only [solves_append] at solved
        exact (by
          simpa [Dual.targets, Ty.applyList, tyApplyList_append,
            List.map_append] using
            RuntimePPatsTyping.cons
              (PPatElaborates.toRuntimePPatTyping head solved.1)
              (PPatsElaborate.toRuntimePPatsTyping tail solved.2))

end

mutual

  /-- A solved M4 data-pattern elaboration yields the runtime pattern
  certificate, including an explicit canonical constructor certificate. -/
  theorem DPatElaborates.toRuntimeDPatTyping
      (elaboration : DPatElaborates signature pattern
        expected supply generated next)
      (compatible : FrozenSignatureRuntimeCompatible signature)
      (solved : Solves solution generated.hard) :
      RuntimeDPatTyping pattern (expected.apply solution)
        (Ty.applyList solution generated.bindings) := by
    cases elaboration with
    | var =>
        simpa [Ty.applyList] using
          (RuntimeDPatTyping.var : RuntimeDPatTyping .var
            (expected.apply solution) [expected.apply solution])
    | wild =>
        simpa [Ty.applyList] using
          (RuntimeDPatTyping.wild : RuntimeDPatTyping .wild
            (expected.apply solution) [])
    | ctor lookup arity peel fieldsElaboration =>
        simp only [List.singleton_append, solves_cons] at solved
        exact RuntimeDPatTyping.ctor
          (compatible.dataConstructorTyping_of_m4 lookup arity peel solved.1)
          (DPatsElaborate.toRuntimeDPatsTyping fieldsElaboration compatible
            solved.2)
    | tuple fieldsEquality itemsElaboration =>
        simp only [List.singleton_append, solves_cons] at solved
        have itemsTyping :=
          DPatsElaborate.toRuntimeDPatsTyping itemsElaboration compatible solved.2
        simp only [Equation.Holds] at solved
        rw [solved.1]
        simpa [Ty.apply, Ty.applyList] using
          RuntimeDPatTyping.tuple itemsTyping

  /-- List counterpart of `DPatElaborates.toRuntimeDPatTyping`; constructor
  fields and synthesized bindings stay left-to-right. -/
  theorem DPatsElaborate.toRuntimeDPatsTyping
      (elaboration : DPatsElaborate signature patterns
        expected supply generated next)
      (compatible : FrozenSignatureRuntimeCompatible signature)
      (solved : Solves solution generated.hard) :
      RuntimeDPatsTyping patterns (Ty.applyList solution expected)
        (Ty.applyList solution generated.bindings) := by
    cases elaboration with
    | nil =>
        simpa [Ty.applyList] using
          (RuntimeDPatsTyping.nil : RuntimeDPatsTyping [] [] [])
    | cons head tail =>
        simp only [solves_append] at solved
        exact (by
          simpa [Ty.applyList, tyApplyList_append] using RuntimeDPatsTyping.cons
            (DPatElaborates.toRuntimeDPatTyping head compatible solved.1)
            (DPatsElaborate.toRuntimeDPatsTyping tail compatible solved.2))

end

namespace GeneratedChecks

/-- The exact semantic evidence needed to erase an M4 checked-expression
block to runtime typing: every hard equation is solved and every delayed
check has a concrete runtime conversion. -/
def RuntimeSolution (generated : GeneratedChecks) (solution : Subst) : Prop :=
  Solves solution generated.hard ∧
    ∀ obligation ∈ generated.pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)

@[simp] theorem runtimeSolution_empty :
    GeneratedChecks.empty.RuntimeSolution solution := by
  simp [RuntimeSolution, GeneratedChecks.empty]

@[simp] theorem runtimeSolution_append :
    (GeneratedChecks.append left right).RuntimeSolution solution ↔
      RuntimeSolution left solution ∧ RuntimeSolution right solution := by
  constructor
  · intro semantic
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro equation member
      exact semantic.1 equation (by
        simp [GeneratedChecks.append, member])
    · intro obligation member
      exact semantic.2 obligation (by
        simp [GeneratedChecks.append, member])
    · intro equation member
      exact semantic.1 equation (by
        simp [GeneratedChecks.append, member])
    · intro obligation member
      exact semantic.2 obligation (by
        simp [GeneratedChecks.append, member])
  · rintro ⟨leftSemantic, rightSemantic⟩
    constructor
    · intro equation member
      simp only [GeneratedChecks.append, List.mem_append] at member
      exact member.elim (leftSemantic.1 equation) (rightSemantic.1 equation)
    · intro obligation member
      simp only [GeneratedChecks.append, List.mem_append] at member
      exact member.elim (leftSemantic.2 obligation)
        (rightSemantic.2 obligation)

end GeneratedChecks

/-- `Pattern.extendContext` and runtime environment concatenation agree after
solving, including the newest-first and source-order convention. -/
theorem runtimeContextCompatible_extendPatternContext
    (compatible : MonomorphicContextCompatible context runtimeContext solution) :
    MonomorphicContextCompatible (Pattern.extendContext bindings context)
      (Ty.applyList solution bindings ++ runtimeContext) solution := by
  induction bindings with
  | nil =>
      simpa [Pattern.extendContext, Ty.applyList] using compatible
  | cons binding bindings induction =>
      simpa [Pattern.extendContext, Ty.applyList] using
        (MonomorphicContextCompatible.cons induction)

/-- A checked M3 expression leaf in the M4 matcher relation erases to runtime
typing once its hard and delayed checks are semantically discharged. -/
theorem CheckedExpressionElaborates.toRuntimeTyping
    (elaboration : CheckedExpressionElaborates
      signature context expression expected supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : RuntimeSupported expression)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    RuntimeTyping expression (expected.apply solution) runtimeContext := by
  induction elaboration with
  | @mk sourceGenerated _ sourceElaboration =>
      have sourceSemantic : Generated.SemanticSolution sourceGenerated solution := by
        constructor
        · exact semantic.1
        · intro obligation member
          exact semantic.2 obligation (by
            simp [GeneratedChecks.checked, member])
      have sourceTyping := supported.elaboration_typing
        (signature := signature.base)
        compatible.toSignatureCompatible sourceElaboration sourceSemantic
        contextCompatible
      obtain ⟨conversionClass, conversion⟩ := semantic.2
        ⟨sourceGenerated.target, expected⟩ (by
          simp [GeneratedChecks.checked])
      exact RuntimeTyping.checked sourceTyping conversion

/-- Solving commutes with the shared zero/one/many hole-product convention. -/
@[simp] theorem holeProductTarget_apply (holes : List Dual) :
    (holeProductTarget holes).apply solution =
      runtimeHoleProductTarget (holes.map (RuntimeDual.apply solution)) := by
  cases holes with
  | nil =>
      simp [holeProductTarget, runtimeHoleProductTarget, Ty.apply, Ty.applyList]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [holeProductTarget, runtimeHoleProductTarget, RuntimeDual.apply]
      | cons second rest =>
          simp [holeProductTarget, runtimeHoleProductTarget, Ty.apply,
            RuntimeDual.targets_apply]

/-- Runtime slot types for a solved, source-ordered hole list. -/
def solvedHoleSlotTypes (solution : Subst) (holes : List Dual) : List Ty :=
  (holes.map (RuntimeDual.apply solution)).map
    (fun hole => .slot hole.capability hole.target)

/-- Checked components of a many-hole next-matcher tuple retain source order
and become pointwise runtime typings at the solved slot types. -/
theorem NextMatcherItemsElaborate.toRuntimeTypings
    (elaboration : NextMatcherItemsElaborate
      signature context expressions holes supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
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
          have headTyping := head.toRuntimeTyping compatible headSupported
            semantic.1 contextCompatible
          have tailTyping := tailInduction tailSupported semantic.2
          simpa [solvedHoleSlotTypes, RuntimeDual.apply, Ty.apply] using
            RuntimeTypings.cons headTyping tailTyping

/-- The relational M4 zero/one/many next-matcher check becomes the exact
runtime decoder certificate after solving. -/
theorem NextMatchersElaborate.toRuntimeNextMatchersTyping
    (elaboration : NextMatchersElaborate
      signature context expression holes supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : RuntimeSupported expression)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution) :
    RuntimeNextMatchersTyping runtimeContext expression
      (holes.map (RuntimeDual.apply solution)) := by
  cases elaboration with
  | zero checked =>
      exact .zero
  | one checked =>
      apply RuntimeNextMatchersTyping.one
      simpa [RuntimeDual.apply, Ty.apply] using
        checked.toRuntimeTyping compatible supported semantic contextCompatible
  | many components =>
      cases supported with
      | tuple itemsSupported =>
          apply RuntimeNextMatchersTyping.many
          simpa [solvedHoleSlotTypes] using
            components.toRuntimeTypings compatible itemsSupported semantic
              contextCompatible

/-- Runtime syntax coverage for source-ordered matcher-arm bodies. -/
inductive MatcherArmBodiesRuntimeSupported : List MatcherArm → Prop where
  | nil : MatcherArmBodiesRuntimeSupported []
  | cons
      (head : RuntimeSupported arm.body)
      (tail : MatcherArmBodiesRuntimeSupported arms) :
      MatcherArmBodiesRuntimeSupported (arm :: arms)

/-- Runtime syntax coverage for all expression leaves of one matcher clause.
This is intentionally separate from M4 elaboration and semantic solving. -/
inductive MatcherClauseRuntimeExpressionsSupported : MatcherClause → Prop where
  | mk
      (nextMatcher : RuntimeSupported nextMatcherExpression)
      (armBodies : MatcherArmBodiesRuntimeSupported arms) :
      MatcherClauseRuntimeExpressionsSupported
        (.mk header nextMatcherExpression arms)

/-- Runtime syntax coverage for a source-ordered clause list. -/
inductive MatcherClausesRuntimeExpressionsSupported :
    List MatcherClause → Prop where
  | nil : MatcherClausesRuntimeExpressionsSupported []
  | cons
      (head : MatcherClauseRuntimeExpressionsSupported clause)
      (tail : MatcherClausesRuntimeExpressionsSupported clauses) :
      MatcherClausesRuntimeExpressionsSupported (clause :: clauses)

/-- One solved M4 arm becomes a runtime arm certificate.  Its expression body
is checked under bindings, captures, and the definition context in precisely
that order. -/
theorem MatcherArmElaborates.toRuntimeMatcherArmTyping
    (elaboration : MatcherArmElaborates signature
      context captures matcherTarget holes arm supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : RuntimeSupported arm.body)
    (semantic : generated.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherArmTyping definitionTypes
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
      have bodyTyping := bodyElaboration.toRuntimeTyping compatible supported
        bodySemantic bodyContextCompatible
      apply RuntimeMatcherArmTyping.mk
        (headerElaboration.toRuntimeDPatTyping compatible headerSolved)
      simpa [DataTypes.list, Ty.apply, Ty.applyList, List.append_assoc] using
        bodyTyping

/-- Source-ordered list lifting for M4 matcher arms. -/
theorem MatcherArmsElaborate.toRuntimeMatcherArmsTyping
    (elaboration : MatcherArmsElaborate signature
      context captures matcherTarget holes arms supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : MatcherArmBodiesRuntimeSupported arms)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherArmsTyping definitionTypes
      (Ty.applyList solution captures) (matcherTarget.apply solution)
      (holes.map (RuntimeDual.apply solution)) arms := by
  induction elaboration with
  | nil => exact .nil
  | cons head tail tailInduction =>
      cases supported with
      | cons headSupported tailSupported =>
          simp only [GeneratedChecks.runtimeSolution_append] at semantic
          exact .cons
            (head.toRuntimeMatcherArmTyping compatible headSupported semantic.1
              contextCompatible)
            (tailInduction tailSupported semantic.2)

/-- A solved M4 clause becomes the runtime clause certificate shared by
preservation and progress.  Header captures are placed before definition
types for the next matcher, while arm bindings precede both. -/
theorem MatcherClauseElaborates.toRuntimeMatcherClauseTyping
    (elaboration : MatcherClauseElaborates signature
      context matcherTarget clause supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
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
          exact RuntimeMatcherClauseTyping.mk
            (headerElaboration.toRuntimePPatTyping headerSolved)
            (nextElaboration.toRuntimeNextMatchersTyping compatible nextSupported
              nextSemantic nextContextCompatible)
            (armsElaboration.toRuntimeMatcherArmsTyping compatible armsSupported
              armsSemantic contextCompatible)

/-- Source-ordered clause-list lifting. -/
theorem MatcherClausesElaborate.toRuntimeMatcherClausesTyping
    (elaboration : MatcherClausesElaborate signature
      context matcherTarget clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
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
            (head.toRuntimeMatcherClauseTyping compatible headSupported
              semantic.1 contextCompatible)
            (tailInduction tailSupported semantic.2)

/-- Literal-level bridge: the solved M4 matcher target determines the target
shared by the runtime clause list.  Runtime expression typing has no matcher
literal constructor yet, so the honest conclusion is the complete clause
certificate rather than a `RuntimeTyping (.matcher ...)` claim. -/
theorem MatcherLiteralElaborates.toRuntimeMatcherClausesTyping
    (elaboration : MatcherLiteralElaborates signature
      context clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClausesTyping definitionTypes
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
      exact clausesElaboration.toRuntimeMatcherClausesTyping compatible
        supported clausesSemantic contextCompatible

/-! ## Capture-aware input certificates

The ordinary M4 relation types the header and its embedded expressions, but
does not yet carry the enclosing source-pattern derivation that justifies the
expressions returned by `inspectPatternPattern`.  The following enriched
relations retain exactly that missing premise.  They copy no weaker header or
constructor rule: every constructor contains the original M4 derivations.
-/

/-- One M4 clause elaboration plus the exact runtime typing of capture
expressions exposed by header inspection for a particular input pattern. -/
inductive MatcherClauseRuntimeInputElaborates
    (signature : FrozenSignature) (solution : Subst)
    (atomEnvironmentTypes : List Ty) (pattern : Pattern)
    (context : Context) (matcherTarget : Ty) :
    MatcherClause → Supply → GeneratedMatcherClause → Supply → Prop where
  | mk {header nextMatchers arms supply generatedHeader afterHeader generatedNext
      afterNext generatedArms next}
      (shape : (MatcherClause.mk header nextMatchers arms).toShape.check
        signature = true)
      (headerElaboration : PPatElaborates signature
        header matcherTarget none supply generatedHeader afterHeader)
      (nextElaboration : NextMatchersElaborate signature
        (Pattern.extendContext generatedHeader.captures context)
        nextMatchers generatedHeader.holes afterHeader generatedNext afterNext)
      (armsElaboration : MatcherArmsElaborate
        signature context generatedHeader.captures
        matcherTarget generatedHeader.holes arms afterNext generatedArms next)
      (captures : ∀ {dispatch},
        inspectPatternPattern header pattern = some dispatch →
        RuntimeCaptureExpressionsTyping
          (fun runtimeContext expression target =>
            RuntimeTyping expression target runtimeContext)
          atomEnvironmentTypes dispatch.captures
          (Ty.applyList solution generatedHeader.captures)) :
      MatcherClauseRuntimeInputElaborates signature solution
        atomEnvironmentTypes pattern context matcherTarget
        (.mk header nextMatchers arms) supply
        ⟨generatedHeader.holes, generatedHeader.evidence,
          ⟨generatedHeader.hard ++ generatedNext.hard ++
              generatedArms.checks.hard,
            generatedNext.pending ++ generatedArms.checks.pending⟩⟩ next

/-- Source-order list form of the capture-aware M4 relation. -/
inductive MatcherClausesRuntimeInputElaborate
    (signature : FrozenSignature) (solution : Subst)
    (atomEnvironmentTypes : List Ty) (pattern : Pattern)
    (context : Context) (matcherTarget : Ty) :
    List MatcherClause → Supply → GeneratedMatcherClauses → Supply → Prop where
  | nil {supply} :
      MatcherClausesRuntimeInputElaborate signature solution
        atomEnvironmentTypes pattern context matcherTarget [] supply
        ⟨[], GeneratedChecks.empty⟩ supply
  | cons {clause clauses supply generatedClause afterClause generatedClauses next}
      (head : MatcherClauseRuntimeInputElaborates signature solution
        atomEnvironmentTypes pattern context matcherTarget clause supply
        generatedClause afterClause)
      (tail : MatcherClausesRuntimeInputElaborate signature solution
        atomEnvironmentTypes pattern context matcherTarget clauses afterClause
        generatedClauses next) :
      MatcherClausesRuntimeInputElaborate signature solution
        atomEnvironmentTypes pattern context matcherTarget (clause :: clauses) supply
        ⟨match generatedClause.evidence with
          | some evidence => evidence :: generatedClauses.evidences
          | none => generatedClauses.evidences,
          generatedClause.checks.append generatedClauses.checks⟩ next

/-- Matcher-literal form of the capture-aware relation. -/
inductive MatcherLiteralRuntimeInputElaborates
    (signature : FrozenSignature) (solution : Subst)
    (atomEnvironmentTypes : List Ty) (pattern : Pattern)
    (context : Context) :
    List MatcherClause → Supply → Generated → Supply → Prop where
  | mk {clauses supply generatedClauses next}
      (checked : StaticChecksHold signature clauses)
      (clausesElaboration : MatcherClausesRuntimeInputElaborate signature
        solution atomEnvironmentTypes pattern context (.var ⟨supply.ty⟩) clauses
        ⟨supply.ty + 1, supply.cap + 1⟩ generatedClauses next) :
      MatcherLiteralRuntimeInputElaborates signature solution
        atomEnvironmentTypes pattern context clauses supply
        ⟨.matcher (.var ⟨supply.cap⟩) (.var ⟨supply.ty⟩),
          evidenceEquations (.var ⟨supply.cap⟩) generatedClauses.evidences ++
            generatedClauses.checks.hard,
          generatedClauses.checks.pending⟩ next

theorem MatcherClauseRuntimeInputElaborates.elaboration
    (input : MatcherClauseRuntimeInputElaborates signature solution
      atomEnvironmentTypes pattern context matcherTarget clause supply generated
      next) :
    MatcherClauseElaborates signature context matcherTarget
      clause supply generated next := by
  cases input with
  | mk shape header nextMatchers arms captures =>
      exact .mk (MatcherClauseShape.wellFormed_of_check shape)
        header nextMatchers arms

theorem MatcherClausesRuntimeInputElaborate.elaboration
    (input : MatcherClausesRuntimeInputElaborate signature solution
      atomEnvironmentTypes pattern context matcherTarget clauses supply generated
      next) :
    MatcherClausesElaborate signature context matcherTarget
      clauses supply generated next := by
  induction input with
  | nil => exact .nil
  | cons head tail tailInduction =>
      exact .cons head.elaboration tailInduction

theorem MatcherLiteralRuntimeInputElaborates.elaboration
    (input : MatcherLiteralRuntimeInputElaborates signature solution
      atomEnvironmentTypes pattern context clauses supply generated next) :
    MatcherLiteralElaborates signature context clauses
      supply generated next := by
  cases input with
  | mk checked clauses => exact .mk checked clauses.elaboration

/-- Capture-aware one-clause bridge to the exact input certificate consumed
by general dispatch safety. -/
theorem MatcherClauseRuntimeInputElaborates.toRuntimeMatcherClauseInputTyping
    (input : MatcherClauseRuntimeInputElaborates signature solution
      atomEnvironmentTypes pattern context matcherTarget clause supply generated
      next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : MatcherClauseRuntimeExpressionsSupported clause)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClauseInputTyping atomEnvironmentTypes definitionTypes
      (matcherTarget.apply solution) pattern clause := by
  cases input with
  | mk shape headerElaboration nextElaboration armsElaboration captures =>
      rename_i header nextMatchers arms generatedHeader afterHeader generatedNext
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
            (nextElaboration.toRuntimeNextMatchersTyping compatible nextSupported
              nextSemantic nextContextCompatible)
            (armsElaboration.toRuntimeMatcherArmsTyping compatible armsSupported
              armsSemantic contextCompatible)
            captures

/-- Capture-aware source-order clause-list bridge. -/
theorem MatcherClausesRuntimeInputElaborate.toRuntimeMatcherClausesInputTyping
    (input : MatcherClausesRuntimeInputElaborate signature solution
      atomEnvironmentTypes pattern context matcherTarget clauses supply generated
      next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.checks.RuntimeSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClausesInputTyping atomEnvironmentTypes definitionTypes
      (matcherTarget.apply solution) pattern clauses := by
  induction input with
  | nil => exact .nil
  | cons head tail tailInduction =>
      cases supported with
      | cons headSupported tailSupported =>
          simp only [GeneratedChecks.runtimeSolution_append] at semantic
          exact .cons
            (head.toRuntimeMatcherClauseInputTyping compatible headSupported
              semantic.1 contextCompatible)
            (tailInduction tailSupported semantic.2)

/-- Capture-aware literal-level bridge.  This is the direct input certificate
for ordered runtime dispatch at one enclosing source pattern. -/
theorem MatcherLiteralRuntimeInputElaborates.toRuntimeMatcherClausesInputTyping
    (input : MatcherLiteralRuntimeInputElaborates signature solution
      atomEnvironmentTypes pattern context clauses supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : MatcherClausesRuntimeExpressionsSupported clauses)
    (semantic : generated.SemanticSolution solution)
    (contextCompatible :
      MonomorphicContextCompatible context definitionTypes solution) :
    RuntimeMatcherClausesInputTyping atomEnvironmentTypes definitionTypes
      ((Ty.var ⟨supply.ty⟩).apply solution) pattern clauses := by
  cases input with
  | mk checked clausesElaboration =>
      rename_i generatedClauses
      have clausesSemantic :
          generatedClauses.checks.RuntimeSolution solution := by
        constructor
        · intro equation member
          exact semantic.1 equation (by simp [member])
        · exact semantic.2
      exact clausesElaboration.toRuntimeMatcherClausesInputTyping compatible
        supported clausesSemantic contextCompatible

end TypePM.Source.MatcherTyping
