import TypePM.Source.M4UserMatcherRuntimeBridge
import TypePM.CommonFuelSafety

/-!
# M4 source-pattern information at the runtime atom boundary

`DelegatedMatchingAtomsTyping` proves the matcher and target value types of a
branch returned by a user matcher, but deliberately erases the source
patterns placed in that branch.  This module records why an unrestricted
callback over that erased certificate is too strong, then defines the
pattern-indexed certificate needed by a sound M4 bridge.

The obstruction is not specific to M4.  An erased certificate can fabricate
a variable pattern even when dispatch actually preserved a wildcard.  A
wildcard atom contributes no binding, whereas that fabricated variable
necessarily contributes one.  `CommonFuelSafety` therefore links its branch
obligation to the concrete successful dispatch.  The indexed definitions
below retain the stronger information needed to derive that obligation from
M4 pattern elaboration rather than assuming an arbitrary erased callback.
-/

namespace TypePM.Source.MatcherTyping

open TypePM.Runtime

/-- Delegated branch typing that retains the source pattern paired with each
solved hole.  Unlike `DelegatedMatchingAtomsTyping`, its indices state the
exact pattern list that runtime `buildMatchingBranches` preserves. -/
inductive PatternIndexedDelegatedMatchingAtomsTyping :
    List MatchingAtom → List Pattern → List Dual → Prop where
  | nil : PatternIndexedDelegatedMatchingAtomsTyping [] [] []
  | cons
      (matcher : ValueTyping matcherValue
        (.slot hole.capability hole.target))
      (target : ValueTyping targetValue hole.target)
      (tail : PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes) :
      PatternIndexedDelegatedMatchingAtomsTyping
        (⟨pattern, matcherValue, targetValue⟩ :: atoms)
        (pattern :: patterns) (hole :: holes)

namespace PatternIndexedDelegatedMatchingAtomsTyping

/-- Erasing the pattern index recovers the existing dispatch certificate. -/
theorem erase
    (typing : PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes) :
    DelegatedMatchingAtomsTyping atoms holes := by
  induction typing with
  | nil => exact .nil
  | cons matcher target tail induction =>
      exact .cons matcher target induction

/-- The pattern index gives the exact source-order length equality used by
`buildMatchingBranches`. -/
theorem patterns_length
    (typing : PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes) :
    patterns.length = holes.length := by
  induction typing with
  | nil => rfl
  | cons matcher target tail induction => simp [induction]

end PatternIndexedDelegatedMatchingAtomsTyping

/-- Pattern-indexed counterpart of the runtime zip theorem.  This is the
sound output shape that an M4 source-pattern bridge needs. -/
theorem zipMatchingAtoms_patternIndexedTyped
    (length : patterns.length = holes.length)
    (matchersTyped : ValueTypings matcherValues
      (holes.map (fun hole => .slot hole.capability hole.target)))
    (targetsTyped : ValueTypings targetValues (Dual.targets holes)) :
    ∃ atoms,
      zipMatchingAtoms patterns matcherValues targetValues = some atoms ∧
      PatternIndexedDelegatedMatchingAtomsTyping atoms patterns holes := by
  induction holes generalizing patterns matcherValues targetValues with
  | nil =>
      cases matchersTyped
      cases targetsTyped
      simp at length
      subst patterns
      exact ⟨[], rfl, .nil⟩
  | cons hole holes induction =>
      cases matchersTyped with
      | cons matcherTyped matchersTyped =>
          cases targetsTyped with
          | cons targetTyped targetsTyped =>
              cases patterns with
              | nil => simp at length
              | cons pattern patterns =>
                  simp at length
                  obtain ⟨atoms, zipped, atomsTyped⟩ :=
                    induction length matchersTyped targetsTyped
                  exact ⟨⟨pattern, _, _⟩ :: atoms, by
                    simp [zipMatchingAtoms, zipped],
                    .cons matcherTyped targetTyped atomsTyped⟩

/-- Pattern-indexed branches retain one common pattern list for every
decomposition, exactly as `buildMatchingBranches` does. -/
inductive PatternIndexedDelegatedMatchingBranchesTyping
    (patterns : List Pattern) (holes : List Dual) : MatchingBranches → Prop where
  | nil : PatternIndexedDelegatedMatchingBranchesTyping patterns holes []
  | cons
      (head : PatternIndexedDelegatedMatchingAtomsTyping branch patterns holes)
      (tail : PatternIndexedDelegatedMatchingBranchesTyping patterns holes branches) :
      PatternIndexedDelegatedMatchingBranchesTyping patterns holes
        (branch :: branches)

/-- Pattern-indexed counterpart of `buildMatchingBranches_typed`. -/
theorem buildMatchingBranches_patternIndexedTyped
    (length : patterns.length = holes.length)
    (matchersTyped : ValueTypings matcherValues
      (holes.map (fun hole => .slot hole.capability hole.target)))
    (decompositionsTyped : HoleDecompositionsTyping holes decompositions) :
    ∃ branches,
      buildMatchingBranches patterns matcherValues decompositions = some branches ∧
      PatternIndexedDelegatedMatchingBranchesTyping patterns holes branches := by
  induction decompositionsTyped with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons targetValues decompositions targetsTyped tailTyped induction =>
      obtain ⟨branch, zipped, branchTyped⟩ :=
        zipMatchingAtoms_patternIndexedTyped length matchersTyped targetsTyped
      obtain ⟨branches, built, branchesTyped⟩ := induction
      change List.mapM (zipMatchingAtoms patterns matcherValues) decompositions =
        some branches at built
      exact ⟨branch :: branches, by
        simp [buildMatchingBranches, List.mapM_cons, zipped, built],
        .cons branchTyped branchesTyped⟩

/-! ## Solved M4 patterns in the built-in runtime fragment

The runtime `PatternBinds` judgment has rules for the structurally direct
fragment and for declared constructor patterns.  For conjunction the bridge
below transports the binding prefix produced by the left child into the right
child.  For disjunction it uses the solved pointwise binding equations to
prove that both alternatives contribute exactly the same binding types.
Pattern-function application and embedded pattern parameters remain outside
this fragment.
-/

mutual

  /-- Syntax coverage for the direct M4-to-`PatternBinds` fragment. -/
  inductive DirectRuntimePatternSupported : Pattern → Prop where
    | var : DirectRuntimePatternSupported .var
    | wild : DirectRuntimePatternSupported .wild
    | value {expression : Expr} (supported : RuntimeSupported expression) :
        DirectRuntimePatternSupported (.value expression)
    | ctor
        (fields : DirectRuntimePatternsSupported patterns) :
        DirectRuntimePatternSupported (.ctor constructor patterns)
    | tuple (items : DirectRuntimePatternsSupported patterns) :
        DirectRuntimePatternSupported (.tuple patterns)
    | and
        (left : DirectRuntimePatternSupported leftPattern)
        (right : DirectRuntimePatternSupported rightPattern) :
        DirectRuntimePatternSupported (.and leftPattern rightPattern)
    | or
        (left : DirectRuntimePatternSupported leftPattern)
        (right : DirectRuntimePatternSupported rightPattern) :
        DirectRuntimePatternSupported (.or leftPattern rightPattern)

  /-- List counterpart of `DirectRuntimePatternSupported`. -/
  inductive DirectRuntimePatternsSupported : List Pattern → Prop where
    | nil : DirectRuntimePatternsSupported []
    | cons
        (head : DirectRuntimePatternSupported pattern)
        (tail : DirectRuntimePatternsSupported patterns) :
        DirectRuntimePatternsSupported (pattern :: patterns)

end

/-- Semantic solution for all constraints emitted by one M4 pattern. -/
def GeneratedPatternRuntimeSolution
    (generated : GeneratedPattern) (solution : Subst) : Prop :=
  Solves solution generated.hard ∧
    ∀ obligation ∈ generated.pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)

/-- Semantic solution for all constraints emitted by an M4 pattern list. -/
def GeneratedPatternsRuntimeSolution
    (generated : GeneratedPatterns) (solution : Subst) : Prop :=
  Solves solution generated.hard ∧
    ∀ obligation ∈ generated.pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)

private theorem applyList_append_bridge (left right : List Ty) :
    Ty.applyList solution (left ++ right) =
      Ty.applyList solution left ++ Ty.applyList solution right := by
  induction left with
  | nil => rfl
  | cons head tail induction => simp [Ty.applyList, induction]

/-- Solved constructor-field equations identify the runtime target types of
the synthesized child patterns with those of the declared hole duals. -/
private theorem Pattern.fieldEquations_runtime_targets_eq
    (arity : actual.length = expected.length)
    (solved : Solves solution (Pattern.fieldEquations actual expected)) :
    Dual.targets (actual.map (RuntimeDual.apply solution)) =
      Dual.targets (expected.map (RuntimeDual.apply solution)) := by
  induction actual generalizing expected with
  | nil =>
      cases expected <;> simp at arity ⊢
  | cons actualHead actualTail induction =>
      cases expected with
      | nil => simp at arity
      | cons expectedHead expectedTail =>
          simp only [List.length_cons, Nat.succ.injEq] at arity
          have fieldsCons : Pattern.fieldEquations
              (actualHead :: actualTail) (expectedHead :: expectedTail) =
              [.ty actualHead.target expectedHead.target,
                .cap actualHead.capability expectedHead.capability] ++
                Pattern.fieldEquations actualTail expectedTail := rfl
          rw [fieldsCons, solves_append] at solved
          have headTarget :
              actualHead.target.apply solution =
                expectedHead.target.apply solution :=
            solved.1 (.ty actualHead.target expectedHead.target) (by simp)
          have tailTargets := induction arity solved.2
          change actualHead.target.apply solution ::
              Dual.targets (actualTail.map (RuntimeDual.apply solution)) =
            expectedHead.target.apply solution ::
              Dual.targets (expectedTail.map (RuntimeDual.apply solution))
          rw [headTarget, tailTargets]

private theorem patternsElaborate_duals_length
    (elaboration : PatternsElaborate signature context arguments patterns
      bindings supply generated next) :
    generated.duals.length = patterns.length := by
  refine @PatternsElaborate.rec signature context arguments
    (fun _ _ _ _ _ _ => True)
    (fun patterns _ _ generated _ _ =>
      generated.duals.length = patterns.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      patterns bindings supply generated next elaboration
  all_goals intros
  all_goals simp_all

/-- Solving the pointwise equations emitted for an or-pattern makes the two
source-ordered binding lists identical after substitution. -/
theorem Pattern.bindingEquations_runtime_eq
    (computed : Pattern.bindingEquations left right = some checks)
    (solved : Solves solution checks) :
    Ty.applyList solution left = Ty.applyList solution right := by
  induction left generalizing right checks with
  | nil =>
      cases right <;> simp [Pattern.bindingEquations] at computed ⊢
  | cons leftHead leftTail induction =>
      cases right with
      | nil => simp [Pattern.bindingEquations] at computed
      | cons rightHead rightTail =>
          simp only [Pattern.bindingEquations] at computed
          cases tailComputed : Pattern.bindingEquations leftTail rightTail with
          | none => simp [tailComputed] at computed
          | some tailChecks =>
              simp [tailComputed] at computed
              subst checks
              simp only [solves_cons] at solved
              have headEq : Ty.apply solution leftHead =
                  Ty.apply solution rightHead := by
                simpa only [Equation.Holds] using solved.1
              simp [Ty.applyList, headEq, induction tailComputed solved.2]

mutual

  /-- A solved relational M4 derivation in the direct runtime fragment becomes
  `PatternBinds`.  The equality records precisely how many solved binding
  types were appended to the incoming source-ordered prefix. -/
  theorem PatternElaborates.toDirectRuntimePatternBinds
      (elaboration : PatternElaborates signature context
        arguments pattern bindings supply generated next)
      (compatible : FrozenSignatureRuntimeCompatible signature)
      (supported : DirectRuntimePatternSupported pattern)
      (semantic : GeneratedPatternRuntimeSolution generated solution)
      (contextCompatible :
        MonomorphicContextCompatible context runtimeContext solution) :
      ∃ newBindings,
        PatternBinds
          (fun runtimeContext expression target =>
            RuntimeTyping expression target runtimeContext)
          runtimeContext (Ty.applyList solution bindings) pattern
          (generated.dual.target.apply solution) newBindings ∧
        Ty.applyList solution generated.bindings =
          Ty.applyList solution bindings ++ newBindings := by
    cases elaboration with
    | var =>
        cases supported
        refine ⟨[Ty.apply solution (.var ⟨supply.ty⟩)], .var, ?_⟩
        simp [Ty.applyList, applyList_append_bridge]
    | wild =>
        cases supported
        exact ⟨[], .wild, by simp⟩
    | value expressionElaboration =>
        cases supported with
        | value expressionSupported =>
            have expressionSemantic : Generated.SemanticSolution _ solution :=
              ⟨semantic.1, semantic.2⟩
            have extendedCompatible :=
              runtimeContextCompatible_extendPatternContext
                (bindings := bindings) contextCompatible
            have expressionTyping := expressionSupported.elaboration_typing
              compatible.toSignatureCompatible expressionElaboration
              expressionSemantic extendedCompatible
            exact ⟨[], .value expressionTyping, by simp⟩
    | ctor lookup arity fieldsElaboration =>
        rename_i scheme generatedFields
        cases supported with
        | ctor fieldsSupported =>
            have hardParts := (solves_append solution generatedFields.hard
              (Pattern.fieldEquations generatedFields.duals
                (scheme.instantiate supply).1.fields)).mp semantic.1
            obtain ⟨fieldBindings, fieldsTyping, bindingsEq⟩ :=
              TypePM.Source.MatcherTyping.PatternsElaborate.toDirectRuntimePatternsBind
                fieldsElaboration compatible fieldsSupported
                  ⟨hardParts.1, semantic.2⟩ contextCompatible
            have fieldArity : generatedFields.duals.length =
                (scheme.instantiate supply).1.fields.length := by
              rw [patternsElaborate_duals_length fieldsElaboration, arity]
              simp [DualScheme.instantiate]
            have targetTypesEq := Pattern.fieldEquations_runtime_targets_eq
              fieldArity hardParts.2
            have appliedTargetTypesEq :
                Ty.applyList solution (Dual.targets generatedFields.duals) =
                  Dual.targets ((scheme.instantiate supply).1.fields.map
                    (RuntimeDual.apply solution)) := by
              simpa using targetTypesEq
            rw [appliedTargetTypesEq] at fieldsTyping
            let declaration : PatternConstructorInstance _
                ((scheme.instantiate supply).1.fields.map
                  (RuntimeDual.apply solution))
                (RuntimeDual.apply solution
                  (scheme.instantiate supply).1.result) :=
              { signature := signature.base
                scheme := scheme
                supply := supply
                solution := solution
                declared := lookup
                holes_eq := rfl
                result_eq := rfl }
            exact ⟨fieldBindings,
              PatternBinds.ctor declaration fieldsTyping, bindingsEq⟩
    | tuple itemsElaboration =>
        cases supported with
        | tuple itemsSupported =>
            obtain ⟨newBindings, itemsTyping, bindingsEq⟩ :=
              TypePM.Source.MatcherTyping.PatternsElaborate.toDirectRuntimePatternsBind
                itemsElaboration compatible itemsSupported
                ⟨semantic.1, semantic.2⟩ contextCompatible
            refine ⟨newBindings, ?_, bindingsEq⟩
            simpa [Ty.apply, Ty.applyList] using PatternBinds.tuple itemsTyping
    | and left right =>
        rename_i generatedLeft afterLeft generatedRight
        cases supported with
        | and leftSupported rightSupported =>
            have hardParts :
                Solves solution generatedLeft.hard ∧
                Solves solution generatedRight.hard ∧
                Solves solution
                  (Pattern.dualEquations generatedLeft.dual generatedRight.dual) := by
              have outer := (solves_append solution
                (generatedLeft.hard ++ generatedRight.hard)
                (Pattern.dualEquations generatedLeft.dual
                  generatedRight.dual)).mp semantic.1
              have inner := (solves_append solution generatedLeft.hard
                generatedRight.hard).mp outer.1
              exact ⟨inner.1, inner.2, outer.2⟩
            have pendingParts :
                (∀ obligation ∈ generatedLeft.pending,
                  ∃ conversionClass,
                    CheckConversion conversionClass
                      (obligation.source.apply solution)
                      (obligation.expected.apply solution)) ∧
                (∀ obligation ∈ generatedRight.pending,
                  ∃ conversionClass,
                    CheckConversion conversionClass
                      (obligation.source.apply solution)
                      (obligation.expected.apply solution)) := by
              constructor <;> intro obligation member
              · exact semantic.2 obligation (by simp [member])
              · exact semantic.2 obligation (by simp [member])
            obtain ⟨leftBindings, leftTyping, leftBindingsEq⟩ :=
              TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
                left compatible leftSupported ⟨hardParts.1, pendingParts.1⟩
                  contextCompatible
            obtain ⟨rightBindings, rightTyping, rightBindingsEq⟩ :=
              TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
                right compatible rightSupported ⟨hardParts.2.1, pendingParts.2⟩
                  contextCompatible
            have targetEq :
                generatedLeft.dual.target.apply solution =
                  generatedRight.dual.target.apply solution := by
              exact hardParts.2.2 (.ty generatedLeft.dual.target
                generatedRight.dual.target) (by
                  simp [Pattern.dualEquations])
            rw [leftBindingsEq] at rightTyping rightBindingsEq
            rw [← targetEq] at rightTyping
            refine ⟨leftBindings ++ rightBindings,
              PatternBinds.and leftTyping rightTyping, ?_⟩
            simpa [List.append_assoc] using rightBindingsEq
    | or left right bindingsEqual =>
        rename_i generatedLeft afterLeft generatedRight bindingChecks
        cases supported with
        | or leftSupported rightSupported =>
            have hardParts :
                Solves solution generatedLeft.hard ∧
                Solves solution generatedRight.hard ∧
                Solves solution
                  (Pattern.dualEquations generatedLeft.dual generatedRight.dual) ∧
                Solves solution bindingChecks := by
              have outer := (solves_append solution
                ((generatedLeft.hard ++ generatedRight.hard) ++
                  Pattern.dualEquations generatedLeft.dual generatedRight.dual)
                bindingChecks).mp semantic.1
              have middle := (solves_append solution
                (generatedLeft.hard ++ generatedRight.hard)
                (Pattern.dualEquations generatedLeft.dual
                  generatedRight.dual)).mp outer.1
              have inner := (solves_append solution generatedLeft.hard
                generatedRight.hard).mp middle.1
              exact ⟨inner.1, inner.2, middle.2, outer.2⟩
            have pendingParts :
                (∀ obligation ∈ generatedLeft.pending,
                  ∃ conversionClass,
                    CheckConversion conversionClass
                      (obligation.source.apply solution)
                      (obligation.expected.apply solution)) ∧
                (∀ obligation ∈ generatedRight.pending,
                  ∃ conversionClass,
                    CheckConversion conversionClass
                      (obligation.source.apply solution)
                      (obligation.expected.apply solution)) := by
              constructor <;> intro obligation member
              · exact semantic.2 obligation (by simp [member])
              · exact semantic.2 obligation (by simp [member])
            obtain ⟨leftBindings, leftTyping, leftBindingsEq⟩ :=
              TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
                left compatible leftSupported ⟨hardParts.1, pendingParts.1⟩
                  contextCompatible
            obtain ⟨rightBindings, rightTyping, rightBindingsEq⟩ :=
              TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
                right compatible rightSupported ⟨hardParts.2.1, pendingParts.2⟩
                  contextCompatible
            have targetEq :
                generatedLeft.dual.target.apply solution =
                  generatedRight.dual.target.apply solution := by
              exact hardParts.2.2.1 (.ty generatedLeft.dual.target
                generatedRight.dual.target) (by
                  simp [Pattern.dualEquations])
            have generatedBindingsEq :=
              Pattern.bindingEquations_runtime_eq bindingsEqual hardParts.2.2.2
            have appendedBindingsEq :
                Ty.applyList solution bindings ++ leftBindings =
                  Ty.applyList solution bindings ++ rightBindings := by
              rw [← leftBindingsEq, ← rightBindingsEq]
              exact generatedBindingsEq
            have newBindingsEq : leftBindings = rightBindings :=
              List.append_cancel_left appendedBindingsEq
            subst rightBindings
            rw [← targetEq] at rightTyping
            exact ⟨leftBindings, PatternBinds.or leftTyping rightTyping,
              leftBindingsEq⟩
    | embed lookup => cases supported
    | app lookup arity fieldsElaboration => cases supported

  /-- Source-ordered list lifting for the direct runtime pattern fragment. -/
  theorem PatternsElaborate.toDirectRuntimePatternsBind
      (elaboration : PatternsElaborate signature context
        arguments patterns bindings supply generated next)
      (compatible : FrozenSignatureRuntimeCompatible signature)
      (supported : DirectRuntimePatternsSupported patterns)
      (semantic : GeneratedPatternsRuntimeSolution generated solution)
      (contextCompatible :
        MonomorphicContextCompatible context runtimeContext solution) :
      ∃ newBindings,
        PatternsBind
          (fun runtimeContext expression target =>
            RuntimeTyping expression target runtimeContext)
          runtimeContext (Ty.applyList solution bindings) patterns
          (Ty.applyList solution (Dual.targets generated.duals)) newBindings ∧
        Ty.applyList solution generated.bindings =
          Ty.applyList solution bindings ++ newBindings := by
    cases elaboration with
    | nil =>
        cases supported
        exact ⟨[], .nil, by simp⟩
    | cons head tail =>
        rename_i pattern patterns generatedPattern afterPattern generatedPatterns
        cases supported with
        | cons headSupported tailSupported =>
            have headSemantic :
                GeneratedPatternRuntimeSolution generatedPattern solution := by
              constructor
              · intro equation member
                exact semantic.1 equation (by simp [member])
              · intro obligation member
                exact semantic.2 obligation (by simp [member])
            have tailSemantic :
                GeneratedPatternsRuntimeSolution generatedPatterns solution := by
              constructor
              · intro equation member
                exact semantic.1 equation (by simp [member])
              · intro obligation member
                exact semantic.2 obligation (by simp [member])
            obtain ⟨headBindings, headTyping, headBindingsEq⟩ :=
              TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
                head compatible headSupported headSemantic contextCompatible
            obtain ⟨tailBindings, tailTyping, tailBindingsEq⟩ :=
              TypePM.Source.MatcherTyping.PatternsElaborate.toDirectRuntimePatternsBind
                tail compatible tailSupported tailSemantic contextCompatible
            rw [headBindingsEq] at tailTyping tailBindingsEq
            refine ⟨headBindings ++ tailBindings, ?_, ?_⟩
            · simpa [Ty.applyList, Dual.targets, RuntimeDual.apply] using
                PatternsBind.cons headTyping tailTyping
            · simpa [List.append_assoc] using tailBindingsEq

end

/-! ## Solved M4 patterns as executable built-in atoms

`PatternBinds` records the type and binding behavior of a source pattern but
does not record which concrete matcher value will execute it.  The following
small shape judgment supplies only that missing runtime fact.  It is strictly
weaker than `MatchingAtomTyping`: it contains no expression typing and no
binding result.  Product matchers retain the exact component shape needed by
tuple reduction, while conjunction and disjunction reuse the same matcher on
both children.
-/

mutual

  inductive DirectPatternMatcherShape : Pattern → Value → Prop where
    | somethingVar : DirectPatternMatcherShape .var .something
    | somethingWild : DirectPatternMatcherShape .wild .something
    | somethingValue :
        DirectPatternMatcherShape (.value expression) .something
    | tuple
        (items : DirectPatternsMatcherShape patterns matchers) :
        DirectPatternMatcherShape (.tuple patterns) (.tuple matchers)
    | and
        (left : DirectPatternMatcherShape leftPattern matcher)
        (right : DirectPatternMatcherShape rightPattern matcher) :
        DirectPatternMatcherShape (.and leftPattern rightPattern) matcher
    | or
        (left : DirectPatternMatcherShape leftPattern matcher)
        (right : DirectPatternMatcherShape rightPattern matcher) :
        DirectPatternMatcherShape (.or leftPattern rightPattern) matcher
    | productVar : DirectPatternMatcherShape .var (.tuple matchers)
    | productWild : DirectPatternMatcherShape .wild (.tuple matchers)
    | productValue :
        DirectPatternMatcherShape (.value expression) (.tuple matchers)

  inductive DirectPatternsMatcherShape : List Pattern → List Value → Prop where
    | nil : DirectPatternsMatcherShape [] []
    | cons
        (head : DirectPatternMatcherShape pattern matcher)
        (tail : DirectPatternsMatcherShape patterns matchers) :
        DirectPatternsMatcherShape (pattern :: patterns) (matcher :: matchers)

end


/-- Combine M4-derived binding behavior with the concrete built-in matcher
shape and the actual typed target value.  The mutual induction principle of
`PatternBinds` simultaneously constructs the source-ordered tuple children. -/
theorem PatternBinds.toDirectMatchingAtomTyping
    {environmentTypes bindingTypes : List Ty}
    {pattern : Pattern} {targetType : Ty} {newBindings : List Ty}
    {matcherValue targetValue : Value}
    (binds : PatternBinds
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes bindingTypes pattern targetType newBindings)
    (matcherShape : DirectPatternMatcherShape pattern matcherValue)
    (targetTyped : ValueTyping targetValue targetType) :
    MatchingAtomTyping
      (fun runtimeContext expression target =>
        RuntimeTyping expression target runtimeContext)
      environmentTypes bindingTypes
      ⟨pattern, matcherValue, targetValue⟩ newBindings := by
  refine @PatternBinds.rec
    (expressionTyping := fun runtimeContext expression target =>
      RuntimeTyping expression target runtimeContext)
    (motive_1 := fun environmentTypes bindingTypes pattern targetType
        newBindings _ =>
      ∀ {matcherValue targetValue},
        DirectPatternMatcherShape pattern matcherValue →
        ValueTyping targetValue targetType →
        MatchingAtomTyping
          (fun runtimeContext expression target =>
            RuntimeTyping expression target runtimeContext)
          environmentTypes bindingTypes
          ⟨pattern, matcherValue, targetValue⟩ newBindings)
    (motive_2 := fun environmentTypes bindingTypes patterns targetTypes
        newBindings _ =>
      ∀ {matcherValues targetValues},
        DirectPatternsMatcherShape patterns matcherValues →
        ValueTypings targetValues targetTypes →
        ∃ atoms,
          MatchingAtomsZip patterns matcherValues targetValues atoms ∧
          MatchingAtomsTyping
            (fun runtimeContext expression target =>
              RuntimeTyping expression target runtimeContext)
            environmentTypes bindingTypes atoms newBindings)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ environmentTypes bindingTypes pattern
      targetType newBindings binds matcherValue targetValue matcherShape
      targetTyped
  · intro environmentTypes bindingTypes target matcherValue targetValue shape typed
    cases shape with
    | somethingVar => exact .somethingVar typed
    | productVar => exact .productVar typed
  · intro environmentTypes bindingTypes target matcherValue targetValue shape typed
    cases shape with
    | somethingWild => exact .somethingWild typed
    | productWild => exact .productWild typed
  · intro bindingTypes environmentTypes expression target expressionTyped
      matcherValue targetValue shape targetTyped
    cases shape with
    | somethingValue => exact .somethingValue expressionTyped targetTyped
    | productValue => exact .productValue expressionTyped targetTyped
  · intro environmentTypes bindingTypes constructor holes result patterns
      newBindings declaration fields fieldsInduction matcherValue targetValue shape
      targetTyped
    cases shape
  · intro environmentTypes bindingTypes patterns targets newBindings
      items itemsInduction matcherValues targetValue shape targetTyped
    cases shape with
    | tuple itemsShape =>
        obtain ⟨targetValues, rfl, targetValuesTyped⟩ :=
          targetTyped.product_canonical
        obtain ⟨atoms, zipped, atomsTyped⟩ :=
          itemsInduction itemsShape targetValuesTyped
        exact .tuple atoms zipped atomsTyped
  · intro environmentTypes bindingTypes leftPattern target leftBindings
      rightPattern rightBindings left right leftInduction rightInduction
      matcherValue targetValue shape targetTyped
    cases shape with
    | and leftShape rightShape =>
        exact .and (leftInduction leftShape targetTyped)
          (rightInduction rightShape targetTyped)
  · intro environmentTypes bindingTypes leftPattern target newBindings
      rightPattern left right leftInduction rightInduction matcherValue
      targetValue shape targetTyped
    cases shape with
    | or leftShape rightShape =>
        exact .or (leftInduction leftShape targetTyped)
          (rightInduction rightShape targetTyped)
  · intro environmentTypes bindingTypes matcherValues targetValues shape typed
    cases shape
    cases typed
    exact ⟨[], .nil, .nil⟩
  · intro environmentTypes bindingTypes pattern target headBindings patterns
      targets tailBindings head tail headInduction tailInduction matcherValues
      targetValues shape targetsTyped
    cases shape with
    | cons headShape tailShapes =>
        cases targetsTyped with
        | cons headTargetTyped tailTargetsTyped =>
            have headTyped := headInduction headShape headTargetTyped
            obtain ⟨tailAtoms, tailZipped, tailTyped⟩ :=
              tailInduction tailShapes tailTargetsTyped
            exact ⟨_ :: tailAtoms, .cons tailZipped,
              .cons _ _ _ _ headTyped tailTyped⟩


/-- A solved M4 derivation in the executable built-in matcher fragment yields
the total initial-atom certificate used by `matchAll` and `matchFirst`.
`matcherTyped` is the outer expression's matcher-type evidence; the sharper
`matcherShape` premise identifies the concrete built-in reduction path. -/
theorem PatternElaborates.toBuiltinTotalMatchingAtomTyping
    (elaboration : PatternElaborates signature context
      arguments pattern bindings supply generated next)
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (supported : DirectRuntimePatternSupported pattern)
    (semantic : GeneratedPatternRuntimeSolution generated solution)
    (contextCompatible :
      MonomorphicContextCompatible context runtimeContext solution)
    (_matcherTyped : ValueTyping matcherValue
      (.matcher (generated.dual.capability.apply solution.cap)
        (generated.dual.target.apply solution)))
    (matcherShape : DirectPatternMatcherShape pattern matcherValue)
    (targetTyped : ValueTyping targetValue
      (generated.dual.target.apply solution)) :
    ∃ newBindings,
      TotalMatchingAtomTyping runtimeContext (Ty.applyList solution bindings)
        ⟨pattern, matcherValue, targetValue⟩ newBindings ∧
      Ty.applyList solution generated.bindings =
        Ty.applyList solution bindings ++ newBindings := by
  obtain ⟨newBindings, patternBinds, bindingsEq⟩ :=
    TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
      elaboration compatible supported semantic contextCompatible
  exact ⟨newBindings,
    .builtin
      (TypePM.Source.MatcherTyping.PatternBinds.toDirectMatchingAtomTyping
        patternBinds matcherShape targetTyped),
    bindingsEq⟩

/-! ## Constructor patterns are matcher-defined, not built in

A source constructor pattern is not reduced structurally by
`reduceBuiltinAtom`.  Its meaning is supplied by the selected user matcher
clause: for example, a list `cons` clause may return head and tail
decompositions together with independently chosen next matchers.  Consequently
adding only a `PatternBinds.ctor` or `MatchingAtomTyping.ctor` constructor would
not justify any executable reduction.  The following two facts make that
operational boundary explicit, followed by the exact user-dispatch certificate
that is sufficient.
-/

/-- Constructor atoms always pass through the built-in reducer to user-matcher
dispatch. -/
theorem reduceBuiltinAtom_constructor_miss
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (environment : ValueEnvironment) (matcher target : Value) :
    reduceBuiltinAtom eval environment
      ⟨.ctor constructor fields, matcher, target⟩ = .ok .miss := by
  rfl

/-- The existing built-in atom judgment deliberately has no constructor case.
This proves that a static `PatternBinds` rule alone could not feed the current
built-in preservation theorem. -/
theorem no_builtin_constructor_atom_typing
    (typing : MatchingAtomTyping expressionTyping environmentTypes bindingTypes
      ⟨.ctor constructor fields, matcher, target⟩ newBindings) : False := by
  cases typing

/-- Exact runtime evidence needed to type a constructor atom owned by a user
matcher.  In particular, `branches` ranges only over the branches returned by
the concrete dispatch and recursively certifies the field-pattern obligations
paired with the next matcher values selected by the matcher clause. -/
structure ConstructorUserDispatchCertificate
    (environmentTypes bindingTypes definitionTypes : List Ty)
    (matcherEnvironment : ValueEnvironment)
    (original remaining : List MatcherClause)
    (constructor : PatternCtor) (fields : List Pattern) (target : Value)
    (matcherTarget : Ty) (newBindings : List Ty) : Prop where
  matcherEnvironmentTyped :
    EnvironmentTyping matcherEnvironment definitionTypes
  targetTyped : ValueTyping target matcherTarget
  clausesTyped : RuntimeMatcherClausesInputTyping
    (bindingTypes ++ environmentTypes) definitionTypes matcherTarget
    (.ctor constructor fields) remaining
  finalCatchAll : MatcherTyping.FinalCatchAll remaining
  branches : ∀ (fuel : Nat) (atomEnvironment : ValueEnvironment)
      {holes recursiveBranches},
    dispatchMatcherClauses (evalFuel fuel) atomEnvironment
        matcherEnvironment remaining (.ctor constructor fields) target =
      .ok (.hit recursiveBranches) →
    DelegatedMatchingBranchesTyping holes recursiveBranches →
    ∀ branch ∈ recursiveBranches,
      TotalMatchingAtomsTyping environmentTypes bindingTypes
        branch newBindings

/-- Packaging the constructor-specific evidence yields exactly the total atom
certificate consumed by common-fuel safety. -/
theorem ConstructorUserDispatchCertificate.toTotalMatchingAtomTyping
    (certificate : ConstructorUserDispatchCertificate environmentTypes
      bindingTypes definitionTypes matcherEnvironment original remaining
      constructor fields target matcherTarget newBindings) :
    TotalMatchingAtomTyping environmentTypes bindingTypes
      ⟨.ctor constructor fields,
        .matcherV matcherEnvironment original remaining, target⟩
      newBindings := by
  exact .user
    (fun _ _ => reduceBuiltinAtom_constructor_miss _ _ _ _)
    certificate.matcherEnvironmentTyped certificate.targetTyped
    certificate.clausesTyped certificate.finalCatchAll certificate.branches

/-! ## Kernel obstruction for the erased certificate -/

private def obstructionHole (targetType : Ty) : Dual := ⟨.any, targetType⟩

private def obstructionAtom (target : Value) : MatchingAtom :=
  ⟨.var, .something, target⟩

private theorem obstructionMatcherTyped (targetType : Ty) :
    ValueTyping .something (.slot .any targetType) :=
  .checked (.something targetType) (.matcherToSlot .equal)

private theorem obstructionDelegated (target : Value)
    (targetTyped : ValueTyping target targetType) :
    DelegatedMatchingBranchesTyping [obstructionHole targetType]
      [[obstructionAtom target]] := by
  exact .cons (.cons (obstructionMatcherTyped targetType) targetTyped .nil) .nil

private theorem obstructionAtom_addsBinding
    (typing : TotalMatchingAtomTyping environmentTypes bindingTypes
      (obstructionAtom target) newBindings) : newBindings ≠ [] := by
  cases typing with
  | builtin typed =>
      cases typed
      simp

private theorem obstructionBranch_addsBinding
    (typing : TotalMatchingAtomsTyping environmentTypes bindingTypes
      [obstructionAtom target] newBindings) : newBindings ≠ [] := by
  cases typing with
  | @cons _ _ _ headBindings _ tailBindings head tail =>
      intro empty
      have parts : headBindings = [] ∧ tailBindings = [] := by
        simpa using empty
      exact obstructionAtom_addsBinding head parts.1

/-- An unrestricted callback over erased branches cannot type a wildcard user
atom with zero bindings: it is forced to accept a fabricated variable-pattern
branch having the same matcher and target value types. -/
theorem erasedBranches_cannot_preserve_wildcard_zeroBindings
    (targetTyped : ValueTyping target targetType)
    (branches : ∀ {holes recursiveBranches},
      DelegatedMatchingBranchesTyping holes recursiveBranches →
      ∀ branch ∈ recursiveBranches,
        TotalMatchingAtomsTyping environmentTypes bindingTypes branch []) : False := by
  have fabricated := branches (obstructionDelegated target targetTyped)
    [obstructionAtom target] (by simp)
  exact obstructionBranch_addsBinding fabricated rfl

end TypePM.Source.MatcherTyping
