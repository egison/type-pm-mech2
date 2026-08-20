import TypePM.GeneratedSemanticAcceptance
import TypePM.Source.M4RecursiveElaboration
import TypePM.Source.Paper1Programs
import TypePM.Source.M4PatternTypingRegression

/-!
# Declarative negative regressions for Paper 1

These regressions prove absence of `M4.Typing`, rather than recording only
an executable `infer = none` result.  Each proof inverts only the source rule
at the failure site, so it does not assume the still-open general completeness
theorem for M4.
-/

namespace TypePM.Source.M4Paper1NegativeRegression

open TypePM.Source
open Paper1Programs

/-- Paper 1 P1-L12: the value pattern refers to `x` before the variable
pattern to its right has introduced it. -/
def valueBeforeBinderProgram : Expr :=
  .matchAll (sourceList [.lit 1, .lit 2, .lit 3]) multisetSomething
    (.ctor PatternCtor.cons
      [.value (.var 0), .ctor PatternCtor.cons [.var, .wild]])
    (.var 0)

/-- A variable lookup in the empty context has no relational elaboration,
regardless of the available fuel. -/
private theorem no_empty_variable_elaboration
    {signature : FrozenSignature} {fuel : Nat} {supply next : Supply}
    {generated : Generated} :
    ¬ M4.ElaboratesFuel signature fuel [] (.var 0) supply generated next := by
  cases fuel <;> simp [M4.ElaboratesFuel]

/-- A principal block closure supplies an ordinary semantic solution of the
original hard and checking constraints. -/
private theorem semantic_solution_of_principal
    {generated : Generated} (closure : PrincipalBlockClosure generated) :
    ∃ solution, generated.SemanticSolution solution := by
  apply Generated.exists_semanticSolution_of_blockAccepts
  exact ⟨closure.finalHard, closure.finalPending,
    closure.hardSubstitution, closure.residualSubstitution,
    closure.saturation, closure.residualPrincipal.1⟩

/-- No finite type is equal to the one-layer list type containing itself. -/
private theorem type_ne_own_list (target : Ty) :
    target ≠ DataTypes.list target := by
  intro equality
  have countEquality := congrArg Ty.nodeCount equality
  simp [DataTypes.list, Ty.nodeCount, Ty.nodeCountList] at countEquality

/-- Paper 1 P1-L11: the value pattern occupies the list-tail position, so
the type of `x` would have to equal the list type containing itself. -/
def occursTailProgram : Expr :=
  .matchAll (sourceList [.lit 1, .lit 2, .lit 3]) multisetSomething
    (.ctor PatternCtor.cons [.var, .value (.var 0)])
    (.var 0)

/-- Paper 1 P1-L10.  The named target binding has the same `List Int` type as
the displayed literal `[1,2,3]`; the embedded expression is exactly
`x ++ [1]`. -/
def valueExpressionMismatchContext : Context :=
  [Scheme.mono (DataTypes.list .int)]

def valueExpressionMismatchProgram : Expr :=
  .matchAll (.var 0) multisetSomething
    (.ctor PatternCtor.cons
      [.var,
        .ctor PatternCtor.cons
          [.value (.prim .append [.var 0, sourceList [.lit 1]]), .wild]])
    (.var 0)

/-- Paper 1 P1-L13: `something` cannot provide the constructor capability
required by a cons pattern. -/
def somethingConsProgram : Expr :=
  .matchAll (sourceList [.lit 1, .lit 2, .lit 3]) .something
    (.ctor PatternCtor.cons [.var, .var])
    (.tuple [.var 0, .var 1])

private theorem no_any_matcher_to_list_slot
    (producerTarget consumerTarget : Ty) (elementCapability : Cap) :
    ¬ ∃ conversionClass,
      CheckConversion conversionClass (.matcher .any producerTarget)
        (.slot (.con PatternFormer.list [elementCapability]) consumerTarget) := by
  rintro ⟨_, conversion⟩
  cases conversion with
  | matcherToSlot demand => cases demand

private theorem matchAll_check_of_semantic
    {target : Generated} {pattern : GeneratedPattern}
    {matcher body : Generated} {solution : Subst}
    (checking : ∀ obligation ∈
      (Generated.fromMatchAll target pattern matcher body).pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)) :
    ∃ conversionClass,
      CheckConversion conversionClass
        (matcher.target.apply solution)
        ((Ty.slot pattern.dual.capability target.target).apply solution) := by
  exact checking
    ⟨matcher.target, Ty.slot pattern.dual.capability target.target⟩
    (by simp [Generated.fromMatchAll])

private theorem inner_application_check_of_semantic
    {function argument outerArgument : Generated}
    {domain innerTarget outerDomain outerTarget : Ty} {solution : Subst}
    (checking : ∀ obligation ∈
      (Generated.fromApp (Generated.fromApp function argument domain innerTarget)
        outerArgument outerDomain outerTarget).pending,
      ∃ conversionClass,
        CheckConversion conversionClass
          (obligation.source.apply solution)
          (obligation.expected.apply solution)) :
    ∃ conversionClass,
      CheckConversion conversionClass
        (argument.target.apply solution) (domain.apply solution) := by
  exact checking ⟨argument.target, domain⟩
    (by simp [Generated.fromApp])

private theorem infer_none_of_not_typable
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr}
    (notTypable : ∀ target, ¬ M4.Typing signature context expression target) :
    M4.infer signature context expression = none := by
  cases result : M4.infer signature context expression with
  | none => rfl
  | some target =>
      exact False.elim
        (notTypable target (M4.infer_success_typing wellFormed result))

/-- P1-L15 models the two named values in the listing: `flags` has type
`List Bool`, while `multiset integer` produces matches over `List Int`. -/
def matcherTargetMismatchContext : Context :=
  [ Scheme.mono (DataTypes.list DataTypes.bool),
    Scheme.mono
      (.matcher (.con PatternFormer.list [.any]) (DataTypes.list .int)) ]

def matcherTargetMismatchProgram : Expr :=
  .matchAll (.var 0) (.var 1)
    (.ctor PatternCtor.cons [.var, .wild]) (.var 0)

private theorem no_int_matcher_to_bool_slot (producer consumer : Cap) :
    ¬ ∃ conversionClass,
      CheckConversion conversionClass
        (.matcher producer (DataTypes.list .int))
        (.slot consumer (DataTypes.list DataTypes.bool)) := by
  rintro ⟨conversionClass, conversion⟩
  cases conversion

/-- Monomorphic top-level environment for the rejected P1-L07 call.  A named
`unconsWith` definition is represented by its already inferred interface. -/
def unconsWithCallType : Ty :=
  .fn (.slot (.con PatternFormer.list [.any]) .int)
    (.fn (DataTypes.list .int)
      (DataTypes.list (.prod [.int, DataTypes.list .int])))

def unconsWithCallContext : Context :=
  [Scheme.mono (DataTypes.list .int), Scheme.mono unconsWithCallType]

def unconsWithSomethingCall : Expr :=
  .app (.app (.var 1) .something) (.var 0)

/-- P1-L12 has no independent M4 typing derivation: the failure occurs while
elaborating the first field of the cons pattern, before the matcher expression
is inspected. -/
theorem value_before_binder_not_typable (target : Ty) :
    ¬ M4.Typing Paper1FrozenSignature.signature []
      valueBeforeBinderProgram target := by
  rintro ⟨_, ⟨derivation⟩, _⟩
  rcases derivation with
    ⟨generated, next, ⟨fuel, elaboration⟩, closure, absorbing, targetEq⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at elaboration
  | succ fuel =>
      change MatchAllElaboratesUsing
        (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
        Paper1FrozenSignature.signature []
        (sourceList [.lit 1, .lit 2, .lit 3]) multisetSomething
        (.ctor PatternCtor.cons
          [.value (.var 0), .ctor PatternCtor.cons [.var, .wild]])
        (.var 0) (Context.initialSupply []) generated next at elaboration
      cases elaboration with
      | mk _ patternElaboration _ _ =>
          cases patternElaboration with
          | ctor _ _ fieldsElaboration =>
              cases fieldsElaboration with
              | cons firstElaboration _ =>
                  cases firstElaboration with
                  | value embeddedElaboration =>
                      exact no_empty_variable_elaboration embeddedElaboration

theorem value_before_binder_infer_none :
    M4.infer Paper1FrozenSignature.signature [] valueBeforeBinderProgram = none :=
  infer_none_of_not_typable Paper1FrozenSignature.wellFormed
    value_before_binder_not_typable

/-- P1-L11 has no independent M4 typing derivation. -/
theorem occurs_tail_not_typable (target : Ty) :
    ¬ M4.Typing Paper1FrozenSignature.signature [] occursTailProgram target := by
  rintro ⟨_, ⟨derivation⟩, _⟩
  rcases derivation with
    ⟨generated, next, ⟨fuel, elaboration⟩, closure, absorbing, targetEq⟩
  rcases semantic_solution_of_principal closure with
    ⟨solution, hardSolved, checkingSolved⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at elaboration
  | succ fuel =>
      change MatchAllElaboratesUsing
        (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
        Paper1FrozenSignature.signature []
        (sourceList [.lit 1, .lit 2, .lit 3]) multisetSomething
        (.ctor PatternCtor.cons [.var, .value (.var 0)])
        (.var 0) (Context.initialSupply []) generated next at elaboration
      cases elaboration with
      | mk _ patternElaboration _ _ =>
          cases patternElaboration with
          | ctor lookup arity fieldsElaboration =>
              simp only [Paper1FrozenSignature.lookup_pattern_cons,
                Option.some.injEq] at lookup
              subst lookup
              cases fieldsElaboration with
              | cons firstElaboration remainingFields =>
                  cases firstElaboration
                  cases remainingFields with
                  | cons secondElaboration noFields =>
                      cases secondElaboration with
                      | value embeddedElaboration =>
                          cases noFields
                          cases fuel with
                          | zero => simp [M4.ElaboratesFuel] at embeddedElaboration
                          | succ innerFuel =>
                              simp [M4.ElaboratesFuel, Pattern.extendContext,
                                Scheme.mono, Scheme.instantiate] at embeddedElaboration
                              rcases embeddedElaboration with ⟨rfl, rfl, rfl, rfl⟩
                              simp [ListPatternSchemes.cons, DualScheme.instantiate,
                                PolyDual.openBound, PolyCap.openBound,
                                PolyCap.openBoundList, PolyTy.openBound,
                                PolyTy.openBoundList, Scheme.boundTyInstance,
                                Scheme.boundCapInstance, PolyDataTypes.list,
                                Pattern.fieldEquations, Generated.fromMatchAll,
                                DataTypes.list] at hardSolved
                              obtain ⟨_, _, fieldType, _, fieldListType, _, _, _⟩ :=
                                hardSolved
                              exact type_ne_own_list _
                                (fieldType.symm.trans fieldListType)

theorem occurs_tail_infer_none :
    M4.infer Paper1FrozenSignature.signature [] occursTailProgram = none :=
  infer_none_of_not_typable Paper1FrozenSignature.wellFormed
    occurs_tail_not_typable

/-- P1-L10 has no independent M4 typing derivation. -/
theorem value_expression_int_list_mismatch_not_typable (target : Ty) :
    ¬ M4.Typing Paper1FrozenSignature.signature
      valueExpressionMismatchContext valueExpressionMismatchProgram target := by
  rintro ⟨_, ⟨derivation⟩, _⟩
  rcases derivation with
    ⟨generated, next, ⟨fuel, elaboration⟩, closure, absorbing, targetEq⟩
  rcases semantic_solution_of_principal closure with
    ⟨solution, hardSolved, checkingSolved⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at elaboration
  | succ fuel =>
      change MatchAllElaboratesUsing
        (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
        Paper1FrozenSignature.signature valueExpressionMismatchContext
        (.var 0) multisetSomething
        (.ctor PatternCtor.cons
          [.var,
            .ctor PatternCtor.cons
              [.value (.prim .append [.var 0, sourceList [.lit 1]]), .wild]])
        (.var 0) (Context.initialSupply valueExpressionMismatchContext)
        generated next at elaboration
      cases elaboration with
      | mk targetElaboration patternElaboration matcherElaboration
          bodyElaboration =>
          cases fuel with
          | zero => simp [M4.ElaboratesFuel] at targetElaboration
          | succ innerFuel =>
              simp [M4.ElaboratesFuel, valueExpressionMismatchContext,
                Scheme.mono, Scheme.instantiate] at targetElaboration
              rcases targetElaboration with ⟨rfl, rfl, rfl, rfl⟩
              cases patternElaboration with
              | ctor outerLookup outerArity outerFields =>
                  simp only [Paper1FrozenSignature.lookup_pattern_cons,
                    Option.some.injEq] at outerLookup
                  subst outerLookup
                  cases outerFields with
                  | cons firstField remainingOuterFields =>
                      cases firstField
                      cases remainingOuterFields with
                      | cons secondField noOuterFields =>
                          cases noOuterFields
                          cases secondField with
                          | ctor innerLookup innerArity innerFields =>
                              simp only [Paper1FrozenSignature.lookup_pattern_cons,
                                Option.some.injEq] at innerLookup
                              subst innerLookup
                              cases innerFields with
                              | cons valueField remainingInnerFields =>
                                  cases valueField with
                                  | value embeddedElaboration =>
                                      cases remainingInnerFields with
                                      | cons wildcardField noInnerFields =>
                                          cases wildcardField
                                          cases noInnerFields
                                          simp only [M4.ElaboratesFuel]
                                            at embeddedElaboration
                                          rcases embeddedElaboration with
                                            ⟨scheme, lookup, arity, closed,
                                              callElaboration⟩
                                          change Paper1Signature.signature.lookupPrimitive
                                            .append = some scheme at lookup
                                          simp only [Paper1Signature.lookup_primitive,
                                            PrimitiveSchemes.ofPrimOp_append,
                                            Option.some.injEq] at lookup
                                          subst lookup
                                          cases callElaboration with
                                          | cons firstArgument remainingCall =>
                                              cases remainingCall with
                                              | cons secondArgument finishedCall =>
                                                  cases finishedCall
                                                  simp [PrimitiveSchemes.append,
                                                    Scheme.instantiate,
                                                    PolyTy.openBound,
                                                    PolyTy.openBoundList,
                                                    Scheme.boundTyInstance,
                                                    Scheme.boundCapInstance,
                                                    PolyDataTypes.list,
                                                    ListPatternSchemes.cons,
                                                    DualScheme.instantiate,
                                                    PolyDual.openBound,
                                                    PolyCap.openBound,
                                                    PolyCap.openBoundList,
                                                    Pattern.fieldEquations,
                                                    Generated.fromApp,
                                                    Generated.fromMatchAll,
                                                    DataTypes.list,
                                                    Equation.Holds, Ty.apply]
                                                    at hardSolved
                                                  rcases hardSolved with
                                                    ⟨baseEq, arg1Solved,
                                                      appendShape,
                                                      arg2Solved,
                                                      secondShape,
                                                      resultToElement,
                                                      capabilityEq, rest⟩
                                                  rcases appendShape with
                                                    ⟨appendDomainEq,
                                                      appendResultEq⟩
                                                  rcases rest with
                                                    ⟨_, _, _, _, elementEq, _⟩
                                                  have appendCodomainEq :=
                                                    appendResultEq.trans secondShape
                                                  injection appendCodomainEq with
                                                    _ appendListResultEq
                                                  injection baseEq with baseEq'
                                                  injection elementEq with elementEq'
                                                  simp only [Ty.apply] at baseEq'
                                                  have impossible :=
                                                    appendListResultEq.trans
                                                      (resultToElement.trans
                                                        (elementEq'.trans baseEq'))
                                                  cases impossible

theorem value_expression_int_list_mismatch_infer_none :
    M4.infer Paper1FrozenSignature.signature valueExpressionMismatchContext
      valueExpressionMismatchProgram = none :=
  infer_none_of_not_typable Paper1FrozenSignature.wellFormed
    value_expression_int_list_mismatch_not_typable

/-- P1-L13's listed cons expression has no M4 typing derivation. -/
theorem something_cons_not_typable (target : Ty) :
    ¬ M4.Typing Paper1FrozenSignature.signature []
      somethingConsProgram target := by
  rintro ⟨_, ⟨derivation⟩, _⟩
  rcases derivation with
    ⟨generated, next, ⟨fuel, elaboration⟩, closure, absorbing, targetEq⟩
  rcases semantic_solution_of_principal closure with
    ⟨solution, hardSolved, checkingSolved⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at elaboration
  | succ fuel =>
      change MatchAllElaboratesUsing
        (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
        Paper1FrozenSignature.signature []
        (sourceList [.lit 1, .lit 2, .lit 3]) .something
        (.ctor PatternCtor.cons [.var, .var])
        (.tuple [.var 0, .var 1]) (Context.initialSupply []) generated next
        at elaboration
      cases elaboration with
      | mk targetElaboration patternElaboration matcherElaboration
          bodyElaboration =>
          cases patternElaboration with
          | ctor lookup arity fieldsElaboration =>
              simp only [Paper1FrozenSignature.lookup_pattern_cons,
                Option.some.injEq] at lookup
              subst lookup
              cases fuel with
              | zero => simp [M4.ElaboratesFuel] at matcherElaboration
              | succ innerFuel =>
                  simp [M4.ElaboratesFuel] at matcherElaboration
                  rcases matcherElaboration with ⟨rfl, rfl⟩
                  have impossible := matchAll_check_of_semantic checkingSolved
                  simp [ListPatternSchemes.cons, DualScheme.instantiate,
                    PolyDual.openBound, PolyCap.openBound,
                    PolyCap.openBoundList, PolyTy.openBound,
                    PolyTy.openBoundList, Scheme.boundTyInstance,
                    Scheme.boundCapInstance, PolyDataTypes.list] at impossible
                  exact no_any_matcher_to_list_slot _ _ _ impossible

theorem something_cons_infer_none :
    M4.infer Paper1FrozenSignature.signature [] somethingConsProgram = none :=
  infer_none_of_not_typable Paper1FrozenSignature.wellFormed
    something_cons_not_typable

/-- P1-L15 has no independent M4 typing derivation. -/
theorem matcher_target_mismatch_not_typable (target : Ty) :
    ¬ M4.Typing Paper1FrozenSignature.signature
      matcherTargetMismatchContext matcherTargetMismatchProgram target := by
  rintro ⟨_, ⟨derivation⟩, _⟩
  rcases derivation with
    ⟨generated, next, ⟨fuel, elaboration⟩, closure, absorbing, targetEq⟩
  rcases semantic_solution_of_principal closure with
    ⟨solution, hardSolved, checkingSolved⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at elaboration
  | succ fuel =>
      change MatchAllElaboratesUsing
        (M4.ElaboratesFuel Paper1FrozenSignature.signature fuel)
        Paper1FrozenSignature.signature matcherTargetMismatchContext
        (.var 0) (.var 1) (.ctor PatternCtor.cons [.var, .wild])
        (.var 0) (Context.initialSupply matcherTargetMismatchContext)
        generated next at elaboration
      cases elaboration with
      | mk targetElaboration patternElaboration matcherElaboration
          bodyElaboration =>
          cases fuel with
          | zero => simp [M4.ElaboratesFuel] at targetElaboration
          | succ innerFuel =>
              simp [M4.ElaboratesFuel, matcherTargetMismatchContext,
                Scheme.mono, Scheme.instantiate] at targetElaboration
              rcases targetElaboration with ⟨rfl, rfl, rfl, rfl⟩
              cases patternElaboration with
              | ctor lookup arity fieldsElaboration =>
                  simp only [Paper1FrozenSignature.lookup_pattern_cons,
                    Option.some.injEq] at lookup
                  subst lookup
                  simp [M4.ElaboratesFuel, matcherTargetMismatchContext,
                    Scheme.mono, Scheme.instantiate] at matcherElaboration
                  rcases matcherElaboration with ⟨rfl, rfl, rfl, rfl⟩
                  have impossible := matchAll_check_of_semantic checkingSolved
                  exact no_int_matcher_to_bool_slot _ _ impossible

theorem matcher_target_mismatch_infer_none :
    M4.infer Paper1FrozenSignature.signature matcherTargetMismatchContext
      matcherTargetMismatchProgram = none :=
  infer_none_of_not_typable Paper1FrozenSignature.wellFormed
    matcher_target_mismatch_not_typable

/-- P1-L07's bare-`something` call has no independent M4 typing derivation. -/
theorem unconsWith_something_not_typable (target : Ty) :
    ¬ M4.Typing Paper1FrozenSignature.signature unconsWithCallContext
      unconsWithSomethingCall target := by
  rintro ⟨_, ⟨derivation⟩, _⟩
  rcases derivation with
    ⟨generated, next, ⟨fuel, elaboration⟩, closure, absorbing, targetEq⟩
  rcases semantic_solution_of_principal closure with
    ⟨solution, hardSolved, checkingSolved⟩
  cases fuel with
  | zero => simp [M4.ElaboratesFuel] at elaboration
  | succ fuel =>
      change ∃ generatedFunction afterFunction generatedArgument afterArgument,
        M4.ElaboratesFuel Paper1FrozenSignature.signature fuel
            unconsWithCallContext (.app (.var 1) .something)
            (Context.initialSupply unconsWithCallContext)
            generatedFunction afterFunction ∧
          M4.ElaboratesFuel Paper1FrozenSignature.signature fuel
            unconsWithCallContext (.var 0) afterFunction
            generatedArgument afterArgument ∧
          generated = Generated.fromApp generatedFunction generatedArgument
            (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩) ∧
          next = afterArgument.nextTy 2 at elaboration
      rcases elaboration with
        ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
          functionElaboration, argumentElaboration, rfl, rfl⟩
      cases fuel with
      | zero => simp [M4.ElaboratesFuel] at functionElaboration
      | succ innerFuel =>
          change ∃ innerFunction afterInnerFunction innerArgument
              afterInnerArgument,
            M4.ElaboratesFuel Paper1FrozenSignature.signature innerFuel
                unconsWithCallContext (.var 1)
                (Context.initialSupply unconsWithCallContext)
                innerFunction afterInnerFunction ∧
              M4.ElaboratesFuel Paper1FrozenSignature.signature innerFuel
                unconsWithCallContext .something afterInnerFunction
                innerArgument afterInnerArgument ∧
              generatedFunction = Generated.fromApp innerFunction innerArgument
                (.var ⟨afterInnerArgument.ty⟩)
                (.var ⟨afterInnerArgument.ty + 1⟩) ∧
              afterFunction = afterInnerArgument.nextTy 2 at functionElaboration
          rcases functionElaboration with
            ⟨innerFunction, afterInnerFunction, innerArgument,
              afterInnerArgument, innerFunctionElaboration,
              innerArgumentElaboration, rfl, rfl⟩
          cases innerFuel with
          | zero => simp [M4.ElaboratesFuel] at innerFunctionElaboration
          | succ leafFuel =>
              let producerTarget : Ty := .var ⟨afterInnerFunction.ty⟩
              let demandedDomain : Ty := .var ⟨afterInnerArgument.ty⟩
              let innerTarget : Ty := .var ⟨afterInnerArgument.ty + 1⟩
              simp [M4.ElaboratesFuel, unconsWithCallContext,
                Scheme.mono, Scheme.instantiate] at innerFunctionElaboration
              rcases innerFunctionElaboration with ⟨rfl, rfl, rfl, rfl⟩
              simp [M4.ElaboratesFuel] at innerArgumentElaboration
              rcases innerArgumentElaboration with ⟨rfl, rfl⟩
              have functionEquation : Equation.Holds solution
                  (Equation.ty unconsWithCallType
                    (Ty.fn demandedDomain innerTarget)) :=
                hardSolved _ (by
                  simp [Generated.fromApp, demandedDomain, innerTarget])
              simp only [Equation.Holds, unconsWithCallType, Ty.apply]
                at functionEquation
              injection functionEquation with domainEquality resultEquality
              have conversion :=
                inner_application_check_of_semantic checkingSolved
              rw [← domainEquality] at conversion
              simpa [Ty.apply, Cap.apply, DataTypes.list] using
                (no_any_matcher_to_list_slot
                  (producerTarget.apply solution)
                  .int .any conversion)

theorem unconsWith_something_infer_none :
    M4.infer Paper1FrozenSignature.signature unconsWithCallContext
      unconsWithSomethingCall = none :=
  infer_none_of_not_typable Paper1FrozenSignature.wellFormed
    unconsWith_something_not_typable

/-! ## Branch-stable higher-order matcher-constructor boundary

`multisetWithListArgument` is `fun list => multiset`.  Its parameter is used
as a function from a matcher slot to a matcher, but the parameter starts with
an unconstrained ordinary type.  The branch-stable checker deliberately does
not guess that this ordinary type should have a matcher-shaped function
domain.  Supplying the known `list` definition at the call site, as
`closedMultisetDefinition` does, establishes that shape before checking.

This is the current inference boundary, not a proof that no declarative M4
typing exists; general M4 completeness remains separate work.  A kernel
regression for this large matcher-literal expression still needs the same
fuel-to-public-inference bridge as the other large Paper 1 fixtures.
-/

end TypePM.Source.M4Paper1NegativeRegression
