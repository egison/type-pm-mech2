import TypePM.Source.M4CanonicalCertificateTransport
import TypePM.Source.M4MatchFirstTotalCoreBridge
import TypePM.ValueIndexedStableFirstOrderSafety

/-!
# A first concrete M5 runtime certificate

This module instantiates the M5 expression-side architecture for a deliberately
small, nonempty fragment.  The fragment contains integer literals, binary
pairs of fragment integers, and nested projections from those pairs.  It is a
closed, stable first-order fragment; it is not claimed to cover every
`Expr.MNodeFree` expression.

The runtime certificate is indexed by the actual M4 principal derivation.  It
contains only a structural fragment typing and the runtime typing reconstructed
from that derivation.  It contains no evaluation result, search result, or
equation predicting either result.
-/

namespace TypePM.Source.M5ClosedPairProjectionCertificate

open TypePM.Runtime
open TypePM.Source.M5CompletionArchitecture
open TypePM.Source.M4.CompletenessArchitecture

/-- Closed stable expressions.  The only result indices are `int` and a
binary pair of integers. -/
inductive Fragment : Expr → Ty → Prop where
    | lit (literal : Int) : Fragment (.lit literal) .int
    | pair
        (left : Fragment leftExpression .int)
        (right : Fragment rightExpression .int) :
        Fragment (.tuple [leftExpression, rightExpression])
          (.prod [.int, .int])
    | pairFirst
        (left : Fragment leftExpression .int)
        (right : Fragment rightExpression .int) :
        Fragment (.prim PrimOp.pairFirst
          [.tuple [leftExpression, rightExpression]]) .int
    | pairSecond
        (left : Fragment leftExpression .int)
        (right : Fragment rightExpression .int) :
        Fragment (.prim PrimOp.pairSecond
          [.tuple [leftExpression, rightExpression]]) .int

/-- List companion used only to invert the mutually inductive runtime typing
of a binary tuple. -/
inductive Fragments : List Expr → List Ty → Prop where
    | nil : Fragments [] []
    | cons
        (head : Fragment expression target)
        (tail : Fragments expressions targets) :
        Fragments (expression :: expressions) (target :: targets)

/-- Existential expression-only scope expected by the M5 architecture. -/
def Supported (expression : Expr) : Prop :=
  ∃ target, Fragment expression target

def DerivationSupported : M5CompletionArchitecture.RuntimeScope :=
  fun {_signature} {_context} {expression} {_principal} _derivation =>
    Supported expression

namespace Fragment

theorem runtimeSupported : Fragment expression target →
    RuntimeSupported expression
  | .lit _ => .lit
  | .pair left right =>
      .tuple (.cons left.runtimeSupported
        (.cons right.runtimeSupported .nil))
  | .pairFirst left right =>
      .pairFirst (.tuple (.cons left.runtimeSupported
        (.cons right.runtimeSupported .nil)))
  | .pairSecond left right =>
      .pairSecond (.tuple (.cons left.runtimeSupported
        (.cons right.runtimeSupported .nil)))

theorem evaluatorIndependent : Fragment expression target →
    Expr.EvaluatorIndependent expression
  | .lit _ => .lit
  | .pair left right =>
      .tuple (.cons left.evaluatorIndependent
        (.cons right.evaluatorIndependent .nil))
  | .pairFirst left right =>
      .prim (by decide) (.cons
        (.tuple (.cons left.evaluatorIndependent
          (.cons right.evaluatorIndependent .nil))) .nil)
  | .pairSecond left right =>
      .prim (by decide) (.cons
        (.tuple (.cons left.evaluatorIndependent
          (.cons right.evaluatorIndependent .nil))) .nil)

theorem mnodeFree (fragment : Fragment expression target) :
    expression.MNodeFree :=
  fragment.evaluatorIndependent.mnodeFree

/-- The fragment type is unchanged by any type substitution. -/
theorem apply (fragment : Fragment expression target)
    (substitution : Subst) :
    Fragment expression (target.apply substitution) := by
  cases fragment <;> simp only [Ty.apply] <;> constructor <;> assumption

end Fragment

namespace Fragments

theorem runtimeSupporteds : Fragments expressions targets →
    RuntimeSupporteds expressions
  | .nil => .nil
  | .cons head tail => .cons head.runtimeSupported tail.runtimeSupporteds

end Fragments

namespace Supported

/-- Every admitted expression is evaluator-independent: in particular it has
no application, `map`, `matchAll`, or `matchFirst` node at any recursive
position. -/
theorem evaluatorIndependent (supported : Supported expression) :
    expression.EvaluatorIndependent := by
  rcases supported with ⟨target, fragment⟩
  exact fragment.evaluatorIndependent

theorem mnodeFree (supported : Supported expression) : expression.MNodeFree :=
  supported.evaluatorIndependent.mnodeFree

end Supported

private theorem checked_target_eq_of_int
    (conversion : CheckConversion conversionClass .int target) :
    target = .int := by
  cases conversion
  rfl

private theorem checked_target_eq_of_intPair
    (conversion : CheckConversion conversionClass
      (.prod [.int, .int]) target) :
    target = .prod [.int, .int] := by
  generalize sourceEq : (Ty.prod [.int, .int]) = source at conversion
  cases conversion with
  | ordinary => rfl
  | matcherToSlot demand => simp at sourceEq
  | @productMatcherToSlot duals consumer nonempty demand =>
      simp only [Ty.prod.injEq] at sourceEq
      cases duals with
      | nil => simp at sourceEq
      | cons first rest => simp [Dual.matcherType] at sourceEq

private theorem runtimeTyping_target_eq_aux
    {expression : Expr} {actual : Ty} {runtimeContext : List Ty}
    (typing : RuntimeTyping expression actual runtimeContext) :
    ∀ expected, Fragment expression expected → actual = expected := by
  apply RuntimeTyping.rec
    (motive_1 := fun expression actual runtimeContext _typing =>
      ∀ expected, Fragment expression expected → actual = expected)
    (motive_2 := fun expressions actuals runtimeContext _typings =>
      ∀ expecteds, Fragments expressions expecteds → actuals = expecteds)
    (t := typing)
  case var =>
    intro context index target lookup expected fragment
    cases fragment
  case lit =>
    intro context literal expected fragment
    cases fragment
    rfl
  case something =>
    intro context target expected fragment
    cases fragment
  case boolTrue =>
    intro context expected fragment
    cases fragment
  case boolFalse =>
    intro context expected fragment
    cases fragment
  case listNil =>
    intro context element expected fragment
    cases fragment
  case listCons =>
      intro headExpression element context tailExpression head tail headIH tailIH
      intro expected fragment; cases fragment
  case tuple =>
    intro expressions actuals runtimeContext items itemsIH
    intro expected fragment
    cases fragment with
    | pair left right =>
        exact congrArg Ty.prod
          (itemsIH [.int, .int] (.cons left (.cons right .nil)))
  case lam =>
      intro bodyExpression codomain domain context body bodyIH expected fragment
      cases fragment
  case app =>
      intro functionExpression domain codomain context argumentExpression
        function argument functionIH argumentIH
      intro expected fragment; cases fragment
  case letE =>
      intro valueExpression valueTarget context bodyExpression bodyTarget value
        body valueIH bodyIH
      intro expected fragment; cases fragment
  case fixE =>
      intro bodyExpression codomain domain context body bodyIH expected fragment
      cases fragment
  case add =>
      intro leftExpression context rightExpression left right leftIH rightIH
      intro expected fragment; cases fragment
  case append =>
      intro leftExpression element context rightExpression left right leftIH
        rightIH
      intro expected fragment; cases fragment
  case member =>
      intro needleExpression element context targetExpression needle target
        needleIH targetIH
      intro expected fragment; cases fragment
  case deleteFirst =>
      intro needleExpression element context targetExpression needle target
        needleIH targetIH
      intro expected fragment; cases fragment
  case map =>
      intro functionExpression domain codomain context targetExpression function
        target functionIH targetIH
      intro expected fragment; cases fragment
  case pairFirst =>
    intro pairExpression firstTarget secondTarget context pairTyping pairIH
    intro expected fragment
    cases fragment with
    | pairFirst left right =>
        have pairEq := pairIH (.prod [.int, .int]) (.pair left right)
        exact (List.cons.inj (Ty.prod.inj pairEq)).1
  case pairSecond =>
    intro pairExpression firstTarget secondTarget context pairTyping pairIH
    intro expected fragment
    cases fragment with
    | pairSecond left right =>
        have pairEq := pairIH (.prod [.int, .int]) (.pair left right)
        exact (List.cons.inj (List.cons.inj (Ty.prod.inj pairEq)).2).1
  case ifE =>
      intro conditionExpression context thenExpression branchTarget
        elseExpression condition thenBranch elseBranch conditionIH thenIH elseIH
      intro expected fragment; cases fragment
  case checked =>
    intro expression sourceTarget context conversionClass target source conversion
      sourceIH
    intro expected fragment
    have sourceEq := sourceIH expected fragment
    subst sourceTarget
    cases fragment with
    | lit => exact checked_target_eq_of_int conversion
    | pair => exact checked_target_eq_of_intPair conversion
    | pairFirst => exact checked_target_eq_of_int conversion
    | pairSecond => exact checked_target_eq_of_int conversion
  case nil =>
    intro context
    intro expecteds fragments
    cases fragments
    rfl
  case cons =>
    intro expression target context expressions targets head tail headIH tailIH
    intro expecteds fragments
    cases fragments with
    | cons expectedHead expectedTail =>
        simp [headIH _ expectedHead, tailIH _ expectedTail]

/-- Runtime typing cannot assign a different type to a fragment term.  This
is the static bridge that keeps the certificate indexed by the actual M4
principal derivation. -/
theorem Fragment.runtimeTyping_target_eq
    (fragment : Fragment expression expected)
    (typing : RuntimeTyping expression actual runtimeContext) :
    actual = expected :=
  runtimeTyping_target_eq_aux typing expected fragment

namespace Fragment

/-- Every evaluation fuel returns either timeout or a value safe at every
logical index.  Pair construction and projection use the reusable stable
first-order safety lemmas. -/
private theorem allFuelResultSafe_aux
    {expression : Expr} {target : Ty}
    (fragment : Fragment expression target) :
    ∀ environment fuel, AllFuelResultSafe target
      (evalFuel fuel environment expression) := by
  induction fragment with
  | lit literal =>
      intro environment fuel
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          exact .inr ⟨.int literal, by simp [evalFuel],
            fuelValueSafe_int literal⟩
  | pair left right leftIH rightIH =>
      intro environment fuel
      exact AllFuelPairResultSafe.toAllFuelResultSafe
        (evalFuel_tuplePair_allFuelSafe_all (leftIH environment)
          (rightIH environment) fuel)
  | pairFirst left right leftIH rightIH =>
      intro environment
      exact evalFuel_pairFirst_allFuelSafe_all
        (evalFuel_tuplePair_allFuelSafe_all (leftIH environment)
          (rightIH environment))
  | pairSecond left right leftIH rightIH =>
      intro environment
      exact evalFuel_pairSecond_allFuelSafe_all
        (evalFuel_tuplePair_allFuelSafe_all (leftIH environment)
          (rightIH environment))

theorem allFuelResultSafe (fragment : Fragment expression target)
    (environment : ValueEnvironment) :
    ∀ fuel, AllFuelResultSafe target
      (evalFuel fuel environment expression) :=
  fragment.allFuelResultSafe_aux environment

end Fragment

/-- Concrete proof-bearing runtime state, indexed by the exact M4 principal
derivation. -/
inductive Certificate
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal) : List Ty → Prop where
  | ordinary
      (fragment : Fragment expression principal)
      (runtimeTyping : RuntimeTyping expression principal []) :
      Certificate derivation []

/-- This first slice is intentionally a closed-top-level lane. -/
def ClosedRuntimeContextRelation : RuntimeContextRelation :=
  @fun _signature context _expression _principal _derivation runtimeContext =>
    context = [] ∧ runtimeContext = []

theorem closedRuntimeContext_realizable :
    ClosedContextRealizable ClosedRuntimeContextRelation := by
  intro signature expression principal derivation
  exact ⟨rfl, rfl⟩

/-- M4 state erasure for the explicit stable fragment. -/
theorem principalStateErasure : PrincipalStateErasure DerivationSupported Certificate
    ClosedRuntimeContextRelation := by
  intro signature context expression principal derivation runtimeContext
    signatureReady supported contextCompatible
  rcases supported with ⟨expected, fragment⟩
  rcases contextCompatible with ⟨rfl, rfl⟩
  rcases derivation.elaboration with ⟨fuel, elaboration⟩
  have sourceElaboration := elaboratesFuel_toM2_of_m2Fragment
    fragment.runtimeSupported.toM2Fragment elaboration
  have runtimeTyping : RuntimeTyping expression
      (derivation.generated.target.apply derivation.closure.substitution) [] :=
    fragment.runtimeSupported.elaboration_typing signatureReady.2
      sourceElaboration
      (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
        derivation.closure)
      MonomorphicContextCompatible.nil
  have closureTyping : RuntimeTyping expression derivation.closure.target [] := by
    simpa [PrincipalBlockClosure.target] using runtimeTyping
  have principalTyping : RuntimeTyping expression principal [] := by
    rw [derivation.target_eq]
    exact closureTyping
  have principalEq : principal = expected :=
    fragment.runtimeTyping_target_eq principalTyping
  subst expected
  exact .ordinary fragment principalTyping

/-- The stable first-order certificate uses the traditional additive fuel
demand.  More expressive certificate families may instead return a structural
demand derived from their retained principal derivation. -/
def evaluationInputDemand : EvaluationInputDemandFamily Certificate
    fuelIndexedSafetyRelations :=
  additiveFuelEvaluationInputDemand Certificate

/-- Typed evaluation for the concrete certificate and the existing
fuel-indexed logical relation. -/
theorem typedEvaluation : TypedEvaluation Certificate
    fuelIndexedSafetyRelations evaluationInputDemand evalFuel := by
  intro signature context expression principal target derivation runtimeContext
    certificate instantiation evaluationFuel resultIndex environment
    _demandApplicable _environmentSafe
  cases certificate with
  | ordinary fragment runtimeTyping =>
      rcases instantiation with ⟨substitution, targetEquation⟩
      have targetFragment : Fragment expression target := by
        rw [← targetEquation]
        exact fragment.apply substitution
      exact AllFuelResultSafe.toFuelResultSafe
        (targetFragment.allFuelResultSafe environment evaluationFuel) resultIndex

/-- Closed source typings in the fragment never evaluate to `stuck`, at any
fuel. -/
theorem closedNoStuck : ClosedNoStuck DerivationSupported evalFuel :=
  closedNoStuck_of_principalStateErasure_and_typedEvaluation
    closedRuntimeContext_realizable principalStateErasure typedEvaluation

/-- Coherent M4 principal derivations transport this certificate by the exact
instance substitution supplied by closure alignment. -/
theorem closedRuntimeCertificateRespectsCoherence :
    ClosedRuntimeCertificateRespectsCoherence Certificate := by
  intro signature expression leftPrincipal rightPrincipal left right pair
    alignment certificate
  cases certificate with
  | ordinary fragment runtimeTyping =>
      obtain ⟨forward, _backward⟩ :=
        alignment.principalTargets_mutualInstances left right
      rcases forward with ⟨substitution, targetEquation⟩
      have rightFragment : Fragment expression rightPrincipal := by
        rw [← targetEquation]
        exact fragment.apply substitution
      have rightTyping : RuntimeTyping expression rightPrincipal [] := by
        rw [← targetEquation]
        exact runtimeTyping.apply substitution
      exact .ordinary rightFragment rightTyping

/-- The ordinary fragment issues no matching-search task.  This empty origin
is not a claim about arbitrary MNode-free expressions. -/
inductive SearchOrigin :
    MatchingSearchOriginFamily BoundedDfsMatchingSearchTask
      fuelIndexedSafetyRelations.SearchDemand

def SearchCertificate :
    MatchingSearchCertificateFamily BoundedDfsMatchingSearchTask
      fuelIndexedSafetyRelations.SearchDemand :=
  fun _task _answerTypes _callbackFuel _searchFuel _resultDemand => False

theorem matchingStateErasure :
    MatchingStateErasure Certificate SearchOrigin SearchCertificate := by
  intro signature context expression principal derivation runtimeContext task
    answerTypes callbackFuel searchFuel resultDemand certificate origin
  cases origin

theorem typedMatchingSearch : TypedMatchingSearch fuelIndexedSafetyRelations
    SearchCertificate runBoundedDfsMatchingSearch := by
  intro task answerTypes callbackFuel searchFuel resultDemand certificate
  exact certificate.elim

/-- The complete M5 conditional schema for this non-search fragment.  Because
`Supported` is syntactically search-free, its search origin is empty and the
two search fields are consequently vacuous.  This theorem is not evidence for
any fragment containing `matchAll` or another search-bearing expression. -/
theorem conditionalCompletionSchema :
    ConditionalCompletionSchema DerivationSupported Certificate
      ClosedRuntimeContextRelation fuelIndexedSafetyRelations
      evaluationInputDemand evalFuel SearchOrigin SearchCertificate
      runBoundedDfsMatchingSearch :=
  conditionalCompletionSchema_of_components
    closedRuntimeContext_realizable principalStateErasure matchingStateErasure
      typedEvaluation typedMatchingSearch

end TypePM.Source.M5ClosedPairProjectionCertificate
