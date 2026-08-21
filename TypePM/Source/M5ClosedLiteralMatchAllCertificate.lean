import TypePM.Source.M5CompletionArchitecture
import TypePM.Source.M4CanonicalCertificateTransport
import TypePM.TwoIndexMatchAllSafety

/-!
# A concrete search-bearing M5 certificate

This module instantiates the M5 architecture for the closed family

`matchAll literal as something with $x -> x`.

The family is deliberately small, but unlike the preceding pair-projection
fragment it issues a real bounded-DFS matching task.  Its search origin and
search certificate are nonempty.  The typed evaluator obtains the actual
search result through `MatchingStateErasure` and `TypedMatchingSearch`, then
uses that result to type the body traversal.  No completed-search equation or
final evaluation result is stored in the runtime certificate.
-/

namespace TypePM.Source.M5ClosedLiteralMatchAllCertificate

open TypePM.Runtime
open TypePM.Source.M5CompletionArchitecture

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, tyEquations, capEquations, eliminatedVariable?,
        unificationVars, Equation.unificationVars, Ty.unificationVars,
        Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, Ty.nodeCount, Ty.nodeCountList,
        Cap.nodeCount, Cap.nodeCountList,
        Ty.occursTy, Ty.occursTyList, Cap.occurs, Cap.occursList,
        Equation.apply, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
        Subst.singleTy, Subst.singleCap, Subst.compose, Subst.id])

/-- The complete closed source family admitted by this certificate. -/
def literalVariableMatchAll (literal : Int) : Expr :=
  .matchAll (.lit literal) .something .var (.var 0)

private def literalVariableGenerated : Generated :=
  { target := DataTypes.list (.var ⟨0⟩)
    hard := [.ty (.var ⟨0⟩) .int]
    pending :=
      [⟨.matcher .any (.var ⟨1⟩), .slot (.var ⟨0⟩) .int⟩] }

private theorem literalVariable_elaborate_exact
    (signature : FrozenSignature) (literal : Int) :
    M4.elaborate signature [] (literalVariableMatchAll literal) ⟨0, 0⟩ =
      some (literalVariableGenerated, ⟨2, 1⟩) := by
  unfold literalVariableMatchAll M4.elaborate
  rfl'

private theorem literalVariable_close_exact :
    (inferGeneratedUsing unify literalVariableGenerated).bind
        (fun closed => some closed.target) =
      some (DataTypes.list .int) := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [literalVariableGenerated, DataTypes.list]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherProduct, Ty.mayBecomeExpectedMatcher,
    Ty.mayBecomeExpectedSlot, Ty.apply, Cap.apply, Subst.compose]
  have resolutionTrace :
      resolve (.matcher .any (.var ⟨1⟩)) (.slot (.var ⟨0⟩) .int) =
        .matcherToSlot .any (.var ⟨0⟩) (.var ⟨1⟩) .int .equal := by
    rfl
  simp only [residualEquations, CheckObligation.residualEquations,
    CheckObligation.resolutionUnder]
  simp [Ty.apply, Cap.apply]
  rw [resolutionTrace]
  simp [Resolution.equations, CapabilityResolution.equations]
  compute_unification

/-- Every integer literal in the family has the same public principal type. -/
theorem literalVariable_infer_exact
    (signature : FrozenSignature) (literal : Int) :
    M4.infer signature [] (literalVariableMatchAll literal) =
      some (DataTypes.list .int) := by
  unfold M4.infer
  rw [show Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    literalVariable_elaborate_exact]
  exact literalVariable_close_exact

/-- A syntax-directed, ground-typed description of the admitted family. -/
inductive Fragment : Expr → Ty → Prop where
  | literal (value : Int) :
      Fragment (literalVariableMatchAll value) (DataTypes.list .int)

def Supported (expression : Expr) : Prop :=
  ∃ target, Fragment expression target

namespace Fragment

theorem mnodeFree (fragment : Fragment expression target) :
    expression.MNodeFree := by
  cases fragment
  simp [literalVariableMatchAll, Expr.MNodeFree,
    Pattern.MNodeFree, PatternFunctionExpansion.expandExpr,
    PatternFunctionExpansion.expandPattern]

theorem apply (fragment : Fragment expression target)
    (substitution : Subst) :
    Fragment expression (target.apply substitution) := by
  cases fragment with
  | literal value =>
      simpa [DataTypes.list, Ty.apply, Ty.applyList] using
        (Fragment.literal value)

end Fragment

namespace Supported

theorem mnodeFree (supported : Supported expression) :
    expression.MNodeFree := by
  rcases supported with ⟨target, fragment⟩
  exact fragment.mnodeFree

end Supported

/-- Global M4 principality identifies every independently chosen principal
derivation of this ground family with the executable representative. -/
theorem principal_target_eq
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {literal : Int} {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature []
      (literalVariableMatchAll literal) principal) :
    principal = DataTypes.list .int := by
  have sourceTyping : M4.Typing signature []
      (literalVariableMatchAll literal) principal :=
    ⟨principal, ⟨derivation⟩, ⟨Subst.id, Ty.apply_id principal⟩⟩
  obtain ⟨substitution, equation⟩ :=
    (M4.infer_success_principalResult wellFormed
      (literalVariable_infer_exact signature literal)).2 principal sourceTyping
  have forward : DataTypes.list .int = principal := by
    simpa [DataTypes.list, Ty.apply, Ty.applyList] using equation
  exact forward.symm

/-! ## Local two-index matching certificate -/

def literalVariableTask (literal : Int) : BoundedDfsMatchingSearchTask :=
  { environment := []
    pattern := .var
    patternMNodeFree := by
      simp [Pattern.MNodeFree, PatternFunctionExpansion.expandPattern]
    matcher := .something
    target := .int literal }

private def literalVariableAtom (literal : Int) : MatchingAtom :=
  ⟨.var, .something, .int literal⟩

private theorem literalVariable_reducer_exact
    (callbackFuel : Nat) (literal : Int) :
    evaluationAtomReducer (evalFuel callbackFuel) []
        (literalVariableAtom literal) =
      .ok (.hit ⟨[[]], [.int literal]⟩) := by
  rfl

/-- The initial built-in variable state is locally safe for every callback
fuel, DFS budget, and requested answer index. -/
theorem literalVariable_initial_twoIndex
    (callbackFuel searchFuel residual : Nat) (literal : Int) :
    TwoIndexMatchingStateTyping FuelEnvironmentSafe FuelEnvironmentSafe
      (evaluationAtomReducer (evalFuel callbackFuel)) searchFuel residual
      ⟨[literalVariableAtom literal], [], []⟩ [.int] := by
  cases searchFuel with
  | zero => exact .zero
  | succ searchFuel =>
      apply TwoIndexMatchingStateTyping.reduce
        (FuelEnvironmentSafe.nil (searchFuel + 1 + residual))
        (FuelEnvironmentSafe.nil (searchFuel + 1 + residual))
      let reduction : AtomReduction := ⟨[[]], [.int literal]⟩
      apply TwoIndexAtomReducerCertificate.hit reduction
      · simpa [reduction] using
          literalVariable_reducer_exact callbackFuel literal
      · intro successor member
        simp only [MatchingState.successors] at member
        rcases List.mem_map.mp member with ⟨branch, branchMember, rfl⟩
        simp only [reduction, List.mem_singleton] at branchMember
        subst branch
        cases searchFuel with
        | zero => exact .zero
        | succ searchFuel =>
            simpa [MatchingState.continueWith, reduction] using
              (TwoIndexMatchingStateTyping.yield
                (FuelEnvironmentSafe.nil (searchFuel + 1 + residual))
                (FuelEnvironmentSafe.cons
                  (fuelValueSafe_int literal (searchFuel + 1 + residual))
                  (FuelEnvironmentSafe.nil
                    (searchFuel + 1 + residual))))

/-! ## Concrete M5 certificate and nonempty search origin -/

inductive Certificate
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {principal : Ty}
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal) : List Ty → Prop where
  | literal
      (contextEq : context = [])
      (fragment : Fragment expression principal) :
      Certificate derivation []

def ClosedRuntimeContextRelation : RuntimeContextRelation :=
  @fun _signature context _expression _principal _derivation runtimeContext =>
    context = [] ∧ runtimeContext = []

theorem closedRuntimeContext_realizable :
    ClosedContextRealizable ClosedRuntimeContextRelation := by
  intro signature expression principal derivation
  exact ⟨rfl, rfl⟩

theorem principalStateErasure : PrincipalStateErasure Supported Certificate
    ClosedRuntimeContextRelation := by
  intro signature context expression principal derivation runtimeContext
    signatureReady supported contextCompatible
  rcases contextCompatible with ⟨rfl, rfl⟩
  rcases supported with ⟨target, fragment⟩
  cases fragment with
  | literal value =>
      have targetEq := principal_target_eq signatureReady.1 derivation
      subst principal
      exact .literal rfl (.literal value)

inductive SearchOrigin :
    MatchingSearchOriginFamily BoundedDfsMatchingSearchTask where
  | issued
      {signature : FrozenSignature} {value : Int}
      {derivation : M4.PrincipalTypingDerivation signature []
        (literalVariableMatchAll value) (DataTypes.list .int)}
      (callbackFuel searchFuel resultIndex : Nat)
      (targetSuccess :
        evalFuel callbackFuel [] (.lit value) = .ok (.int value))
      (matcherSuccess :
        evalFuel callbackFuel [] .something = .ok .something) :
      SearchOrigin derivation [] (literalVariableTask value) [.int]
        (callbackFuel + searchFuel + resultIndex)

/-- A ground-task tag produced by state erasure.  The input index is retained
as part of the architecture boundary; the uniform two-index initial-state
proof is reconstructed from this tag by `typedMatchingSearch`. -/
inductive SearchCertificate :
    MatchingSearchCertificateFamily BoundedDfsMatchingSearchTask where
  | literal (value : Int) (inputIndex : Nat) :
      SearchCertificate (literalVariableTask value) [.int] inputIndex

theorem matchingStateErasure :
    MatchingStateErasure Certificate SearchOrigin SearchCertificate := by
  intro signature context expression principal derivation runtimeContext task
    answerTypes inputIndex certificate origin
  cases certificate with
  | literal contextEq fragment =>
      subst context
      cases origin
      exact .literal _ _

theorem typedMatchingSearch : TypedMatchingSearch SearchCertificate
    fuelIndexedSafetyRelations runBoundedDfsMatchingSearch := by
  intro task answerTypes callbackFuel searchFuel resultIndex certificate
  cases certificate with
  | literal value inputIndex =>
      change FuelMatchingSearchResultSafe resultIndex [.int]
        (searchPatternFuel (evalFuel callbackFuel) searchFuel [] .var
          .something (.int value))
      simpa [runBoundedDfsMatchingSearch, literalVariableTask,
        literalVariableAtom] using
        (searchPatternFuel_twoIndexSafe
          IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
          IndexedMatchingInvariant.fuelEnvironmentSafe_downwardClosed
          (literalVariable_initial_twoIndex callbackFuel searchFuel resultIndex
            value))

private theorem literal_target_safe (fuel : Nat) (value : Int) :
    FuelResultSafe fuel .int (evalFuel fuel [] (.lit value)) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨.int value, rfl, fuelValueSafe_int value (fuel + 1)⟩

private theorem something_matcher_safe (fuel : Nat) :
    FuelResultSafe fuel (.matcher .any .int)
      (evalFuel fuel [] .something) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
      exact .inr ⟨.something, rfl, fuelValueSafe_something .int (fuel + 1)⟩

private theorem literalVariable_body_safe
    (evaluationFuel resultIndex : Nat) :
    EvaluatedBindingBodySafeUnder (FuelEnvironmentSafe resultIndex)
      evaluationFuel resultIndex [] [.int] (.var 0) .int := by
  intro bindings bindingsSafe
  cases evaluationFuel with
  | zero => exact .inl rfl
  | succ evaluationFuel =>
      cases bindings with
      | nil =>
          have impossible := bindingsSafe.1
          simp at impossible
      | cons value values =>
          have valuesLength : values.length = 0 := by
            simpa using bindingsSafe.1
          have valuesEq : values = [] := by simpa using valuesLength
          subst values
          obtain ⟨foundValue, found, foundSafe⟩ :=
            bindingsSafe.2 0 .int (by simp)
          have valueEq : value = foundValue := by simpa using found
          subst foundValue
          exact .inr ⟨value, rfl, foundSafe⟩

private theorem evaluated_search_safe
    {signature : FrozenSignature} {value : Int}
    {derivation : M4.PrincipalTypingDerivation signature []
      (literalVariableMatchAll value) (DataTypes.list .int)}
    (certificate : Certificate derivation [])
    (operationalFuel resultIndex : Nat) :
    EvaluatedPatternSearchSafeUnder (FuelEnvironmentSafe resultIndex)
      operationalFuel [] (.lit value) .something .var [.int] := by
  intro targetValue matcherValue targetSuccess matcherSuccess
  cases operationalFuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ operationalFuel =>
      simp [evalFuel] at targetSuccess matcherSuccess
      subst targetValue
      subst matcherValue
      have origin : SearchOrigin derivation [] (literalVariableTask value)
          [.int] ((operationalFuel + 1) + (operationalFuel + 1) +
            resultIndex) :=
        .issued (operationalFuel + 1) (operationalFuel + 1) resultIndex
          rfl rfl
      have searchCertificate : SearchCertificate (literalVariableTask value)
          [.int] ((operationalFuel + 1) + (operationalFuel + 1) +
            resultIndex) :=
        matchingStateErasure certificate origin
      have searchSafe := typedMatchingSearch (operationalFuel + 1)
        (operationalFuel + 1) resultIndex searchCertificate
      change FuelMatchingSearchResultSafe resultIndex [.int]
        (searchPatternFuel (evalFuel (operationalFuel + 1))
          (operationalFuel + 1) [] .var .something (.int value))
      simpa [runBoundedDfsMatchingSearch, literalVariableTask,
        fuelIndexedSafetyRelations] using searchSafe

/-- The expression-side proof uses the nonempty search certificate above for
the exact task selected by successful target and matcher evaluations. -/
theorem typedEvaluation : TypedEvaluation Certificate
    fuelIndexedSafetyRelations evalFuel := by
  intro signature context expression principal target derivation runtimeContext
    certificate instantiation evaluationFuel resultIndex environment
    environmentSafe
  cases certificate with
  | literal contextEq fragment =>
      subst context
      cases fragment with
      | literal value =>
          rcases instantiation with ⟨substitution, targetEquation⟩
          have targetEq : target = DataTypes.list .int := by
            simpa [DataTypes.list, Ty.apply, Ty.applyList] using
              targetEquation.symm
          subst target
          have environmentEq : environment = [] := by
            have := environmentSafe.1
            simpa using this
          subst environment
          have currentCertificate : Certificate derivation [] :=
            .literal rfl (.literal value)
          cases evaluationFuel with
          | zero => exact .inl rfl
          | succ operationalFuel =>
              simpa [Nat.succ_eq_add_one, fuelIndexedSafetyRelations,
                literalVariableMatchAll, DataTypes.list, Ty.apply,
                Ty.applyList] using
                (matchAllFuel_valueAndBindingIndexedSafe
                  (literal_target_safe operationalFuel value)
                  (something_matcher_safe operationalFuel)
                  (evaluated_search_safe currentCertificate
                    operationalFuel resultIndex)
                  (literalVariable_body_safe operationalFuel resultIndex))

theorem closedNoStuck : ClosedNoStuck Supported evalFuel :=
  closedNoStuck_of_principalStateErasure_and_typedEvaluation
    closedRuntimeContext_realizable principalStateErasure typedEvaluation

theorem closedRuntimeCertificateRespectsCoherence :
    ClosedRuntimeCertificateRespectsCoherence Certificate := by
  intro signature expression leftPrincipal rightPrincipal left right pair
    alignment certificate
  cases certificate with
  | literal contextEq fragment =>
      obtain ⟨forward, _backward⟩ :=
        alignment.principalTargets_mutualInstances left right
      rcases forward with ⟨substitution, targetEquation⟩
      have rightFragment : Fragment expression rightPrincipal := by
        rw [← targetEquation]
        exact fragment.apply substitution
      exact .literal contextEq rightFragment

/-- A complete M5 conditional schema whose matching fields are genuinely
inhabited and whose typed evaluation consumes the same bounded-DFS search
certificate. -/
theorem conditionalCompletionSchema :
    ConditionalCompletionSchema Supported Certificate
      ClosedRuntimeContextRelation fuelIndexedSafetyRelations evalFuel
      SearchOrigin SearchCertificate runBoundedDfsMatchingSearch :=
  conditionalCompletionSchema_of_components
    closedRuntimeContext_realizable principalStateErasure matchingStateErasure
      typedEvaluation typedMatchingSearch

end TypePM.Source.M5ClosedLiteralMatchAllCertificate
