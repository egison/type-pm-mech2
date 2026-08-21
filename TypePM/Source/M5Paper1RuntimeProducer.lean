import TypePM.Source.M5PrincipalOriginCertificate

/-!
# Paper-1 runtime scope and its principal origin producer

The scope below is a recursively M-node-free source fragment.  A `letE` is
admitted either when its right-hand side belongs to the explicitly closed
first-order subgrammar or when the exact principal derivation carries the
arity-zero source-context condition required by S6.  Thus the scope cannot
hide a general open polymorphic let behind an expression-only proposition,
and it does not store the runtime producer that the later theorem is meant to
construct.

The first producer theorem in this module covers the variable/literal leaf
boundary.  It is an independently checked base for the subsequent structural
induction over tuples, calls, closed lets, recursion, and matching forms.
-/

namespace TypePM.Source.M5Paper1RuntimeProducer

open TypePM.Runtime
open M5CompletionArchitecture
open M5PrincipalOriginCertificate

mutual

  /-- Closed, binder-free right-hand sides admitted by the Paper-1 `letE`
  constructor.  Variables, lambdas, applications, recursion, matcher
  literals, and matching forms are deliberately absent. -/
  inductive ClosedRhs : Expr → Prop where
    | lit : ClosedRhs (.lit literal)
    | something : ClosedRhs .something
    | tuple (items : ClosedRhss expressions) : ClosedRhs (.tuple expressions)
    | ctor (arguments : ClosedRhss expressions) :
        ClosedRhs (.ctor constructor expressions)
    | prim
        (notMap : operation ≠ .map)
        (arguments : ClosedRhss expressions) :
        ClosedRhs (.prim operation expressions)
    | ifE
        (condition : ClosedRhs conditionExpression)
        (thenBranch : ClosedRhs thenExpression)
        (elseBranch : ClosedRhs elseExpression) :
        ClosedRhs (.ifE conditionExpression thenExpression elseExpression)

  inductive ClosedRhss : List Expr → Prop where
    | nil : ClosedRhss []
    | cons (head : ClosedRhs expression) (tail : ClosedRhss expressions) :
        ClosedRhss (expression :: expressions)

end

mutual

  /-- Explicit Paper-1 runtime scope.  Pattern-function nodes (`embed` and
  pattern `app`) have no constructors, so every admitted expression is
  recursively M-node-free. -/
  inductive Scope : Expr → Prop where
    | var : Scope (.var position)
    | lit : Scope (.lit literal)
    | something : Scope .something
    | lam (body : Scope bodyExpression) : Scope (.lam bodyExpression)
    | app (function : Scope functionExpression)
        (argument : Scope argumentExpression) :
        Scope (.app functionExpression argumentExpression)
    | tuple (items : Scopes expressions) : Scope (.tuple expressions)
    | letClosed
        (value : ClosedRhs valueExpression)
        (body : Scope bodyExpression) :
        Scope (.letE valueExpression bodyExpression)
    | ctor (arguments : Scopes expressions) :
        Scope (.ctor constructor expressions)
    | prim (arguments : Scopes expressions) :
        Scope (.prim operation expressions)
    | ifE
        (condition : Scope conditionExpression)
        (thenBranch : Scope thenExpression)
        (elseBranch : Scope elseExpression) :
        Scope (.ifE conditionExpression thenExpression elseExpression)
    | fixE (body : Scope bodyExpression) : Scope (.fixE bodyExpression)
    | matcher (clauses : MatcherClausesScope sourceClauses) :
        Scope (.matcher sourceClauses)
    | matchAll
        (target : Scope targetExpression)
        (matcher : Scope matcherExpression)
        (pattern : PatternScope sourcePattern)
        (body : Scope bodyExpression) :
        Scope (.matchAll targetExpression matcherExpression sourcePattern
          bodyExpression)
    | matchFirst
        (target : Scope targetExpression)
        (matcher : Scope matcherExpression)
        (arms : MatchFirstArmsScope sourceArms)
        (fallback : Scope fallbackExpression) :
        Scope (.matchFirst targetExpression matcherExpression sourceArms
          fallbackExpression)

  inductive Scopes : List Expr → Prop where
    | nil : Scopes []
    | cons (head : Scope expression) (tail : Scopes expressions) :
        Scopes (expression :: expressions)

  inductive PatternScope : Pattern → Prop where
    | var : PatternScope .var
    | wild : PatternScope .wild
    | value (expression : Scope sourceExpression) :
        PatternScope (.value sourceExpression)
    | ctor (fields : PatternScopes sourcePatterns) :
        PatternScope (.ctor constructor sourcePatterns)
    | tuple (items : PatternScopes sourcePatterns) :
        PatternScope (.tuple sourcePatterns)
    | and (left : PatternScope leftPattern)
        (right : PatternScope rightPattern) :
        PatternScope (.and leftPattern rightPattern)
    | or (left : PatternScope leftPattern)
        (right : PatternScope rightPattern) :
        PatternScope (.or leftPattern rightPattern)

  inductive PatternScopes : List Pattern → Prop where
    | nil : PatternScopes []
    | cons (head : PatternScope pattern) (tail : PatternScopes patterns) :
        PatternScopes (pattern :: patterns)

  inductive MatcherClausesScope : List MatcherClause → Prop where
    | nil : MatcherClausesScope []
    | cons
        (nextMatchers : Scope nextMatcherExpression)
        (arms : MatcherArmsScope sourceArms)
        (tail : MatcherClausesScope sourceClauses) :
        MatcherClausesScope
          (MatcherClause.mk header nextMatcherExpression sourceArms ::
            sourceClauses)

  inductive MatcherArmsScope : List MatcherArm → Prop where
    | nil : MatcherArmsScope []
    | cons (body : Scope bodyExpression)
        (tail : MatcherArmsScope sourceArms) :
        MatcherArmsScope
          (MatcherArm.mk header bodyExpression :: sourceArms)

  inductive MatchFirstArmsScope : List MatchFirstArm → Prop where
    | nil : MatchFirstArmsScope []
    | cons
        (pattern : PatternScope sourcePattern)
        (body : Scope bodyExpression)
        (tail : MatchFirstArmsScope sourceArms) :
        MatchFirstArmsScope
          (MatchFirstArm.mk sourcePattern bodyExpression :: sourceArms)

end

/-- Derivation-indexed Paper-1 scope used by the M5 architecture.  The first
constructor recursively restricts every `letE` to `ClosedRhs`.  The second
admits an open right-hand side at a `letE` only when the exact source context
stored by the principal derivation satisfies S6's arity-zero premise. -/
inductive RuntimeScope : M5CompletionArchitecture.RuntimeScope where
  | closed
      (syntaxScope : Scope expression)
      (mnodeFree : expression.MNodeFree) :
      RuntimeScope derivation
  | letArityZero
      (contextArityZero : M4.ContextSchemeArityZero context)
      (value : Scope valueExpression)
      (body : Scope bodyExpression)
      (mnodeFree :
        (Expr.letE valueExpression bodyExpression).MNodeFree) :
      RuntimeScope
        (derivation : M4.PrincipalTypingDerivation signature context
          (.letE valueExpression bodyExpression) principal)

/-- The independently closed first producer boundary. -/
inductive LeafScope : Expr → Prop where
  | var : LeafScope (.var position)
  | lit : LeafScope (.lit literal)
  | something : LeafScope .something

theorem LeafScope.toScope : LeafScope expression → Scope expression
  | .var => .var
  | .lit => .lit
  | .something => .something

private theorem literal_target_eq
    (derivation : M4.PrincipalTypingDerivation signature context (.lit literal)
      principal)
    (instantiation : IsInstance principal target) :
    target = .int := by
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      simp only [M4.ElaboratesFuel] at elaboration
      rcases elaboration with ⟨generatedEq, _nextEq⟩
      rcases instantiation with ⟨later, targetEq⟩
      rw [← targetEq, derivation.target_eq]
      simp [PrincipalBlockClosure.target, generatedEq, Ty.apply]

private theorem literalValueSafe_of_applicable (literal : Int) :
    ∀ demand,
      OriginDemandApplicable demand .int →
        OriginValueSafe demand (.int literal) .int
  | .none, _ => by simp [OriginValueSafe]
  | .fuel index, _ => OriginValueSafe.ofFuel (fuelValueSafe_int literal index)
  | .both left right, applicable =>
      have applicable' : OriginDemandApplicable left .int ∧
          OriginDemandApplicable right .int := by
        simpa only [OriginDemandApplicable] using applicable
      OriginValueSafe.both
        (literalValueSafe_of_applicable literal left applicable'.1)
        (literalValueSafe_of_applicable literal right applicable'.2)
  | .listOf _, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨elementType, impossible, _⟩
      cases impossible
  | .pairOf _ _, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨leftType, rightType, impossible, _left, _right⟩
      cases impossible
  | .bool, applicable => by
      simp only [OriginDemandApplicable] at applicable
      cases applicable
  | .int, _ => OriginValueSafe.int literal
  | .plainCall _ _ _, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨domain, codomain, impossible, _⟩
      cases impossible
termination_by demand => demand

private def literalRequestProducer
    (derivation : M4.PrincipalTypingDerivation signature context (.lit literal)
      principal)
    (runtimeContext : List Ty) :
    PrincipalOriginRequestProducer derivation runtimeContext :=
  PrincipalOriginRequestProducer.ofAdditional
    (fun _operationalFuel _outputDemand => OriginEnvironmentDemand.none)
    (by
      intro operationalFuel outputDemand target instantiation applicable
        environment environmentSafe
      have targetEq := literal_target_eq derivation instantiation
      subst target
      cases operationalFuel with
      | zero => exact .inl rfl
      | succ operationalFuel =>
          exact .inr ⟨.int literal, rfl,
            literalValueSafe_of_applicable literal outputDemand applicable⟩)

private theorem something_target_eq
    (derivation : M4.PrincipalTypingDerivation signature context .something
      principal)
    (instantiation : IsInstance principal target) :
    ∃ itemType, target = .matcher .any itemType := by
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      simp only [M4.ElaboratesFuel] at elaboration
      rcases elaboration with ⟨generatedEq, _nextEq⟩
      rcases instantiation with ⟨later, targetEq⟩
      refine ⟨(Ty.var ⟨context.initialSupply.ty⟩).apply
        (Subst.compose later derivation.closure.substitution), ?_⟩
      have closureTargetEq : derivation.closure.target =
          .matcher .any
            ((Ty.var ⟨context.initialSupply.ty⟩).apply
              derivation.closure.substitution) := by
        simp [PrincipalBlockClosure.target, generatedEq, Ty.apply, Cap.apply]
      have principalEq : principal =
          .matcher .any
            ((Ty.var ⟨context.initialSupply.ty⟩).apply
              derivation.closure.substitution) :=
        derivation.target_eq.trans closureTargetEq
      calc
        target = principal.apply later := targetEq.symm
        _ = (Ty.matcher .any
              ((Ty.var ⟨context.initialSupply.ty⟩).apply
                derivation.closure.substitution)).apply later := by
              exact congrArg (Ty.apply later) principalEq
        _ = Ty.matcher .any
              ((Ty.var ⟨context.initialSupply.ty⟩).apply
                (Subst.compose later derivation.closure.substitution)) := by
              have inner := Ty.apply_compose later
                derivation.closure.substitution
                (Ty.var ⟨context.initialSupply.ty⟩)
              simpa only [Ty.apply, Cap.apply] using
                congrArg (Ty.matcher Cap.any) inner

private theorem no_product_conversion_to_anyMatcher
    (conversion : CheckConversion conversionClass
      (.prod [leftType, rightType]) (.matcher .any itemType)) : False := by
  generalize sourceEq : Ty.prod [leftType, rightType] = source at conversion
  cases conversion <;> simp at sourceEq ⊢

private theorem somethingValueSafe_of_applicable (itemType : Ty) :
    ∀ demand,
      OriginDemandApplicable demand (.matcher .any itemType) →
        OriginValueSafe demand .something (.matcher .any itemType)
  | .none, _ => by simp [OriginValueSafe]
  | .fuel index, _ =>
      OriginValueSafe.ofFuel (fuelValueSafe_something itemType index)
  | .both left right, applicable =>
      have applicable' :
          OriginDemandApplicable left (.matcher .any itemType) ∧
            OriginDemandApplicable right (.matcher .any itemType) := by
        simpa only [OriginDemandApplicable] using applicable
      OriginValueSafe.both
        (somethingValueSafe_of_applicable itemType left applicable'.1)
        (somethingValueSafe_of_applicable itemType right applicable'.2)
  | .listOf _, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨elementType, impossible, _⟩
      cases impossible
  | .pairOf _ _, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨leftType, rightType, impossible, _left, _right⟩
      cases impossible
  | .bool, applicable => by
      simp only [OriginDemandApplicable] at applicable
      cases applicable
  | .int, applicable => by
      simp only [OriginDemandApplicable] at applicable
      cases applicable
  | .plainCall _ _ _, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨domain, codomain, impossible, _⟩
      cases impossible
termination_by demand => demand

private def somethingRequestProducer
    (derivation : M4.PrincipalTypingDerivation signature context .something
      principal)
    (runtimeContext : List Ty) :
    PrincipalOriginRequestProducer derivation runtimeContext :=
  PrincipalOriginRequestProducer.ofAdditional
    (fun _operationalFuel _outputDemand => OriginEnvironmentDemand.none)
    (by
      intro operationalFuel outputDemand target instantiation applicable
        environment environmentSafe
      obtain ⟨itemType, targetEq⟩ :=
        something_target_eq derivation instantiation
      subst target
      cases operationalFuel with
      | zero => exact .inl rfl
      | succ operationalFuel =>
          exact .inr ⟨.something, rfl,
            somethingValueSafe_of_applicable itemType outputDemand
              applicable⟩)

/-- Search-free leaf producer.  Variables use the exact raw request plan;
literals use their canonical integer result and the applicability proof.  The
runtime-context stability premise is concrete and is automatic for closed
programs. -/
theorem LeafScope.derivationRequestProducer
    (scope : LeafScope expression)
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext) :
    DerivationRequestProducer derivation runtimeContext := by
  cases scope with
  | @var position =>
      let inputDemand : Nat → OriginDemand → OriginEnvironmentDemand :=
        fun _ outputDemand =>
          OriginEnvironmentDemand.single position outputDemand
      have plans : ∀ operationalFuel outputDemand,
          M4.RawOriginRequestPlan operationalFuel (.var position) outputDemand
            (inputDemand operationalFuel outputDemand) := by
        intro operationalFuel outputDemand
        exact .var
      exact derivationRequestProducer_of_raw
        (PrincipalRawOriginPlanProducer.ofStablePlans contextCompatible stable
          inputDemand plans)
  | lit =>
      exact ⟨literalRequestProducer derivation runtimeContext⟩
  | something =>
      exact ⟨somethingRequestProducer derivation runtimeContext⟩

/-- Derivation-indexed leaf scope used for the independently closed base of
the full Paper-1 induction. -/
def LeafRuntimeScope : M5CompletionArchitecture.RuntimeScope :=
  fun {_signature} {_context} {expression} {_principal} _derivation =>
    LeafScope expression

/-- Open monomorphic context realization strengthened by the exact condition
needed to reuse it after any public instance substitution. -/
def StableMonomorphicRuntimeContextRelation : RuntimeContextRelation :=
  fun derivation runtimeContext =>
    MonomorphicRuntimeContextRelation derivation runtimeContext ∧
      PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
        runtimeContext

theorem stableMonomorphicRuntimeContext_closed :
    ClosedContextRealizable StableMonomorphicRuntimeContextRelation := by
  intro signature expression principal derivation
  exact ⟨monomorphicRuntimeContext_closed derivation,
    PrincipalRawOriginPlanProducer.substitutionStable_nil⟩

/-- Principal state erasure for the leaf base, now using the
derivation-indexed architecture scope. -/
theorem leafPrincipalStateErasure :
    PrincipalStateErasure LeafRuntimeScope Certificate
      StableMonomorphicRuntimeContextRelation := by
  intro signature context expression principal derivation runtimeContext
    signatureReady scope contextRealization
  rcases contextRealization with ⟨contextCompatible, stable⟩
  exact certificate_of_derivationRequestProducer signatureReady
    contextCompatible
    (scope.derivationRequestProducer derivation runtimeContext
      contextCompatible stable)

/-! ## Search-free binary tuple trees -/

/-- Ground integer/pair trees.  This is a structural search-free fragment,
not a fixed expression fixture. -/
inductive PairTree : Expr → Ty → Prop where
  | lit : PairTree (.lit literal) .int
  | pair
      (left : PairTree leftExpression leftTarget)
      (right : PairTree rightExpression rightTarget) :
      PairTree (.tuple [leftExpression, rightExpression])
        (.prod [leftTarget, rightTarget])

namespace PairTree

/-- Every pair tree has a raw plan for every ordinary fuel observation. -/
theorem fuelPlan
    (tree : PairTree expression target)
    (operationalFuel resultIndex : Nat) :
    ∃ inputDemand,
      M4.RawOriginRequestPlan operationalFuel expression (.fuel resultIndex)
        inputDemand := by
  induction tree generalizing operationalFuel with
  | lit =>
      exact ⟨OriginEnvironmentDemand.none, .litFuel⟩
  | @pair leftExpression leftTarget rightExpression rightTarget left right
      leftIH rightIH =>
      cases operationalFuel with
      | zero => exact ⟨OriginEnvironmentDemand.none, .timeout⟩
      | succ childFuel =>
          obtain ⟨leftInput, leftPlan⟩ := leftIH childFuel
          obtain ⟨rightInput, rightPlan⟩ := rightIH childFuel
          exact ⟨OriginEnvironmentDemand.both leftInput
              (OriginEnvironmentDemand.both rightInput
                OriginEnvironmentDemand.none),
            .tupleFuel (.cons leftPlan (.cons rightPlan .nil))⟩

/-- Demand-directed raw planner for pair trees.  Applicability rules out
ill-shaped observations; every admitted structural observation is translated
to the corresponding raw plan constructor. -/
theorem plan
    (tree : PairTree expression target) :
    ∀ operationalFuel outputDemand,
      OriginDemandApplicable outputDemand target →
        ∃ inputDemand,
          M4.RawOriginRequestPlan operationalFuel expression outputDemand
            inputDemand
  | operationalFuel, .none, _ => by
      obtain ⟨inputDemand, available⟩ := tree.fuelPlan operationalFuel 0
      exact ⟨inputDemand, .universal available .none⟩
  | operationalFuel, .fuel resultIndex, _ =>
      tree.fuelPlan operationalFuel resultIndex
  | operationalFuel, .both leftDemand rightDemand, applicable => by
      have applicable' : OriginDemandApplicable leftDemand target ∧
          OriginDemandApplicable rightDemand target := by
        simpa only [OriginDemandApplicable] using applicable
      obtain ⟨leftInput, leftPlan⟩ :=
        tree.plan operationalFuel leftDemand applicable'.1
      obtain ⟨rightInput, rightPlan⟩ :=
        tree.plan operationalFuel rightDemand applicable'.2
      exact ⟨OriginEnvironmentDemand.both leftInput rightInput,
        .both leftPlan rightPlan⟩
  | operationalFuel, .listOf elementDemand, applicable => by
      cases tree with
      | lit =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨elementType, impossible, _⟩
          cases impossible
      | pair left right =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨elementType, impossible, _⟩
          cases impossible
  | operationalFuel, .pairOf leftDemand rightDemand, applicable => by
      cases tree with
      | lit =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨leftType, rightType, impossible,
            _leftApplicable, _rightApplicable⟩
          cases impossible
      | @pair leftExpression leftTarget rightExpression rightTarget left right =>
          simp only [OriginDemandApplicable] at applicable
          rcases applicable with ⟨actualLeft, actualRight, targetEq,
            leftApplicable, rightApplicable⟩
          simp only [Ty.prod.injEq, List.cons.injEq, and_true] at targetEq
          obtain ⟨rfl, rfl⟩ := targetEq
          cases operationalFuel with
          | zero => exact ⟨OriginEnvironmentDemand.none, .timeout⟩
          | succ childFuel =>
              obtain ⟨leftInput, leftPlan⟩ :=
                left.plan childFuel leftDemand leftApplicable
              obtain ⟨rightInput, rightPlan⟩ :=
                right.plan childFuel rightDemand rightApplicable
              exact ⟨OriginEnvironmentDemand.both leftInput rightInput,
                .tuplePair leftPlan rightPlan⟩
  | operationalFuel, .bool, applicable => by
      cases tree <;> simp [OriginDemandApplicable, DataTypes.bool] at applicable
  | operationalFuel, .int, applicable => by
      cases tree with
      | lit => exact ⟨OriginEnvironmentDemand.none, .litInt⟩
      | pair left right =>
          simp [OriginDemandApplicable] at applicable
  | operationalFuel, .plainCall callFuel argumentDemand resultDemand,
      applicable => by
      cases tree <;> simp [OriginDemandApplicable] at applicable
termination_by _ outputDemand => outputDemand

/-- The generated target of a pair-tree elaboration is its ground structural
target before solving. -/
theorem elaboration_target
    (tree : PairTree expression target)
    (elaboration : M4.ElaboratesFuel signature staticFuel context expression
      supply generated next) :
    generated.target = target := by
  induction tree generalizing staticFuel context supply generated next with
  | lit =>
      cases staticFuel with
      | zero => exact False.elim elaboration
      | succ staticFuel =>
          simp only [M4.ElaboratesFuel] at elaboration
          rcases elaboration with ⟨generatedEq, _nextEq⟩
          simp [generatedEq]
  | @pair leftExpression leftTarget rightExpression rightTarget left right
      leftIH rightIH =>
      cases staticFuel with
      | zero => exact False.elim elaboration
      | succ childStaticFuel =>
          simp only [M4.ElaboratesFuel] at elaboration
          rcases elaboration with ⟨generatedItems, itemsElaboration, generatedEq⟩
          cases itemsElaboration with
          | cons leftElaboration tailElaboration =>
              cases tailElaboration with
              | cons rightElaboration nilElaboration =>
                  cases nilElaboration
                  have leftEq := leftIH leftElaboration
                  have rightEq := rightIH rightElaboration
                  simp [generatedEq, leftEq, rightEq]

/-- Pair-tree targets are ground and therefore fixed by every substitution. -/
theorem target_apply
    (tree : PairTree expression target) (substitution : Subst) :
    target.apply substitution = target := by
  induction tree with
  | lit => simp [Ty.apply]
  | pair left right leftIH rightIH =>
      simp [Ty.apply, Ty.applyList, leftIH, rightIH]

theorem principal_target_eq
    (tree : PairTree expression expected)
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal) :
    principal = expected := by
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  have generatedEq := tree.elaboration_target elaboration
  rw [derivation.target_eq]
  simp only [PrincipalBlockClosure.target, generatedEq]
  exact tree.target_apply derivation.closure.substitution

/-- Total request policy selected from the demand-directed plan theorem. -/
noncomputable def inputDemand
    (tree : PairTree expression expected) :
    Nat → OriginDemand → OriginEnvironmentDemand := by
  classical
  exact fun operationalFuel outputDemand =>
    if applicable : OriginDemandApplicable outputDemand expected then
      Classical.choose (tree.plan operationalFuel outputDemand applicable)
    else OriginEnvironmentDemand.none

noncomputable def requestProducer
    (tree : PairTree expression expected)
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext) :
    PrincipalOriginRequestProducer derivation runtimeContext where
  inputDemand := tree.inputDemand
  request := by
    classical
    intro operationalFuel outputDemand target instantiation applicable
    have principalEq := tree.principal_target_eq derivation
    rcases instantiation with ⟨later, targetEq⟩
    have targetExpected : target = expected := by
      calc
        target = principal.apply later := targetEq.symm
        _ = expected.apply later := by rw [principalEq]
        _ = expected := tree.target_apply later
    have applicableExpected : OriginDemandApplicable outputDemand expected := by
      rw [← targetExpected]
      exact applicable
    have selected := tree.plan operationalFuel outputDemand applicableExpected
    have plan : M4.RawOriginRequestPlan operationalFuel expression outputDemand
        (tree.inputDemand operationalFuel outputDemand) := by
      rw [inputDemand, dif_pos applicableExpected]
      exact Classical.choose_spec selected
    exact ⟨.raw plan (by
      intro later laterEq environment environmentSafe
      have postcomposed := contextCompatible.postcompose later
      rw [stable later] at postcomposed
      exact environmentSafe.toSchemeOrigin postcomposed)⟩

theorem derivationRequestProducer
    (tree : PairTree expression expected)
    (derivation : M4.PrincipalTypingDerivation signature context expression
      principal)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext) :
    DerivationRequestProducer derivation runtimeContext :=
  ⟨tree.requestProducer derivation runtimeContext contextCompatible stable⟩

end PairTree

/-! ## Open monomorphic alias lets -/

namespace ArityZeroAlias

/-- Input policy for `let x = outer[position] in x`.  At zero evaluator fuel
the whole expression times out before inspecting the environment.  At a
positive fuel the value occurrence and the body's free tail are kept as the
two explicit S6 premises. -/
def inputDemand (position operationalFuel : Nat)
    (outputDemand : OriginDemand) : OriginEnvironmentDemand :=
  match operationalFuel with
  | 0 => OriginEnvironmentDemand.none
  | _ + 1 =>
      OriginEnvironmentDemand.both
        (OriginEnvironmentDemand.single position outputDemand)
        (OriginEnvironmentDemand.tail
          (OriginEnvironmentDemand.single 0 outputDemand))

/-- Exact S6 request evidence for an open monomorphic alias let.  This is a
genuine open-right-hand-side family, not a closed fixture: the surrounding
position, operational fuel, public instance type, and applicable result
observation are all arbitrary. -/
def requestProducer
    (derivation : M4.PrincipalTypingDerivation signature context
      (.letE (.var position) (.var 0)) principal)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext)
    (contextArityZero : M4.ContextSchemeArityZero context) :
    PrincipalOriginRequestProducer derivation runtimeContext where
  inputDemand := inputDemand position
  request := by
    intro operationalFuel outputDemand target _instantiation _applicable
    have environmentTransport : ∀ later,
        principal.apply later = target →
          ∀ environment,
            OriginEnvironmentSafe (inputDemand position operationalFuel
              outputDemand) environment runtimeContext →
              SchemeOriginEnvironmentSafe
                (inputDemand position operationalFuel outputDemand)
                (Subst.compose later derivation.closure.substitution)
                environment context := by
      intro later _targetEq environment environmentSafe
      have postcomposed := contextCompatible.postcompose later
      rw [stable later] at postcomposed
      exact environmentSafe.toSchemeOrigin postcomposed
    cases operationalFuel with
    | zero =>
        exact ⟨.raw .timeout environmentTransport⟩
    | succ childFuel =>
        let valueInput :=
          OriginEnvironmentDemand.single position outputDemand
        let bodyInput := OriginEnvironmentDemand.single 0 outputDemand
        let plan : M4.RawOriginLetArityZeroPlan context childFuel
            (.var position) (.var 0) outputDemand valueInput bodyInput :=
          { contextArityZero := contextArityZero
            valuePlan := .var
            bodyPlan := .var }
        exact ⟨.elaboration (by
          intro staticFuel supply generated next sourceElaboration
          cases staticFuel with
          | zero => exact False.elim sourceElaboration
          | succ staticFuel =>
              simpa [inputDemand, valueInput, bodyInput] using
                plan.exactCertificate sourceElaboration)
          (by simpa [inputDemand, valueInput, bodyInput] using
            environmentTransport)⟩

/-- Derivation-indexed arbitrary-fuel producer for the open monomorphic alias
slice of the Paper-1 let scope. -/
theorem derivationRequestProducer
    (derivation : M4.PrincipalTypingDerivation signature context
      (.letE (.var position) (.var 0)) principal)
    (runtimeContext : List Ty)
    (contextCompatible : MonomorphicRuntimeContextRelation derivation
      runtimeContext)
    (stable : PrincipalRawOriginPlanProducer.SubstitutionStableRuntimeContext
      runtimeContext)
    (contextArityZero : M4.ContextSchemeArityZero context) :
    DerivationRequestProducer derivation runtimeContext :=
  ⟨requestProducer derivation runtimeContext contextCompatible stable
    contextArityZero⟩

end ArityZeroAlias

end TypePM.Source.M5Paper1RuntimeProducer
