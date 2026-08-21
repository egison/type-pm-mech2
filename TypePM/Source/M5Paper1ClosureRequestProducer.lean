import TypePM.Source.M5Paper1RuntimeProducer
import TypePM.Source.M4OriginMatcherProducer
import TypePM.Source.M4OriginPlainFixProducer
import TypePM.Source.M4RawOriginRecursiveProducer

/-!
# Total principal request producers for Paper-1 closure forms

All producers in this module are closed-root and indexed by the exact M4
principal derivation.  Type applicability eliminates ill-shaped observations.
The remaining dynamic body obligations are explicit call-certificate families.
-/

namespace TypePM.Source.M5Paper1ClosureRequestProducer

open TypePM.Runtime
open M5CompletionArchitecture
open M5PrincipalOriginCertificate

/-- A total exact-certificate builder for every raw elaboration of one closed
source expression. -/
structure ClosedExactCertificateFamily
    (signature : FrozenSignature) (expression : Expr) where
  inputDemand : Nat → OriginDemand → OriginEnvironmentDemand
  certificate : ∀ operationalFuel outputDemand
      {staticFuel supply generated next},
    (elaboration : M4.ElaboratesFuel signature staticFuel [] expression
      supply generated next) →
      Nonempty (M4.ExactRawOriginRequestCertificate elaboration
        operationalFuel outputDemand
        (inputDemand operationalFuel outputDemand))

namespace ClosedExactCertificateFamily

def requestProducer
    (family : ClosedExactCertificateFamily signature expression)
    (derivation : M4.PrincipalTypingDerivation signature [] expression
      principal) :
    PrincipalOriginRequestProducer derivation [] where
  inputDemand := family.inputDemand
  request := by
    intro operationalFuel outputDemand target instantiation applicable
    refine ⟨.elaboration (family.certificate operationalFuel outputDemand) ?_⟩
    intro later targetEq environment environmentSafe
    have environmentEq : environment = [] := by
      simpa using environmentSafe.1
    subst environment
    exact SchemeOriginEnvironmentSafe.nil _ _

theorem derivationRequestProducer
    (family : ClosedExactCertificateFamily signature expression)
    (derivation : M4.PrincipalTypingDerivation signature [] expression
      principal) :
    DerivationRequestProducer derivation [] :=
  ⟨family.requestProducer derivation⟩

end ClosedExactCertificateFamily

/-- Demand-directed application composition at the common predecessor fuel. -/
def applicationExactCertificateFamily
    (functionFamily : ClosedExactCertificateFamily signature function)
    (argumentFamily : ClosedExactCertificateFamily signature argument)
    (argumentDemand : Nat → OriginDemand → OriginDemand) :
    ClosedExactCertificateFamily signature (.app function argument) where
  inputDemand := fun operationalFuel outputDemand =>
    match operationalFuel with
    | 0 => OriginEnvironmentDemand.none
    | childFuel + 1 =>
        OriginEnvironmentDemand.both
          (functionFamily.inputDemand childFuel
            (.plainCall childFuel (argumentDemand childFuel outputDemand)
              outputDemand))
          (argumentFamily.inputDemand childFuel
            (argumentDemand childFuel outputDemand))
  certificate := by
    intro operationalFuel outputDemand staticFuel supply generated next
      elaboration
    cases operationalFuel with
    | zero => exact ⟨M4.ExactRawOriginRequestCertificate.timeout elaboration _⟩
    | succ childFuel =>
        cases staticFuel with
        | zero => exact False.elim elaboration
        | succ childStaticFuel =>
            apply M4.ExactRawOriginRequestCertificate.app elaboration
              (functionFamily.inputDemand childFuel
                (.plainCall childFuel (argumentDemand childFuel outputDemand)
                  outputDemand))
              (argumentFamily.inputDemand childFuel
                (argumentDemand childFuel outputDemand))
            · intro generatedFunction afterFunction generatedArgument
                afterArgument functionElaboration argumentElaboration
              exact functionFamily.certificate childFuel
                (.plainCall childFuel (argumentDemand childFuel outputDemand)
                  outputDemand) functionElaboration
            · intro generatedFunction afterFunction generatedArgument
                afterArgument functionElaboration argumentElaboration
              exact argumentFamily.certificate childFuel
                (argumentDemand childFuel outputDemand) argumentElaboration

theorem application_derivationRequestProducer_total
    (functionFamily : ClosedExactCertificateFamily signature function)
    (argumentFamily : ClosedExactCertificateFamily signature argument)
    (argumentDemand : Nat → OriginDemand → OriginDemand)
    (derivation : M4.PrincipalTypingDerivation signature []
      (.app function argument) principal) :
    DerivationRequestProducer derivation [] :=
  (applicationExactCertificateFamily functionFamily argumentFamily
    argumentDemand).derivationRequestProducer derivation

/-! ## Matcher literal -/

theorem fuelLeafDemand_of_applicable_matcher :
    ∀ demand,
      OriginDemandApplicable demand (.matcher capability item) →
        FuelLeafDemand demand
  | .none, _ => .none
  | .fuel index, _ => .fuel index
  | .both left right, applicable =>
      have applicable' : OriginDemandApplicable left
            (.matcher capability item) ∧
          OriginDemandApplicable right (.matcher capability item) := by
        simpa only [OriginDemandApplicable] using applicable
      .both
        (fuelLeafDemand_of_applicable_matcher left applicable'.1)
        (fuelLeafDemand_of_applicable_matcher right applicable'.2)
  | .listOf element, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨elementType, impossible, _⟩
      cases impossible
  | .pairOf left right, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨leftType, rightType, impossible, _left, _right⟩
      cases impossible
  | .bool, applicable => by
      simp only [OriginDemandApplicable] at applicable
      cases applicable
  | .int, applicable => by
      simp only [OriginDemandApplicable] at applicable
      cases applicable
  | .plainCall callFuel argument result, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨domain, codomain, impossible, _⟩
      cases impossible
termination_by demand => demand

theorem matcherLiteralFuelLeafExactCertificate
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (shape : FuelLeafDemand outputDemand)
    (elaboration : M4.ElaboratesFuel signature staticFuel []
      (.matcher clauses) supply generated next) :
    Nonempty (M4.ExactRawOriginRequestCertificate elaboration operationalFuel
      outputDemand OriginEnvironmentDemand.none) := by
  let certificate : M4.RawOriginRequestCertificate elaboration operationalFuel
      outputDemand :=
    ⟨OriginEnvironmentDemand.none, by
      intro _baseCompatible solution semantic environment environmentSafe
      have environmentEq : environment = [] := by simpa using environmentSafe.1
      subst environment
      cases staticFuel with
      | zero => exact False.elim elaboration
      | succ childFuel =>
          have matcherElaboration : MatcherTyping.MatcherLiteralElaboratesUsing
              (M4.ElaboratesFuel signature childFuel)
              MatcherTyping.PPatElaborates MatcherTyping.DPatElaborates
              signature [] clauses supply generated next := by
            simpa only [M4.ElaboratesFuel] using elaboration
          exact matcherElaboration.eval_originResultSafe_of_m4Fuel compatible
            semantic .nil
            (fuelLeafEnvironmentSafe_of_originEnvironmentSafe shape
              (OriginEnvironmentSafe.nil (fun _ => outputDemand)))⟩
  exact ⟨⟨certificate, rfl⟩⟩

/-- Public instances of the principal matcher literal retain matcher shape. -/
abbrev MatcherInstances
    (_derivation : M4.PrincipalTypingDerivation signature [] (.matcher clauses)
      principal) : Prop :=
  ∀ target, IsInstance principal target →
    ∃ capability item, target = .matcher capability item

private theorem matcherLiteral_generatedTarget_eq
    (elaboration : MatcherTyping.MatcherLiteralElaboratesUsing
      expressionRelation MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context clauses supply generated
      next) :
    generated.target = .matcher (Cap.var ⟨supply.cap⟩)
      (Ty.var ⟨supply.ty⟩) := by
  cases elaboration
  rfl

theorem matcherInstances_of_derivation
    (derivation : M4.PrincipalTypingDerivation signature [] (.matcher clauses)
      principal) :
    MatcherInstances derivation := by
  intro target instantiation
  obtain ⟨later, targetEq⟩ := instantiation
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ childFuel =>
      have matcherElaboration : MatcherTyping.MatcherLiteralElaboratesUsing
          (M4.ElaboratesFuel signature childFuel)
          MatcherTyping.PPatElaborates MatcherTyping.DPatElaborates
          signature [] clauses (Context.initialSupply []) derivation.generated
          derivation.next := by
        simpa only [M4.ElaboratesFuel] using elaboration
      have generatedTargetEq :=
        matcherLiteral_generatedTarget_eq matcherElaboration
      refine ⟨(Cap.var ⟨(Context.initialSupply []).cap⟩).apply
          (Subst.compose later derivation.closure.substitution).cap,
        (Ty.var ⟨(Context.initialSupply []).ty⟩).apply
          (Subst.compose later derivation.closure.substitution), ?_⟩
      calc
        target = principal.apply later := targetEq.symm
        _ = derivation.closure.target.apply later :=
          congrArg (fun candidate => candidate.apply later)
            derivation.target_eq
        _ = derivation.generated.target.apply
              (Subst.compose later derivation.closure.substitution) := by
          simp [PrincipalBlockClosure.target, Ty.apply_compose]
        _ = _ := by
          rw [generatedTargetEq]
          rfl

def matcherLiteralRequestProducer
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (derivation : M4.PrincipalTypingDerivation signature [] (.matcher clauses)
      principal)
    (instances : MatcherInstances derivation) :
    PrincipalOriginRequestProducer derivation [] where
  inputDemand := fun _ _ => OriginEnvironmentDemand.none
  request := by
    intro operationalFuel outputDemand target instantiation applicable
    obtain ⟨capability, item, targetEq⟩ := instances target instantiation
    subst target
    have shape := fuelLeafDemand_of_applicable_matcher outputDemand applicable
    refine ⟨.elaboration
      (fun elaboration =>
        matcherLiteralFuelLeafExactCertificate compatible shape elaboration)
      ?_⟩
    intro later laterEq environment environmentSafe
    have environmentEq : environment = [] := by simpa using environmentSafe.1
    subst environment
    exact SchemeOriginEnvironmentSafe.nil _ _

theorem matcherLiteral_derivationRequestProducer_total
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (derivation : M4.PrincipalTypingDerivation signature [] (.matcher clauses)
      principal) :
    DerivationRequestProducer derivation [] :=
  ⟨matcherLiteralRequestProducer compatible derivation
    (matcherInstances_of_derivation derivation)⟩

/-! ## Function-shaped closure producers -/

/-- Public instances retain the outer function constructor. -/
abbrev FunctionInstances
    (_derivation : M4.PrincipalTypingDerivation signature [] expression
      principal) : Prop :=
  ∀ target, IsInstance principal target →
    ∃ domain codomain, target = .fn domain codomain

/-- Every public instance has one fixed outer function type.  Ground Paper-1
closures satisfy this boundary; polymorphic closures instead require a
codomain-indexed certificate family. -/
abbrev FixedFunctionInstances
    (_derivation : M4.PrincipalTypingDerivation signature [] expression
      principal) (domain codomain : Ty) : Prop :=
  ∀ target, IsInstance principal target → target = .fn domain codomain

theorem functionInstances_of_generatedTarget
    (derivation : M4.PrincipalTypingDerivation signature [] expression
      principal)
    (shape : ∃ domain codomain,
      derivation.generated.target = .fn domain codomain) :
    FunctionInstances derivation := by
  obtain ⟨sourceDomain, sourceCodomain, generatedTargetEq⟩ := shape
  intro target instantiation
  obtain ⟨later, targetEq⟩ := instantiation
  refine ⟨sourceDomain.apply
      (Subst.compose later derivation.closure.substitution),
    sourceCodomain.apply
      (Subst.compose later derivation.closure.substitution), ?_⟩
  calc
    target = principal.apply later := targetEq.symm
    _ = derivation.closure.target.apply later :=
      congrArg (fun candidate => candidate.apply later) derivation.target_eq
    _ = derivation.generated.target.apply
          (Subst.compose later derivation.closure.substitution) := by
      simp [PrincipalBlockClosure.target, Ty.apply_compose]
    _ = _ := by rw [generatedTargetEq]; rfl

theorem lambdaFunctionInstances
    (derivation : M4.PrincipalTypingDerivation signature [] (.lam body)
      principal) :
    FunctionInstances derivation := by
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ childFuel =>
      simp only [M4.ElaboratesFuel] at elaboration
      obtain ⟨generatedBody, _bodyElaboration, generatedEq⟩ := elaboration
      apply functionInstances_of_generatedTarget derivation
      refine ⟨Ty.var ⟨(Context.initialSupply []).ty⟩,
        generatedBody.target, ?_⟩
      simpa [Generated.fromLam] using
        congrArg Generated.target generatedEq

private theorem fix_generatedTarget_eq
    (elaboration : FixElaboratesUsing bodyRelation context (.fixE body)
      supply generated next) :
    generated.target = .fn (Fix.domain body supply)
      (Fix.codomain body supply) := by
  cases elaboration
  rfl

theorem fixFunctionInstances
    (derivation : M4.PrincipalTypingDerivation signature [] (.fixE body)
      principal) :
    FunctionInstances derivation := by
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ childFuel =>
      have fixElaboration : FixElaboratesUsing
          (M4.ElaboratesFuel signature childFuel) [] (.fixE body)
          (Context.initialSupply []) derivation.generated derivation.next := by
        simpa only [M4.ElaboratesFuel] using elaboration
      apply functionInstances_of_generatedTarget derivation
      exact ⟨Fix.domain body (Context.initialSupply []),
        Fix.codomain body (Context.initialSupply []),
        fix_generatedTarget_eq fixElaboration⟩

/-- Atomic certificate builders for one closed function expression.  The
environment demand of a positive lambda call may be the tail of its body
certificate, so it is retained explicitly instead of being forced to
`none`.  Conjunction inputs are assembled structurally below. -/
structure ClosedFunctionDemandCertificates
    (signature : FrozenSignature) (expression : Expr)
    (domain codomain : Ty) where
  atomicInput : OriginDemand → OriginEnvironmentDemand
  call : ∀ constructionFuel callFuel argumentDemand resultDemand
      {staticFuel supply generated next},
    OriginDemandApplicable argumentDemand domain →
      OriginDemandApplicable resultDemand codomain →
        (elaboration : M4.ElaboratesFuel signature staticFuel [] expression
          supply generated next) →
          Nonempty (M4.ExactRawOriginRequestCertificate elaboration
            constructionFuel (.plainCall callFuel argumentDemand resultDemand)
            (atomicInput (.plainCall callFuel argumentDemand resultDemand)))
  none : ∀ constructionFuel {staticFuel supply generated next},
    (elaboration : M4.ElaboratesFuel signature staticFuel [] expression
      supply generated next) →
      Nonempty (M4.ExactRawOriginRequestCertificate elaboration
        constructionFuel .none (atomicInput .none))
  zeroFuel : ∀ constructionFuel {staticFuel supply generated next},
    (elaboration : M4.ElaboratesFuel signature staticFuel [] expression
      supply generated next) →
      Nonempty (M4.ExactRawOriginRequestCertificate elaboration
        constructionFuel (.fuel 0) (atomicInput (.fuel 0)))

namespace ClosedFunctionDemandCertificates

/-- The input selected for an applicable function demand.  Only conjunctions
combine inputs; every other case is supplied by its atomic builder. -/
def inputDemand
    (certificates : ClosedFunctionDemandCertificates signature expression
      domain codomain) :
    OriginDemand → OriginEnvironmentDemand
  | .both left right => OriginEnvironmentDemand.both
      (certificates.inputDemand left) (certificates.inputDemand right)
  | demand => certificates.atomicInput demand
termination_by demand => demand

/-- Applicability-directed exact certificate construction.  Conjunctions may
freely mix call observations with fuel leaves. -/
theorem applicableCertificate
    (certificates : ClosedFunctionDemandCertificates signature expression
      domain codomain)
    (elaboration : M4.ElaboratesFuel signature staticFuel [] expression
      supply generated next)
    (operationalFuel : Nat) :
    ∀ demand,
      OriginDemandApplicable demand (.fn domain codomain) →
        Nonempty (M4.ExactRawOriginRequestCertificate elaboration
          operationalFuel demand (certificates.inputDemand demand))
  | .none, _ => by
      simpa only [inputDemand] using
        certificates.none operationalFuel elaboration
  | .fuel index, applicable => by
      simp only [OriginDemandApplicable] at applicable
      cases applicable with
      | zero =>
          simpa only [inputDemand] using
            certificates.zeroFuel operationalFuel elaboration
  | .both left right, applicable => by
      have applicable' : OriginDemandApplicable left (.fn domain codomain) ∧
          OriginDemandApplicable right (.fn domain codomain) := by
        simpa only [OriginDemandApplicable] using applicable
      obtain ⟨leftCertificate⟩ :=
        certificates.applicableCertificate elaboration operationalFuel left
          applicable'.1
      obtain ⟨rightCertificate⟩ :=
        certificates.applicableCertificate elaboration operationalFuel right
          applicable'.2
      simpa only [inputDemand] using
        (show Nonempty (M4.ExactRawOriginRequestCertificate elaboration
            operationalFuel (.both left right)
            (OriginEnvironmentDemand.both (certificates.inputDemand left)
              (certificates.inputDemand right))) from
          ⟨M4.ExactRawOriginRequestCertificate.both leftCertificate
            rightCertificate⟩)
  | .listOf element, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨elementType, impossible, _⟩
      cases impossible
  | .pairOf left right, applicable => by
      simp only [OriginDemandApplicable] at applicable
      rcases applicable with ⟨leftType, rightType, impossible, _left, _right⟩
      cases impossible
  | .bool, applicable => by
      simp only [OriginDemandApplicable] at applicable
      cases applicable
  | .int, applicable => by
      simp only [OriginDemandApplicable] at applicable
      cases applicable
  | .plainCall callFuel argument result, applicable => by
      simp only [OriginDemandApplicable] at applicable
      obtain ⟨actualDomain, actualCodomain, targetEq, argumentApplicable,
        resultApplicable⟩ := applicable
      cases targetEq
      simpa only [inputDemand] using
        certificates.call operationalFuel callFuel argument result
          argumentApplicable resultApplicable elaboration
termination_by demand => demand

def requestProducer
    (certificates : ClosedFunctionDemandCertificates signature expression
      domain codomain)
    (derivation : M4.PrincipalTypingDerivation signature [] expression
      principal)
    (instances : FixedFunctionInstances derivation domain codomain) :
    PrincipalOriginRequestProducer derivation [] where
  inputDemand := fun _ outputDemand => certificates.inputDemand outputDemand
  request := by
    intro operationalFuel outputDemand target instantiation applicable
    have targetEq := instances target instantiation
    subst target
    refine ⟨.elaboration
      (fun elaboration => certificates.applicableCertificate elaboration
        operationalFuel outputDemand applicable) ?_⟩
    intro later laterEq environment environmentSafe
    have environmentEq : environment = [] := by simpa using environmentSafe.1
    subst environment
    exact SchemeOriginEnvironmentSafe.nil _ _

end ClosedFunctionDemandCertificates

/-! ## Lambda -/

/-- Positive lambda calls delegate to exact body certificates in the extended
argument context. -/
structure LambdaCallBodyFamily
    (signature : FrozenSignature) (body : Expr) (domain codomain : Ty) where
  bodyInput : Nat → OriginDemand → OriginDemand → OriginEnvironmentDemand
  certificate : ∀ bodyFuel argumentDemand resultDemand
      {staticFuel : Nat} {supply : Supply} {generatedBody : Generated}
      {next : Supply},
    OriginDemandApplicable argumentDemand domain →
      OriginDemandApplicable resultDemand codomain →
        (bodyElaboration : M4.ElaboratesFuel signature staticFuel
          [Scheme.mono (Ty.var ⟨supply.ty⟩)] body (supply.nextTy 1)
          generatedBody next) →
          Nonempty (M4.ExactRawOriginRequestCertificate bodyElaboration bodyFuel
            resultDemand (bodyInput bodyFuel argumentDemand resultDemand))
  argumentCovers : ∀ bodyFuel argumentDemand resultDemand domain,
    OriginDemandApplicable argumentDemand domain →
    OriginDemand.Le ((bodyInput bodyFuel argumentDemand resultDemand) 0)
      argumentDemand

def lambdaAtomicInput
    (calls : LambdaCallBodyFamily signature body domain codomain) :
    OriginDemand → OriginEnvironmentDemand
  | .plainCall (bodyFuel + 1) argumentDemand resultDemand =>
      OriginEnvironmentDemand.tail
        (calls.bodyInput bodyFuel argumentDemand resultDemand)
  | _ => OriginEnvironmentDemand.none

def lambdaFunctionCertificates
    (calls : LambdaCallBodyFamily signature body domain codomain) :
    ClosedFunctionDemandCertificates signature (.lam body) domain codomain where
  atomicInput := lambdaAtomicInput calls
  call := by
    intro constructionFuel callFuel argumentDemand resultDemand staticFuel
      supply generated next argumentApplicable resultApplicable elaboration
    cases staticFuel with
    | zero => exact False.elim elaboration
    | succ childStaticFuel =>
        cases callFuel with
        | zero =>
            simpa [lambdaAtomicInput] using
              (M4.ExactRawOriginRequestCertificate.lamZeroCall elaboration
                constructionFuel argumentDemand resultDemand)
        | succ bodyFuel =>
            simpa only [lambdaAtomicInput] using
              (M4.ExactRawOriginRequestCertificate.lamPlainCall elaboration
                (calls.bodyInput bodyFuel argumentDemand resultDemand)
                (fun generatedBody bodyElaboration =>
                  calls.certificate bodyFuel argumentDemand resultDemand
                    argumentApplicable resultApplicable
                    bodyElaboration)
                (calls.argumentCovers bodyFuel argumentDemand resultDemand
                  domain argumentApplicable))
  none := by
    intro constructionFuel staticFuel supply generated next elaboration
    cases staticFuel with
    | zero => exact False.elim elaboration
    | succ childStaticFuel =>
        obtain ⟨zeroCall⟩ :=
          M4.ExactRawOriginRequestCertificate.lamZeroCall elaboration
            constructionFuel .none .none
        simpa [lambdaAtomicInput] using
          (show Nonempty (M4.ExactRawOriginRequestCertificate elaboration
              constructionFuel .none OriginEnvironmentDemand.none) from
            ⟨zeroCall.reobserveUniversal .none⟩)
  zeroFuel := by
    intro constructionFuel staticFuel supply generated next elaboration
    cases staticFuel with
    | zero => exact False.elim elaboration
    | succ childStaticFuel =>
        obtain ⟨zeroCall⟩ :=
          M4.ExactRawOriginRequestCertificate.lamZeroCall elaboration
            constructionFuel .none .none
        simpa [lambdaAtomicInput] using
          (show Nonempty (M4.ExactRawOriginRequestCertificate elaboration
              constructionFuel (.fuel 0) OriginEnvironmentDemand.none) from
            ⟨zeroCall.reobserveUniversal .zero⟩)

theorem lambda_derivationRequestProducer_total
    (calls : LambdaCallBodyFamily signature body domain codomain)
    (derivation : M4.PrincipalTypingDerivation signature [] (.lam body)
      principal)
    (instances : FixedFunctionInstances derivation domain codomain) :
    DerivationRequestProducer derivation [] :=
  ⟨(lambdaFunctionCertificates calls).requestProducer derivation
    instances⟩

/-! ## Ordinary and matcher-root `fixE` -/

structure PlainFixCallFamily (signature : FrozenSignature) (body : Expr)
    (observedDomain observedCodomain : Ty) where
  bodyTyped : ∀ {staticFuel supply generated next}
      (_elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
        supply generated next) solution,
    generated.SemanticSolution solution →
      TotalRecursiveClosureBodyTyping
        [((Fix.domain body supply).apply solution),
          .fn ((Fix.domain body supply).apply solution)
            ((Fix.codomain body supply).apply solution)]
        body ((Fix.codomain body supply).apply solution)
  bodySafe : ∀ {staticFuel supply generated next}
      (_elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
        supply generated next) bodyFuel argumentDemand resultDemand,
    OriginDemandApplicable argumentDemand observedDomain →
      OriginDemandApplicable resultDemand observedCodomain →
        ∀ solution,
    generated.SemanticSolution solution →
      MatcherTyping.PlainFixBodyOriginSafe [] body
        ((Fix.domain body supply).apply solution)
        ((Fix.codomain body supply).apply solution)
        bodyFuel argumentDemand resultDemand

theorem plainFixCallExactCertificate
    (calls : PlainFixCallFamily signature body observedDomain observedCodomain)
    (argumentApplicable : OriginDemandApplicable argumentDemand observedDomain)
    (resultApplicable : OriginDemandApplicable resultDemand observedCodomain)
    (elaboration : M4.ElaboratesFuel signature staticFuel [] (.fixE body)
      supply generated next) :
    Nonempty (M4.ExactRawOriginRequestCertificate elaboration constructionFuel
      (.plainCall callFuel argumentDemand resultDemand)
      OriginEnvironmentDemand.none) := by
  let certificate : M4.RawOriginRequestCertificate elaboration constructionFuel
      (.plainCall callFuel argumentDemand resultDemand) :=
    ⟨OriginEnvironmentDemand.none, by
      intro _compatible solution semantic environment environmentSafe
      have environmentEq : environment = [] := by simpa using environmentSafe.1
      subst environment
      cases callFuel with
      | zero =>
          exact MatcherTyping.fixElaboration_eval_originResultSafe_zeroCall_of_m4Fuel
            elaboration semantic (calls.bodyTyped elaboration solution semantic)
            .nil
      | succ bodyFuel =>
          exact MatcherTyping.fixElaboration_eval_originResultSafe_plainCall_of_m4Fuel
            elaboration semantic (calls.bodyTyped elaboration solution semantic)
            .nil (calls.bodySafe elaboration bodyFuel argumentDemand
              resultDemand argumentApplicable resultApplicable solution
              semantic)⟩
  exact ⟨⟨certificate, rfl⟩⟩

def plainFixFunctionCertificates
    (calls : PlainFixCallFamily signature body domain codomain) :
    ClosedFunctionDemandCertificates signature (.fixE body) domain codomain where
  atomicInput := fun _ => OriginEnvironmentDemand.none
  call := by
    intro constructionFuel callFuel argumentDemand resultDemand staticFuel
      supply generated next argumentApplicable resultApplicable elaboration
    exact plainFixCallExactCertificate calls argumentApplicable
      resultApplicable elaboration
  none := by
    intro constructionFuel staticFuel supply generated next elaboration
    obtain ⟨zeroCall⟩ := plainFixCallExactCertificate
      (constructionFuel := constructionFuel) (callFuel := 0)
      (argumentDemand := .none) (resultDemand := .none) calls
      (by simp [OriginDemandApplicable]) (by simp [OriginDemandApplicable])
      elaboration
    exact ⟨zeroCall.reobserveUniversal .none⟩
  zeroFuel := by
    intro constructionFuel staticFuel supply generated next elaboration
    obtain ⟨zeroCall⟩ := plainFixCallExactCertificate
      (constructionFuel := constructionFuel) (callFuel := 0)
      (argumentDemand := .none) (resultDemand := .none) calls
      (by simp [OriginDemandApplicable]) (by simp [OriginDemandApplicable])
      elaboration
    exact ⟨zeroCall.reobserveUniversal .zero⟩

theorem plainFix_derivationRequestProducer_total
    (calls : PlainFixCallFamily signature body domain codomain)
    (derivation : M4.PrincipalTypingDerivation signature [] (.fixE body)
      principal)
    (instances : FixedFunctionInstances derivation domain codomain) :
    DerivationRequestProducer derivation [] :=
  ⟨(plainFixFunctionCertificates calls).requestProducer derivation
    instances⟩

/-- The only remaining matcher-root call obligation is safety of evaluating
the matcher body after inserting the argument and recursive self.  Structural
body typing is derived from the solved matcher elaboration by S8. -/
structure MatcherFixCallFamily
    (signature : FrozenSignature) (clauses : List MatcherClause)
    (observedDomain observedCodomain : Ty) where
  bodySafe : ∀ {staticFuel supply generated next}
      (_elaboration : M4.ElaboratesFuel signature staticFuel []
        (.fixE (.matcher clauses)) supply generated next)
      bodyFuel argumentDemand resultDemand,
    OriginDemandApplicable argumentDemand observedDomain →
      OriginDemandApplicable resultDemand observedCodomain →
        ∀ solution,
    generated.SemanticSolution solution →
      MatcherTyping.PlainFixBodyOriginSafe [] (.matcher clauses)
        ((Fix.domain (.matcher clauses) supply).apply solution)
        ((Fix.codomain (.matcher clauses) supply).apply solution)
        bodyFuel argumentDemand resultDemand

def matcherFixPlainCallFamily
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (calls : MatcherFixCallFamily signature clauses domain codomain) :
    PlainFixCallFamily signature (.matcher clauses) domain codomain where
  bodyTyped := by
    intro staticFuel supply generated next elaboration solution semantic
    exact MatcherTyping.matcherFixElaboration_totalRecursiveClosureBodyTyping_of_m4Fuel
      elaboration compatible semantic .nil
  bodySafe := calls.bodySafe

theorem matcherFixFuelLeafExactCertificate
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (shape : FuelLeafDemand outputDemand)
    (elaboration : M4.ElaboratesFuel signature staticFuel []
      (.fixE (.matcher clauses)) supply generated next) :
    Nonempty (M4.ExactRawOriginRequestCertificate elaboration constructionFuel
      outputDemand OriginEnvironmentDemand.none) := by
  let certificate : M4.RawOriginRequestCertificate elaboration constructionFuel
      outputDemand :=
    ⟨OriginEnvironmentDemand.none, by
      intro _baseCompatible solution semantic environment environmentSafe
      have environmentEq : environment = [] := by simpa using environmentSafe.1
      subst environment
      exact MatcherTyping.matcherFixElaboration_eval_originResultSafe_of_m4Fuel
        elaboration compatible semantic .nil .nil
        (fuelLeafEnvironmentSafe_of_originEnvironmentSafe shape
          (OriginEnvironmentSafe.nil (fun _ => outputDemand)))⟩
  exact ⟨⟨certificate, rfl⟩⟩

def matcherFixFunctionCertificates
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (calls : MatcherFixCallFamily signature clauses domain codomain) :
    ClosedFunctionDemandCertificates signature (.fixE (.matcher clauses))
      domain codomain where
  atomicInput := fun _ => OriginEnvironmentDemand.none
  call := by
    intro constructionFuel callFuel argumentDemand resultDemand staticFuel
      supply generated next argumentApplicable resultApplicable elaboration
    exact plainFixCallExactCertificate
      (matcherFixPlainCallFamily compatible calls) argumentApplicable
      resultApplicable elaboration
  none := by
    intro constructionFuel staticFuel supply generated next elaboration
    exact matcherFixFuelLeafExactCertificate compatible .none elaboration
  zeroFuel := by
    intro constructionFuel staticFuel supply generated next elaboration
    exact matcherFixFuelLeafExactCertificate compatible (.fuel 0) elaboration

theorem matcherFix_derivationRequestProducer_total
    (compatible : FrozenSignatureRuntimeCompatible signature)
    (calls : MatcherFixCallFamily signature clauses domain codomain)
    (derivation : M4.PrincipalTypingDerivation signature []
      (.fixE (.matcher clauses)) principal)
    (instances : FixedFunctionInstances derivation domain codomain) :
    DerivationRequestProducer derivation [] :=
  ⟨(matcherFixFunctionCertificates compatible calls).requestProducer derivation
    instances⟩

end TypePM.Source.M5Paper1ClosureRequestProducer
