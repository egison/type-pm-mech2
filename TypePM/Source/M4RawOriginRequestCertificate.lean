import TypePM.Source.M4OriginDemandSafety

/-!
# Raw M4 certificates with structural observation demands

`FuelDemand` assigns one natural-number index to each source-environment
position.  That is insufficient for higher-order source terms: a captured
value may have to support a future call whose argument and result have
different observations.  This module replaces each numeric entry by an
`OriginDemand` tree.

The certificate fixes evaluator fuel and its output demand before a semantic
solution is supplied.  Its input demand therefore cannot inspect solved
types, runtime values, or a completed evaluator result.  The source rules in
this file are conditional composition rules, not a claim that every raw M4
term satisfies every possible demand.

The application rule deliberately exposes its checking-conversion boundary.
`appOfCheckStable` covers only demands whose safety crosses every current
conversion.  Positive `fuel` leaves are not in that class: a dynamic user
matcher can be fuel-safe at matcher type without being fuel-safe at slot type.
-/

namespace TypePM.Runtime

/-- One finite structural observation demand per newest-first environment
position. -/
abbrev OriginEnvironmentDemand := Nat → OriginDemand

namespace OriginEnvironmentDemand

def none : OriginEnvironmentDemand := fun _ => .none

def both (left right : OriginEnvironmentDemand) : OriginEnvironmentDemand :=
  fun position => .both (left position) (right position)

/-- Embed the old per-position numeric demands as `fuel` leaves. -/
def fuel (demand : FuelDemand) : OriginEnvironmentDemand :=
  fun position => .fuel (demand position)

/-- Drop the newest source-environment entry. -/
def tail (demand : OriginEnvironmentDemand) : OriginEnvironmentDemand :=
  fun position => demand (position + 1)

def single (selected : Nat) (demand : OriginDemand) :
    OriginEnvironmentDemand :=
  fun position => if position = selected then demand else .none

end OriginEnvironmentDemand

/-- A runtime value satisfies one structural demand at every occurrence type
obtained by instantiating the aligned source scheme under one fixed solution. -/
def SchemeOriginValueSafe (demand : OriginDemand) (value : Value)
    (scheme : Source.Scheme) (solution : Subst) : Prop :=
  ∀ supply,
    OriginValueSafe demand value
      ((scheme.instantiate supply).1.apply solution)

/-- Per-position structural safety for a runtime environment aligned with an
exact source context. -/
def SchemeOriginEnvironmentSafe (demand : OriginEnvironmentDemand)
    (solution : Subst) (values : List Value) (context : Source.Context) : Prop :=
  values.length = context.length ∧
    ∀ (position : Nat) (scheme : Source.Scheme) (value : Value),
      context[position]? = some scheme →
      values[position]? = some value →
      SchemeOriginValueSafe (demand position) value scheme solution

namespace SchemeOriginValueSafe

theorem ofMono
    (safe : OriginValueSafe demand value (target.apply solution)) :
    SchemeOriginValueSafe demand value (Source.Scheme.mono target) solution := by
  intro supply
  simpa using safe

theorem mono
    (safe : SchemeOriginValueSafe available value scheme solution)
    (weaken : OriginDemand.Le requested available) :
    SchemeOriginValueSafe requested value scheme solution :=
  fun supply => (safe supply).mono weaken

end SchemeOriginValueSafe

namespace SchemeOriginEnvironmentSafe

theorem mono
    (safe : SchemeOriginEnvironmentSafe available solution values context)
    (weaken : ∀ position, OriginDemand.Le (requested position)
      (available position)) :
    SchemeOriginEnvironmentSafe requested solution values context := by
  refine ⟨safe.1, ?_⟩
  intro position scheme value schemeFound valueFound
  exact (safe.2 position scheme value schemeFound valueFound).mono
    (weaken position)

/-- Demands outside the finite source context are observationally irrelevant. -/
theorem congr
    (safe : SchemeOriginEnvironmentSafe first solution values context)
    (agree : ∀ position, position < context.length →
      first position = second position) :
    SchemeOriginEnvironmentSafe second solution values context := by
  refine ⟨safe.1, ?_⟩
  intro position scheme value schemeFound valueFound
  have inBounds : position < context.length :=
    (List.getElem?_eq_some_iff.mp schemeFound).1
  rw [← agree position inBounds]
  exact safe.2 position scheme value schemeFound valueFound

theorem lookup
    (safe : SchemeOriginEnvironmentSafe demand solution values context)
    (schemeFound : context[position]? = some scheme) :
    ∃ value,
      values[position]? = some value ∧
        SchemeOriginValueSafe (demand position) value scheme solution := by
  have positionLt : position < context.length :=
    (List.getElem?_eq_some_iff.mp schemeFound).1
  have valueLt : position < values.length := by
    simpa [safe.1] using positionLt
  let value := values[position]'valueLt
  have valueFound : values[position]? = some value :=
    List.getElem?_eq_getElem valueLt
  exact ⟨value, valueFound,
    safe.2 position scheme value schemeFound valueFound⟩

theorem nil (demand : OriginEnvironmentDemand) (solution : Subst) :
    SchemeOriginEnvironmentSafe demand solution [] [] := by
  constructor
  · rfl
  · intro position scheme value schemeFound
    simp at schemeFound

theorem cons
    (head : SchemeOriginValueSafe headDemand value scheme solution)
    (tail : SchemeOriginEnvironmentSafe tailDemand solution values context) :
    SchemeOriginEnvironmentSafe
      (fun position => match position with
        | 0 => headDemand
        | position + 1 => tailDemand position)
      solution (value :: values) (scheme :: context) := by
  constructor
  · simp [tail.1]
  · intro position foundScheme foundValue schemeFound valueFound
    cases position with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at schemeFound valueFound
        subst foundScheme
        subst foundValue
        exact head
    | succ position =>
        simp only [List.getElem?_cons_succ] at schemeFound valueFound
        exact tail.2 position foundScheme foundValue schemeFound valueFound

/-- Erase a structural environment whose entries are all `fuel` leaves back
to the preceding numeric-demand relation. -/
theorem toFuel
    (safe : SchemeOriginEnvironmentSafe
      (OriginEnvironmentDemand.fuel demand) solution values context) :
    SchemeDemandEnvironmentSafe demand solution values context := by
  refine ⟨safe.1, ?_⟩
  intro position scheme value schemeFound valueFound supply
  have originSafe := safe.2 position scheme value schemeFound valueFound supply
  simpa [OriginEnvironmentDemand.fuel, OriginValueSafe] using originSafe

end SchemeOriginEnvironmentSafe

namespace OriginResultSafe

/-- Combine two observations of the same deterministic evaluator result. -/
theorem bothIntro
    (leftSafe : OriginResultSafe left target result)
    (rightSafe : OriginResultSafe right target result) :
    OriginResultSafe (.both left right) target result := by
  cases resultEq : result with
  | timeout => exact .inl rfl
  | stuck =>
      have contradiction := leftSafe.notStuck
      rw [resultEq] at contradiction
      contradiction
  | ok value =>
      rcases leftSafe with leftTimeout | ⟨leftValue, leftOk, leftValueSafe⟩
      · rw [resultEq] at leftTimeout
        contradiction
      · rcases rightSafe with rightTimeout |
            ⟨rightValue, rightOk, rightValueSafe⟩
        · rw [resultEq] at rightTimeout
          contradiction
        · rw [resultEq] at leftOk rightOk
          cases leftOk
          cases rightOk
          exact .inr ⟨value, rfl,
            OriginValueSafe.both leftValueSafe rightValueSafe⟩

end OriginResultSafe

/-- Demands whose value safety can cross every currently normalized checking
conversion.  Positive ordinary-fuel leaves are intentionally excluded. -/
inductive OriginDemand.CheckStable : OriginDemand → Prop where
  | none : CheckStable .none
  | zero : CheckStable (.fuel 0)
  | both (left : CheckStable leftDemand) (right : CheckStable rightDemand) :
      CheckStable (.both leftDemand rightDemand)
  | plainCall : CheckStable (.plainCall operationalFuel argument result)

/-- `CheckStable` is exactly the sufficient boundary used by raw application.
A call demand forces the source value's outer type to be a function, so every
special matcher conversion is impossible at that outer node. -/
theorem OriginValueSafe.ofCheckConversion
    (stable : OriginDemand.CheckStable demand)
    (conversion : CheckConversion conversionClass source expected)
    (safe : OriginValueSafe demand value source) :
    OriginValueSafe demand value expected := by
  induction stable with
  | none => simp only [OriginValueSafe]
  | zero => simp [OriginValueSafe, FuelValueSafe]
  | both left right leftIH rightIH =>
      exact OriginValueSafe.both
        (leftIH safe.bothLeft)
        (rightIH safe.bothRight)
  | plainCall =>
      simp only [OriginValueSafe] at safe ⊢
      cases safe with
      | zero =>
          cases conversion
          exact .zero
      | closure bodySafe =>
          cases conversion
          exact .closure bodySafe

theorem OriginResultSafe.ofCheckConversion
    (stable : OriginDemand.CheckStable demand)
    (conversion : CheckConversion conversionClass source expected)
    (safe : OriginResultSafe demand source result) :
    OriginResultSafe demand expected result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success,
      valueSafe.ofCheckConversion stable conversion⟩

end TypePM.Runtime

namespace TypePM.Source.M4

open TypePM.Runtime

/-- A proof-producing certificate for one exact raw M4 derivation, one fixed
evaluator fuel, and one finite output observation.  `inputDemand` is selected
before the later semantic solution. -/
structure RawOriginRequestCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next)
    (operationalFuel : Nat) (outputDemand : OriginDemand) : Type where
  inputDemand : OriginEnvironmentDemand
  preserves : ∀ solution,
    generated.SemanticSolution solution →
      ∀ environment,
        SchemeOriginEnvironmentSafe inputDemand solution environment context →
          OriginResultSafe outputDemand (generated.target.apply solution)
            (evalFuel operationalFuel environment expression)

namespace RawOriginRequestCertificate

/-- A variable can satisfy any requested observation when the aligned source
environment stores that observation at its selected position. -/
def var
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next)
    (operationalFuel : Nat) (outputDemand : OriginDemand) :
    RawOriginRequestCertificate elaboration operationalFuel outputDemand := by
  let inputDemand := OriginEnvironmentDemand.single position outputDemand
  refine ⟨inputDemand, ?_⟩
  intro solution _semantic environment environmentSafe
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨scheme, schemeFound, generatedEq, _nextEq⟩ := elaboration
  obtain ⟨value, valueFound, valueSafe⟩ := environmentSafe.lookup schemeFound
  have selected : inputDemand position = outputDemand := by
    simp [inputDemand, OriginEnvironmentDemand.single]
  rw [selected] at valueSafe
  rw [generatedEq]
  simpa [OriginResultSafe, FuelResultSafeWith] using
    (evalFuel_var_resultSafeWith valueFound (valueSafe supply)
      operationalFuel)

@[simp] theorem var_inputDemand_selected
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next)
    (operationalFuel : Nat) (outputDemand : OriginDemand) :
    (var elaboration operationalFuel outputDemand).inputDemand position =
      outputDemand := by
  simp [var, OriginEnvironmentDemand.single]

/-- Embed an existing numeric raw certificate at one `fuel` output leaf. -/
def ofFuel
    {elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next}
    (certificate : RawFuelCertificate elaboration)
    (operationalFuel resultIndex : Nat) :
    RawOriginRequestCertificate elaboration operationalFuel
      (.fuel resultIndex) := by
  let inputDemand := OriginEnvironmentDemand.fuel
    (certificate.inputDemand operationalFuel resultIndex)
  refine ⟨inputDemand, ?_⟩
  intro solution semantic environment environmentSafe
  apply OriginResultSafe.ofFuel
  exact certificate.preserves solution semantic operationalFuel resultIndex
    environment environmentSafe.toFuel

/-- Conjoin two finite observations of the same raw evaluation. -/
def both
    {elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next}
    (left : RawOriginRequestCertificate elaboration operationalFuel leftDemand)
    (right : RawOriginRequestCertificate elaboration operationalFuel rightDemand) :
    RawOriginRequestCertificate elaboration operationalFuel
      (.both leftDemand rightDemand) := by
  let inputDemand := OriginEnvironmentDemand.both
    left.inputDemand right.inputDemand
  refine ⟨inputDemand, ?_⟩
  intro solution semantic environment environmentSafe
  apply OriginResultSafe.bothIntro
  · apply left.preserves solution semantic environment
    apply environmentSafe.mono
    intro position
    exact .fromLeft (.refl _)
  · apply right.preserves solution semantic environment
    apply environmentSafe.mono
    intro position
    exact .fromRight (.refl _)

/-- Request a weaker output observation without changing the input demand. -/
def weakenOutput
    (certificate : RawOriginRequestCertificate elaboration operationalFuel
      availableDemand)
    (weaken : OriginDemand.Le requestedDemand availableDemand) :
    RawOriginRequestCertificate elaboration operationalFuel requestedDemand :=
  ⟨certificate.inputDemand, by
    intro solution semantic environment environmentSafe
    exact (certificate.preserves solution semantic environment
      environmentSafe).mono weaken⟩

/-- Supply a stronger input environment than the certificate minimally asks
for. -/
def strengthenInput
    (certificate : RawOriginRequestCertificate elaboration operationalFuel
      outputDemand)
    (stronger : OriginEnvironmentDemand)
    (covers : ∀ position,
      OriginDemand.Le (certificate.inputDemand position) (stronger position)) :
    RawOriginRequestCertificate elaboration operationalFuel outputDemand :=
  ⟨stronger, by
    intro solution semantic environment environmentSafe
    exact certificate.preserves solution semantic environment
      (environmentSafe.mono covers)⟩

/-- One smaller body certificate together with the contravariant fact that
the public lambda argument demand covers its exact position-zero demand. -/
structure LambdaBodyRequest
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {body : Expr} {bodySupply next : Supply}
    {generatedBody : Generated}
    (bodyElaboration : ElaboratesFuel signature staticFuel context body
      bodySupply generatedBody next)
    (bodyOperationalFuel : Nat)
    (argumentDemand resultDemand : OriginDemand) : Type where
  certificate : RawOriginRequestCertificate bodyElaboration
    bodyOperationalFuel resultDemand
  argumentCoversBody : OriginDemand.Le (certificate.inputDemand 0)
    argumentDemand

/-- General raw source-lambda rule for one positive future plain call.
The body head determines the required argument observation and the shifted
tail is exactly the captured-environment demand. -/
theorem lamPlainCall
    {bodyOperationalFuel lambdaOperationalFuel : Nat}
    {argumentDemand resultDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lam body) supply generated next)
    (bodyRequest : ∀ generatedBody,
      ∀ bodyElaboration : ElaboratesFuel signature staticFuel
        (Scheme.mono (.var ⟨supply.ty⟩) :: context) body
        (supply.nextTy 1) generatedBody next,
      Nonempty (LambdaBodyRequest bodyElaboration bodyOperationalFuel
        argumentDemand resultDemand)) :
    Nonempty (RawOriginRequestCertificate elaboration lambdaOperationalFuel
      (.plainCall (bodyOperationalFuel + 1)
        argumentDemand resultDemand)) := by
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedBody, bodyElaboration, generatedEq⟩ := elaboration
  subst generated
  obtain ⟨request⟩ := bodyRequest generatedBody bodyElaboration
  let certificate := request.certificate
  let inputDemand : OriginEnvironmentDemand :=
    OriginEnvironmentDemand.tail certificate.inputDemand
  refine ⟨⟨inputDemand, ?_⟩⟩
  intro solution semantic environment environmentSafe
  cases lambdaOperationalFuel with
  | zero => exact .inl rfl
  | succ lambdaFuel =>
      refine .inr ⟨.plainClosure environment body, rfl, ?_⟩
      apply OriginValueSafe.plainClosure
      intro argument argumentSafe
      apply certificate.preserves solution semantic (argument :: environment)
      have headSafe : SchemeOriginValueSafe
          (certificate.inputDemand 0) argument
          (Scheme.mono (.var ⟨supply.ty⟩)) solution :=
        SchemeOriginValueSafe.ofMono
          (argumentSafe.mono request.argumentCoversBody)
      have pushed := SchemeOriginEnvironmentSafe.cons headSafe environmentSafe
      apply pushed.congr
      intro position _positionLt
      cases position <;> rfl

/-- A zero-fuel call observes no closure body and needs no captured input. -/
theorem lamZeroCall
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lam body) supply generated next)
    (lambdaOperationalFuel : Nat)
    (argumentDemand resultDemand : OriginDemand) :
    Nonempty (RawOriginRequestCertificate elaboration lambdaOperationalFuel
      (.plainCall 0 argumentDemand resultDemand)) := by
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedBody, bodyElaboration, generatedEq⟩ := elaboration
  subst generated
  let inputDemand := OriginEnvironmentDemand.none
  refine ⟨⟨inputDemand, ?_⟩⟩
  intro solution _semantic environment _environmentSafe
  cases lambdaOperationalFuel with
  | zero => exact .inl rfl
  | succ lambdaFuel =>
      refine .inr ⟨.plainClosure environment body, rfl, ?_⟩
      simp only [OriginValueSafe]
      exact .zero

/-- General application composition.  The transport callback receives the
exact child blocks, the parent `Generated.fromApp` semantic solution, and the
actual pending `CheckConversion` extracted from that same parent block. -/
theorem appWithArgumentTransport
    {childFuel : Nat} {argumentDemand resultDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.app function argument) supply generated next)
    (functionCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ _argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (RawOriginRequestCertificate functionElaboration childFuel
        (.plainCall childFuel argumentDemand resultDemand)))
    (argumentCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ _functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (RawOriginRequestCertificate argumentElaboration childFuel
        argumentDemand))
    (argumentTransport : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ _functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ _argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      ∀ solution,
        (Generated.fromApp generatedFunction generatedArgument
          (.var ⟨afterArgument.ty⟩)
          (.var ⟨afterArgument.ty + 1⟩)).SemanticSolution solution →
      ∀ conversionClass value,
        CheckConversion conversionClass
          (generatedArgument.target.apply solution)
          ((Ty.var ⟨afterArgument.ty⟩).apply solution) →
        OriginValueSafe argumentDemand value
          (generatedArgument.target.apply solution) →
        OriginValueSafe argumentDemand value
          ((Ty.var ⟨afterArgument.ty⟩).apply solution)) :
    Nonempty (RawOriginRequestCertificate elaboration (childFuel + 1)
      resultDemand) := by
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
    functionElaboration, argumentElaboration, generatedEq, nextEq⟩ := elaboration
  subst generated
  subst next
  obtain ⟨functionCertificate⟩ := functionCertificate generatedFunction
    afterFunction generatedArgument afterArgument functionElaboration
    argumentElaboration
  obtain ⟨argumentCertificate⟩ := argumentCertificate generatedFunction
    afterFunction generatedArgument afterArgument functionElaboration
    argumentElaboration
  let inputDemand := OriginEnvironmentDemand.both
    functionCertificate.inputDemand argumentCertificate.inputDemand
  refine ⟨⟨inputDemand, ?_⟩⟩
  intro solution semantic environment environmentSafe
  have functionSemantic : generatedFunction.SemanticSolution solution := by
    constructor
    · intro equation membership
      exact semantic.1 equation (by
        simp only [Generated.fromApp, List.mem_append]
        exact .inl (.inl membership))
    · intro obligation membership
      exact semantic.2 obligation (by
        simp only [Generated.fromApp, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false]
        exact .inl (.inl membership))
  have argumentSemantic : generatedArgument.SemanticSolution solution := by
    constructor
    · intro equation membership
      exact semantic.1 equation (by
        simp only [Generated.fromApp, List.mem_append]
        exact .inl (.inr membership))
    · intro obligation membership
      exact semantic.2 obligation (by
        simp only [Generated.fromApp, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false]
        exact .inl (.inr membership))
  have functionType : generatedFunction.target.apply solution =
      .fn ((Ty.var ⟨afterArgument.ty⟩).apply solution)
        ((Ty.var ⟨afterArgument.ty + 1⟩).apply solution) := by
    exact semantic.1
      (.ty generatedFunction.target
        (.fn (.var ⟨afterArgument.ty⟩)
          (.var ⟨afterArgument.ty + 1⟩)))
      (by simp [Generated.fromApp])
  obtain ⟨conversionClass, argumentConversion⟩ :=
    semantic.2
      ⟨generatedArgument.target, Ty.var ⟨afterArgument.ty⟩⟩
      (by simp [Generated.fromApp])
  have functionSafe := functionCertificate.preserves solution functionSemantic
    environment (environmentSafe.mono (fun position => .fromLeft (.refl _)))
  rw [functionType] at functionSafe
  have argumentSafeAtSource := argumentCertificate.preserves solution
    argumentSemantic environment
    (environmentSafe.mono (fun position => .fromRight (.refl _)))
  have argumentSafe : OriginResultSafe argumentDemand
      ((Ty.var ⟨afterArgument.ty⟩).apply solution)
      (evalFuel childFuel environment argument) := by
    rcases argumentSafeAtSource with timeout |
        ⟨argumentValue, success, valueSafe⟩
    · exact .inl timeout
    · exact .inr ⟨argumentValue, success,
        argumentTransport generatedFunction afterFunction generatedArgument
          afterArgument functionElaboration argumentElaboration solution
          semantic conversionClass argumentValue argumentConversion valueSafe⟩
  exact evalFuel_app_origin functionSafe argumentSafe

/-- Application for the exact demand class known to cross every current
checking conversion. -/
theorem appOfCheckStable
    {childFuel : Nat} {argumentDemand resultDemand : OriginDemand}
    (argumentStable : argumentDemand.CheckStable)
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.app function argument) supply generated next)
    (functionCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ _argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (RawOriginRequestCertificate functionElaboration childFuel
        (.plainCall childFuel argumentDemand resultDemand)))
    (argumentCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ _functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (RawOriginRequestCertificate argumentElaboration childFuel
        argumentDemand)) :
    Nonempty (RawOriginRequestCertificate elaboration (childFuel + 1)
      resultDemand) := by
  apply appWithArgumentTransport elaboration functionCertificate
    argumentCertificate
  intro generatedFunction afterFunction generatedArgument afterArgument
    functionElaboration argumentElaboration solution semantic conversionClass
    value conversion valueSafe
  exact valueSafe.ofCheckConversion argumentStable conversion

/-- Equality-specialized application.  The equality callback is indexed by
the exact parent application block and its semantic solution; an unrelated
type equality is not accepted. -/
theorem appOfArgumentEquality
    {childFuel : Nat} {argumentDemand resultDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.app function argument) supply generated next)
    (functionCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ _argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (RawOriginRequestCertificate functionElaboration childFuel
        (.plainCall childFuel argumentDemand resultDemand)))
    (argumentCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ _functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (RawOriginRequestCertificate argumentElaboration childFuel
        argumentDemand))
    (argumentEquality : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ _functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ _argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      ∀ solution,
        (Generated.fromApp generatedFunction generatedArgument
          (.var ⟨afterArgument.ty⟩)
          (.var ⟨afterArgument.ty + 1⟩)).SemanticSolution solution →
        generatedArgument.target.apply solution =
          (Ty.var ⟨afterArgument.ty⟩).apply solution) :
    Nonempty (RawOriginRequestCertificate elaboration (childFuel + 1)
      resultDemand) := by
  apply appWithArgumentTransport elaboration functionCertificate
    argumentCertificate
  intro generatedFunction afterFunction generatedArgument afterArgument
    functionElaboration argumentElaboration solution semantic conversionClass
    value conversion valueSafe
  rw [← argumentEquality generatedFunction afterFunction generatedArgument
    afterArgument functionElaboration argumentElaboration solution semantic]
  exact valueSafe

end RawOriginRequestCertificate

/-- Every expression in the preceding numeric raw fragment embeds at a
`fuel` output leaf. -/
theorem RawFiniteDemandSupported.originFuelCertificate
    (supported : RawFiniteDemandSupported expression)
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next)
    (operationalFuel resultIndex : Nat) :
    Nonempty (RawOriginRequestCertificate elaboration operationalFuel
      (.fuel resultIndex)) := by
  obtain ⟨certificate⟩ := supported.certificate elaboration
  exact ⟨RawOriginRequestCertificate.ofFuel certificate operationalFuel
    resultIndex⟩

end TypePM.Source.M4
