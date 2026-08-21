import TypePM.Source.GeneralizedOccurrenceSolution
import TypePM.Source.M4RawOriginRequestCertificate

/-!
# Recursive raw M4 producer for structural origin demands

`RawOriginRequestPlan` is a static request-realizability judgment for the
largest uniform raw-M4 fragment currently justified by structural origin
demands.  It fixes evaluator fuel, the output observation, and the exact
source-environment input observation without storing a semantic solution,
runtime value, or completed evaluation result.

The producer below turns a plan into an exact raw certificate by mutual
induction over expressions and tuple fields.  Plain lambdas retain the
contravariant argument-coverage proof; application transports every demand
through the solved checking conversion.
-/

namespace TypePM.Runtime

/-- Demands satisfied by every value at every type.  They still require the
evaluation itself not to be stuck. -/
inductive OriginDemand.Universal : OriginDemand → Prop where
  | none : OriginDemand.Universal .none
  | zero : OriginDemand.Universal (.fuel 0)
  | both (left : OriginDemand.Universal leftDemand)
      (right : OriginDemand.Universal rightDemand) :
      OriginDemand.Universal (.both leftDemand rightDemand)

theorem OriginDemand.Universal.valueSafe
    (universal : OriginDemand.Universal demand) (value : Value) (target : Ty) :
    OriginValueSafe demand value target := by
  induction universal with
  | none => simp only [OriginValueSafe]
  | zero => simp [OriginValueSafe, FuelValueSafe]
  | both left right leftIH rightIH =>
      exact OriginValueSafe.both leftIH rightIH

theorem OriginResultSafe.reobserveUniversal
    (safe : OriginResultSafe available target result)
    (universal : OriginDemand.Universal requested) :
    OriginResultSafe requested target result := by
  rcases safe with timeout | ⟨value, success, _valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, universal.valueSafe value target⟩

end TypePM.Runtime

namespace TypePM.Source.M4

open TypePM.Runtime

private theorem sourceScheme_mem_of_getElem?_eq_some
    {context : Context} {position : Nat} {scheme : Scheme}
    (lookup : context[position]? = some scheme) :
    scheme ∈ context := by
  induction context generalizing position with
  | nil => simp at lookup
  | cons head tail induction =>
      cases position with
      | zero =>
          simp at lookup
          subst scheme
          simp
      | succ position =>
          simp only [List.getElem?_cons_succ] at lookup
          exact List.mem_cons_of_mem head (induction lookup)

/-- Pointwise universal demands need only source/runtime length alignment. -/
private theorem schemeOriginEnvironmentSafe_ofUniversal
    (lengthEq : values.length = context.length)
    (universal : ∀ position, OriginDemand.Universal (demand position)) :
    SchemeOriginEnvironmentSafe demand solution values context := by
  refine ⟨lengthEq, ?_⟩
  intro position scheme value _schemeFound _valueFound occurrenceSupply
  exact (universal position).valueSafe value
    ((scheme.instantiate occurrenceSupply).1.apply solution)

/-- Closing the source context at an exact `letE` interface preserves every
structural environment observation under the enclosing solution. -/
private theorem schemeOriginEnvironmentSafe_ofApplyFreeInterface
    (safe : SchemeOriginEnvironmentSafe demand solution values context)
    (solved : Solves solution (context.interfaceEquations block)) :
    SchemeOriginEnvironmentSafe demand solution values
      (context.applyFree block) := by
  refine ⟨?_, ?_⟩
  · simpa [Context.applyFree] using safe.1
  · intro position transformedScheme value transformedFound valueFound
    simp only [Context.applyFree, List.getElem?_map] at transformedFound
    cases originalFound : context[position]? with
    | none => simp [originalFound] at transformedFound
    | some scheme =>
        simp only [originalFound, Option.map_some, Option.some.injEq] at transformedFound
        subst transformedScheme
        intro occurrenceSupply
        have valueSafe := safe.2 position scheme value originalFound valueFound
          occurrenceSupply
        rw [SchemeFuelEnvironmentSafe.instantiate_applyFree_apply_eq_of_interface
          (sourceScheme_mem_of_getElem?_eq_some originalFound) block solution
          solved occurrenceSupply]
        exact valueSafe

private theorem semanticSolution_fromLet_parts
    (semantic : (Generated.fromLet effects bodyGenerated).SemanticSolution
      solution) :
    Solves solution effects ∧ bodyGenerated.SemanticSolution solution := by
  constructor
  · intro equation membership
    exact semantic.1 equation (by simp [Generated.fromLet, membership])
  · constructor
    · intro equation membership
      exact semantic.1 equation (by simp [Generated.fromLet, membership])
    · intro obligation membership
      exact semantic.2 obligation (by
        simpa [Generated.fromLet] using membership)

/-- A raw certificate whose synthesized input demand is exactly the demand
advertised by the static request plan. -/
structure ExactRawOriginRequestCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next)
    (operationalFuel : Nat) (outputDemand : OriginDemand)
    (inputDemand : OriginEnvironmentDemand) : Type where
  certificate : RawOriginRequestCertificate elaboration operationalFuel
    outputDemand
  input_eq : certificate.inputDemand = inputDemand

/-- List-valued companion used by tuple evaluation. -/
structure RawOriginItemsFuelCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (elaboration : ItemsElaborateUsing (ElaboratesFuel signature staticFuel)
      context expressions supply generated next)
    (operationalFuel resultIndex : Nat) : Type where
  inputDemand : OriginEnvironmentDemand
  preserves : ∀ solution,
    TypePM.Runtime.GeneratedItems.SemanticSolution generated solution →
      ∀ environment,
        SchemeOriginEnvironmentSafe inputDemand solution environment context →
          FuelEnvironmentResultSafe resultIndex
            (Ty.applyList solution generated.targets)
            (FuelResult.traverse (evalFuel operationalFuel environment)
              expressions)

structure ExactRawOriginItemsFuelCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (elaboration : ItemsElaborateUsing (ElaboratesFuel signature staticFuel)
      context expressions supply generated next)
    (operationalFuel resultIndex : Nat)
    (inputDemand : OriginEnvironmentDemand) : Type where
  certificate : RawOriginItemsFuelCertificate elaboration operationalFuel
    resultIndex
  input_eq : certificate.inputDemand = inputDemand

private theorem semanticSolution_postcompose
    {generated : Generated} {earlier : Subst}
    (semantic : generated.SemanticSolution earlier) (later : Subst) :
    generated.SemanticSolution (Subst.compose later earlier) := by
  constructor
  · exact solves_postcompose semantic.1 later
  · intro obligation membership
    obtain ⟨conversionClass, conversion⟩ :=
      semantic.2 obligation membership
    exact ⟨conversionClass, by
      simpa only [Ty.apply_compose] using
        TypePM.Runtime.CheckConversion.apply conversion later⟩

namespace ExactRawOriginRequestCertificate

def timeout
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next)
    (outputDemand : OriginDemand) :
    ExactRawOriginRequestCertificate elaboration 0 outputDemand OriginEnvironmentDemand.none := by
  let certificate : RawOriginRequestCertificate elaboration 0 outputDemand :=
    ⟨OriginEnvironmentDemand.none, by
      intro solution semantic environment environmentSafe
      exact .inl rfl⟩
  exact ⟨certificate, rfl⟩

def var
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next)
    (operationalFuel : Nat) (outputDemand : OriginDemand) :
    ExactRawOriginRequestCertificate elaboration operationalFuel outputDemand
      (OriginEnvironmentDemand.single position outputDemand) := by
  let certificate := RawOriginRequestCertificate.var elaboration
    operationalFuel outputDemand
  refine ⟨certificate, ?_⟩
  rfl

def litFuel
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lit literal) supply generated next)
    (operationalFuel resultIndex : Nat) :
    ExactRawOriginRequestCertificate elaboration operationalFuel (.fuel resultIndex)
      OriginEnvironmentDemand.none := by
  let certificate : RawOriginRequestCertificate elaboration operationalFuel
      (.fuel resultIndex) :=
    ⟨OriginEnvironmentDemand.none, by
      intro solution _semantic environment _environmentSafe
      simp only [ElaboratesFuel] at elaboration
      obtain ⟨generatedEq, _nextEq⟩ := elaboration
      rw [generatedEq]
      cases operationalFuel with
      | zero => exact .inl rfl
      | succ _ =>
          exact .inr ⟨.int literal, rfl,
            OriginValueSafe.ofFuel (fuelValueSafe_int literal resultIndex)⟩⟩
  exact ⟨certificate, rfl⟩

def somethingFuel
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      .something supply generated next)
    (operationalFuel resultIndex : Nat) :
    ExactRawOriginRequestCertificate elaboration operationalFuel (.fuel resultIndex)
      OriginEnvironmentDemand.none := by
  let certificate : RawOriginRequestCertificate elaboration operationalFuel
      (.fuel resultIndex) :=
    ⟨OriginEnvironmentDemand.none, by
      intro solution _semantic environment _environmentSafe
      simp only [ElaboratesFuel] at elaboration
      obtain ⟨generatedEq, _nextEq⟩ := elaboration
      rw [generatedEq]
      cases operationalFuel with
      | zero => exact .inl rfl
      | succ _ =>
          exact .inr ⟨.something, rfl, OriginValueSafe.ofFuel (by
            simpa [Ty.apply, Cap.apply] using
              fuelValueSafe_something
                ((Ty.var ⟨supply.ty⟩).apply solution) resultIndex)⟩⟩
  exact ⟨certificate, rfl⟩

def both
    (left : ExactRawOriginRequestCertificate elaboration operationalFuel leftDemand leftInput)
    (right : ExactRawOriginRequestCertificate elaboration operationalFuel rightDemand rightInput) :
    ExactRawOriginRequestCertificate elaboration operationalFuel (.both leftDemand rightDemand)
      (OriginEnvironmentDemand.both leftInput rightInput) := by
  let certificate := RawOriginRequestCertificate.both left.certificate
    right.certificate
  refine ⟨certificate, ?_⟩
  simp [certificate, RawOriginRequestCertificate.both,
    left.input_eq, right.input_eq]

def weaken
    (available : ExactRawOriginRequestCertificate elaboration operationalFuel availableDemand
      inputDemand)
    (weaken : OriginDemand.Le requestedDemand availableDemand) :
    ExactRawOriginRequestCertificate elaboration operationalFuel requestedDemand inputDemand := by
  exact ⟨available.certificate.weakenOutput weaken, by
    simp [RawOriginRequestCertificate.weakenOutput, available.input_eq]⟩

def strengthenInput
    (available : ExactRawOriginRequestCertificate elaboration operationalFuel outputDemand
      inputDemand)
    (stronger : OriginEnvironmentDemand)
    (covers : ∀ position,
      OriginDemand.Le (inputDemand position) (stronger position)) :
    ExactRawOriginRequestCertificate elaboration operationalFuel outputDemand stronger := by
  let certificate := available.certificate.strengthenInput stronger (by
    intro position
    rw [available.input_eq]
    exact covers position)
  exact ⟨certificate, rfl⟩

def reobserveUniversal
    (available : ExactRawOriginRequestCertificate elaboration operationalFuel availableDemand
      inputDemand)
    (universal : OriginDemand.Universal requestedDemand) :
    ExactRawOriginRequestCertificate elaboration operationalFuel requestedDemand inputDemand := by
  let certificate : RawOriginRequestCertificate elaboration operationalFuel
      requestedDemand :=
    ⟨available.certificate.inputDemand, by
      intro solution semantic environment environmentSafe
      exact OriginResultSafe.reobserveUniversal
        (available.certificate.preserves solution semantic environment
          environmentSafe) universal⟩
  exact ⟨certificate, available.input_eq⟩

end ExactRawOriginRequestCertificate

namespace ExactRawOriginItemsFuelCertificate

def nil
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context [] supply generated next)
    (operationalFuel resultIndex : Nat) :
    ExactRawOriginItemsFuelCertificate elaboration operationalFuel resultIndex
      OriginEnvironmentDemand.none := by
  let certificate : RawOriginItemsFuelCertificate elaboration
      operationalFuel resultIndex :=
    ⟨OriginEnvironmentDemand.none, by
      intro solution semantic environment environmentSafe
      cases elaboration
      exact .inr ⟨[], by simp [FuelResult.traverse],
        FuelEnvironmentSafe.nil resultIndex⟩⟩
  exact ⟨certificate, rfl⟩

theorem cons
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context (expression :: expressions)
      supply generated next)
    (operationalFuel resultIndex : Nat)
    (headInput tailInput : OriginEnvironmentDemand)
    (headCertificate : ∀ generatedHead afterHead,
      ∀ headElaboration : ElaboratesFuel signature staticFuel context
        expression supply generatedHead afterHead,
        Nonempty (ExactRawOriginRequestCertificate headElaboration operationalFuel
          (.fuel resultIndex) headInput))
    (tailCertificate : ∀ afterHead generatedTail,
      ∀ tailElaboration : ItemsElaborateUsing
        (ElaboratesFuel signature staticFuel) context expressions afterHead
        generatedTail next,
        Nonempty (ExactRawOriginItemsFuelCertificate tailElaboration operationalFuel
          resultIndex tailInput)) :
    Nonempty (ExactRawOriginItemsFuelCertificate elaboration operationalFuel resultIndex
      (OriginEnvironmentDemand.both headInput tailInput)) := by
  cases elaboration with
  | @cons _ _ _ generatedHead afterHead generatedTail _ headElaboration
      tailElaboration =>
      obtain ⟨headExact⟩ :=
        headCertificate generatedHead afterHead headElaboration
      obtain ⟨tailExact⟩ :=
        tailCertificate afterHead generatedTail tailElaboration
      let headCertificate := headExact.certificate
      let tailCertificate := tailExact.certificate
      let inputDemand := OriginEnvironmentDemand.both
        headCertificate.inputDemand tailCertificate.inputDemand
      let certificate : RawOriginItemsFuelCertificate
          (ItemsElaborateUsing.cons headElaboration tailElaboration)
          operationalFuel resultIndex :=
        ⟨inputDemand, by
          intro solution semantic environment environmentSafe
          have headSemantic : generatedHead.SemanticSolution solution := by
            constructor
            · intro equation membership
              exact semantic.1 equation (by
                simp only [List.mem_append]
                exact .inl membership)
            · intro obligation membership
              exact semantic.2 obligation (by
                simp only [List.mem_append]
                exact .inl membership)
          have tailSemantic :
              TypePM.Runtime.GeneratedItems.SemanticSolution generatedTail
                solution := by
            constructor
            · intro equation membership
              exact semantic.1 equation (by
                simp only [List.mem_append]
                exact .inr membership)
            · intro obligation membership
              exact semantic.2 obligation (by
                simp only [List.mem_append]
                exact .inr membership)
          have headEnvironmentSafe := environmentSafe.mono
            (fun position => OriginDemand.Le.fromLeft (.refl _))
          have tailEnvironmentSafe := environmentSafe.mono
            (fun position => OriginDemand.Le.fromRight (.refl _))
          rcases (headCertificate.preserves solution headSemantic environment
              headEnvironmentSafe).toFuel with headTimeout |
              ⟨headValue, headOk, headSafe⟩
          · exact .inl (by simp [FuelResult.traverse, headTimeout])
          · rcases tailCertificate.preserves solution tailSemantic environment
                tailEnvironmentSafe with tailTimeout |
                ⟨tailValues, tailOk, tailSafe⟩
            · exact .inl (by
                simp [FuelResult.traverse, headOk, tailTimeout,
                  FuelResult.bind, FuelResult.map])
            · exact .inr ⟨headValue :: tailValues, by
                simp [FuelResult.traverse, headOk, tailOk, FuelResult.bind,
                  FuelResult.map], by
                simpa [Ty.applyList] using
                  FuelEnvironmentSafe.cons headSafe tailSafe⟩⟩
      refine ⟨⟨certificate, ?_⟩⟩
      simp [certificate, inputDemand, headCertificate, tailCertificate,
        headExact.input_eq, tailExact.input_eq]

end ExactRawOriginItemsFuelCertificate

namespace ExactRawOriginRequestCertificate

theorem tupleFuel
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.tuple expressions) supply generated next)
    (childFuel resultIndex : Nat) (inputDemand : OriginEnvironmentDemand)
    (itemsCertificate : ∀ generatedItems,
      ∀ itemsElaboration : ItemsElaborateUsing
        (ElaboratesFuel signature staticFuel) context expressions supply
        generatedItems next,
      Nonempty (ExactRawOriginItemsFuelCertificate itemsElaboration childFuel
        resultIndex inputDemand)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      (.fuel resultIndex) inputDemand) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedItems, itemsElaboration, generatedEq⟩ := elaboration
  obtain ⟨itemsExact⟩ := itemsCertificate generatedItems itemsElaboration
  let itemsCertificate := itemsExact.certificate
  let certificate : RawOriginRequestCertificate parentElaboration (childFuel + 1)
      (.fuel resultIndex) :=
    ⟨itemsCertificate.inputDemand, by
      intro solution semantic environment environmentSafe
      have itemsSemantic :
          TypePM.Runtime.GeneratedItems.SemanticSolution generatedItems
            solution := by
        rw [generatedEq] at semantic
        exact semantic
      rw [generatedEq]
      rcases itemsCertificate.preserves solution itemsSemantic environment
          environmentSafe with timeout | ⟨values, success, valuesSafe⟩
      · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
      · exact .inr ⟨.tuple values, by
          simp [evalFuel, success, FuelResult.map], OriginValueSafe.ofFuel (by
          simpa [Ty.apply] using
            fuelValueSafe_tuple_of_environment resultIndex values
              (Ty.applyList solution generatedItems.targets) valuesSafe)⟩⟩
  refine ⟨⟨certificate, ?_⟩⟩
  exact itemsExact.input_eq

theorem lamPlainCall
    {bodyOperationalFuel lambdaOperationalFuel : Nat}
    {argumentDemand resultDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lam body) supply generated next)
    (bodyInput : OriginEnvironmentDemand)
    (bodyCertificate : ∀ generatedBody,
      ∀ bodyElaboration : ElaboratesFuel signature staticFuel
        (Scheme.mono (.var ⟨supply.ty⟩) :: context) body
        (supply.nextTy 1) generatedBody next,
      Nonempty (ExactRawOriginRequestCertificate bodyElaboration bodyOperationalFuel
        resultDemand bodyInput))
    (argumentCoversBody : OriginDemand.Le (bodyInput 0) argumentDemand) :
    Nonempty (ExactRawOriginRequestCertificate elaboration lambdaOperationalFuel
      (.plainCall (bodyOperationalFuel + 1) argumentDemand resultDemand)
      (OriginEnvironmentDemand.tail bodyInput)) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedBody, bodyElaboration, generatedEq⟩ := elaboration
  obtain ⟨bodyExact⟩ := bodyCertificate generatedBody bodyElaboration
  let bodyCertificate := bodyExact.certificate
  let inputDemand := OriginEnvironmentDemand.tail bodyCertificate.inputDemand
  let certificate : RawOriginRequestCertificate parentElaboration
      lambdaOperationalFuel
      (.plainCall (bodyOperationalFuel + 1) argumentDemand resultDemand) :=
    ⟨inputDemand, by
      intro solution semantic environment environmentSafe
      cases lambdaOperationalFuel with
      | zero => exact .inl rfl
      | succ lambdaFuel =>
          rw [generatedEq] at semantic ⊢
          refine .inr ⟨.plainClosure environment body, rfl, ?_⟩
          apply OriginValueSafe.plainClosure
          intro argument argumentSafe
          apply bodyCertificate.preserves solution semantic
            (argument :: environment)
          have headCovered : OriginDemand.Le
              (bodyCertificate.inputDemand 0) argumentDemand := by
            rw [bodyExact.input_eq]
            exact argumentCoversBody
          have headSafe : SchemeOriginValueSafe
              (bodyCertificate.inputDemand 0) argument
              (Scheme.mono (.var ⟨supply.ty⟩)) solution :=
            SchemeOriginValueSafe.ofMono
              (argumentSafe.mono headCovered)
          have pushed := SchemeOriginEnvironmentSafe.cons headSafe
            environmentSafe
          apply pushed.congr
          intro position _positionLt
          cases position <;> rfl⟩
  refine ⟨⟨certificate, ?_⟩⟩
  exact congrArg OriginEnvironmentDemand.tail bodyExact.input_eq

theorem lamZeroCall
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lam body) supply generated next)
    (lambdaOperationalFuel : Nat)
    (argumentDemand resultDemand : OriginDemand) :
    Nonempty (ExactRawOriginRequestCertificate elaboration lambdaOperationalFuel
      (.plainCall 0 argumentDemand resultDemand)
      OriginEnvironmentDemand.none) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedBody, bodyElaboration, generatedEq⟩ := elaboration
  let certificate : RawOriginRequestCertificate parentElaboration
      lambdaOperationalFuel (.plainCall 0 argumentDemand resultDemand) :=
    ⟨OriginEnvironmentDemand.none, by
      intro solution semantic environment environmentSafe
      cases lambdaOperationalFuel with
      | zero => exact .inl rfl
      | succ lambdaFuel =>
          rw [generatedEq] at semantic ⊢
          refine .inr ⟨.plainClosure environment body, rfl, ?_⟩
          simp only [OriginValueSafe]
          exact .zero⟩
  exact ⟨⟨certificate, rfl⟩⟩

theorem app
    {childFuel : Nat} {argumentDemand resultDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.app function argument) supply generated next)
    (functionInput argumentInput : OriginEnvironmentDemand)
    (functionCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ _argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (ExactRawOriginRequestCertificate functionElaboration childFuel
        (.plainCall childFuel argumentDemand resultDemand) functionInput))
    (argumentCertificate : ∀ generatedFunction afterFunction
        generatedArgument afterArgument,
      ∀ _functionElaboration : ElaboratesFuel signature staticFuel context
        function supply generatedFunction afterFunction,
      ∀ argumentElaboration : ElaboratesFuel signature staticFuel context
        argument afterFunction generatedArgument afterArgument,
      Nonempty (ExactRawOriginRequestCertificate argumentElaboration childFuel
        argumentDemand argumentInput)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1) resultDemand
      (OriginEnvironmentDemand.both functionInput argumentInput)) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedFunction, afterFunction, generatedArgument, afterArgument,
    functionElaboration, argumentElaboration, generatedEq, nextEq⟩ := elaboration
  obtain ⟨functionExact⟩ := functionCertificate generatedFunction
    afterFunction generatedArgument afterArgument functionElaboration
    argumentElaboration
  obtain ⟨argumentExact⟩ := argumentCertificate generatedFunction
    afterFunction generatedArgument afterArgument functionElaboration
    argumentElaboration
  let functionCertificate := functionExact.certificate
  let argumentCertificate := argumentExact.certificate
  let inputDemand := OriginEnvironmentDemand.both
    functionCertificate.inputDemand argumentCertificate.inputDemand
  let certificate : RawOriginRequestCertificate parentElaboration
      (childFuel + 1) resultDemand :=
    ⟨inputDemand, by
      intro solution semantic environment environmentSafe
      rw [generatedEq] at semantic ⊢
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
      have functionSafe := functionCertificate.preserves solution
        functionSemantic environment
        (environmentSafe.mono (fun position => .fromLeft (.refl _)))
      rw [functionType] at functionSafe
      have argumentSafeAtSource := argumentCertificate.preserves solution
        argumentSemantic environment
        (environmentSafe.mono (fun position => .fromRight (.refl _)))
      have argumentSafe := argumentSafeAtSource.ofCheckConversion
        argumentConversion
      exact evalFuel_app_origin functionSafe argumentSafe⟩
  refine ⟨⟨certificate, ?_⟩⟩
  change OriginEnvironmentDemand.both functionCertificate.inputDemand
      argumentCertificate.inputDemand =
    OriginEnvironmentDemand.both functionInput argumentInput
  rw [functionExact.input_eq, argumentExact.input_eq]

/-- Source-derived `letE` composition when every observation requested by
the right-hand side from the outer environment is universal.  The body may
request an arbitrary structural observation from the generalized binding.

For each scheme occurrence, the exact principal right-hand-side closure
constructs an occurrence-specific semantic solution.  Universality makes the
outer runtime environment safe under that solution without assuming an
evaluation result or an occurrence-transport oracle. -/
theorem letUniversalInput
    {childFuel : Nat} {outputDemand : OriginDemand}
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.letE value body) supply generated next)
    (valueInput bodyInput : OriginEnvironmentDemand)
    (valueInputUniversal : ∀ position,
      OriginDemand.Universal (valueInput position))
    (valueCertificate : ∀ generatedValue afterValue,
      ∀ valueElaboration : ElaboratesFuel signature staticFuel context value
        supply generatedValue afterValue,
      Nonempty (ExactRawOriginRequestCertificate valueElaboration childFuel
        (bodyInput 0) valueInput))
    (bodyCertificate : ∀ generatedValue afterValue,
      ∀ _valueElaboration : ElaboratesFuel signature staticFuel context value
        supply generatedValue afterValue,
      ∀ valueClosure : PrincipalBlockClosure generatedValue,
      ∀ bodyGenerated,
      ∀ bodyElaboration : ElaboratesFuel signature staticFuel
        ((context.applyFree valueClosure.substitution).generalize
            valueClosure.target :: context.applyFree valueClosure.substitution)
        body
        (afterValue.join
          (context.applyFree valueClosure.substitution).initialSupply)
        bodyGenerated next,
      Nonempty (ExactRawOriginRequestCertificate bodyElaboration childFuel
        outputDemand bodyInput)) :
    Nonempty (ExactRawOriginRequestCertificate elaboration (childFuel + 1)
      outputDemand (OriginEnvironmentDemand.tail bodyInput)) := by
  let parentElaboration := elaboration
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedValue, afterValue, valueElaboration, valueClosure,
    bodyGenerated, valueAbsorbing, bodyElaboration, generatedEq⟩ := elaboration
  obtain ⟨valueExact⟩ := valueCertificate generatedValue afterValue
    valueElaboration
  obtain ⟨bodyExact⟩ := bodyCertificate generatedValue afterValue
    valueElaboration valueClosure bodyGenerated bodyElaboration
  let generalizedScheme :=
    (context.applyFree valueClosure.substitution).generalize
      valueClosure.target
  let certificate : RawOriginRequestCertificate parentElaboration
      (childFuel + 1) outputDemand :=
    ⟨OriginEnvironmentDemand.tail bodyInput, by
      intro solution semantic environment environmentSafe
      rw [generatedEq] at semantic
      obtain ⟨interfaceSolved, bodySemantic⟩ :=
        semanticSolution_fromLet_parts semantic
      have valueResult : FuelResultSafeWith
          (fun value => SchemeOriginValueSafe (bodyInput 0) value
            generalizedScheme solution)
          (evalFuel childFuel environment value) := by
        let initialSupply : Supply := ⟨0, 0⟩
        let initialOccurrence :=
          TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution
            valueClosure valueAbsorbing context solution interfaceSolved
              initialSupply
        have initialEnvironmentSafe : SchemeOriginEnvironmentSafe valueInput
            initialOccurrence.solution environment context :=
          schemeOriginEnvironmentSafe_ofUniversal environmentSafe.1
            valueInputUniversal
        have initialResult := valueExact.certificate.preserves
          initialOccurrence.solution initialOccurrence.semantic environment
          (by simpa [valueExact.input_eq] using initialEnvironmentSafe)
        rw [initialOccurrence.target_eq] at initialResult
        rcases initialResult with valueTimeout |
            ⟨actual, valueSuccess, _initialSafe⟩
        · exact .inl valueTimeout
        · refine .inr ⟨actual, valueSuccess, ?_⟩
          intro occurrenceSupply
          let occurrence :=
            TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution
              valueClosure valueAbsorbing context solution interfaceSolved
                occurrenceSupply
          have occurrenceEnvironmentSafe : SchemeOriginEnvironmentSafe
              valueInput occurrence.solution environment context :=
            schemeOriginEnvironmentSafe_ofUniversal environmentSafe.1
              valueInputUniversal
          have occurrenceResult := valueExact.certificate.preserves
            occurrence.solution occurrence.semantic environment
            (by simpa [valueExact.input_eq] using occurrenceEnvironmentSafe)
          rw [occurrence.target_eq] at occurrenceResult
          rcases occurrenceResult with occurrenceTimeout |
              ⟨occurrenceValue, occurrenceSuccess, occurrenceSafe⟩
          · rw [valueSuccess] at occurrenceTimeout
            contradiction
          · rw [valueSuccess] at occurrenceSuccess
            cases occurrenceSuccess
            exact occurrenceSafe
      have bodyTailClosedSafe : SchemeOriginEnvironmentSafe
          (OriginEnvironmentDemand.tail bodyInput) solution environment
          (context.applyFree valueClosure.substitution) :=
        schemeOriginEnvironmentSafe_ofApplyFreeInterface environmentSafe
          interfaceSolved
      rw [generatedEq]
      apply evalFuel_letE_resultSafeWith valueResult
      intro boundValue boundSafe
      have bodyEnvironmentSafe : SchemeOriginEnvironmentSafe bodyInput
          solution (boundValue :: environment)
          (generalizedScheme ::
            context.applyFree valueClosure.substitution) := by
        have pushed := SchemeOriginEnvironmentSafe.cons boundSafe
          bodyTailClosedSafe
        apply pushed.congr
        intro position _within
        cases position <;> rfl
      exact bodyExact.certificate.preserves solution bodySemantic
        (boundValue :: environment)
        (by simpa [bodyExact.input_eq] using bodyEnvironmentSafe)⟩
  exact ⟨⟨certificate, rfl⟩⟩

end ExactRawOriginRequestCertificate

mutual

  /-- Static realizability of one output observation.  The indices state the
  evaluator fuel, output demand, and exact source-environment input demand.
  No semantic solution or runtime value occurs in this judgment. -/
  inductive RawOriginRequestPlan :
      Nat → Expr → OriginDemand → OriginEnvironmentDemand → Prop where
    /-- At evaluator fuel zero every expression times out, so every output
    observation is vacuously realizable without observing the environment. -/
    | timeout : RawOriginRequestPlan 0 expression outputDemand
        OriginEnvironmentDemand.none
    | var : RawOriginRequestPlan operationalFuel (.var position) outputDemand
        (OriginEnvironmentDemand.single position outputDemand)
    | litFuel : RawOriginRequestPlan operationalFuel (.lit literal) (.fuel resultIndex)
        OriginEnvironmentDemand.none
    | somethingFuel : RawOriginRequestPlan operationalFuel .something (.fuel resultIndex)
        OriginEnvironmentDemand.none
    /-- A positive tuple observation uses one less evaluator fuel for every
    field and requests the same ordinary result index from every field. -/
    | tupleFuel
        (items : RawOriginItemsFuelPlan childFuel expressions resultIndex input) :
        RawOriginRequestPlan (childFuel + 1) (.tuple expressions) (.fuel resultIndex)
          input
    /-- A positive future call delegates its result observation to the body.
    The public argument demand must cover the body's exact position-zero
    demand; the remaining positions become the captured-environment demand. -/
    | lamPlainCall
        (bodyPlan : RawOriginRequestPlan bodyOperationalFuel body resultDemand bodyInput)
        (argumentCoversBody : OriginDemand.Le (bodyInput 0) argumentDemand) :
        RawOriginRequestPlan lambdaOperationalFuel (.lam body)
          (.plainCall (bodyOperationalFuel + 1)
            argumentDemand resultDemand)
          (OriginEnvironmentDemand.tail bodyInput)
    | lamZeroCall : RawOriginRequestPlan lambdaOperationalFuel (.lam body)
        (.plainCall 0 argumentDemand resultDemand)
        OriginEnvironmentDemand.none
    /-- Uniform application transports any argument demand through the
    normalized checking conversion stored by the parent block. -/
    | app
        (functionPlan : RawOriginRequestPlan childFuel function
          (.plainCall childFuel argumentDemand resultDemand) functionInput)
        (argumentPlan : RawOriginRequestPlan childFuel argument argumentDemand
          argumentInput) :
        RawOriginRequestPlan (childFuel + 1) (.app function argument) resultDemand
          (OriginEnvironmentDemand.both functionInput argumentInput)
    /-- A generalized `letE` may delegate its binding observation to the
    right-hand side when the latter's outer-environment observations are
    universal under every occurrence-specific semantic solution. -/
    | letUniversalInput
        (valuePlan : RawOriginRequestPlan childFuel value (bodyInput 0)
          valueInput)
        (valueInputUniversal : ∀ position,
          OriginDemand.Universal (valueInput position))
        (bodyPlan : RawOriginRequestPlan childFuel body outputDemand bodyInput) :
        RawOriginRequestPlan (childFuel + 1) (.letE value body) outputDemand
          (OriginEnvironmentDemand.tail bodyInput)
    | both
        (left : RawOriginRequestPlan operationalFuel expression leftDemand leftInput)
        (right : RawOriginRequestPlan operationalFuel expression rightDemand rightInput) :
        RawOriginRequestPlan operationalFuel expression (.both leftDemand rightDemand)
          (OriginEnvironmentDemand.both leftInput rightInput)
    | weaken
        (available : RawOriginRequestPlan operationalFuel expression availableDemand input)
        (weaken : OriginDemand.Le requestedDemand availableDemand) :
        RawOriginRequestPlan operationalFuel expression requestedDemand input
    /-- Once evaluation is known not to be stuck, it can be reobserved with a
    demand that is satisfied by every value and type. -/
    | universal
        (available : RawOriginRequestPlan operationalFuel expression availableDemand input)
        (requested : OriginDemand.Universal requestedDemand) :
        RawOriginRequestPlan operationalFuel expression requestedDemand input
    | strengthenInput
        (available : RawOriginRequestPlan operationalFuel expression outputDemand input)
        (covers : ∀ position,
          OriginDemand.Le (input position) (stronger position)) :
        RawOriginRequestPlan operationalFuel expression outputDemand stronger

  /-- Tuple-field companion: every field must realize the same positive
  ordinary-fuel output observation at the tuple's child evaluator fuel. -/
  inductive RawOriginItemsFuelPlan :
      Nat → List Expr → Nat → OriginEnvironmentDemand → Prop where
    | nil : RawOriginItemsFuelPlan operationalFuel [] resultIndex
        OriginEnvironmentDemand.none
    | cons
        (head : RawOriginRequestPlan operationalFuel expression (.fuel resultIndex)
          headInput)
        (tail : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
          tailInput) :
        RawOriginItemsFuelPlan operationalFuel (expression :: expressions)
          resultIndex (OriginEnvironmentDemand.both headInput tailInput)

end

/-- Motive used by the mutual recursor.  It is stated separately so the same
kernel-checked handlers feed both projections of the mutual recursion. -/
private def RawOriginRequestCertificateMotive
    (operationalFuel : Nat) (expression : Expr)
    (outputDemand : OriginDemand) (inputDemand : OriginEnvironmentDemand)
    (_plan : RawOriginRequestPlan operationalFuel expression outputDemand inputDemand) :
    Prop :=
  ∀ {signature staticFuel context supply generated next},
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next) →
    Nonempty (ExactRawOriginRequestCertificate elaboration operationalFuel outputDemand
      inputDemand)

private def RawOriginItemsFuelCertificateMotive
    (operationalFuel : Nat) (expressions : List Expr) (resultIndex : Nat)
    (inputDemand : OriginEnvironmentDemand)
    (_plan : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
      inputDemand) : Prop :=
  ∀ {signature staticFuel context supply generated next},
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context expressions supply
      generated next) →
    Nonempty (ExactRawOriginItemsFuelCertificate elaboration operationalFuel
      resultIndex inputDemand)

namespace RawOriginRequestProducerHandlers

private theorem timeout : ∀ {expression outputDemand},
    RawOriginRequestCertificateMotive 0 expression outputDemand OriginEnvironmentDemand.none
      .timeout := by
  intro expression outputDemand signature staticFuel context supply generated
    next elaboration
  exact ⟨ExactRawOriginRequestCertificate.timeout elaboration _⟩

private theorem var : ∀ {operationalFuel position outputDemand},
    RawOriginRequestCertificateMotive operationalFuel (.var position) outputDemand
      (OriginEnvironmentDemand.single position outputDemand) .var := by
  intro operationalFuel position outputDemand signature staticFuel context
    supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel => exact ⟨ExactRawOriginRequestCertificate.var elaboration _ _⟩

private theorem litFuel : ∀ {operationalFuel literal resultIndex},
    RawOriginRequestCertificateMotive operationalFuel (.lit literal) (.fuel resultIndex)
      OriginEnvironmentDemand.none .litFuel := by
  intro operationalFuel literal resultIndex signature staticFuel context supply
    generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel => exact ⟨ExactRawOriginRequestCertificate.litFuel elaboration _ _⟩

private theorem somethingFuel : ∀ {operationalFuel resultIndex},
    RawOriginRequestCertificateMotive operationalFuel .something (.fuel resultIndex)
      OriginEnvironmentDemand.none .somethingFuel := by
  intro operationalFuel resultIndex signature staticFuel context supply
    generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel => exact ⟨ExactRawOriginRequestCertificate.somethingFuel elaboration _ _⟩

private theorem tupleFuel : ∀ {childFuel expressions resultIndex input}
    (items : RawOriginItemsFuelPlan childFuel expressions resultIndex input),
    RawOriginItemsFuelCertificateMotive childFuel expressions resultIndex input
      items →
    RawOriginRequestCertificateMotive (childFuel + 1) (.tuple expressions)
      (.fuel resultIndex) input (.tupleFuel items) := by
  intro childFuel expressions resultIndex input items itemsIH signature
    staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.tupleFuel elaboration _ _ _
      intro generatedItems itemsElaboration
      exact itemsIH itemsElaboration

private theorem lamPlainCall :
    ∀ {bodyOperationalFuel body resultDemand bodyInput argumentDemand
        lambdaOperationalFuel}
      (bodyPlan : RawOriginRequestPlan bodyOperationalFuel body resultDemand bodyInput)
      (argumentCoversBody : OriginDemand.Le (bodyInput 0) argumentDemand),
      RawOriginRequestCertificateMotive bodyOperationalFuel body resultDemand bodyInput
          bodyPlan →
        RawOriginRequestCertificateMotive lambdaOperationalFuel (.lam body)
          (.plainCall (bodyOperationalFuel + 1) argumentDemand resultDemand)
          (OriginEnvironmentDemand.tail bodyInput)
          (.lamPlainCall bodyPlan argumentCoversBody) := by
  intro bodyOperationalFuel body resultDemand bodyInput argumentDemand
    lambdaOperationalFuel bodyPlan argumentCoversBody bodyIH signature
    staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.lamPlainCall elaboration _
      · intro generatedBody bodyElaboration
        exact bodyIH bodyElaboration
      · exact argumentCoversBody

private theorem lamZeroCall : ∀ {lambdaOperationalFuel body argumentDemand resultDemand},
    RawOriginRequestCertificateMotive lambdaOperationalFuel (.lam body)
      (.plainCall 0 argumentDemand resultDemand) OriginEnvironmentDemand.none
      .lamZeroCall := by
  intro lambdaOperationalFuel body argumentDemand resultDemand signature
    staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      exact ExactRawOriginRequestCertificate.lamZeroCall elaboration _ _ _

private theorem app :
    ∀ {childFuel function argumentDemand resultDemand functionInput argument
        argumentInput}
      (functionPlan : RawOriginRequestPlan childFuel function
        (.plainCall childFuel argumentDemand resultDemand) functionInput)
      (argumentPlan : RawOriginRequestPlan childFuel argument argumentDemand argumentInput),
      RawOriginRequestCertificateMotive childFuel function
          (.plainCall childFuel argumentDemand resultDemand) functionInput
          functionPlan →
        RawOriginRequestCertificateMotive childFuel argument argumentDemand argumentInput
            argumentPlan →
          RawOriginRequestCertificateMotive (childFuel + 1) (.app function argument)
            resultDemand (OriginEnvironmentDemand.both functionInput
              argumentInput)
            (.app functionPlan argumentPlan) := by
  intro childFuel function argumentDemand resultDemand functionInput argument
    argumentInput functionPlan argumentPlan functionIH argumentIH
    signature staticFuel context supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.app elaboration _ _
      · intro generatedFunction afterFunction generatedArgument afterArgument
          functionElaboration argumentElaboration
        exact functionIH functionElaboration
      · intro generatedFunction afterFunction generatedArgument afterArgument
          functionElaboration argumentElaboration
        exact argumentIH argumentElaboration

private theorem letUniversalInput :
    ∀ {childFuel value bodyInput valueInput body outputDemand}
      (valuePlan : RawOriginRequestPlan childFuel value (bodyInput 0)
        valueInput)
      (valueInputUniversal : ∀ position,
        OriginDemand.Universal (valueInput position))
      (bodyPlan : RawOriginRequestPlan childFuel body outputDemand bodyInput),
      RawOriginRequestCertificateMotive childFuel value (bodyInput 0)
          valueInput valuePlan →
        RawOriginRequestCertificateMotive childFuel body outputDemand bodyInput
            bodyPlan →
          RawOriginRequestCertificateMotive (childFuel + 1)
            (.letE value body) outputDemand
            (OriginEnvironmentDemand.tail bodyInput)
            (.letUniversalInput valuePlan valueInputUniversal bodyPlan) := by
  intro childFuel value bodyInput valueInput body outputDemand valuePlan
    valueInputUniversal bodyPlan valueIH bodyIH signature staticFuel context
    supply generated next elaboration
  cases staticFuel with
  | zero => exact False.elim elaboration
  | succ staticFuel =>
      apply ExactRawOriginRequestCertificate.letUniversalInput elaboration
        valueInput bodyInput valueInputUniversal
      · intro generatedValue afterValue valueElaboration
        exact valueIH valueElaboration
      · intro generatedValue afterValue valueElaboration valueClosure
          bodyGenerated bodyElaboration
        exact bodyIH bodyElaboration

private theorem both :
    ∀ {operationalFuel expression leftDemand leftInput rightDemand rightInput}
      (left : RawOriginRequestPlan operationalFuel expression leftDemand leftInput)
      (right : RawOriginRequestPlan operationalFuel expression rightDemand rightInput),
      RawOriginRequestCertificateMotive operationalFuel expression leftDemand leftInput left →
        RawOriginRequestCertificateMotive operationalFuel expression rightDemand rightInput
            right →
          RawOriginRequestCertificateMotive operationalFuel expression (.both leftDemand
            rightDemand) (OriginEnvironmentDemand.both leftInput rightInput)
            (.both left right) := by
  intro operationalFuel expression leftDemand leftInput rightDemand rightInput
    left right leftIH rightIH signature staticFuel context supply generated next
    elaboration
  obtain ⟨leftExact⟩ := leftIH elaboration
  obtain ⟨rightExact⟩ := rightIH elaboration
  exact ⟨ExactRawOriginRequestCertificate.both leftExact rightExact⟩

private theorem weaken :
    ∀ {operationalFuel expression availableDemand input requestedDemand}
      (available : RawOriginRequestPlan operationalFuel expression availableDemand input)
      (weaken : OriginDemand.Le requestedDemand availableDemand),
      RawOriginRequestCertificateMotive operationalFuel expression availableDemand input
          available →
        RawOriginRequestCertificateMotive operationalFuel expression requestedDemand input
          (.weaken available weaken) := by
  intro operationalFuel expression availableDemand input requestedDemand
    available weaken availableIH signature staticFuel context supply generated
    next elaboration
  obtain ⟨availableExact⟩ := availableIH elaboration
  exact ⟨ExactRawOriginRequestCertificate.weaken availableExact weaken⟩

private theorem universal :
    ∀ {operationalFuel expression availableDemand input requestedDemand}
      (available : RawOriginRequestPlan operationalFuel expression availableDemand input)
      (requested : OriginDemand.Universal requestedDemand),
      RawOriginRequestCertificateMotive operationalFuel expression availableDemand input
          available →
        RawOriginRequestCertificateMotive operationalFuel expression requestedDemand input
          (.universal available requested) := by
  intro operationalFuel expression availableDemand input requestedDemand
    available requested availableIH signature staticFuel context supply
    generated next elaboration
  obtain ⟨availableExact⟩ := availableIH elaboration
  exact ⟨ExactRawOriginRequestCertificate.reobserveUniversal availableExact requested⟩

private theorem strengthenInput :
    ∀ {operationalFuel expression outputDemand input stronger}
      (available : RawOriginRequestPlan operationalFuel expression outputDemand input)
      (covers : ∀ position,
        OriginDemand.Le (input position) (stronger position)),
      RawOriginRequestCertificateMotive operationalFuel expression outputDemand input
          available →
        RawOriginRequestCertificateMotive operationalFuel expression outputDemand stronger
          (.strengthenInput available covers) := by
  intro operationalFuel expression outputDemand input stronger available covers
    availableIH signature staticFuel context supply generated next elaboration
  obtain ⟨availableExact⟩ := availableIH elaboration
  exact ⟨ExactRawOriginRequestCertificate.strengthenInput availableExact _ covers⟩

private theorem nil : ∀ {operationalFuel resultIndex},
    RawOriginItemsFuelCertificateMotive operationalFuel [] resultIndex
      OriginEnvironmentDemand.none .nil := by
  intro operationalFuel resultIndex signature staticFuel context supply
    generated next elaboration
  exact ⟨ExactRawOriginItemsFuelCertificate.nil elaboration _ _⟩

private theorem cons :
    ∀ {operationalFuel expression resultIndex headInput expressions tailInput}
      (head : RawOriginRequestPlan operationalFuel expression (.fuel resultIndex)
        headInput)
      (tail : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
        tailInput),
      RawOriginRequestCertificateMotive operationalFuel expression (.fuel resultIndex)
          headInput head →
        RawOriginItemsFuelCertificateMotive operationalFuel expressions
            resultIndex tailInput tail →
          RawOriginItemsFuelCertificateMotive operationalFuel
            (expression :: expressions) resultIndex
            (OriginEnvironmentDemand.both headInput tailInput)
            (.cons head tail) := by
  intro operationalFuel expression resultIndex headInput expressions tailInput
    head tail headIH tailIH signature staticFuel context supply generated next
    elaboration
  apply ExactRawOriginItemsFuelCertificate.cons elaboration _ _ _ _
  · intro generatedHead afterHead headElaboration
    exact headIH headElaboration
  · intro afterHead generatedTail tailElaboration
    exact tailIH tailElaboration

end RawOriginRequestProducerHandlers

theorem RawOriginRequestPlan.certificate
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand inputDemand) :
    RawOriginRequestCertificateMotive operationalFuel expression outputDemand inputDemand
      plan :=
  RawOriginRequestPlan.rec (motive_1 := RawOriginRequestCertificateMotive)
    (motive_2 := RawOriginItemsFuelCertificateMotive)
    RawOriginRequestProducerHandlers.timeout RawOriginRequestProducerHandlers.var RawOriginRequestProducerHandlers.litFuel
    RawOriginRequestProducerHandlers.somethingFuel RawOriginRequestProducerHandlers.tupleFuel
    RawOriginRequestProducerHandlers.lamPlainCall RawOriginRequestProducerHandlers.lamZeroCall
    RawOriginRequestProducerHandlers.app RawOriginRequestProducerHandlers.letUniversalInput
    RawOriginRequestProducerHandlers.both
    RawOriginRequestProducerHandlers.weaken RawOriginRequestProducerHandlers.universal
    RawOriginRequestProducerHandlers.strengthenInput RawOriginRequestProducerHandlers.nil
    RawOriginRequestProducerHandlers.cons plan

theorem RawOriginItemsFuelPlan.certificate
    (plan : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
      inputDemand) :
    RawOriginItemsFuelCertificateMotive operationalFuel expressions resultIndex
      inputDemand
      plan :=
  RawOriginItemsFuelPlan.rec (motive_1 := RawOriginRequestCertificateMotive)
    (motive_2 := RawOriginItemsFuelCertificateMotive)
    RawOriginRequestProducerHandlers.timeout RawOriginRequestProducerHandlers.var RawOriginRequestProducerHandlers.litFuel
    RawOriginRequestProducerHandlers.somethingFuel RawOriginRequestProducerHandlers.tupleFuel
    RawOriginRequestProducerHandlers.lamPlainCall RawOriginRequestProducerHandlers.lamZeroCall
    RawOriginRequestProducerHandlers.app RawOriginRequestProducerHandlers.letUniversalInput
    RawOriginRequestProducerHandlers.both
    RawOriginRequestProducerHandlers.weaken RawOriginRequestProducerHandlers.universal
    RawOriginRequestProducerHandlers.strengthenInput RawOriginRequestProducerHandlers.nil
    RawOriginRequestProducerHandlers.cons plan

/-- A static request plan produces an exact certificate for every matching
raw M4 derivation.  In particular, the advertised input demand is not hidden
behind the existential field of `RawOriginRequestCertificate`. -/
theorem RawOriginRequestPlan.exactCertificate
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next) :
    Nonempty (ExactRawOriginRequestCertificate elaboration operationalFuel
      outputDemand inputDemand) :=
  plan.certificate elaboration

/-- Tuple-field companion of `RawOriginRequestPlan.exactCertificate`. -/
theorem RawOriginItemsFuelPlan.exactCertificate
    (plan : RawOriginItemsFuelPlan operationalFuel expressions resultIndex
      inputDemand)
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context expressions supply
      generated next) :
    Nonempty (ExactRawOriginItemsFuelCertificate elaboration operationalFuel
      resultIndex inputDemand) :=
  plan.certificate elaboration

namespace RawOriginRequestPlan

/-- Reobserve any supported evaluation only for absence of `stuck`.  The
existing input demand is retained; at a closed root it is harmless because
the empty runtime environment satisfies every per-position demand. -/
def rootNone
    (plan : RawOriginRequestPlan operationalFuel expression availableDemand inputDemand) :
    RawOriginRequestPlan operationalFuel expression .none inputDemand :=
  .universal plan .none

/-- Closed-root no-stuck consequence.  The plan fixes operational fuel and
all environment demands before the later semantic solution is supplied. -/
theorem closedNoStuckOfElaboration
    (plan : RawOriginRequestPlan operationalFuel expression .none inputDemand)
    (elaboration : ElaboratesFuel signature staticFuel [] expression supply
      generated next)
    (semantic : generated.SemanticSolution solution) :
    (evalFuel operationalFuel [] expression).NotStuck := by
  obtain ⟨exact⟩ := plan.exactCertificate elaboration
  exact (exact.certificate.preserves solution semantic []
    (SchemeOriginEnvironmentSafe.nil exact.certificate.inputDemand
      solution)).notStuck

/-- A closed public M4 typing supplies the principal raw derivation and a
semantic solution required by the plan.  Postcomposing the principal closure
with the typing instance transports the generated target to the requested
public result type. -/
theorem closedOriginResultSafe
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (typing : Typing signature [] expression target) :
    OriginResultSafe outputDemand target
      (evalFuel operationalFuel [] expression) := by
  rcases typing with
    ⟨principal, ⟨derivation⟩, later, targetEquality⟩
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  obtain ⟨exact⟩ := plan.exactCertificate elaboration
  let solution := Subst.compose later derivation.closure.substitution
  have semantic : derivation.generated.SemanticSolution solution :=
    semanticSolution_postcompose
      (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
        derivation.closure)
      later
  have safe := exact.certificate.preserves solution semantic []
    (SchemeOriginEnvironmentSafe.nil exact.certificate.inputDemand solution)
  have targetApplied :
      derivation.generated.target.apply solution = target := by
    calc
      derivation.generated.target.apply solution =
          (derivation.generated.target.apply
            derivation.closure.substitution).apply later := by
        simp [solution, Ty.apply_compose]
      _ = derivation.closure.target.apply later := by
        rfl
      _ = principal.apply later := by
        rw [← derivation.target_eq]
      _ = target := targetEquality
  rw [targetApplied] at safe
  exact safe

/-- Every closed public M4 typing with a realizable request avoids `stuck` at
the plan's evaluator fuel. -/
theorem closedNeverStuck
    (plan : RawOriginRequestPlan operationalFuel expression outputDemand
      inputDemand)
    (typing : Typing signature [] expression target) :
    (evalFuel operationalFuel [] expression).NotStuck :=
  (plan.closedOriginResultSafe typing).notStuck

end RawOriginRequestPlan

/-- A source expression has a realizable no-stuck request at every evaluator
fuel.  The input demand may depend on fuel but is always fixed before a later
semantic solution or runtime environment is supplied. -/
def RawOriginNoStuckSupported (expression : Expr) : Prop :=
  ∀ operationalFuel,
    ∃ inputDemand,
      RawOriginRequestPlan operationalFuel expression .none inputDemand

/-- A closed public M4 typing in the uniformly supported fragment avoids
`stuck` at every evaluator fuel. -/
theorem RawOriginNoStuckSupported.closedNeverStuck
    (supported : RawOriginNoStuckSupported expression)
    (typing : Typing signature [] expression target)
    (operationalFuel : Nat) :
    (evalFuel operationalFuel [] expression).NotStuck := by
  obtain ⟨inputDemand, plan⟩ := supported operationalFuel
  exact plan.closedNeverStuck typing

end TypePM.Source.M4
