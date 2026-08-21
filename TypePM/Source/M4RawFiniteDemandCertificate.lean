import TypePM.SchemeIndexedFuelSafety
import TypePM.RuntimeTyping

/-!
# Raw M4 certificates with finite per-position input demand

An expression does not generally need the same logical safety index from
every captured environment entry.  A variable needs its requested result
index only at the selected position, while a tuple joins the demands of its
children position by position.  This module records that finite information
without identifying evaluator fuel, M4 structural fuel, and the logical
result index.

The demand function is chosen from the exact raw `M4.ElaboratesFuel`
derivation before a semantic solution is supplied.  This quantifier order is
essential for a later polymorphic `let` rule: distinct occurrences of the
generalized right-hand side use distinct postcomposed solutions, but must
still share one finite input demand.

The constructor-wide fragment completed here contains variables, integer
literals, `something`, and arbitrarily nested tuples.  Application remains
separate because the current `FuelValueSafe` relation is not yet proved
closed under every `CheckConversion`.  Lambda additionally needs a logical
relation that can use a monomorphic argument at its available index, and
`letE` needs a static producer relating every generalized occurrence to a
postcomposition of the exact right-hand-side principal closure.

For this completed constructor scope, the final closed wrappers below consume
the principal witness hidden by `M4.Typing`, postcompose its semantic solution
to the requested result-type instance, and establish safety directly from the
raw certificate.  They do not inspect a completed evaluator result.
-/

namespace TypePM.Runtime

/-- A finite logical-index requirement for each newest-first environment
position. -/
abbrev FuelDemand := Nat → Nat

namespace FuelDemand

def zero : FuelDemand := fun _ => 0

def max (left right : FuelDemand) : FuelDemand :=
  fun position => Nat.max (left position) (right position)

def single (selected logicalIndex : Nat) : FuelDemand :=
  fun position => if position = selected then logicalIndex else 0

def Le (smaller larger : FuelDemand) : Prop :=
  ∀ position, smaller position ≤ larger position

theorem left_le_max : Le left (max left right) :=
  fun _ => Nat.le_max_left _ _

theorem right_le_max : Le right (max left right) :=
  fun _ => Nat.le_max_right _ _

end FuelDemand

/-- Source-scheme safety with a separate finite index at each runtime
environment position. -/
def SchemeDemandEnvironmentSafe (demand : FuelDemand) (solution : Subst)
    (values : List Value) (context : Source.Context) : Prop :=
  values.length = context.length ∧
    ∀ (position : Nat) (scheme : Source.Scheme) (value : Value),
      context[position]? = some scheme →
      values[position]? = some value →
      SchemeFuelValueSafe (demand position) value scheme solution

namespace SchemeDemandEnvironmentSafe

theorem mono
    (safe : SchemeDemandEnvironmentSafe larger solution values context)
    (smallerLe : FuelDemand.Le smaller larger) :
    SchemeDemandEnvironmentSafe smaller solution values context := by
  refine ⟨safe.1, ?_⟩
  intro position scheme value schemeFound valueFound
  exact (safe.2 position scheme value schemeFound valueFound).mono
    (smallerLe position)

/-- Demands outside the finite source context are observationally irrelevant. -/
theorem congr
    (safe : SchemeDemandEnvironmentSafe first solution values context)
    (agree : ∀ position, position < context.length →
      first position = second position) :
    SchemeDemandEnvironmentSafe second solution values context := by
  refine ⟨safe.1, ?_⟩
  intro position scheme value schemeFound valueFound
  have inBounds : position < context.length :=
    (List.getElem?_eq_some_iff.mp schemeFound).1
  rw [← agree position inBounds]
  exact safe.2 position scheme value schemeFound valueFound

theorem lookup
    (safe : SchemeDemandEnvironmentSafe demand solution values context)
    (schemeFound : context[position]? = some scheme) :
    ∃ value,
      values[position]? = some value ∧
        SchemeFuelValueSafe (demand position) value scheme solution := by
  have positionLt : position < context.length :=
    (List.getElem?_eq_some_iff.mp schemeFound).1
  have valueLt : position < values.length := by
    simpa [safe.1] using positionLt
  let value := values[position]'valueLt
  have valueFound : values[position]? = some value :=
    List.getElem?_eq_getElem valueLt
  exact ⟨value, valueFound,
    safe.2 position scheme value schemeFound valueFound⟩

theorem lookupValue
    (safe : SchemeDemandEnvironmentSafe demand solution values context)
    (schemeFound : context[position]? = some scheme)
    (valueFound : values[position]? = some value) :
    SchemeFuelValueSafe (demand position) value scheme solution := by
  obtain ⟨foundValue, found, valueSafe⟩ := safe.lookup schemeFound
  rw [valueFound] at found
  cases found
  exact valueSafe

theorem nil (demand : FuelDemand) (solution : Subst) :
    SchemeDemandEnvironmentSafe demand solution [] [] := by
  constructor
  · rfl
  · intro position scheme value schemeFound
    simp at schemeFound

theorem cons
    (head : SchemeFuelValueSafe headDemand value scheme solution)
    (tail : SchemeDemandEnvironmentSafe tailDemand solution values context) :
    SchemeDemandEnvironmentSafe
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

end SchemeDemandEnvironmentSafe

/-- Timeout or a completed heterogeneous value list safe at one requested
logical index. -/
def FuelEnvironmentResultSafe (index : Nat) (targets : List Ty)
    (result : FuelResult (List Value)) : Prop :=
  result = .timeout ∨
    ∃ values,
      result = .ok values ∧ FuelEnvironmentSafe index values targets

end TypePM.Runtime

namespace TypePM.Source.M4

open TypePM.Runtime

/-- A proof-producing runtime certificate for one exact raw M4 expression
derivation.  `inputDemand` cannot depend on the later semantic solution. -/
structure RawFuelCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expression : Expr} {supply next : Supply}
    {generated : Generated}
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next) : Type where
  inputDemand : Nat → Nat → FuelDemand
  preserves : ∀ solution,
    generated.SemanticSolution solution →
      ∀ operationalFuel resultIndex environment,
        SchemeDemandEnvironmentSafe
            (inputDemand operationalFuel resultIndex)
            solution environment context →
          FuelResultSafe resultIndex (generated.target.apply solution)
            (evalFuel operationalFuel environment expression)

/-- Mutual list companion used by raw tuple elaboration. -/
structure RawItemsFuelCertificate
    {signature : FrozenSignature} {staticFuel : Nat}
    {context : Context} {expressions : List Expr} {supply next : Supply}
    {generated : GeneratedItems}
    (elaboration : ItemsElaborateUsing (ElaboratesFuel signature staticFuel)
      context expressions supply generated next) : Type where
  inputDemand : Nat → Nat → FuelDemand
  preserves : ∀ solution,
    TypePM.Runtime.GeneratedItems.SemanticSolution generated solution →
      ∀ operationalFuel resultIndex environment,
        SchemeDemandEnvironmentSafe
            (inputDemand operationalFuel resultIndex)
            solution environment context →
          FuelEnvironmentResultSafe resultIndex
            (Ty.applyList solution generated.targets)
            (FuelResult.traverse (evalFuel operationalFuel environment)
              expressions)

namespace RawFuelCertificate

def varWitness
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next) :
    RawFuelCertificate elaboration := by
  let demand : Nat → Nat → FuelDemand :=
    fun _ resultIndex => FuelDemand.single position resultIndex
  refine ⟨demand, ?_⟩
  intro solution _semantic operationalFuel resultIndex environment
    environmentSafe
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨scheme, schemeFound, generatedEq, _nextEq⟩ := elaboration
  obtain ⟨value, valueFound, valueSafe⟩ := environmentSafe.lookup schemeFound
  have selected : demand operationalFuel resultIndex position = resultIndex := by
    simp [demand, FuelDemand.single]
  rw [selected] at valueSafe
  rw [generatedEq]
  simpa [FuelResultSafe, FuelResultSafeWith] using
    (evalFuel_var_resultSafeWith valueFound (valueSafe supply)
      operationalFuel)

/-- The variable witness requires exactly the requested result index at the
selected source-context position and zero at every other position. -/
theorem varWitness_inputDemand
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next)
    (operationalFuel resultIndex : Nat) :
    (varWitness elaboration).inputDemand operationalFuel resultIndex =
      FuelDemand.single position resultIndex := by
  rfl

@[simp] theorem varWitness_inputDemand_selected
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next)
    (operationalFuel resultIndex : Nat) :
    (varWitness elaboration).inputDemand operationalFuel resultIndex
        position = resultIndex := by
  rw [varWitness_inputDemand]
  simp [FuelDemand.single]

@[simp] theorem varWitness_inputDemand_other
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next)
    (operationalFuel resultIndex otherPosition : Nat)
    (different : otherPosition ≠ position) :
    (varWitness elaboration).inputDemand operationalFuel resultIndex
        otherPosition = 0 := by
  rw [varWitness_inputDemand]
  simp [FuelDemand.single, different]

theorem var
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.var position) supply generated next) :
    Nonempty (RawFuelCertificate elaboration) :=
  ⟨varWitness elaboration⟩

theorem lit
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.lit literal) supply generated next) :
    Nonempty (RawFuelCertificate elaboration) := by
  let demand : Nat → Nat → FuelDemand := fun _ _ => FuelDemand.zero
  refine ⟨⟨demand, ?_⟩⟩
  intro solution _semantic operationalFuel resultIndex environment
    _environmentSafe
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedEq, _nextEq⟩ := elaboration
  rw [generatedEq]
  cases operationalFuel with
  | zero => exact .inl rfl
  | succ _ =>
      exact .inr ⟨.int literal, rfl, fuelValueSafe_int literal resultIndex⟩

theorem something
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      .something supply generated next) :
    Nonempty (RawFuelCertificate elaboration) := by
  let demand : Nat → Nat → FuelDemand := fun _ _ => FuelDemand.zero
  refine ⟨⟨demand, ?_⟩⟩
  intro solution _semantic operationalFuel resultIndex environment
    _environmentSafe
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedEq, _nextEq⟩ := elaboration
  rw [generatedEq]
  cases operationalFuel with
  | zero => exact .inl rfl
  | succ _ =>
      exact .inr ⟨.something, rfl, by
        simpa [Ty.apply, Cap.apply] using
          fuelValueSafe_something ((Ty.var ⟨supply.ty⟩).apply solution)
            resultIndex⟩

end RawFuelCertificate

namespace RawItemsFuelCertificate

theorem nil
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context [] supply generated next) :
    Nonempty (RawItemsFuelCertificate elaboration) := by
  cases elaboration
  let demand : Nat → Nat → FuelDemand := fun _ _ => FuelDemand.zero
  refine ⟨⟨demand, ?_⟩⟩
  intro solution _semantic operationalFuel resultIndex environment
    _environmentSafe
  exact .inr ⟨[], by simp [FuelResult.traverse], FuelEnvironmentSafe.nil _⟩

theorem cons
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context (expression :: expressions)
      supply generated next)
    (headCertificate : ∀ generatedHead afterHead,
      ∀ headElaboration : ElaboratesFuel signature staticFuel context
        expression supply generatedHead afterHead,
        Nonempty (RawFuelCertificate headElaboration))
    (tailCertificate : ∀ afterHead generatedTail,
      ∀ tailElaboration : ItemsElaborateUsing
        (ElaboratesFuel signature staticFuel) context expressions afterHead
        generatedTail next,
        Nonempty (RawItemsFuelCertificate tailElaboration)) :
    Nonempty (RawItemsFuelCertificate elaboration) := by
  cases elaboration with
  | @cons _ _ _ generatedHead afterHead generatedTail _ headElaboration
      tailElaboration =>
      obtain ⟨headCertificate⟩ :=
        headCertificate generatedHead afterHead headElaboration
      obtain ⟨tailCertificate⟩ :=
        tailCertificate afterHead generatedTail tailElaboration
      let demand : Nat → Nat → FuelDemand :=
        fun operationalFuel resultIndex =>
          FuelDemand.max
            (headCertificate.inputDemand operationalFuel resultIndex)
            (tailCertificate.inputDemand operationalFuel resultIndex)
      refine ⟨⟨demand, ?_⟩⟩
      intro solution semantic operationalFuel resultIndex environment
        environmentSafe
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
        (FuelDemand.left_le_max
          (left := headCertificate.inputDemand operationalFuel resultIndex)
          (right := tailCertificate.inputDemand operationalFuel resultIndex))
      have tailEnvironmentSafe := environmentSafe.mono
        (FuelDemand.right_le_max
          (left := headCertificate.inputDemand operationalFuel resultIndex)
          (right := tailCertificate.inputDemand operationalFuel resultIndex))
      rcases headCertificate.preserves solution headSemantic operationalFuel
          resultIndex environment headEnvironmentSafe with headTimeout |
          ⟨headValue, headOk, headSafe⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · rcases tailCertificate.preserves solution tailSemantic
            operationalFuel resultIndex environment tailEnvironmentSafe with
            tailTimeout | ⟨tailValues, tailOk, tailSafe⟩
        · exact .inl (by
            simp [FuelResult.traverse, headOk, tailTimeout, FuelResult.bind,
              FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headOk, tailOk, FuelResult.bind,
              FuelResult.map], by
            simpa [Ty.applyList] using
              FuelEnvironmentSafe.cons headSafe tailSafe⟩

end RawItemsFuelCertificate

namespace RawFuelCertificate

theorem tuple
    (elaboration : ElaboratesFuel signature (staticFuel + 1) context
      (.tuple expressions) supply generated next)
    (itemsCertificate : ∀ generatedItems,
      ∀ itemsElaboration : ItemsElaborateUsing
        (ElaboratesFuel signature staticFuel) context expressions supply
        generatedItems next,
        Nonempty (RawItemsFuelCertificate itemsElaboration)) :
    Nonempty (RawFuelCertificate elaboration) := by
  simp only [ElaboratesFuel] at elaboration
  obtain ⟨generatedItems, itemsElaboration, generatedEq⟩ := elaboration
  obtain ⟨itemsCertificate⟩ :=
    itemsCertificate generatedItems itemsElaboration
  let demand : Nat → Nat → FuelDemand
    | 0, _ => FuelDemand.zero
    | operationalFuel + 1, resultIndex =>
        itemsCertificate.inputDemand operationalFuel resultIndex
  refine ⟨⟨demand, ?_⟩⟩
  intro solution semantic operationalFuel resultIndex environment
    environmentSafe
  have itemsSemantic :
      TypePM.Runtime.GeneratedItems.SemanticSolution generatedItems
        solution := by
    rw [generatedEq] at semantic
    exact semantic
  cases operationalFuel with
  | zero => exact .inl rfl
  | succ childFuel =>
      rw [generatedEq]
      rcases itemsCertificate.preserves solution itemsSemantic childFuel
          resultIndex environment environmentSafe with timeout |
          ⟨values, success, valuesSafe⟩
      · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
      · exact .inr ⟨.tuple values, by
          simp [evalFuel, success, FuelResult.map], by
          simpa [Ty.apply] using
            fuelValueSafe_tuple_of_environment resultIndex values
              (Ty.applyList solution generatedItems.targets) valuesSafe⟩

end RawFuelCertificate

mutual

  /-- Syntax-wide scope completed by the raw finite-demand induction. -/
  inductive RawFiniteDemandSupported : Expr → Prop where
    | var : RawFiniteDemandSupported (.var position)
    | lit : RawFiniteDemandSupported (.lit literal)
    | something : RawFiniteDemandSupported .something
    | tuple
        (items : RawFiniteDemandSupporteds expressions) :
        RawFiniteDemandSupported (.tuple expressions)

  /-- List companion for nested tuple fields. -/
  inductive RawFiniteDemandSupporteds : List Expr → Prop where
    | nil : RawFiniteDemandSupporteds []
    | cons
        (head : RawFiniteDemandSupported expression)
        (tail : RawFiniteDemandSupporteds expressions) :
        RawFiniteDemandSupporteds (expression :: expressions)

end

mutual

theorem RawFiniteDemandSupported.certificate
    (supported : RawFiniteDemandSupported expression)
    (elaboration : ElaboratesFuel signature staticFuel context expression
      supply generated next) :
    Nonempty (RawFuelCertificate elaboration) := by
  cases supported with
  | var =>
      cases staticFuel with
      | zero => simp [ElaboratesFuel] at elaboration
      | succ staticFuel => exact RawFuelCertificate.var elaboration
  | lit =>
      cases staticFuel with
      | zero => simp [ElaboratesFuel] at elaboration
      | succ staticFuel => exact RawFuelCertificate.lit elaboration
  | something =>
      cases staticFuel with
      | zero => simp [ElaboratesFuel] at elaboration
      | succ staticFuel => exact RawFuelCertificate.something elaboration
  | @tuple expressions items =>
      cases staticFuel with
      | zero => simp [ElaboratesFuel] at elaboration
      | succ staticFuel =>
          apply RawFuelCertificate.tuple elaboration
          intro generatedItems itemsElaboration
          exact items.certificate itemsElaboration

theorem RawFiniteDemandSupporteds.certificate
    (supported : RawFiniteDemandSupporteds expressions)
    (elaboration : ItemsElaborateUsing
      (ElaboratesFuel signature staticFuel) context expressions supply
      generated next) :
    Nonempty (RawItemsFuelCertificate elaboration) := by
  cases supported with
  | nil => exact RawItemsFuelCertificate.nil elaboration
  | @cons expression expressions head tail =>
      apply RawItemsFuelCertificate.cons elaboration
      · intro generatedHead afterHead headElaboration
        exact head.certificate headElaboration
      · intro afterHead generatedTail tailElaboration
        exact tail.certificate tailElaboration

end

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

/-- Every closed expression in the raw finite-demand scope is safe at every
evaluator fuel and requested logical result index.  The proof opens the
principal raw derivation stored by `M4.Typing`; no completed evaluation
equation is assumed. -/
theorem RawFiniteDemandSupported.closedFuelResultSafe
    (supported : RawFiniteDemandSupported expression)
    (typing : Typing signature [] expression target)
    (operationalFuel resultIndex : Nat) :
    FuelResultSafe resultIndex target
      (evalFuel operationalFuel [] expression) := by
  rcases typing with
    ⟨principal, ⟨derivation⟩, later, targetEquality⟩
  rcases derivation.elaboration with ⟨staticFuel, elaboration⟩
  obtain ⟨certificate⟩ := supported.certificate elaboration
  let solution := Subst.compose later derivation.closure.substitution
  have semantic : derivation.generated.SemanticSolution solution :=
    semanticSolution_postcompose
      (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
        derivation.closure)
      later
  have safe := certificate.preserves solution semantic operationalFuel
    resultIndex []
    (SchemeDemandEnvironmentSafe.nil
      (certificate.inputDemand operationalFuel resultIndex) solution)
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

/-- Closed raw finite-demand expressions never evaluate to `stuck`, at any
evaluator fuel. -/
theorem RawFiniteDemandSupported.closedNeverStuck
    (supported : RawFiniteDemandSupported expression)
    (typing : Typing signature [] expression target)
    (operationalFuel : Nat) :
    (evalFuel operationalFuel [] expression).NotStuck :=
  (supported.closedFuelResultSafe typing operationalFuel 0).notStuck

end TypePM.Source.M4
