import TypePM.StepIndexedClosureSafety
import TypePM.Runtime.EvaluationStuckMonotonicity

/-!
# Structural source-origin demands for runtime values

The existing `FuelValueSafe` relation uses one logical index for a function,
its argument, its result, and the operational fuel of the call.  A source
lambda needs more information.  In particular, a higher-order argument or
result may itself need a future call contract rather than one uniform fuel
index.

`OriginDemand` is a finite observation tree.  A call node records its
operational fuel and structurally smaller demands for its argument and
result.  `PlainCallValueSafe` is a nonrecursive, strictly positive call layer;
`OriginValueSafe` interprets the finite tree by structural recursion.  This
keeps higher-order occurrences positive without changing `FuelValueSafe`.

This module contains only the evaluator-facing relation and its application
laws.  Source elaboration bridges live in higher modules.  The relation
currently covers plain closures; recursive closures, matcher calls, and
search-specific observations require separate demand nodes and safety laws.
-/

namespace TypePM.Runtime

/-- A convenient numeric view of a call whose argument and result demands
are ordinary fuel leaves. -/
structure PlainCallDemand where
  operationalFuel : Nat
  argumentIndex : Nat
  resultIndex : Nat

namespace PlainCallDemand

/-- Safe weakening of a fuel-leaf call: run no longer, assume a stronger
argument, and request a weaker result observation. -/
structure Le (requested available : PlainCallDemand) : Prop where
  operational : requested.operationalFuel ≤ available.operationalFuel
  argument : available.argumentIndex ≤ requested.argumentIndex
  result : requested.resultIndex ≤ available.resultIndex

theorem Le.refl (call : PlainCallDemand) : call.Le call :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem Le.trans
    {requested middle available : PlainCallDemand}
    (first : requested.Le middle) (second : middle.Le available) :
    requested.Le available :=
  ⟨Nat.le_trans first.operational second.operational,
    Nat.le_trans second.argument first.argument,
    Nat.le_trans first.result second.result⟩

end PlainCallDemand

/-- A finite tree of observations requested from a runtime value. -/
inductive OriginDemand where
  | none
  | fuel (index : Nat)
  | both (left right : OriginDemand)
  /-- Observe every element of one canonical runtime list. -/
  | listOf (element : OriginDemand)
  /-- Observe both fields of one binary runtime tuple. -/
  | pairOf (left right : OriginDemand)
  /-- Observe one canonical Boolean constructor. -/
  | bool
  /-- Observe one canonical integer value. -/
  | int
  | plainCall (operationalFuel : Nat)
      (argument result : OriginDemand)

/-- One finite structural observation demand per newest-first runtime
environment position.  Keeping this runtime-level definition independent of
source schemes lets expression evaluation and matching callbacks share the
same demand language. -/
abbrev OriginEnvironmentDemand := Nat → OriginDemand

namespace OriginEnvironmentDemand

def none : OriginEnvironmentDemand := fun _ => .none

def both (left right : OriginEnvironmentDemand) : OriginEnvironmentDemand :=
  fun position => .both (left position) (right position)

/-- Embed an ordinary numeric demand at every environment position. -/
def fuel (demand : Nat → Nat) : OriginEnvironmentDemand :=
  fun position => .fuel (demand position)

/-- Drop the newest environment entry. -/
def tail (demand : OriginEnvironmentDemand) : OriginEnvironmentDemand :=
  fun position => demand (position + 1)

def single (selected : Nat) (demand : OriginDemand) :
    OriginEnvironmentDemand :=
  fun position => if position = selected then demand else .none

end OriginEnvironmentDemand

namespace PlainCallDemand

/-- Embed the numeric convenience view into the structural demand tree. -/
def toOriginDemand (call : PlainCallDemand) : OriginDemand :=
  .plainCall call.operationalFuel (.fuel call.argumentIndex)
    (.fuel call.resultIndex)

end PlainCallDemand

namespace OriginDemand

/-- Semantic weakening.  Function arguments are contravariant; call fuel
and results are covariant, while `both` can be introduced or projected. -/
inductive Le : OriginDemand → OriginDemand → Prop where
  | none : Le .none available
  | fuel (indexLe : requested ≤ available) :
      Le (.fuel requested) (.fuel available)
  | both
      (left : Le requestedLeft availableLeft)
      (right : Le requestedRight availableRight) :
      Le (.both requestedLeft requestedRight)
        (.both availableLeft availableRight)
  | fromLeft
      (selected : Le requested availableLeft) :
      Le requested (.both availableLeft availableRight)
  | fromRight
      (selected : Le requested availableRight) :
      Le requested (.both availableLeft availableRight)
  | bothIntro
      (left : Le requestedLeft available)
      (right : Le requestedRight available) :
      Le (.both requestedLeft requestedRight) available
  | listOf (element : Le requestedElement availableElement) :
      Le (.listOf requestedElement) (.listOf availableElement)
  | pairOf
      (left : Le requestedLeft availableLeft)
      (right : Le requestedRight availableRight) :
      Le (.pairOf requestedLeft requestedRight)
        (.pairOf availableLeft availableRight)
  | bool : Le .bool .bool
  | int : Le .int .int
  | plainCall
      (operational : requestedFuel ≤ availableFuel)
      (argument : Le availableArgument requestedArgument)
      (result : Le requestedResult availableResult) :
      Le (.plainCall requestedFuel requestedArgument requestedResult)
        (.plainCall availableFuel availableArgument availableResult)

def Le.refl : ∀ demand, Le demand demand
  | .none => .none
  | .fuel _ => .fuel (Nat.le_refl _)
  | .both left right => .both (Le.refl left) (Le.refl right)
  | .listOf element => .listOf (Le.refl element)
  | .pairOf left right => .pairOf (Le.refl left) (Le.refl right)
  | .bool => .bool
  | .int => .int
  | .plainCall _ argument result =>
      .plainCall (Nat.le_refl _) (Le.refl argument) (Le.refl result)

end OriginDemand

/-- A nonrecursive, strictly positive call layer.  The two predicates have
already been fixed to smaller demand trees by `OriginValueSafe`. -/
inductive PlainCallValueSafe
    (argumentSafe resultSafe : Value → Ty → Prop) :
    Nat → Value → Ty → Prop where
  | zero : PlainCallValueSafe argumentSafe resultSafe 0 value
      (.fn domain codomain)
  | closure
      (bodySafe : ∀ argument,
        argumentSafe argument domain →
          evalFuel bodyFuel (argument :: environment) body = .timeout ∨
            ∃ result,
              evalFuel bodyFuel (argument :: environment) body = .ok result ∧
                resultSafe result codomain) :
      PlainCallValueSafe argumentSafe resultSafe (bodyFuel + 1)
        (Value.plainClosure environment body) (.fn domain codomain)
  | recursiveClosure
      (environmentTyped : TotalEnvironmentTyping environment context)
      (bodyTyped : TotalRecursiveClosureBodyTyping
        (domain :: .fn domain codomain :: context) body codomain)
      (bodySafe : ∀ argument,
        argumentSafe argument domain →
          evalFuel bodyFuel
              (argument :: Value.recursiveClosure environment body ::
                environment)
              body = .timeout ∨
            ∃ result,
              evalFuel bodyFuel
                  (argument :: Value.recursiveClosure environment body ::
                    environment)
                  body = .ok result ∧
                resultSafe result codomain) :
      PlainCallValueSafe argumentSafe resultSafe (bodyFuel + 1)
        (Value.recursiveClosure environment body) (.fn domain codomain)

/-- A strictly positive list layer.  The element predicate has already been
fixed to the structurally smaller child demand. -/
inductive ListOfValueSafe (elementSafe : Value → Ty → Prop) :
    Value → Ty → Prop where
  | nil : ListOfValueSafe elementSafe (Value.buildList [])
      (DataTypes.list elementType)
  | cons
      (head : elementSafe value elementType)
      (tail : ListOfValueSafe elementSafe (Value.buildList values)
        (DataTypes.list elementType)) :
      ListOfValueSafe elementSafe (Value.buildList (value :: values))
        (DataTypes.list elementType)

namespace ListOfValueSafe

theorem existsViewList
    (safe : ListOfValueSafe elementSafe value target) :
    ∃ values, Value.viewList value = some values := by
  cases safe with
  | nil => exact ⟨[], Value.viewList_buildList []⟩
  | @cons value elementType values head tail =>
      exact ⟨value :: values, Value.viewList_buildList _⟩

theorem deleteFirstStructural
    (safe : ListOfValueSafe elementSafe value target)
    (encoding : Value.viewList value = some values) (needle : Value) :
    ListOfValueSafe elementSafe
      (Value.buildList (Value.deleteFirstStructural needle values)) target := by
  induction safe generalizing values with
  | nil =>
      have valuesEq : values = [] := by
        simpa using encoding.symm
      subst values
      exact .nil
  | @cons value elementType storedValues head tail tailIH =>
      have valuesEq : values = value :: storedValues := by
        simpa using encoding.symm
      subst values
      simp only [Value.deleteFirstStructural]
      split
      · exact tail
      · exact .cons head
          (tailIH (Value.viewList_buildList storedValues))

/-- Re-encode a structurally safe list using an observed host-list view. -/
theorem ofView
    (safe : ListOfValueSafe elementSafe value target)
    (encoding : Value.viewList value = some values) :
    ListOfValueSafe elementSafe (Value.buildList values) target := by
  induction safe generalizing values with
  | nil =>
      have valuesEq : values = [] := by simpa using encoding.symm
      subst values
      exact .nil
  | @cons value elementType storedValues head tail tailIH =>
      have valuesEq : values = value :: storedValues := by
        simpa using encoding.symm
      subst values
      exact .cons head (tailIH (Value.viewList_buildList storedValues))

/-- Concatenating two observed canonical runtime lists preserves the same
element predicate without comparing their elements. -/
theorem appendStructural
    (left : ListOfValueSafe elementSafe leftValue target)
    (leftView : Value.viewList leftValue = some leftValues)
    (right : ListOfValueSafe elementSafe rightValue target)
    (rightView : Value.viewList rightValue = some rightValues) :
    ListOfValueSafe elementSafe
      (Value.buildList (leftValues ++ rightValues)) target := by
  induction left generalizing leftValues with
  | nil =>
      have leftValuesEq : leftValues = [] := by
        simpa using leftView.symm
      subst leftValues
      simpa using right.ofView rightView
  | @cons value elementType storedValues head tail tailIH =>
      have leftValuesEq : leftValues = value :: storedValues := by
        simpa using leftView.symm
      subst leftValues
      exact .cons head
        (tailIH (Value.viewList_buildList storedValues) right)

/-- Build-list specialization of `appendStructural`. -/
theorem append
    (left : ListOfValueSafe elementSafe (Value.buildList leftValues) target)
    (right : ListOfValueSafe elementSafe (Value.buildList rightValues) target) :
    ListOfValueSafe elementSafe
      (Value.buildList (leftValues ++ rightValues)) target :=
  left.appendStructural (Value.viewList_buildList leftValues) right
    (Value.viewList_buildList rightValues)

end ListOfValueSafe

/-- Compose two normalized checking conversions.  Special conversions now
end directly at a matcher slot, so only an ordinary second step is possible. -/
theorem CheckConversion.trans
    (first : CheckConversion firstClass source middle)
    (second : CheckConversion secondClass middle target) :
    ∃ finalClass, CheckConversion finalClass source target := by
  cases first with
  | ordinary => exact ⟨_, second⟩
  | matcherToSlot demand =>
      cases second
      exact ⟨_, .matcherToSlot demand⟩
  | @productMatcherToSlot duals consumer nonempty demand =>
      cases second
      exact ⟨_, .productMatcherToSlot nonempty demand⟩

/-- A strictly positive binary-product layer.  Retaining the normalized
conversion from the ordinary product source makes the observation stable
under product-matcher and slot checking conversions. -/
inductive PairOfValueSafe
    (leftSafe rightSafe : Value → Ty → Prop) : Value → Ty → Prop where
  | pair
      (left : leftSafe leftValue leftType)
      (right : rightSafe rightValue rightType)
      (conversion : CheckConversion conversionClass
        (.prod [leftType, rightType]) target) :
      PairOfValueSafe leftSafe rightSafe
        (.tuple [leftValue, rightValue]) target

/-- Canonical Boolean values, retaining which constructor occurred. -/
inductive BoolValueSafe : Value → Ty → Prop where
  | true : BoolValueSafe (.data DataCtor.true []) DataTypes.bool
  | false : BoolValueSafe (.data DataCtor.false []) DataTypes.bool

/-- Canonical integer values. -/
inductive IntValueSafe : Value → Ty → Prop where
  | int : IntValueSafe (.int value) .int

/-- Interpret a finite source-origin observation tree.  The recursive calls
in the call case are on the two strict subtrees. -/
def OriginValueSafe : OriginDemand → Value → Ty → Prop
  | .none, _, _ => True
  | .fuel index, value, target => FuelValueSafe index value target
  | .both left right, value, target =>
      OriginValueSafe left value target ∧ OriginValueSafe right value target
  | .listOf element, value, target =>
      ListOfValueSafe
        (fun item itemType => OriginValueSafe element item itemType)
        value target
  | .pairOf left right, value, target =>
      PairOfValueSafe
        (fun item itemType => OriginValueSafe left item itemType)
        (fun item itemType => OriginValueSafe right item itemType)
        value target
  | .bool, value, target => BoolValueSafe value target
  | .int, value, target => IntValueSafe value target
  | .plainCall operationalFuel argumentDemand resultDemand, value, target =>
      PlainCallValueSafe
        (fun argument domain => OriginValueSafe argumentDemand argument domain)
        (fun result codomain => OriginValueSafe resultDemand result codomain)
        operationalFuel value target
termination_by demand => demand

/-- Pointwise interpretation of a demand list over runtime argument values
and the corresponding solved domain types. -/
inductive OriginValueSafes : List OriginDemand → List Value → List Ty → Prop where
  | nil : OriginValueSafes [] [] []
  | cons
      (head : OriginValueSafe demand value target)
      (tail : OriginValueSafes demands values targets) :
      OriginValueSafes (demand :: demands) (value :: values)
        (target :: targets)

/-- Timeout or a value satisfying one finite source-origin demand. -/
def OriginResultSafe (demand : OriginDemand) (target : Ty)
    (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧ OriginValueSafe demand value target

/-- Pointwise structural safety for a monomorphic runtime environment. -/
def OriginEnvironmentSafe (demand : OriginEnvironmentDemand)
    (values : ValueEnvironment) (targets : List Ty) : Prop :=
  values.length = targets.length ∧
    ∀ (position : Nat) (target : Ty) (value : Value),
      targets[position]? = some target →
      values[position]? = some value →
      OriginValueSafe (demand position) value target

/-- Static data supplied for one embedded evaluation request.  Binding types
and the outer environment remain separate even though the embedded evaluator
observes their concatenation. -/
abbrev FuelEmbeddedExpressionCertificateFamily :=
  Nat → List Ty → List Ty → Source.Expr → Ty →
    OriginDemand → OriginEnvironmentDemand → Prop

/-- Demand-indexed evaluator contract used at the expression/search boundary.
The certificate chooses the finite input and output observations before the
runtime values are supplied.  The contract then closes the callback over the
actual `bindings ++ environment`, exactly matching embedded expression
evaluation inside value patterns and user-matcher clauses. -/
def FuelEmbeddedEvaluatorSafe
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (evaluate : Nat → ValueEnvironment → Source.Expr → FuelResult Value) :
    Prop :=
  ∀ {operationalFuel bindingTypes environmentTypes expression target
      outputDemand inputDemand bindings environment},
    Certificate operationalFuel bindingTypes environmentTypes expression
        target outputDemand inputDemand →
      OriginEnvironmentSafe inputDemand (bindings ++ environment)
        (bindingTypes ++ environmentTypes) →
        OriginResultSafe outputDemand target
          (evaluate operationalFuel (bindings ++ environment) expression)

namespace OriginEnvironmentSafe

theorem nil (demand : OriginEnvironmentDemand) :
    OriginEnvironmentSafe demand [] [] := by
  constructor
  · rfl
  · intro position target value targetFound
    simp at targetFound

end OriginEnvironmentSafe

namespace OriginResultSafe

theorem notStuck
    (safe : OriginResultSafe demand target result) : result.NotStuck := by
  rcases safe with timeout | ⟨value, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

theorem ofFuel
    (safe : FuelResultSafe index target result) :
    OriginResultSafe (.fuel index) target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have originSafe : OriginValueSafe (.fuel index) value target := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, originSafe⟩

theorem toFuel
    (safe : OriginResultSafe (.fuel index) target result) :
    FuelResultSafe index target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have fuelSafe : FuelValueSafe index value target := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, fuelSafe⟩

theorem bothLeft
    (safe : OriginResultSafe (.both left right) target result) :
    OriginResultSafe left target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have unfolded : OriginValueSafe left value target ∧
        OriginValueSafe right value target := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, unfolded.1⟩

theorem bothRight
    (safe : OriginResultSafe (.both left right) target result) :
    OriginResultSafe right target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · have unfolded : OriginValueSafe left value target ∧
        OriginValueSafe right value target := by
      simpa only [OriginValueSafe] using valueSafe
    exact .inr ⟨value, success, unfolded.2⟩

end OriginResultSafe

namespace OriginValueSafe

theorem ofFuel
    (safe : FuelValueSafe index value target) :
    OriginValueSafe (.fuel index) value target := by
  simpa only [OriginValueSafe]

theorem toFuel
    (safe : OriginValueSafe (.fuel index) value target) :
    FuelValueSafe index value target := by
  simpa only [OriginValueSafe] using safe

theorem both
    (left : OriginValueSafe leftDemand value target)
    (right : OriginValueSafe rightDemand value target) :
    OriginValueSafe (.both leftDemand rightDemand) value target := by
  simpa only [OriginValueSafe] using And.intro left right

theorem bothLeft
    (safe : OriginValueSafe (.both left right) value target) :
    OriginValueSafe left value target := by
  have unfolded : OriginValueSafe left value target ∧
      OriginValueSafe right value target := by
    simpa only [OriginValueSafe] using safe
  exact unfolded.1

theorem bothRight
    (safe : OriginValueSafe (.both left right) value target) :
    OriginValueSafe right value target := by
  have unfolded : OriginValueSafe left value target ∧
      OriginValueSafe right value target := by
    simpa only [OriginValueSafe] using safe
  exact unfolded.2

theorem listNil :
    OriginValueSafe (.listOf elementDemand) (Value.buildList [])
      (DataTypes.list elementType) := by
  simp only [OriginValueSafe]
  exact .nil

theorem listCons
    (head : OriginValueSafe elementDemand value elementType)
    (tail : OriginValueSafe (.listOf elementDemand)
      (Value.buildList values) (DataTypes.list elementType)) :
    OriginValueSafe (.listOf elementDemand)
      (Value.buildList (value :: values)) (DataTypes.list elementType) := by
  simp only [OriginValueSafe] at tail ⊢
  exact .cons head tail

theorem pair
    (left : OriginValueSafe leftDemand leftValue leftType)
    (right : OriginValueSafe rightDemand rightValue rightType) :
    OriginValueSafe (.pairOf leftDemand rightDemand)
      (.tuple [leftValue, rightValue]) (.prod [leftType, rightType]) := by
  simp only [OriginValueSafe]
  exact .pair left right .ordinary

theorem boolTrue :
    OriginValueSafe .bool (.data DataCtor.true []) DataTypes.bool := by
  simp only [OriginValueSafe]
  exact .true

theorem boolFalse :
    OriginValueSafe .bool (.data DataCtor.false []) DataTypes.bool := by
  simp only [OriginValueSafe]
  exact .false

theorem boolValue (value : Bool) :
    OriginValueSafe .bool (Value.boolValue value) DataTypes.bool := by
  cases value <;> simp [Value.boolValue, boolTrue, boolFalse]

theorem int (value : Int) :
    OriginValueSafe .int (.int value) .int := by
  simp only [OriginValueSafe]
  exact .int

/-- Construct the exact structural call contract of one plain closure. -/
theorem plainClosure
    (bodySafe : ∀ argument,
      OriginValueSafe argumentDemand argument domain →
        OriginResultSafe resultDemand codomain
          (evalFuel bodyFuel (argument :: environment) body)) :
    OriginValueSafe
      (.plainCall (bodyFuel + 1) argumentDemand resultDemand)
      (Value.plainClosure environment body) (.fn domain codomain) := by
  simpa only [OriginValueSafe] using PlainCallValueSafe.closure bodySafe

/-- Construct the exact structural call contract of one recursive closure.
The runtime self value is inserted at environment position one. -/
theorem recursiveClosure
    (environmentTyped : TotalEnvironmentTyping environment context)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: context) body codomain)
    (bodySafe : ∀ argument,
      OriginValueSafe argumentDemand argument domain →
        OriginResultSafe resultDemand codomain
          (evalFuel bodyFuel
            (argument :: Value.recursiveClosure environment body :: environment)
            body)) :
    OriginValueSafe
      (.plainCall (bodyFuel + 1) argumentDemand resultDemand)
      (Value.recursiveClosure environment body) (.fn domain codomain) := by
  simpa only [OriginValueSafe] using
    PlainCallValueSafe.recursiveClosure environmentTyped bodyTyped bodySafe

theorem apply
    (functionSafe : OriginValueSafe
      (.plainCall operationalFuel argumentDemand resultDemand)
      functionValue (.fn domain codomain))
    (argumentSafe : OriginValueSafe argumentDemand argumentValue domain) :
    OriginResultSafe resultDemand codomain
      (applyFuel operationalFuel functionValue argumentValue) := by
  simp only [OriginValueSafe] at functionSafe
  cases functionSafe with
  | zero => exact .inl rfl
  | closure bodySafe =>
      change OriginResultSafe _ _ (evalFuel _ (_ :: _) _)
      exact bodySafe argumentValue argumentSafe
  | recursiveClosure _environmentTyped _bodyTyped bodySafe =>
      change OriginResultSafe _ _ (evalFuel _ (_ :: _ :: _) _)
      exact bodySafe argumentValue argumentSafe

private theorem applyFuel_originResultSafe_mono
    (operationalLe : smallerFuel ≤ largerFuel)
    (safe : OriginResultSafe availableDemand target
      (applyFuel largerFuel function argument))
    (valueMono : ∀ value,
      OriginValueSafe availableDemand value target →
        OriginValueSafe requestedDemand value target) :
    OriginResultSafe requestedDemand target
      (applyFuel smallerFuel function argument) := by
  cases actualEq : applyFuel smallerFuel function argument with
  | timeout => exact .inl rfl
  | stuck =>
      have raisedStuck := applyFuel_stuck_of_le operationalLe actualEq
      have contradiction : False := by
        have notStuck := safe.notStuck
        rw [raisedStuck] at notStuck
        exact notStuck
      exact contradiction.elim
  | ok actual =>
      have raisedOk := applyFuel_ok_of_le operationalLe actualEq
      rcases safe with timeout | ⟨value, success, valueSafe⟩
      · rw [raisedOk] at timeout
        contradiction
      · rw [raisedOk] at success
        cases success
        exact .inr ⟨actual, rfl, valueMono actual valueSafe⟩

/-- Structural demand weakening, including argument contravariance and
result covariance at call nodes. -/
theorem mono
    (weaken : OriginDemand.Le requested available)
    (safe : OriginValueSafe available value target) :
    OriginValueSafe requested value target := by
  induction weaken generalizing value target with
  | none => simp only [OriginValueSafe]
  | fuel indexLe =>
      exact OriginValueSafe.ofFuel (safe.toFuel.mono indexLe)
  | both left right leftIH rightIH =>
      exact OriginValueSafe.both
        (leftIH safe.bothLeft) (rightIH safe.bothRight)
  | fromLeft selected selectedIH =>
      exact selectedIH safe.bothLeft
  | fromRight selected selectedIH =>
      exact selectedIH safe.bothRight
  | bothIntro left right leftIH rightIH =>
      exact OriginValueSafe.both (leftIH safe) (rightIH safe)
  | listOf element elementIH =>
      simp only [OriginValueSafe] at safe ⊢
      induction safe with
      | nil => exact .nil
      | cons head tail tailIH => exact .cons (elementIH head) tailIH
  | pairOf left right leftIH rightIH =>
      simp only [OriginValueSafe] at safe ⊢
      cases safe with
      | pair leftSafe rightSafe conversion =>
          exact .pair (leftIH leftSafe) (rightIH rightSafe) conversion
  | bool => exact safe
  | int => exact safe
  | @plainCall requestedFuel availableFuel availableArgument
      requestedArgument requestedResult availableResult operational
      argument result argumentIH resultIH =>
      simp only [OriginValueSafe] at safe ⊢
      cases safe with
      | zero =>
          cases requestedFuel with
          | zero => exact .zero
          | succ _ => omega
      | @closure domain availableBodyFuel environment body codomain bodySafe =>
          cases requestedFuel with
          | zero => exact .zero
          | succ requestedBodyFuel =>
              apply PlainCallValueSafe.closure
              intro actualArgument actualArgumentSafe
              have availableArgumentSafe := argumentIH actualArgumentSafe
              have availableApplication : OriginResultSafe availableResult
                  codomain
                  (applyFuel (availableBodyFuel + 1)
                    (.plainClosure environment body) actualArgument) := by
                change OriginResultSafe availableResult codomain
                  (evalFuel availableBodyFuel
                    (actualArgument :: environment) body)
                exact bodySafe actualArgument availableArgumentSafe
              have lowered := applyFuel_originResultSafe_mono operational
                availableApplication (fun resultValue resultSafe =>
                  resultIH resultSafe)
              change OriginResultSafe requestedResult codomain
                (evalFuel requestedBodyFuel
                  (actualArgument :: environment) body)
              exact lowered
      | @recursiveClosure environment context domain codomain body
          availableBodyFuel environmentTyped bodyTyped bodySafe =>
          cases requestedFuel with
          | zero => exact .zero
          | succ requestedBodyFuel =>
              apply PlainCallValueSafe.recursiveClosure environmentTyped bodyTyped
              intro actualArgument actualArgumentSafe
              have availableArgumentSafe := argumentIH actualArgumentSafe
              have availableApplication : OriginResultSafe availableResult
                  codomain
                  (applyFuel (availableBodyFuel + 1)
                    (.recursiveClosure environment body) actualArgument) := by
                change OriginResultSafe availableResult codomain
                  (evalFuel availableBodyFuel
                    (actualArgument :: .recursiveClosure environment body ::
                      environment)
                    body)
                exact bodySafe actualArgument availableArgumentSafe
              have lowered := applyFuel_originResultSafe_mono operational
                availableApplication (fun resultValue resultSafe =>
                  resultIH resultSafe)
              change OriginResultSafe requestedResult codomain
                (evalFuel requestedBodyFuel
                  (actualArgument :: .recursiveClosure environment body ::
                    environment)
                  body)
              exact lowered

theorem plainCallFuelMono
    {requested available : PlainCallDemand}
    (safe : OriginValueSafe available.toOriginDemand functionValue
      (.fn domain codomain))
    (weaken : PlainCallDemand.Le requested available) :
    OriginValueSafe requested.toOriginDemand functionValue
      (.fn domain codomain) := by
  apply safe.mono
  exact .plainCall weaken.operational (.fuel weaken.argument)
    (.fuel weaken.result)

end OriginValueSafe

namespace OriginResultSafe

theorem mono
    (weaken : OriginDemand.Le requested available)
    (safe : OriginResultSafe available target result) :
    OriginResultSafe requested target result := by
  rcases safe with timeout | ⟨value, success, valueSafe⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, valueSafe.mono weaken⟩

end OriginResultSafe

/-- Exact call-by-value application composition with independent finite
demand trees for the function argument and result. -/
theorem evalFuel_app_origin
    (functionSafe : OriginResultSafe
      (.plainCall childFuel argumentDemand resultDemand)
      (.fn domain codomain)
      (evalFuel childFuel environment functionExpression))
    (argumentSafe : OriginResultSafe argumentDemand domain
      (evalFuel childFuel environment argumentExpression)) :
    OriginResultSafe resultDemand codomain
      (evalFuel (childFuel + 1) environment
        (.app functionExpression argumentExpression)) := by
  rcases functionSafe with functionTimeout |
      ⟨functionValue, functionOk, functionValueSafe⟩
  · exact .inl (by simp [evalFuel, functionTimeout, FuelResult.bind])
  · rcases argumentSafe with argumentTimeout |
        ⟨argumentValue, argumentOk, argumentValueSafe⟩
    · exact .inl (by
        simp [evalFuel, functionOk, argumentTimeout, FuelResult.bind])
    · have applied := functionValueSafe.apply argumentValueSafe
      rcases applied with applicationTimeout |
          ⟨resultValue, applicationOk, resultSafe⟩
      · exact .inl (by
          simp [evalFuel, functionOk, argumentOk, applicationTimeout,
            FuelResult.bind])
      · exact .inr ⟨resultValue, by
          simp [evalFuel, functionOk, argumentOk, applicationOk,
            FuelResult.bind], resultSafe⟩

end TypePM.Runtime
