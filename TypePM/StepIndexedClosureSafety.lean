import TypePM.TotalPlainClosureSafety

/-!
# Fuel-indexed safety for recursive closures

Structural typing alone cannot say that the self value captured by a
recursive closure is safe to call.  The relation below indexes that dynamic
fact by fuel.  Function safety quantifies only over strictly smaller indices;
matcher closures retain a body certificate and an environment safe at the
preceding index.  This makes the recursive self occurrence well founded.
-/

namespace TypePM.Runtime

mutual

  /-- The positive-index layer of the logical relation.  Products and Lists
  recurse pointwise at this same layer.  Function calls and captured matcher
  environments alone use `previous`, the strictly smaller fuel index. -/
  inductive PositiveValueSafe
      (fuel : Nat) (previous : Value → Ty → Prop) : Value → Ty → Prop where
    | int (literal : Int) (lower : previous (.int literal) .int) :
        PositiveValueSafe fuel previous (.int literal) .int
    | boolTrue (lower : previous
        (.data DataCtor.true []) TypePM.DataTypes.bool) :
        PositiveValueSafe fuel previous
        (.data DataCtor.true []) TypePM.DataTypes.bool
    | boolFalse (lower : previous
        (.data DataCtor.false []) TypePM.DataTypes.bool) :
        PositiveValueSafe fuel previous
        (.data DataCtor.false []) TypePM.DataTypes.bool
    | tuple (lower : previous (.tuple values) (.prod targets))
        (items : PositiveValueSafes fuel previous values targets) :
        PositiveValueSafe fuel previous (.tuple values) (.prod targets)
    | list (lower : previous (Value.buildList values)
          (TypePM.DataTypes.list element))
        (items : PositiveListValueSafes fuel previous values element) :
        PositiveValueSafe fuel previous (Value.buildList values)
          (TypePM.DataTypes.list element)
    | function
        (lower : previous value (.fn domain codomain))
        (typing : TotalPlainValueTyping value (.fn domain codomain))
        (application : ∀ argument, previous argument domain →
          applyFuel (fuel + 1) value argument = .timeout ∨
            ∃ result,
              applyFuel (fuel + 1) value argument = .ok result ∧
                previous result codomain) :
        PositiveValueSafe fuel previous value (.fn domain codomain)
    | matcher
        (lower : previous value (.matcher capability target))
        (typing : PositiveMatcherValueSafe fuel previous value capability target) :
        PositiveValueSafe fuel previous value (.matcher capability target)
    | matcherSlot
        (lower : previous value (.slot consumer target))
        (typing : PositiveMatcherValueSafe fuel previous value producer target)
        (conversion : CheckConversion .matcherToSlot
          (.matcher producer target) (.slot consumer target)) :
        PositiveValueSafe fuel previous value (.slot consumer target)

  /-- Pointwise positive-index safety for heterogeneous tuples. -/
  inductive PositiveValueSafes
      (fuel : Nat) (previous : Value → Ty → Prop) : List Value → List Ty → Prop where
    | nil : PositiveValueSafes fuel previous [] []
    | cons
        (head : PositiveValueSafe fuel previous value target)
        (tail : PositiveValueSafes fuel previous values targets) :
        PositiveValueSafes fuel previous (value :: values) (target :: targets)

  /-- Pointwise positive-index safety for the canonical runtime List. -/
  inductive PositiveListValueSafes
      (fuel : Nat) (previous : Value → Ty → Prop) : List Value → Ty → Prop where
    | nil : PositiveListValueSafes fuel previous [] element
    | cons
        (head : PositiveValueSafe fuel previous value element)
        (tail : PositiveListValueSafes fuel previous values element) :
        PositiveListValueSafes fuel previous (value :: values) element

  /-- Positive matcher safety covers primitive matchers, products of matchers,
  and generated user matcher closures.  Generated closures retain both their
  total body certificate and pointwise safety of the captured environment at
  the preceding index. -/
  inductive PositiveMatcherValueSafe
      (fuel : Nat) (previous : Value → Ty → Prop) : Value → Cap → Ty → Prop where
    | something (target : Ty) :
        PositiveMatcherValueSafe fuel previous .something .any target
    | tuple
        (items : PositiveMatcherValueSafes fuel previous
          values capabilities targets) :
        PositiveMatcherValueSafe fuel previous (.tuple values)
          (.prod capabilities) (.prod targets)
    | generated
        (value_eq : value = .matcherV environment clauses clauses)
        (environmentLength : environment.length = environmentTypes.length)
        (environmentSafe : ∀ (index : Nat) targetType,
          environmentTypes[index]? = some targetType →
            ∃ captured,
              environment[index]? = some captured ∧
                previous captured targetType)
        (body : TotalRecursiveClosureBodyTyping environmentTypes
          (.matcher clauses) (.matcher capability target)) :
        PositiveMatcherValueSafe fuel previous value capability target

  /-- Pointwise safety for fields of the built-in tuple matcher. -/
  inductive PositiveMatcherValueSafes
      (fuel : Nat) (previous : Value → Ty → Prop) :
      List Value → List Cap → List Ty → Prop where
    | nil : PositiveMatcherValueSafes fuel previous [] [] []
    | cons
        (head : PositiveMatcherValueSafe fuel previous value capability target)
        (tail : PositiveMatcherValueSafes fuel previous values capabilities targets) :
        PositiveMatcherValueSafes fuel previous (value :: values)
          (capability :: capabilities) (target :: targets)

end

/-- Step-indexed value safety.  Index zero deliberately contains every
value.  Each positive index unfolds one `PositiveValueSafe` layer, with
function application and recursive captures referring only to the preceding
index. -/
def FuelValueSafe : Nat → Value → Ty → Prop
  | 0, _, _ => True
  | fuel + 1, value, target =>
      PositiveValueSafe fuel (FuelValueSafe fuel) value target

/-- Pointwise step-indexed safety for newest-first environments. -/
def FuelEnvironmentSafe (fuel : Nat) (values : List Value)
    (targets : List Ty) : Prop :=
  values.length = targets.length ∧
    ∀ (index : Nat) target,
      targets[index]? = some target →
        ∃ value, values[index]? = some value ∧ FuelValueSafe fuel value target

/-- Timeout or a value safe at the requested residual index. -/
def FuelResultSafe (fuel : Nat) (target : Ty)
    (result : FuelResult Value) : Prop :=
  result = .timeout ∨
    ∃ value, result = .ok value ∧ FuelValueSafe fuel value target

theorem FuelResultSafe.notStuck
    (safe : FuelResultSafe fuel target result) : result.NotStuck := by
  rcases safe with timeout | ⟨value, success, _⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

namespace FuelEnvironmentSafe

theorem nil (fuel : Nat) : FuelEnvironmentSafe fuel [] [] := by
  constructor
  · rfl
  · intro index target found
    simp at found

theorem cons
    (head : FuelValueSafe fuel value target)
    (tail : FuelEnvironmentSafe fuel values targets) :
    FuelEnvironmentSafe fuel (value :: values) (target :: targets) := by
  constructor
  · simp [tail.1]
  · intro index foundTarget found
    cases index with
    | zero =>
        simp at found
        subst foundTarget
        exact ⟨value, rfl, head⟩
    | succ index =>
        simp only [List.getElem?_cons_succ] at found ⊢
        exact tail.2 index foundTarget found

end FuelEnvironmentSafe

/-- A successful function clause can be projected directly at any smaller
application index. -/
theorem FuelValueSafe.apply
    (safe : FuelValueSafe (fuel + 1) functionValue (.fn domain codomain))
    (argumentSafe : FuelValueSafe fuel argument domain) :
    FuelResultSafe fuel codomain
      (applyFuel (fuel + 1) functionValue argument) := by
  cases safe with
  | function _ _ application => exact application argument argumentSafe

/-- Positive indices are cumulative: forgetting the current layer yields the
certificate at the immediately preceding index. -/
theorem FuelValueSafe.previous
    (safe : FuelValueSafe (fuel + 1) value target) :
    FuelValueSafe fuel value target := by
  cases safe <;> assumption

/-- Pointwise product safety at matcher types exposes the matcher-specific
certificate needed by product checking conversions. -/
theorem PositiveValueSafes.toPositiveMatcherValueSafes :
    ∀ (duals : List Dual) values,
      PositiveValueSafes fuel previous values (duals.map Dual.matcherType) →
        PositiveMatcherValueSafes fuel previous values
          (Dual.capabilities duals) (Dual.targets duals)
  | [], _, safe => by
      cases safe
      exact .nil
  | dual :: duals, _, safe => by
      cases safe with
      | cons head tail =>
          cases head with
          | matcher _ matcherSafe =>
              exact .cons matcherSafe
                (toPositiveMatcherValueSafes duals _ tail)

/-- Fuel-indexed value safety is preserved by every normalized checking
conversion.  The recursive call transports the cumulative lower layer; the
positive layer either reuses a matcher certificate or collects the matcher
certificates stored in a product. -/
theorem FuelValueSafe.ofCheckConversion
  (conversion : CheckConversion conversionClass source target) :
    ∀ fuel value, FuelValueSafe fuel value source →
      FuelValueSafe fuel value target
  | 0, _, _ => by simp [FuelValueSafe]
  | fuel + 1, value, safe => by
      cases conversion with
      | ordinary => exact safe
      | matcherToSlot demand =>
          cases safe with
          | matcher lower matcherSafe =>
              exact .matcherSlot
                (FuelValueSafe.ofCheckConversion
                  (.matcherToSlot demand) fuel value lower)
                matcherSafe (.matcherToSlot demand)
      | @productMatcherToSlot duals consumer nonempty demand =>
          cases safe with
          | tuple lower items =>
              exact .matcherSlot
                (FuelValueSafe.ofCheckConversion
                  (.productMatcherToSlot nonempty demand) fuel _ lower)
                (.tuple items.toPositiveMatcherValueSafes)
                (.matcherToSlot demand)

/-- Step-indexed value safety is downward closed: a certificate at a larger
logical index can be used at every smaller index. -/
theorem FuelValueSafe.mono
    (safe : FuelValueSafe larger value target)
    (smaller_le : smaller ≤ larger) :
    FuelValueSafe smaller value target := by
  induction larger generalizing smaller with
  | zero =>
      have smaller_eq : smaller = 0 := Nat.eq_zero_of_le_zero smaller_le
      subst smaller
      exact safe
  | succ larger induction =>
      by_cases equal : smaller = larger + 1
      · subst smaller
        exact safe
      · have smaller_le_larger : smaller ≤ larger := by omega
        exact induction safe.previous smaller_le_larger

namespace FuelEnvironmentSafe

/-- Forget the current environment-safety layer pointwise. -/
theorem previous
    (safe : FuelEnvironmentSafe (fuel + 1) values targets) :
    FuelEnvironmentSafe fuel values targets := by
  refine ⟨safe.1, ?_⟩
  intro index target found
  obtain ⟨value, valueFound, valueSafe⟩ := safe.2 index target found
  exact ⟨value, valueFound, valueSafe.previous⟩

/-- Environment safety is downward closed in its logical index. -/
theorem mono
    (safe : FuelEnvironmentSafe larger values targets)
    (smaller_le : smaller ≤ larger) :
    FuelEnvironmentSafe smaller values targets := by
  refine ⟨safe.1, ?_⟩
  intro index target found
  obtain ⟨value, valueFound, valueSafe⟩ := safe.2 index target found
  exact ⟨value, valueFound, valueSafe.mono smaller_le⟩

/-- Concatenating equally indexed safe environments preserves source order
and pointwise safety. -/
theorem append
    (left : FuelEnvironmentSafe fuel leftValues leftTargets)
    (right : FuelEnvironmentSafe fuel rightValues rightTargets) :
    FuelEnvironmentSafe fuel (leftValues ++ rightValues)
      (leftTargets ++ rightTargets) := by
  induction leftValues generalizing leftTargets with
  | nil =>
      cases leftTargets with
      | nil => simpa using right
      | cons target targets =>
          have impossible := left.1
          simp at impossible
  | cons value values induction =>
      cases leftTargets with
      | nil =>
          have impossible := left.1
          simp at impossible
      | cons target targets =>
          have headSafe : FuelValueSafe fuel value target := by
            obtain ⟨foundValue, found, safe⟩ := left.2 0 target (by simp)
            simp at found
            subst foundValue
            exact safe
          have tailSafe : FuelEnvironmentSafe fuel values targets := by
            refine ⟨by simpa using left.1, ?_⟩
            intro index tailTarget found
            simpa only [List.getElem?_cons_succ] using
              left.2 (index + 1) tailTarget (by
                simpa only [List.getElem?_cons_succ] using found)
          simpa using FuelEnvironmentSafe.cons headSafe
            (induction tailSafe)

/-- A positive-index environment certificate exposes the corresponding
pointwise positive layer. -/
theorem toPositiveValueSafes :
    ∀ {values targets},
      FuelEnvironmentSafe (fuel + 1) values targets →
        PositiveValueSafes fuel (FuelValueSafe fuel) values targets
  | [], [], _ => .nil
  | [], _ :: _, safe => by
      have impossible : False := by simpa using safe.1
      exact impossible.elim
  | _ :: _, [], safe => by
      have impossible : False := by simpa using safe.1
      exact impossible.elim
  | value :: values, target :: targets, safe => by
      obtain ⟨headValue, headFound, headSafe⟩ :=
        safe.2 0 target (by simp)
      simp at headFound
      subst headValue
      have tailSafe : FuelEnvironmentSafe (fuel + 1) values targets := by
        refine ⟨by simpa using safe.1, ?_⟩
        intro index tailTarget found
        simpa only [List.getElem?_cons_succ] using
          safe.2 (index + 1) tailTarget (by
            simpa only [List.getElem?_cons_succ] using found)
      exact .cons (by simpa [FuelValueSafe] using headSafe)
        tailSafe.toPositiveValueSafes

end FuelEnvironmentSafe

/-- The index-zero boundary is unconditional, as required by the guarded
recursive occurrence. -/
theorem fuelValueSafe_zero (value : Value) (target : Ty) :
    FuelValueSafe 0 value target := by
  simp [FuelValueSafe]

/-- Ordinary integers are safe at every index. -/
theorem fuelValueSafe_int (literal : Int) (fuel : Nat) :
    FuelValueSafe fuel (.int literal) .int := by
  induction fuel with
  | zero => simp [FuelValueSafe]
  | succ fuel induction => exact .int literal induction

/-- The two closed Boolean constructors are safe at every index. -/
theorem fuelValueSafe_boolTrue (fuel : Nat) :
    FuelValueSafe fuel (.data DataCtor.true []) TypePM.DataTypes.bool := by
  induction fuel with
  | zero => simp [FuelValueSafe]
  | succ fuel induction => exact .boolTrue induction

theorem fuelValueSafe_boolFalse (fuel : Nat) :
    FuelValueSafe fuel (.data DataCtor.false []) TypePM.DataTypes.bool := by
  induction fuel with
  | zero => simp [FuelValueSafe]
  | succ fuel induction => exact .boolFalse induction

/-- Product safety is pointwise; structural typing cannot hide executable
function or matcher values in a field. -/
theorem fuelValueSafe_tuple
    (lower : FuelValueSafe fuel (.tuple values) (.prod fields))
    (items : PositiveValueSafes fuel (FuelValueSafe fuel) values fields) :
    FuelValueSafe (fuel + 1) (.tuple values) (.prod fields) :=
  .tuple lower items

/-- A tuple built from a fuel-safe heterogeneous environment is fuel-safe at
the product of the same types. -/
theorem fuelValueSafe_tuple_of_environment :
    ∀ fuel values targets,
      FuelEnvironmentSafe fuel values targets →
        FuelValueSafe fuel (.tuple values) (.prod targets)
  | 0, _, _, _ => fuelValueSafe_zero _ _
  | fuel + 1, values, targets, safe =>
      fuelValueSafe_tuple
        (fuelValueSafe_tuple_of_environment fuel values targets safe.previous)
        safe.toPositiveValueSafes

/-- Canonical Lists are pointwise safe at the same positive index. -/
theorem fuelValueSafe_list
    (lower : FuelValueSafe fuel (Value.buildList values)
      (TypePM.DataTypes.list element))
    (items : PositiveListValueSafes fuel (FuelValueSafe fuel) values element) :
    FuelValueSafe (fuel + 1) (Value.buildList values)
      (TypePM.DataTypes.list element) :=
  .list lower items

theorem PositiveListValueSafes.of_forall
    (safe : ∀ value ∈ values,
      FuelValueSafe (fuel + 1) value element) :
    PositiveListValueSafes fuel (FuelValueSafe fuel) values element := by
  induction values with
  | nil => exact .nil
  | cons value values induction =>
      exact .cons (safe value (by simp))
        (induction (by
          intro candidate member
          exact safe candidate (by simp [member])))

/-- A host List is indexed-safe when every element is indexed-safe at the
same index.  The proof also constructs the cumulative lower layer required
by the List certificate. -/
theorem fuelValueSafe_list_of_forall (element : Ty) :
    ∀ fuel values,
      (∀ value ∈ values, FuelValueSafe fuel value element) →
        FuelValueSafe fuel (Value.buildList values)
          (TypePM.DataTypes.list element)
  | 0, _, _ => fuelValueSafe_zero _ _
  | fuel + 1, values, safe => by
      have lower : FuelValueSafe fuel (Value.buildList values)
          (TypePM.DataTypes.list element) := by
        apply fuelValueSafe_list_of_forall element fuel values
        intro value member
        exact (safe value member).previous
      exact .list lower (PositiveListValueSafes.of_forall safe)

/-- `something` is the primitive matcher-safe leaf. -/
theorem fuelValueSafe_something (target : Ty) :
    ∀ fuel, FuelValueSafe fuel .something (.matcher .any target)
  | 0 => by simp [FuelValueSafe]
  | fuel + 1 =>
      .matcher (fuelValueSafe_something target fuel) (.something target)

/-- The concrete `something` matcher is safe in the equal-capability slot
accepted by `CheckConversion.matcherToSlot`.  No capability variable is
silently specialized by this constructor. -/
theorem fuelValueSafe_somethingSlot (target : Ty) :
    ∀ fuel, FuelValueSafe fuel .something (.slot .any target)
  | 0 => by simp [FuelValueSafe]
  | fuel + 1 =>
      .matcherSlot (fuelValueSafe_somethingSlot target fuel)
        (.something target) (.matcherToSlot .equal)

/-- Public boundary supplied by this stage: a function value is safe at all
indices.  Its application theorem applies only to an argument carrying the
matching indexed certificate for the function's domain. -/
def FuelFunctionSafe (value : Value) (domain codomain : Ty) : Prop :=
  ∀ fuel, FuelValueSafe fuel value (.fn domain codomain)

end TypePM.Runtime
