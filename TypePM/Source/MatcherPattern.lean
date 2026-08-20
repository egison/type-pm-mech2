import TypePM.Source.FrozenSignature

/-!
# Matcher-pattern static shapes

This module records only the expression-free pattern shapes needed at
matcher-clause headers.  The direct clause and expression syntax is defined
separately in `Source.Syntax`, so this checker remains independent of clause
bodies.  Hole, capture, and data-variable binders are nameless; their stable
identifiers are their left-to-right positions in the corresponding summary.
-/

namespace TypePM.Source

/-- A pattern pattern: the pattern-shaped header inspected by a matcher
clause. -/
inductive PPat where
  | hole
  | wild
  | capture
  | ctor (constructor : PatternCtor) (fields : List PPat)
deriving Repr

/-- A data pattern used to inspect a data value in a matcher implementation. -/
inductive DPat where
  | var
  | wild
  | ctor (constructor : DataCtor) (fields : List DPat)
  | tuple (items : List DPat)
deriving Repr

/-- Hole and capture occurrences, with no user-chosen binder name. -/
inductive PPatOccurrence where
  | hole
  | capture
deriving Repr, DecidableEq

/-- Separate namespaces for all source-order nameless identifiers in matcher
patterns. -/
inductive NamelessBinderSlot where
  | hole (index : Nat)
  | capture (index : Nat)
  | dataVar (index : Nat)
deriving Repr, DecidableEq

namespace PPat

/-- Hole and capture occurrences in left-to-right source order. -/
def occurrences : PPat → List PPatOccurrence
  | .hole => [.hole]
  | .wild => []
  | .capture => [.capture]
  | .ctor _ fields => fields.flatMap occurrences

def holeCount : PPat → Nat
  | .hole => 1
  | .wild => 0
  | .capture => 0
  | .ctor _ fields => (fields.map holeCount).sum

def captureCount : PPat → Nat
  | .hole => 0
  | .wild => 0
  | .capture => 1
  | .ctor _ fields => (fields.map captureCount).sum

/-- Nameless holes receive consecutive identifiers in source order. -/
def holesInSourceOrder (pattern : PPat) : List Nat :=
  List.range pattern.holeCount

/-- Nameless captures receive consecutive binding identifiers in source
order. -/
def captureBindings (pattern : PPat) : List Nat :=
  List.range pattern.captureCount

def holeSlots (pattern : PPat) : List NamelessBinderSlot :=
  pattern.holesInSourceOrder.map NamelessBinderSlot.hole

def captureSlots (pattern : PPat) : List NamelessBinderSlot :=
  pattern.captureBindings.map NamelessBinderSlot.capture

theorem holesInSourceOrder_nodup (pattern : PPat) :
    pattern.holesInSourceOrder.Nodup :=
  List.nodup_range

theorem captureBindings_nodup (pattern : PPat) :
    pattern.captureBindings.Nodup :=
  List.nodup_range

theorem holeSlots_nodup (pattern : PPat) : pattern.holeSlots.Nodup := by
  apply pattern.holesInSourceOrder_nodup.map
  intro left right unequal equalSlots
  exact unequal (NamelessBinderSlot.hole.inj equalSlots)

theorem captureSlots_nodup (pattern : PPat) :
    pattern.captureSlots.Nodup := by
  apply pattern.captureBindings_nodup.map
  intro left right unequal equalSlots
  exact unequal (NamelessBinderSlot.capture.inj equalSlots)

/-- Hole and capture positions are disjoint even when their numeric
source-order indices agree. -/
theorem hole_capture_slots_disjoint (pattern : PPat) :
    ∀ slot ∈ pattern.holeSlots, slot ∉ pattern.captureSlots := by
  intro slot holeMember captureMember
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp holeMember
  simp [captureSlots] at captureMember

/-- Scan an occurrence summary while recording whether its first hole has
already been seen. -/
def captureBeforeFirstHoleFrom : Bool → List PPatOccurrence → Bool
  | _, [] => true
  | _, .hole :: rest => captureBeforeFirstHoleFrom true rest
  | false, .capture :: rest => captureBeforeFirstHoleFrom false rest
  | true, .capture :: _ => false

/-- Executable check that no capture occurs after the first hole. -/
def captureBeforeFirstHole (pattern : PPat) : Bool :=
  captureBeforeFirstHoleFrom false pattern.occurrences

/-- Declarative scan state for capture ordering.  The Boolean index records
whether a hole has already occurred; there is deliberately no constructor
for a capture in the `true` state. -/
inductive CaptureOrderFrom : Bool → List PPatOccurrence → Prop where
  | nil {holeSeen} : CaptureOrderFrom holeSeen []
  | hole {holeSeen rest}
      (tail : CaptureOrderFrom true rest) :
      CaptureOrderFrom holeSeen (.hole :: rest)
  | capture {rest}
      (tail : CaptureOrderFrom false rest) :
      CaptureOrderFrom false (.capture :: rest)

/-- Declarative capture-before-first-hole condition for one header. -/
def CaptureBeforeFirstHole (pattern : PPat) : Prop :=
  CaptureOrderFrom false pattern.occurrences

theorem CaptureOrderFrom.check_eq_true
    {holeSeen : Bool} {summary : List PPatOccurrence}
    (ordered : CaptureOrderFrom holeSeen summary) :
    captureBeforeFirstHoleFrom holeSeen summary = true := by
  induction ordered with
  | nil => rfl
  | hole tail induction =>
      simpa [captureBeforeFirstHoleFrom] using induction
  | capture tail induction =>
      simpa [captureBeforeFirstHoleFrom] using induction

theorem captureOrderFrom_of_check
    {holeSeen : Bool} {summary : List PPatOccurrence}
    (checked : captureBeforeFirstHoleFrom holeSeen summary = true) :
    CaptureOrderFrom holeSeen summary := by
  induction summary generalizing holeSeen with
  | nil => exact .nil
  | cons occurrence rest induction =>
      cases occurrence with
      | hole =>
          exact .hole (induction (by
            simpa [captureBeforeFirstHoleFrom] using checked))
      | capture =>
          cases holeSeen with
          | false =>
              exact .capture (induction (by
                simpa [captureBeforeFirstHoleFrom] using checked))
          | true => simp [captureBeforeFirstHoleFrom] at checked

theorem captureOrderFrom_iff (holeSeen : Bool)
    (summary : List PPatOccurrence) :
    CaptureOrderFrom holeSeen summary ↔
      captureBeforeFirstHoleFrom holeSeen summary = true :=
  ⟨CaptureOrderFrom.check_eq_true, captureOrderFrom_of_check⟩

theorem captureBeforeFirstHole_iff (pattern : PPat) :
    pattern.CaptureBeforeFirstHole ↔
      pattern.captureBeforeFirstHole = true :=
  captureOrderFrom_iff false pattern.occurrences

instance (pattern : PPat) : Decidable pattern.CaptureBeforeFirstHole :=
  decidable_of_iff (pattern.captureBeforeFirstHole = true)
    (captureBeforeFirstHole_iff pattern).symm

mutual

  /-- Check constructor existence, constructor field count, and all nested
  pattern shapes against a frozen signature. -/
  def shapeOK (signature : FrozenSignature) : PPat → Bool
    | .hole | .wild | .capture => true
    | .ctor constructor fields =>
        match signature.lookupPatternConstructor constructor with
        | none => false
        | some scheme =>
            fields.length == scheme.fields.length &&
              shapesOK signature fields

  def shapesOK (signature : FrozenSignature) : List PPat → Bool
    | [] => true
    | pattern :: rest =>
        shapeOK signature pattern && shapesOK signature rest

end

mutual

  /-- Declarative pattern-pattern shape judgment.  Constructor lookup and
  arity are retained as proof premises, while nested fields are checked by
  the companion list judgment. -/
  inductive ShapeWellFormed (signature : FrozenSignature) : PPat → Prop where
    | hole : ShapeWellFormed signature .hole
    | wild : ShapeWellFormed signature .wild
    | capture : ShapeWellFormed signature .capture
    | ctor {constructor fields scheme}
        (declared : signature.lookupPatternConstructor constructor = some scheme)
        (arity : fields.length = scheme.fields.length)
        (fieldsWellFormed : ShapesWellFormed signature fields) :
        ShapeWellFormed signature (.ctor constructor fields)

  /-- Declarative left-to-right list form of `ShapeWellFormed`. -/
  inductive ShapesWellFormed (signature : FrozenSignature) : List PPat → Prop where
    | nil : ShapesWellFormed signature []
    | cons {pattern patterns}
        (head : ShapeWellFormed signature pattern)
        (tail : ShapesWellFormed signature patterns) :
        ShapesWellFormed signature (pattern :: patterns)

end

mutual

  theorem ShapeWellFormed.check_eq_true
      {signature : FrozenSignature} {pattern : PPat}
      (wellFormed : ShapeWellFormed signature pattern) :
      pattern.shapeOK signature = true := by
    cases wellFormed with
    | hole | wild | capture => rfl
    | ctor declared arity fieldsWellFormed =>
        simp [shapeOK, declared, arity,
          ShapesWellFormed.check_eq_true fieldsWellFormed]

  theorem ShapesWellFormed.check_eq_true
      {signature : FrozenSignature} {patterns : List PPat}
      (wellFormed : ShapesWellFormed signature patterns) :
      shapesOK signature patterns = true := by
    cases wellFormed with
    | nil => rfl
    | cons head tail =>
        simp [shapesOK, ShapeWellFormed.check_eq_true head,
          ShapesWellFormed.check_eq_true tail]

end


mutual

  theorem shapeWellFormed_of_check
      {signature : FrozenSignature} {pattern : PPat}
      (checked : pattern.shapeOK signature = true) :
      ShapeWellFormed signature pattern := by
    cases pattern with
    | hole => exact .hole
    | wild => exact .wild
    | capture => exact .capture
    | ctor constructor fields =>
        cases declared : signature.lookupPatternConstructor constructor with
        | none => simp [shapeOK, declared] at checked
        | some scheme =>
            have conditions :
                fields.length = scheme.fields.length ∧
                  shapesOK signature fields = true := by
              simpa [shapeOK, declared, Bool.and_eq_true] using checked
            exact .ctor declared conditions.1
              (shapesWellFormed_of_check conditions.2)

  theorem shapesWellFormed_of_check
      {signature : FrozenSignature} {patterns : List PPat}
      (checked : shapesOK signature patterns = true) :
      ShapesWellFormed signature patterns := by
    cases patterns with
    | nil => exact .nil
    | cons pattern patterns =>
        have conditions :
            pattern.shapeOK signature = true ∧
              shapesOK signature patterns = true := by
          simpa [shapesOK, Bool.and_eq_true] using checked
        exact .cons (shapeWellFormed_of_check conditions.1)
          (shapesWellFormed_of_check conditions.2)

end


theorem shapeWellFormed_iff (signature : FrozenSignature) (pattern : PPat) :
    ShapeWellFormed signature pattern ↔ pattern.shapeOK signature = true :=
  ⟨ShapeWellFormed.check_eq_true, shapeWellFormed_of_check⟩

theorem shapesWellFormed_iff (signature : FrozenSignature)
    (patterns : List PPat) :
    ShapesWellFormed signature patterns ↔ shapesOK signature patterns = true :=
  ⟨ShapesWellFormed.check_eq_true, shapesWellFormed_of_check⟩

end PPat

namespace DPat

def bindingCount : DPat → Nat
  | .var => 1
  | .wild => 0
  | .ctor _ fields => (fields.map bindingCount).sum
  | .tuple items => (items.map bindingCount).sum

/-- Nameless data-pattern variables receive consecutive binding identifiers
in left-to-right source order. -/
def bindingsInSourceOrder (pattern : DPat) : List Nat :=
  List.range pattern.bindingCount

def bindingSlots (pattern : DPat) : List NamelessBinderSlot :=
  pattern.bindingsInSourceOrder.map NamelessBinderSlot.dataVar

theorem bindingsInSourceOrder_nodup (pattern : DPat) :
    pattern.bindingsInSourceOrder.Nodup :=
  List.nodup_range

theorem bindingSlots_nodup (pattern : DPat) : pattern.bindingSlots.Nodup := by
  apply pattern.bindingsInSourceOrder_nodup.map
  intro left right unequal equalSlots
  exact unequal (NamelessBinderSlot.dataVar.inj equalSlots)

/-- Count the curried arguments before a declared data result. -/
def constructorArity? : PolyTy → Option Nat
  | .fn _ result => (constructorArity? result).map Nat.succ
  | .data _ _ => some 0
  | _ => none

mutual

  /-- Check constructor existence, constructor field count, and all nested
  data pattern shapes against a frozen signature.  Tuples have no declaration
  lookup and recursively check each item. -/
  def shapeOK (signature : FrozenSignature) : DPat → Bool
    | .var | .wild => true
    | .tuple items => shapesOK signature items
    | .ctor constructor fields =>
        match signature.lookupDataConstructor constructor with
        | none => false
        | some scheme =>
            constructorArity? scheme.body == some fields.length &&
              shapesOK signature fields

  def shapesOK (signature : FrozenSignature) : List DPat → Bool
    | [] => true
    | pattern :: rest =>
        shapeOK signature pattern && shapesOK signature rest

end

mutual

  /-- Declarative data-pattern shape judgment.  A constructor records its
  frozen declaration and exact curried arity; tuples only require their
  component judgments. -/
  inductive ShapeWellFormed (signature : FrozenSignature) : DPat → Prop where
    | var : ShapeWellFormed signature .var
    | wild : ShapeWellFormed signature .wild
    | ctor {constructor fields scheme}
        (declared : signature.lookupDataConstructor constructor = some scheme)
        (arity : constructorArity? scheme.body = some fields.length)
        (fieldsWellFormed : ShapesWellFormed signature fields) :
        ShapeWellFormed signature (.ctor constructor fields)
    | tuple {items}
        (itemsWellFormed : ShapesWellFormed signature items) :
        ShapeWellFormed signature (.tuple items)

  /-- Declarative left-to-right list form of data-pattern shape validity. -/
  inductive ShapesWellFormed (signature : FrozenSignature) : List DPat → Prop where
    | nil : ShapesWellFormed signature []
    | cons {pattern patterns}
        (head : ShapeWellFormed signature pattern)
        (tail : ShapesWellFormed signature patterns) :
        ShapesWellFormed signature (pattern :: patterns)

end


mutual

  theorem ShapeWellFormed.check_eq_true
      {signature : FrozenSignature} {pattern : DPat}
      (wellFormed : ShapeWellFormed signature pattern) :
      pattern.shapeOK signature = true := by
    cases wellFormed with
    | var | wild => rfl
    | ctor declared arity fieldsWellFormed =>
        simp [shapeOK, declared, arity,
          ShapesWellFormed.check_eq_true fieldsWellFormed]
    | tuple itemsWellFormed =>
        exact ShapesWellFormed.check_eq_true itemsWellFormed

  theorem ShapesWellFormed.check_eq_true
      {signature : FrozenSignature} {patterns : List DPat}
      (wellFormed : ShapesWellFormed signature patterns) :
      shapesOK signature patterns = true := by
    cases wellFormed with
    | nil => rfl
    | cons head tail =>
        simp [shapesOK, ShapeWellFormed.check_eq_true head,
          ShapesWellFormed.check_eq_true tail]

end


mutual

  theorem shapeWellFormed_of_check
      {signature : FrozenSignature} {pattern : DPat}
      (checked : pattern.shapeOK signature = true) :
      ShapeWellFormed signature pattern := by
    cases pattern with
    | var => exact .var
    | wild => exact .wild
    | tuple items =>
        exact .tuple (shapesWellFormed_of_check checked)
    | ctor constructor fields =>
        cases declared : signature.lookupDataConstructor constructor with
        | none => simp [shapeOK, declared] at checked
        | some scheme =>
            have conditions :
                constructorArity? scheme.body = some fields.length ∧
                  shapesOK signature fields = true := by
              simpa [shapeOK, declared, Bool.and_eq_true] using checked
            exact .ctor declared conditions.1
              (shapesWellFormed_of_check conditions.2)

  theorem shapesWellFormed_of_check
      {signature : FrozenSignature} {patterns : List DPat}
      (checked : shapesOK signature patterns = true) :
      ShapesWellFormed signature patterns := by
    cases patterns with
    | nil => exact .nil
    | cons pattern patterns =>
        have conditions :
            pattern.shapeOK signature = true ∧
              shapesOK signature patterns = true := by
          simpa [shapesOK, Bool.and_eq_true] using checked
        exact .cons (shapeWellFormed_of_check conditions.1)
          (shapesWellFormed_of_check conditions.2)

end


theorem shapeWellFormed_iff (signature : FrozenSignature) (pattern : DPat) :
    ShapeWellFormed signature pattern ↔ pattern.shapeOK signature = true :=
  ⟨ShapeWellFormed.check_eq_true, shapeWellFormed_of_check⟩

theorem shapesWellFormed_iff (signature : FrozenSignature)
    (patterns : List DPat) :
    ShapesWellFormed signature patterns ↔ shapesOK signature patterns = true :=
  ⟨ShapesWellFormed.check_eq_true, shapesWellFormed_of_check⟩

end DPat

/-- Pattern captures and data-pattern variables occupy disjoint namespaces. -/
theorem capture_data_binding_slots_disjoint (pattern : PPat) (data : DPat) :
    ∀ slot ∈ pattern.captureSlots, slot ∉ data.bindingSlots := by
  intro slot captureMember dataMember
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp captureMember
  simp [DPat.bindingSlots] at dataMember

end TypePM.Source
