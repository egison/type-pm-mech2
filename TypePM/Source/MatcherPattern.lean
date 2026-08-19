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

/-- Propositional form of the capture-before-first-hole condition. -/
def CaptureBeforeFirstHole (pattern : PPat) : Prop :=
  pattern.captureBeforeFirstHole = true

instance (pattern : PPat) : Decidable pattern.CaptureBeforeFirstHole :=
  by unfold CaptureBeforeFirstHole; infer_instance

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

end DPat

/-- Pattern captures and data-pattern variables occupy disjoint namespaces. -/
theorem capture_data_binding_slots_disjoint (pattern : PPat) (data : DPat) :
    ∀ slot ∈ pattern.captureSlots, slot ∉ data.bindingSlots := by
  intro slot captureMember dataMember
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp captureMember
  simp [DPat.bindingSlots] at dataMember

end TypePM.Source
