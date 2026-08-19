import TypePM.Source.MatcherPattern

/-!
# Execution-free matcher-clause structure

This module records the expression-free erasure of a matcher clause: one
pattern-pattern header, an ordered list of data-pattern arm headers, and
metadata describing the number of delegated holes.  It contains no source
expression, inference rule, or execution rule; `Source.Syntax` maps each
direct clause to this shape before checking it.
-/

namespace TypePM.Source

/-- The three conventions used by clause headers with zero, one, or a fixed
number `k` of delegated holes.  `multiple k` is valid only when `k ≥ 2`; the
checker below derives the canonical convention from the header. -/
inductive HoleConvention where
  | zero
  | one
  | multiple (count : Nat)
deriving Repr, DecidableEq

namespace HoleConvention

def ofCount : Nat → HoleConvention
  | 0 => .zero
  | 1 => .one
  | count => .multiple count

end HoleConvention

/-- A data-pattern arm header and its claimed left-to-right binding order.
The binding list is metadata, not a list of user variable names. -/
structure MatcherArmHeader where
  pattern : DPat
  bindingOrder : List Nat
deriving Repr

namespace MatcherArmHeader

/-- Construct binding metadata directly from the data pattern. -/
def canonical (pattern : DPat) : MatcherArmHeader :=
  { pattern := pattern
    bindingOrder := pattern.bindingsInSourceOrder }

def bindingSlots (arm : MatcherArmHeader) : List NamelessBinderSlot :=
  arm.bindingOrder.map NamelessBinderSlot.dataVar

/-- Check the data-constructor shape and the exact source-order binding
metadata. -/
def check (signature : FrozenSignature) (arm : MatcherArmHeader) : Bool :=
  arm.pattern.shapeOK signature &&
    arm.bindingOrder == arm.pattern.bindingsInSourceOrder

@[simp] theorem check_canonical
    (signature : FrozenSignature) (pattern : DPat) :
    (canonical pattern).check signature = pattern.shapeOK signature := by
  simp [check, canonical]

theorem bindingOrder_exact_of_check
    {signature : FrozenSignature} {arm : MatcherArmHeader}
    (checked : arm.check signature = true) :
    arm.bindingOrder = arm.pattern.bindingsInSourceOrder := by
  simp only [check, Bool.and_eq_true] at checked
  exact beq_iff_eq.mp checked.2

theorem bindingSlots_nodup_of_check
    {signature : FrozenSignature} {arm : MatcherArmHeader}
    (checked : arm.check signature = true) : arm.bindingSlots.Nodup := by
  rw [bindingSlots, bindingOrder_exact_of_check checked]
  exact arm.pattern.bindingSlots_nodup

end MatcherArmHeader

/-- The static, execution-free part of a matcher clause. -/
structure MatcherClauseShape where
  header : PPat
  holeConvention : HoleConvention
  arms : List MatcherArmHeader
deriving Repr

namespace MatcherClauseShape

def check (signature : FrozenSignature) (clause : MatcherClauseShape) : Bool :=
  clause.header.shapeOK signature &&
    clause.header.captureBeforeFirstHole &&
    clause.holeConvention == HoleConvention.ofCount clause.header.holeCount &&
    clause.arms.all (MatcherArmHeader.check signature)

theorem arm_bindingSlots_nodup
    {signature : FrozenSignature} {clause : MatcherClauseShape}
    (checked : clause.check signature = true)
    {arm : MatcherArmHeader} (member : arm ∈ clause.arms) :
    arm.bindingSlots.Nodup := by
  have armsChecked :
      clause.arms.all (MatcherArmHeader.check signature) = true :=
    by
      simp only [check, Bool.and_eq_true] at checked
      exact checked.2
  have armChecked : arm.check signature = true := by
    exact (List.all_eq_true.mp armsChecked) arm member
  exact MatcherArmHeader.bindingSlots_nodup_of_check armChecked

/-- Capture slots from the pattern-pattern header cannot collide with the
data-variable slots of any arm. -/
theorem capture_arm_bindingSlots_disjoint
    (clause : MatcherClauseShape) (arm : MatcherArmHeader) :
    ∀ slot ∈ clause.header.captureSlots, slot ∉ arm.bindingSlots := by
  intro slot captureMember armMember
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp captureMember
  simp [MatcherArmHeader.bindingSlots] at armMember

end MatcherClauseShape

namespace MatcherClauseShapes

/-- A bare hole is the catch-all pattern-pattern header. -/
def isCatchAll (clause : MatcherClauseShape) : Bool :=
  match clause.header with
  | .hole => true
  | _ => false

/-- Require exactly one catch-all clause and require it to be last. -/
def catchAllLast : List MatcherClauseShape → Bool
  | [] => false
  | clause :: rest =>
      match rest with
      | [] => isCatchAll clause
      | _ :: _ => !isCatchAll clause && catchAllLast rest

def check (signature : FrozenSignature)
    (clauses : List MatcherClauseShape) : Bool :=
  catchAllLast clauses && clauses.all (MatcherClauseShape.check signature)

end MatcherClauseShapes

end TypePM.Source
