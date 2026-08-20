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

/-- Declarative shape judgment for one arm header.  Binding order is an
exact equality, not evidence obtained by running the Boolean checker. -/
inductive WellFormed (signature : FrozenSignature) :
    MatcherArmHeader → Prop where
  | mk {pattern bindingOrder}
      (patternWellFormed : DPat.ShapeWellFormed signature pattern)
      (bindingOrderExact : bindingOrder = pattern.bindingsInSourceOrder) :
      WellFormed signature ⟨pattern, bindingOrder⟩

theorem WellFormed.check_eq_true
    {signature : FrozenSignature} {arm : MatcherArmHeader}
    (wellFormed : WellFormed signature arm) : arm.check signature = true := by
  cases wellFormed with
  | mk patternWellFormed bindingOrderExact =>
      simp [check, DPat.ShapeWellFormed.check_eq_true patternWellFormed,
        bindingOrderExact]

theorem wellFormed_of_check
    {signature : FrozenSignature} {arm : MatcherArmHeader}
    (checked : arm.check signature = true) : WellFormed signature arm := by
  cases arm with
  | mk pattern bindingOrder =>
      have conditions :
          pattern.shapeOK signature = true ∧
            bindingOrder = pattern.bindingsInSourceOrder := by
        simpa [check, Bool.and_eq_true] using checked
      exact .mk ((DPat.shapeWellFormed_iff signature pattern).2 conditions.1)
        conditions.2

theorem wellFormed_iff (signature : FrozenSignature) (arm : MatcherArmHeader) :
    WellFormed signature arm ↔ arm.check signature = true :=
  ⟨WellFormed.check_eq_true, wellFormed_of_check⟩

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

namespace MatcherArmHeaders

/-- Declarative left-to-right validity of every arm header. -/
inductive WellFormed (signature : FrozenSignature) :
    List MatcherArmHeader → Prop where
  | nil : WellFormed signature []
  | cons {arm arms}
      (head : arm.WellFormed signature)
      (tail : WellFormed signature arms) :
      WellFormed signature (arm :: arms)

theorem WellFormed.check_eq_true
    {signature : FrozenSignature} {arms : List MatcherArmHeader}
    (wellFormed : WellFormed signature arms) :
    arms.all (MatcherArmHeader.check signature) = true := by
  induction wellFormed with
  | nil => rfl
  | cons head tail induction =>
      simp [MatcherArmHeader.WellFormed.check_eq_true head, induction]

theorem wellFormed_of_check
    {signature : FrozenSignature} {arms : List MatcherArmHeader}
    (checked : arms.all (MatcherArmHeader.check signature) = true) :
    WellFormed signature arms := by
  induction arms with
  | nil => exact .nil
  | cons arm arms induction =>
      have conditions : arm.check signature = true ∧
          arms.all (MatcherArmHeader.check signature) = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using checked
      exact .cons (MatcherArmHeader.wellFormed_of_check conditions.1)
        (induction conditions.2)

theorem wellFormed_iff (signature : FrozenSignature)
    (arms : List MatcherArmHeader) :
    WellFormed signature arms ↔
      arms.all (MatcherArmHeader.check signature) = true :=
  ⟨WellFormed.check_eq_true, wellFormed_of_check⟩

end MatcherArmHeaders

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

/-- Declarative execution-free shape judgment for one matcher clause. -/
inductive WellFormed (signature : FrozenSignature) :
    MatcherClauseShape → Prop where
  | mk {header holeConvention arms}
      (headerWellFormed : PPat.ShapeWellFormed signature header)
      (captureOrder : header.CaptureBeforeFirstHole)
      (holeConventionExact :
        holeConvention = HoleConvention.ofCount header.holeCount)
      (armsWellFormed : MatcherArmHeaders.WellFormed signature arms) :
      WellFormed signature ⟨header, holeConvention, arms⟩

theorem WellFormed.check_eq_true
    {signature : FrozenSignature} {clause : MatcherClauseShape}
    (wellFormed : WellFormed signature clause) :
    clause.check signature = true := by
  cases wellFormed with
  | mk headerWellFormed captureOrder holeConventionExact armsWellFormed =>
      simp only [check, Bool.and_eq_true, beq_iff_eq]
      exact
        ⟨⟨⟨PPat.ShapeWellFormed.check_eq_true headerWellFormed,
            (PPat.captureBeforeFirstHole_iff _).1 captureOrder⟩,
          holeConventionExact⟩,
        MatcherArmHeaders.WellFormed.check_eq_true armsWellFormed⟩

theorem wellFormed_of_check
    {signature : FrozenSignature} {clause : MatcherClauseShape}
    (checked : clause.check signature = true) : WellFormed signature clause := by
  cases clause with
  | mk header holeConvention arms =>
      have conditions :
          ((header.shapeOK signature = true ∧
              header.captureBeforeFirstHole = true) ∧
            holeConvention = HoleConvention.ofCount header.holeCount) ∧
          arms.all (MatcherArmHeader.check signature) = true := by
        simpa only [check, Bool.and_eq_true, beq_iff_eq] using checked
      exact .mk
        ((PPat.shapeWellFormed_iff signature header).2 conditions.1.1.1)
        ((PPat.captureBeforeFirstHole_iff header).2 conditions.1.1.2)
        conditions.1.2
        (MatcherArmHeaders.wellFormed_of_check conditions.2)

theorem wellFormed_iff (signature : FrozenSignature)
    (clause : MatcherClauseShape) :
    WellFormed signature clause ↔ clause.check signature = true :=
  ⟨WellFormed.check_eq_true, wellFormed_of_check⟩

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

/-- The proof-level form of `isCatchAll`. -/
def IsCatchAll (clause : MatcherClauseShape) : Prop :=
  clause.header = .hole

theorem isCatchAll_iff (clause : MatcherClauseShape) :
    IsCatchAll clause ↔ isCatchAll clause = true := by
  cases clause with
  | mk header holeConvention arms =>
      cases header <;> simp [IsCatchAll, isCatchAll]

/-- Exactly one catch-all shape occurs, and it is the final shape. -/
inductive CatchAllLast : List MatcherClauseShape → Prop where
  | last {clause} (catchAll : IsCatchAll clause) : CatchAllLast [clause]
  | skip {clause next rest}
      (notCatchAll : ¬ IsCatchAll clause)
      (tail : CatchAllLast (next :: rest)) :
      CatchAllLast (clause :: next :: rest)

theorem catchAllLast_iff (clauses : List MatcherClauseShape) :
    CatchAllLast clauses ↔ catchAllLast clauses = true := by
  constructor
  · intro valid
    induction valid with
    | last catchAll =>
        simpa [catchAllLast] using (isCatchAll_iff _).1 catchAll
    | @skip clause next rest notCatchAll tail induction =>
        have isCatchAllFalse : isCatchAll clause = false := by
          cases result : isCatchAll clause with
          | false => rfl
          | true => exact False.elim (notCatchAll ((isCatchAll_iff _).2 result))
        rw [catchAllLast]
        simp only [isCatchAllFalse, Bool.not_false, Bool.true_and]
        exact induction
  · induction clauses with
    | nil => simp [catchAllLast]
    | cons clause clauses induction =>
        cases clauses with
        | nil =>
            intro checked
            exact .last ((isCatchAll_iff clause).2 (by
              simpa [catchAllLast] using checked))
        | cons next rest =>
            intro checked
            have conditions :
                !isCatchAll clause = true ∧
                  catchAllLast (next :: rest) = true := by
              simpa [catchAllLast, Bool.and_eq_true] using checked
            have notCatchAll : ¬ IsCatchAll clause := by
              intro catchAll
              have catchAllTrue := (isCatchAll_iff clause).1 catchAll
              simp [catchAllTrue] at conditions
            exact .skip notCatchAll (induction conditions.2)

/-- Declarative left-to-right validity of every clause shape. -/
inductive AllWellFormed (signature : FrozenSignature) :
    List MatcherClauseShape → Prop where
  | nil : AllWellFormed signature []
  | cons {clause clauses}
      (head : clause.WellFormed signature)
      (tail : AllWellFormed signature clauses) :
      AllWellFormed signature (clause :: clauses)

theorem AllWellFormed.check_eq_true
    {signature : FrozenSignature} {clauses : List MatcherClauseShape}
    (wellFormed : AllWellFormed signature clauses) :
    clauses.all (MatcherClauseShape.check signature) = true := by
  induction wellFormed with
  | nil => rfl
  | cons head tail induction =>
      simp [MatcherClauseShape.WellFormed.check_eq_true head, induction]

theorem allWellFormed_of_check
    {signature : FrozenSignature} {clauses : List MatcherClauseShape}
    (checked : clauses.all (MatcherClauseShape.check signature) = true) :
    AllWellFormed signature clauses := by
  induction clauses with
  | nil => exact .nil
  | cons clause clauses induction =>
      have conditions : clause.check signature = true ∧
          clauses.all (MatcherClauseShape.check signature) = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using checked
      exact .cons (MatcherClauseShape.wellFormed_of_check conditions.1)
        (induction conditions.2)

/-- Complete declarative counterpart of `MatcherClauseShapes.check`. -/
inductive WellFormed (signature : FrozenSignature) :
    List MatcherClauseShape → Prop where
  | mk {clauses}
      (catchAll : CatchAllLast clauses)
      (clausesWellFormed : AllWellFormed signature clauses) :
      WellFormed signature clauses

theorem WellFormed.check_eq_true
    {signature : FrozenSignature} {clauses : List MatcherClauseShape}
    (wellFormed : WellFormed signature clauses) :
    check signature clauses = true := by
  cases wellFormed with
  | mk catchAll clausesWellFormed =>
      simp [check, (catchAllLast_iff _).1 catchAll,
        AllWellFormed.check_eq_true clausesWellFormed]

theorem wellFormed_of_check
    {signature : FrozenSignature} {clauses : List MatcherClauseShape}
    (checked : check signature clauses = true) : WellFormed signature clauses := by
  have conditions : catchAllLast clauses = true ∧
      clauses.all (MatcherClauseShape.check signature) = true := by
    simpa [check, Bool.and_eq_true] using checked
  exact .mk ((catchAllLast_iff clauses).2 conditions.1)
    (allWellFormed_of_check conditions.2)

theorem wellFormed_iff (signature : FrozenSignature)
    (clauses : List MatcherClauseShape) :
    WellFormed signature clauses ↔ check signature clauses = true :=
  ⟨WellFormed.check_eq_true, wellFormed_of_check⟩

end MatcherClauseShapes

end TypePM.Source
