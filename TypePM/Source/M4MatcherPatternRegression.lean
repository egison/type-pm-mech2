import TypePM.Source.MatcherPattern

/-!
# M4 matcher-pattern regressions

The seven pattern-pattern values below are exactly the clause headers of the
paper's multiset matcher.  They remain independent of matcher-clause bodies
and source expressions.
-/

namespace TypePM.Source.M4MatcherPatternRegression

def nilHeader : PPat := .ctor PatternCtor.nil []

def headOnlyHeader : PPat :=
  .ctor PatternCtor.cons [.hole, .wild]

/-- `#$value :: $`: the capture precedes the delegated hole. -/
def valueConsHeader : PPat :=
  .ctor PatternCtor.cons [.capture, .hole]

def generalConsHeader : PPat :=
  .ctor PatternCtor.cons [.hole, .hole]

def joinHeader : PPat :=
  .ctor PatternCtor.join [.hole, .hole]

def wholeValueHeader : PPat := .capture

def catchAllHeader : PPat := .hole

/-- The rejected reversal `$ :: #$value`. -/
def captureAfterHoleHeader : PPat :=
  .ctor PatternCtor.cons [.hole, .capture]

theorem all_seven_headers_shapeOK :
    [ nilHeader, headOnlyHeader, valueConsHeader, generalConsHeader,
      joinHeader, wholeValueHeader, catchAllHeader ].all
        (PPat.shapeOK Paper1FrozenSignature.signature) = true := by
  rfl

theorem all_seven_headers_capture_order :
    [ nilHeader, headOnlyHeader, valueConsHeader, generalConsHeader,
      joinHeader, wholeValueHeader, catchAllHeader ].all
        PPat.captureBeforeFirstHole = true := by
  simp [PPat.captureBeforeFirstHole, PPat.captureBeforeFirstHoleFrom,
    PPat.occurrences, nilHeader, headOnlyHeader, valueConsHeader,
    generalConsHeader, joinHeader, wholeValueHeader, catchAllHeader]

theorem nil_summary_exact :
    nilHeader.occurrences = [] ∧
      nilHeader.holesInSourceOrder = [] ∧
      nilHeader.captureCount = 0 := by
  simp [nilHeader, PPat.occurrences, PPat.holesInSourceOrder,
    PPat.holeCount, PPat.captureCount]

theorem head_only_summary_exact :
    headOnlyHeader.occurrences = [.hole] ∧
      headOnlyHeader.holesInSourceOrder = [0] ∧
      headOnlyHeader.captureCount = 0 := by
  simp [headOnlyHeader, PPat.occurrences, PPat.holesInSourceOrder,
    PPat.holeCount, PPat.captureCount]

theorem value_cons_summary_exact :
    valueConsHeader.occurrences = [.capture, .hole] ∧
      valueConsHeader.holesInSourceOrder = [0] ∧
      valueConsHeader.captureBindings = [0] := by
  simp [valueConsHeader, PPat.occurrences, PPat.holesInSourceOrder,
    PPat.captureBindings, PPat.holeCount, PPat.captureCount]

theorem general_cons_summary_exact :
    generalConsHeader.occurrences = [.hole, .hole] ∧
      generalConsHeader.holesInSourceOrder = [0, 1] ∧
      generalConsHeader.captureCount = 0 := by
  have rangeTwo : List.range 2 = [0, 1] := by decide
  simp [generalConsHeader, PPat.occurrences, PPat.holesInSourceOrder,
    PPat.holeCount, PPat.captureCount, rangeTwo]

theorem join_summary_exact :
    joinHeader.occurrences = [.hole, .hole] ∧
      joinHeader.holesInSourceOrder = [0, 1] ∧
      joinHeader.captureCount = 0 := by
  have rangeTwo : List.range 2 = [0, 1] := by decide
  simp [joinHeader, PPat.occurrences, PPat.holesInSourceOrder,
    PPat.holeCount, PPat.captureCount, rangeTwo]

theorem whole_value_summary_exact :
    wholeValueHeader.occurrences = [.capture] ∧
      wholeValueHeader.holesInSourceOrder = [] ∧
      wholeValueHeader.captureBindings = [0] := by
  simp [wholeValueHeader, PPat.occurrences, PPat.holesInSourceOrder,
    PPat.captureBindings, PPat.holeCount, PPat.captureCount]

theorem catch_all_summary_exact :
    catchAllHeader.occurrences = [.hole] ∧
      catchAllHeader.holesInSourceOrder = [0] ∧
      catchAllHeader.captureCount = 0 := by
  simp [catchAllHeader, PPat.occurrences, PPat.holesInSourceOrder,
    PPat.holeCount, PPat.captureCount]

theorem value_cons_capture_before_hole :
    valueConsHeader.CaptureBeforeFirstHole := by
  simp [PPat.CaptureBeforeFirstHole, PPat.captureBeforeFirstHole,
    PPat.captureBeforeFirstHoleFrom, valueConsHeader, PPat.occurrences]

theorem capture_after_hole_rejected :
    ¬ captureAfterHoleHeader.CaptureBeforeFirstHole := by
  simp [PPat.CaptureBeforeFirstHole, PPat.captureBeforeFirstHole,
    PPat.captureBeforeFirstHoleFrom, captureAfterHoleHeader,
    PPat.occurrences]

theorem hole_counts_zero_one_two :
    nilHeader.holeCount = 0 ∧
      headOnlyHeader.holeCount = 1 ∧
      generalConsHeader.holeCount = 2 := by
  simp [nilHeader, headOnlyHeader, generalConsHeader, PPat.holeCount]

theorem all_seven_capture_counts_exact :
    [ nilHeader.captureCount, headOnlyHeader.captureCount,
      valueConsHeader.captureCount, generalConsHeader.captureCount,
      joinHeader.captureCount, wholeValueHeader.captureCount,
      catchAllHeader.captureCount ] = [0, 0, 1, 0, 0, 1, 0] := by
  simp [PPat.captureCount, nilHeader, headOnlyHeader, valueConsHeader,
    generalConsHeader, joinHeader, wholeValueHeader, catchAllHeader]

theorem header_capture_bindings_linear :
    valueConsHeader.captureSlots.Nodup ∧
      valueConsHeader.holeSlots.Nodup ∧
      (∀ slot ∈ valueConsHeader.holeSlots,
        slot ∉ valueConsHeader.captureSlots) :=
  ⟨valueConsHeader.captureSlots_nodup,
    valueConsHeader.holeSlots_nodup,
    valueConsHeader.hole_capture_slots_disjoint⟩

def nilArm : DPat := .ctor DataCtor.nil []

def consArm : DPat := .ctor DataCtor.cons [.var, .var]

def tupleListArm : DPat :=
  .tuple [.var, .ctor DataCtor.cons [.var, .ctor DataCtor.nil []]]

theorem data_arms_shapeOK :
    nilArm.shapeOK Paper1FrozenSignature.signature = true ∧
      consArm.shapeOK Paper1FrozenSignature.signature = true ∧
      tupleListArm.shapeOK Paper1FrozenSignature.signature = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem data_arm_bindings_exact :
    nilArm.bindingCount = 0 ∧
      consArm.bindingCount = 2 ∧
      tupleListArm.bindingCount = 2 ∧
      tupleListArm.bindingsInSourceOrder = [0, 1] := by
  have rangeTwo : List.range 2 = [0, 1] := by decide
  simp [nilArm, consArm, tupleListArm, DPat.bindingCount,
    DPat.bindingsInSourceOrder, rangeTwo]

theorem data_arm_bindings_linear :
    tupleListArm.bindingSlots.Nodup ∧
      (∀ slot ∈ valueConsHeader.captureSlots,
        slot ∉ tupleListArm.bindingSlots) :=
  ⟨tupleListArm.bindingSlots_nodup,
    capture_data_binding_slots_disjoint valueConsHeader tupleListArm⟩

def badPatternConstructorArity : PPat :=
  .ctor PatternCtor.cons [.hole]

def badDataConstructorArity : DPat :=
  .ctor DataCtor.cons [.var]

theorem bad_constructor_arities_rejected :
    badPatternConstructorArity.shapeOK Paper1FrozenSignature.signature = false ∧
      badDataConstructorArity.shapeOK Paper1FrozenSignature.signature = false := by
  exact ⟨rfl, rfl⟩

end TypePM.Source.M4MatcherPatternRegression
