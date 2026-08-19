import TypePM.Source.M4RecursiveElaboration
import TypePM.Source.Paper1Programs

namespace TypePM.Source.M4RecursiveElaborationRegression

open TypePM.Source
open TypePM.Source.Paper1Programs

def valuePatternMatch : Expr :=
  .matchAll (.lit 1) .something (.value (.lit 1)) (.lit 2)

def firstMatch : Expr :=
  .matchFirst (.lit 1) .something [.mk .wild (.lit 2)]

def valuePatternRecurses : Bool :=
  (M4.elaborate Paper1FrozenSignature.signature [] valuePatternMatch
    ⟨0, 0⟩).isSome

def firstMatchRecurses : Bool :=
  (M4.elaborate Paper1FrozenSignature.signature [] firstMatch ⟨0, 0⟩).isSome

#eval valuePatternRecurses
#eval firstMatchRecurses

/-- Exact final-source fixtures exercised by the full dispatcher.  These
booleans are executable regression entry points; documentation records the
remaining closure mismatch separately from traversal. -/
def listMatcherElaborates : Bool :=
  (M4.elaborate Paper1FrozenSignature.signature [] listMatcherDefinition
    ⟨0, 0⟩).isSome

def multisetElaborates : Bool :=
  (M4.elaborate Paper1FrozenSignature.signature
    [.mono (.fn (.matcher .any .int) (.matcher .any
      (DataTypes.list .int)))] multisetDefinition ⟨2, 0⟩).isSome

def closedMultisetElaborates : Bool :=
  (M4.elaborate Paper1FrozenSignature.signature [] closedMultisetDefinition
    ⟨0, 0⟩).isSome

#eval listMatcherElaborates
#eval multisetElaborates
#eval closedMultisetElaborates

def nonexhaustiveFirst : Expr :=
  .matchFirst (.lit 1) .something [.mk (.value (.lit 1)) (.lit 2)]

theorem nonexhaustive_match_first_rejected :
    M4.infer Paper1FrozenSignature.signature [] nonexhaustiveFirst = none := by
  rfl

def escapingSelf : Expr := .fixE (.var 1)

theorem escaping_self_rejected :
    M4.infer Paper1FrozenSignature.signature [] escapingSelf = none := by
  simp [M4.infer, M4.elaborate, M4.elaborateFuel, escapingSelf,
    elaborateFixUsing, DirectSelf.check]

end TypePM.Source.M4RecursiveElaborationRegression
