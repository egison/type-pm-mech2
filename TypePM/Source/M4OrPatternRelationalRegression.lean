import TypePM.Source.M4PatternTypingRegression

/-!
# M4 or-pattern relational regression

The executable elaborator already fixes the two positional binding slots of
the or-pattern exactly.  This regression records the corresponding
proof-relevant `PatternElaborates` derivation, symmetrically with the existing
conjunction regression.
-/

namespace TypePM.Source.M4PatternTypingRegression

/-- Executable or-pattern elaboration is sound for two alternatives that bind
the same two source-order positions. -/
theorem positionalOr_relational :
    PatternElaborates Paper1FrozenSignature.signature [] []
      positionalOrPattern [] ⟨0, 0⟩ positionalOrGenerated ⟨4, 4⟩ :=
  elaboratePattern_sound Paper1FrozenSignature.wellFormed
    elaborate_or_positional_bindings_exact

end TypePM.Source.M4PatternTypingRegression
