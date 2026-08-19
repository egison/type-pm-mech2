import TypePM.Signature

/-!
# M3 declaration regressions

These kernel-checked examples fix the exact paper signature before source
constructor and primitive syntax is connected in the next M3 step.
-/

namespace TypePM.Source.M3DeclarationsRegression

theorem bool_alias_exact :
    TypePM.DataTypes.bool = .data DataFormer.bool [] := by
  rfl

theorem list_alias_exact (element : Ty) :
    TypePM.DataTypes.list element = .data DataFormer.list [element] := by
  rfl

theorem list_pattern_wellFormed :
    ListPatternSchemes.nil.WellFormed ∧
      ListPatternSchemes.cons.WellFormed ∧
      ListPatternSchemes.join.WellFormed := by
  exact ⟨ListPatternSchemes.nil.wellFormed,
    ListPatternSchemes.cons.wellFormed,
    ListPatternSchemes.join.wellFormed⟩

theorem list_pattern_closed :
    ListPatternSchemes.nil.Closed ∧
      ListPatternSchemes.cons.Closed ∧
      ListPatternSchemes.join.Closed := by
  constructor
  · constructor <;> rfl
  · constructor
    · constructor <;> rfl
    · constructor <;> rfl

theorem list_cons_dual_shape :
    ListPatternSchemes.cons.fields =
      [ { capability := .bound 0, target := .bound 0 },
        { capability := .con PatternFormer.list [.bound 0],
          target := PolyDataTypes.list (.bound 0) } ] ∧
    ListPatternSchemes.cons.result =
      { capability := .con PatternFormer.list [.bound 0]
        target := PolyDataTypes.list (.bound 0) } := by
  exact ⟨rfl, rfl⟩

theorem list_cons_dual_instantiation_exact :
    ListPatternSchemes.cons.instantiate ⟨7, 3⟩ =
      ( { fields :=
          [ { capability := .var ⟨3⟩, target := .var ⟨7⟩ },
            { capability := .con PatternFormer.list [.var ⟨3⟩],
              target := TypePM.DataTypes.list (.var ⟨7⟩) } ]
          result :=
            { capability := .con PatternFormer.list [.var ⟨3⟩]
              target := TypePM.DataTypes.list (.var ⟨7⟩) } },
        ⟨8, 4⟩) := by
  rfl

theorem map_instantiation_exact :
    PrimitiveSchemes.map.instantiate ⟨7, 3⟩ =
      (.fn (.fn (.var ⟨7⟩) (.var ⟨8⟩))
        (.fn (TypePM.DataTypes.list (.var ⟨7⟩))
          (TypePM.DataTypes.list (.var ⟨8⟩))),
        ⟨9, 3⟩) := by
  rfl

theorem paper1_signature_wellFormed :
    Paper1Signature.signature.WellFormed :=
  Paper1Signature.wellFormed

theorem paper1_primitive_coverage (operation : PrimOp) :
    Paper1Signature.signature.lookupPrimitive operation =
      some (PrimitiveSchemes.ofPrimOp operation) :=
  Paper1Signature.lookup_primitive operation

/-- The pre-integration bug: the List pattern former has arity one, so a
zero-argument List capability must not pass signature validation. -/
def malformedListNil : DualScheme :=
  { tyArity := 1
    capArity := 0
    fields := []
    result :=
      { capability := .con PatternFormer.list []
        target := PolyDataTypes.list (.bound 0) }
    fieldsWellScoped := by simp
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyDataTypes.list,
        PolyCap.WellScoped, PolyTy.WellScoped] }

def malformedListSignature : Signature :=
  { Paper1Signature.signature with
    patternConstructors :=
      [ ⟨PatternCtor.nil, malformedListNil⟩,
        ⟨PatternCtor.cons, ListPatternSchemes.cons⟩,
        ⟨PatternCtor.join, ListPatternSchemes.join⟩ ] }

theorem malformed_list_capability_not_wellFormed :
    ¬ malformedListSignature.WellFormed := by
  intro wellFormed
  have invalid := wellFormed.patternConstructorCapability
    (⟨PatternCtor.nil, malformedListNil⟩ : PatternConstructorDeclaration)
    (by simp [malformedListSignature])
  simp only [malformedListNil, Signature.patternCapabilityResult?,
    Option.some.injEq, Prod.mk.injEq] at invalid
  obtain ⟨former, arity, ⟨formerEquality, arityEquality⟩,
    lookup⟩ := invalid
  subst former
  subst arity
  simp [malformedListSignature, Paper1Signature.signature,
    Paper1Signature.patternFormers,
    Signature.lookupPatternFormer] at lookup

end TypePM.Source.M3DeclarationsRegression
