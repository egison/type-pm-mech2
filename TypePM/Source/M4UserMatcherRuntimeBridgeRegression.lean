import TypePM.Source.M4UserMatcherRuntimeBridge
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility

/-!
# Regression: solved M4 matcher headers at the runtime boundary

These examples exercise source-order hole/capture accumulation and a nested
tuple/data-constructor pattern whose constructor result equation is solved by
an explicit substitution.
-/

namespace TypePM.Source.MatcherTyping.M4UserMatcherRuntimeBridgeRegression

open TypePM.Runtime

def start : Supply := ⟨0, 0⟩

def tupleSolution : Subst :=
  { cap := Cap.var
    ty := fun index => if index.index = 0 then DataTypes.bool else .int }

def nestedPattern : DPat :=
  .tuple [.ctor DataCtor.true [], .var]

def nestedExpected : Ty :=
  .prod [.var ⟨0⟩, .var ⟨1⟩]

def nestedGenerated : GeneratedDPat :=
  ⟨[.var ⟨1⟩],
    [.ty (.prod [.var ⟨0⟩, .var ⟨1⟩])
        (.prod [.var ⟨0⟩, .var ⟨1⟩]),
      .ty DataTypes.bool (.var ⟨0⟩)]⟩

theorem nestedPattern_elaborates :
    DPatElaborates Paper1FrozenSignature.signature nestedPattern nestedExpected
      start nestedGenerated ⟨2, 0⟩ := by
  unfold nestedPattern nestedExpected nestedGenerated start
  refine DPatElaborates.tuple
    (items := [.ctor DataCtor.true [], .var])
    (expected := .prod [.var ⟨0⟩, .var ⟨1⟩])
    (supply := ⟨0, 0⟩)
    (fields := [.var ⟨0⟩, .var ⟨1⟩])
    (generatedItems := ⟨[.var ⟨1⟩],
      [.ty DataTypes.bool (.var ⟨0⟩)]⟩)
    (next := ⟨2, 0⟩) (by
      simp [freshTargets, List.range_succ]) ?_
  have trueElaboration :
      DPatElaborates Paper1FrozenSignature.signature
        (.ctor DataCtor.true []) (.var ⟨0⟩) ⟨2, 0⟩
        ⟨[], [.ty DataTypes.bool (.var ⟨0⟩)]⟩ ⟨2, 0⟩ := by
    refine DPatElaborates.ctor
      (scheme := ConstructorSchemes.boolTrue) (fieldTypes := [])
      (resultType := DataTypes.bool) (generatedFields := ⟨[], []⟩) ?_ rfl ?_ .nil
    · exact Paper1FrozenSignature.lookup_true
    · rfl
  have itemsElaboration :
      DPatsElaborate Paper1FrozenSignature.signature
        [.ctor DataCtor.true [], .var] [.var ⟨0⟩, .var ⟨1⟩]
        ⟨2, 0⟩ ⟨[.var ⟨1⟩], [.ty DataTypes.bool (.var ⟨0⟩)]⟩
        ⟨2, 0⟩ := by
    exact .cons trueElaboration (.cons .var .nil)
  simpa [Supply.nextTy] using itemsElaboration

theorem nestedPattern_solved :
    Solves tupleSolution nestedGenerated.hard := by
  simp [nestedGenerated, Solves, Equation.Holds, tupleSolution,
    Ty.apply, Ty.applyList, DataTypes.bool]

/-- The constructor opening and tuple equation bridge to a nested runtime
certificate, with the variable binding retained in source order. -/
theorem nested_constructor_tuple_runtime :
    RuntimeDPatTyping nestedPattern (.prod [DataTypes.bool, .int]) [.int] := by
  simpa [nestedPattern, nestedExpected, nestedGenerated, tupleSolution,
    Ty.apply, Ty.applyList, DataTypes.bool] using
    nestedPattern_elaborates.toRuntimeDPatTyping
      Paper1FrozenSignature.runtimeCompatible nestedPattern_solved

def headerExpected : List Dual :=
  [⟨.var ⟨0⟩, .int⟩, ⟨.any, DataTypes.bool⟩]

def headerGenerated : GeneratedPPats :=
  ⟨[⟨.var ⟨0⟩, .int⟩], [DataTypes.bool],
    [.cap (.var ⟨0⟩) (.var ⟨0⟩)]⟩

theorem header_elaborates :
    PPatsElaborate Paper1FrozenSignature.signature [.hole, .capture]
      headerExpected start headerGenerated ⟨0, 1⟩ := by
  exact .cons .hole (.cons .capture .nil)

/-- Hole and capture output lists preserve their left-to-right source order. -/
theorem header_source_order_runtime :
    RuntimePPatsTyping [.hole, .capture] [.int, DataTypes.bool]
      [⟨.var ⟨0⟩, .int⟩] [DataTypes.bool] := by
  apply header_elaborates.toRuntimePPatsTyping (solution := Subst.id)
  simp [headerGenerated, Solves, Equation.Holds]

end TypePM.Source.MatcherTyping.M4UserMatcherRuntimeBridgeRegression
