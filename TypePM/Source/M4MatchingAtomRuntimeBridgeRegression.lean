import TypePM.Source.M4MatchingAtomRuntimeBridge
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility

/-!
# Regressions for the pattern-preserving runtime bridge

The positive example checks solved M4 tuple-pattern synthesis and its exact
source-order binding output.  The negative example fixes the erased-branch
obstruction at a concrete wildcard user atom.
-/

namespace TypePM.Source.MatcherTyping.M4MatchingAtomRuntimeBridgeRegression

open TypePM.Runtime

def tuplePattern : Pattern := .tuple [.var, .wild]

def tupleGenerated : GeneratedPattern :=
  { dual := ⟨.prod [.var ⟨0⟩, .var ⟨1⟩],
      .prod [.var ⟨0⟩, .var ⟨1⟩]⟩
    bindings := [.var ⟨0⟩]
    hard := []
    pending := [] }

theorem tuplePattern_elaborates :
    PatternElaborates Paper1FrozenSignature.signature [] [] tuplePattern []
      ⟨0, 0⟩ tupleGenerated ⟨2, 2⟩ := by
  unfold tuplePattern tupleGenerated
  exact .tuple (.cons .var (.cons .wild .nil))

theorem tuplePattern_supported : DirectRuntimePatternSupported tuplePattern := by
  exact .tuple (.cons .var (.cons .wild .nil))

theorem tuplePattern_semantic :
    GeneratedPatternRuntimeSolution tupleGenerated Subst.id := by
  simp [GeneratedPatternRuntimeSolution, tupleGenerated, Solves]

/-- Solved M4 synthesis becomes the runtime pattern judgment, with the first
tuple item contributing the sole binding. -/
theorem tuplePattern_runtimeBinds :
    ∃ newBindings,
      PatternBinds
        (fun context expression target => RuntimeTyping expression target context)
        [] [] tuplePattern
        (.prod [.var ⟨0⟩, .var ⟨1⟩]) newBindings ∧
      newBindings = [.var ⟨0⟩] := by
  obtain ⟨newBindings, typing, equality⟩ :=
    TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
      tuplePattern_elaborates Paper1FrozenSignature.runtimeCompatible
      tuplePattern_supported tuplePattern_semantic
      MonomorphicContextCompatible.nil
  refine ⟨newBindings, by simpa [tupleGenerated, Ty.apply, Ty.applyList] using typing,
    ?_⟩
  simpa [tupleGenerated, Ty.applyList] using equality.symm

def bridgeSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

theorem tuplePattern_semantic_bridge :
    GeneratedPatternRuntimeSolution tupleGenerated bridgeSolution := by
  simp [GeneratedPatternRuntimeSolution, tupleGenerated, bridgeSolution, Solves]

private theorem tupleMatcher_typed :
    ValueTyping (.tuple [.something, .something])
      (.matcher (.prod [.any, .any]) (.prod [.int, .int])) := by
  apply ValueTyping.checked
  · exact .tuple (.cons (.something .int) (.cons (.something .int) .nil))
  · exact CheckConversion.productMatcher (duals :=
      [(⟨.any, .int⟩ : Dual), ⟨.any, .int⟩]) (by simp)

/-- The executable bridge also handles a real product matcher: the tuple
pattern is split into source-ordered child atoms using the typed target tuple. -/
theorem tuplePattern_productTotalAtom :
    ∃ newBindings,
      TotalMatchingAtomTyping [] []
        ⟨tuplePattern, .tuple [.something, .something],
          .tuple [.int 1, .int 2]⟩ newBindings ∧
      newBindings = [.int] := by
  obtain ⟨newBindings, atomTyped, bindingsEq⟩ :=
    PatternElaborates.toBuiltinTotalMatchingAtomTyping
      tuplePattern_elaborates Paper1FrozenSignature.runtimeCompatible
      tuplePattern_supported
      tuplePattern_semantic_bridge MonomorphicContextCompatible.nil
      tupleMatcher_typed
      (.tuple (.cons .somethingVar (.cons .somethingWild .nil)))
      (.tuple (.cons (.int 1) (.cons (.int 2) .nil)))
  refine ⟨newBindings, atomTyped, ?_⟩
  simpa [tupleGenerated, bridgeSolution, Ty.applyList, Ty.apply] using
    bindingsEq.symm

def conjunctionPattern : Pattern := .and .var .wild

def conjunctionGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := [.var ⟨0⟩]
    hard := [
      .ty (.var ⟨0⟩) (.var ⟨1⟩),
      .cap (.var ⟨0⟩) (.var ⟨1⟩)]
    pending := [] }

theorem conjunctionPattern_elaborates :
    PatternElaborates Paper1FrozenSignature.signature [] []
      conjunctionPattern [] ⟨0, 0⟩ conjunctionGenerated ⟨2, 2⟩ := by
  unfold conjunctionPattern conjunctionGenerated
  exact .and .var .wild

theorem conjunctionPattern_semantic :
    GeneratedPatternRuntimeSolution conjunctionGenerated bridgeSolution := by
  simp [GeneratedPatternRuntimeSolution, conjunctionGenerated, bridgeSolution,
    Solves, Equation.Holds, Ty.apply, Cap.apply]

theorem conjunctionPattern_supported :
    DirectRuntimePatternSupported conjunctionPattern := by
  exact .and .var .wild

/-- The right conjunct is checked after the binding contributed by the left
conjunct, and the solved dual equations identify their common target. -/
theorem conjunctionPattern_runtimeBinds :
    ∃ newBindings,
      PatternBinds
        (fun context expression target => RuntimeTyping expression target context)
        [] [] conjunctionPattern .int newBindings ∧
      newBindings = [.int] := by
  obtain ⟨newBindings, typing, equality⟩ :=
    TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
      conjunctionPattern_elaborates Paper1FrozenSignature.runtimeCompatible
      (.and .var .wild)
      conjunctionPattern_semantic MonomorphicContextCompatible.nil
  refine ⟨newBindings, by
    simpa [conjunctionGenerated, bridgeSolution, Ty.apply, Ty.applyList] using typing,
    ?_⟩
  simpa [conjunctionGenerated, bridgeSolution, Ty.applyList, Ty.apply] using
    equality.symm

def disjunctionPattern : Pattern := .or .var .var

def disjunctionGenerated : GeneratedPattern :=
  { dual := ⟨.var ⟨0⟩, .var ⟨0⟩⟩
    bindings := [.var ⟨0⟩]
    hard := [
      .ty (.var ⟨0⟩) (.var ⟨1⟩),
      .cap (.var ⟨0⟩) (.var ⟨1⟩),
      .ty (.var ⟨0⟩) (.var ⟨1⟩)]
    pending := [] }

theorem disjunctionPattern_elaborates :
    PatternElaborates Paper1FrozenSignature.signature [] []
      disjunctionPattern [] ⟨0, 0⟩ disjunctionGenerated ⟨2, 2⟩ := by
  unfold disjunctionPattern disjunctionGenerated
  exact .or .var .var rfl

theorem disjunctionPattern_semantic :
    GeneratedPatternRuntimeSolution disjunctionGenerated bridgeSolution := by
  simp [GeneratedPatternRuntimeSolution, disjunctionGenerated, bridgeSolution,
    Solves, Equation.Holds, Ty.apply, Cap.apply]

/-- Solved pointwise binding equations make the two alternatives contribute
the same runtime binding list, as required by `PatternBinds.or`. -/
theorem disjunctionPattern_runtimeBinds :
    ∃ newBindings,
      PatternBinds
        (fun context expression target => RuntimeTyping expression target context)
        [] [] disjunctionPattern .int newBindings ∧
      newBindings = [.int] := by
  obtain ⟨newBindings, typing, equality⟩ :=
    TypePM.Source.MatcherTyping.PatternElaborates.toDirectRuntimePatternBinds
      disjunctionPattern_elaborates Paper1FrozenSignature.runtimeCompatible
      (.or .var .var)
      disjunctionPattern_semantic MonomorphicContextCompatible.nil
  refine ⟨newBindings, by
    simpa [disjunctionGenerated, bridgeSolution, Ty.apply, Ty.applyList] using typing,
    ?_⟩
  simpa [disjunctionGenerated, bridgeSolution, Ty.applyList, Ty.apply] using
    equality.symm

def conjunctionMatchAll : Expr :=
  .matchAll (.lit 7) .something conjunctionPattern (.var 0)

private theorem conjunctionMatchAll_initialAtom
    {fuel : Nat} {environment : ValueEnvironment}
    {targetValue matcherValue : Value}
    (environmentTyped : EnvironmentTyping environment [])
    (targetSuccess : evalFuel fuel environment (.lit 7) = .ok targetValue)
    (matcherSuccess : evalFuel fuel environment .something = .ok matcherValue)
    (targetTyped : ValueTyping targetValue .int)
    (matcherTyped : ValueTyping matcherValue (.matcher .any .int)) :
    TotalMatchingAtomTyping [] []
      ⟨conjunctionPattern, matcherValue, targetValue⟩ [.int] := by
  cases environmentTyped
  cases fuel with
  | zero => simp [evalFuel] at targetSuccess
  | succ fuel =>
      simp [evalFuel] at targetSuccess matcherSuccess
      subst targetValue
      subst matcherValue
      obtain ⟨newBindings, atomTyped, bindingsEq⟩ :=
        PatternElaborates.toBuiltinTotalMatchingAtomTyping
          conjunctionPattern_elaborates Paper1FrozenSignature.runtimeCompatible
          conjunctionPattern_supported
          conjunctionPattern_semantic MonomorphicContextCompatible.nil
          matcherTyped (.and .somethingVar .somethingWild) targetTyped
      have newBindingsEq : newBindings = [.int] := by
        simpa [conjunctionGenerated, bridgeSolution, Ty.applyList, Ty.apply]
          using bindingsEq.symm
      subst newBindings
      exact atomTyped

/-- A complete `matchAll` certificate whose initial atom is constructed from
the solved M4 pattern derivation and the concrete typed runtime values. -/
theorem conjunctionMatchAll_totalCoreTyping :
    TotalCoreTyping conjunctionMatchAll (TypePM.DataTypes.list .int) [] := by
  unfold conjunctionMatchAll
  exact .matchAll (.core (.lit 7)) (.core (.something .int))
    conjunctionMatchAll_initialAtom (.core (.var rfl))

theorem conjunctionMatchAll_exact :
    evalFuel 8 [] conjunctionMatchAll =
      .ok (Value.buildList [.int 7]) := by
  with_unfolding_all rfl

theorem conjunctionMatchAll_neverStuck (fuel : Nat) :
    (evalFuel fuel [] conjunctionMatchAll).NotStuck :=
  conjunctionMatchAll_totalCoreTyping.neverStuck fuel [] .nil

/-- Concrete form of the erased-pattern obstruction retained as a regression:
an unrestricted callback over erased delegated branches is inconsistent at
zero bindings.  The total atom interface instead ties its callback to an
actual successful dispatch. -/
theorem erased_wildcard_branch_callback_impossible :
    ¬ (∀ {holes recursiveBranches},
      DelegatedMatchingBranchesTyping holes recursiveBranches →
      ∀ branch ∈ recursiveBranches,
        TotalMatchingAtomsTyping [] [] branch []) := by
  intro erased
  exact erasedBranches_cannot_preserve_wildcard_zeroBindings
    (ValueTyping.int 0) erased

end TypePM.Source.MatcherTyping.M4MatchingAtomRuntimeBridgeRegression
