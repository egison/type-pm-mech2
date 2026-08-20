import TypePM.PatternFunctionBodyPlanAutomation
import TypePM.PatternFunctionSafetyRegression

/-!
# Automatic checked-body plan regression

The three-parameter public-freeze fixture is rebuilt through the structural
execution compiler.  The certificate mentions only the three unavoidable
actual-argument exports; tuple and nested-conjunction plan assembly is
automatic.
-/

namespace TypePM.PatternFunctionBodyPlanAutomationRegression

open Source Runtime
open PatternFunctionSafetyRegression

theorem triple_body_shape_checked :
    checkedBodyPlanShape [.var, .wild, .var]
      ⟨tripleBody, .tuple [.something, .something],
        .tuple [.int 41, .int 42]⟩ = true := by
  rfl

theorem private_variable_body_is_outside_automatic_fragment :
    checkedBodyPlanShape [] ⟨.var, .something, .int 0⟩ = false := by
  rfl

theorem missing_actual_argument_is_rejected :
    checkedBodyPlanShape [.var]
      ⟨.embed 1, .something, .int 0⟩ = false := by
  rfl

def tripleLeafResolver :
    CheckedBodyExportResolver frozenTriple.signature frozenTriple.definitions
      [] [.var, .wild, .var] where
  resolve outerBindingTypes index matcher target :=
    match index, matcher, target with
    | 0, .something, .int 41 =>
        some ⟨outerBindingTypes ++ [.int],
          CheckedBodyExecution.parameter rfl
            (.ordinary
              (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 41)))
              .nil)⟩
    | 1, .something, .int 41 =>
        some ⟨outerBindingTypes,
          CheckedBodyExecution.parameter rfl
            (.ordinary
              (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingWild (.int 41)))
              (by simpa using
                (.nil : CheckedScopedWorkTyping frozenTriple.signature
                  frozenTriple.definitions [] outerBindingTypes []
                  outerBindingTypes)))⟩
    | 2, .something, .int 42 =>
        some ⟨outerBindingTypes ++ [.int],
          CheckedBodyExecution.parameter rfl
            (.ordinary
              (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar (.int 42)))
              .nil)⟩
    | _, _, _ => none

def tripleCompilation :=
  CheckedBodyExecution.compile tripleLeafResolver []
    ⟨tripleBody, .tuple [.something, .something],
      .tuple [.int 41, .int 42]⟩

theorem tripleCompilation_isSome : tripleCompilation.isSome = true := by
  simp [tripleCompilation, CheckedBodyExecution.compile,
    CheckedBodyExecution.compileFuel,
    CheckedBodyExecution.compileFuel.compileAtoms, tripleLeafResolver,
    tripleBody, zipMatchingAtoms]

def tripleCompilationResult :=
  tripleCompilation.get tripleCompilation_isSome

theorem tripleCompilation_answerTypes :
    tripleCompilationResult.1 = [.int, .int] := by
  simp [tripleCompilationResult, tripleCompilation,
    CheckedBodyExecution.compile, CheckedBodyExecution.compileFuel,
    CheckedBodyExecution.compileFuel.compileAtoms, tripleLeafResolver,
    tripleBody, zipMatchingAtoms]

def tripleBodyExecution :
    CheckedBodyExecution frozenTriple.signature frozenTriple.definitions
      [] [.var, .wild, .var] []
      ⟨tripleBody, .tuple [.something, .something],
        .tuple [.int 41, .int 42]⟩ [.int, .int] :=
  tripleCompilation_answerTypes ▸ tripleCompilationResult.2

theorem tripleInitialState_checked_automatic :
    CheckedScopedStateTyping frozenTriple.signature frozenTriple.definitions
      tripleInitialState [.int, .int] := by
  refine .mk .nil .nil ?_
  exact CheckedScopedWorkTyping.applicationOfCheckedBodyExecution
    frozenTriple.agreement frozenTriple_lookup rfl tripleBodyExecution .nil

theorem public_frozen_triple_automatic_exact :
    depthFirstFuel
      (stepPatternFunctionState frozenTriple.definitions variableOnlyReducer)
      20 [tripleInitialState] = .ok [[.int 41, .int 42]] :=
  public_frozen_triple_scoped_dfs_exact

theorem public_frozen_triple_automatic_typed :
    TypedMatchingSearchResult [.int, .int]
      (depthFirstFuel
        (stepPatternFunctionState frozenTriple.definitions variableOnlyReducer)
        20 [tripleInitialState]) := by
  apply depthFirstCheckedScopedMatching_typedSafe
    variableOnlyReducer_checkedSafe variableOnlyReducer_structuralSafe
  intro state member
  simp only [List.mem_singleton] at member
  subst state
  exact tripleInitialState_checked_automatic

theorem public_frozen_triple_automatic_never_stuck :
    (depthFirstFuel
      (stepPatternFunctionState frozenTriple.definitions variableOnlyReducer)
      20 [tripleInitialState]).NotStuck := by
  rw [public_frozen_triple_automatic_exact]
  trivial

end TypePM.PatternFunctionBodyPlanAutomationRegression
