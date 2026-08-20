import TypePM.Source.PatternFunctionFreeze
import TypePM.Source.M4PatternFunctionPairRegression
import TypePM.Source.ElaborationCompleteness
import TypePM.Source.Paper1Programs
import TypePM.Runtime.PatternFunctionNodeEvaluation

/-!
# Public pattern-function freeze checker regressions

Paper 2's `pair` exercises a body with a private binder and an embedded value
expression.  The positive regression freezes its source interface and body,
then passes the resulting agreement certificate to the checked MNode
evaluator.  The negative regressions reject duplicate names and a body whose
embedded parameter lies outside the declared interface.
-/

namespace TypePM.Source.PatternFunctionFreezeRegression

open PatternFunctionFreeze
open M4PatternFunctionPairRegression
open Paper1Programs

def pairSources : List PatternFunctionSourceDefinition :=
  [{ name := pairName
     scheme := pairScheme
     body := pairDefinition.body }]

theorem pair_names_nodup :
    (pairSources.map PatternFunctionSourceDefinition.name).Nodup := by
  decide

theorem pair_interfaces_closed : interfacesClosed pairSources = true := by
  rfl

theorem generated_pair_signature_exact :
    PatternFunctionFreeze.signature Paper1Signature.signature pairSources =
      M4PatternFunctionPairRegression.signature := by
  rfl

set_option maxRecDepth 100000 in
theorem pair_bodies_checked :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature pairSources)
      pairSources = true := by
  have blockSemantic :
      (resultCheckBlock pairGenerated
        (pairScheme.instantiate ⟨0, 0⟩).1.result).SemanticSolution
          pairSolution := by
    constructor
    · apply (solves_append pairSolution pairGenerated.hard
        (Pattern.dualEquations pairGenerated.dual
          (pairScheme.instantiate ⟨0, 0⟩).1.result)).2
      exact ⟨pair_semantic_solution.1, by
        simp [Pattern.dualEquations, Solves, Equation.Holds,
          pairGenerated, pairScheme, pairSolution, DualScheme.instantiate,
          PolyDual.openBound, PolyCap.openBound, PolyCap.openBoundList,
          PolyTy.openBound, PolyTy.openBoundList, Scheme.boundTyInstance,
          Scheme.boundCapInstance, Cap.apply, Cap.applyList, Ty.apply,
          Ty.applyList, DataTypes.list, PolyDataTypes.list]⟩
    · exact pair_semantic_solution.2
  have noPending :
      (resultCheckBlock pairGenerated
        (pairScheme.instantiate ⟨0, 0⟩).1.result).pending = [] := by
    rfl
  have accepts :=
    (Generated.blockAccepts_iff_exists_semanticSolution_of_pending_eq_nil
      (resultCheckBlock pairGenerated
        (pairScheme.instantiate ⟨0, 0⟩).1.result) noPending).2
      ⟨pairSolution, blockSemantic⟩
  have succeeds := accepts.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases inferenceEq : inferGeneratedUsing unify
      (resultCheckBlock pairGenerated
        (pairScheme.instantiate ⟨0, 0⟩).1.result) with
  | none => exact False.elim (succeeds inferenceEq)
  | some result =>
      simp only [pairSources, checkBodies, Bool.and_true]
      change
        (checkBody
          (PatternFunctionFreeze.signature Paper1Signature.signature pairSources)
          pairScheme pairDefinition.body).isSome = true
      simp only [checkBody]
      rw [generated_pair_signature_exact, pair_elaboration_exact]
      simp [inferenceEq]

set_option maxRecDepth 100000 in
theorem pair_freeze_succeeds :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed pairSources).isSome = true := by
  rw [freezePatternFunctions, dif_pos pair_names_nodup,
    dif_pos pair_interfaces_closed, dif_pos pair_bodies_checked]
  rfl

def frozenPair : FrozenPatternFunctionProgram :=
  (freezePatternFunctions Paper1Signature.signature
    Paper1Signature.wellFormed pairSources).get pair_freeze_succeeds

theorem pair_freeze_exact :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed pairSources = some frozenPair := by
  cases freezeEq : freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed pairSources with
  | none =>
      have impossible := pair_freeze_succeeds
      rw [freezeEq] at impossible
      contradiction
  | some program =>
      simp [frozenPair, freezeEq]

set_option maxRecDepth 100000 in
theorem frozen_pair_signature_exact : frozenPair.signature =
    M4PatternFunctionPairRegression.signature := by
  exact (freezePatternFunctions_signature
    (program := frozenPair) pair_freeze_exact).trans
    generated_pair_signature_exact

set_option maxRecDepth 100000 in
theorem frozen_pair_definitions_exact :
    frozenPair.definitions = M4PatternFunctionPairRegression.definitions := by
  exact freezePatternFunctions_definitions
    (program := frozenPair) pair_freeze_exact

def duplicatePairSources : List PatternFunctionSourceDefinition :=
  pairSources ++ pairSources

theorem duplicate_name_rejected :
    freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed duplicatePairSources = none := by
  rfl

def badParameterSource : PatternFunctionSourceDefinition :=
  { name := ⟨"badParameter"⟩
    scheme := pairScheme
    body := .embed 2 }

theorem bad_parameter_names_nodup :
    (([badParameterSource] : List PatternFunctionSourceDefinition).map
      PatternFunctionSourceDefinition.name).Nodup := by
  decide

theorem bad_parameter_interface_closed :
    interfacesClosed [badParameterSource] = true := by
  rfl

theorem bad_parameter_body_rejected :
    checkBodies
      (PatternFunctionFreeze.signature Paper1Signature.signature
        [badParameterSource]) [badParameterSource] = false := by
  simp only [checkBodies, Bool.and_true]
  change
    (checkBody
      (PatternFunctionFreeze.signature Paper1Signature.signature
        [badParameterSource]) pairScheme (.embed 2)).isSome = false
  have elaborationFails :
      elaboratePattern
        (PatternFunctionFreeze.signature Paper1Signature.signature
          [badParameterSource]) [] (pairScheme.instantiate ⟨0, 0⟩).1.fields
        (.embed 2) [] (pairScheme.instantiate ⟨0, 0⟩).2 = none := by
    simp [elaboratePattern, pairScheme, DualScheme.instantiate,
      PolyDual.openBound, PolyCap.openBound, PolyCap.openBoundList,
      PolyTy.openBound, Scheme.boundTyInstance, Scheme.boundCapInstance]
  simp [checkBody, elaborationFails]

theorem out_of_range_parameter_rejected :
    (freezePatternFunctions Paper1Signature.signature
      Paper1Signature.wellFormed [badParameterSource]).isSome = false := by
  rw [freezePatternFunctions, dif_pos bad_parameter_names_nodup,
    dif_pos bad_parameter_interface_closed, dif_neg (by
      simpa using bad_parameter_body_rejected)]
  rfl

def pairPattern : Pattern :=
  .ctor PatternCtor.cons [.var, .app pairName [.var, .wild]]

def pairProgram : Expr :=
  .matchFirst (sourceList [.lit 1, .lit 2, .lit 1, .lit 3])
    multisetSomething [⟨pairPattern, .tuple [.var 1, .var 0]⟩]
    (sourceList [])

set_option maxRecDepth 100000 in
theorem frozen_pair_runs_through_checked_mnode_evaluator :
    Runtime.evalCheckedPatternFunctionNodesFuel frozenPair.signature
      frozenPair.definitions frozenPair.agreement 250 [] pairProgram =
        .ok (.tuple [.int 1, .int 2]) := by
  change Runtime.evalPatternFunctionNodesFuel frozenPair.definitions 250 []
    pairProgram = .ok (.tuple [.int 1, .int 2])
  rw [frozen_pair_definitions_exact]
  with_unfolding_all rfl

end TypePM.Source.PatternFunctionFreezeRegression
