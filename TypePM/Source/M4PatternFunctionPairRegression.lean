import TypePM.Source.PatternFunctionDefinition
import TypePM.Source.Paper1Programs

/-!
# General pattern-function declaration regression

Paper 2's `pair` body has one private binder, so its raw generated result is
not literally the declared result and its binding list is not empty.  The
checked declaration instead records one semantic solution of all generated
constraints and compares the two result duals after that solution is applied.
-/

namespace TypePM.Source.M4PatternFunctionPairRegression

def pairName : PatternFunName := ⟨"pair"⟩

def pairDefinition : PatternFunctionDefinition :=
  { name := pairName
    parameterCount := 2
    body := .ctor PatternCtor.cons
      [.and .var (.embed 0),
       .ctor PatternCtor.cons [.value (.var 0), .embed 1]] }

def pairScheme : DualScheme :=
  { tyArity := 1
    capArity := 1
    fields := [⟨.bound 0, .bound 0⟩,
      ⟨.con PatternFormer.list [.bound 0], PolyDataTypes.list (.bound 0)⟩]
    result :=
      ⟨.con PatternFormer.list [.bound 0], PolyDataTypes.list (.bound 0)⟩
    fieldsWellScoped := by
      intro field member
      simp at member
      rcases member with rfl | rfl <;>
        simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped,
          PolyDataTypes.list]
    resultWellScoped := by
      simp [PolyDual.WellScoped, PolyCap.WellScoped, PolyTy.WellScoped,
        PolyDataTypes.list] }

def signature : FrozenSignature :=
  { base := Paper1Signature.signature
    patternFunctions := [⟨pairName, pairScheme⟩] }

theorem signature_wellFormed : signature.WellFormed := by
  refine
    { baseWellFormed := Paper1Signature.wellFormed
      patternFunctionNodup := by decide
      patternFunctionClosed := ?_
      patternFunctionWellFormed := ?_ }
  · intro declaration member
    simp [signature] at member
    subst declaration
    simp [DualScheme.Closed, DualScheme.freeTyVars,
      DualScheme.freeCapVars, pairScheme, PolyTy.freeTyVars,
      PolyTy.freeTyVarsList, PolyTy.freeCapVars, PolyTy.freeCapVarsList,
      PolyCap.freeCapVars, PolyCap.freeCapVarsList, PolyDataTypes.list,
      dedupFirst, dedup]
  · intro declaration member
    simp [signature] at member
    subst declaration
    exact pairScheme.wellFormed

def pairGenerated : GeneratedPattern :=
  { dual := ⟨.con PatternFormer.list [.var ⟨1⟩],
      DataTypes.list (.var ⟨1⟩)⟩
    bindings := [.var ⟨2⟩]
    hard := [
      .ty (.var ⟨2⟩) (.var ⟨0⟩),
      .cap (.var ⟨2⟩) (.var ⟨0⟩),
      .ty (.var ⟨2⟩) (.var ⟨3⟩),
      .cap (.var ⟨4⟩) (.var ⟨3⟩),
      .ty (DataTypes.list (.var ⟨0⟩)) (DataTypes.list (.var ⟨3⟩)),
      .cap (.con PatternFormer.list [.var ⟨0⟩])
        (.con PatternFormer.list [.var ⟨3⟩]),
      .ty (.var ⟨2⟩) (.var ⟨1⟩),
      .cap (.var ⟨2⟩) (.var ⟨1⟩),
      .ty (DataTypes.list (.var ⟨3⟩)) (DataTypes.list (.var ⟨1⟩)),
      .cap (.con PatternFormer.list [.var ⟨3⟩])
        (.con PatternFormer.list [.var ⟨1⟩])]
    pending := [] }

theorem pair_elaboration_exact :
    elaboratePattern signature [] (pairScheme.instantiate ⟨0, 0⟩).1.fields
      pairDefinition.body [] (pairScheme.instantiate ⟨0, 0⟩).2 =
      some (pairGenerated, ⟨4, 5⟩) := by
  simp [pairDefinition, pairGenerated, pairScheme, signature,
    elaboratePattern, elaboratePatterns, Pattern.extendContext,
    Pattern.dualEquations, Pattern.fieldEquations, elaborate,
    Scheme.mono, Scheme.instantiate, DualScheme.instantiate,
    FrozenSignature.lookupPatternConstructor,
    ListPatternSchemes.cons,
    PolyDual.openBound, PolyCap.openBound, PolyCap.openBoundList,
    PolyTy.openBound, PolyTy.openBoundList, Scheme.boundTyInstance,
    Scheme.boundCapInstance, PolyDataTypes.list, DataTypes.list]

def pairSolution : Subst :=
  { cap := fun _ => .any
    ty := fun _ => .int }

theorem pair_semantic_solution :
    pairGenerated.SemanticSolution pairSolution := by
  simp [GeneratedPattern.SemanticSolution, pairGenerated, pairSolution,
    Solves, Equation.Holds, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
    DataTypes.list]

def pairChecked : pairDefinition.Checked signature where
  scheme := pairScheme
  lookup := by rfl
  arity := by rfl
  generated := pairGenerated
  next := ⟨4, 5⟩
  bodyElaboration := elaboratePattern_sound signature_wellFormed
    pair_elaboration_exact
  solution := pairSolution
  semanticSolution := pair_semantic_solution
  resultCapability_eq := by
    simp [pairGenerated, pairScheme, pairSolution, DualScheme.instantiate,
      PolyDual.openBound, PolyCap.openBound, PolyCap.openBoundList,
      Scheme.boundCapInstance, Cap.apply, Cap.applyList]
  resultTarget_eq := by
    simp [pairGenerated, pairScheme, pairSolution, DualScheme.instantiate,
      PolyDual.openBound, PolyTy.openBound, PolyTy.openBoundList,
      Scheme.boundTyInstance, Ty.apply, Ty.applyList, DataTypes.list,
      PolyDataTypes.list]

def definitions : PatternFunctionDefinitions := [pairDefinition]

theorem definitions_agree_with_checked_source :
    ∃ _checked : pairDefinition.Checked signature,
      definitions.lookup pairName = some pairDefinition := by
  exact ⟨pairChecked, rfl⟩

/-- The executable body table and frozen source signature agree in both
directions: the runtime body is checked, and the sole source declaration has
that runtime implementation. -/
theorem definitions_agree : definitions.Agree signature := by
  refine
    { signatureWellFormed := signature_wellFormed
      namesNodup := by decide
      runtimeChecked := ?_
      sourceImplemented := ?_ }
  · intro definition member
    simp [definitions] at member
    subst definition
    exact ⟨pairChecked⟩
  · intro declaration member
    simp [signature] at member
    subst declaration
    exact ⟨pairDefinition, by simp [definitions], rfl⟩

end TypePM.Source.M4PatternFunctionPairRegression
