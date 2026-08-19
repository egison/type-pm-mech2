import TypePM.Source.Elaboration

/-!
# M3 source regression tests

These tests connect the finite paper signature to source elaboration.  They
cover every newly introduced source form, rejected lookup and arity cases,
an unsatisfiable generated constraint, and the relational soundness endpoint
for successful inference.
-/

namespace TypePM.Source.M3Regression

set_option linter.unusedSimpArgs false

def paper : Signature := Paper1Signature.signature

def trueExpression : Expr := .ctor DataCtor.true []
def falseExpression : Expr := .ctor DataCtor.false []
def nilExpression : Expr := .ctor DataCtor.nil []
def consExpression : Expr :=
  .ctor DataCtor.cons [.lit 1, .ctor DataCtor.nil []]
def addExpression : Expr := .prim PrimOp.add [.lit 1, .lit 2]
def conditionalExpression : Expr :=
  .ifE (.ctor DataCtor.true []) (.lit 1) (.lit 2)

private theorem unify_nil_exact : unify [] = some Subst.id := by
  unfold unify
  rw [unifyLoop.eq_def]

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, eliminatedVariable?, unificationVars,
        Equation.unificationVars, Ty.unificationVars,
        Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, Ty.nodeCount, Ty.nodeCountList,
        Cap.nodeCount, Cap.nodeCountList,
        Ty.occursTy, Ty.occursTyList, Cap.occurs, Cap.occursList,
        Equation.apply, Ty.apply, Ty.applyList, Cap.apply, Cap.applyList,
        Subst.singleTy, Subst.singleCap, Subst.compose, Subst.id])

private theorem close_empty (target : Ty) :
    inferGeneratedUsing unify ⟨target, [], []⟩ =
      some ⟨Subst.id, target⟩ := by
  simp [inferGeneratedUsing, saturateUsing, saturateLoop,
    unify_nil_exact, promoteUnder, residualEquations]

private theorem boolTrue_callArity :
    ConstructorSchemes.boolTrue.callArity = 0 := rfl

private theorem boolFalse_callArity :
    ConstructorSchemes.boolFalse.callArity = 0 := rfl

private theorem listNil_callArity :
    ConstructorSchemes.listNil.callArity = 0 := rfl

private theorem listCons_callArity :
    ConstructorSchemes.listCons.callArity = 2 := rfl

private theorem add_callArity : PrimitiveSchemes.add.callArity = 2 := rfl

private theorem conditional_callArity : conditionalScheme.callArity = 3 := rfl

private theorem elaborate_true_exact :
    elaborateRoot paper [] trueExpression =
      some ⟨TypePM.DataTypes.bool, [], []⟩ := by
  simp [paper, trueExpression, elaborateRoot, elaborate, elaborateCall,
    Paper1Signature.lookup_true, boolTrue_callArity,
    ConstructorSchemes.boolTrue, PolyDataTypes.bool, Scheme.instantiate]
  constructor <;> rfl

theorem infer_true_exact :
    infer paper [] trueExpression = some TypePM.DataTypes.bool := by
  simp [infer, elaborate_true_exact, close_empty]

theorem infer_false_exact :
    infer paper [] falseExpression = some TypePM.DataTypes.bool := by
  have elaborates : elaborateRoot paper [] falseExpression =
      some ⟨TypePM.DataTypes.bool, [], []⟩ := by
    simp [paper, falseExpression, elaborateRoot, elaborate, elaborateCall,
      Paper1Signature.lookup_false, boolFalse_callArity,
      ConstructorSchemes.boolFalse, PolyDataTypes.bool, Scheme.instantiate]
    constructor <;> rfl
  simp [infer, elaborates, close_empty]

theorem infer_nil_exact :
    infer paper [] nilExpression =
      some (TypePM.DataTypes.list (.var ⟨0⟩)) := by
  have elaborates : elaborateRoot paper [] nilExpression =
      some ⟨TypePM.DataTypes.list (.var ⟨0⟩), [], []⟩ := by
    simp [paper, nilExpression, elaborateRoot, elaborate, elaborateCall,
      Paper1Signature.lookup_data_nil, listNil_callArity,
      ConstructorSchemes.listNil, PolyDataTypes.list, Scheme.instantiate]
    constructor <;> rfl
  simp [infer, elaborates, close_empty]

theorem elaborate_cons_succeeds :
    elaborateRoot paper [] consExpression ≠ none := by
  simp [paper, consExpression, elaborateRoot, elaborate, elaborateCall,
    Paper1Signature.lookup_data_cons, Paper1Signature.lookup_data_nil,
    listCons_callArity, listNil_callArity, ConstructorSchemes.listCons,
    ConstructorSchemes.listNil, PolyDataTypes.list, Scheme.instantiate]
  constructor <;> rfl

theorem elaborate_add_succeeds :
    elaborateRoot paper [] addExpression ≠ none := by
  simp [paper, addExpression, elaborateRoot, elaborate, elaborateCall,
    Paper1Signature.lookup_primitive, add_callArity,
    PrimitiveSchemes.add, Scheme.instantiate]
  rfl

theorem elaborate_conditional_succeeds :
    elaborateRoot paper [] conditionalExpression ≠ none := by
  simp [paper, conditionalExpression, elaborateRoot, elaborate,
    elaborateCall,
    Paper1Signature.lookup_true, boolTrue_callArity,
    conditional_callArity, ConstructorSchemes.boolTrue,
    conditionalScheme, PolyDataTypes.bool, Scheme.instantiate]
  constructor <;> rfl

/-- A signature without declarations makes both declaration lookups fail. -/
def emptySignature : Signature :=
  { dataFormers := []
    dataConstructors := []
    patternFormers := []
    patternConstructors := []
    primitives := [] }

theorem missing_constructor_lookup_rejected :
    infer emptySignature [] trueExpression = none := by
  simp [infer, elaborateRoot, elaborate, trueExpression, emptySignature,
    Signature.lookupDataConstructor]

theorem missing_primitive_lookup_rejected :
    infer emptySignature [] addExpression = none := by
  simp [infer, elaborateRoot, elaborate, addExpression, emptySignature,
    Signature.lookupPrimitive]

theorem constructor_arity_mismatch_rejected :
    infer paper [] (.ctor DataCtor.true [.lit 1]) = none := by
  simp [infer, paper, elaborateRoot, elaborate,
    Paper1Signature.lookup_true, boolTrue_callArity]

theorem primitive_arity_mismatch_rejected :
    infer paper [] (.prim PrimOp.add [.lit 1]) = none := by
  simp [infer, paper, elaborateRoot, elaborate,
    Paper1Signature.lookup_primitive, add_callArity]

private def mismatchGenerated : Generated :=
  { target := .var ⟨3⟩
    hard := [
      .ty (.fn .int (.fn .int .int))
        (.fn (.var ⟨0⟩) (.var ⟨1⟩)),
      .ty (.var ⟨1⟩) (.fn (.var ⟨2⟩) (.var ⟨3⟩))]
    pending := [
      ⟨TypePM.DataTypes.bool, .var ⟨0⟩⟩,
      ⟨.int, .var ⟨2⟩⟩] }

private theorem elaborate_mismatch_exact :
    elaborateRoot paper []
      (.prim PrimOp.add [.ctor DataCtor.true [], .lit 2]) =
        some mismatchGenerated := by
  simp [paper, mismatchGenerated, elaborateRoot, elaborate, elaborateCall,
    Paper1Signature.lookup_primitive, Paper1Signature.lookup_true,
    add_callArity, boolTrue_callArity, PrimitiveSchemes.add,
    ConstructorSchemes.boolTrue, PolyDataTypes.bool, Scheme.instantiate,
    Generated.fromApp]
  constructor
  · rfl
  · refine ⟨⟨4, 0⟩, ?_⟩
    simp only [Scheme.callArity]
    rfl

private theorem close_mismatch_none :
    inferGeneratedUsing unify mismatchGenerated = none := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [mismatchGenerated]
  compute_unification
  simp [promoteUnder, Ty.couldSpecial, Ty.mayBecomeMatcher,
    Ty.mayBecomeMatcherItems, Ty.mayBecomeMatcherProduct,
    Ty.mayBecomeExpectedMatcher, Ty.mayBecomeExpectedSlot,
    Ty.apply, Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, TypePM.DataTypes.bool]
  simp only [saturateLoop]
  compute_unification

theorem primitive_type_mismatch_rejected :
    infer paper []
      (.prim PrimOp.add [.ctor DataCtor.true [], .lit 2]) = none := by
  simp [infer, elaborate_mismatch_exact, close_mismatch_none]

/-- Executable success is connected to the independent relational source
typing judgment under the paper signature's well-formedness proof. -/
theorem true_relational_soundness :
    Typing paper [] trueExpression TypePM.DataTypes.bool :=
  Inference.infer_success_typing Paper1Signature.wellFormed infer_true_exact

theorem cons_relational_soundness :
    ∀ {target}, infer paper [] consExpression = some target →
      Typing paper [] consExpression target :=
  fun success =>
    Inference.infer_success_typing Paper1Signature.wellFormed success

end TypePM.Source.M3Regression
