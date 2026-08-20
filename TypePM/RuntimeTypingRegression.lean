import TypePM.NoStuck
import TypePM.Source.M3Regression

/-!
# Runtime-typing and safety regressions

The examples exercise the source-to-runtime chain for the certified tuple
core and runtime preservation for the canonical Boolean/addition/conditional
extension.
-/

namespace TypePM.RuntimeTypingRegression

open TypePM.Source TypePM.Runtime

def nestedTuple : Source.Expr :=
  .tuple [.lit 1, .tuple [.lit 2, .lit 3]]

def nestedTupleType : Ty :=
  .prod [.int, .prod [.int, .int]]

theorem nestedTuple_runtimeTyping :
    RuntimeTyping nestedTuple nestedTupleType := by
  exact .tuple (.cons (.lit 1)
    (.cons (.tuple (.cons (.lit 2) (.cons (.lit 3) .nil))) .nil))

theorem nestedTuple_supported : RuntimeSupported nestedTuple :=
  .tuple (.cons .lit
    (.cons (.tuple (.cons .lit (.cons .lit .nil))) .nil))

private theorem unify_nil_exact : unify [] = some Subst.id := by
  unfold unify
  rw [unifyLoop.eq_def]

private theorem close_empty (target : Ty) :
    inferGeneratedUsing unify ⟨target, [], []⟩ =
      some ⟨Subst.id, target⟩ := by
  simp [inferGeneratedUsing, saturateUsing, saturateLoop,
    unify_nil_exact, promoteUnder, residualEquations]

theorem infer_nestedTuple_exact :
    infer Paper1Signature.signature [] nestedTuple = some nestedTupleType := by
  have elaborated :
      elaborateRoot Paper1Signature.signature [] nestedTuple =
        some ⟨nestedTupleType, [], []⟩ := by
    simp [nestedTuple, nestedTupleType, elaborateRoot, elaborate,
      elaborateItems]
  simp [infer, elaborated, close_empty]

theorem nestedTuple_sourceTyping :
    Source.Typing Paper1Signature.signature [] nestedTuple nestedTupleType :=
  Inference.infer_success_typing Paper1Signature.wellFormed
    infer_nestedTuple_exact

/-- The theorem-5.6 bridge recovers the same structural runtime judgment from
the independent public source typing. -/
theorem nestedTuple_state_erasure :
    RuntimeTyping nestedTuple nestedTupleType :=
  nestedTuple_sourceTyping.toRuntimeTyping paper1SignatureCompatible
    nestedTuple_supported

/-- Successful evaluation preserves the nested product type. -/
theorem nestedTuple_typed_result :
    TypedResult nestedTupleType (evalFuel 3 [] nestedTuple) :=
  nestedTuple_sourceTyping.coreSafety paper1SignatureCompatible
    nestedTuple_supported 3

/-- Public inference success rules out runtime `stuck` at every fuel amount. -/
theorem inferred_nestedTuple_neverStuck (fuel : Nat) :
    (evalFuel fuel [] nestedTuple).NotStuck :=
  Inference.infer_neverStuck Paper1Signature.wellFormed
    paper1SignatureCompatible infer_nestedTuple_exact nestedTuple_supported fuel

/-- The preservation endpoint identifies the exact runtime value type. -/
theorem nestedTuple_exact_valueTyping :
    ValueTyping
      (.tuple [.int 1, .tuple [.int 2, .int 3]]) nestedTupleType := by
  have typed := nestedTuple_typed_result
  rcases typed with timeout | ⟨value, success, valueTyping⟩
  · have evaluated :
        evalFuel 3 [] nestedTuple =
          .ok (.tuple [.int 1, .tuple [.int 2, .int 3]]) := by
      rfl
    rw [evaluated] at timeout
    contradiction
  · cases success
    exact valueTyping

/-- The runtime coverage invariant needed by `matchFirst` safety is visible at
the executable boundary: an empty arm list is stuck.  The M4 static
elaborator's exhaustiveness gate rejects this shape. -/
theorem matchFirst_empty_arms_is_stuck :
    evalFuel 3 [] (.matchFirst (.lit 1) .something []) = .stuck := by
  rfl

def identityApplication : Source.Expr :=
  .app (.lam (.var 0)) (.lit 7)

theorem identityApplication_supported :
    RuntimeSupported identityApplication :=
  .app (.lam .var) .lit

theorem identityApplication_runtimeTyping :
    RuntimeTyping identityApplication .int := by
  exact .app (.lam (.var rfl)) (.lit 7)

theorem identityApplication_state_erasure
    (sourceTyping : Source.Typing Paper1Signature.signature []
      identityApplication .int) :
    RuntimeTyping identityApplication .int :=
  sourceTyping.toRuntimeTyping paper1SignatureCompatible
    identityApplication_supported

theorem identityApplication_exact_evaluation :
    evalFuel 3 [] identityApplication = .ok (.int 7) := by
  with_unfolding_all rfl

theorem identityApplication_neverStuck (fuel : Nat) :
    (evalFuel fuel [] identityApplication).NotStuck :=
  identityApplication_runtimeTyping.neverStuck fuel [] .nil

def monomorphicLet : Source.Expr :=
  .letE (.lit 8) (.prim PrimOp.add [.var 0, .lit 1])

theorem monomorphicLet_runtimeTyping :
    RuntimeTyping monomorphicLet .int := by
  exact .letE (.lit 8) (.add (.var rfl) (.lit 1))

theorem monomorphicLet_exact_evaluation :
    evalFuel 3 [] monomorphicLet = .ok (.int 9) := by
  with_unfolding_all rfl

theorem monomorphicLet_neverStuck (fuel : Nat) :
    (evalFuel fuel [] monomorphicLet).NotStuck :=
  monomorphicLet_runtimeTyping.neverStuck fuel [] .nil

/-- Treating every runtime context type as an unrestricted generic type would
not be stable under the structural context substitution used for closures.
Here `α` has `Int` as an instance, but substituting `Bool` for `α` in the
context cannot turn that same `Int` occurrence into an instance of `Bool`.
This is why the remaining polymorphic-`let` bridge needs binding provenance,
not only an `IsInstance` premise on `RuntimeTyping.var`. -/
theorem naivePolymorphicLookup_not_substitutionStable :
    IsInstance (.var ⟨0⟩) .int ∧
      ¬ IsInstance
        ((Ty.var ⟨0⟩).apply
          (Subst.singleTy ⟨0⟩ TypePM.DataTypes.bool))
        (Ty.int.apply
          (Subst.singleTy ⟨0⟩ TypePM.DataTypes.bool)) := by
  constructor
  · refine ⟨Subst.singleTy ⟨0⟩ .int, ?_⟩
    simp [Subst.singleTy, Ty.apply]
  · simp [IsInstance, Subst.singleTy, Ty.apply,
      TypePM.DataTypes.bool, Ty.applyList]

def directFixApplication : Source.Expr :=
  .app (.fixE (.var 0)) (.lit 5)

theorem directFixApplication_runtimeTyping :
    RuntimeTyping directFixApplication .int := by
  exact .app (.fixE (.var rfl)) (.lit 5)

theorem directFixApplication_exact_evaluation :
    evalFuel 3 [] directFixApplication = .ok (.int 5) := by
  with_unfolding_all rfl

theorem directFixApplication_neverStuck (fuel : Nat) :
    (evalFuel fuel [] directFixApplication).NotStuck :=
  directFixApplication_runtimeTyping.neverStuck fuel [] .nil

/-- The function position is itself evaluated: it need not be syntactically
a lambda or a fixed point. -/
def conditionalFunctionApplication : Source.Expr :=
  .app
    (.ifE (.ctor DataCtor.true []) (.lam (.var 0)) (.lam (.var 0)))
    (.lit 11)

theorem conditionalFunctionApplication_runtimeTyping :
    RuntimeTyping conditionalFunctionApplication .int := by
  exact .app (.ifE .boolTrue (.lam (.var rfl)) (.lam (.var rfl))) (.lit 11)

theorem conditionalFunctionApplication_exact_evaluation :
    evalFuel 4 [] conditionalFunctionApplication = .ok (.int 11) := by
  with_unfolding_all rfl

theorem conditionalFunctionApplication_neverStuck (fuel : Nat) :
    (evalFuel fuel [] conditionalFunctionApplication).NotStuck :=
  conditionalFunctionApplication_runtimeTyping.neverStuck fuel [] .nil

theorem capturedVariable_typed_result :
    TypedResult .int (evalFuel 1 [.int 9] (.var 0)) := by
  exact (RuntimeTyping.var (context := [.int]) (target := .int) rfl).coreSafety
    1 [.int 9] (.cons (.int 9) .nil)

theorem true_environmentTyping :
    EnvironmentTyping [.data DataCtor.true []] [TypePM.DataTypes.bool] :=
  .cons .boolTrue .nil

/-- Canonical data is connected through executable inference, source typing,
runtime typing, and the fixed evaluator. -/
theorem true_state_erasure :
    RuntimeTyping Source.M3Regression.trueExpression
      TypePM.DataTypes.bool :=
  Source.M3Regression.true_relational_soundness.toRuntimeTyping
    paper1SignatureCompatible .boolTrue

theorem inferred_true_neverStuck (fuel : Nat) :
    (evalFuel fuel [] Source.M3Regression.trueExpression).NotStuck :=
  Source.Inference.infer_neverStuck Paper1Signature.wellFormed
    paper1SignatureCompatible Source.M3Regression.infer_true_exact
    .boolTrue fuel

def canonicalConditional : Source.Expr :=
  .ifE (.ctor DataCtor.true [])
    (.prim PrimOp.add [.lit 1, .lit 2])
    (.lit 0)

theorem canonicalConditional_runtimeTyping :
    RuntimeTyping canonicalConditional .int := by
  exact .ifE .boolTrue (.add (.lit 1) (.lit 2)) (.lit 0)

theorem canonicalConditional_supported :
    RuntimeSupported canonicalConditional :=
  .ifE .boolTrue (.add .lit .lit) .lit

/-- The state-erasure bridge now covers canonical Boolean data, addition, and
an integer conditional whenever the independent source judgment types this
program. -/
theorem canonicalConditional_state_erasure
    (sourceTyping : Source.Typing Paper1Signature.signature []
      canonicalConditional .int) :
    RuntimeTyping canonicalConditional .int :=
  sourceTyping.toRuntimeTyping
    paper1SignatureCompatible canonicalConditional_supported

/-- The runtime preservation theorem rules out `stuck` for every fuel bound,
not only for the concrete successful run used by the regression. -/
theorem canonicalConditional_neverStuck (fuel : Nat) :
    (evalFuel fuel [] canonicalConditional).NotStuck :=
  canonicalConditional_runtimeTyping.neverStuck fuel [] .nil

theorem canonicalConditional_exact_valueTyping :
    ValueTyping (.int 3) .int := by
  have exactEvaluation :
      evalFuel 4 [] canonicalConditional = .ok (.int 3) := by
    rfl
  have typed := canonicalConditional_runtimeTyping.coreSafety 4 [] .nil
  rcases typed with timeout | ⟨value, success, valueTyping⟩
  · rw [exactEvaluation] at timeout
    contradiction
  · rw [exactEvaluation] at success
    cases success
    exact valueTyping

def intList12 : Source.Expr :=
  .ctor DataCtor.cons [.lit 1,
    .ctor DataCtor.cons [.lit 2, .ctor DataCtor.nil []]]

def intList3 : Source.Expr :=
  .ctor DataCtor.cons [.lit 3, .ctor DataCtor.nil []]

def append123 : Source.Expr :=
  .prim PrimOp.append [intList12, intList3]

def member2 : Source.Expr :=
  .prim PrimOp.member [.lit 2, intList12]

def delete1 : Source.Expr :=
  .prim PrimOp.deleteFirst [.lit 1, intList12]

theorem intList12_runtimeTyping :
    RuntimeTyping intList12 (TypePM.DataTypes.list .int) := by
  exact .listCons (.lit 1) (.listCons (.lit 2) (.listNil .int))

theorem append123_runtimeTyping :
    RuntimeTyping append123 (TypePM.DataTypes.list .int) := by
  exact .append intList12_runtimeTyping
    (.listCons (.lit 3) (.listNil .int))

theorem append123_supported : RuntimeSupported append123 := by
  exact .append
    (.listCons .lit (.listCons .lit .listNil))
    (.listCons .lit .listNil)

theorem append123_exact_evaluation :
    evalFuel 4 [] append123 =
      .ok (Value.buildList [.int 1, .int 2, .int 3]) := by
  with_unfolding_all rfl

theorem append123_neverStuck (fuel : Nat) :
    (evalFuel fuel [] append123).NotStuck :=
  append123_runtimeTyping.neverStuck fuel [] .nil

theorem member2_exact_evaluation :
    evalFuel 4 [] member2 =
      .ok (.data DataCtor.true []) := by
  with_unfolding_all rfl

theorem member2_runtimeTyping :
    RuntimeTyping member2 TypePM.DataTypes.bool := by
  exact .member (.lit 2) intList12_runtimeTyping

theorem delete1_exact_evaluation :
    evalFuel 4 [] delete1 = .ok (Value.buildList [.int 2]) := by
  with_unfolding_all rfl

theorem delete1_runtimeTyping :
    RuntimeTyping delete1 (TypePM.DataTypes.list .int) := by
  exact .deleteFirst (.lit 1) intList12_runtimeTyping

def incrementList : Source.Expr :=
  .prim PrimOp.map
    [.lam (.prim PrimOp.add [.var 0, .lit 1]), intList12]

theorem incrementList_supported : RuntimeSupported incrementList :=
  .map (.lam (.add .var .lit))
    (.listCons .lit (.listCons .lit .listNil))

theorem incrementList_runtimeTyping :
    RuntimeTyping incrementList (TypePM.DataTypes.list .int) := by
  exact .map (.lam (.add (.var rfl) (.lit 1))) intList12_runtimeTyping

theorem incrementList_state_erasure
    (sourceTyping : Source.Typing Paper1Signature.signature []
      incrementList (TypePM.DataTypes.list .int)) :
    RuntimeTyping incrementList (TypePM.DataTypes.list .int) :=
  sourceTyping.toRuntimeTyping paper1SignatureCompatible incrementList_supported

theorem incrementList_exact_evaluation :
    evalFuel 5 [] incrementList =
      .ok (Value.buildList [.int 2, .int 3]) := by
  with_unfolding_all rfl

theorem incrementList_neverStuck (fuel : Nat) :
    (evalFuel fuel [] incrementList).NotStuck :=
  incrementList_runtimeTyping.neverStuck fuel [] .nil

end TypePM.RuntimeTypingRegression
