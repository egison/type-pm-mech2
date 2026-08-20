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

/-- The current theorem boundary is intentionally strict: even a harmless
identity application awaits closure/application preservation. -/
theorem identity_application_not_in_certified_core :
    ¬ RuntimeSupported (.app (.lam (.var 0)) (.lit 1)) := by
  intro supported
  cases supported

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
  canonicalConditional_runtimeTyping.neverStuck fuel []

theorem canonicalConditional_exact_valueTyping :
    ValueTyping (.int 3) .int := by
  have exactEvaluation :
      evalFuel 4 [] canonicalConditional = .ok (.int 3) := by
    rfl
  have typed := canonicalConditional_runtimeTyping.coreSafety 4 []
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
  append123_runtimeTyping.neverStuck fuel []

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

/-- `map` evaluates closures, so it remains outside this checkpoint until
closure and application preservation are connected to runtime typing. -/
theorem map_not_in_certified_core :
    ¬ RuntimeSupported (.prim PrimOp.map [.lam (.var 0), intList12]) := by
  intro supported
  cases supported

end TypePM.RuntimeTypingRegression
