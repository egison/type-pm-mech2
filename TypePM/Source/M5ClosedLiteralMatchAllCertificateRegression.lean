import TypePM.Source.M5ClosedLiteralMatchAllCertificate
import TypePM.Source.Paper1FrozenSignatureRuntimeCompatibility
import TypePM.Runtime.MatchAllRegression

/-!
# Regression for the first search-bearing M5 certificate

The fixture is the closed bounded-DFS expression

`matchAll 7 as something with $x -> x`.

Unlike the preceding search-free pair fragment, this regression constructs an
actual search origin from the principal derivation recovered from public M4
inference.  The matching result is proved safe through state erasure and the
two-index search theorem.  Exact execution equations are stated separately and
are not premises of the certificate or safety proofs.
-/

namespace TypePM.Source.M5ClosedLiteralMatchAllCertificateRegression

open TypePM.Runtime
open TypePM.Source.M5CompletionArchitecture
open TypePM.Source.M5ClosedLiteralMatchAllCertificate

def expression : Expr :=
  literalVariableMatchAll 7

theorem expression_fragment : Fragment expression (DataTypes.list .int) := by
  exact .literal 7

theorem expression_supported : Supported expression :=
  ⟨DataTypes.list .int, expression_fragment⟩

theorem expression_mnodeFree : expression.MNodeFree :=
  expression_fragment.mnodeFree

/-- The executable public M4 entry point accepts the fixture. -/
theorem expression_infer :
    M4.infer Paper1FrozenSignature.signature [] expression =
      some (DataTypes.list .int) := by
  simpa [expression] using
    (literalVariable_infer_exact Paper1FrozenSignature.signature 7)

/-- Public inference soundness supplies the declarative source typing. -/
theorem expression_typing :
    M4.Typing Paper1FrozenSignature.signature [] expression
      (DataTypes.list .int) :=
  M4.infer_success_typing Paper1FrozenSignature.wellFormed expression_infer

private theorem signatureReady :
    RuntimeSignatureReady Paper1FrozenSignature.signature :=
  ⟨Paper1FrozenSignature.wellFormed,
    Paper1FrozenSignature.runtimeCompatible.toSignatureCompatible⟩

noncomputable def canonicalDerivation :
    M4.PrincipalTypingDerivation Paper1FrozenSignature.signature [] expression
      (DataTypes.list .int) :=
  M4.canonicalPrincipalTypingDerivation Paper1FrozenSignature.wellFormed
    expression_infer

theorem canonicalCertificate : Certificate canonicalDerivation [] :=
  principalStateErasure canonicalDerivation [] signatureReady
    expression_supported ⟨rfl, rfl⟩

/-- A concrete search obligation issued by successful target and matcher
evaluation.  Its callback fuel, DFS fuel, and logical result index remain
separate. -/
theorem concreteSearchOrigin :
    SearchOrigin canonicalDerivation [] (literalVariableTask 7) [.int]
      2 2 (show fuelIndexedSafetyRelations.SearchDemand from (1 : Nat)) := by
  exact .issued 2 2
    (show fuelIndexedSafetyRelations.SearchDemand from (1 : Nat)) rfl rfl

/-- The nonempty search side of the schema is exercised independently of any
completed-search equation. -/
theorem concreteSearchSafe :
    FuelMatchingSearchResultSafe 1 [.int]
      (runBoundedDfsMatchingSearch 2 2 (literalVariableTask 7)) := by
  exact matchingSearchSafe_of_erasure
    (scope := DerivationSupported)
    (Certificate := Certificate)
    (contextRelation := ClosedRuntimeContextRelation)
    (relations := fuelIndexedSafetyRelations)
    (SearchTask := BoundedDfsMatchingSearchTask)
    (SearchOrigin := SearchOrigin)
    (SearchCertificate := SearchCertificate)
    (runSearch := runBoundedDfsMatchingSearch)
    principalStateErasure matchingStateErasure typedMatchingSearch
    canonicalDerivation [] signatureReady expression_supported ⟨rfl, rfl⟩
    2 2 (show fuelIndexedSafetyRelations.SearchDemand from (1 : Nat))
      concreteSearchOrigin

theorem concreteSearchNeverStuck :
    (runBoundedDfsMatchingSearch 2 2
      (literalVariableTask 7)).NotStuck :=
  concreteSearchSafe.notStuck

/-- Every fuel amount yields timeout or a value; `stuck` is impossible. -/
theorem expression_neverStuck (fuel : Nat) :
    (evalFuel fuel [] expression).NotStuck :=
  closedNoStuck (target := DataTypes.list .int) canonicalDerivation
    signatureReady expression_supported ⟨Subst.id, by simp⟩ fuel

/-- Public static acceptance, a genuine typed matching search, and the
arbitrary-fuel runtime endpoint are visible together. -/
theorem publicInferSearchSafetyAndNoStuck :
    M4.infer Paper1FrozenSignature.signature [] expression =
        some (DataTypes.list .int) ∧
      M4.Typing Paper1FrozenSignature.signature [] expression
        (DataTypes.list .int) ∧
      FuelMatchingSearchResultSafe 1 [.int]
        (runBoundedDfsMatchingSearch 2 2 (literalVariableTask 7)) ∧
      ∀ fuel, (evalFuel fuel [] expression).NotStuck :=
  ⟨expression_infer, expression_typing, concreteSearchSafe,
    expression_neverStuck⟩

/-- Exact search is an independent operational regression, not a premise of
`concreteSearchSafe`. -/
theorem concreteSearch_exact :
    runBoundedDfsMatchingSearch 2 2 (literalVariableTask 7) =
      .ok [[.int 7]] := by
  rfl

/-- Exact whole-expression evaluation is likewise kept outside the safety
certificate. -/
theorem expression_eval_exact :
    evalFuel 3 [] expression = .ok (Value.buildList [.int 7]) := by
  simpa [expression, literalVariableMatchAll,
    Runtime.MatchAllRegression.somethingVariable] using
      Runtime.MatchAllRegression.something_variable_evaluates_body_under_binding

theorem expression_eval_relational :
    Eval [] expression (Value.buildList [.int 7]) :=
  evalFuel_sound expression_eval_exact

end TypePM.Source.M5ClosedLiteralMatchAllCertificateRegression
