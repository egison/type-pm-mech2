import TypePM.NoStuck

/-!
# Provenance-protected runtime typing for polymorphic `let`

`RuntimeTyping` deliberately keeps an evaluator-facing `List Ty` context.
Consequently one context entry cannot itself say that a value came from a
generalized source `let`.  This module adds that information in a separate
proof-only Boolean mask.  Only entries marked by the `letPoly` rule may use
`instantiatedVar`; ordinary runtime variables keep exact lookup typing.

The protected relation is intentionally small.  It supplies the structural
forms needed to use one generalized value in applications and tuples, and it
can embed any already certified `RuntimeTyping` subtree.  In particular it
does not add an unrestricted `IsInstance` constructor to `RuntimeTyping` and
does not change runtime contexts to source schemes.
-/

namespace TypePM.Runtime

mutual

/-- Runtime typing with a proof-only mask recording which context entries
were introduced by a generalized source `let`.  The evaluator-facing context
remains `List Ty`; `protected` is erased before evaluation. -/
inductive ProtectedRuntimeTyping :
    (provenance : List Bool) → Source.Expr → Ty →
      (context : List Ty := []) → Prop where
  | runtime
      (typing : RuntimeTyping expression target context) :
      ProtectedRuntimeTyping provenance expression target context
  | instantiatedVar
      (typeLookup : context[index]? = some general)
      (provenanceLookup : provenance[index]? = some true)
      (instantiation : IsInstance general target) :
      ProtectedRuntimeTyping provenance (.var index) target context
  | app
      (function : ProtectedRuntimeTyping provenance functionExpression
        (.fn domain codomain) context)
      (argument : ProtectedRuntimeTyping provenance argumentExpression
        domain context) :
      ProtectedRuntimeTyping provenance
        (.app functionExpression argumentExpression) codomain context
  | tuple
      (items : ProtectedRuntimeTypings provenance expressions targets context) :
      ProtectedRuntimeTyping provenance (.tuple expressions) (.prod targets)
        context
  | letPoly
      (value : ProtectedRuntimeTyping provenance valueExpression general context)
      (body : ProtectedRuntimeTyping (true :: provenance) bodyExpression target
        (general :: context)) :
      ProtectedRuntimeTyping provenance (.letE valueExpression bodyExpression)
        target context

/-- Pointwise protected typing for tuple children. -/
inductive ProtectedRuntimeTypings :
    List Bool → List Source.Expr → List Ty → List Ty → Prop where
  | nil : ProtectedRuntimeTypings provenance [] [] context
  | cons
      (head : ProtectedRuntimeTyping provenance expression target context)
      (tail : ProtectedRuntimeTypings provenance expressions targets context) :
      ProtectedRuntimeTypings provenance (expression :: expressions)
        (target :: targets) context

end

mutual

/-- Preservation and ready progress for provenance-protected runtime typing.
The proof mask has no runtime representation; its only dynamic use is to
justify applying a `ValueTyping` substitution after an environment lookup. -/
theorem ProtectedRuntimeTyping.coreSafety
    (typing : ProtectedRuntimeTyping provenance expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    TypedResult target (evalFuel fuel environment expression) := by
  cases typing with
  | runtime runtimeTyping =>
      exact runtimeTyping.coreSafety fuel environment environmentTyping
  | instantiatedVar typeLookup provenanceLookup instantiation =>
      cases fuel with
      | zero => exact .inl rfl
      | succ fuel =>
          obtain ⟨value, found, valueTyping⟩ :=
            EnvironmentTyping.lookup environmentTyping typeLookup
          rcases instantiation with ⟨substitution, targetEq⟩
          exact .inr ⟨value, by simp [evalFuel, found], by
            rw [← targetEq]
            exact valueTyping.apply substitution⟩
  | app function argument =>
      cases fuel with
      | zero => exact .inl rfl
      | succ applicationFuel =>
          have functionResult :=
            function.coreSafety applicationFuel environment environmentTyping
          rcases functionResult with functionTimeout |
            ⟨functionValue, functionSuccess, functionValueTyping⟩
          · exact .inl (by
              simp [evalFuel, functionTimeout, FuelResult.bind])
          · have argumentResult :=
              argument.coreSafety applicationFuel environment environmentTyping
            rcases argumentResult with argumentTimeout |
              ⟨argumentValue, argumentSuccess, argumentValueTyping⟩
            · exact .inl (by
                simp [evalFuel, functionSuccess, argumentTimeout,
                  FuelResult.bind])
            · cases applicationFuel with
              | zero => exact .inl (by simp [evalFuel])
              | succ bodyFuel =>
                  rcases functionValueTyping.function_canonical with
                    ⟨definitionEnvironment, definitionContext, bodyExpression,
                      functionEq, definitionEnvironmentTyping, bodyTyping⟩ |
                    ⟨definitionEnvironment, definitionContext, bodyExpression,
                      functionEq, definitionEnvironmentTyping, bodyTyping⟩
                  · subst functionValue
                    have bodyResult := bodyTyping.coreSafety bodyFuel
                      (argumentValue :: definitionEnvironment)
                      (.cons argumentValueTyping definitionEnvironmentTyping)
                    rcases bodyResult with bodyTimeout |
                      ⟨value, bodySuccess, valueTyping⟩
                    · exact .inl (by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodyTimeout)
                    · exact .inr ⟨value, by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodySuccess, valueTyping⟩
                  · subst functionValue
                    let closure := Value.recursiveClosure definitionEnvironment
                      bodyExpression
                    have closureTyping :=
                      ValueTyping.recursiveClosure definitionEnvironmentTyping
                        bodyTyping
                    have bodyResult := bodyTyping.coreSafety bodyFuel
                      (argumentValue :: closure :: definitionEnvironment)
                      (.cons argumentValueTyping
                        (.cons closureTyping definitionEnvironmentTyping))
                    rcases bodyResult with bodyTimeout |
                      ⟨value, bodySuccess, valueTyping⟩
                    · exact .inl (by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodyTimeout)
                    · exact .inr ⟨value, by
                        rw [evalFuel.eq_def]
                        simp only
                        rw [functionSuccess, argumentSuccess]
                        exact bodySuccess, valueTyping⟩
  | tuple items =>
      cases fuel with
      | zero => exact .inl rfl
      | succ childFuel =>
          have children := items.coreSafety childFuel environment environmentTyping
          rcases children with timeout | ⟨values, success, childrenTyping⟩
          · exact .inl (by simp [evalFuel, timeout, FuelResult.map])
          · exact .inr ⟨.tuple values, by
              simp [evalFuel, success, FuelResult.map], .tuple childrenTyping⟩
  | letPoly value body =>
      cases fuel with
      | zero => exact .inl rfl
      | succ childFuel =>
          have valueResult :=
            value.coreSafety childFuel environment environmentTyping
          rcases valueResult with valueTimeout |
            ⟨valueResult, valueSuccess, valueTyping⟩
          · exact .inl (by
              simp [evalFuel, valueTimeout, FuelResult.bind])
          · have bodyResult := body.coreSafety childFuel
                (valueResult :: environment)
                (.cons valueTyping environmentTyping)
            rcases bodyResult with bodyTimeout |
              ⟨result, bodySuccess, resultTyping⟩
            · exact .inl (by
                simp [evalFuel, valueSuccess, bodyTimeout, FuelResult.bind])
            · exact .inr ⟨result, by
                simp [evalFuel, valueSuccess, bodySuccess, FuelResult.bind],
                resultTyping⟩

/-- List counterpart of `ProtectedRuntimeTyping.coreSafety`. -/
theorem ProtectedRuntimeTypings.coreSafety
    (typing : ProtectedRuntimeTypings provenance expressions targets context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    TypedResults targets
      (FuelResult.traverse (evalFuel fuel environment) expressions) := by
  cases typing with
  | nil => exact .inr ⟨[], rfl, .nil⟩
  | cons head tail =>
      have headResult := head.coreSafety fuel environment environmentTyping
      rcases headResult with headTimeout |
        ⟨headValue, headSuccess, headTyping⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · have tailResult := tail.coreSafety fuel environment environmentTyping
        rcases tailResult with tailTimeout |
          ⟨tailValues, tailSuccess, tailTyping⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            .cons headTyping tailTyping⟩

end


/-- Provenance-protected runtime typing rules out evaluator `stuck` for every
fuel amount. -/
theorem ProtectedRuntimeTyping.neverStuck
    (typing : ProtectedRuntimeTyping provenance expression target context)
    (fuel : Nat) (environment : ValueEnvironment)
    (environmentTyping : EnvironmentTyping environment context) :
    (evalFuel fuel environment expression).NotStuck :=
  (typing.coreSafety fuel environment environmentTyping).notStuck

end TypePM.Runtime

namespace TypePM.Source

/-- A proof-only source-to-runtime certificate.  Its source component is an
actual relational `PrincipalTyping` witness (and therefore contains an
`Elaborates` derivation with all `letE` closures); its runtime component uses
the protected provenance relation above.  The last field is exactly the
instance closure used by public `Source.Typing`. -/
inductive ProvenancedRuntimeTyping
    (signature : Signature) (expression : Expr) (target : Ty) : Prop where
  | intro {principal : Ty}
      (sourcePrincipal : PrincipalTyping signature [] expression principal)
      (runtimePrincipal :
        Runtime.ProtectedRuntimeTyping [] expression principal [])
      (instantiation : IsInstance principal target) :
      ProvenancedRuntimeTyping signature expression target

namespace ProvenancedRuntimeTyping

/-- Pair an actual relational source principal derivation with its protected
runtime interpretation.  Identity instantiation makes the shared principal
type the public result type. -/
theorem ofPrincipal
    (sourcePrincipal : PrincipalTyping signature [] expression target)
    (runtimePrincipal :
      Runtime.ProtectedRuntimeTyping [] expression target []) :
    ProvenancedRuntimeTyping signature expression target :=
  .intro sourcePrincipal runtimePrincipal ⟨Subst.id, by simp⟩

/-- Erasing the runtime certificate recovers the public declarative source
typing judgment, so this relation is a strengthening of `Source.Typing`, not
an unrelated safety judgment. -/
theorem toSourceTyping
    (typing : ProvenancedRuntimeTyping signature expression target) :
    Typing signature [] expression target := by
  cases typing with
  | intro sourcePrincipal runtimePrincipal instantiation =>
      exact ⟨_, sourcePrincipal, instantiation⟩

/-- Source-to-runtime preservation for the protected polymorphic-`let`
certificate. -/
theorem coreSafety
    (typing : ProvenancedRuntimeTyping signature expression target)
    (fuel : Nat) :
    Runtime.TypedResult target (Runtime.evalFuel fuel [] expression) := by
  cases typing with
  | @intro principal sourcePrincipal runtimePrincipal instantiation =>
  have principalResult := runtimePrincipal.coreSafety fuel [] .nil
  rcases instantiation with ⟨substitution, targetEq⟩
  rcases principalResult with timeout | ⟨value, success, valueTyping⟩
  · exact .inl timeout
  · exact .inr ⟨value, success, by
      rw [← targetEq]
      exact valueTyping.apply substitution⟩

/-- Source-to-runtime no-stuck endpoint for provenance-protected
polymorphic `let`. -/
theorem neverStuck
    (typing : ProvenancedRuntimeTyping signature expression target)
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (typing.coreSafety fuel).notStuck

end ProvenancedRuntimeTyping

namespace Inference

/-- Successful public source inference plus a protected runtime
interpretation yields the source-to-runtime bridge certificate. -/
theorem infer_success_provenancedRuntimeTyping
    {signature : Signature} (wellFormed : signature.WellFormed)
    {expression : Expr} {target : Ty}
    (success : infer signature [] expression = some target)
    (runtimeTyping :
      Runtime.ProtectedRuntimeTyping [] expression target []) :
    ProvenancedRuntimeTyping signature expression target :=
  ProvenancedRuntimeTyping.ofPrincipal
    (infer_success_principalTyping wellFormed success) runtimeTyping

/-- Executable-inference no-stuck endpoint for the protected polymorphic
`let` bridge. -/
theorem infer_neverStuck_provenanced
    {signature : Signature} (wellFormed : signature.WellFormed)
    {expression : Expr} {target : Ty}
    (success : infer signature [] expression = some target)
    (runtimeTyping :
      Runtime.ProtectedRuntimeTyping [] expression target [])
    (fuel : Nat) :
    (Runtime.evalFuel fuel [] expression).NotStuck :=
  (infer_success_provenancedRuntimeTyping wellFormed success runtimeTyping).neverStuck
    fuel

end Inference

end TypePM.Source
