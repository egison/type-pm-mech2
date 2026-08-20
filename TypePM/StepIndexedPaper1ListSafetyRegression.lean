import TypePM.StepIndexedClosureSafety
import TypePM.Source.M4Paper1RecursiveClosureTotalTyping

/-!
# Step-indexed safety of the Paper 1 list constructor

The concrete recursive closure is proved safe without quantifying over an
unrelated structurally typed environment.  Its self entry is used only at a
strictly smaller index.  Applying it to `something` produces the actual list
matcher closure with the concrete two-value captured environment.
-/

namespace TypePM.StepIndexedPaper1ListSafetyRegression

open Runtime Source
open Source.Paper1Programs
open Source.MatcherTyping.M4Paper1RecursiveSafetyBoundaryRegression
open Source.MatcherTyping.M4Paper1RecursiveClosureTotalTyping

/-- Call-site specialization selected by applying the public List matcher
constructor to `something : Matcher Any Int`. -/
def concreteListSpecialization : Subst :=
  Subst.compose (Subst.singleTy ⟨44⟩ .int)
    (Subst.singleCap ⟨10⟩ .any)

def listDomain : Ty :=
  .slot (.var ⟨10⟩) (.var ⟨44⟩)

def listCodomain : Ty :=
  .matcher (.con PatternFormer.list [.var ⟨10⟩])
    (DataTypes.list (.var ⟨44⟩))

def concreteListDomain : Ty := .slot .any .int

def concreteListCodomain : Ty :=
  .matcher (.con PatternFormer.list [.any]) (DataTypes.list .int)

theorem concreteListSpecialization_domain :
    listDomain.apply concreteListSpecialization = concreteListDomain := by
  rfl

theorem concreteListSpecialization_codomain :
    listCodomain.apply concreteListSpecialization = concreteListCodomain := by
  rfl

/-- A principal closed matcher-root fix remains totally typed after any
call-site postcomposition of its semantic solution. -/
theorem principalMatcherFix_totalValueTyping_postcompose
    (typing : M4.PrincipalTyping Paper1FrozenSignature.signature []
      (.fixE (.matcher clauses)) target)
    (post : Subst) :
    TotalValueTyping (Value.recursiveClosure [] (.matcher clauses))
      (target.apply post) := by
  rcases typing with ⟨derivation⟩
  rcases derivation.elaboration with ⟨fuel, fuelDerivation⟩
  let principalSolution := derivation.closure.substitution
  let solution := Subst.compose post principalSolution
  have principalSemantic : derivation.generated.SemanticSolution
      principalSolution :=
    TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution
      derivation.closure
  have semantic : derivation.generated.SemanticSolution solution := by
    exact principalSemantic.postcompose post
  have closureTyped := matcherFixElaboration_totalValueTyping fuelDerivation
    semantic (MonomorphicContextCompatible.nil) (TotalValueTypings.nil)
  rw [derivation.target_eq]
  simpa [PrincipalBlockClosure.target, solution, principalSolution,
    Ty.apply_compose] using closureTyped

/-- The actual recursive List constructor at the concrete type demanded by
the `something` call site. -/
theorem listRecursiveClosure_concreteTotalValueTyping :
    TotalValueTyping listRecursiveClosure
      (.fn concreteListDomain concreteListCodomain) := by
  have specialized := principalMatcherFix_totalValueTyping_postcompose
    (M4.infer_success_principalTyping Paper1FrozenSignature.wellFormed
      M4Paper1ListExactRegression.infer_exact)
    concreteListSpecialization
  change TotalValueTyping listRecursiveClosure
    ((Ty.fn listDomain listCodomain).apply concreteListSpecialization)
      at specialized
  simpa only [Ty.apply, concreteListSpecialization_domain,
    concreteListSpecialization_codomain] using specialized

theorem listRecursiveClosure_concreteTotalPlainTyping :
    TotalPlainValueTyping listRecursiveClosure
      (.fn concreteListDomain concreteListCodomain) :=
  .existing listRecursiveClosure_concreteTotalValueTyping

theorem listRecursiveClosure_concreteBodyTyping :
    TotalRecursiveClosureBodyTyping
      [concreteListDomain,
        .fn concreteListDomain concreteListCodomain]
      (.matcher listMatcherClauses) concreteListCodomain := by
  rcases listRecursiveClosure_concreteTotalPlainTyping.function_canonical with
    ⟨environment, context, body, equality, _, _⟩ |
    ⟨environment, context, body, equality, environmentTyped, bodyTyped⟩
  · simp [listRecursiveClosure, Value.recursiveClosure,
      Value.plainClosure] at equality
  · have environment_eq : environment = [] := by
      simpa [listRecursiveClosure, Value.recursiveClosure] using
        congrArg (fun value => match value with
          | .closure .recursive captured _ => captured
          | _ => []) equality.symm
    subst environment
    cases environmentTyped
    have body_eq : body = .matcher listMatcherClauses := by
      simpa [listRecursiveClosure, Value.recursiveClosure] using
        congrArg (fun value => match value with
          | .closure .recursive _ closureBody => closureBody
          | _ => .lit 0) equality.symm
    subst body
    exact bodyTyped

theorem something_concreteListDomain_fuelValueSafe (fuel : Nat) :
    FuelValueSafe fuel .something concreteListDomain := by
  exact fuelValueSafe_somethingSlot .int fuel

mutual

  /-- Step-indexed safety of the actual recursive List constructor after the
  public principal solution is specialized at the concrete call site. -/
  theorem listRecursiveClosure_concreteFuelValueSafe :
      ∀ fuel, FuelValueSafe fuel listRecursiveClosure
        (.fn concreteListDomain concreteListCodomain)
    | 0 => fuelValueSafe_zero _ _
    | fuel + 1 => by
        exact .function
          (listRecursiveClosure_concreteFuelValueSafe fuel)
          listRecursiveClosure_concreteTotalPlainTyping (by
            intro argument argumentSafe
            cases fuel with
            | zero => exact .inl rfl
            | succ residual =>
                exact .inr ⟨.matcherV [argument, listRecursiveClosure]
                  listMatcherClauses listMatcherClauses, rfl,
                  listMatcherClosure_concreteFuelValueSafe argument
                    (residual + 1) argumentSafe⟩)

  /-- The exact generated matcher value retains the concrete argument and
  recursive self entry at the preceding index. -/
  theorem listMatcherClosure_concreteFuelValueSafe (argument : Value) :
      ∀ fuel, FuelValueSafe fuel argument concreteListDomain →
        FuelValueSafe fuel
          (.matcherV [argument, listRecursiveClosure]
            listMatcherClauses listMatcherClauses)
          concreteListCodomain
    | 0, _ => fuelValueSafe_zero _ _
    | fuel + 1, argumentSafe => by
        exact .generatedMatcher
          (listMatcherClosure_concreteFuelValueSafe argument fuel
            argumentSafe.previous)
          rfl rfl (by
            intro index target found
            cases index with
            | zero =>
                simp at found
                subst target
                exact ⟨argument, rfl, argumentSafe.previous⟩
            | succ index =>
                cases index with
                | zero =>
                    simp at found
                    subst target
                    exact ⟨listRecursiveClosure, rfl,
                      listRecursiveClosure_concreteFuelValueSafe fuel⟩
                | succ index => simp at found)
          listRecursiveClosure_concreteBodyTyping

end


/-- With two or more units of application fuel, the actual `something` call
constructs the exact user matcher closure rather than timing out. -/
theorem listRecursiveClosure_something_application_exact (fuel : Nat) :
    applyFuel (fuel + 2) listRecursiveClosure .something =
      .ok (.matcherV [.something, listRecursiveClosure]
        listMatcherClauses listMatcherClauses) := by
  rfl

theorem listRecursiveClosure_something_application_safe (fuel : Nat) :
    FuelResultSafe (fuel + 1) concreteListCodomain
      (applyFuel (fuel + 2) listRecursiveClosure .something) := by
  exact .inr ⟨_, listRecursiveClosure_something_application_exact fuel,
    listMatcherClosure_concreteFuelValueSafe .something (fuel + 1)
      (something_concreteListDomain_fuelValueSafe (fuel + 1))⟩

theorem listRecursiveClosure_something_application_neverStuck (fuel : Nat) :
    (applyFuel (fuel + 2) listRecursiveClosure .something).NotStuck :=
  (listRecursiveClosure_something_application_safe fuel).notStuck

end TypePM.StepIndexedPaper1ListSafetyRegression
