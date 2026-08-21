import TypePM.Source.M5TracedOriginSafety
import TypePM.Source.M5CompletionArchitecture

/-!
# Closing recursive-self trace safety

A recursive closure may be returned as a higher-order result, so induction on
the current evaluator fuel alone is insufficient.  The finite observation
requested from self is instead required to be smaller than the enclosing call
observation.  Well-founded induction on that observation closes the recursive
self while the evaluator still consumes the ordinary predecessor fuel.
-/

namespace TypePM.Runtime

namespace OriginDemand

/-- A well-founded size for finite origin observations.  Call fuel contributes
to the size in addition to the two structurally nested observations. -/
def rank : OriginDemand → Nat
  | .none | .fuel _ | .bool | .int => 1
  | .both left right | .pairOf left right =>
      rank left + rank right + 1
  | .listOf element => rank element + 1
  | .plainCall callFuel argument result =>
      callFuel + rank argument + rank result + 1
termination_by demand => demand

end OriginDemand

/-- The exact condition needed to use well-founded induction for the self
observation selected by a recursive body certificate. -/
def RecursiveSelfDemandGuarded
    (selfDemand : Nat → OriginDemand → OriginDemand → OriginDemand) :
    Prop :=
  ∀ bodyFuel argumentDemand resultDemand,
    (selfDemand bodyFuel argumentDemand resultDemand).rank <
      (OriginDemand.plainCall (bodyFuel + 1) argumentDemand
        resultDemand).rank

/-- A closed recursive closure is trace-safe for every applicable finite
observation once the body certificate selects an applicable, strictly smaller
self observation.  Ordinary and trace-refined body preservation are separate:
the former accepts ordinary arguments, while the latter may rely on the trace
provenance carried by a trace-refined argument. -/
theorem recursiveClosure_tracedSafe_of_guardedSelf
    (environmentTyped : TotalEnvironmentTyping environment context)
    (bodyTyped : TotalRecursiveClosureBodyTyping
      (domain :: .fn domain codomain :: context) body codomain)
    (selfDemand : Nat → OriginDemand → OriginDemand → OriginDemand)
    (selfGuarded : RecursiveSelfDemandGuarded selfDemand)
    (selfApplicable : ∀ bodyFuel argumentDemand resultDemand,
      TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable
        (selfDemand bodyFuel argumentDemand resultDemand)
        (.fn domain codomain))
    (ordinaryBodySafe : ∀ bodyFuel argumentDemand resultDemand argument,
      OriginValueSafe argumentDemand argument domain →
        OriginResultSafe resultDemand codomain
          (evalFuel bodyFuel
            (argument :: Value.recursiveClosure environment body :: environment)
            body))
    (tracedBodySafe : ∀ bodyFuel argumentDemand resultDemand argument,
      TracedOriginValueSafe eventSafe argumentDemand argument domain →
      TracedOriginValueSafe eventSafe
        (selfDemand bodyFuel argumentDemand resultDemand)
        (Value.recursiveClosure environment body) (.fn domain codomain) →
        TracedOriginResultSafe eventSafe resultDemand codomain
          (evalFuel bodyFuel
            (argument :: Value.recursiveClosure environment body :: environment)
            body)
          (evalFuelTrace bodyFuel
            (argument :: Value.recursiveClosure environment body :: environment)
            body)) :
    ∀ demand,
      TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable demand
        (.fn domain codomain) →
      TracedOriginValueSafe eventSafe demand
        (Value.recursiveClosure environment body) (.fn domain codomain) := by
  intro demand
  apply (measure OriginDemand.rank).wf.induction demand
  intro current induction applicable
  cases current with
  | none =>
      simp [TracedOriginValueSafe, OriginValueSafe]
  | fuel index =>
      simp only [TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable]
        at applicable
      cases applicable with
      | zero =>
          simpa only [TracedOriginValueSafe] using
            OriginValueSafe.ofFuel
              (fuelValueSafe_zero (Value.recursiveClosure environment body)
                (.fn domain codomain))
  | both left right =>
      have applicable' :
          TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable left
              (.fn domain codomain) ∧
            TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable right
              (.fn domain codomain) := by
        simpa only
          [TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable] using
          applicable
      simp only [TracedOriginValueSafe]
      constructor
      · apply induction left
        · show left.rank < (OriginDemand.both left right).rank
          simp only [OriginDemand.rank]
          omega
        · exact applicable'.1
      · apply induction right
        · show right.rank < (OriginDemand.both left right).rank
          simp only [OriginDemand.rank]
          omega
        · exact applicable'.2
  | listOf element =>
      simp only [TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable]
        at applicable
      rcases applicable with ⟨elementType, impossible, _⟩
      cases impossible
  | pairOf left right =>
      simp only [TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable]
        at applicable
      rcases applicable with ⟨leftType, rightType, impossible, _⟩
      cases impossible
  | bool =>
      simp only [TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable]
        at applicable
      cases applicable
  | int =>
      simp only [TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable]
        at applicable
      cases applicable
  | plainCall callFuel argumentDemand resultDemand =>
      simp only [TypePM.Source.M5CompletionArchitecture.OriginDemandApplicable]
        at applicable
      rcases applicable with
        ⟨actualDomain, actualCodomain, targetEq, _argumentApplicable,
          _resultApplicable⟩
      have typeEq : actualDomain = domain ∧ actualCodomain = codomain :=
        ⟨(Ty.fn.inj targetEq).1.symm, (Ty.fn.inj targetEq).2.symm⟩
      rcases typeEq with ⟨rfl, rfl⟩
      cases callFuel with
      | zero =>
          simp only [TracedOriginValueSafe]
          refine ⟨?_, _, _, rfl, ?_⟩
          · simp only [OriginValueSafe]
            exact PlainCallValueSafe.zero
          · intro argument _argumentSafe
            constructor
            · exact .inl rfl
            · intro event member
              simp [applyFuelTrace] at member
      | succ bodyFuel =>
          apply TracedOriginValueSafe.recursiveClosure environmentTyped
            bodyTyped
          · intro argument argumentSafe
            exact ordinaryBodySafe bodyFuel argumentDemand resultDemand
              argument argumentSafe
          · intro argument argumentSafe
            apply tracedBodySafe bodyFuel argumentDemand resultDemand argument
              argumentSafe
            apply induction
              (selfDemand bodyFuel argumentDemand resultDemand)
            · exact selfGuarded bodyFuel argumentDemand resultDemand
            · exact selfApplicable bodyFuel argumentDemand resultDemand

end TypePM.Runtime
