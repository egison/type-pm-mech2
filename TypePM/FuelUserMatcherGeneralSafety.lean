import TypePM.OriginDemandSafety
import TypePM.UserMatcherGeneralSafety

/-!
# Demand-indexed safety for user-matcher clause steps

This module lifts capture evaluation and one arm/clause step from structural
`ValueTyping` to the fuel-indexed logical relation.  Embedded expression
certificates choose their input demands before runtime values are supplied.
Callers remain responsible for proving those demands for the actual matcher
environments; recursive search-branch composition is a later boundary.
-/

namespace TypePM.Runtime

open TypePM.Source

namespace OriginEnvironmentSafe

theorem bothLeft
    (safe : OriginEnvironmentSafe
      (OriginEnvironmentDemand.both left right) values targets) :
    OriginEnvironmentSafe left values targets := by
  refine ⟨safe.1, ?_⟩
  intro position target value targetFound valueFound
  exact (safe.2 position target value targetFound valueFound).bothLeft

theorem bothRight
    (safe : OriginEnvironmentSafe
      (OriginEnvironmentDemand.both left right) values targets) :
    OriginEnvironmentSafe right values targets := by
  refine ⟨safe.1, ?_⟩
  intro position target value targetFound valueFound
  exact (safe.2 position target value targetFound valueFound).bothRight

end OriginEnvironmentSafe

/-- Certificates for a source-ordered capture list.  Every expression is
evaluated in the same environment; their independently selected input
demands are combined pointwise with `both`. -/
inductive FuelCaptureCertificates
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (operationalFuel resultFuel : Nat)
    (bindingTypes environmentTypes : List Ty) :
    List Source.Expr → List Ty → OriginEnvironmentDemand → Prop where
  | nil : FuelCaptureCertificates Certificate operationalFuel resultFuel
      bindingTypes environmentTypes [] [] OriginEnvironmentDemand.none
  | cons
      (head : Certificate operationalFuel bindingTypes environmentTypes
        expression target (.fuel (resultFuel + 1)) headInput)
      (tail : FuelCaptureCertificates Certificate operationalFuel resultFuel
        bindingTypes environmentTypes expressions targets tailInput) :
      FuelCaptureCertificates Certificate operationalFuel resultFuel
        bindingTypes environmentTypes (expression :: expressions)
        (target :: targets) (OriginEnvironmentDemand.both headInput tailInput)

/-- Demand-indexed capture traversal.  Successful captures retain positive
fuel safety pointwise and preserve source order. -/
theorem FuelCaptureCertificates.traverse_fuelSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (environmentSafe : OriginEnvironmentSafe inputDemand
      (bindings ++ environment) (bindingTypes ++ environmentTypes))
    (certificates : FuelCaptureCertificates Certificate operationalFuel
      resultFuel bindingTypes environmentTypes expressions targets inputDemand) :
    FuelResult.traverse
        (evaluate operationalFuel (bindings ++ environment)) expressions = .timeout ∨
      ∃ values,
        FuelResult.traverse
          (evaluate operationalFuel (bindings ++ environment)) expressions =
            .ok values ∧
        FuelEnvironmentSafe (resultFuel + 1) values targets := by
  induction certificates with
  | nil => exact .inr ⟨[], rfl, FuelEnvironmentSafe.nil _⟩
  | @cons expression target expressions targets headInput tailInput head tail ih =>
      have headResult := evalSafe head environmentSafe.bothLeft
      rcases headResult with headTimeout | ⟨headValue, headSuccess, headSafe⟩
      · exact .inl (by simp [FuelResult.traverse, headTimeout])
      · rcases ih environmentSafe.bothRight with tailTimeout |
          ⟨tailValues, tailSuccess, tailSafe⟩
        · exact .inl (by
            simp [FuelResult.traverse, headSuccess, tailTimeout,
              FuelResult.bind, FuelResult.map])
        · exact .inr ⟨headValue :: tailValues, by
            simp [FuelResult.traverse, headSuccess, tailSuccess,
              FuelResult.bind, FuelResult.map],
            FuelEnvironmentSafe.cons headSafe.toFuel tailSafe⟩

/-- Fuel-indexed safety of one decoded decomposition candidate. -/
abbrev FuelHoleValuesSafe (fuel : Nat) (holes : List Dual)
    (values : List Value) : Prop :=
  FuelEnvironmentSafe fuel values (Dual.targets holes)

/-- Pointwise safety for all decoded decomposition candidates. -/
inductive FuelHoleDecompositionsSafe (fuel : Nat) (holes : List Dual) :
    List (List Value) → Prop where
  | nil : FuelHoleDecompositionsSafe fuel holes []
  | cons
      (head : FuelHoleValuesSafe fuel holes values)
      (tail : FuelHoleDecompositionsSafe fuel holes decompositions) :
      FuelHoleDecompositionsSafe fuel holes (values :: decompositions)

/-- Recover a fuel-safe heterogeneous value list from its positive product
layer. -/
theorem PositiveValueSafes.toFuelEnvironmentSafe
    : ∀ {values targets},
      PositiveValueSafes fuel (FuelValueSafe fuel) values targets →
        FuelEnvironmentSafe (fuel + 1) values targets
  | [], [], _ => FuelEnvironmentSafe.nil _
  | value :: values, target :: targets, safe => by
      cases safe with
      | cons head tail =>
          exact FuelEnvironmentSafe.cons head
            (PositiveValueSafes.toFuelEnvironmentSafe tail)

/-- Positive fuel safety validates the zero/one/many product decoder. -/
theorem FuelValueSafe.decodeRuntimeProduct
    (safe : FuelValueSafe (fuel + 1) value (runtimeProductTarget targets)) :
    ∃ values,
      decodeProduct targets.length value = some values ∧
      FuelEnvironmentSafe (fuel + 1) values targets := by
  cases targets with
  | nil =>
      cases safe with
      | tuple _ items =>
          cases items
          exact ⟨[], rfl, FuelEnvironmentSafe.nil _⟩
  | cons first rest =>
      cases rest with
      | nil =>
          exact ⟨[value], rfl,
            FuelEnvironmentSafe.cons safe (FuelEnvironmentSafe.nil _)⟩
      | cons second rest =>
          cases safe with
          | tuple _ items =>
              have valuesSafe := items.toFuelEnvironmentSafe
              exact ⟨_, decodeProduct_many_exact (by simp) _ valuesSafe.1,
                valuesSafe⟩

/-- Positive fuel safety validates the decomposition element decoder. -/
theorem FuelValueSafe.decodeHoleProduct
    (safe : FuelValueSafe (fuel + 1) value
      (runtimeHoleProductTarget holes)) :
    ∃ values,
      decodeProduct holes.length value = some values ∧
      FuelHoleValuesSafe (fuel + 1) holes values := by
  cases holes with
  | nil =>
      change ∃ values,
        decodeProduct 0 value = some values ∧
        FuelEnvironmentSafe (fuel + 1) values []
      simpa [runtimeHoleProductTarget, runtimeProductTarget] using
        (FuelValueSafe.decodeRuntimeProduct
          (targets := []) (value := value) safe)
  | cons first rest =>
      cases rest with
      | nil =>
          change ∃ values,
            decodeProduct 1 value = some values ∧
            FuelEnvironmentSafe (fuel + 1) values [first.target]
          have decoded := FuelValueSafe.decodeRuntimeProduct
            (targets := [first.target]) (value := value) safe
          simpa using decoded
      | cons second rest =>
          change ∃ values,
            decodeProduct (first :: second :: rest).length value = some values ∧
            FuelEnvironmentSafe (fuel + 1) values
              (Dual.targets (first :: second :: rest))
          have decoded := FuelValueSafe.decodeRuntimeProduct
            (targets := Dual.targets (first :: second :: rest))
              (value := value) safe
          have lengths : (Dual.targets (first :: second :: rest)).length =
              (first :: second :: rest).length := by
            simp [Dual.targets]
          rw [lengths] at decoded
          exact decoded

theorem PositiveListValueSafes.decodeHoleProducts
    : ∀ {values},
      PositiveListValueSafes fuel (FuelValueSafe fuel)
        values (runtimeHoleProductTarget holes) →
      ∃ decompositions,
        List.mapM (decodeProduct holes.length) values = some decompositions ∧
        FuelHoleDecompositionsSafe (fuel + 1) holes decompositions
  | [], _ => ⟨[], rfl, .nil⟩
  | value :: values, safe => by
      cases safe with
      | cons head tail =>
          have headFuel : FuelValueSafe (fuel + 1) value
              (runtimeHoleProductTarget holes) := head
          obtain ⟨headValues, headDecoded, headSafe⟩ :=
            headFuel.decodeHoleProduct
          obtain ⟨tailValues, tailDecoded, tailSafe⟩ :=
            PositiveListValueSafes.decodeHoleProducts tail
          exact ⟨headValues :: tailValues, by
            simp [List.mapM_cons, headDecoded, tailDecoded],
            .cons headSafe tailSafe⟩

/-- A positive fuel-safe canonical list of hole products passes the complete
decomposition decoder. -/
theorem FuelValueSafe.decodeDecompositions
    (safe : FuelValueSafe (fuel + 1) value
      (DataTypes.list (runtimeHoleProductTarget holes))) :
    ∃ decompositions,
      decodeDecompositions holes.length value = some decompositions ∧
      FuelHoleDecompositionsSafe (fuel + 1) holes decompositions := by
  generalize targetEq : DataTypes.list (runtimeHoleProductTarget holes) = target
    at safe
  cases safe <;>
    simp_all [DataTypes.list, DataTypes.bool]
  rename_i element _ items
  have element_eq : element = runtimeHoleProductTarget holes := by
    exact targetEq.symm
  subst element
  simp only [TypePM.Runtime.decodeDecompositions,
    Value.viewList_buildList]
  exact items.decodeHoleProducts

namespace FuelEnvironmentSafe

theorem head
    (safe : FuelEnvironmentSafe fuel (value :: values) (target :: targets)) :
    FuelValueSafe fuel value target := by
  obtain ⟨found, foundEq, foundSafe⟩ := safe.2 0 target (by simp)
  simp at foundEq
  subst found
  exact foundSafe

theorem tail
    (safe : FuelEnvironmentSafe fuel (value :: values) (target :: targets)) :
    FuelEnvironmentSafe fuel values targets := by
  refine ⟨by simpa using safe.1, ?_⟩
  intro index target found
  simpa only [List.getElem?_cons_succ] using
    safe.2 (index + 1) target (by
      simpa only [List.getElem?_cons_succ] using found)

end FuelEnvironmentSafe

/-- Fuel-indexed delegated atom safety. -/
inductive FuelDelegatedMatchingAtomsSafe (fuel : Nat) :
    List MatchingAtom → List Dual → Prop where
  | nil : FuelDelegatedMatchingAtomsSafe fuel [] []
  | cons
      (matcher : FuelValueSafe fuel matcherValue
        (.slot hole.capability hole.target))
      (target : FuelValueSafe fuel targetValue hole.target)
      (tail : FuelDelegatedMatchingAtomsSafe fuel atoms holes) :
      FuelDelegatedMatchingAtomsSafe fuel
        (⟨pattern, matcherValue, targetValue⟩ :: atoms) (hole :: holes)

inductive FuelDelegatedMatchingBranchesSafe (fuel : Nat) (holes : List Dual) :
    MatchingBranches → Prop where
  | nil : FuelDelegatedMatchingBranchesSafe fuel holes []
  | cons
      (head : FuelDelegatedMatchingAtomsSafe fuel branch holes)
      (tail : FuelDelegatedMatchingBranchesSafe fuel holes branches) :
      FuelDelegatedMatchingBranchesSafe fuel holes (branch :: branches)

inductive FuelMatcherArmResultSafe (fuel : Nat) (holes : List Dual) :
    DispatchResult MatchingBranches → Prop where
  | miss : FuelMatcherArmResultSafe fuel holes .miss
  | hit
      (branches : FuelDelegatedMatchingBranchesSafe fuel holes result) :
      FuelMatcherArmResultSafe fuel holes (.hit result)

inductive FuelMatcherClauseResultSafe (fuel : Nat) :
    DispatchResult MatchingBranches → Prop where
  | miss : FuelMatcherClauseResultSafe fuel .miss
  | hit
      (branches : FuelDelegatedMatchingBranchesSafe fuel holes result) :
      FuelMatcherClauseResultSafe fuel (.hit result)

theorem zipMatchingAtoms_fuelSafe
    (length : patterns.length = holes.length)
    (matchersSafe : FuelEnvironmentSafe fuel matcherValues
      (holes.map (fun hole => .slot hole.capability hole.target)))
    (targetsSafe : FuelHoleValuesSafe fuel holes targetValues) :
    ∃ atoms,
      zipMatchingAtoms patterns matcherValues targetValues = some atoms ∧
      FuelDelegatedMatchingAtomsSafe fuel atoms holes := by
  induction holes generalizing patterns matcherValues targetValues with
  | nil =>
      have matcherNil : matcherValues = [] := by
        exact List.eq_nil_of_length_eq_zero (by simpa using matchersSafe.1)
      have targetNil : targetValues = [] := by
        exact List.eq_nil_of_length_eq_zero (by simpa [Dual.targets] using targetsSafe.1)
      subst matcherValues
      subst targetValues
      simp at length
      subst patterns
      exact ⟨[], rfl, .nil⟩
  | cons hole holes ih =>
      cases patterns with
      | nil => simp at length
      | cons pattern patterns =>
          cases matcherValues with
          | nil =>
              have impossible := matchersSafe.1
              simp at impossible
          | cons matcherValue matcherValues =>
              cases targetValues with
              | nil =>
                  have impossible := targetsSafe.1
                  simp [Dual.targets] at impossible
              | cons targetValue targetValues =>
                  have matcherHead : FuelValueSafe fuel matcherValue
                      (.slot hole.capability hole.target) := by
                    exact matchersSafe.head
                  have targetHead : FuelValueSafe fuel targetValue hole.target := by
                    simpa [Dual.targets] using targetsSafe.head
                  have matcherTail : FuelEnvironmentSafe fuel matcherValues
                      (holes.map (fun hole => .slot hole.capability hole.target)) := by
                    simpa using matchersSafe.tail
                  have targetTail : FuelHoleValuesSafe fuel holes targetValues := by
                    change FuelEnvironmentSafe fuel targetValues (Dual.targets holes)
                    simpa [Dual.targets] using targetsSafe.tail
                  simp at length
                  obtain ⟨atoms, zipped, atomsSafe⟩ :=
                    ih length matcherTail targetTail
                  exact ⟨⟨pattern, matcherValue, targetValue⟩ :: atoms, by
                    simp [zipMatchingAtoms, zipped],
                    .cons matcherHead targetHead atomsSafe⟩

theorem buildMatchingBranches_fuelSafe
    (length : patterns.length = holes.length)
    (matchersSafe : FuelEnvironmentSafe fuel matcherValues
      (holes.map (fun hole => .slot hole.capability hole.target)))
    (decompositionsSafe : FuelHoleDecompositionsSafe fuel holes decompositions) :
    ∃ branches,
      buildMatchingBranches patterns matcherValues decompositions = some branches ∧
      FuelDelegatedMatchingBranchesSafe fuel holes branches := by
  induction decompositionsSafe with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons head tail ih =>
      obtain ⟨branch, zipped, branchSafe⟩ :=
        zipMatchingAtoms_fuelSafe length matchersSafe head
      obtain ⟨branches, built, branchesSafe⟩ := ih
      change List.mapM (zipMatchingAtoms patterns matcherValues) _ = some branches
        at built
      exact ⟨branch :: branches, by
        simp [buildMatchingBranches, List.mapM_cons, zipped, built],
        .cons branchSafe branchesSafe⟩

/-- One user-matcher arm step using demand-indexed body and next-matcher
certificates.  Runtime environment-demand proofs are explicit because their
construction belongs to the expression producer. -/
theorem tryMatcherArm_fuelSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (targetTyped : ValueTyping target matcherTarget)
    (header : RuntimeDPatTyping dataPattern matcherTarget bindingTypes)
    (bodyCertificate : Certificate operationalFuel bindingTypes
      (captureTypes ++ definitionTypes) bodyExpression
      (DataTypes.list (runtimeHoleProductTarget holes))
      (.fuel (resultFuel + 1)) bodyInput)
    (nextCertificate : Certificate operationalFuel captureTypes definitionTypes
      nextMatchers (runtimeMatcherProductTarget holes)
      (.fuel (resultFuel + 1)) nextInput)
    (bodyEnvironmentSafe : ∀ dataValues,
      matchValueDataPattern dataPattern target = some dataValues →
      OriginEnvironmentSafe bodyInput
        (dataValues ++ (captureValues ++ matcherEnvironment))
        (bindingTypes ++ (captureTypes ++ definitionTypes)))
    (nextEnvironmentSafe : OriginEnvironmentSafe nextInput
      (captureValues ++ matcherEnvironment) (captureTypes ++ definitionTypes))
    (patternsLength : patterns.length = holes.length) :
    tryMatcherArm (evaluate operationalFuel) matcherEnvironment captureValues
        patterns nextMatchers target (.mk dataPattern bodyExpression) = .timeout ∨
      ∃ result,
        tryMatcherArm (evaluate operationalFuel) matcherEnvironment captureValues
          patterns nextMatchers target (.mk dataPattern bodyExpression) = .ok result ∧
        FuelMatcherArmResultSafe (resultFuel + 1) holes result := by
  rcases header.match_typed targetTyped with dataMismatch |
    ⟨dataValues, dataMatch, _dataValuesTyped⟩
  · exact .inr ⟨.miss, by simp [tryMatcherArm, dataMismatch], .miss⟩
  · have bodySafe := evalSafe bodyCertificate
      (bodyEnvironmentSafe dataValues dataMatch)
    rcases bodySafe with bodyTimeout |
      ⟨decompositionValue, bodySuccess, decompositionSafe⟩
    · exact .inl (by simp [tryMatcherArm, dataMatch, bodyTimeout])
    · obtain ⟨decompositions, decompositionsDecoded,
          decompositionsSafe⟩ := decompositionSafe.toFuel.decodeDecompositions
      have decompositionsDecoded' :
          decodeDecompositions patterns.length decompositionValue =
            some decompositions := by
        simpa [patternsLength] using decompositionsDecoded
      have nextSafe := evalSafe nextCertificate nextEnvironmentSafe
      rcases nextSafe with nextTimeout |
        ⟨matcherProduct, nextSuccess, matcherProductSafe⟩
      · exact .inl (by
          simp [tryMatcherArm, dataMatch, bodySuccess,
            decompositionsDecoded', nextTimeout])
      · obtain ⟨matcherValues, matchersDecoded, matcherValuesSafe⟩ :=
          matcherProductSafe.toFuel.decodeRuntimeProduct
        have matchersDecoded' :
            decodeProduct patterns.length matcherProduct = some matcherValues := by
          simpa [patternsLength] using matchersDecoded
        obtain ⟨branches, branchesBuilt, branchesSafe⟩ :=
          buildMatchingBranches_fuelSafe patternsLength matcherValuesSafe
            decompositionsSafe
        exact .inr ⟨.hit branches, by
          simp [tryMatcherArm, dataMatch, bodySuccess, decompositionsDecoded',
            nextSuccess, matchersDecoded', branchesBuilt], .hit branchesSafe⟩

private theorem closeMatcherArmsResult_fuelSafe
    (safe : FuelMatcherArmResultSafe fuel holes result) :
    FuelMatcherClauseResultSafe fuel (closeMatcherArmsResult result) := by
  cases safe with
  | miss => exact .hit (holes := holes) .nil
  | hit branches => exact .hit branches

/-- One complete single-arm clause step: header inspection, capture traversal,
arm evaluation, and closing arm exhaustion to an empty successful branch. -/
theorem tryMatcherClause_singleArm_fuelSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (_atomEnvironmentTyped : EnvironmentTyping atomEnvironment atomEnvironmentTypes)
    (targetTyped : ValueTyping target matcherTarget)
    (header : RuntimePPatTyping patternPattern matcherTarget holes captureTypes)
    (armHeader : RuntimeDPatTyping dataPattern matcherTarget bindingTypes)
    (captureInput : PatternDispatch → OriginEnvironmentDemand)
    (captureCertificates : ∀ {dispatch},
      inspectPatternPattern patternPattern pattern = some dispatch →
      FuelCaptureCertificates Certificate operationalFuel resultFuel
        atomEnvironmentTypes [] dispatch.captures captureTypes
        (captureInput dispatch))
    (captureEnvironmentSafe : ∀ {dispatch},
      inspectPatternPattern patternPattern pattern = some dispatch →
      OriginEnvironmentSafe (captureInput dispatch) atomEnvironment
        atomEnvironmentTypes)
    (bodyCertificate : Certificate operationalFuel bindingTypes
      (captureTypes ++ definitionTypes) bodyExpression
      (DataTypes.list (runtimeHoleProductTarget holes))
      (.fuel (resultFuel + 1)) bodyInput)
    (nextCertificate : Certificate operationalFuel captureTypes definitionTypes
      nextMatchers (runtimeMatcherProductTarget holes)
      (.fuel (resultFuel + 1)) nextInput)
    (bodyEnvironmentSafe : ∀ dataValues captureValues,
      matchValueDataPattern dataPattern target = some dataValues →
      FuelEnvironmentSafe (resultFuel + 1) captureValues captureTypes →
      OriginEnvironmentSafe bodyInput
        (dataValues ++ (captureValues ++ matcherEnvironment))
        (bindingTypes ++ (captureTypes ++ definitionTypes)))
    (nextEnvironmentSafe : ∀ captureValues,
      FuelEnvironmentSafe (resultFuel + 1) captureValues captureTypes →
      OriginEnvironmentSafe nextInput (captureValues ++ matcherEnvironment)
        (captureTypes ++ definitionTypes)) :
    tryMatcherClause (evaluate operationalFuel) atomEnvironment
        matcherEnvironment pattern target
        (.mk patternPattern nextMatchers [.mk dataPattern bodyExpression]) = .timeout ∨
      ∃ result,
        tryMatcherClause (evaluate operationalFuel) atomEnvironment
          matcherEnvironment pattern target
          (.mk patternPattern nextMatchers [.mk dataPattern bodyExpression]) =
            .ok result ∧
        FuelMatcherClauseResultSafe (resultFuel + 1) result := by
  cases inspected : inspectPatternPattern patternPattern pattern with
  | none => exact .inr ⟨.miss, by simp [tryMatcherClause, inspected], .miss⟩
  | some dispatch =>
      have runtimeCounts := (inspectPatternPattern_sound inspected).counts
      have staticCounts := header.counts
      have patternsLength : dispatch.holes.length = holes.length := by omega
      have capturesSafe := captureEnvironmentSafe inspected
      rcases FuelCaptureCertificates.traverse_fuelSafe
          (Certificate := Certificate) (evaluate := evaluate)
          (evalSafe := evalSafe)
          (bindingTypes := atomEnvironmentTypes) (environmentTypes := [])
          (bindings := atomEnvironment) (environment := [])
          (environmentSafe := by simpa using capturesSafe)
          (certificates := captureCertificates inspected) with
        captureTimeout | ⟨captureValues, captureSuccess, captureValuesSafe⟩
      · have captureTimeout' :
            FuelResult.traverse (evaluate operationalFuel atomEnvironment)
              dispatch.captures = .timeout := by
            simpa using captureTimeout
        exact .inl (by simp [tryMatcherClause, inspected, captureTimeout'])
      · rcases tryMatcherArm_fuelSafe
            (Certificate := Certificate) (evaluate := evaluate)
            (operationalFuel := operationalFuel) (resultFuel := resultFuel)
            (evalSafe := evalSafe) (targetTyped := targetTyped)
            (header := armHeader) (bodyCertificate := bodyCertificate)
            (nextCertificate := nextCertificate)
            (fun dataValues matched =>
              bodyEnvironmentSafe dataValues captureValues matched captureValuesSafe)
            (nextEnvironmentSafe captureValues captureValuesSafe)
            patternsLength with
          armTimeout | ⟨armResult, armSuccess, armSafe⟩
        · have captureSuccess' :
              FuelResult.traverse (evaluate operationalFuel atomEnvironment)
                dispatch.captures = .ok captureValues := by
              simpa using captureSuccess
          exact .inl (by
            simp [tryMatcherClause, inspected, captureSuccess', firstHit,
              armTimeout, FuelResult.map])
        · have captureSuccess' :
              FuelResult.traverse (evaluate operationalFuel atomEnvironment)
                dispatch.captures = .ok captureValues := by
              simpa using captureSuccess
          exact .inr ⟨closeMatcherArmsResult armResult, by
            simp [tryMatcherClause, inspected, captureSuccess', firstHit,
              armSuccess, FuelResult.map]
            cases armResult <;> rfl,
            closeMatcherArmsResult_fuelSafe armSafe⟩

end TypePM.Runtime
