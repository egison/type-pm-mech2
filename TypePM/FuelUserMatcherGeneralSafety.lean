import TypePM.OriginDemandSafety
import TypePM.UserMatcherGeneralSafety
import TypePM.UserMatcherExhaustiveness

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

/-! ## Ordered arm and clause dispatch -/

/-- Demand certificates for a source-ordered arm suffix, after capture
evaluation has supplied its concrete values.  Each arm may synthesize a
different data-pattern binding context and select a different body input
demand. -/
inductive FuelMatcherArmsCertificates
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (operationalFuel resultFuel : Nat)
    (definitionTypes captureTypes : List Ty) (matcherTarget : Ty)
    (holes : List Dual) (matcherEnvironment captureValues : ValueEnvironment)
    (target : Value) : List MatcherArm → Prop where
  | nil : FuelMatcherArmsCertificates Certificate operationalFuel resultFuel
      definitionTypes captureTypes matcherTarget holes matcherEnvironment
      captureValues target []
  | cons
      (header : RuntimeDPatTyping dataPattern matcherTarget bindingTypes)
      (bodyCertificate : Certificate operationalFuel bindingTypes
        (captureTypes ++ definitionTypes) bodyExpression
        (DataTypes.list (runtimeHoleProductTarget holes))
        (.fuel (resultFuel + 1)) bodyInput)
      (bodyEnvironmentSafe : ∀ dataValues,
        matchValueDataPattern dataPattern target = some dataValues →
        OriginEnvironmentSafe bodyInput
          (dataValues ++ (captureValues ++ matcherEnvironment))
          (bindingTypes ++ (captureTypes ++ definitionTypes)))
      (tail : FuelMatcherArmsCertificates Certificate operationalFuel resultFuel
        definitionTypes captureTypes matcherTarget holes matcherEnvironment
        captureValues target arms) :
      FuelMatcherArmsCertificates Certificate operationalFuel resultFuel
        definitionTypes captureTypes matcherTarget holes matcherEnvironment
        captureValues target (.mk dataPattern bodyExpression :: arms)

/-- Ordered arm dispatch preserves the fuel-indexed delegated-branch
certificate.  A timeout stops the suffix, a hit stops at the first matching
arm, and only a normal miss advances to the tail. -/
theorem FuelMatcherArmsCertificates.firstHit_fuelSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (targetTyped : ValueTyping target matcherTarget)
    (nextCertificate : Certificate operationalFuel captureTypes definitionTypes
      nextMatchers (runtimeMatcherProductTarget holes)
      (.fuel (resultFuel + 1)) nextInput)
    (nextEnvironmentSafe : OriginEnvironmentSafe nextInput
      (captureValues ++ matcherEnvironment) (captureTypes ++ definitionTypes))
    (patternsLength : patterns.length = holes.length)
    (certificates : FuelMatcherArmsCertificates Certificate operationalFuel
      resultFuel definitionTypes captureTypes matcherTarget holes
      matcherEnvironment captureValues target arms) :
    firstHit
        (tryMatcherArm (evaluate operationalFuel) matcherEnvironment
          captureValues patterns nextMatchers target) arms = .timeout ∨
      ∃ result,
        firstHit
          (tryMatcherArm (evaluate operationalFuel) matcherEnvironment
            captureValues patterns nextMatchers target) arms = .ok result ∧
        FuelMatcherArmResultSafe (resultFuel + 1) holes result := by
  induction certificates with
  | nil => exact .inr ⟨.miss, rfl, .miss⟩
  | cons header bodyCertificate bodyEnvironmentSafe tail ih =>
      rcases tryMatcherArm_fuelSafe
          (Certificate := Certificate) (evaluate := evaluate)
          (operationalFuel := operationalFuel) (resultFuel := resultFuel)
          (evalSafe := evalSafe) (targetTyped := targetTyped)
          (header := header) (bodyCertificate := bodyCertificate)
          (nextCertificate := nextCertificate)
          (bodyEnvironmentSafe := bodyEnvironmentSafe)
          (nextEnvironmentSafe := nextEnvironmentSafe)
          (patternsLength := patternsLength) with
        headTimeout | ⟨headResult, headSuccess, headSafe⟩
      · exact .inl (by simp [firstHit, headTimeout])
      · cases headSafe with
        | hit branchesSafe =>
            exact .inr ⟨_, by simp [firstHit, headSuccess], .hit branchesSafe⟩
        | miss =>
            rcases ih with tailTimeout |
              ⟨tailResult, tailSuccess, tailSafe⟩
            · exact .inl (by
                simp [firstHit, headSuccess, tailTimeout])
            · exact .inr ⟨tailResult, by
                simp [firstHit, headSuccess, tailSuccess], tailSafe⟩

/-- A demand-indexed certificate for one concrete matcher clause input.  The
header determines the hole and capture types.  Capture certificates are
selected from the inspected source pattern; after traversal, the remaining
fields supply the next-matcher and ordered-arm demand proofs for the actual
capture values. -/
inductive FuelMatcherClauseCertificate
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (operationalFuel resultFuel : Nat)
    (atomEnvironmentTypes definitionTypes : List Ty) (matcherTarget : Ty)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (pattern : Pattern) (target : Value) : MatcherClause → Prop where
  | mk
      (header : RuntimePPatTyping patternPattern matcherTarget holes captureTypes)
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
      (nextCertificate : Certificate operationalFuel captureTypes definitionTypes
        nextMatchers (runtimeMatcherProductTarget holes)
        (.fuel (resultFuel + 1)) nextInput)
      (nextEnvironmentSafe : ∀ captureValues,
        FuelEnvironmentSafe (resultFuel + 1) captureValues captureTypes →
        OriginEnvironmentSafe nextInput (captureValues ++ matcherEnvironment)
          (captureTypes ++ definitionTypes))
      (armsCertificates : ∀ captureValues,
        FuelEnvironmentSafe (resultFuel + 1) captureValues captureTypes →
        FuelMatcherArmsCertificates Certificate operationalFuel resultFuel
          definitionTypes captureTypes matcherTarget holes matcherEnvironment
          captureValues target arms) :
      FuelMatcherClauseCertificate Certificate operationalFuel resultFuel
        atomEnvironmentTypes definitionTypes matcherTarget atomEnvironment
        matcherEnvironment pattern target (.mk patternPattern nextMatchers arms)

/-- One arbitrary ordered-arm clause step. -/
theorem FuelMatcherClauseCertificate.try_fuelSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (targetTyped : ValueTyping target matcherTarget)
    (certificate : FuelMatcherClauseCertificate Certificate operationalFuel
      resultFuel atomEnvironmentTypes definitionTypes matcherTarget
      atomEnvironment matcherEnvironment pattern target clause) :
    tryMatcherClause (evaluate operationalFuel) atomEnvironment
        matcherEnvironment pattern target clause = .timeout ∨
      ∃ result,
        tryMatcherClause (evaluate operationalFuel) atomEnvironment
          matcherEnvironment pattern target clause = .ok result ∧
        FuelMatcherClauseResultSafe (resultFuel + 1) result := by
  cases certificate with
  | @mk patternPattern holes captureTypes nextMatchers arms nextInput header
      captureInput captureCertificates captureEnvironmentSafe nextCertificate
      nextEnvironmentSafe armsCertificates =>
      cases inspected : inspectPatternPattern patternPattern pattern with
      | none =>
          exact .inr ⟨.miss, by simp [tryMatcherClause, inspected], .miss⟩
      | some dispatch =>
          have runtimeCounts := (inspectPatternPattern_sound inspected).counts
          have staticCounts := header.counts
          have patternsLength : dispatch.holes.length = holes.length := by omega
          rcases FuelCaptureCertificates.traverse_fuelSafe
              (Certificate := Certificate) (evaluate := evaluate)
              (evalSafe := evalSafe)
              (bindingTypes := atomEnvironmentTypes) (environmentTypes := [])
              (bindings := atomEnvironment) (environment := [])
              (environmentSafe := by
                simpa using captureEnvironmentSafe inspected)
              (certificates := captureCertificates inspected) with
            captureTimeout |
              ⟨captureValues, captureSuccess, captureValuesSafe⟩
          · have captureTimeout' :
                FuelResult.traverse
                    (evaluate operationalFuel atomEnvironment)
                    dispatch.captures = .timeout := by
                simpa using captureTimeout
            exact .inl (by
              simp [tryMatcherClause, inspected, captureTimeout'])
          · rcases (armsCertificates captureValues captureValuesSafe).firstHit_fuelSafe
                (evaluate := evaluate) (evalSafe := evalSafe)
                (targetTyped := targetTyped)
                (nextCertificate := nextCertificate)
                (nextEnvironmentSafe :=
                  nextEnvironmentSafe captureValues captureValuesSafe)
                (patternsLength := patternsLength) with
              armsTimeout | ⟨armsResult, armsSuccess, armsSafe⟩
            · have captureSuccess' :
                  FuelResult.traverse
                      (evaluate operationalFuel atomEnvironment)
                      dispatch.captures = .ok captureValues := by
                  simpa using captureSuccess
              exact .inl (by
                simp [tryMatcherClause, inspected, captureSuccess', armsTimeout,
                  FuelResult.map])
            · have captureSuccess' :
                  FuelResult.traverse
                      (evaluate operationalFuel atomEnvironment)
                      dispatch.captures = .ok captureValues := by
                  simpa using captureSuccess
              exact .inr ⟨closeMatcherArmsResult armsResult, by
                simp [tryMatcherClause, inspected, captureSuccess', armsSuccess,
                  FuelResult.map],
                closeMatcherArmsResult_fuelSafe armsSafe⟩

/-- Pointwise certificates for a source-ordered clause suffix. -/
inductive FuelMatcherClausesCertificates
    (Certificate : FuelEmbeddedExpressionCertificateFamily)
    (operationalFuel resultFuel : Nat)
    (atomEnvironmentTypes definitionTypes : List Ty) (matcherTarget : Ty)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (pattern : Pattern) (target : Value) : List MatcherClause → Prop where
  | nil : FuelMatcherClausesCertificates Certificate operationalFuel resultFuel
      atomEnvironmentTypes definitionTypes matcherTarget atomEnvironment
      matcherEnvironment pattern target []
  | cons
      (head : FuelMatcherClauseCertificate Certificate operationalFuel resultFuel
        atomEnvironmentTypes definitionTypes matcherTarget atomEnvironment
        matcherEnvironment pattern target clause)
      (tail : FuelMatcherClausesCertificates Certificate operationalFuel resultFuel
        atomEnvironmentTypes definitionTypes matcherTarget atomEnvironment
        matcherEnvironment pattern target clauses) :
      FuelMatcherClausesCertificates Certificate operationalFuel resultFuel
        atomEnvironmentTypes definitionTypes matcherTarget atomEnvironment
        matcherEnvironment pattern target (clause :: clauses)

/-- Ordered clause dispatch preserves fuel safety.  Different clauses may
produce different solved hole lists, existentially recorded by the common
clause-result certificate. -/
theorem FuelMatcherClausesCertificates.dispatch_fuelSafe
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (targetTyped : ValueTyping target matcherTarget)
    (certificates : FuelMatcherClausesCertificates Certificate operationalFuel
      resultFuel atomEnvironmentTypes definitionTypes matcherTarget
      atomEnvironment matcherEnvironment pattern target clauses) :
    dispatchMatcherClauses (evaluate operationalFuel) atomEnvironment
        matcherEnvironment clauses pattern target = .timeout ∨
      ∃ result,
        dispatchMatcherClauses (evaluate operationalFuel) atomEnvironment
          matcherEnvironment clauses pattern target = .ok result ∧
        FuelMatcherClauseResultSafe (resultFuel + 1) result := by
  induction certificates with
  | nil => exact .inr ⟨.miss, rfl, .miss⟩
  | cons head tail ih =>
      rcases head.try_fuelSafe (evaluate := evaluate) evalSafe targetTyped with
        headTimeout | ⟨headResult, headSuccess, headSafe⟩
      · exact .inl (by
          simp [dispatchMatcherClauses, firstHit, headTimeout])
      · cases headSafe with
        | hit branchesSafe =>
            exact .inr ⟨_, by
              simp [dispatchMatcherClauses, firstHit, headSuccess],
              .hit branchesSafe⟩
        | miss =>
            rcases ih with tailTimeout |
              ⟨tailResult, tailSuccess, tailSafe⟩
            · exact .inl (by
                simp [dispatchMatcherClauses, firstHit, headSuccess]
                simpa [dispatchMatcherClauses] using tailTimeout)
            · exact .inr ⟨tailResult, by
                simp [dispatchMatcherClauses, firstHit, headSuccess]
                simpa [dispatchMatcherClauses] using tailSuccess,
                tailSafe⟩

/-- With the declarative final catch-all, ordered fuel-safe dispatch cannot
finish with a normal miss: it either times out or returns fuel-safe recursive
matching branches. -/
theorem FuelMatcherClausesCertificates.dispatch_fuelSafe_of_finalCatchAll
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (targetTyped : ValueTyping target matcherTarget)
    (certificates : FuelMatcherClausesCertificates Certificate operationalFuel
      resultFuel atomEnvironmentTypes definitionTypes matcherTarget
      atomEnvironment matcherEnvironment pattern target clauses)
    (finalCatchAll : MatcherTyping.FinalCatchAll clauses) :
    dispatchMatcherClauses (evaluate operationalFuel) atomEnvironment
        matcherEnvironment clauses pattern target = .timeout ∨
      ∃ branches holes,
        dispatchMatcherClauses (evaluate operationalFuel) atomEnvironment
            matcherEnvironment clauses pattern target = .ok (.hit branches) ∧
          FuelDelegatedMatchingBranchesSafe (resultFuel + 1) holes branches := by
  rcases certificates.dispatch_fuelSafe (evaluate := evaluate) evalSafe
      targetTyped with timeout | ⟨result, success, resultSafe⟩
  · exact .inl timeout
  · cases resultSafe with
    | miss =>
        exact False.elim (finalCatchAll_dispatch_ne_miss finalCatchAll success)
    | @hit holes branches branchesSafe =>
        exact .inr ⟨branches, holes, success, branchesSafe⟩

/-- The final-catch-all endpoint rules out the runtime `stuck` result without
requiring an evaluator equation or a fixed operational-fuel value. -/
theorem FuelMatcherClausesCertificates.dispatch_notStuck_of_finalCatchAll
    (evalSafe : FuelEmbeddedEvaluatorSafe Certificate evaluate)
    (targetTyped : ValueTyping target matcherTarget)
    (certificates : FuelMatcherClausesCertificates Certificate operationalFuel
      resultFuel atomEnvironmentTypes definitionTypes matcherTarget
      atomEnvironment matcherEnvironment pattern target clauses)
    (finalCatchAll : MatcherTyping.FinalCatchAll clauses) :
    (dispatchMatcherClauses (evaluate operationalFuel) atomEnvironment
      matcherEnvironment clauses pattern target).NotStuck := by
  rcases certificates.dispatch_fuelSafe_of_finalCatchAll
      (evaluate := evaluate) evalSafe targetTyped finalCatchAll with
    timeout | ⟨branches, holes, success, branchesSafe⟩
  · rw [timeout]
    trivial
  · rw [success]
    trivial

end TypePM.Runtime
