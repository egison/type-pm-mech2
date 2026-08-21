import TypePM.Source.M4RawFiniteDemandCertificate

namespace TypePM.Source.M4RawFiniteDemandCertificateRegression

open TypePM.Runtime

def identityScheme : Source.Scheme :=
  ⟨1, 0, .fn (.bound 0) (.bound 0), by
    simp [Source.PolyTy.WellScoped]⟩

def openContext : Source.Context :=
  [identityScheme, Source.Scheme.mono .int]

def identityValue : Value :=
  Value.plainClosure [] (.var 0)

def openEnvironment : ValueEnvironment :=
  [identityValue, .int 11]

def distinctDemand : FuelDemand
  | 0 => 5
  | position + 1 => match position with
    | 0 => 2
    | _ => 0

private theorem identityValue_fuelSafe (index : Nat) (domain : Ty) :
    FuelValueSafe index identityValue (.fn domain domain) := by
  induction index with
  | zero => exact fuelValueSafe_zero _ _
  | succ index induction =>
      apply PositiveValueSafe.function induction
      · exact .plainClosure .nil
          (.expression (.core (.core (.var rfl))))
      · intro argument argumentSafe
        change FuelResultSafe index domain
          (evalFuel index [argument] (.var 0))
        exact evalFuel_var_resultSafeWith rfl argumentSafe index

private theorem identitySchemeSafe (index : Nat) :
    SchemeFuelValueSafe index identityValue identityScheme Subst.id := by
  intro supply
  simpa [identityScheme, Source.Scheme.instantiate,
    Source.PolyTy.openBound, Source.Scheme.boundTyInstance, Ty.apply] using
    identityValue_fuelSafe index (.var ⟨supply.ty⟩)

private theorem integerSchemeSafe (index : Nat) :
    SchemeFuelValueSafe index (.int 11) (Source.Scheme.mono .int)
      Subst.id := by
  apply SchemeFuelValueSafe.ofMono
  simpa using fuelValueSafe_int 11 index

theorem openEnvironment_distinctDemandSafe :
    SchemeDemandEnvironmentSafe distinctDemand Subst.id openEnvironment
      openContext := by
  have prefixSafe := SchemeDemandEnvironmentSafe.cons (identitySchemeSafe 5)
    (SchemeDemandEnvironmentSafe.cons (integerSchemeSafe 2)
      (SchemeDemandEnvironmentSafe.nil (fun _ => 0) Subst.id))
  apply prefixSafe.congr
  intro position positionLt
  cases position with
  | zero => rfl
  | succ position =>
      cases position with
      | zero => rfl
      | succ position =>
          have impossible : position + 2 < 2 := by simpa using positionLt
          omega

theorem openEnvironment_firstDemand :
    SchemeFuelValueSafe 5 identityValue identityScheme Subst.id := by
  have safe := openEnvironment_distinctDemandSafe.lookupValue
    (position := 0) (scheme := identityScheme) (value := identityValue)
    (by simp [openContext]) (by simp [openEnvironment])
  simpa [distinctDemand] using safe

theorem openEnvironment_secondDemand :
    SchemeFuelValueSafe 2 (.int 11) (Source.Scheme.mono .int) Subst.id := by
  have safe := openEnvironment_distinctDemandSafe.lookupValue
    (position := 1) (scheme := Source.Scheme.mono .int) (value := .int 11)
    (by simp [openContext]) (by simp [openEnvironment])
  simpa [distinctDemand] using safe

def nestedTuple : Source.Expr :=
  .tuple [.var 0, .tuple [.lit 7, .var 1]]

def nestedGenerated : Generated :=
  ⟨.prod [.fn (.var ⟨0⟩) (.var ⟨0⟩), .prod [.int, .int]], [], []⟩

def nestedSolution : Subst :=
  Subst.singleTy ⟨0⟩ .int

def openVariableGenerated : Generated :=
  ⟨.fn (.var ⟨0⟩) (.var ⟨0⟩), [], []⟩

theorem openVariableElaboration (signature : Source.FrozenSignature) :
    Source.M4.ElaboratesFuel signature 1 openContext (.var 0) ⟨0, 0⟩
      openVariableGenerated ⟨1, 0⟩ := by
  simp [Source.M4.ElaboratesFuel, openContext, openVariableGenerated,
    identityScheme, Source.Scheme.instantiate, Source.PolyTy.openBound,
    Source.Scheme.boundTyInstance]

def openVariableCertificate (signature : Source.FrozenSignature) :
    Source.M4.RawFuelCertificate (openVariableElaboration signature) :=
  Source.M4.RawFuelCertificate.varWitness
    (openVariableElaboration signature)

/-- The actual variable certificate asks for a positive index only at source
position zero; the unused source position receives demand zero. -/
theorem openVariableCertificate_exactDemand
    (signature : Source.FrozenSignature) (operationalFuel logicalIndex : Nat) :
    (openVariableCertificate signature).inputDemand operationalFuel
        (logicalIndex + 1) 0 = logicalIndex + 1 ∧
      (openVariableCertificate signature).inputDemand operationalFuel
        (logicalIndex + 1) 1 = 0 := by
  constructor
  · exact Source.M4.RawFuelCertificate.varWitness_inputDemand_selected
      (openVariableElaboration signature) operationalFuel (logicalIndex + 1)
  · exact Source.M4.RawFuelCertificate.varWitness_inputDemand_other
      (openVariableElaboration signature) operationalFuel (logicalIndex + 1)
      1 (by omega)

theorem openVariableGeneratedSemantic :
    openVariableGenerated.SemanticSolution nestedSolution := by
  constructor <;> simp [openVariableGenerated]

/-- Concrete execution is deliberately independent of the raw safety proof. -/
theorem nestedTuple_fuelThree_exact :
    evalFuel 3 openEnvironment nestedTuple =
      .ok (.tuple [identityValue, .tuple [.int 7, .int 11]]) := by
  rfl

theorem nestedTupleElaboration (signature : Source.FrozenSignature) :
    Source.M4.ElaboratesFuel signature 3 openContext nestedTuple ⟨0, 0⟩
      nestedGenerated ⟨1, 0⟩ := by
  have firstElaboration :
      Source.M4.ElaboratesFuel signature 2 openContext (.var 0) ⟨0, 0⟩
        ⟨.fn (.var ⟨0⟩) (.var ⟨0⟩), [], []⟩ ⟨1, 0⟩ := by
    simp [Source.M4.ElaboratesFuel, openContext, identityScheme,
      Source.Scheme.instantiate, Source.PolyTy.openBound,
      Source.Scheme.boundTyInstance]
  have literalElaboration :
      Source.M4.ElaboratesFuel signature 1 openContext (.lit 7) ⟨1, 0⟩
        ⟨.int, [], []⟩ ⟨1, 0⟩ := by
    simp [Source.M4.ElaboratesFuel]
  have secondVariableElaboration :
      Source.M4.ElaboratesFuel signature 1 openContext (.var 1) ⟨1, 0⟩
        ⟨.int, [], []⟩ ⟨1, 0⟩ := by
    simp [Source.M4.ElaboratesFuel, openContext, Source.Scheme.instantiate,
      Source.Scheme.mono, Source.PolyTy.ofTy, Source.PolyTy.openBound]
  have innerItems : Source.M4.ItemsElaborateUsing
      (Source.M4.ElaboratesFuel signature 1) openContext
      [.lit 7, .var 1] ⟨1, 0⟩ ⟨[.int, .int], [], []⟩ ⟨1, 0⟩ :=
    .cons literalElaboration
      (.cons secondVariableElaboration .nil)
  have innerElaboration :
      Source.M4.ElaboratesFuel signature 2 openContext
        (.tuple [.lit 7, .var 1]) ⟨1, 0⟩
        ⟨.prod [.int, .int], [], []⟩ ⟨1, 0⟩ := by
    simp only [Source.M4.ElaboratesFuel]
    exact ⟨⟨[.int, .int], [], []⟩, innerItems, rfl⟩
  have outerItems : Source.M4.ItemsElaborateUsing
      (Source.M4.ElaboratesFuel signature 2) openContext
      [.var 0, .tuple [.lit 7, .var 1]] ⟨0, 0⟩
      ⟨[.fn (.var ⟨0⟩) (.var ⟨0⟩), .prod [.int, .int]], [], []⟩
      ⟨1, 0⟩ :=
    .cons firstElaboration (.cons innerElaboration .nil)
  simp only [Source.M4.ElaboratesFuel]
  exact ⟨_, outerItems, rfl⟩

theorem nestedGeneratedSemantic :
    nestedGenerated.SemanticSolution nestedSolution := by
  constructor <;> simp [nestedGenerated]

def nestedTupleSupported : Source.M4.RawFiniteDemandSupported nestedTuple :=
  .tuple (.cons .var (.cons (.tuple (.cons .lit (.cons .var .nil))) .nil))

private theorem openEnvironment_anyDemand (demand : FuelDemand) :
    SchemeDemandEnvironmentSafe demand nestedSolution openEnvironment
      openContext := by
  have identitySafe : SchemeFuelValueSafe (demand 0) identityValue
      identityScheme nestedSolution := by
    intro supply
    simpa [identityScheme, Source.Scheme.instantiate,
      Source.PolyTy.openBound, Source.Scheme.boundTyInstance, Ty.apply] using
      identityValue_fuelSafe (demand 0)
        ((Ty.var ⟨supply.ty⟩).apply nestedSolution)
  have integerSafe : SchemeFuelValueSafe (demand 1) (.int 11)
      (Source.Scheme.mono .int) nestedSolution := by
    apply SchemeFuelValueSafe.ofMono
    change FuelValueSafe (demand 1) (.int 11) .int
    exact fuelValueSafe_int 11 (demand 1)
  have prefixSafe := SchemeDemandEnvironmentSafe.cons identitySafe
      (SchemeDemandEnvironmentSafe.cons integerSafe
        (SchemeDemandEnvironmentSafe.nil (fun _ => 0) nestedSolution))
  apply prefixSafe.congr
  intro position positionLt
  cases position with
  | zero => rfl
  | succ position =>
      cases position with
      | zero => rfl
      | succ position =>
          have impossible : position + 2 < 2 := by simpa using positionLt
          omega

/-- The exact demand exposed above is sufficient for the variable witness's
`preserves` field; this theorem does not replace that demand by a uniform
environment index. -/
theorem openVariableCertificate_preserves
    (signature : Source.FrozenSignature) (operationalFuel logicalIndex : Nat) :
    FuelResultSafe (logicalIndex + 1) (.fn .int .int)
      (evalFuel operationalFuel openEnvironment (.var 0)) := by
  let certificate := openVariableCertificate signature
  have result := certificate.preserves nestedSolution
    openVariableGeneratedSemantic operationalFuel (logicalIndex + 1)
    openEnvironment
    (openEnvironment_anyDemand
      (certificate.inputDemand operationalFuel (logicalIndex + 1)))
  simpa [certificate, openVariableCertificate, openVariableGenerated,
    nestedSolution, Ty.apply, Subst.singleTy] using result

private theorem nestedTargetApplied :
    nestedGenerated.target.apply nestedSolution =
      .prod [.fn .int .int, .prod [.int, .int]] := by
  simp [nestedGenerated, nestedSolution, Ty.apply, Ty.applyList,
    Subst.singleTy]

theorem nestedTuple_rawSafe (signature : Source.FrozenSignature)
    (operationalFuel resultIndex : Nat) :
    FuelResultSafe resultIndex
      (.prod [.fn .int .int, .prod [.int, .int]])
      (evalFuel operationalFuel openEnvironment nestedTuple) := by
  obtain ⟨certificate⟩ := nestedTupleSupported.certificate
    (nestedTupleElaboration signature)
  have result := certificate.preserves nestedSolution nestedGeneratedSemantic
    operationalFuel resultIndex openEnvironment
    (openEnvironment_anyDemand
      (certificate.inputDemand operationalFuel resultIndex))
  rw [nestedTargetApplied] at result
  exact result

theorem nestedTuple_neverStuck (signature : Source.FrozenSignature)
    (operationalFuel : Nat) :
    (evalFuel operationalFuel openEnvironment nestedTuple).NotStuck :=
  (nestedTuple_rawSafe signature operationalFuel 0).notStuck

end TypePM.Source.M4RawFiniteDemandCertificateRegression
