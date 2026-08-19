import TypePM.Source.Elaboration
import TypePM.GeneralizationTransport

/-!
# Fresh-supply transport for source elaboration

A two-sort variable permutation does not in general preserve the consecutive
names chosen by executable elaboration. Source transport therefore uses
explicit finite-prefix alignment for the names which a derivation actually
allocates. The stronger infinite-stream predicate below is retained for
simple corollaries, but is not a premise of full structural transport.
-/

namespace TypePM.Source

namespace Supply

/-- `MapsPrefix rho source target tyCount capCount` maps exactly the finite
ordinary- and capability-name prefixes allocated from two supplies.  Unlike
`MapsFrom`, it places no condition on the unused infinite tails. -/
def MapsPrefix (rho : VariableRenaming) (source target : Supply)
    (tyCount capCount : Nat) : Prop :=
  (∀ offset, offset < tyCount →
      rho.tyForward ⟨source.ty + offset⟩ = ⟨target.ty + offset⟩) ∧
    (∀ offset, offset < capCount →
      rho.capForward ⟨source.cap + offset⟩ = ⟨target.cap + offset⟩)

/-- `MapsFrom rho source target` aligns every future ordinary and capability
name at the same offset from two supplies. -/
def MapsFrom (rho : VariableRenaming) (source target : Supply) : Prop :=
  (∀ offset,
      rho.tyForward ⟨source.ty + offset⟩ = ⟨target.ty + offset⟩) ∧
    (∀ offset,
      rho.capForward ⟨source.cap + offset⟩ = ⟨target.cap + offset⟩)

theorem MapsFrom.mapsPrefix
    {rho : VariableRenaming} {source target : Supply}
    (mapping : MapsFrom rho source target) (tyCount capCount : Nat) :
    MapsPrefix rho source target tyCount capCount :=
  ⟨fun offset _ => mapping.1 offset, fun offset _ => mapping.2 offset⟩

theorem mapsFrom_nextTy
    {rho : VariableRenaming} {source target : Supply}
    (mapping : MapsFrom rho source target) (count : Nat) :
    MapsFrom rho (source.nextTy count) (target.nextTy count) := by
  constructor
  · intro offset
    have mapped := mapping.1 (count + offset)
    simpa [Supply.nextTy, Nat.add_assoc] using mapped
  · intro offset
    simpa [Supply.nextTy] using mapping.2 offset

/-- A let boundary needs this additional alignment because `join` takes a
numeric maximum, which an arbitrary finite permutation need not preserve. -/
def MapsJoin (rho : VariableRenaming)
    (sourceLeft sourceRight targetLeft targetRight : Supply) : Prop :=
  MapsFrom rho (sourceLeft.join sourceRight)
    (targetLeft.join targetRight)

theorem mapsJoin_elim
    {rho : VariableRenaming}
    {sourceLeft sourceRight targetLeft targetRight : Supply}
    (mapping : MapsJoin rho sourceLeft sourceRight targetLeft targetRight) :
    MapsFrom rho (sourceLeft.join sourceRight)
      (targetLeft.join targetRight) :=
  mapping

end Supply


namespace Scheme

mutual

theorem PolyCap.openBound_eq_of_wellScoped
    {capArity : Nat} {capability : PolyCap}
    (wellScoped : capability.WellScoped capArity)
    {left right : Nat → Cap}
    (agree : ∀ position, position < capArity →
      left position = right position) :
    capability.openBound left = capability.openBound right := by
  cases capability with
  | any => rfl
  | free => rfl
  | bound position =>
      exact agree position (by
        simpa [PolyCap.WellScoped] using wellScoped)
  | prod items =>
      simp only [PolyCap.openBound]
      exact congrArg Cap.prod
        (PolyCap.openBoundList_eq_of_wellScoped (by
          simpa [PolyCap.WellScoped] using wellScoped) agree)
  | con former arguments =>
      simp only [PolyCap.openBound]
      exact congrArg (Cap.con former)
        (PolyCap.openBoundList_eq_of_wellScoped (by
          simpa [PolyCap.WellScoped] using wellScoped) agree)

theorem PolyCap.openBoundList_eq_of_wellScoped
    {capArity : Nat} {items : List PolyCap}
    (wellScoped : ∀ item ∈ items, item.WellScoped capArity)
    {left right : Nat → Cap}
    (agree : ∀ position, position < capArity →
      left position = right position) :
    PolyCap.openBoundList left items =
      PolyCap.openBoundList right items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [PolyCap.openBoundList]
      rw [PolyCap.openBound_eq_of_wellScoped
          (wellScoped item (by simp)) agree,
        PolyCap.openBoundList_eq_of_wellScoped
          (fun candidate membership => wellScoped candidate (by simp [membership]))
          agree]

end

mutual

theorem PolyTy.openBound_eq_of_wellScoped
    {tyArity capArity : Nat} {body : PolyTy}
    (wellScoped : body.WellScoped tyArity capArity)
    {leftTy rightTy : Nat → Ty} {leftCap rightCap : Nat → Cap}
    (tyAgree : ∀ position, position < tyArity →
      leftTy position = rightTy position)
    (capAgree : ∀ position, position < capArity →
      leftCap position = rightCap position) :
    body.openBound leftTy leftCap =
      body.openBound rightTy rightCap := by
  cases body with
  | free => rfl
  | bound position => exact tyAgree position (by
      simpa [PolyTy.WellScoped] using wellScoped)
  | int => rfl
  | fn domain codomain =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.openBound]
      rw [PolyTy.openBound_eq_of_wellScoped wellScoped.1 tyAgree capAgree,
        PolyTy.openBound_eq_of_wellScoped wellScoped.2 tyAgree capAgree]
  | prod items =>
      simp only [PolyTy.openBound]
      exact congrArg Ty.prod
        (PolyTy.openBoundList_eq_of_wellScoped (by
          simpa [PolyTy.WellScoped] using wellScoped) tyAgree capAgree)
  | data former arguments =>
      simp only [PolyTy.openBound]
      exact congrArg (Ty.data former)
        (PolyTy.openBoundList_eq_of_wellScoped (by
          simpa [PolyTy.WellScoped] using wellScoped) tyAgree capAgree)
  | matcher capability target =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.openBound]
      rw [PolyCap.openBound_eq_of_wellScoped wellScoped.1 capAgree,
        PolyTy.openBound_eq_of_wellScoped wellScoped.2 tyAgree capAgree]
  | slot capability target =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.openBound]
      rw [PolyCap.openBound_eq_of_wellScoped wellScoped.1 capAgree,
        PolyTy.openBound_eq_of_wellScoped wellScoped.2 tyAgree capAgree]

theorem PolyTy.openBoundList_eq_of_wellScoped
    {tyArity capArity : Nat} {items : List PolyTy}
    (wellScoped : ∀ item ∈ items, item.WellScoped tyArity capArity)
    {leftTy rightTy : Nat → Ty} {leftCap rightCap : Nat → Cap}
    (tyAgree : ∀ position, position < tyArity →
      leftTy position = rightTy position)
    (capAgree : ∀ position, position < capArity →
      leftCap position = rightCap position) :
    PolyTy.openBoundList leftTy leftCap items =
      PolyTy.openBoundList rightTy rightCap items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [PolyTy.openBoundList]
      rw [PolyTy.openBound_eq_of_wellScoped
          (wellScoped item (by simp)) tyAgree capAgree,
        PolyTy.openBoundList_eq_of_wellScoped
          (fun candidate membership => wellScoped candidate (by simp [membership]))
          tyAgree capAgree]

end

/-- Canonical scheme instantiation only needs the finite fresh prefixes
whose lengths are the two binder arities. -/
theorem instantiate_variableRenaming_prefix
    (rho : VariableRenaming) (scheme : Scheme)
    {source target : Supply}
    (mapping : source.MapsPrefix rho target
      scheme.tyArity scheme.capArity) :
    ((scheme.applyFree rho.substitution).instantiate target).1 =
      (scheme.instantiate source).1.apply rho.substitution := by
  change
    (scheme.body.applyFree rho.substitution).openBound
        (fun position => .var (boundTyInstance target position))
        (fun position => .var (boundCapInstance target position)) =
      (scheme.body.openBound
        (fun position => .var (boundTyInstance source position))
        (fun position => .var (boundCapInstance source position))).apply
          rho.substitution
  have transported := PolyTy.openBound_applyFree rho.substitution
    (fun position => .var (boundTyInstance source position))
    (fun position => .var (boundCapInstance source position))
    scheme.body
  rw [← transported]
  apply PolyTy.openBound_eq_of_wellScoped
    (PolyTy.applyFree_wellScoped rho.substitution
      scheme.tyArity scheme.capArity scheme.wellScoped)
  · intro position within
    exact (congrArg Ty.var (mapping.1 position within)).symm
  · intro position within
    exact (congrArg Cap.var (mapping.2 position within)).symm

/-- Canonical scheme instantiation is equivariant when the two fresh streams
are aligned pointwise. -/
theorem instantiate_variableRenaming
    (rho : VariableRenaming) (scheme : Scheme)
    {source target : Supply} (mapping : source.MapsFrom rho target) :
    ((scheme.applyFree rho.substitution).instantiate target).1 =
      (scheme.instantiate source).1.apply rho.substitution := by
  exact instantiate_variableRenaming_prefix rho scheme
    (mapping.mapsPrefix scheme.tyArity scheme.capArity)

/-- Instantiation advances aligned supplies by the same two arities. -/
theorem instantiate_next_mapsFrom
    (rho : VariableRenaming) (scheme : Scheme)
    {source target : Supply} (mapping : source.MapsFrom rho target) :
    (scheme.instantiate source).2.MapsFrom rho
      ((scheme.applyFree rho.substitution).instantiate target).2 := by
  constructor
  · intro offset
    have mapped := mapping.1 (scheme.tyArity + offset)
    simpa [Scheme.instantiate, Scheme.applyFree, Nat.add_assoc] using mapped
  · intro offset
    have mapped := mapping.2 (scheme.capArity + offset)
    simpa [Scheme.instantiate, Scheme.applyFree, Nat.add_assoc] using mapped

end Scheme


namespace Context

/-- The explicit root precondition for transporting executable elaboration.
It is deliberately not asserted for every permutation: `initialSupply` is a
numeric maximum and hence depends on the chosen variable names. -/
def InitialSuppliesAligned (rho : VariableRenaming)
    (context : Context) : Prop :=
  context.initialSupply.MapsFrom rho
    (context.applyFree rho.substitution).initialSupply

end Context

end TypePM.Source
