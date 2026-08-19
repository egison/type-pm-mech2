import TypePM.GenerationRelation

/-!
# Fresh-supply bounds for M1 generation

This file establishes the two bounds needed by the later freshness theorem:
generation never decreases its supply, and `Context.nextVar` lies strictly
above every ordinary type variable occurring in the context.  The proofs use
only generated targets and supply threading; they do not inspect the shape of
hard constraints.
-/

namespace TypePM

mutual

/-- Structural occurrence of an ordinary variable in a type.  Capability
variables are intentionally outside this relation. -/
inductive TyVarOccurs : TyVar → Ty → Prop where
  | var {needle} : TyVarOccurs needle (.var needle)
  | fnDomain {needle domain codomain} :
      TyVarOccurs needle domain →
      TyVarOccurs needle (.fn domain codomain)
  | fnCodomain {needle domain codomain} :
      TyVarOccurs needle codomain →
      TyVarOccurs needle (.fn domain codomain)
  | prod {needle items} :
      TyVarOccursList needle items →
      TyVarOccurs needle (.prod items)
  | data {needle former arguments} :
      TyVarOccursList needle arguments →
      TyVarOccurs needle (.data former arguments)
  | matcher {needle capability target} :
      TyVarOccurs needle target →
      TyVarOccurs needle (.matcher capability target)
  | slot {needle capability target} :
      TyVarOccurs needle target →
      TyVarOccurs needle (.slot capability target)

/-- Structural occurrence of an ordinary variable in a list of types. -/
inductive TyVarOccursList : TyVar → List Ty → Prop where
  | head {needle target targets} :
      TyVarOccurs needle target →
      TyVarOccursList needle (target :: targets)
  | tail {needle target targets} :
      TyVarOccursList needle targets →
      TyVarOccursList needle (target :: targets)

end

/-- Every ordinary type variable in a type has an index below `bound`.
Using `Ty.nextVar` makes this property independent of constraint syntax. -/
def Ty.tyVarsBelow (bound : Nat) (target : Ty) : Prop :=
  target.nextVar ≤ bound

/-- Ordinary-variable scope for either sort of hard equation.  Capability
equations contain no ordinary type variables. -/
def Equation.tyVarsBelow (bound : Nat) : Equation → Prop
  | .ty left right => left.tyVarsBelow bound ∧ right.tyVarsBelow bound
  | .cap _ _ => True

def CheckObligation.tyVarsBelow
    (bound : Nat) (obligation : CheckObligation) : Prop :=
  obligation.source.tyVarsBelow bound ∧
    obligation.expected.tyVarsBelow bound

/-- All ordinary variables in one generated expression result are below the
given bound. -/
def Generated.tyVarsBelow (bound : Nat) (generated : Generated) : Prop :=
  generated.target.tyVarsBelow bound ∧
  (∀ equation, equation ∈ generated.hard → equation.tyVarsBelow bound) ∧
  (∀ obligation, obligation ∈ generated.pending →
    obligation.tyVarsBelow bound)

/-- List counterpart of `Generated.tyVarsBelow`. -/
def GeneratedItems.tyVarsBelow
    (bound : Nat) (generated : GeneratedItems) : Prop :=
  (∀ target, target ∈ generated.targets → target.tyVarsBelow bound) ∧
  (∀ equation, equation ∈ generated.hard → equation.tyVarsBelow bound) ∧
  (∀ obligation, obligation ∈ generated.pending →
    obligation.tyVarsBelow bound)

namespace Ty

theorem tyVarsBelow_mono
    {target : Ty} {smaller larger : Nat}
    (bounded : target.tyVarsBelow smaller) (le : smaller ≤ larger) :
    target.tyVarsBelow larger :=
  Nat.le_trans bounded le

end Ty

namespace Equation

theorem tyVarsBelow_mono
    {equation : Equation} {smaller larger : Nat}
    (bounded : equation.tyVarsBelow smaller) (le : smaller ≤ larger) :
    equation.tyVarsBelow larger := by
  cases equation with
  | ty left right =>
      exact ⟨Ty.tyVarsBelow_mono bounded.1 le,
        Ty.tyVarsBelow_mono bounded.2 le⟩
  | cap left right => trivial

end Equation

namespace CheckObligation

theorem tyVarsBelow_mono
    {obligation : CheckObligation} {smaller larger : Nat}
    (bounded : obligation.tyVarsBelow smaller) (le : smaller ≤ larger) :
    obligation.tyVarsBelow larger :=
  ⟨Ty.tyVarsBelow_mono bounded.1 le,
    Ty.tyVarsBelow_mono bounded.2 le⟩

end CheckObligation

namespace Generated

theorem tyVarsBelow_mono
    {generated : Generated} {smaller larger : Nat}
    (bounded : generated.tyVarsBelow smaller) (le : smaller ≤ larger) :
    generated.tyVarsBelow larger := by
  refine ⟨Ty.tyVarsBelow_mono bounded.1 le, ?_, ?_⟩
  · intro equation membership
    exact Equation.tyVarsBelow_mono (bounded.2.1 equation membership) le
  · intro obligation membership
    exact CheckObligation.tyVarsBelow_mono
      (bounded.2.2 obligation membership) le

end Generated

namespace GeneratedItems

theorem tyVarsBelow_mono
    {generated : GeneratedItems} {smaller larger : Nat}
    (bounded : generated.tyVarsBelow smaller) (le : smaller ≤ larger) :
    generated.tyVarsBelow larger := by
  refine ⟨?_, ?_, ?_⟩
  · intro target membership
    exact Ty.tyVarsBelow_mono (bounded.1 target membership) le
  · intro equation membership
    exact Equation.tyVarsBelow_mono (bounded.2.1 equation membership) le
  · intro obligation membership
    exact CheckObligation.tyVarsBelow_mono
      (bounded.2.2 obligation membership) le

end GeneratedItems

mutual

/-- Relational generation never decreases the fresh-variable supply. -/
theorem Generates.supply_le_next
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (derivation : Generates context expression supply generated next) :
    supply ≤ next := by
  cases derivation with
  | var _ => exact Nat.le_refl _
  | lit => exact Nat.le_refl _
  | something => omega
  | lam bodyDerivation =>
      have bodyBound := Generates.supply_le_next bodyDerivation
      omega
  | app functionDerivation argumentDerivation =>
      have functionBound := Generates.supply_le_next functionDerivation
      have argumentBound := Generates.supply_le_next argumentDerivation
      omega
  | tuple itemsDerivation =>
      exact GeneratesItems.supply_le_next itemsDerivation

/-- Relational list generation never decreases the fresh-variable supply. -/
theorem GeneratesItems.supply_le_next
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems}
    (derivation : GeneratesItems context expressions supply generated next) :
    supply ≤ next := by
  cases derivation with
  | nil => exact Nat.le_refl _
  | cons itemDerivation itemsDerivation =>
      have itemBound := Generates.supply_le_next itemDerivation
      have itemsBound := GeneratesItems.supply_le_next itemsDerivation
      exact Nat.le_trans itemBound itemsBound

end

/-- Executable generation inherits supply monotonicity from its relational
specification. -/
theorem generate_supply_le_next
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (success : generate context expression supply = some (generated, next)) :
    supply ≤ next :=
  (generate_to_generates success).supply_le_next

/-- Executable list generation inherits supply monotonicity from its
relational specification. -/
theorem generateItems_supply_le_next
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems}
    (success : generateItems context expressions supply = some (generated, next)) :
    supply ≤ next :=
  (generateItems_to_generatesItems success).supply_le_next

namespace Ty

/-- Every member contributes at most the next-variable bound of the entire
type list. -/
theorem nextVar_le_nextVarList_of_mem
    {target : Ty} {targets : List Ty}
    (membership : target ∈ targets) :
    target.nextVar ≤ Ty.nextVarList targets := by
  induction targets with
  | nil => simp at membership
  | cons head tail induction =>
      simp only [List.mem_cons] at membership
      simp only [Ty.nextVarList]
      rcases membership with equality | membership
      · subst target
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (induction membership) (Nat.le_max_right _ _)

/-- A pointwise bound on a type list bounds its aggregate next-variable
index. -/
theorem nextVarList_le_of_forall_mem
    {targets : List Ty} {bound : Nat}
    (bounded : ∀ target, target ∈ targets → target.nextVar ≤ bound) :
    Ty.nextVarList targets ≤ bound := by
  induction targets with
  | nil => simp [Ty.nextVarList]
  | cons target targets induction =>
      simp only [Ty.nextVarList]
      apply (Nat.max_le).2
      constructor
      · exact bounded target (by simp)
      · apply induction
        intro member membership
        exact bounded member (by simp [membership])

mutual

/-- An ordinary variable occurring in a type has an index below that type's
next-variable bound. -/
theorem index_lt_nextVar_of_occursTy
    {needle : TyVar} {target : Ty}
    (occurs : TyVarOccurs needle target) :
    needle.index < target.nextVar := by
  cases occurs with
  | var =>
      simp [Ty.nextVar]
  | fnDomain domainOccurs =>
      exact Nat.lt_of_lt_of_le
        (index_lt_nextVar_of_occursTy domainOccurs) (Nat.le_max_left _ _)
  | fnCodomain codomainOccurs =>
      exact Nat.lt_of_lt_of_le
        (index_lt_nextVar_of_occursTy codomainOccurs) (Nat.le_max_right _ _)
  | prod listOccurs =>
      exact index_lt_nextVarList_of_occursTyList listOccurs
  | data listOccurs =>
      exact index_lt_nextVarList_of_occursTyList listOccurs
  | matcher targetOccurs =>
      simpa [Ty.nextVar] using index_lt_nextVar_of_occursTy targetOccurs
  | slot targetOccurs =>
      simpa [Ty.nextVar] using index_lt_nextVar_of_occursTy targetOccurs

/-- List counterpart of `index_lt_nextVar_of_occursTy`. -/
theorem index_lt_nextVarList_of_occursTyList
    {needle : TyVar} {targets : List Ty}
    (occurs : TyVarOccursList needle targets) :
    needle.index < Ty.nextVarList targets := by
  cases occurs with
  | head targetOccurs =>
      exact Nat.lt_of_lt_of_le
        (index_lt_nextVar_of_occursTy targetOccurs) (Nat.le_max_left _ _)
  | tail targetsOccur =>
      exact Nat.lt_of_lt_of_le
        (index_lt_nextVarList_of_occursTyList targetsOccur)
        (Nat.le_max_right _ _)

end

end Ty

namespace TyVarOccursList

/-- A list-occurrence derivation identifies a concrete member containing the
variable. -/
theorem exists_mem
    {needle : TyVar} {targets : List Ty}
    (occurs : TyVarOccursList needle targets) :
    ∃ target, target ∈ targets ∧ TyVarOccurs needle target := by
  cases occurs with
  | head targetOccurs =>
      exact ⟨_, by simp, targetOccurs⟩
  | tail targetsOccur =>
      obtain ⟨target, membership, targetOccurs⟩ := exists_mem targetsOccur
      exact ⟨target, by simp [membership], targetOccurs⟩

end TyVarOccursList

namespace Context

/-- A successful indexed lookup witnesses list membership. -/
theorem mem_of_getElem?_eq_some
    {context : Context} {index : Nat} {target : Ty}
    (lookup : context[index]? = some target) :
    target ∈ context := by
  induction context generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          simp at lookup
          subst target
          simp
      | succ index =>
          simp at lookup
          exact List.mem_cons_of_mem head (induction lookup)

/-- A type stored in a context is bounded by the context's root supply. -/
theorem type_nextVar_le_nextVar_of_mem
    {context : Context} {target : Ty}
    (membership : target ∈ context) :
    target.nextVar ≤ context.nextVar := by
  exact Ty.nextVar_le_nextVarList_of_mem membership

/-- Lookup form of `type_nextVar_le_nextVar_of_mem`. -/
theorem type_nextVar_le_nextVar_of_getElem?_eq_some
    {context : Context} {index : Nat} {target : Ty}
    (lookup : context[index]? = some target) :
    target.nextVar ≤ context.nextVar := by
  induction context generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          simp at lookup
          subst target
          exact Nat.le_max_left _ _
      | succ index =>
          simp at lookup
          exact Nat.le_trans (induction lookup) (Nat.le_max_right _ _)

/-- Every ordinary variable occurring in a context entry is strictly below
the context's root supply. -/
theorem index_lt_nextVar_of_lookup_occurs
    {context : Context} {position : Nat} {target : Ty} {needle : TyVar}
    (lookup : context[position]? = some target)
    (occurs : TyVarOccurs needle target) :
    needle.index < context.nextVar := by
  exact Nat.lt_of_lt_of_le
    (Ty.index_lt_nextVar_of_occursTy occurs)
    (type_nextVar_le_nextVar_of_getElem?_eq_some lookup)

/-- If a generator starts no lower than `Context.nextVar`, every variable in
the original context lies strictly below its allocation range. -/
theorem index_lt_supply_of_lookup_occurs
    {context : Context} {position : Nat} {target : Ty} {needle : TyVar}
    {supply : Nat}
    (rootBound : context.nextVar ≤ supply)
    (lookup : context[position]? = some target)
    (occurs : TyVarOccurs needle target) :
    needle.index < supply := by
  exact Nat.lt_of_lt_of_le
    (index_lt_nextVar_of_lookup_occurs lookup occurs) rootBound

/-- Extending a context by the variable at the current supply advances its
root bound by exactly one, provided the old context is already below the
supply. -/
theorem nextVar_cons_fresh
    {context : Context} {supply : Nat}
    (rootBound : context.nextVar ≤ supply) :
    Context.nextVar (.var ⟨supply⟩ :: context) = supply + 1 := by
  simp only [Context.nextVar, Ty.nextVarList, Ty.nextVar]
  exact Nat.max_eq_left (Nat.le_trans rootBound (Nat.le_add_right supply 1))

end Context

mutual

/-- If generation starts above the context, every ordinary type variable in
its complete output is below the returned supply. -/
theorem Generates.tyVarsBelow_next
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (derivation : Generates context expression supply generated next)
    (contextBound : context.nextVar ≤ supply) :
    generated.tyVarsBelow next := by
  cases derivation with
  | var lookup =>
      refine ⟨?_, ?_, ?_⟩
      · exact Nat.le_trans
          (Context.type_nextVar_le_nextVar_of_getElem?_eq_some lookup)
          contextBound
      · simp
      · simp
  | lit =>
      simp [Generated.tyVarsBelow, Ty.tyVarsBelow, Ty.nextVar]
  | something =>
      simp [Generated.tyVarsBelow, Ty.tyVarsBelow, Ty.nextVar]
  | lam bodyDerivation =>
      have bodyContextBound :
          Context.nextVar (.var ⟨supply⟩ :: context) ≤ supply + 1 := by
        rw [Context.nextVar_cons_fresh contextBound]
        exact Nat.le_refl _
      have bodyBound :=
        Generates.tyVarsBelow_next bodyDerivation bodyContextBound
      have bodySupply := Generates.supply_le_next bodyDerivation
      refine ⟨?_, bodyBound.2.1, bodyBound.2.2⟩
      exact (Nat.max_le).2 ⟨bodySupply, bodyBound.1⟩
  | app functionDerivation argumentDerivation =>
      have functionSupply := Generates.supply_le_next functionDerivation
      have argumentSupply := Generates.supply_le_next argumentDerivation
      have functionBound :=
        Generates.tyVarsBelow_next functionDerivation contextBound
      have argumentContextBound := Nat.le_trans contextBound functionSupply
      have argumentBound :=
        Generates.tyVarsBelow_next argumentDerivation argumentContextBound
      refine ⟨?_, ?_, ?_⟩
      · simp [Ty.tyVarsBelow, Ty.nextVar]
      · intro equation membership
        simp only [List.mem_append, List.mem_singleton] at membership
        rcases membership with (functionMember | argumentMember) | equality
        · exact Equation.tyVarsBelow_mono
            (functionBound.2.1 equation functionMember) (by omega)
        · exact Equation.tyVarsBelow_mono
            (argumentBound.2.1 equation argumentMember) (by omega)
        · subst equation
          refine ⟨Ty.tyVarsBelow_mono functionBound.1 (by omega), ?_⟩
          simp [Ty.tyVarsBelow, Ty.nextVar]
      · intro obligation membership
        simp only [List.mem_append, List.mem_singleton] at membership
        rcases membership with (functionMember | argumentMember) | equality
        · exact CheckObligation.tyVarsBelow_mono
            (functionBound.2.2 obligation functionMember) (by omega)
        · exact CheckObligation.tyVarsBelow_mono
            (argumentBound.2.2 obligation argumentMember) (by omega)
        · subst obligation
          refine ⟨Ty.tyVarsBelow_mono argumentBound.1 (by omega), ?_⟩
          simp [Ty.tyVarsBelow, Ty.nextVar]
  | tuple itemsDerivation =>
      have itemsBound :=
        GeneratesItems.tyVarsBelow_next itemsDerivation contextBound
      refine ⟨?_, itemsBound.2.1, itemsBound.2.2⟩
      exact Ty.nextVarList_le_of_forall_mem itemsBound.1

/-- List counterpart of `Generates.tyVarsBelow_next`. -/
theorem GeneratesItems.tyVarsBelow_next
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems}
    (derivation : GeneratesItems context expressions supply generated next)
    (contextBound : context.nextVar ≤ supply) :
    generated.tyVarsBelow next := by
  cases derivation with
  | nil =>
      simp [GeneratedItems.tyVarsBelow]
  | cons itemDerivation itemsDerivation =>
      have itemSupply := Generates.supply_le_next itemDerivation
      have itemsSupply := GeneratesItems.supply_le_next itemsDerivation
      have itemBound :=
        Generates.tyVarsBelow_next itemDerivation contextBound
      have itemsContextBound := Nat.le_trans contextBound itemSupply
      have itemsBound :=
        GeneratesItems.tyVarsBelow_next itemsDerivation itemsContextBound
      have itemFinal :=
        Generated.tyVarsBelow_mono itemBound itemsSupply
      refine ⟨?_, ?_, ?_⟩
      · intro target membership
        simp only [List.mem_cons] at membership
        rcases membership with equality | membership
        · subst target
          exact itemFinal.1
        · exact itemsBound.1 target membership
      · intro equation membership
        simp only [List.mem_append] at membership
        rcases membership with membership | membership
        · exact itemFinal.2.1 equation membership
        · exact itemsBound.2.1 equation membership
      · intro obligation membership
        simp only [List.mem_append] at membership
        rcases membership with membership | membership
        · exact itemFinal.2.2 obligation membership
        · exact itemsBound.2.2 obligation membership

end

/-- Executable form of the complete generated-output upper bound. -/
theorem generate_tyVarsBelow_next
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (success : generate context expression supply = some (generated, next))
    (contextBound : context.nextVar ≤ supply) :
    generated.tyVarsBelow next :=
  (generate_to_generates success).tyVarsBelow_next contextBound

/-- Executable list form of the complete generated-output upper bound. -/
theorem generateItems_tyVarsBelow_next
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems}
    (success : generateItems context expressions supply = some (generated, next))
    (contextBound : context.nextVar ≤ supply) :
    generated.tyVarsBelow next :=
  (generateItems_to_generatesItems success).tyVarsBelow_next contextBound

namespace Generated

/-- Target projection of `Generated.tyVarsBelow`. -/
theorem target_index_lt
    {generated : Generated} {bound : Nat} {needle : TyVar}
    (bounded : generated.tyVarsBelow bound)
    (occurs : TyVarOccurs needle generated.target) :
    needle.index < bound := by
  exact Nat.lt_of_lt_of_le
    (Ty.index_lt_nextVar_of_occursTy occurs) bounded.1

/-- Left-hand projection for an ordinary-type hard equation. -/
theorem hard_ty_left_index_lt
    {generated : Generated} {bound : Nat} {needle : TyVar}
    {left right : Ty}
    (bounded : generated.tyVarsBelow bound)
    (membership : Equation.ty left right ∈ generated.hard)
    (occurs : TyVarOccurs needle left) :
    needle.index < bound := by
  have equationBound := bounded.2.1 (.ty left right) membership
  exact Nat.lt_of_lt_of_le
    (Ty.index_lt_nextVar_of_occursTy occurs) equationBound.1

/-- Right-hand projection for an ordinary-type hard equation. -/
theorem hard_ty_right_index_lt
    {generated : Generated} {bound : Nat} {needle : TyVar}
    {left right : Ty}
    (bounded : generated.tyVarsBelow bound)
    (membership : Equation.ty left right ∈ generated.hard)
    (occurs : TyVarOccurs needle right) :
    needle.index < bound := by
  have equationBound := bounded.2.1 (.ty left right) membership
  exact Nat.lt_of_lt_of_le
    (Ty.index_lt_nextVar_of_occursTy occurs) equationBound.2

/-- Source projection for a pending checking obligation. -/
theorem pending_source_index_lt
    {generated : Generated} {bound : Nat} {needle : TyVar}
    {obligation : CheckObligation}
    (bounded : generated.tyVarsBelow bound)
    (membership : obligation ∈ generated.pending)
    (occurs : TyVarOccurs needle obligation.source) :
    needle.index < bound := by
  have obligationBound := bounded.2.2 obligation membership
  exact Nat.lt_of_lt_of_le
    (Ty.index_lt_nextVar_of_occursTy occurs) obligationBound.1

/-- Expected-type projection for a pending checking obligation. -/
theorem pending_expected_index_lt
    {generated : Generated} {bound : Nat} {needle : TyVar}
    {obligation : CheckObligation}
    (bounded : generated.tyVarsBelow bound)
    (membership : obligation ∈ generated.pending)
    (occurs : TyVarOccurs needle obligation.expected) :
    needle.index < bound := by
  have obligationBound := bounded.2.2 obligation membership
  exact Nat.lt_of_lt_of_le
    (Ty.index_lt_nextVar_of_occursTy occurs) obligationBound.2

end Generated

/-! ## Lower bounds for variables introduced by generation -/

/-- An ordinary variable originates in the external monomorphic context when
it occurs in one of its stored types. -/
def TyVarOccursInContext (needle : TyVar) (context : Context) : Prop :=
  ∃ target, target ∈ context ∧ TyVarOccurs needle target

/-- Every variable in a type either originates in `context` or is in the
generator's allocation range starting at `supply`. -/
def Ty.varsFromContextOrFresh
    (context : Context) (supply : Nat) (target : Ty) : Prop :=
  ∀ needle, TyVarOccurs needle target →
    TyVarOccursInContext needle context ∨ supply ≤ needle.index

def Equation.tyVarsFromContextOrFresh
    (context : Context) (supply : Nat) : Equation → Prop
  | .ty left right =>
      left.varsFromContextOrFresh context supply ∧
        right.varsFromContextOrFresh context supply
  | .cap _ _ => True

def CheckObligation.tyVarsFromContextOrFresh
    (context : Context) (supply : Nat)
    (obligation : CheckObligation) : Prop :=
  obligation.source.varsFromContextOrFresh context supply ∧
    obligation.expected.varsFromContextOrFresh context supply

def Generated.tyVarsFromContextOrFresh
    (context : Context) (supply : Nat) (generated : Generated) : Prop :=
  generated.target.varsFromContextOrFresh context supply ∧
  (∀ equation, equation ∈ generated.hard →
    equation.tyVarsFromContextOrFresh context supply) ∧
  (∀ obligation, obligation ∈ generated.pending →
    obligation.tyVarsFromContextOrFresh context supply)

def GeneratedItems.tyVarsFromContextOrFresh
    (context : Context) (supply : Nat) (generated : GeneratedItems) : Prop :=
  (∀ target, target ∈ generated.targets →
    target.varsFromContextOrFresh context supply) ∧
  (∀ equation, equation ∈ generated.hard →
    equation.tyVarsFromContextOrFresh context supply) ∧
  (∀ obligation, obligation ∈ generated.pending →
    obligation.tyVarsFromContextOrFresh context supply)

namespace Ty

/-- Lowering the start of the allocation range preserves the origin
property. -/
theorem varsFromContextOrFresh_monoSupply
    {context : Context} {earlier later : Nat} {target : Ty}
    (bounded : target.varsFromContextOrFresh context later)
    (le : earlier ≤ later) :
    target.varsFromContextOrFresh context earlier := by
  intro needle occurs
  rcases bounded needle occurs with contextOrigin | fresh
  · exact Or.inl contextOrigin
  · exact Or.inr (Nat.le_trans le fresh)

/-- A property relative to a freshly extended lambda context can be rebased
to the outer context and the lambda's allocation point. -/
theorem varsFromFreshCons
    {context : Context} {supply : Nat} {target : Ty}
    (bounded : target.varsFromContextOrFresh
      (.var ⟨supply⟩ :: context) (supply + 1)) :
    target.varsFromContextOrFresh context supply := by
  intro needle occurs
  rcases bounded needle occurs with contextOrigin | fresh
  · rcases contextOrigin with ⟨origin, membership, originOccurs⟩
    simp only [List.mem_cons] at membership
    rcases membership with equality | membership
    · subst origin
      cases originOccurs
      exact Or.inr (Nat.le_refl _)
    · exact Or.inl ⟨origin, membership, originOccurs⟩
  · exact Or.inr (by omega)

end Ty

namespace Equation

theorem tyVarsFromContextOrFresh_monoSupply
    {context : Context} {earlier later : Nat} {equation : Equation}
    (bounded : equation.tyVarsFromContextOrFresh context later)
    (le : earlier ≤ later) :
    equation.tyVarsFromContextOrFresh context earlier := by
  cases equation with
  | ty left right =>
      exact ⟨Ty.varsFromContextOrFresh_monoSupply bounded.1 le,
        Ty.varsFromContextOrFresh_monoSupply bounded.2 le⟩
  | cap left right => trivial

theorem tyVarsFromFreshCons
    {context : Context} {supply : Nat} {equation : Equation}
    (bounded : equation.tyVarsFromContextOrFresh
      (.var ⟨supply⟩ :: context) (supply + 1)) :
    equation.tyVarsFromContextOrFresh context supply := by
  cases equation with
  | ty left right =>
      exact ⟨Ty.varsFromFreshCons bounded.1,
        Ty.varsFromFreshCons bounded.2⟩
  | cap left right => trivial

end Equation

namespace CheckObligation

theorem tyVarsFromContextOrFresh_monoSupply
    {context : Context} {earlier later : Nat}
    {obligation : CheckObligation}
    (bounded : obligation.tyVarsFromContextOrFresh context later)
    (le : earlier ≤ later) :
    obligation.tyVarsFromContextOrFresh context earlier :=
  ⟨Ty.varsFromContextOrFresh_monoSupply bounded.1 le,
    Ty.varsFromContextOrFresh_monoSupply bounded.2 le⟩

theorem tyVarsFromFreshCons
    {context : Context} {supply : Nat} {obligation : CheckObligation}
    (bounded : obligation.tyVarsFromContextOrFresh
      (.var ⟨supply⟩ :: context) (supply + 1)) :
    obligation.tyVarsFromContextOrFresh context supply :=
  ⟨Ty.varsFromFreshCons bounded.1, Ty.varsFromFreshCons bounded.2⟩

end CheckObligation

namespace Generated

theorem tyVarsFromFreshCons
    {context : Context} {supply : Nat} {generated : Generated}
    (bounded : generated.tyVarsFromContextOrFresh
      (.var ⟨supply⟩ :: context) (supply + 1)) :
    generated.tyVarsFromContextOrFresh context supply := by
  refine ⟨Ty.varsFromFreshCons bounded.1, ?_, ?_⟩
  · intro equation membership
    exact Equation.tyVarsFromFreshCons (bounded.2.1 equation membership)
  · intro obligation membership
    exact CheckObligation.tyVarsFromFreshCons
      (bounded.2.2 obligation membership)

theorem tyVarsFromContextOrFresh_monoSupply
    {context : Context} {earlier later : Nat} {generated : Generated}
    (bounded : generated.tyVarsFromContextOrFresh context later)
    (le : earlier ≤ later) :
    generated.tyVarsFromContextOrFresh context earlier := by
  refine ⟨Ty.varsFromContextOrFresh_monoSupply bounded.1 le, ?_, ?_⟩
  · intro equation membership
    exact Equation.tyVarsFromContextOrFresh_monoSupply
      (bounded.2.1 equation membership) le
  · intro obligation membership
    exact CheckObligation.tyVarsFromContextOrFresh_monoSupply
      (bounded.2.2 obligation membership) le

end Generated

mutual

/-- Every variable in a relational generation result is either inherited
from the starting context or allocated at/above the starting supply. -/
theorem Generates.tyVarsFromContextOrFresh
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (derivation : Generates context expression supply generated next) :
    generated.tyVarsFromContextOrFresh context supply := by
  cases derivation with
  | var lookup =>
      refine ⟨?_, ?_, ?_⟩
      · intro needle occurs
        exact Or.inl ⟨_, Context.mem_of_getElem?_eq_some lookup, occurs⟩
      · simp
      · simp
  | lit =>
      simp [Generated.tyVarsFromContextOrFresh,
        Ty.varsFromContextOrFresh]
      intro needle occurs
      cases occurs
  | something =>
      refine ⟨?_, by simp, by simp⟩
      intro needle occurs
      cases occurs with
      | matcher targetOccurs =>
          cases targetOccurs
          exact Or.inr (Nat.le_refl _)
  | lam bodyDerivation =>
      have bodyBound := Generated.tyVarsFromFreshCons
        (Generates.tyVarsFromContextOrFresh bodyDerivation)
      refine ⟨?_, bodyBound.2.1, bodyBound.2.2⟩
      intro needle occurs
      cases occurs with
      | fnDomain domainOccurs =>
          cases domainOccurs
          exact Or.inr (Nat.le_refl _)
      | fnCodomain codomainOccurs =>
          exact bodyBound.1 needle codomainOccurs
  | app functionDerivation argumentDerivation =>
      have functionSupply := Generates.supply_le_next functionDerivation
      have functionBound :=
        Generates.tyVarsFromContextOrFresh functionDerivation
      have argumentBoundLater :=
        Generates.tyVarsFromContextOrFresh argumentDerivation
      have argumentBound :=
        Generated.tyVarsFromContextOrFresh_monoSupply
          argumentBoundLater functionSupply
      have startBeforeArgument := Nat.le_trans functionSupply
        (Generates.supply_le_next argumentDerivation)
      refine ⟨?_, ?_, ?_⟩
      · intro needle occurs
        cases occurs
        exact Or.inr (by
          have stepped := Nat.le_trans startBeforeArgument
            (Nat.le_add_right _ 1)
          simpa using stepped)
      · intro equation membership
        simp only [List.mem_append, List.mem_singleton] at membership
        rcases membership with (functionMember | argumentMember) | equality
        · exact functionBound.2.1 equation functionMember
        · exact argumentBound.2.1 equation argumentMember
        · subst equation
          refine ⟨functionBound.1, ?_⟩
          intro needle occurs
          cases occurs with
          | fnDomain domainOccurs =>
              cases domainOccurs
              exact Or.inr startBeforeArgument
          | fnCodomain codomainOccurs =>
              cases codomainOccurs
              exact Or.inr (by
                have stepped := Nat.le_trans startBeforeArgument
                  (Nat.le_add_right _ 1)
                simpa using stepped)
      · intro obligation membership
        simp only [List.mem_append, List.mem_singleton] at membership
        rcases membership with (functionMember | argumentMember) | equality
        · exact functionBound.2.2 obligation functionMember
        · exact argumentBound.2.2 obligation argumentMember
        · subst obligation
          refine ⟨argumentBound.1, ?_⟩
          intro needle occurs
          cases occurs
          exact Or.inr startBeforeArgument
  | tuple itemsDerivation =>
      have itemsBound :=
        GeneratesItems.tyVarsFromContextOrFresh itemsDerivation
      refine ⟨?_, itemsBound.2.1, itemsBound.2.2⟩
      intro needle occurs
      cases occurs with
      | prod listOccurs =>
          obtain ⟨target, membership, targetOccurs⟩ := listOccurs.exists_mem
          exact itemsBound.1 target membership needle targetOccurs

/-- List counterpart of `Generates.tyVarsFromContextOrFresh`. -/
theorem GeneratesItems.tyVarsFromContextOrFresh
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems}
    (derivation : GeneratesItems context expressions supply generated next) :
    generated.tyVarsFromContextOrFresh context supply := by
  cases derivation with
  | nil => simp [GeneratedItems.tyVarsFromContextOrFresh]
  | cons itemDerivation itemsDerivation =>
      have itemSupply := Generates.supply_le_next itemDerivation
      have itemBound := Generates.tyVarsFromContextOrFresh itemDerivation
      have itemsBoundLater :=
        GeneratesItems.tyVarsFromContextOrFresh itemsDerivation
      refine ⟨?_, ?_, ?_⟩
      · intro target membership
        simp only [List.mem_cons] at membership
        rcases membership with equality | membership
        · subst target
          exact itemBound.1
        · exact Ty.varsFromContextOrFresh_monoSupply
            (itemsBoundLater.1 target membership) itemSupply
      · intro equation membership
        simp only [List.mem_append] at membership
        rcases membership with membership | membership
        · exact itemBound.2.1 equation membership
        · exact Equation.tyVarsFromContextOrFresh_monoSupply
            (itemsBoundLater.2.1 equation membership) itemSupply
      · intro obligation membership
        simp only [List.mem_append] at membership
        rcases membership with membership | membership
        · exact itemBound.2.2 obligation membership
        · exact CheckObligation.tyVarsFromContextOrFresh_monoSupply
            (itemsBoundLater.2.2 obligation membership) itemSupply

end

/-- Executable form of the context-origin/allocation-range lower bound. -/
theorem generate_tyVarsFromContextOrFresh
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (success : generate context expression supply = some (generated, next)) :
    generated.tyVarsFromContextOrFresh context supply :=
  (generate_to_generates success).tyVarsFromContextOrFresh

/-- The complete generated-output invariant: all variables are below `next`,
and every variable not inherited from the context is at least `supply`. -/
theorem Generates.tyVarsWellScoped
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (derivation : Generates context expression supply generated next)
    (contextBound : context.nextVar ≤ supply) :
    generated.tyVarsBelow next ∧
      generated.tyVarsFromContextOrFresh context supply :=
  ⟨derivation.tyVarsBelow_next contextBound,
    derivation.tyVarsFromContextOrFresh⟩

/-- Executable form of `Generates.tyVarsWellScoped`. -/
theorem generate_tyVarsWellScoped
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (success : generate context expression supply = some (generated, next))
    (contextBound : context.nextVar ≤ supply) :
    generated.tyVarsBelow next ∧
      generated.tyVarsFromContextOrFresh context supply :=
  (generate_to_generates success).tyVarsWellScoped contextBound

/-- A target variable absent from the context lies in exactly the generated
half-open interval `[supply, next)`. -/
theorem Generates.target_fresh_range
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated} {needle : TyVar}
    (derivation : Generates context expression supply generated next)
    (contextBound : context.nextVar ≤ supply)
    (occurs : TyVarOccurs needle generated.target)
    (notFromContext : ¬ TyVarOccursInContext needle context) :
    supply ≤ needle.index ∧ needle.index < next := by
  have wellScoped := derivation.tyVarsWellScoped contextBound
  refine ⟨?_, Generated.target_index_lt wellScoped.1 occurs⟩
  rcases wellScoped.2.1 needle occurs with contextOrigin | fresh
  · exact False.elim (notFromContext contextOrigin)
  · exact fresh

/-- A variable on the left of a generated type equation, when absent from the
context, lies in `[supply, next)`. -/
theorem Generates.hard_ty_left_fresh_range
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated} {needle : TyVar} {left right : Ty}
    (derivation : Generates context expression supply generated next)
    (contextBound : context.nextVar ≤ supply)
    (membership : Equation.ty left right ∈ generated.hard)
    (occurs : TyVarOccurs needle left)
    (notFromContext : ¬ TyVarOccursInContext needle context) :
    supply ≤ needle.index ∧ needle.index < next := by
  have wellScoped := derivation.tyVarsWellScoped contextBound
  refine ⟨?_, Generated.hard_ty_left_index_lt
    wellScoped.1 membership occurs⟩
  have originBound := wellScoped.2.2.1 (.ty left right) membership
  rcases originBound.1 needle occurs with contextOrigin | fresh
  · exact False.elim (notFromContext contextOrigin)
  · exact fresh

/-- Right-hand counterpart of `hard_ty_left_fresh_range`. -/
theorem Generates.hard_ty_right_fresh_range
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated} {needle : TyVar} {left right : Ty}
    (derivation : Generates context expression supply generated next)
    (contextBound : context.nextVar ≤ supply)
    (membership : Equation.ty left right ∈ generated.hard)
    (occurs : TyVarOccurs needle right)
    (notFromContext : ¬ TyVarOccursInContext needle context) :
    supply ≤ needle.index ∧ needle.index < next := by
  have wellScoped := derivation.tyVarsWellScoped contextBound
  refine ⟨?_, Generated.hard_ty_right_index_lt
    wellScoped.1 membership occurs⟩
  have originBound := wellScoped.2.2.1 (.ty left right) membership
  rcases originBound.2 needle occurs with contextOrigin | fresh
  · exact False.elim (notFromContext contextOrigin)
  · exact fresh

/-- A variable in the source of a pending obligation, when absent from the
context, lies in `[supply, next)`. -/
theorem Generates.pending_source_fresh_range
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated} {needle : TyVar}
    {obligation : CheckObligation}
    (derivation : Generates context expression supply generated next)
    (contextBound : context.nextVar ≤ supply)
    (membership : obligation ∈ generated.pending)
    (occurs : TyVarOccurs needle obligation.source)
    (notFromContext : ¬ TyVarOccursInContext needle context) :
    supply ≤ needle.index ∧ needle.index < next := by
  have wellScoped := derivation.tyVarsWellScoped contextBound
  refine ⟨?_, Generated.pending_source_index_lt
    wellScoped.1 membership occurs⟩
  have originBound := wellScoped.2.2.2 obligation membership
  rcases originBound.1 needle occurs with contextOrigin | fresh
  · exact False.elim (notFromContext contextOrigin)
  · exact fresh

/-- Expected-type counterpart of `pending_source_fresh_range`. -/
theorem Generates.pending_expected_fresh_range
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated} {needle : TyVar}
    {obligation : CheckObligation}
    (derivation : Generates context expression supply generated next)
    (contextBound : context.nextVar ≤ supply)
    (membership : obligation ∈ generated.pending)
    (occurs : TyVarOccurs needle obligation.expected)
    (notFromContext : ¬ TyVarOccursInContext needle context) :
    supply ≤ needle.index ∧ needle.index < next := by
  have wellScoped := derivation.tyVarsWellScoped contextBound
  refine ⟨?_, Generated.pending_expected_index_lt
    wellScoped.1 membership occurs⟩
  have originBound := wellScoped.2.2.2 obligation membership
  rcases originBound.2 needle occurs with contextOrigin | fresh
  · exact False.elim (notFromContext contextOrigin)
  · exact fresh

end TypePM
