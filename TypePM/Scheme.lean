import TypePM.Substitution

/-!
# Bound-index polymorphic type schemes

The source-language layer represents a quantified variable by a natural-number
position, while a free variable retains its `TyVar` or `CapVar` name.  Because
the two forms are different constructors, applying a substitution to free
variables never has to rename binders.  In particular, applying the identity
substitution is literal equality, not merely equality up to binder renaming.
-/

namespace TypePM

/-! ## Finite free-variable collections for monotypes -/

mutual

def Ty.tyVars : Ty → List TyVar
  | .var index => [index]
  | .int => []
  | .fn domain codomain => domain.tyVars ++ codomain.tyVars
  | .prod items => Ty.tyVarsList items
  | .matcher _ target => target.tyVars
  | .slot _ target => target.tyVars

def Ty.tyVarsList : List Ty → List TyVar
  | [] => []
  | item :: items => item.tyVars ++ Ty.tyVarsList items

end


mutual

def Cap.capVars : Cap → List CapVar
  | .any => []
  | .var index => [index]
  | .prod items => Cap.capVarsList items

def Cap.capVarsList : List Cap → List CapVar
  | [] => []
  | item :: items => item.capVars ++ Cap.capVarsList items

end


mutual

def Ty.capVars : Ty → List CapVar
  | .var _ => []
  | .int => []
  | .fn domain codomain => domain.capVars ++ codomain.capVars
  | .prod items => Ty.capVarsList items
  | .matcher capability target => capability.capVars ++ target.capVars
  | .slot capability target => capability.capVars ++ target.capVars

def Ty.capVarsList : List Ty → List CapVar
  | [] => []
  | item :: items => item.capVars ++ Ty.capVarsList items

end


def TyVar.next : List TyVar → Nat
  | [] => 0
  | index :: indices => max (index.index + 1) (TyVar.next indices)

def CapVar.next : List CapVar → Nat
  | [] => 0
  | index :: indices => max (index.index + 1) (CapVar.next indices)

theorem TyVar.index_lt_next {index : TyVar} {indices : List TyVar}
    (member : index ∈ indices) : index.index < TyVar.next indices := by
  induction indices with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst index
        simp only [TyVar.next]
        omega
      · simp only [TyVar.next]
        have := ih member
        omega

theorem CapVar.index_lt_next {index : CapVar} {indices : List CapVar}
    (member : index ∈ indices) : index.index < CapVar.next indices := by
  induction indices with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst index
        simp only [CapVar.next]
        omega
      · simp only [CapVar.next]
        have := ih member
        omega

/-! ## Stable duplicate removal -/

/-- Duplicate removal which retains the last occurrence. -/
def dedup [BEq α] : List α → List α
  | [] => []
  | item :: items =>
      if items.contains item then dedup items else item :: dedup items

theorem mem_dedup [BEq α] [LawfulBEq α] {item : α} {items : List α} :
    item ∈ dedup items ↔ item ∈ items := by
  induction items with
  | nil => simp [dedup]
  | cons head tail ih =>
      simp only [dedup]
      split <;> rename_i present
      · rw [List.contains_iff_mem] at present
        constructor
        · intro member
          exact List.mem_cons_of_mem head (ih.mp member)
        · intro member
          apply ih.mpr
          by_cases equality : item = head
          · rw [equality]
            exact present
          · simp [List.mem_cons, equality] at member
            exact member
      · simp only [List.mem_cons]
        rw [ih]

theorem dedup_nodup [BEq α] [LawfulBEq α] (items : List α) :
    (dedup items).Nodup := by
  induction items with
  | nil => simp [dedup]
  | cons item items ih =>
      simp only [dedup]
      split <;> rename_i present
      · exact ih
      · rw [List.nodup_cons]
        exact ⟨fun member => by
          apply present
          rw [List.contains_iff_mem]
          exact mem_dedup.mp member, ih⟩

/-- Duplicate removal which retains the first occurrence and its order. -/
def dedupFirst [BEq α] (items : List α) : List α :=
  (dedup items.reverse).reverse

theorem mem_dedupFirst [BEq α] [LawfulBEq α]
    {item : α} {items : List α} :
    item ∈ dedupFirst items ↔ item ∈ items := by
  simp [dedupFirst, mem_dedup]

theorem dedupFirst_nodup [BEq α] [LawfulBEq α] (items : List α) :
    (dedupFirst items).Nodup := by
  unfold dedupFirst
  change List.Pairwise (fun a b : α => a ≠ b) (dedup items.reverse).reverse
  rw [List.pairwise_reverse]
  apply (dedup_nodup items.reverse).imp
  intro left right unequal equality
  exact unequal equality.symm

theorem dedupFirst_keeps_first_occurrence :
    dedupFirst ([⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨2⟩] : List TyVar) =
      [⟨0⟩, ⟨1⟩, ⟨2⟩] := by
  decide

theorem getElem?_idxOf_of_mem [BEq α] [LawfulBEq α]
    {item : α} {items : List α} (member : item ∈ items) :
    items[items.idxOf item]? = some item := by
  induction items with
  | nil => simp at member
  | cons head tail ih =>
      by_cases equality : head = item
      · subst head
        simp
      · have itemNe : item ≠ head := fun reverse => equality reverse.symm
        have tailMember : item ∈ tail := by
          simpa [List.mem_cons, itemNe] using member
        rw [List.idxOf_cons]
        have beqFalse : (head == item) = false := by
          apply Bool.eq_false_iff.mpr
          intro equal
          exact equality (beq_iff_eq.mp equal)
        rw [beqFalse]
        exact ih tailMember

theorem or_and_common_right (left right common : Prop) :
    (left ∧ common) ∨ (right ∧ common) ↔
      (left ∨ right) ∧ common := by
  constructor
  · intro hypothesis
    rcases hypothesis with hypothesis | hypothesis
    · exact ⟨Or.inl hypothesis.1, hypothesis.2⟩
    · exact ⟨Or.inr hypothesis.1, hypothesis.2⟩
  · intro hypothesis
    rcases hypothesis.1 with leftHolds | rightHolds
    · exact Or.inl ⟨leftHolds, hypothesis.2⟩
    · exact Or.inr ⟨rightHolds, hypothesis.2⟩

namespace Source

/-! ## Bound-index scheme bodies -/

/-- Capabilities in a scheme body.  Free names and bound positions cannot be
confused. -/
inductive PolyCap where
  | any
  | free (index : CapVar)
  | bound (index : Nat)
  | prod (items : List PolyCap)
deriving Repr

/-- Types in a scheme body, with separate constructors for free names and
bound positions of both variable sorts. -/
inductive PolyTy where
  | free (index : TyVar)
  | bound (index : Nat)
  | int
  | fn (domain codomain : PolyTy)
  | prod (items : List PolyTy)
  | matcher (capability : PolyCap) (target : PolyTy)
  | slot (capability : PolyCap) (target : PolyTy)
deriving Repr

/-- Recover a capability name by binder position.  The fallback is unreachable
when opening a well-scoped body closed with the same list. -/
def capNameAt (names : List CapVar) (index : Nat) : Cap :=
  match names[index]? with
  | some name => .var name
  | none => .any

/-- Recover an ordinary type-variable name by binder position. -/
def tyNameAt (names : List TyVar) (index : Nat) : Ty :=
  match names[index]? with
  | some name => .var name
  | none => .int

theorem capNameAt_idxOf {names : List CapVar} {name : CapVar}
    (member : name ∈ names) :
    capNameAt names (names.idxOf name) = .var name := by
  simp [capNameAt, getElem?_idxOf_of_mem member]

theorem tyNameAt_idxOf {names : List TyVar} {name : TyVar}
    (member : name ∈ names) :
    tyNameAt names (names.idxOf name) = .var name := by
  simp [tyNameAt, getElem?_idxOf_of_mem member]

mutual

def PolyCap.ofCap : Cap → PolyCap
  | .any => .any
  | .var index => .free index
  | .prod items => .prod (PolyCap.ofCapList items)

def PolyCap.ofCapList : List Cap → List PolyCap
  | [] => []
  | item :: items => PolyCap.ofCap item :: PolyCap.ofCapList items

end


mutual

def PolyTy.ofTy : Ty → PolyTy
  | .var index => .free index
  | .int => .int
  | .fn domain codomain => .fn (PolyTy.ofTy domain) (PolyTy.ofTy codomain)
  | .prod items => .prod (PolyTy.ofTyList items)
  | .matcher capability target =>
      .matcher (PolyCap.ofCap capability) (PolyTy.ofTy target)
  | .slot capability target =>
      .slot (PolyCap.ofCap capability) (PolyTy.ofTy target)

def PolyTy.ofTyList : List Ty → List PolyTy
  | [] => []
  | item :: items => PolyTy.ofTy item :: PolyTy.ofTyList items

end


mutual

/-- Replace bound capability positions; free variables remain free. -/
def PolyCap.openBound (boundCap : Nat → Cap) : PolyCap → Cap
  | .any => .any
  | .free index => .var index
  | .bound index => boundCap index
  | .prod items => .prod (PolyCap.openBoundList boundCap items)

def PolyCap.openBoundList (boundCap : Nat → Cap) : List PolyCap → List Cap
  | [] => []
  | item :: items => item.openBound boundCap ::
      PolyCap.openBoundList boundCap items

end


mutual

/-- Replace both sorts of bound positions, yielding an ordinary monotype. -/
def PolyTy.openBound (boundTy : Nat → Ty) (boundCap : Nat → Cap) :
    PolyTy → Ty
  | .free index => .var index
  | .bound index => boundTy index
  | .int => .int
  | .fn domain codomain =>
      .fn (domain.openBound boundTy boundCap)
        (codomain.openBound boundTy boundCap)
  | .prod items => .prod (PolyTy.openBoundList boundTy boundCap items)
  | .matcher capability target =>
      .matcher (capability.openBound boundCap)
        (target.openBound boundTy boundCap)
  | .slot capability target =>
      .slot (capability.openBound boundCap)
        (target.openBound boundTy boundCap)

def PolyTy.openBoundList (boundTy : Nat → Ty) (boundCap : Nat → Cap) :
    List PolyTy → List Ty
  | [] => []
  | item :: items => item.openBound boundTy boundCap ::
      PolyTy.openBoundList boundTy boundCap items

end


mutual

def PolyCap.applyFree (substitution : CapSubst) : PolyCap → PolyCap
  | .any => .any
  | .free index => PolyCap.ofCap (substitution index)
  | .bound index => .bound index
  | .prod items => .prod (PolyCap.applyFreeList substitution items)

def PolyCap.applyFreeList (substitution : CapSubst) :
    List PolyCap → List PolyCap
  | [] => []
  | item :: items => item.applyFree substitution ::
      PolyCap.applyFreeList substitution items

end


mutual

/-- Apply a simultaneous substitution only at free-name constructors. -/
def PolyTy.applyFree (substitution : Subst) : PolyTy → PolyTy
  | .free index => PolyTy.ofTy (substitution.ty index)
  | .bound index => .bound index
  | .int => .int
  | .fn domain codomain =>
      .fn (domain.applyFree substitution) (codomain.applyFree substitution)
  | .prod items => .prod (PolyTy.applyFreeList substitution items)
  | .matcher capability target =>
      .matcher (capability.applyFree substitution.cap)
        (target.applyFree substitution)
  | .slot capability target =>
      .slot (capability.applyFree substitution.cap)
        (target.applyFree substitution)

def PolyTy.applyFreeList (substitution : Subst) : List PolyTy → List PolyTy
  | [] => []
  | item :: items => item.applyFree substitution ::
      PolyTy.applyFreeList substitution items

end


mutual

@[simp] theorem PolyCap.ofCap_open (capability : Cap) (boundCap : Nat → Cap) :
    (PolyCap.ofCap capability).openBound boundCap = capability := by
  cases capability with
  | any => rfl
  | var => rfl
  | prod items => simp [PolyCap.ofCap, PolyCap.openBound, PolyCap.ofCapList_open]

@[simp] theorem PolyCap.ofCapList_open
    (items : List Cap) (boundCap : Nat → Cap) :
    PolyCap.openBoundList boundCap (PolyCap.ofCapList items) = items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.ofCapList, PolyCap.openBoundList,
        PolyCap.ofCap_open, PolyCap.ofCapList_open]

end


mutual

@[simp] theorem PolyTy.ofTy_open
    (target : Ty) (boundTy : Nat → Ty) (boundCap : Nat → Cap) :
    (PolyTy.ofTy target).openBound boundTy boundCap = target := by
  cases target with
  | var => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.ofTy, PolyTy.openBound, PolyTy.ofTy_open]
  | prod items => simp [PolyTy.ofTy, PolyTy.openBound, PolyTy.ofTyList_open]
  | matcher capability target =>
      simp [PolyTy.ofTy, PolyTy.openBound, PolyTy.ofTy_open]
  | slot capability target =>
      simp [PolyTy.ofTy, PolyTy.openBound, PolyTy.ofTy_open]

@[simp] theorem PolyTy.ofTyList_open
    (items : List Ty) (boundTy : Nat → Ty) (boundCap : Nat → Cap) :
    PolyTy.openBoundList boundTy boundCap (PolyTy.ofTyList items) = items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.ofTyList, PolyTy.openBoundList,
        PolyTy.ofTy_open, PolyTy.ofTyList_open]

end


mutual

@[simp] theorem PolyCap.applyFree_id (capability : PolyCap) :
    capability.applyFree Subst.id.cap = capability := by
  cases capability with
  | any => rfl
  | free => rfl
  | bound => rfl
  | prod items => simp [PolyCap.applyFree, PolyCap.applyFreeList_id]

@[simp] theorem PolyCap.applyFreeList_id (items : List PolyCap) :
    PolyCap.applyFreeList Subst.id.cap items = items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.applyFreeList, PolyCap.applyFree_id,
        PolyCap.applyFreeList_id]

end


mutual

@[simp] theorem PolyTy.applyFree_id (target : PolyTy) :
    target.applyFree Subst.id = target := by
  cases target with
  | free => rfl
  | bound => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.applyFree, PolyTy.applyFree_id]
  | prod items => simp [PolyTy.applyFree, PolyTy.applyFreeList_id]
  | matcher capability target =>
      simp [PolyTy.applyFree, PolyTy.applyFree_id]
  | slot capability target =>
      simp [PolyTy.applyFree, PolyTy.applyFree_id]

@[simp] theorem PolyTy.applyFreeList_id (items : List PolyTy) :
    PolyTy.applyFreeList Subst.id items = items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.applyFreeList, PolyTy.applyFree_id,
        PolyTy.applyFreeList_id]

end


mutual

def PolyCap.WellScoped (capArity : Nat) : PolyCap → Prop
  | .any => True
  | .free _ => True
  | .bound index => index < capArity
  | .prod items => ∀ item ∈ items, item.WellScoped capArity

def PolyTy.WellScoped (tyArity capArity : Nat) : PolyTy → Prop
  | .free _ => True
  | .bound index => index < tyArity
  | .int => True
  | .fn domain codomain =>
      domain.WellScoped tyArity capArity ∧
        codomain.WellScoped tyArity capArity
  | .prod items =>
      ∀ item ∈ items, item.WellScoped tyArity capArity
  | .matcher capability target =>
      capability.WellScoped capArity ∧ target.WellScoped tyArity capArity
  | .slot capability target =>
      capability.WellScoped capArity ∧ target.WellScoped tyArity capArity

end


mutual

theorem PolyCap.ofCap_wellScoped (capArity : Nat) (capability : Cap) :
    (PolyCap.ofCap capability).WellScoped capArity := by
  cases capability with
  | any => simp [PolyCap.ofCap, PolyCap.WellScoped]
  | var => simp [PolyCap.ofCap, PolyCap.WellScoped]
  | prod items =>
      simp only [PolyCap.ofCap, PolyCap.WellScoped]
      exact PolyCap.ofCapList_wellScoped capArity items

theorem PolyCap.ofCapList_wellScoped (capArity : Nat) (items : List Cap) :
    ∀ item ∈ PolyCap.ofCapList items, item.WellScoped capArity := by
  cases items with
  | nil => simp [PolyCap.ofCapList]
  | cons item items =>
      intro candidate membership
      simp only [PolyCap.ofCapList, List.mem_cons] at membership
      rcases membership with equality | membership
      · subst candidate
        exact PolyCap.ofCap_wellScoped capArity item
      · exact PolyCap.ofCapList_wellScoped capArity items
          candidate membership

end


mutual

theorem PolyTy.ofTy_wellScoped
    (tyArity capArity : Nat) (target : Ty) :
    (PolyTy.ofTy target).WellScoped tyArity capArity := by
  cases target with
  | var => simp [PolyTy.ofTy, PolyTy.WellScoped]
  | int => simp [PolyTy.ofTy, PolyTy.WellScoped]
  | fn domain codomain =>
      simp only [PolyTy.ofTy, PolyTy.WellScoped]
      exact ⟨PolyTy.ofTy_wellScoped tyArity capArity domain,
        PolyTy.ofTy_wellScoped tyArity capArity codomain⟩
  | prod items =>
      simp only [PolyTy.ofTy, PolyTy.WellScoped]
      exact PolyTy.ofTyList_wellScoped tyArity capArity items
  | matcher capability target =>
      simp only [PolyTy.ofTy, PolyTy.WellScoped]
      exact ⟨PolyCap.ofCap_wellScoped capArity capability,
        PolyTy.ofTy_wellScoped tyArity capArity target⟩
  | slot capability target =>
      simp only [PolyTy.ofTy, PolyTy.WellScoped]
      exact ⟨PolyCap.ofCap_wellScoped capArity capability,
        PolyTy.ofTy_wellScoped tyArity capArity target⟩

theorem PolyTy.ofTyList_wellScoped
    (tyArity capArity : Nat) (items : List Ty) :
    ∀ item ∈ PolyTy.ofTyList items,
      item.WellScoped tyArity capArity := by
  cases items with
  | nil => simp [PolyTy.ofTyList]
  | cons item items =>
      intro candidate membership
      simp only [PolyTy.ofTyList, List.mem_cons] at membership
      rcases membership with equality | membership
      · subst candidate
        exact PolyTy.ofTy_wellScoped tyArity capArity item
      · exact PolyTy.ofTyList_wellScoped tyArity capArity items
          candidate membership

end


mutual

theorem PolyCap.applyFree_wellScoped
    (substitution : CapSubst) (capArity : Nat) {capability : PolyCap}
    (wellScoped : capability.WellScoped capArity) :
    (capability.applyFree substitution).WellScoped capArity := by
  cases capability with
  | any => trivial
  | free index => exact PolyCap.ofCap_wellScoped capArity (substitution index)
  | bound index => exact wellScoped
  | prod items =>
      simp only [PolyCap.WellScoped] at wellScoped
      simp only [PolyCap.applyFree, PolyCap.WellScoped]
      exact PolyCap.applyFreeList_wellScoped substitution capArity items wellScoped

theorem PolyCap.applyFreeList_wellScoped
    (substitution : CapSubst) (capArity : Nat) (items : List PolyCap)
    (wellScoped : ∀ item ∈ items, item.WellScoped capArity) :
    ∀ item ∈ PolyCap.applyFreeList substitution items,
      item.WellScoped capArity := by
  cases items with
  | nil => simp [PolyCap.applyFreeList]
  | cons item items =>
      intro candidate membership
      simp only [PolyCap.applyFreeList, List.mem_cons] at membership
      rcases membership with equality | membership
      · subst candidate
        exact PolyCap.applyFree_wellScoped substitution capArity
          (wellScoped item (by simp))
      · exact PolyCap.applyFreeList_wellScoped substitution capArity items
          (fun candidate member => wellScoped candidate (by simp [member]))
          candidate membership

end


mutual

theorem PolyTy.applyFree_wellScoped
    (substitution : Subst) (tyArity capArity : Nat) {target : PolyTy}
    (wellScoped : target.WellScoped tyArity capArity) :
    (target.applyFree substitution).WellScoped tyArity capArity := by
  cases target with
  | free index =>
      exact PolyTy.ofTy_wellScoped tyArity capArity (substitution.ty index)
  | bound index => exact wellScoped
  | int => trivial
  | fn domain codomain =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.applyFree, PolyTy.WellScoped]
      exact ⟨PolyTy.applyFree_wellScoped substitution tyArity capArity wellScoped.1,
        PolyTy.applyFree_wellScoped substitution tyArity capArity wellScoped.2⟩
  | prod items =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.applyFree, PolyTy.WellScoped]
      exact PolyTy.applyFreeList_wellScoped substitution tyArity capArity
        items wellScoped
  | matcher capability target =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.applyFree, PolyTy.WellScoped]
      exact ⟨PolyCap.applyFree_wellScoped substitution.cap capArity wellScoped.1,
        PolyTy.applyFree_wellScoped substitution tyArity capArity wellScoped.2⟩
  | slot capability target =>
      simp only [PolyTy.WellScoped] at wellScoped
      simp only [PolyTy.applyFree, PolyTy.WellScoped]
      exact ⟨PolyCap.applyFree_wellScoped substitution.cap capArity wellScoped.1,
        PolyTy.applyFree_wellScoped substitution tyArity capArity wellScoped.2⟩

theorem PolyTy.applyFreeList_wellScoped
    (substitution : Subst) (tyArity capArity : Nat) (items : List PolyTy)
    (wellScoped : ∀ item ∈ items, item.WellScoped tyArity capArity) :
    ∀ item ∈ PolyTy.applyFreeList substitution items,
      item.WellScoped tyArity capArity := by
  cases items with
  | nil => simp [PolyTy.applyFreeList]
  | cons item items =>
      intro candidate membership
      simp only [PolyTy.applyFreeList, List.mem_cons] at membership
      rcases membership with equality | membership
      · subst candidate
        exact PolyTy.applyFree_wellScoped substitution tyArity capArity
          (wellScoped item (by simp))
      · exact PolyTy.applyFreeList_wellScoped substitution tyArity capArity
          items (fun candidate member => wellScoped candidate (by simp [member]))
          candidate membership

end


mutual

def PolyCap.close (boundCap : List CapVar) : Cap → PolyCap
  | .any => .any
  | .var index =>
      if boundCap.contains index then .bound (boundCap.idxOf index)
      else .free index
  | .prod items => .prod (PolyCap.closeList boundCap items)

def PolyCap.closeList (boundCap : List CapVar) : List Cap → List PolyCap
  | [] => []
  | item :: items => PolyCap.close boundCap item ::
      PolyCap.closeList boundCap items

end


mutual

def PolyTy.close (boundTy : List TyVar) (boundCap : List CapVar) : Ty → PolyTy
  | .var index =>
      if boundTy.contains index then .bound (boundTy.idxOf index)
      else .free index
  | .int => .int
  | .fn domain codomain =>
      .fn (PolyTy.close boundTy boundCap domain)
        (PolyTy.close boundTy boundCap codomain)
  | .prod items => .prod (PolyTy.closeList boundTy boundCap items)
  | .matcher capability target =>
      .matcher (PolyCap.close boundCap capability)
        (PolyTy.close boundTy boundCap target)
  | .slot capability target =>
      .slot (PolyCap.close boundCap capability)
        (PolyTy.close boundTy boundCap target)

def PolyTy.closeList (boundTy : List TyVar) (boundCap : List CapVar) :
    List Ty → List PolyTy
  | [] => []
  | item :: items => PolyTy.close boundTy boundCap item ::
      PolyTy.closeList boundTy boundCap items

end


mutual

@[simp] theorem PolyCap.close_nil (capability : Cap) :
    PolyCap.close [] capability = PolyCap.ofCap capability := by
  cases capability with
  | any => rfl
  | var => rfl
  | prod items =>
      simp [PolyCap.close, PolyCap.ofCap, PolyCap.closeList_nil]

@[simp] theorem PolyCap.closeList_nil (items : List Cap) :
    PolyCap.closeList [] items = PolyCap.ofCapList items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.closeList, PolyCap.ofCapList,
        PolyCap.close_nil, PolyCap.closeList_nil]

end


mutual

@[simp] theorem PolyTy.close_nil (target : Ty) :
    PolyTy.close [] [] target = PolyTy.ofTy target := by
  cases target with
  | var => rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.close, PolyTy.ofTy, PolyTy.close_nil]
  | prod items =>
      simp [PolyTy.close, PolyTy.ofTy, PolyTy.closeList_nil]
  | matcher capability target =>
      simp [PolyTy.close, PolyTy.ofTy, PolyTy.close_nil]
  | slot capability target =>
      simp [PolyTy.close, PolyTy.ofTy, PolyTy.close_nil]

@[simp] theorem PolyTy.closeList_nil (items : List Ty) :
    PolyTy.closeList [] [] items = PolyTy.ofTyList items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.closeList, PolyTy.ofTyList,
        PolyTy.close_nil, PolyTy.closeList_nil]

end


mutual

@[simp] theorem PolyCap.open_close
    (boundCap : List CapVar) (capability : Cap) :
    (PolyCap.close boundCap capability).openBound (capNameAt boundCap) =
      capability := by
  cases capability with
  | any => rfl
  | var index =>
      simp only [PolyCap.close]
      split <;> rename_i membership
      · rw [PolyCap.openBound]
        exact capNameAt_idxOf (List.contains_iff_mem.mp membership)
      · rfl
  | prod items =>
      simp [PolyCap.close, PolyCap.openBound, PolyCap.openCloseList]

@[simp] theorem PolyCap.openCloseList
    (boundCap : List CapVar) (items : List Cap) :
    PolyCap.openBoundList (capNameAt boundCap)
      (PolyCap.closeList boundCap items) = items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyCap.closeList, PolyCap.openBoundList,
        PolyCap.open_close, PolyCap.openCloseList]

end


mutual

@[simp] theorem PolyTy.open_close
    (boundTy : List TyVar) (boundCap : List CapVar) (target : Ty) :
    (PolyTy.close boundTy boundCap target).openBound
      (tyNameAt boundTy) (capNameAt boundCap) = target := by
  cases target with
  | var index =>
      simp only [PolyTy.close]
      split <;> rename_i membership
      · rw [PolyTy.openBound]
        exact tyNameAt_idxOf (List.contains_iff_mem.mp membership)
      · rfl
  | int => rfl
  | fn domain codomain =>
      simp [PolyTy.close, PolyTy.openBound, PolyTy.open_close]
  | prod items =>
      simp [PolyTy.close, PolyTy.openBound, PolyTy.openCloseList]
  | matcher capability target =>
      simp [PolyTy.close, PolyTy.openBound, PolyTy.open_close]
  | slot capability target =>
      simp [PolyTy.close, PolyTy.openBound, PolyTy.open_close]

@[simp] theorem PolyTy.openCloseList
    (boundTy : List TyVar) (boundCap : List CapVar) (items : List Ty) :
    PolyTy.openBoundList (tyNameAt boundTy) (capNameAt boundCap)
      (PolyTy.closeList boundTy boundCap items) = items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [PolyTy.closeList, PolyTy.openBoundList,
        PolyTy.open_close, PolyTy.openCloseList]

end


mutual

theorem PolyCap.close_wellScoped (boundCap : List CapVar) (capability : Cap) :
    (PolyCap.close boundCap capability).WellScoped boundCap.length := by
  cases capability with
  | any => simp [PolyCap.close, PolyCap.WellScoped]
  | var index =>
      simp only [PolyCap.close]
      split <;> rename_i membership
      · simp only [PolyCap.WellScoped]
        exact List.idxOf_lt_length_iff.mpr
          (List.contains_iff_mem.mp membership)
      · simp [PolyCap.WellScoped]
  | prod items =>
      simp only [PolyCap.close, PolyCap.WellScoped]
      exact PolyCap.closeList_wellScoped boundCap items

theorem PolyCap.closeList_wellScoped
    (boundCap : List CapVar) (items : List Cap) :
    ∀ item ∈ PolyCap.closeList boundCap items,
      item.WellScoped boundCap.length := by
  cases items with
  | nil => simp [PolyCap.closeList]
  | cons item items =>
      intro candidate membership
      simp only [PolyCap.closeList, List.mem_cons] at membership
      rcases membership with equality | membership
      · subst candidate
        exact PolyCap.close_wellScoped boundCap item
      · exact PolyCap.closeList_wellScoped boundCap items candidate membership

end


mutual

theorem PolyTy.close_wellScoped
    (boundTy : List TyVar) (boundCap : List CapVar) (target : Ty) :
    (PolyTy.close boundTy boundCap target).WellScoped
      boundTy.length boundCap.length := by
  cases target with
  | var index =>
      simp only [PolyTy.close]
      split <;> rename_i membership
      · simp only [PolyTy.WellScoped]
        exact List.idxOf_lt_length_iff.mpr
          (List.contains_iff_mem.mp membership)
      · simp [PolyTy.WellScoped]
  | int => simp [PolyTy.close, PolyTy.WellScoped]
  | fn domain codomain =>
      simp only [PolyTy.close, PolyTy.WellScoped]
      exact ⟨PolyTy.close_wellScoped boundTy boundCap domain,
        PolyTy.close_wellScoped boundTy boundCap codomain⟩
  | prod items =>
      simp only [PolyTy.close, PolyTy.WellScoped]
      exact PolyTy.closeList_wellScoped boundTy boundCap items
  | matcher capability target =>
      simp only [PolyTy.close, PolyTy.WellScoped]
      exact ⟨PolyCap.close_wellScoped boundCap capability,
        PolyTy.close_wellScoped boundTy boundCap target⟩
  | slot capability target =>
      simp only [PolyTy.close, PolyTy.WellScoped]
      exact ⟨PolyCap.close_wellScoped boundCap capability,
        PolyTy.close_wellScoped boundTy boundCap target⟩

theorem PolyTy.closeList_wellScoped
    (boundTy : List TyVar) (boundCap : List CapVar) (items : List Ty) :
    ∀ item ∈ PolyTy.closeList boundTy boundCap items,
      item.WellScoped boundTy.length boundCap.length := by
  cases items with
  | nil => simp [PolyTy.closeList]
  | cons item items =>
      intro candidate membership
      simp only [PolyTy.closeList, List.mem_cons] at membership
      rcases membership with equality | membership
      · subst candidate
        exact PolyTy.close_wellScoped boundTy boundCap item
      · exact PolyTy.closeList_wellScoped boundTy boundCap items
          candidate membership

end


mutual

def PolyCap.freeCapVars : PolyCap → List CapVar
  | .any => []
  | .free index => [index]
  | .bound _ => []
  | .prod items => PolyCap.freeCapVarsList items

def PolyCap.freeCapVarsList : List PolyCap → List CapVar
  | [] => []
  | item :: items => item.freeCapVars ++ PolyCap.freeCapVarsList items

end


mutual

def PolyTy.freeTyVars : PolyTy → List TyVar
  | .free index => [index]
  | .bound _ => []
  | .int => []
  | .fn domain codomain => domain.freeTyVars ++ codomain.freeTyVars
  | .prod items => PolyTy.freeTyVarsList items
  | .matcher _ target => target.freeTyVars
  | .slot _ target => target.freeTyVars

def PolyTy.freeTyVarsList : List PolyTy → List TyVar
  | [] => []
  | item :: items => item.freeTyVars ++ PolyTy.freeTyVarsList items

end


mutual

def PolyTy.freeCapVars : PolyTy → List CapVar
  | .free _ => []
  | .bound _ => []
  | .int => []
  | .fn domain codomain => domain.freeCapVars ++ codomain.freeCapVars
  | .prod items => PolyTy.freeCapVarsList items
  | .matcher capability target =>
      capability.freeCapVars ++ target.freeCapVars
  | .slot capability target =>
      capability.freeCapVars ++ target.freeCapVars

def PolyTy.freeCapVarsList : List PolyTy → List CapVar
  | [] => []
  | item :: items => item.freeCapVars ++ PolyTy.freeCapVarsList items

end


mutual

theorem PolyCap.mem_freeCapVars_close
    (boundCap : List CapVar) (capability : Cap) (index : CapVar) :
    index ∈ (PolyCap.close boundCap capability).freeCapVars ↔
      index ∈ capability.capVars ∧ index ∉ boundCap := by
  cases capability with
  | any => simp [PolyCap.close, PolyCap.freeCapVars, Cap.capVars]
  | var name =>
      simp only [PolyCap.close]
      split <;> rename_i membership
      · have inBound := List.contains_iff_mem.mp membership
        simp [PolyCap.freeCapVars, Cap.capVars]
        intro equality
        subst index
        exact inBound
      · have notInBound : name ∉ boundCap := by
          intro inBound
          exact membership (List.contains_iff_mem.mpr inBound)
        simp [PolyCap.freeCapVars, Cap.capVars]
        intro equality inBound
        subst index
        exact notInBound inBound
  | prod items =>
      simp only [PolyCap.close, PolyCap.freeCapVars, Cap.capVars]
      exact PolyCap.mem_freeCapVars_closeList boundCap items index

theorem PolyCap.mem_freeCapVars_closeList
    (boundCap : List CapVar) (items : List Cap) (index : CapVar) :
    index ∈ PolyCap.freeCapVarsList (PolyCap.closeList boundCap items) ↔
      index ∈ Cap.capVarsList items ∧ index ∉ boundCap := by
  cases items with
  | nil =>
      simp only [PolyCap.closeList, PolyCap.freeCapVarsList,
        Cap.capVarsList, List.not_mem_nil, false_and]
  | cons item items =>
      simp only [PolyCap.closeList, PolyCap.freeCapVarsList,
        Cap.capVarsList, List.mem_append]
      rw [PolyCap.mem_freeCapVars_close,
        PolyCap.mem_freeCapVars_closeList]
      constructor
      · intro hypothesis
        rcases hypothesis with hypothesis | hypothesis
        · exact ⟨Or.inl hypothesis.1, hypothesis.2⟩
        · exact ⟨Or.inr hypothesis.1, hypothesis.2⟩
      · intro hypothesis
        rcases hypothesis.1 with member | member
        · exact Or.inl ⟨member, hypothesis.2⟩
        · exact Or.inr ⟨member, hypothesis.2⟩

end


mutual

theorem PolyTy.mem_freeTyVars_close
    (boundTy : List TyVar) (boundCap : List CapVar)
    (target : Ty) (index : TyVar) :
    index ∈ (PolyTy.close boundTy boundCap target).freeTyVars ↔
      index ∈ target.tyVars ∧ index ∉ boundTy := by
  cases target with
  | var name =>
      simp only [PolyTy.close]
      split <;> rename_i membership
      · have inBound := List.contains_iff_mem.mp membership
        simp [PolyTy.freeTyVars, Ty.tyVars]
        intro equality
        subst index
        exact inBound
      · have notInBound : name ∉ boundTy := by
          intro inBound
          exact membership (List.contains_iff_mem.mpr inBound)
        simp [PolyTy.freeTyVars, Ty.tyVars]
        intro equality inBound
        subst index
        exact notInBound inBound
  | int => simp [PolyTy.close, PolyTy.freeTyVars, Ty.tyVars]
  | fn domain codomain =>
      simp only [PolyTy.close, PolyTy.freeTyVars, Ty.tyVars, List.mem_append]
      rw [PolyTy.mem_freeTyVars_close, PolyTy.mem_freeTyVars_close]
      exact or_and_common_right _ _ _
  | prod items =>
      simp only [PolyTy.close, PolyTy.freeTyVars, Ty.tyVars]
      exact PolyTy.mem_freeTyVars_closeList boundTy boundCap items index
  | matcher capability target =>
      simp only [PolyTy.close, PolyTy.freeTyVars, Ty.tyVars]
      exact PolyTy.mem_freeTyVars_close boundTy boundCap target index
  | slot capability target =>
      simp only [PolyTy.close, PolyTy.freeTyVars, Ty.tyVars]
      exact PolyTy.mem_freeTyVars_close boundTy boundCap target index

theorem PolyTy.mem_freeTyVars_closeList
    (boundTy : List TyVar) (boundCap : List CapVar)
    (items : List Ty) (index : TyVar) :
    index ∈ PolyTy.freeTyVarsList
      (PolyTy.closeList boundTy boundCap items) ↔
      index ∈ Ty.tyVarsList items ∧ index ∉ boundTy := by
  cases items with
  | nil =>
      simp only [PolyTy.closeList, PolyTy.freeTyVarsList,
        Ty.tyVarsList, List.not_mem_nil, false_and]
  | cons item items =>
      simp only [PolyTy.closeList, PolyTy.freeTyVarsList,
        Ty.tyVarsList, List.mem_append]
      rw [PolyTy.mem_freeTyVars_close,
        PolyTy.mem_freeTyVars_closeList]
      exact or_and_common_right _ _ _

end


mutual

theorem PolyTy.mem_freeCapVars_close
    (boundTy : List TyVar) (boundCap : List CapVar)
    (target : Ty) (index : CapVar) :
    index ∈ (PolyTy.close boundTy boundCap target).freeCapVars ↔
      index ∈ target.capVars ∧ index ∉ boundCap := by
  cases target with
  | var =>
      simp only [PolyTy.close]
      split <;> simp [PolyTy.freeCapVars, Ty.capVars]
  | int => simp [PolyTy.close, PolyTy.freeCapVars, Ty.capVars]
  | fn domain codomain =>
      simp only [PolyTy.close, PolyTy.freeCapVars, Ty.capVars, List.mem_append]
      rw [PolyTy.mem_freeCapVars_close, PolyTy.mem_freeCapVars_close]
      exact or_and_common_right _ _ _
  | prod items =>
      simp only [PolyTy.close, PolyTy.freeCapVars, Ty.capVars]
      exact PolyTy.mem_freeCapVars_closeList boundTy boundCap items index
  | matcher capability target =>
      simp only [PolyTy.close, PolyTy.freeCapVars, Ty.capVars, List.mem_append]
      rw [PolyCap.mem_freeCapVars_close, PolyTy.mem_freeCapVars_close]
      exact or_and_common_right _ _ _
  | slot capability target =>
      simp only [PolyTy.close, PolyTy.freeCapVars, Ty.capVars, List.mem_append]
      rw [PolyCap.mem_freeCapVars_close, PolyTy.mem_freeCapVars_close]
      exact or_and_common_right _ _ _

theorem PolyTy.mem_freeCapVars_closeList
    (boundTy : List TyVar) (boundCap : List CapVar)
    (items : List Ty) (index : CapVar) :
    index ∈ PolyTy.freeCapVarsList
      (PolyTy.closeList boundTy boundCap items) ↔
      index ∈ Ty.capVarsList items ∧ index ∉ boundCap := by
  cases items with
  | nil =>
      simp only [PolyTy.closeList, PolyTy.freeCapVarsList,
        Ty.capVarsList, List.not_mem_nil, false_and]
  | cons item items =>
      simp only [PolyTy.closeList, PolyTy.freeCapVarsList,
        Ty.capVarsList, List.mem_append]
      rw [PolyTy.mem_freeCapVars_close,
        PolyTy.mem_freeCapVars_closeList]
      exact or_and_common_right _ _ _

end


/-- A scheme records its arities and a position-bound body.  Bound positions
remove dependence on binder names; unused positions are still permitted. -/
structure Scheme where
  tyArity : Nat
  capArity : Nat
  body : PolyTy
  wellScoped : body.WellScoped tyArity capArity
deriving Repr

/-- Independent supplies for ordinary and capability variables. -/
structure Supply where
  ty : Nat
  cap : Nat
deriving Repr, DecidableEq

namespace Scheme

theorem eq_of_body_eq
    {tyArity capArity : Nat} {left right : PolyTy}
    {leftScoped : left.WellScoped tyArity capArity}
    {rightScoped : right.WellScoped tyArity capArity}
    (bodyEquality : left = right) :
    Scheme.mk tyArity capArity left leftScoped =
      Scheme.mk tyArity capArity right rightScoped := by
  subst right
  rfl

def WellFormed (scheme : Scheme) : Prop :=
  scheme.body.WellScoped scheme.tyArity scheme.capArity

theorem wellFormed (scheme : Scheme) : scheme.WellFormed :=
  scheme.wellScoped

def mono (body : Ty) : Scheme :=
  ⟨0, 0, PolyTy.ofTy body, PolyTy.ofTy_wellScoped 0 0 body⟩

def freeTyVars (scheme : Scheme) : List TyVar :=
  dedupFirst scheme.body.freeTyVars

def freeCapVars (scheme : Scheme) : List CapVar :=
  dedupFirst scheme.body.freeCapVars

theorem mem_freeTyVars {scheme : Scheme} {index : TyVar} :
    index ∈ scheme.freeTyVars ↔ index ∈ scheme.body.freeTyVars := by
  exact mem_dedupFirst

theorem mem_freeCapVars {scheme : Scheme} {index : CapVar} :
    index ∈ scheme.freeCapVars ↔ index ∈ scheme.body.freeCapVars := by
  exact mem_dedupFirst

def applyFree (substitution : Subst) (scheme : Scheme) : Scheme :=
  ⟨scheme.tyArity, scheme.capArity, scheme.body.applyFree substitution,
    PolyTy.applyFree_wellScoped substitution scheme.tyArity scheme.capArity
      scheme.wellScoped⟩

/-- Fresh ordinary variable assigned to one bound position. -/
def boundTyInstance (supply : Supply) (position : Nat) : TyVar :=
  ⟨supply.ty + position⟩

/-- Fresh capability variable assigned to one bound position. -/
def boundCapInstance (supply : Supply) (position : Nat) : CapVar :=
  ⟨supply.cap + position⟩

def instantiate (scheme : Scheme) (supply : Supply) : Ty × Supply :=
  (scheme.body.openBound
      (fun position => .var (boundTyInstance supply position))
      (fun position => .var (boundCapInstance supply position)),
    ⟨supply.ty + scheme.tyArity, supply.cap + scheme.capArity⟩)

/-- Declarative instantiation chooses one monotype/capability for each bound
position. -/
def Instantiates (scheme : Scheme) (target : Ty) : Prop :=
  ∃ boundTy : Nat → Ty, ∃ boundCap : Nat → Cap,
    target = scheme.body.openBound boundTy boundCap

@[simp] theorem mono_wellFormed (body : Ty) : (mono body).WellFormed := by
  exact (mono body).wellScoped

@[simp] theorem applyFree_id (scheme : Scheme) :
    scheme.applyFree Subst.id = scheme := by
  cases scheme
  simp [applyFree]

theorem applyFree_wellFormed
    (substitution : Subst) (scheme : Scheme) :
    (scheme.applyFree substitution).WellFormed := by
  exact (scheme.applyFree substitution).wellScoped

@[simp] theorem instantiate_next_ty (scheme : Scheme) (supply : Supply) :
    (scheme.instantiate supply).2.ty = supply.ty + scheme.tyArity := rfl

@[simp] theorem instantiate_next_cap (scheme : Scheme) (supply : Supply) :
    (scheme.instantiate supply).2.cap = supply.cap + scheme.capArity := rfl

@[simp] theorem instantiate_mono (body : Ty) (supply : Supply) :
    (mono body).instantiate supply = (body, supply) := by
  simp [instantiate, mono]

theorem instantiate_sound (scheme : Scheme) (supply : Supply) :
    scheme.Instantiates (scheme.instantiate supply).1 := by
  exact ⟨fun position => .var (boundTyInstance supply position),
    fun position => .var (boundCapInstance supply position), rfl⟩

@[simp] theorem boundTyInstance_index (supply : Supply) (position : Nat) :
    (boundTyInstance supply position).index = supply.ty + position := rfl

@[simp] theorem boundCapInstance_index (supply : Supply) (position : Nat) :
    (boundCapInstance supply position).index = supply.cap + position := rfl

theorem boundTyInstance_ge_start
    (supply : Supply) (position : Nat) :
    supply.ty ≤ (boundTyInstance supply position).index := by
  simp [boundTyInstance]

theorem boundCapInstance_ge_start
    (supply : Supply) (position : Nat) :
    supply.cap ≤ (boundCapInstance supply position).index := by
  simp [boundCapInstance]

theorem boundTyInstance_lt_end
    (scheme : Scheme) (supply : Supply) {position : Nat}
    (valid : position < scheme.tyArity) :
    (boundTyInstance supply position).index <
      (scheme.instantiate supply).2.ty := by
  simp only [boundTyInstance_index, instantiate_next_ty]
  omega

theorem boundCapInstance_lt_end
    (scheme : Scheme) (supply : Supply) {position : Nat}
    (valid : position < scheme.capArity) :
    (boundCapInstance supply position).index <
      (scheme.instantiate supply).2.cap := by
  simp only [boundCapInstance_index, instantiate_next_cap]
  omega

theorem freeTyVars_nodup (scheme : Scheme) : scheme.freeTyVars.Nodup :=
  dedupFirst_nodup _

theorem freeCapVars_nodup (scheme : Scheme) : scheme.freeCapVars.Nodup :=
  dedupFirst_nodup _

end Scheme

/-! ## Source contexts and generalization -/

abbrev Context := List Scheme

namespace Context

def freeTyVars (context : Context) : List TyVar :=
  dedupFirst (context.flatMap Scheme.freeTyVars)

def freeCapVars (context : Context) : List CapVar :=
  dedupFirst (context.flatMap Scheme.freeCapVars)

def generalizedTyVars (context : Context) (target : Ty) : List TyVar :=
  dedupFirst (target.tyVars.filter fun index => !context.freeTyVars.contains index)

def generalizedCapVars (context : Context) (target : Ty) : List CapVar :=
  dedupFirst (target.capVars.filter fun index => !context.freeCapVars.contains index)

def generalize (context : Context) (target : Ty) : Scheme :=
  let boundTy := context.generalizedTyVars target
  let boundCap := context.generalizedCapVars target
  ⟨boundTy.length, boundCap.length,
    PolyTy.close boundTy boundCap target,
    PolyTy.close_wellScoped boundTy boundCap target⟩

def applyFree (substitution : Subst) (context : Context) : Context :=
  context.map (Scheme.applyFree substitution)

def initialSupply (context : Context) : Supply :=
  ⟨TyVar.next (context.flatMap Scheme.freeTyVars),
    CapVar.next (context.flatMap Scheme.freeCapVars)⟩

theorem freeTy_index_lt_initialSupply
    {context : Context} {index : TyVar}
    (member : index ∈ context.freeTyVars) :
    index.index < context.initialSupply.ty := by
  apply TyVar.index_lt_next
  exact mem_dedupFirst.mp member

theorem freeCap_index_lt_initialSupply
    {context : Context} {index : CapVar}
    (member : index ∈ context.freeCapVars) :
    index.index < context.initialSupply.cap := by
  apply CapVar.index_lt_next
  exact mem_dedupFirst.mp member

theorem generalize_wellFormed (context : Context) (target : Ty) :
    (context.generalize target).WellFormed := by
  exact (context.generalize target).wellScoped

@[simp] theorem generalize_tyArity (context : Context) (target : Ty) :
    (context.generalize target).tyArity =
      (context.generalizedTyVars target).length := rfl

@[simp] theorem generalize_capArity (context : Context) (target : Ty) :
    (context.generalize target).capArity =
      (context.generalizedCapVars target).length := rfl

/-- Opening a generalized body with the same first-occurrence name lists
recovers the original monotype by literal equality. -/
theorem generalize_open (context : Context) (target : Ty) :
    (context.generalize target).body.openBound
      (tyNameAt (context.generalizedTyVars target))
      (capNameAt (context.generalizedCapVars target)) = target := by
  exact PolyTy.open_close
    (context.generalizedTyVars target)
    (context.generalizedCapVars target) target

theorem mem_generalizedTyVars
    {context : Context} {target : Ty} {index : TyVar} :
    index ∈ context.generalizedTyVars target ↔
      index ∈ target.tyVars ∧ index ∉ context.freeTyVars := by
  simp [generalizedTyVars, mem_dedupFirst]

theorem mem_generalizedCapVars
    {context : Context} {target : Ty} {index : CapVar} :
    index ∈ context.generalizedCapVars target ↔
      index ∈ target.capVars ∧ index ∉ context.freeCapVars := by
  simp [generalizedCapVars, mem_dedupFirst]

theorem mem_generalize_freeTyVars
    {context : Context} {target : Ty} {index : TyVar} :
    index ∈ (context.generalize target).freeTyVars ↔
      index ∈ target.tyVars ∧ index ∈ context.freeTyVars := by
  rw [Scheme.mem_freeTyVars]
  change index ∈ (PolyTy.close
      (context.generalizedTyVars target)
      (context.generalizedCapVars target) target).freeTyVars ↔ _
  rw [PolyTy.mem_freeTyVars_close, mem_generalizedTyVars]
  constructor
  · intro hypothesis
    refine ⟨hypothesis.1, ?_⟩
    by_cases inContext : index ∈ context.freeTyVars
    · exact inContext
    · exact False.elim (hypothesis.2 ⟨hypothesis.1, inContext⟩)
  · intro hypothesis
    exact ⟨hypothesis.1, fun generalized => generalized.2 hypothesis.2⟩

theorem mem_generalize_freeCapVars
    {context : Context} {target : Ty} {index : CapVar} :
    index ∈ (context.generalize target).freeCapVars ↔
      index ∈ target.capVars ∧ index ∈ context.freeCapVars := by
  rw [Scheme.mem_freeCapVars]
  change index ∈ (PolyTy.close
      (context.generalizedTyVars target)
      (context.generalizedCapVars target) target).freeCapVars ↔ _
  rw [PolyTy.mem_freeCapVars_close, mem_generalizedCapVars]
  constructor
  · intro hypothesis
    refine ⟨hypothesis.1, ?_⟩
    by_cases inContext : index ∈ context.freeCapVars
    · exact inContext
    · exact False.elim (hypothesis.2 ⟨hypothesis.1, inContext⟩)
  · intro hypothesis
    exact ⟨hypothesis.1, fun generalized => generalized.2 hypothesis.2⟩

theorem freeTyVars_nodup (context : Context) : context.freeTyVars.Nodup :=
  dedupFirst_nodup _

theorem freeCapVars_nodup (context : Context) : context.freeCapVars.Nodup :=
  dedupFirst_nodup _

theorem index_lt_initialSupply_ty
    {context : Context} {scheme : Scheme} {index : TyVar}
    (schemeMember : scheme ∈ context)
    (indexMember : index ∈ scheme.freeTyVars) :
    index.index < context.initialSupply.ty := by
  apply freeTy_index_lt_initialSupply
  apply mem_dedupFirst.mpr
  rw [List.mem_flatMap]
  exact ⟨scheme, schemeMember, indexMember⟩

theorem index_lt_initialSupply_cap
    {context : Context} {scheme : Scheme} {index : CapVar}
    (schemeMember : scheme ∈ context)
    (indexMember : index ∈ scheme.freeCapVars) :
    index.index < context.initialSupply.cap := by
  apply freeCap_index_lt_initialSupply
  apply mem_dedupFirst.mpr
  rw [List.mem_flatMap]
  exact ⟨scheme, schemeMember, indexMember⟩

/-- Every fresh ordinary bound instance is disjoint from the context's free
variables when instantiation starts at or above the context supply. -/
theorem instantiate_boundTy_not_contextFree
    (context : Context) (scheme : Scheme) (supply : Supply)
    (supplyAbove : context.initialSupply.ty ≤ supply.ty)
    {position : Nat} (valid : position < scheme.tyArity) :
    Scheme.boundTyInstance supply position ∉ context.freeTyVars := by
  intro member
  have below := context.freeTy_index_lt_initialSupply member
  have above := Scheme.boundTyInstance_ge_start supply position
  have within := Scheme.boundTyInstance_lt_end scheme supply valid
  omega

/-- Capability bound instances obey the analogous disjointness property. -/
theorem instantiate_boundCap_not_contextFree
    (context : Context) (scheme : Scheme) (supply : Supply)
    (supplyAbove : context.initialSupply.cap ≤ supply.cap)
    {position : Nat} (valid : position < scheme.capArity) :
    Scheme.boundCapInstance supply position ∉ context.freeCapVars := by
  intro member
  have below := context.freeCap_index_lt_initialSupply member
  have above := Scheme.boundCapInstance_ge_start supply position
  have within := Scheme.boundCapInstance_lt_end scheme supply valid
  omega

theorem instantiate_boundTy_not_contextFree_initial
    (context : Context) (scheme : Scheme)
    {position : Nat} (valid : position < scheme.tyArity) :
    Scheme.boundTyInstance context.initialSupply position ∉
      context.freeTyVars :=
  context.instantiate_boundTy_not_contextFree scheme context.initialSupply
    (Nat.le_refl _) valid

theorem instantiate_boundCap_not_contextFree_initial
    (context : Context) (scheme : Scheme)
    {position : Nat} (valid : position < scheme.capArity) :
    Scheme.boundCapInstance context.initialSupply position ∉
      context.freeCapVars :=
  context.instantiate_boundCap_not_contextFree scheme context.initialSupply
    (Nat.le_refl _) valid

end Context

end Source
end TypePM
