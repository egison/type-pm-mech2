import TypePM.GenerationRelation
import TypePM.Unification

/-!
# Fresh-name and sibling-permutation infrastructure

Generating sibling expressions from left to right makes their concrete fresh
type-variable names depend on source order.  The semantic comparison therefore
needs two independent operations: a bijective renaming of ordinary type
variables, and a permutation of the collected sibling results.

This module supplies that algebra without changing the generator.  In
particular, `GeneratedItems.SiblingAlphaEq` is the comparison relation needed
by a future transport theorem for `GeneratesItems`.  Capability variables are
left fixed because M1 generation allocates only ordinary type variables.
-/

namespace TypePM

private theorem congrArgTwo
    {α β γ : Type} (function : α → β → γ)
    {left₁ left₂ : α} {right₁ right₂ : β}
    (left : left₁ = left₂) (right : right₁ = right₂) :
    function left₁ right₁ = function left₂ right₂ := by
  subst left₂
  subst right₂
  rfl

private theorem map_eq_self_of_fixed
    {α : Type} (function : α → α)
    (fixed : ∀ item, function item = item) (items : List α) :
    items.map function = items := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      exact congrArgTwo List.cons (fixed item) induction

private theorem symm_map_perm
    {α : Type} {left right : List α} (forward backward : α → α)
    (inverse : ∀ item, backward (forward item) = item)
    (permutation : (left.map forward).Perm right) :
    (right.map backward).Perm left := by
  have mapped := permutation.map backward
  simpa [List.map_map, Function.comp_def, inverse] using mapped.symm

mutual

/-- Number of ordinary fresh variables allocated by successful M1 generation.
It depends only on syntax, not on sibling order or generated constraints. -/
def Expr.freshCount : Expr → Nat
  | .var _ => 0
  | .lit _ => 0
  | .something => 1
  | .lam body => 1 + body.freshCount
  | .app function argument =>
      function.freshCount + argument.freshCount + 2
  | .tuple items => Expr.freshCountList items

/-- Total allocation width of an expression list. -/
def Expr.freshCountList : List Expr → Nat
  | [] => 0
  | item :: items => item.freshCount + Expr.freshCountList items

end

mutual

/-- The endpoint of a relational generation is its starting supply plus the
syntax-determined allocation width. -/
theorem Generates.next_eq_start_add_freshCount
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (derivation : Generates context expression supply generated next) :
    next = supply + expression.freshCount := by
  cases derivation with
  | var lookup => simp [Expr.freshCount]
  | lit => simp [Expr.freshCount]
  | something => simp [Expr.freshCount]
  | lam body =>
      have bodyCount := Generates.next_eq_start_add_freshCount body
      simp [Expr.freshCount]
      omega
  | app function argument =>
      have functionCount :=
        Generates.next_eq_start_add_freshCount function
      have argumentCount :=
        Generates.next_eq_start_add_freshCount argument
      simp [Expr.freshCount]
      omega
  | tuple items =>
      exact GeneratesItems.next_eq_start_add_freshCount items

/-- List counterpart of `Generates.next_eq_start_add_freshCount`. -/
theorem GeneratesItems.next_eq_start_add_freshCount
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems}
    (derivation : GeneratesItems context expressions supply generated next) :
    next = supply + Expr.freshCountList expressions := by
  cases derivation with
  | nil => simp [Expr.freshCountList]
  | cons item items =>
      have itemCount := Generates.next_eq_start_add_freshCount item
      have itemsCount := GeneratesItems.next_eq_start_add_freshCount items
      simp [Expr.freshCountList]
      omega

end

/-- A bijective change of the ordinary variables allocated by M1 generation.
The two inverse laws are exactly what transport in both directions needs. -/
structure TyRenaming where
  forward : TyVar → TyVar
  backward : TyVar → TyVar
  backward_forward : ∀ index, backward (forward index) = index
  forward_backward : ∀ index, forward (backward index) = index

namespace TyRenaming

instance : CoeFun TyRenaming (fun _ => TyVar → TyVar) :=
  ⟨TyRenaming.forward⟩

def refl : TyRenaming :=
  { forward := id
    backward := id
    backward_forward := fun _ => rfl
    forward_backward := fun _ => rfl }

def symm (rho : TyRenaming) : TyRenaming :=
  { forward := rho.backward
    backward := rho.forward
    backward_forward := rho.forward_backward
    forward_backward := rho.backward_forward }

/-- `trans first second` applies `first` and then `second`. -/
def trans (first second : TyRenaming) : TyRenaming :=
  { forward := fun index => second (first index)
    backward := fun index => first.backward (second.backward index)
    backward_forward := fun index => by
      simp only [first.backward_forward, second.backward_forward]
    forward_backward := fun index => by
      simp only [first.forward_backward, second.forward_backward] }

@[simp] theorem symm_apply_apply (rho : TyRenaming) (index : TyVar) :
    rho.symm (rho index) = index :=
  rho.backward_forward index

@[simp] theorem apply_symm_apply (rho : TyRenaming) (index : TyVar) :
    rho (rho.symm index) = index :=
  rho.forward_backward index

/-- Only finitely many variable names are changed.  The witnessing list need
not be duplicate-free; finiteness, rather than a canonical support, is what
the source-order theorem requires. -/
def FiniteSupport (rho : TyRenaming) : Prop :=
  ∃ support : List TyVar,
    ∀ index, index ∉ support → rho index = index

theorem finiteSupport_refl : FiniteSupport refl := by
  exact ⟨[], by simp [TyRenaming.refl]⟩

theorem finiteSupport_symm {rho : TyRenaming}
    (finite : FiniteSupport rho) : FiniteSupport rho.symm := by
  rcases finite with ⟨support, fixed⟩
  refine ⟨support, ?_⟩
  intro index outside
  have forwardFixed := fixed index outside
  have backwardEquality := congrArg rho.backward forwardFixed
  exact (rho.backward_forward index ▸ backwardEquality).symm

theorem finiteSupport_trans {first second : TyRenaming}
    (firstFinite : FiniteSupport first)
    (secondFinite : FiniteSupport second) :
    FiniteSupport (first.trans second) := by
  rcases firstFinite with ⟨firstSupport, firstFixed⟩
  rcases secondFinite with ⟨secondSupport, secondFixed⟩
  refine ⟨firstSupport ++ secondSupport, ?_⟩
  intro index outside
  have outsideBoth : index ∉ firstSupport ∧ index ∉ secondSupport := by
    simpa using outside
  simp [TyRenaming.trans,
    firstFixed index outsideBoth.1,
    secondFixed index outsideBoth.2]

/-- Exchange two adjacent half-open blocks of natural-numbered fresh names.
The first block has width `leftWidth` and the second has width `rightWidth`;
indices outside their union are fixed. -/
def swapAdjacentIndex
    (start leftWidth rightWidth index : Nat) : Nat :=
  if index < start then index
  else if index < start + leftWidth then index + rightWidth
  else if index < start + leftWidth + rightWidth then index - leftWidth
  else index

private theorem swapAdjacentIndex_inverse
    (start leftWidth rightWidth index : Nat) :
    swapAdjacentIndex start rightWidth leftWidth
        (swapAdjacentIndex start leftWidth rightWidth index) = index := by
  unfold swapAdjacentIndex
  split <;> rename_i beforeStart
  · simp
  · split <;> rename_i inLeft
    · have movedNotBefore : ¬index + rightWidth < start := by omega
      have movedInSecond :
          index + rightWidth < start + rightWidth + leftWidth := by omega
      simp [movedNotBefore, movedInSecond]
      omega
    · split <;> rename_i inSecond
      · have startLeIndex : start ≤ index := by omega
        have leftEndLeIndex : start + leftWidth ≤ index := by omega
        have subNotBefore : ¬index - leftWidth < start := by omega
        have subInFirst : index - leftWidth < start + rightWidth := by omega
        simp [subNotBefore, subInFirst]
        omega
      · have notBefore : ¬index < start := beforeStart
        have notFirst : ¬index < start + rightWidth := by omega
        have notUnion : ¬index < start + rightWidth + leftWidth := by omega
        simp [notFirst, notUnion]

/-- The finite fresh-name permutation that exchanges two adjacent allocation
blocks.  Its inverse exchanges the resulting blocks in the opposite width
order. -/
def swapAdjacentBlocks
    (start leftWidth rightWidth : Nat) : TyRenaming :=
  { forward := fun index =>
      ⟨swapAdjacentIndex start leftWidth rightWidth index.index⟩
    backward := fun index =>
      ⟨swapAdjacentIndex start rightWidth leftWidth index.index⟩
    backward_forward := fun index => by
      cases index
      simp only [TyVar.mk.injEq]
      exact swapAdjacentIndex_inverse start leftWidth rightWidth _
    forward_backward := fun index => by
      cases index
      simp only [TyVar.mk.injEq]
      exact swapAdjacentIndex_inverse start rightWidth leftWidth _ }

theorem finiteSupport_swapAdjacentBlocks
    (start leftWidth rightWidth : Nat) :
    FiniteSupport (swapAdjacentBlocks start leftWidth rightWidth) := by
  refine ⟨(List.range (start + leftWidth + rightWidth)).map TyVar.mk, ?_⟩
  intro index outside
  cases index with
  | mk rawIndex =>
      have rawOutside :
          rawIndex ∉ List.range (start + leftWidth + rightWidth) := by
        intro membership
        exact outside (List.mem_map.mpr ⟨rawIndex, membership, rfl⟩)
      have endpointLe :
          start + leftWidth + rightWidth ≤ rawIndex := by
        simpa [List.mem_range] using rawOutside
      have notBefore : ¬rawIndex < start := by omega
      have notLeft : ¬rawIndex < start + leftWidth := by omega
      have notUnion :
          ¬rawIndex < start + leftWidth + rightWidth := by omega
      simp [swapAdjacentBlocks, swapAdjacentIndex,
        notBefore, notLeft, notUnion]

theorem swapAdjacentBlocks_before
    {start leftWidth rightWidth : Nat} {index : TyVar}
    (before : index.index < start) :
    swapAdjacentBlocks start leftWidth rightWidth index = index := by
  cases index
  simp [swapAdjacentBlocks, swapAdjacentIndex, before]

theorem swapAdjacentBlocks_left
    {start leftWidth rightWidth : Nat} {index : TyVar}
    (lower : start ≤ index.index)
    (upper : index.index < start + leftWidth) :
    (swapAdjacentBlocks start leftWidth rightWidth index).index =
      index.index + rightWidth := by
  simp [swapAdjacentBlocks, swapAdjacentIndex, Nat.not_lt.mpr lower, upper]

theorem swapAdjacentBlocks_right
    {start leftWidth rightWidth : Nat} {index : TyVar}
    (lower : start + leftWidth ≤ index.index)
    (upper : index.index < start + leftWidth + rightWidth) :
    (swapAdjacentBlocks start leftWidth rightWidth index).index =
      index.index - leftWidth := by
  have notBefore : ¬index.index < start := by omega
  have notLeft : ¬index.index < start + leftWidth := by omega
  simp [swapAdjacentBlocks, swapAdjacentIndex, notBefore, notLeft, upper]

theorem swapAdjacentBlocks_after
    {start leftWidth rightWidth : Nat} {index : TyVar}
    (after : start + leftWidth + rightWidth ≤ index.index) :
    swapAdjacentBlocks start leftWidth rightWidth index = index := by
  cases index with
  | mk rawIndex =>
      change start + leftWidth + rightWidth ≤ rawIndex at after
      have notBefore : ¬rawIndex < start := by omega
      have notLeft : ¬rawIndex < start + leftWidth := by omega
      have notUnion :
          ¬rawIndex < start + leftWidth + rightWidth := by omega
      simp [swapAdjacentBlocks, swapAdjacentIndex,
        notBefore, notLeft, notUnion]

end TyRenaming

mutual

/-- Rename every ordinary type variable, leaving capability variables fixed. -/
def Ty.rename (rho : TyRenaming) : Ty → Ty
  | .var index => .var (rho index)
  | .int => .int
  | .fn domain codomain =>
      .fn (domain.rename rho) (codomain.rename rho)
  | .prod items => .prod (Ty.renameList rho items)
  | .matcher capability target =>
      .matcher capability (target.rename rho)
  | .slot capability target =>
      .slot capability (target.rename rho)

/-- List counterpart of `Ty.rename`. -/
def Ty.renameList (rho : TyRenaming) : List Ty → List Ty
  | [] => []
  | target :: targets =>
      target.rename rho :: Ty.renameList rho targets

end

namespace Ty

@[simp] theorem renameList_eq_map
    (rho : TyRenaming) (targets : List Ty) :
    renameList rho targets = targets.map (rename rho) := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp [renameList, induction]

mutual

@[simp] theorem rename_refl (target : Ty) :
    target.rename TyRenaming.refl = target := by
  cases target with
  | var index => rfl
  | int => rfl
  | fn domain codomain =>
      exact congrArgTwo Ty.fn (rename_refl domain) (rename_refl codomain)
  | prod items => exact congrArg Ty.prod (renameList_refl items)
  | matcher capability target =>
      exact congrArg (Ty.matcher capability) (rename_refl target)
  | slot capability target =>
      exact congrArg (Ty.slot capability) (rename_refl target)

@[simp] theorem renameList_refl (targets : List Ty) :
    Ty.renameList TyRenaming.refl targets = targets := by
  cases targets with
  | nil => rfl
  | cons target targets =>
      exact congrArgTwo List.cons (rename_refl target) (renameList_refl targets)

end

mutual

theorem rename_trans
    (first second : TyRenaming) (target : Ty) :
    (target.rename first).rename second =
      target.rename (first.trans second) := by
  cases target with
  | var index => rfl
  | int => rfl
  | fn domain codomain =>
      exact congrArgTwo Ty.fn
        (rename_trans first second domain)
        (rename_trans first second codomain)
  | prod items =>
      exact congrArg Ty.prod (renameList_trans first second items)
  | matcher capability target =>
      exact congrArg (Ty.matcher capability)
        (rename_trans first second target)
  | slot capability target =>
      exact congrArg (Ty.slot capability)
        (rename_trans first second target)

theorem renameList_trans
    (first second : TyRenaming) (targets : List Ty) :
    Ty.renameList second (Ty.renameList first targets) =
      Ty.renameList (first.trans second) targets := by
  cases targets with
  | nil => rfl
  | cons target targets =>
      exact congrArgTwo List.cons
        (rename_trans first second target)
        (renameList_trans first second targets)

end

mutual

@[simp] theorem rename_symm_apply (rho : TyRenaming) (target : Ty) :
    (target.rename rho).rename rho.symm = target := by
  cases target with
  | var index => simp [Ty.rename]
  | int => rfl
  | fn domain codomain =>
      exact congrArgTwo Ty.fn
        (rename_symm_apply rho domain)
        (rename_symm_apply rho codomain)
  | prod items =>
      exact congrArg Ty.prod (renameList_symm_apply rho items)
  | matcher capability target =>
      exact congrArg (Ty.matcher capability) (rename_symm_apply rho target)
  | slot capability target =>
      exact congrArg (Ty.slot capability) (rename_symm_apply rho target)

@[simp] theorem renameList_symm_apply
    (rho : TyRenaming) (targets : List Ty) :
    Ty.renameList rho.symm (Ty.renameList rho targets) = targets := by
  cases targets with
  | nil => rfl
  | cons target targets =>
      exact congrArgTwo List.cons
        (rename_symm_apply rho target)
        (renameList_symm_apply rho targets)

end


@[simp] theorem rename_apply_symm (rho : TyRenaming) (target : Ty) :
    (target.rename rho.symm).rename rho = target :=
  rename_symm_apply rho.symm target

end Ty

namespace Equation

/-- Rename the ordinary variables in a hard equation. -/
def rename (rho : TyRenaming) : Equation → Equation
  | .cap left right => .cap left right
  | .ty left right => .ty (left.rename rho) (right.rename rho)

@[simp] theorem rename_refl (equation : Equation) :
    equation.rename TyRenaming.refl = equation := by
  cases equation <;> simp [Equation.rename]

@[simp] theorem rename_symm_apply
    (rho : TyRenaming) (equation : Equation) :
    (equation.rename rho).rename rho.symm = equation := by
  cases equation <;> simp [Equation.rename]

theorem rename_trans (first second : TyRenaming) (equation : Equation) :
    (equation.rename first).rename second =
      equation.rename (first.trans second) := by
  cases equation <;> simp [Equation.rename, Ty.rename_trans]

end Equation

namespace CheckObligation

/-- Rename both sides of a delayed checking obligation. -/
def rename (rho : TyRenaming)
    (obligation : CheckObligation) : CheckObligation :=
  { source := obligation.source.rename rho
    expected := obligation.expected.rename rho }

@[simp] theorem rename_refl (obligation : CheckObligation) :
    obligation.rename TyRenaming.refl = obligation := by
  cases obligation
  simp [CheckObligation.rename]

@[simp] theorem rename_symm_apply
    (rho : TyRenaming) (obligation : CheckObligation) :
    (obligation.rename rho).rename rho.symm = obligation := by
  cases obligation
  simp [CheckObligation.rename]

theorem rename_trans (first second : TyRenaming)
    (obligation : CheckObligation) :
    (obligation.rename first).rename second =
      obligation.rename (first.trans second) := by
  cases obligation
  simp [CheckObligation.rename, Ty.rename_trans]

end CheckObligation

namespace Generated

/-- Apply one fresh-variable rho to a generated constraint problem. -/
def rename (rho : TyRenaming) (generated : Generated) : Generated :=
  { target := generated.target.rename rho
    hard := generated.hard.map (Equation.rename rho)
    pending := generated.pending.map (CheckObligation.rename rho) }

@[simp] theorem rename_refl (generated : Generated) :
    generated.rename TyRenaming.refl = generated := by
  cases generated with
  | mk target hard pending =>
      unfold Generated.rename
      rw [Ty.rename_refl,
        map_eq_self_of_fixed _ Equation.rename_refl hard,
        map_eq_self_of_fixed _ CheckObligation.rename_refl pending]

@[simp] theorem rename_symm_apply
    (rho : TyRenaming) (generated : Generated) :
    (generated.rename rho).rename rho.symm = generated := by
  cases generated
  simp [Generated.rename, List.map_map, Function.comp_def]

theorem rename_trans (first second : TyRenaming) (generated : Generated) :
    (generated.rename first).rename second =
      generated.rename (first.trans second) := by
  cases generated
  simp [Generated.rename, List.map_map, Function.comp_def,
    Ty.rename_trans, Equation.rename_trans, CheckObligation.rename_trans]

/-- Two generated problems agree up to a finite fresh-variable change and
worklist order.  Unlike the sibling relation below, their single result types
must correspond exactly. -/
def AlphaEq (left right : Generated) : Prop :=
  ∃ rho : TyRenaming,
    rho.FiniteSupport ∧
      (left.rename rho).target = right.target ∧
      (left.rename rho).hard.Perm right.hard ∧
      (left.rename rho).pending.Perm right.pending

namespace AlphaEq

theorem refl (generated : Generated) : AlphaEq generated generated := by
  exact ⟨TyRenaming.refl, TyRenaming.finiteSupport_refl,
    by simp, by simp, by simp⟩

theorem symm {left right : Generated} (equivalence : AlphaEq left right) :
    AlphaEq right left := by
  rcases equivalence with ⟨rho, finite, target, hard, pending⟩
  refine ⟨rho.symm, TyRenaming.finiteSupport_symm finite, ?_, ?_, ?_⟩
  · change right.target.rename rho.symm = left.target
    change left.target.rename rho = right.target at target
    have restored := congrArg (Ty.rename rho.symm) target
    simpa using restored.symm
  · change (right.hard.map (Equation.rename rho.symm)).Perm left.hard
    exact symm_map_perm
      (Equation.rename rho) (Equation.rename rho.symm)
      (Equation.rename_symm_apply rho)
      (by simpa [Generated.rename] using hard)
  · change
      (right.pending.map (CheckObligation.rename rho.symm)).Perm left.pending
    exact symm_map_perm
      (CheckObligation.rename rho) (CheckObligation.rename rho.symm)
      (CheckObligation.rename_symm_apply rho)
      (by simpa [Generated.rename] using pending)

theorem trans {left middle right : Generated}
    (first : AlphaEq left middle) (second : AlphaEq middle right) :
    AlphaEq left right := by
  rcases first with ⟨firstRho, firstFinite, firstTarget,
    firstHard, firstPending⟩
  rcases second with ⟨secondRho, secondFinite, secondTarget,
    secondHard, secondPending⟩
  refine ⟨firstRho.trans secondRho,
    TyRenaming.finiteSupport_trans firstFinite secondFinite, ?_, ?_, ?_⟩
  · change left.target.rename (firstRho.trans secondRho) = right.target
    change left.target.rename firstRho = middle.target at firstTarget
    change middle.target.rename secondRho = right.target at secondTarget
    rw [← Ty.rename_trans, firstTarget, secondTarget]
  · have mapped := firstHard.map (Equation.rename secondRho)
    exact (by
      simpa [Generated.rename, List.map_map, Function.comp_def,
        Equation.rename_trans] using mapped.trans secondHard)
  · have mapped := firstPending.map (CheckObligation.rename secondRho)
    exact (by
      simpa [Generated.rename, List.map_map, Function.comp_def,
        CheckObligation.rename_trans] using mapped.trans secondPending)

end AlphaEq

end Generated

namespace GeneratedItems

/-- Apply one fresh-variable renaming to all sibling results and constraints. -/
def rename (rho : TyRenaming)
    (generated : GeneratedItems) : GeneratedItems :=
  { targets := Ty.renameList rho generated.targets
    hard := generated.hard.map (Equation.rename rho)
    pending := generated.pending.map (CheckObligation.rename rho) }

@[simp] theorem rename_refl (generated : GeneratedItems) :
    generated.rename TyRenaming.refl = generated := by
  cases generated with
  | mk targets hard pending =>
      unfold GeneratedItems.rename
      rw [Ty.renameList_refl,
        map_eq_self_of_fixed _ Equation.rename_refl hard,
        map_eq_self_of_fixed _ CheckObligation.rename_refl pending]

@[simp] theorem rename_symm_apply
    (rho : TyRenaming) (generated : GeneratedItems) :
    (generated.rename rho).rename rho.symm = generated := by
  cases generated
  simp [GeneratedItems.rename, List.map_map, Function.comp_def]

/-- Collect independently named sibling results.  This is the same
concatenation performed by `GeneratesItems`, but exposes the per-sibling
boundaries needed to state a permutation lemma. -/
def collect : List Generated → GeneratedItems
  | [] => ⟨[], [], []⟩
  | generated :: generateds =>
      let rest := collect generateds
      ⟨generated.target :: rest.targets,
        generated.hard ++ rest.hard,
        generated.pending ++ rest.pending⟩

@[simp] theorem collect_targets (generateds : List Generated) :
    (collect generateds).targets = generateds.map Generated.target := by
  induction generateds with
  | nil => rfl
  | cons generated generateds induction =>
      simp [collect, induction]

@[simp] theorem collect_hard (generateds : List Generated) :
    (collect generateds).hard = generateds.flatMap Generated.hard := by
  induction generateds with
  | nil => rfl
  | cons generated generateds induction =>
      simp [collect, induction]

@[simp] theorem collect_pending (generateds : List Generated) :
    (collect generateds).pending = generateds.flatMap Generated.pending := by
  induction generateds with
  | nil => rfl
  | cons generated generateds induction =>
      simp [collect, induction]

/-- Reordering already generated sibling blocks permutes their targets, hard
equations, and pending obligations, without changing any member. -/
theorem collect_perm
    {left right : List Generated} (permutation : left.Perm right) :
    (collect left).targets.Perm (collect right).targets ∧
      (collect left).hard.Perm (collect right).hard ∧
      (collect left).pending.Perm (collect right).pending := by
  simp only [collect_targets, collect_hard, collect_pending]
  exact ⟨permutation.map Generated.target,
    permutation.flatMap_right Generated.hard,
    permutation.flatMap_right Generated.pending⟩

/-- The exact comparison relation required after changing sibling source
order: one bijective fresh-name change, followed by independent permutations
of result positions and of the two constraint worklists. -/
def SiblingAlphaEq (left right : GeneratedItems) : Prop :=
  ∃ rho : TyRenaming,
    rho.FiniteSupport ∧
      (left.rename rho).targets.Perm right.targets ∧
      (left.rename rho).hard.Perm right.hard ∧
      (left.rename rho).pending.Perm right.pending

/-- A permutation of independently generated sibling blocks is a finite
alpha-equivalence (with the identity fresh-name change). -/
theorem siblingAlphaEq_collect_of_perm
    {left right : List Generated} (permutation : left.Perm right) :
    SiblingAlphaEq (collect left) (collect right) := by
  obtain ⟨targets, hard, pending⟩ := collect_perm permutation
  exact ⟨TyRenaming.refl, TyRenaming.finiteSupport_refl,
    by simpa using targets, by simpa using hard, by simpa using pending⟩

namespace SiblingAlphaEq

theorem refl (generated : GeneratedItems) :
    SiblingAlphaEq generated generated := by
  exact ⟨TyRenaming.refl, TyRenaming.finiteSupport_refl,
    by simp, by simp, by simp⟩

/-- Sibling alpha-equivalence is symmetric because its fresh-name map is
bijective. -/
theorem symm {left right : GeneratedItems}
    (equivalence : SiblingAlphaEq left right) :
    SiblingAlphaEq right left := by
  rcases equivalence with ⟨rho, finite, targets, hard, pending⟩
  refine ⟨rho.symm, TyRenaming.finiteSupport_symm finite, ?_, ?_, ?_⟩
  · change (Ty.renameList rho.symm right.targets).Perm left.targets
    rw [Ty.renameList_eq_map]
    exact symm_map_perm
      (Ty.rename rho)
      (Ty.rename rho.symm)
      (Ty.rename_symm_apply rho)
      (by
        simpa [GeneratedItems.rename, Ty.renameList_eq_map] using
          targets)
  · change (right.hard.map (Equation.rename rho.symm)).Perm left.hard
    exact symm_map_perm
      (Equation.rename rho)
      (Equation.rename rho.symm)
      (Equation.rename_symm_apply rho)
      (by simpa [GeneratedItems.rename] using hard)
  · change
      (right.pending.map (CheckObligation.rename rho.symm)).Perm left.pending
    exact symm_map_perm
      (CheckObligation.rename rho)
      (CheckObligation.rename rho.symm)
      (CheckObligation.rename_symm_apply rho)
      (by simpa [GeneratedItems.rename] using pending)

end SiblingAlphaEq

end GeneratedItems

/-- Conjugate a solution by a fresh-variable renaming.  This is the solution
appropriate for the renamed equation problem. -/
def Subst.renameSolution (rho : TyRenaming)
    (substitution : Subst) : Subst :=
  { cap := substitution.cap
    ty := fun index =>
      (substitution.ty (rho.symm index)).rename rho }

mutual

/-- Renaming an input type and conjugating its solution commute. -/
theorem Ty.rename_apply_renameSolution
    (rho : TyRenaming) (substitution : Subst) (target : Ty) :
    (target.rename rho).apply
        (Subst.renameSolution rho substitution) =
      (target.apply substitution).rename rho := by
  cases target with
  | var index => simp [Ty.rename, Ty.apply, Subst.renameSolution]
  | int => rfl
  | fn domain codomain =>
      exact congrArgTwo Ty.fn
        (Ty.rename_apply_renameSolution rho substitution domain)
        (Ty.rename_apply_renameSolution rho substitution codomain)
  | prod items =>
      exact congrArg Ty.prod
        (Ty.renameList_apply_renameSolution rho substitution items)
  | matcher capability target =>
      exact congrArg (Ty.matcher (capability.apply substitution.cap))
        (Ty.rename_apply_renameSolution rho substitution target)
  | slot capability target =>
      exact congrArg (Ty.slot (capability.apply substitution.cap))
        (Ty.rename_apply_renameSolution rho substitution target)

/-- List counterpart of `Ty.rename_apply_renameSolution`. -/
theorem Ty.renameList_apply_renameSolution
    (rho : TyRenaming) (substitution : Subst) (targets : List Ty) :
    Ty.applyList (Subst.renameSolution rho substitution)
        (Ty.renameList rho targets) =
      Ty.renameList rho (Ty.applyList substitution targets) := by
  cases targets with
  | nil => rfl
  | cons target targets =>
      exact congrArgTwo List.cons
        (Ty.rename_apply_renameSolution rho substitution target)
        (Ty.renameList_apply_renameSolution rho substitution targets)

end

namespace Equation

/-- Equation satisfaction is equivariant under a bijective change of fresh
ordinary variable names. -/
theorem holds_rename
    (rho : TyRenaming) (substitution : Subst)
    (equation : Equation) :
    (equation.rename rho).Holds
        (Subst.renameSolution rho substitution) ↔
      equation.Holds substitution := by
  cases equation with
  | cap left right => rfl
  | ty left right =>
      simp only [Equation.rename, Equation.Holds,
        Ty.rename_apply_renameSolution]
      constructor
      · intro equality
        have restored := congrArg (Ty.rename rho.symm) equality
        simpa using restored
      · intro equality
        exact congrArg (Ty.rename rho) equality

end Equation

/-- A solution transports to the renamed and reordered hard worklist. -/
theorem solves_rename_perm
    (rho : TyRenaming) (substitution : Subst)
    {left right : List Equation}
    (permutation : (left.map (Equation.rename rho)).Perm right) :
    Solves substitution left ↔
      Solves (Subst.renameSolution rho substitution) right := by
  constructor
  · intro solved equation membership
    have renamedMembership :
        equation ∈ left.map (Equation.rename rho) :=
      permutation.mem_iff.mpr membership
    obtain ⟨original, originalMembership, equality⟩ :=
      List.mem_map.mp renamedMembership
    subst equation
    exact (Equation.holds_rename rho substitution original).mpr
      (solved original originalMembership)
  · intro solved equation membership
    have renamedMembership :
        Equation.rename rho equation ∈ right :=
      permutation.mem_iff.mp (List.mem_map.mpr ⟨equation, membership, rfl⟩)
    exact (Equation.holds_rename rho substitution equation).mp
      (solved _ renamedMembership)

end TypePM
