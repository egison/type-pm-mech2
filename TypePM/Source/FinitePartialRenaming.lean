import TypePM.GeneralizationTransport

/-!
# Extending finite partial bijections to global renamings

A bijection between two finite lists of names can be extended to a
permutation of the whole name type.  The construction processes pairs from
right to left.  At each step it swaps the current image of the new source
with its required target, preserving all pairs already installed.
-/

namespace TypePM.Source

namespace FinitePermutation

structure Permutation (α : Type) where
  forward : α → α
  backward : α → α
  backward_forward : ∀ item, backward (forward item) = item
  forward_backward : ∀ item, forward (backward item) = item

namespace Permutation

def refl : Permutation α :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def trans (first second : Permutation α) : Permutation α :=
  { forward := fun item => second.forward (first.forward item)
    backward := fun item => first.backward (second.backward item)
    backward_forward := fun item => by
      simp only [second.backward_forward, first.backward_forward]
    forward_backward := fun item => by
      simp only [second.forward_backward, first.forward_backward] }

def FiniteSupport [DecidableEq α] (rho : Permutation α) : Prop :=
  ∃ support : List α,
    ∀ item, item ∉ support → rho.forward item = item

theorem finiteSupport_refl [DecidableEq α] :
    FiniteSupport (refl : Permutation α) := by
  exact ⟨[], by simp [refl]⟩

theorem finiteSupport_trans [DecidableEq α]
    {first second : Permutation α}
    (firstFinite : first.FiniteSupport)
    (secondFinite : second.FiniteSupport) :
    (first.trans second).FiniteSupport := by
  obtain ⟨firstSupport, firstFixed⟩ := firstFinite
  obtain ⟨secondSupport, secondFixed⟩ := secondFinite
  refine ⟨firstSupport ++ secondSupport, ?_⟩
  intro item outside
  have outsideBoth : item ∉ firstSupport ∧ item ∉ secondSupport := by
    simpa using outside
  simp [trans, firstFixed item outsideBoth.1,
    secondFixed item outsideBoth.2]

end Permutation


section Swap

variable { α : Type } [DecidableEq α]

def swapIndex (left right item : α) : α :=
  if item = left then right else if item = right then left else item

theorem swapIndex_selfInverse (left right item : α) :
    swapIndex left right (swapIndex left right item) = item := by
  by_cases equal : left = right
  · subst right
    by_cases atLeft : item = left <;> simp [swapIndex, atLeft]
  · by_cases atLeft : item = left
    · subst item
      have reverse : right ≠ left := fun equality => equal equality.symm
      simp [swapIndex, reverse]
    · by_cases atRight : item = right
      · subst item
        have reverse : right ≠ left := fun equality => equal equality.symm
        simp [swapIndex, reverse]
      · simp [swapIndex, atLeft, atRight]

def swap (left right : α) : Permutation α :=
  { forward := swapIndex left right
    backward := swapIndex left right
    backward_forward := swapIndex_selfInverse left right
    forward_backward := swapIndex_selfInverse left right }

@[simp] theorem swap_left (left right : α) :
    (swap left right).forward left = right := by
  simp [swap, swapIndex]

theorem swap_fixed {left right item : α}
    (notLeft : item ≠ left) (notRight : item ≠ right) :
    (swap left right).forward item = item := by
  simp [swap, swapIndex, notLeft, notRight]

theorem finiteSupport_swap (left right : α) :
    (swap left right).FiniteSupport := by
  refine ⟨[left, right], ?_⟩
  intro item outside
  have notBoth : item ≠ left ∧ item ≠ right := by simpa using outside
  exact swap_fixed notBoth.1 notBoth.2

end Swap


section Extend

variable { α : Type } [DecidableEq α]

inductive Aligned (relation : α → β → Prop) :
    List α → List β → Prop where
  | nil : Aligned relation [] []
  | cons : relation source target →
      Aligned relation sources targets →
      Aligned relation (source :: sources) (target :: targets)

namespace Aligned

omit [DecidableEq α] in
theorem imp {left : α → β → Prop} {right : α → β → Prop}
    {sources : List α} {targets : List β}
    (pairs : Aligned left sources targets)
    (mapping : ∀ source target, left source target → right source target) :
    Aligned right sources targets := by
  induction pairs with
  | nil => exact .nil
  | cons head tail induction => exact .cons (mapping _ _ head) induction

end Aligned

/-- Install the aligned source/target pairs as a global permutation. -/
def extend : List α → List α → Permutation α
  | source :: sources, target :: targets =>
      let tail := extend sources targets
      tail.trans (swap (tail.forward source) target)
  | _, _ => .refl

theorem extend_finiteSupport (sources targets : List α) :
    (extend sources targets).FiniteSupport := by
  induction sources generalizing targets with
  | nil =>
      cases targets <;> exact Permutation.finiteSupport_refl
  | cons source sources induction =>
      cases targets with
      | nil => exact Permutation.finiteSupport_refl
      | cons target targets =>
          exact Permutation.finiteSupport_trans
            (induction targets)
            (finiteSupport_swap _ _)

omit [DecidableEq α] in
private theorem Permutation.forward_injective (rho : Permutation α) :
    Function.Injective rho.forward := by
  intro left right equality
  have restored := congrArg rho.backward equality
  simpa only [rho.backward_forward] using restored

private theorem extend_forall₂_with_mem
    {sources targets : List α}
    (sourceNodup : sources.Nodup) (targetNodup : targets.Nodup)
    (sameLength : sources.length = targets.length) :
    Aligned
      (fun source target =>
        (extend sources targets).forward source = target ∧
          source ∈ sources ∧ target ∈ targets)
      sources targets := by
  induction sources generalizing targets with
  | nil =>
      cases targets with
      | nil => exact .nil
      | cons => simp at sameLength
  | cons source sources induction =>
      cases targets with
      | nil => simp at sameLength
      | cons target targets =>
          have tailLength : sources.length = targets.length :=
            Nat.add_right_cancel sameLength
          have sourceFresh := (List.nodup_cons.mp sourceNodup).1
          have sourcesNodup := (List.nodup_cons.mp sourceNodup).2
          have targetFresh := (List.nodup_cons.mp targetNodup).1
          have targetsNodup := (List.nodup_cons.mp targetNodup).2
          have tailPairs := induction sourcesNodup targetsNodup tailLength
          apply Aligned.cons
          · exact ⟨by simp [extend, Permutation.trans], by simp⟩
          · exact tailPairs.imp (by
              intro oldSource oldTarget oldFacts
              change
                (swap ((extend sources targets).forward source) target).forward
                    ((extend sources targets).forward oldSource) = oldTarget ∧
                  oldSource ∈ source :: sources ∧
                    oldTarget ∈ target :: targets
              refine ⟨?_, List.mem_cons_of_mem _ oldFacts.2.1,
                List.mem_cons_of_mem _ oldFacts.2.2⟩
              rw [oldFacts.1]
              apply swap_fixed
              · intro equality
                have imageEquality :
                    (extend sources targets).forward oldSource =
                      (extend sources targets).forward source := by
                  simpa [oldFacts.1] using equality
                have sourceEquality :=
                  (extend sources targets).forward_injective imageEquality
                exact sourceFresh (sourceEquality ▸ oldFacts.2.1)
              · exact fun equality =>
                  targetFresh (equality ▸ oldFacts.2.2))

/-- With duplicate-free aligned lists, `extend` realizes every listed pair. -/
theorem extend_forall₂
    {sources targets : List α}
    (sourceNodup : sources.Nodup) (targetNodup : targets.Nodup)
    (sameLength : sources.length = targets.length) :
    Aligned
      (fun source target =>
        (extend sources targets).forward source = target)
      sources targets :=
  (extend_forall₂_with_mem sourceNodup targetNodup sameLength).imp
    (fun _ _ facts => facts.1)

omit [DecidableEq α] in
private theorem Aligned.map_right
    (function : α → β) (items : List α) :
    Aligned (fun left right => right = function left)
      items (items.map function) := by
  induction items with
  | nil => exact .nil
  | cons item items induction => exact .cons rfl induction

omit [DecidableEq α] in
private theorem Aligned.agree_on_left
    {relation : α → β → Prop} {function : α → β}
    {items : List α}
    (relations : Aligned relation items (items.map function)) :
    ∀ item, item ∈ items → relation item (function item) := by
  induction items with
  | nil => simp
  | cons head tail induction =>
      cases relations with
      | cons headRelation tailRelations =>
          intro item membership
          simp only [List.mem_cons] at membership
          rcases membership with equality | tailMember
          · subst item
            exact headRelation
          · exact induction tailRelations item tailMember

omit [DecidableEq α] in
/-- The extension agrees with a prescribed finite injective map on every
listed source name. -/
private theorem nodup_map_of_injectiveOn
    (sources : List α) (function : α → α)
    (sourceNodup : sources.Nodup)
    (injectiveOn : ∀ {left right}, left ∈ sources → right ∈ sources →
      function left = function right → left = right) :
    (sources.map function).Nodup := by
  induction sources with
  | nil => simp
  | cons source sources induction =>
      have fresh := (List.nodup_cons.mp sourceNodup).1
      have tailNodup := (List.nodup_cons.mp sourceNodup).2
      apply List.nodup_cons.mpr
      constructor
      · intro membership
        obtain ⟨other, otherMember, equality⟩ := List.mem_map.mp membership
        have sourceEquality := injectiveOn (by simp)
          (List.mem_cons_of_mem _ otherMember) equality.symm
        exact fresh (sourceEquality ▸ otherMember)
      · exact induction tailNodup (by
          intro left right leftMember rightMember equality
          exact injectiveOn
            (List.mem_cons_of_mem _ leftMember)
            (List.mem_cons_of_mem _ rightMember) equality)

theorem extend_map_agrees
    (sources : List α) (function : α → α)
    (sourceNodup : sources.Nodup)
    (injectiveOn : ∀ {left right}, left ∈ sources → right ∈ sources →
      function left = function right → left = right) :
    ∀ source, source ∈ sources →
      (extend sources (sources.map function)).forward source =
        function source := by
  have targetNodup : (sources.map function).Nodup :=
    nodup_map_of_injectiveOn sources function sourceNodup injectiveOn
  have pairs := extend_forall₂ sourceNodup targetNodup (by simp)
  exact pairs.agree_on_left

end Extend

end FinitePermutation


/-- A bijection between two finite supports.  The functions only need to be
inverse on the indicated supports. -/
structure FinitePartialBijection (α : Type) [DecidableEq α] where
  source : List α
  target : List α
  forward : α → α
  backward : α → α
  source_nodup : source.Nodup
  target_nodup : target.Nodup
  forward_mem : ∀ {item}, item ∈ source → forward item ∈ target
  backward_mem : ∀ {item}, item ∈ target → backward item ∈ source
  backward_forward : ∀ {item}, item ∈ source →
    backward (forward item) = item
  forward_backward : ∀ {item}, item ∈ target →
    forward (backward item) = item

namespace FinitePartialBijection

variable { α : Type } [DecidableEq α]

private theorem forward_injectiveOn (data : FinitePartialBijection α) :
    ∀ {left right}, left ∈ data.source → right ∈ data.source →
      data.forward left = data.forward right → left = right := by
  intro left right leftMember rightMember equality
  have restored := congrArg data.backward equality
  simpa only [data.backward_forward leftMember,
    data.backward_forward rightMember] using restored

/-- Extend the partial finite bijection to a finite-support permutation of
the whole name type. -/
def extend (data : FinitePartialBijection α) :
    FinitePermutation.Permutation α :=
  FinitePermutation.extend data.source
    (data.source.map data.forward)

theorem extend_forward_agrees (data : FinitePartialBijection α)
    {item : α} (member : item ∈ data.source) :
    data.extend.forward item = data.forward item := by
  exact FinitePermutation.extend_map_agrees
    data.source data.forward data.source_nodup
    data.forward_injectiveOn item member

theorem extend_backward_agrees (data : FinitePartialBijection α)
    {item : α} (member : item ∈ data.target) :
    data.extend.backward item = data.backward item := by
  have sourceMember := data.backward_mem member
  have forwardEquality := data.extend_forward_agrees sourceMember
  rw [data.forward_backward member] at forwardEquality
  have restored := congrArg data.extend.backward forwardEquality
  simpa only [data.extend.backward_forward] using restored.symm

theorem extend_finiteSupport (data : FinitePartialBijection α) :
    data.extend.FiniteSupport :=
  FinitePermutation.extend_finiteSupport _ _

end FinitePartialBijection


/-- Two independent finite partial bijections whose variable images agree
with a pair of simultaneous substitutions. -/
structure SubstitutionPartialBijection (forward backward : Subst) where
  ty : FinitePartialBijection TyVar
  cap : FinitePartialBijection CapVar
  ty_forward : ∀ {index}, index ∈ ty.source →
    forward.ty index = .var (ty.forward index)
  ty_backward : ∀ {index}, index ∈ ty.target →
    backward.ty index = .var (ty.backward index)
  cap_forward : ∀ {index}, index ∈ cap.source →
    forward.cap index = .var (cap.forward index)
  cap_backward : ∀ {index}, index ∈ cap.target →
    backward.cap index = .var (cap.backward index)

namespace SubstitutionPartialBijection

/-- Extend both sorts and package them as one source variable renaming. -/
def toVariableRenaming {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward) :
    VariableRenaming :=
  { tyForward := data.ty.extend.forward
    tyBackward := data.ty.extend.backward
    capForward := data.cap.extend.forward
    capBackward := data.cap.extend.backward
    ty_backward_forward := data.ty.extend.backward_forward
    ty_forward_backward := data.ty.extend.forward_backward
    cap_backward_forward := data.cap.extend.backward_forward
    cap_forward_backward := data.cap.extend.forward_backward }

theorem tyForward_agrees {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward)
    {index : TyVar} (member : index ∈ data.ty.source) :
    data.toVariableRenaming.tyForward index = data.ty.forward index :=
  data.ty.extend_forward_agrees member

theorem tyBackward_agrees {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward)
    {index : TyVar} (member : index ∈ data.ty.target) :
    data.toVariableRenaming.tyBackward index = data.ty.backward index :=
  data.ty.extend_backward_agrees member

theorem capForward_agrees {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward)
    {index : CapVar} (member : index ∈ data.cap.source) :
    data.toVariableRenaming.capForward index = data.cap.forward index :=
  data.cap.extend_forward_agrees member

theorem capBackward_agrees {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward)
    {index : CapVar} (member : index ∈ data.cap.target) :
    data.toVariableRenaming.capBackward index = data.cap.backward index :=
  data.cap.extend_backward_agrees member

theorem substitution_ty_agrees {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward)
    {index : TyVar} (member : index ∈ data.ty.source) :
    data.toVariableRenaming.substitution.ty index = forward.ty index := by
  simp only [VariableRenaming.substitution]
  rw [data.tyForward_agrees member, data.ty_forward member]

theorem substitution_cap_agrees {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward)
    {index : CapVar} (member : index ∈ data.cap.source) :
    data.toVariableRenaming.substitution.cap index = forward.cap index := by
  simp only [VariableRenaming.substitution]
  rw [data.capForward_agrees member, data.cap_forward member]

theorem finiteSupport {forward backward : Subst}
    (data : SubstitutionPartialBijection forward backward) :
    FinitePermutation.Permutation.FiniteSupport data.ty.extend ∧
      FinitePermutation.Permutation.FiniteSupport data.cap.extend :=
  ⟨data.ty.extend_finiteSupport, data.cap.extend_finiteSupport⟩

end SubstitutionPartialBijection

end TypePM.Source
