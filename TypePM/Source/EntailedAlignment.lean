import TypePM.EntailedPendingTransport
import TypePM.FreshAliasPrincipalClosure
import TypePM.Source.DirectLetComparison

/-!
# Semantic alignment of generated blocks

This module records the part of the proposed general-`let` invariant that is
independent of saturation transport.  Two types or delayed checking
obligations are aligned when every solution of a reference hard worklist
makes their substituted forms equal.

The main result is structural: this alignment is preserved by every
`GeneratedFrame`.  Thus target alignment is exactly the additional datum
needed to compose delayed-obligation alignment through application frames.
Acceptance transport is supplied by `TypePM.EntailedPendingTransport`.
-/

namespace TypePM.Source

/-- Two types agree after every solution of `reference` is applied. -/
def EntailedTypeEq (reference : List Equation) (left right : Ty) : Prop :=
  ∀ substitution, Solves substitution reference →
    left.apply substitution = right.apply substitution

namespace EntailedTypeEq

theorem refl (reference : List Equation) (target : Ty) :
    EntailedTypeEq reference target target :=
  fun _ _ => rfl

theorem weaken {smaller larger : List Equation} {left right : Ty}
    (entailed : EntailedTypeEq smaller left right)
    (solutions : ∀ substitution,
      Solves substitution larger → Solves substitution smaller) :
    EntailedTypeEq larger left right := by
  intro substitution solved
  exact entailed substitution (solutions substitution solved)

theorem fn {reference : List Equation} {left right : Ty}
    (entailed : EntailedTypeEq reference left right) (domain : Ty) :
    EntailedTypeEq reference (.fn domain left) (.fn domain right) := by
  intro substitution solved
  simp only [Ty.apply]
  rw [entailed substitution solved]

end EntailedTypeEq

private theorem entailedObligation_ofSource
    {reference : List Equation} {left right expected : Ty}
    (entailed : EntailedTypeEq reference left right) :
    EntailedObligationEq reference ⟨left, expected⟩ ⟨right, expected⟩ := by
  intro substitution solved
  simp only [CheckObligation.apply]
  rw [entailed substitution solved]

/-- Hard worklists have the same solutions, while result types and delayed
checks agree under every solution of the left worklist. -/
structure EntailedGeneratedAlignment (left right : Generated) : Prop where
  hardEquivalent : HardEquivalent left.hard right.hard
  targetEntailed : EntailedTypeEq left.hard left.target right.target
  pendingAligned : EntailedPendingEq left.hard left.pending right.pending

namespace EntailedGeneratedAlignment

theorem refl (generated : Generated) :
    EntailedGeneratedAlignment generated generated := by
  refine ⟨HardEquivalent.refl _, EntailedTypeEq.refl _ _, ?_⟩
  induction generated.pending with
  | nil => exact .nil
  | cons obligation pending induction =>
      exact .cons (EntailedObligationEq.refl _ obligation) induction

private theorem pending_trans
    {leftReference rightReference : List Equation}
    {left middle right : List CheckObligation}
    (first : EntailedPendingEq leftReference left middle)
    (second : EntailedPendingEq rightReference middle right)
    (references : HardEquivalent leftReference rightReference) :
    EntailedPendingEq leftReference left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | @cons leftHead middleHead leftTail middleTail headFirst tailFirst
      induction =>
      cases second with
      | cons headSecond tailSecond =>
          apply EntailedPendingEq.cons
          · intro substitution solved
            exact (headFirst substitution solved).trans
              (headSecond substitution
                ((references substitution).mp solved))
          · exact induction tailSecond

theorem symm {left right : Generated}
    (aligned : EntailedGeneratedAlignment left right) :
    EntailedGeneratedAlignment right left := by
  refine ⟨aligned.hardEquivalent.symm, ?_,
    aligned.pendingAligned.symm_of_hardEquivalent aligned.hardEquivalent⟩
  intro substitution solved
  exact (aligned.targetEntailed substitution
    ((aligned.hardEquivalent substitution).mpr solved)).symm

theorem trans {left middle right : Generated}
    (first : EntailedGeneratedAlignment left middle)
    (second : EntailedGeneratedAlignment middle right) :
    EntailedGeneratedAlignment left right := by
  refine ⟨first.hardEquivalent.trans second.hardEquivalent, ?_, ?_⟩
  · intro substitution solved
    exact (first.targetEntailed substitution solved).trans
      (second.targetEntailed substitution
        ((first.hardEquivalent substitution).mp solved))
  · exact pending_trans first.pendingAligned second.pendingAligned
      first.hardEquivalent

private theorem pending_weaken_general
    {weaker stronger : List Equation}
    {left right : List CheckObligation}
    (aligned : EntailedPendingEq weaker left right)
    (solutions : ∀ substitution,
      Solves substitution stronger → Solves substitution weaker) :
    EntailedPendingEq stronger left right := by
  induction aligned with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (head.weaken solutions) induction

/-- Adding one identical alias equation to both sides strengthens the common
hard theory without disturbing target or pending alignment. -/
theorem addAliasBoth {left right : Generated}
    (aligned : EntailedGeneratedAlignment left right)
    (alias : FreshAliasSequence.Alias) :
    EntailedGeneratedAlignment (alias.add left) (alias.add right) := by
  cases alias with
  | ty fresh existing =>
      let equation : Equation := .ty (.var fresh) (.var existing)
      refine ⟨?_, ?_, ?_⟩
      · change HardEquivalent (equation :: left.hard)
          (equation :: right.hard)
        simpa [equation] using
          ((HardEquivalent.refl [equation]).append aligned.hardEquivalent)
      · apply aligned.targetEntailed.weaken
        intro substitution solved
        exact (solves_cons substitution equation left.hard).mp solved |>.2
      · apply pending_weaken_general aligned.pendingAligned
        intro substitution solved
        exact (solves_cons substitution equation left.hard).mp solved |>.2
  | cap fresh existing =>
      let equation : Equation := .cap (.var fresh) (.var existing)
      refine ⟨?_, ?_, ?_⟩
      · change HardEquivalent (equation :: left.hard)
          (equation :: right.hard)
        simpa [equation] using
          ((HardEquivalent.refl [equation]).append aligned.hardEquivalent)
      · apply aligned.targetEntailed.weaken
        intro substitution solved
        exact (solves_cons substitution equation left.hard).mp solved |>.2
      · apply pending_weaken_general aligned.pendingAligned
        intro substitution solved
        exact (solves_cons substitution equation left.hard).mp solved |>.2

theorem addAllBoth {left right : Generated}
    (aligned : EntailedGeneratedAlignment left right)
    (aliases : List FreshAliasSequence.Alias) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll aliases left)
      (FreshAliasSequence.addAll aliases right) := by
  induction aliases generalizing left right with
  | nil => exact aligned
  | cons alias aliases induction =>
      exact induction (aligned.addAliasBoth alias)

theorem addAll_swap
    (first second : List FreshAliasSequence.Alias) (body : Generated) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll (first ++ second) body)
      (FreshAliasSequence.addAll (second ++ first) body) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [InterfaceAliasDecomposition.EquationLists.addAll_hard,
      InterfaceAliasDecomposition.EquationLists.addAll_hard]
    intro substitution
    simp [InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
      List.reverse_append, List.map_append, solves_append,
      and_left_comm, and_comm, and_assoc]
  · simpa using (EntailedTypeEq.refl
      (FreshAliasSequence.addAll (first ++ second) body).hard body.target)
  · rw [FreshAliasSequence.addAll_pending,
      FreshAliasSequence.addAll_pending]
    induction body.pending with
    | nil => exact .nil
    | cons obligation pending induction =>
        exact .cons (EntailedObligationEq.refl _ obligation) induction

private theorem addAliases_move_after_prefix
    (aliases : List FreshAliasSequence.Alias)
    (initial hard suffix : List Equation) :
    HardEquivalent
      (InterfaceAliasDecomposition.EquationLists.addAliases aliases
        (initial ++ hard ++ suffix))
      (initial ++
        InterfaceAliasDecomposition.EquationLists.addAliases aliases hard ++
        suffix) := by
  intro substitution
  simp [InterfaceAliasDecomposition.EquationLists.addAliases_eq_reverse_map_append,
    solves_append, and_comm, and_assoc]

private theorem pending_refl (reference : List Equation)
    (pending : List CheckObligation) :
    EntailedPendingEq reference pending pending := by
  induction pending with
  | nil => exact .nil
  | cons obligation obligations induction =>
      exact .cons (EntailedObligationEq.refl reference obligation) induction

private theorem addAll_lam_reposition
    (aliases : List FreshAliasSequence.Alias) (domain : Ty)
    (body : Generated) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll aliases (Generated.fromLam domain body))
      (Generated.fromLam domain (FreshAliasSequence.addAll aliases body)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Generated.fromLam,
      InterfaceAliasDecomposition.EquationLists.addAll_hard] using
      (HardEquivalent.refl
        (InterfaceAliasDecomposition.EquationLists.addAliases aliases
          body.hard))
  · simpa [Generated.fromLam] using
      (EntailedTypeEq.refl
        (FreshAliasSequence.addAll aliases
          (Generated.fromLam domain body)).hard
        (.fn domain body.target))
  · simpa [Generated.fromLam] using pending_refl
      (FreshAliasSequence.addAll aliases
        (Generated.fromLam domain body)).hard body.pending

private theorem addAll_appFunction_reposition
    (aliases : List FreshAliasSequence.Alias)
    (body argument : Generated) (domain target : Ty) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll aliases
        (Generated.fromApp body argument domain target))
      (Generated.fromApp (FreshAliasSequence.addAll aliases body)
        argument domain target) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Generated.fromApp, List.append_assoc,
      InterfaceAliasDecomposition.EquationLists.addAll_hard,
      InterfaceAliasDecomposition.EquationLists.addAliases_append] using
      (HardEquivalent.refl
        (InterfaceAliasDecomposition.EquationLists.addAliases aliases
          body.hard ++ (argument.hard ++
            [.ty body.target (.fn domain target)])))
  · simpa [Generated.fromApp] using (EntailedTypeEq.refl
      (FreshAliasSequence.addAll aliases
        (Generated.fromApp body argument domain target)).hard target)
  · simpa [Generated.fromApp] using pending_refl
      (FreshAliasSequence.addAll aliases
        (Generated.fromApp body argument domain target)).hard
      (body.pending ++ (argument.pending ++ [⟨argument.target, domain⟩]))

private theorem addAll_appArgument_reposition
    (aliases : List FreshAliasSequence.Alias)
    (body function : Generated) (domain target : Ty) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll aliases
        (Generated.fromApp function body domain target))
      (Generated.fromApp function (FreshAliasSequence.addAll aliases body)
        domain target) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [InterfaceAliasDecomposition.EquationLists.addAll_hard]
    simpa [Generated.fromApp, List.append_assoc,
      InterfaceAliasDecomposition.EquationLists.addAll_hard] using
      addAliases_move_after_prefix aliases function.hard body.hard
        [.ty function.target (.fn domain target)]
  · simpa [Generated.fromApp] using (EntailedTypeEq.refl
      (FreshAliasSequence.addAll aliases
        (Generated.fromApp function body domain target)).hard target)
  · simpa [Generated.fromApp] using pending_refl
      (FreshAliasSequence.addAll aliases
        (Generated.fromApp function body domain target)).hard
      (function.pending ++ (body.pending ++ [⟨body.target, domain⟩]))

private theorem addAll_letBody_reposition
    (aliases : List FreshAliasSequence.Alias)
    (effects : List Equation) (body : Generated) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll aliases (Generated.fromLet effects body))
      (Generated.fromLet effects (FreshAliasSequence.addAll aliases body)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [InterfaceAliasDecomposition.EquationLists.addAll_hard]
    simpa [Generated.fromLet,
      InterfaceAliasDecomposition.EquationLists.addAll_hard] using
      addAliases_move_after_prefix aliases effects body.hard []
  · simpa [Generated.fromLet] using
      (EntailedTypeEq.refl
        (FreshAliasSequence.addAll aliases
          (Generated.fromLet effects body)).hard body.target)
  · simpa [Generated.fromLet] using pending_refl
      (FreshAliasSequence.addAll aliases
        (Generated.fromLet effects body)).hard body.pending

private theorem addAll_tupleItem_reposition
    (aliases : List FreshAliasSequence.Alias)
    (before after : GeneratedItems) (body : Generated) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll aliases
        (GeneratedItems.asTuple <| GeneratedItems.append before <|
          GeneratedItems.append (GeneratedItems.singleton body) after))
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append
          (GeneratedItems.singleton
            (FreshAliasSequence.addAll aliases body)) after) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [InterfaceAliasDecomposition.EquationLists.addAll_hard]
    simpa [GeneratedItems.asTuple, GeneratedItems.append,
      GeneratedItems.singleton, GeneratedItems.cons, GeneratedItems.nil,
      List.append_assoc,
      InterfaceAliasDecomposition.EquationLists.addAll_hard] using
        addAliases_move_after_prefix aliases before.hard body.hard after.hard
  · simpa [GeneratedItems.asTuple, GeneratedItems.append,
      GeneratedItems.singleton, GeneratedItems.cons, GeneratedItems.nil]
      using (EntailedTypeEq.refl
        (FreshAliasSequence.addAll aliases
          (GeneratedItems.asTuple <| GeneratedItems.append before <|
            GeneratedItems.append (GeneratedItems.singleton body) after)).hard
        (GeneratedItems.asTuple <| GeneratedItems.append before <|
          GeneratedItems.append (GeneratedItems.singleton body) after).target)
  · simpa [GeneratedItems.asTuple, GeneratedItems.append,
      GeneratedItems.singleton, GeneratedItems.cons, GeneratedItems.nil,
      List.append_assoc] using pending_refl
        (FreshAliasSequence.addAll aliases
          (GeneratedItems.asTuple <| GeneratedItems.append before <|
            GeneratedItems.append (GeneratedItems.singleton body) after)).hard
        (before.pending ++ body.pending ++ after.pending)

private theorem solves_left_of_combined
    {initial suffix : List Equation} {substitution : Subst}
    (solved : Solves substitution (initial ++ suffix)) :
    Solves substitution initial :=
  (solves_append substitution initial suffix).mp solved |>.1

private theorem pending_weaken_append
    {reference suffix : List Equation}
    {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right) :
    EntailedPendingEq (reference ++ suffix) left right := by
  induction aligned with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (head.weaken fun substitution solved =>
          solves_left_of_combined solved)
        induction

private theorem pending_weaken
    {weaker stronger : List Equation}
    {left right : List CheckObligation}
    (aligned : EntailedPendingEq weaker left right)
    (solutions : ∀ substitution,
      Solves substitution stronger → Solves substitution weaker) :
    EntailedPendingEq stronger left right := by
  induction aligned with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (head.weaken solutions) induction

private theorem pending_append_refl
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right)
    (suffix : List CheckObligation) :
    EntailedPendingEq reference
      (left ++ suffix) (right ++ suffix) := by
  induction aligned with
  | nil =>
      induction suffix with
      | nil => exact .nil
      | cons obligation obligations induction =>
          exact .cons (EntailedObligationEq.refl reference obligation) induction
  | cons head tail induction => exact .cons head induction

private theorem pending_append
    {reference : List Equation}
    {left₁ right₁ left₂ right₂ : List CheckObligation}
    (first : EntailedPendingEq reference left₁ right₁)
    (second : EntailedPendingEq reference left₂ right₂) :
    EntailedPendingEq reference
      (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction first with
  | nil => simpa using second
  | cons head tail induction => exact .cons head induction

private theorem pending_prepend_refl
    {reference : List Equation} {left right : List CheckObligation}
    (initial : List CheckObligation)
    (aligned : EntailedPendingEq reference left right) :
    EntailedPendingEq reference
      (initial ++ left) (initial ++ right) := by
  induction initial with
  | nil => simpa using aligned
  | cons head tail induction =>
      exact .cons (EntailedObligationEq.refl reference head) induction

private theorem hard_append_right
    {left right suffix : List Equation}
    (equivalent : HardEquivalent left right) :
    HardEquivalent (left ++ suffix) (right ++ suffix) :=
  equivalent.appendLeft

/-- Lambda preserves semantic alignment. -/
theorem lam {left right : Generated}
    (aligned : EntailedGeneratedAlignment left right) (domain : Ty) :
    EntailedGeneratedAlignment
      (Generated.fromLam domain left) (Generated.fromLam domain right) := by
  refine ⟨aligned.hardEquivalent, aligned.targetEntailed.fn domain, ?_⟩
  exact aligned.pendingAligned

/-- Using aligned blocks as the function side of a common application
preserves alignment. -/
theorem appFunction {left right argument : Generated} (domain target : Ty)
    (aligned : EntailedGeneratedAlignment left right) :
    EntailedGeneratedAlignment
      (Generated.fromApp left argument domain target)
      (Generated.fromApp right argument domain target) := by
  let suffix := argument.hard ++
    [.ty left.target (.fn domain target)]
  let rightSuffix := argument.hard ++
    [.ty right.target (.fn domain target)]
  have hard : HardEquivalent (left.hard ++ suffix)
      (right.hard ++ rightSuffix) := by
    intro substitution
    simp only [suffix, rightSuffix, solves_append, solves_cons, solves_nil,
      and_true]
    constructor
    · rintro ⟨leftSolved, argumentSolved, applicationSolved⟩
      have targetEq := aligned.targetEntailed substitution leftSolved
      exact ⟨(aligned.hardEquivalent substitution).mp leftSolved,
        argumentSolved, by
          simpa [Equation.Holds] using targetEq.symm ▸ applicationSolved⟩
    · rintro ⟨rightSolved, argumentSolved, applicationSolved⟩
      have leftSolved :=
        (aligned.hardEquivalent substitution).mpr rightSolved
      have targetEq := aligned.targetEntailed substitution leftSolved
      exact ⟨leftSolved, argumentSolved, by
        simpa [Equation.Holds] using targetEq ▸ applicationSolved⟩
  refine ⟨?_, EntailedTypeEq.refl _ target, ?_⟩
  · simpa [Generated.fromApp, suffix, rightSuffix, List.append_assoc] using hard
  · have weakened := pending_weaken_append aligned.pendingAligned
      (suffix := suffix)
    have withArgument := pending_append_refl weakened argument.pending
    have withCheck := pending_append_refl withArgument
      [⟨argument.target, domain⟩]
    simpa [Generated.fromApp, suffix, List.append_assoc] using withCheck

/-- Using aligned blocks as the argument side of a common application
preserves alignment. -/
theorem appArgument {left right function : Generated} (domain target : Ty)
    (aligned : EntailedGeneratedAlignment left right) :
    EntailedGeneratedAlignment
      (Generated.fromApp function left domain target)
      (Generated.fromApp function right domain target) := by
  let leftHard := function.hard ++ left.hard ++
    [.ty function.target (.fn domain target)]
  let rightHard := function.hard ++ right.hard ++
    [.ty function.target (.fn domain target)]
  have hard : HardEquivalent leftHard rightHard := by
    simpa [leftHard, rightHard, List.append_assoc] using
      ((HardEquivalent.refl function.hard).append
        (aligned.hardEquivalent.appendLeft
          (suffix := [.ty function.target (.fn domain target)])))
  refine ⟨?_, EntailedTypeEq.refl _ target, ?_⟩
  · simpa [Generated.fromApp, leftHard, rightHard,
      List.append_assoc] using hard
  · have alignedUnder : EntailedPendingEq leftHard
        left.pending right.pending := by
      apply pending_weaken aligned.pendingAligned
      intro substitution solved
      change Solves substitution
        (function.hard ++ left.hard ++
          [.ty function.target (.fn domain target)]) at solved
      have split := (solves_append substitution function.hard
        (left.hard ++ [.ty function.target (.fn domain target)])).mp
          (by simpa [List.append_assoc] using solved)
      exact (solves_append substitution left.hard
        [.ty function.target (.fn domain target)]).mp split.2 |>.1
    have prefixed := pending_prepend_refl function.pending alignedUnder
    have sourceCheck : EntailedObligationEq leftHard
        ⟨left.target, domain⟩ ⟨right.target, domain⟩ := by
      apply entailedObligation_ofSource
      apply aligned.targetEntailed.weaken
      intro substitution solved
      change Solves substitution
        (function.hard ++ left.hard ++
          [.ty function.target (.fn domain target)]) at solved
      have split := (solves_append substitution function.hard
        (left.hard ++ [.ty function.target (.fn domain target)])).mp
          (by simpa [List.append_assoc] using solved)
      exact (solves_append substitution left.hard
        [.ty function.target (.fn domain target)]).mp split.2 |>.1
    exact pending_append prefixed (.cons sourceCheck .nil)

/-- Adding the same `let` effects preserves semantic alignment. -/
theorem letBody {left right : Generated} (effects : List Equation)
    (aligned : EntailedGeneratedAlignment left right) :
    EntailedGeneratedAlignment
      (Generated.fromLet effects left) (Generated.fromLet effects right) := by
  have hard : HardEquivalent (effects ++ left.hard) (effects ++ right.hard) :=
    (HardEquivalent.refl effects).append aligned.hardEquivalent
  refine ⟨hard, ?_, ?_⟩
  · apply aligned.targetEntailed.weaken
    intro substitution solved
    exact (solves_append substitution effects left.hard).mp solved |>.2
  · exact pending_weaken aligned.pendingAligned (by
      intro substitution solved
      exact (solves_append substitution effects left.hard).mp solved |>.2)

/-- Replacing one item of a common tuple by an aligned item preserves
alignment. -/
theorem tupleItem {left right : Generated}
    (before after : GeneratedItems)
    (aligned : EntailedGeneratedAlignment left right) :
    EntailedGeneratedAlignment
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append (GeneratedItems.singleton left) after)
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append (GeneratedItems.singleton right) after) := by
  let leftHard := before.hard ++ left.hard ++ after.hard
  let rightHard := before.hard ++ right.hard ++ after.hard
  have hard : HardEquivalent leftHard rightHard := by
    simpa [leftHard, rightHard, List.append_assoc] using
      ((HardEquivalent.refl before.hard).append
        (aligned.hardEquivalent.appendLeft (suffix := after.hard)))
  refine ⟨?_, ?_, ?_⟩
  · simpa [GeneratedItems.asTuple, GeneratedItems.append,
      GeneratedItems.singleton, GeneratedItems.cons, GeneratedItems.nil,
      leftHard, rightHard, List.append_assoc] using hard
  · intro substitution solved
    have leftSolved : Solves substitution left.hard := by
      have solved' : Solves substitution leftHard := by
        simpa [GeneratedItems.asTuple, GeneratedItems.append,
          GeneratedItems.singleton, GeneratedItems.cons, GeneratedItems.nil,
          leftHard, List.append_assoc] using solved
      have outer := (solves_append substitution before.hard
        (left.hard ++ after.hard)).mp
        (by simpa [leftHard, List.append_assoc] using solved')
      exact (solves_append substitution left.hard after.hard).mp outer.2 |>.1
    have targetEq := aligned.targetEntailed substitution leftSolved
    change
      Ty.prod (Ty.applyList substitution
        (before.targets ++ left.target :: after.targets)) =
      Ty.prod (Ty.applyList substitution
        (before.targets ++ right.target :: after.targets))
    congr 1
    induction before.targets with
    | nil => simp [Ty.applyList, targetEq]
    | cons item items induction => simp [Ty.applyList, induction]
  · have alignedUnder : EntailedPendingEq leftHard
        left.pending right.pending := by
      apply pending_weaken aligned.pendingAligned
      intro substitution solved
      change Solves substitution leftHard at solved
      have outer := (solves_append substitution before.hard
        (left.hard ++ after.hard)).mp
        (by simpa [leftHard, List.append_assoc] using solved)
      exact (solves_append substitution left.hard after.hard).mp outer.2 |>.1
    have prefixed := pending_prepend_refl before.pending alignedUnder
    have completed := pending_append_refl prefixed after.pending
    simpa [GeneratedItems.asTuple, GeneratedItems.append,
      GeneratedItems.singleton, GeneratedItems.cons, GeneratedItems.nil,
      leftHard, List.append_assoc] using completed

/-- Semantic alignment is a congruence for every one-hole source-generated
frame.  This is the compositional core needed by the proposed `letE`
certificate. -/
theorem frame {left right : Generated}
    (aligned : EntailedGeneratedAlignment left right)
    (generatedFrame : GeneratedFrame) :
    EntailedGeneratedAlignment
      (generatedFrame.plug left) (generatedFrame.plug right) := by
  induction generatedFrame generalizing left right with
  | hole => exact aligned
  | lam domain outer induction =>
      exact induction (aligned.lam domain)
  | appFunction argument domain target outer induction =>
      exact induction (aligned.appFunction domain target)
  | appArgument function domain target outer induction =>
      exact induction (aligned.appArgument domain target)
  | tupleItem before after outer induction =>
      exact induction (aligned.tupleItem before after)
  | letBody effects outer induction =>
      exact induction (aligned.letBody effects)

/-- Moving a finite alias sequence from outside a frame to its hole changes
only the order of conjunctive hard equations. -/
theorem addAll_frame_reposition
    (aliases : List FreshAliasSequence.Alias)
    (generatedFrame : GeneratedFrame) (body : Generated) :
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll aliases (generatedFrame.plug body))
      (generatedFrame.plug (FreshAliasSequence.addAll aliases body)) := by
  induction generatedFrame generalizing body with
  | hole => exact EntailedGeneratedAlignment.refl _
  | lam domain outer induction =>
      exact (induction (Generated.fromLam domain body)).trans
        ((addAll_lam_reposition aliases domain body).frame outer)
  | appFunction argument domain target outer induction =>
      exact (induction (Generated.fromApp body argument domain target)).trans
        ((addAll_appFunction_reposition aliases body argument domain target).frame
          outer)
  | appArgument function domain target outer induction =>
      exact (induction (Generated.fromApp function body domain target)).trans
        ((addAll_appArgument_reposition aliases body function domain target).frame
          outer)
  | tupleItem before after outer induction =>
      exact (induction (GeneratedItems.asTuple <|
        GeneratedItems.append before <|
          GeneratedItems.append (GeneratedItems.singleton body) after)).trans
        ((addAll_tupleItem_reposition aliases before after body).frame outer)
  | letBody effects outer induction =>
      exact (induction (Generated.fromLet effects body)).trans
        ((addAll_letBody_reposition aliases effects body).frame outer)

end EntailedGeneratedAlignment

namespace GeneratedFrame

/-- Every variable of the hole block remains observable in the block obtained
by plugging it into a source-generated frame. -/
theorem hole_unificationVars_subset
    (generatedFrame : GeneratedFrame) (body : Generated) :
    ∀ candidate, candidate ∈ body.unificationVars →
      candidate ∈ (generatedFrame.plug body).unificationVars := by
  induction generatedFrame generalizing body with
  | hole => exact fun _ member => member
  | lam domain outer induction =>
      intro candidate member
      apply induction (Generated.fromLam domain body) candidate
      simp only [Generated.fromLam, Generated.unificationVars,
        Ty.unificationVars, List.mem_append] at member ⊢
      rcases member with (targetMember | hardMember) | pendingMember
      · exact Or.inl (Or.inl (Or.inr targetMember))
      · exact Or.inl (Or.inr hardMember)
      · exact Or.inr pendingMember
  | appFunction argument domain target outer induction =>
      intro candidate member
      apply induction (Generated.fromApp body argument domain target) candidate
      simp only [Generated.fromApp, Generated.unificationVars,
        Ty.unificationVars, Equation.unificationVars,
        CheckObligation.unificationVars, TypePM.unificationVars,
        unificationVars_append, pendingUnificationVars,
        pendingUnificationVars_append, List.mem_append] at member ⊢
      rcases member with (targetMember | hardMember) | pendingMember
      · exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl targetMember))))
      · exact Or.inl (Or.inr (Or.inl (Or.inl hardMember)))
      · exact Or.inr (Or.inl (Or.inl pendingMember))
  | appArgument function domain target outer induction =>
      intro candidate member
      apply induction (Generated.fromApp function body domain target) candidate
      simp only [Generated.fromApp, Generated.unificationVars,
        Ty.unificationVars, Equation.unificationVars,
        CheckObligation.unificationVars, TypePM.unificationVars,
        unificationVars_append, pendingUnificationVars,
        pendingUnificationVars_append, List.mem_append] at member ⊢
      rcases member with (targetMember | hardMember) | pendingMember
      · exact Or.inr (Or.inr (Or.inl (Or.inl targetMember)))
      · exact Or.inl (Or.inr (Or.inl (Or.inr hardMember)))
      · exact Or.inr (Or.inl (Or.inr pendingMember))
  | tupleItem before after outer induction =>
      intro candidate member
      apply induction (GeneratedItems.asTuple <|
        GeneratedItems.append before <|
          GeneratedItems.append (GeneratedItems.singleton body) after) candidate
      have singletonMember : candidate ∈
          (GeneratedItems.singleton body).unificationVars := by
        simpa using member
      have middleMember : candidate ∈
          (GeneratedItems.append (GeneratedItems.singleton body) after).unificationVars :=
        (GeneratedItems.mem_unificationVars_append candidate _ _).2
          (Or.inl singletonMember)
      have allMember : candidate ∈
          (GeneratedItems.append before
            (GeneratedItems.append (GeneratedItems.singleton body) after)).unificationVars :=
        (GeneratedItems.mem_unificationVars_append candidate _ _).2
          (Or.inr middleMember)
      exact allMember
  | letBody effects outer induction =>
      intro candidate member
      apply induction (Generated.fromLet effects body) candidate
      simp only [Generated.fromLet, Generated.unificationVars,
        unificationVars_append, List.mem_append] at member ⊢
      rcases member with (targetMember | hardMember) | pendingMember
      · exact Or.inl (Or.inl targetMember)
      · exact Or.inl (Or.inr (Or.inr hardMember))
      · exact Or.inr pendingMember

end GeneratedFrame

/-- A finite-alias semantic certificate.  The aliases may be asymmetric;
this is essential in the source-derived counterexample, where only one side
needs the missing interface equality. -/
structure EntailedAlignmentCertificate
    (start next : Supply) (left right : Generated) where
  hidden : List UnificationVar
  hiddenFresh : VariablesFreshIn start next hidden
  leftAliases : List FreshAliasSequence.Alias
  rightAliases : List FreshAliasSequence.Alias
  leftAliasFresh : ∀ alias, alias ∈ leftAliases →
    InterfaceAliasDecomposition.AliasFreshness.freshVariable alias ∈ hidden
  rightAliasFresh : ∀ alias, alias ∈ rightAliases →
    InterfaceAliasDecomposition.AliasFreshness.freshVariable alias ∈ hidden
  leftAdmissible : ∀ (frame : GeneratedFrame), frame.Avoids hidden →
    FreshAliasSequence.Admissible leftAliases (frame.plug left)
  rightAdmissible : ∀ (frame : GeneratedFrame), frame.Avoids hidden →
    FreshAliasSequence.Admissible rightAliases (frame.plug right)
  aligned : ∀ (frame : GeneratedFrame), frame.Avoids hidden →
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll leftAliases (frame.plug left))
      (FreshAliasSequence.addAll rightAliases (frame.plug right))

namespace EntailedAlignmentCertificate

theorem addAll_append
    (first second : List FreshAliasSequence.Alias) (body : Generated) :
    FreshAliasSequence.addAll (first ++ second) body =
      FreshAliasSequence.addAll second
        (FreshAliasSequence.addAll first body) := by
  induction first generalizing body with
  | nil => rfl
  | cons alias aliases induction =>
      simp only [List.cons_append, FreshAliasSequence.addAll]
      exact induction (alias.add body)

def refl (start next : Supply) (generated : Generated) :
    EntailedAlignmentCertificate start next generated generated :=
  { hidden := []
    hiddenFresh := VariablesFreshIn.nil start next
    leftAliases := []
    rightAliases := []
    leftAliasFresh := by simp
    rightAliasFresh := by simp
    leftAdmissible := by intro _frame _frameAvoids; trivial
    rightAdmissible := by intro _frame _frameAvoids; trivial
    aligned := by
      intro frame _frameAvoids
      exact EntailedGeneratedAlignment.refl (frame.plug generated) }

def rebase
    {start next newStart newNext : Supply} {left right : Generated}
    (certificate : EntailedAlignmentCertificate start next left right)
    (hiddenFresh : VariablesFreshIn newStart newNext certificate.hidden) :
    EntailedAlignmentCertificate newStart newNext left right :=
  { certificate with hiddenFresh := hiddenFresh }

def symm
    {start next : Supply} {left right : Generated}
    (certificate : EntailedAlignmentCertificate start next left right) :
    EntailedAlignmentCertificate start next right left :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.rightAliases
    rightAliases := certificate.leftAliases
    leftAliasFresh := certificate.rightAliasFresh
    rightAliasFresh := certificate.leftAliasFresh
    leftAdmissible := certificate.rightAdmissible
    rightAdmissible := certificate.leftAdmissible
    aligned := by
      intro frame frameAvoids
      exact (certificate.aligned frame frameAvoids).symm }

/-- General transitivity interface.  The caller must semantically reconcile
the two augmented presentations of the middle block. -/
def transWith
    {start next : Supply} {left middle right : Generated}
    (first : EntailedAlignmentCertificate start next left middle)
    (second : EntailedAlignmentCertificate start next middle right)
    (middleAligned : ∀ (frame : GeneratedFrame),
      frame.Avoids (first.hidden ++ second.hidden) →
        EntailedGeneratedAlignment
          (FreshAliasSequence.addAll first.rightAliases
            (frame.plug middle))
          (FreshAliasSequence.addAll second.leftAliases
            (frame.plug middle))) :
    EntailedAlignmentCertificate start next left right :=
  { hidden := first.hidden ++ second.hidden
    hiddenFresh := first.hiddenFresh.append second.hiddenFresh
    leftAliases := first.leftAliases
    rightAliases := second.rightAliases
    leftAliasFresh := by
      intro alias member
      exact List.mem_append_left _ (first.leftAliasFresh alias member)
    rightAliasFresh := by
      intro alias member
      exact List.mem_append_right _ (second.rightAliasFresh alias member)
    leftAdmissible := by
      intro frame frameAvoids
      exact first.leftAdmissible frame frameAvoids.of_append_left
    rightAdmissible := by
      intro frame frameAvoids
      exact second.rightAdmissible frame frameAvoids.of_append_right
    aligned := by
      intro frame frameAvoids
      have leftToMiddle := first.aligned frame frameAvoids.of_append_left
      have middleToRight := second.aligned frame frameAvoids.of_append_right
      exact leftToMiddle.trans
        ((middleAligned frame frameAvoids).trans middleToRight) }

/-- Transitivity specializes to literal equality of the two middle alias
sequences.  Without at least semantic middle compatibility, arbitrary alias
sequences may impose different equations and transitivity is invalid. -/
def trans
    {start next : Supply} {left middle right : Generated}
    (first : EntailedAlignmentCertificate start next left middle)
    (second : EntailedAlignmentCertificate start next middle right)
    (middleAliases : first.rightAliases = second.leftAliases) :
    EntailedAlignmentCertificate start next left right := by
  apply first.transWith second
  intro frame _frameAvoids
  rw [middleAliases]
  exact EntailedGeneratedAlignment.refl _

/-- Insert a certified pair under a common lambda frame. -/
def lam
    {start next : Supply} {left right : Generated}
    (certificate : EntailedAlignmentCertificate start next left right)
    (domain : Ty) (domainAvoids : TypeAvoids certificate.hidden domain) :
    EntailedAlignmentCertificate start next
      (Generated.fromLam domain left) (Generated.fromLam domain right) :=
  { certificate with
    leftAdmissible := by
      intro outer outerAvoids
      exact certificate.leftAdmissible (.lam domain outer)
        ⟨domainAvoids, outerAvoids⟩
    rightAdmissible := by
      intro outer outerAvoids
      exact certificate.rightAdmissible (.lam domain outer)
        ⟨domainAvoids, outerAvoids⟩
    aligned := by
      intro outer outerAvoids
      exact certificate.aligned (.lam domain outer)
        ⟨domainAvoids, outerAvoids⟩ }

/-- Insert a certified pair as the function of a common application. -/
def appFunction
    {start next : Supply} {left right argument : Generated}
    (certificate : EntailedAlignmentCertificate start next left right)
    (domain target : Ty)
    (argumentAvoids : GeneratedAvoids certificate.hidden argument)
    (domainAvoids : TypeAvoids certificate.hidden domain)
    (targetAvoids : TypeAvoids certificate.hidden target) :
    EntailedAlignmentCertificate start next
      (Generated.fromApp left argument domain target)
      (Generated.fromApp right argument domain target) :=
  { certificate with
    leftAdmissible := by
      intro outer outerAvoids
      exact certificate.leftAdmissible
        (.appFunction argument domain target outer)
        ⟨argumentAvoids, domainAvoids, targetAvoids, outerAvoids⟩
    rightAdmissible := by
      intro outer outerAvoids
      exact certificate.rightAdmissible
        (.appFunction argument domain target outer)
        ⟨argumentAvoids, domainAvoids, targetAvoids, outerAvoids⟩
    aligned := by
      intro outer outerAvoids
      exact certificate.aligned
        (.appFunction argument domain target outer)
        ⟨argumentAvoids, domainAvoids, targetAvoids, outerAvoids⟩ }

/-- Insert a certified pair as the argument of a common application. -/
def appArgument
    {start next : Supply} {left right function : Generated}
    (certificate : EntailedAlignmentCertificate start next left right)
    (domain target : Ty)
    (functionAvoids : GeneratedAvoids certificate.hidden function)
    (domainAvoids : TypeAvoids certificate.hidden domain)
    (targetAvoids : TypeAvoids certificate.hidden target) :
    EntailedAlignmentCertificate start next
      (Generated.fromApp function left domain target)
      (Generated.fromApp function right domain target) :=
  { certificate with
    leftAdmissible := by
      intro outer outerAvoids
      exact certificate.leftAdmissible
        (.appArgument function domain target outer)
        ⟨functionAvoids, domainAvoids, targetAvoids, outerAvoids⟩
    rightAdmissible := by
      intro outer outerAvoids
      exact certificate.rightAdmissible
        (.appArgument function domain target outer)
        ⟨functionAvoids, domainAvoids, targetAvoids, outerAvoids⟩
    aligned := by
      intro outer outerAvoids
      exact certificate.aligned
        (.appArgument function domain target outer)
        ⟨functionAvoids, domainAvoids, targetAvoids, outerAvoids⟩ }

/-- Compose independently certified function and argument blocks.  The
cross-avoidance hypotheses are exactly those produced by sequential source
elaboration.  The middle-alias equality is currently essential: it says that
the two presentations of `fromApp rightFunction leftArgument` impose the
same auxiliary equations. -/
def app
    {start next : Supply}
    {leftFunction rightFunction leftArgument rightArgument : Generated}
    (functionCertificate : EntailedAlignmentCertificate start next
      leftFunction rightFunction)
    (argumentCertificate : EntailedAlignmentCertificate start next
      leftArgument rightArgument)
    (domain target : Ty)
    (leftArgumentAvoids : GeneratedAvoids
      functionCertificate.hidden leftArgument)
    (rightFunctionAvoids : GeneratedAvoids
      argumentCertificate.hidden rightFunction)
    (domainAvoidsFunction : TypeAvoids
      functionCertificate.hidden domain)
    (targetAvoidsFunction : TypeAvoids
      functionCertificate.hidden target)
    (domainAvoidsArgument : TypeAvoids
      argumentCertificate.hidden domain)
    (targetAvoidsArgument : TypeAvoids
      argumentCertificate.hidden target)
    (middleAliases : functionCertificate.rightAliases =
      argumentCertificate.leftAliases) :
    EntailedAlignmentCertificate start next
      (Generated.fromApp leftFunction leftArgument domain target)
      (Generated.fromApp rightFunction rightArgument domain target) := by
  let functionStep := functionCertificate.appFunction domain target
    leftArgumentAvoids domainAvoidsFunction targetAvoidsFunction
  let argumentStep := argumentCertificate.appArgument domain target
    rightFunctionAvoids domainAvoidsArgument targetAvoidsArgument
  exact functionStep.trans argumentStep middleAliases

/-- General two-child application composition.  The two child alias lists
are accumulated independently on each concrete side.  Semantic alignment is
closed here; the remaining explicit premises are exactly the stepwise
admissibility facts for the concatenated lists. -/
def appCombined
    {start next : Supply}
    {leftFunction rightFunction leftArgument rightArgument : Generated}
    (functionCertificate : EntailedAlignmentCertificate start next
      leftFunction rightFunction)
    (argumentCertificate : EntailedAlignmentCertificate start next
      leftArgument rightArgument)
    (domain target : Ty)
    (leftArgumentAvoids : GeneratedAvoids
      functionCertificate.hidden leftArgument)
    (rightFunctionAvoids : GeneratedAvoids
      argumentCertificate.hidden rightFunction)
    (domainAvoidsFunction : TypeAvoids
      functionCertificate.hidden domain)
    (targetAvoidsFunction : TypeAvoids
      functionCertificate.hidden target)
    (domainAvoidsArgument : TypeAvoids
      argumentCertificate.hidden domain)
    (targetAvoidsArgument : TypeAvoids
      argumentCertificate.hidden target)
    (combinedLeftAdmissible : ∀ (frame : GeneratedFrame),
      frame.Avoids
          (functionCertificate.hidden ++ argumentCertificate.hidden) →
        FreshAliasSequence.Admissible
          (functionCertificate.leftAliases ++
            argumentCertificate.leftAliases)
          (frame.plug (Generated.fromApp leftFunction leftArgument
            domain target)))
    (combinedRightAdmissible : ∀ (frame : GeneratedFrame),
      frame.Avoids
          (functionCertificate.hidden ++ argumentCertificate.hidden) →
        FreshAliasSequence.Admissible
          (functionCertificate.rightAliases ++
            argumentCertificate.rightAliases)
          (frame.plug (Generated.fromApp rightFunction rightArgument
            domain target))) :
    EntailedAlignmentCertificate start next
      (Generated.fromApp leftFunction leftArgument domain target)
      (Generated.fromApp rightFunction rightArgument domain target) :=
  { hidden := functionCertificate.hidden ++ argumentCertificate.hidden
    hiddenFresh := functionCertificate.hiddenFresh.append
      argumentCertificate.hiddenFresh
    leftAliases := functionCertificate.leftAliases ++
      argumentCertificate.leftAliases
    rightAliases := functionCertificate.rightAliases ++
      argumentCertificate.rightAliases
    leftAliasFresh := by
      intro alias member
      rcases List.mem_append.mp member with functionMember | argumentMember
      · exact List.mem_append_left _
          (functionCertificate.leftAliasFresh alias functionMember)
      · exact List.mem_append_right _
          (argumentCertificate.leftAliasFresh alias argumentMember)
    rightAliasFresh := by
      intro alias member
      rcases List.mem_append.mp member with functionMember | argumentMember
      · exact List.mem_append_left _
          (functionCertificate.rightAliasFresh alias functionMember)
      · exact List.mem_append_right _
          (argumentCertificate.rightAliasFresh alias argumentMember)
    leftAdmissible := combinedLeftAdmissible
    rightAdmissible := combinedRightAdmissible
    aligned := by
      intro outer outerAvoids
      have functionBase := functionCertificate.aligned
        (.appFunction leftArgument domain target outer)
        ⟨leftArgumentAvoids, domainAvoidsFunction,
          targetAvoidsFunction, outerAvoids.of_append_left⟩
      have functionStrong := functionBase.addAllBoth
        argumentCertificate.leftAliases
      have argumentBase := argumentCertificate.aligned
        (.appArgument rightFunction domain target outer)
        ⟨rightFunctionAvoids, domainAvoidsArgument,
          targetAvoidsArgument, outerAvoids.of_append_right⟩
      have argumentStrong := argumentBase.addAllBoth
        functionCertificate.rightAliases
      have functionStrong' : EntailedGeneratedAlignment
          (FreshAliasSequence.addAll
            (functionCertificate.leftAliases ++
              argumentCertificate.leftAliases)
            (outer.plug (Generated.fromApp leftFunction leftArgument
              domain target)))
          (FreshAliasSequence.addAll
            (functionCertificate.rightAliases ++
              argumentCertificate.leftAliases)
            (outer.plug (Generated.fromApp rightFunction leftArgument
              domain target))) := by
        rw [addAll_append, addAll_append]
        exact functionStrong
      have argumentStrong' : EntailedGeneratedAlignment
          (FreshAliasSequence.addAll
            (argumentCertificate.leftAliases ++
              functionCertificate.rightAliases)
            (outer.plug (Generated.fromApp rightFunction leftArgument
              domain target)))
          (FreshAliasSequence.addAll
            (argumentCertificate.rightAliases ++
              functionCertificate.rightAliases)
            (outer.plug (Generated.fromApp rightFunction rightArgument
              domain target))) := by
        rw [addAll_append, addAll_append]
        exact argumentStrong
      have middleSwap := EntailedGeneratedAlignment.addAll_swap
        functionCertificate.rightAliases argumentCertificate.leftAliases
        (outer.plug (Generated.fromApp rightFunction leftArgument
          domain target))
      have rightSwap := EntailedGeneratedAlignment.addAll_swap
        argumentCertificate.rightAliases functionCertificate.rightAliases
        (outer.plug (Generated.fromApp rightFunction rightArgument
          domain target))
      exact functionStrong'.trans
        (middleSwap.trans (argumentStrong'.trans rightSwap)) }

/-- General application composition using the standard `ScopedBy`
freshness criterion.  Source support provenance can target these two
pointwise scope obligations directly. -/
def appCombinedScoped
    {start next : Supply}
    {leftFunction rightFunction leftArgument rightArgument : Generated}
    (functionCertificate : EntailedAlignmentCertificate start next
      leftFunction rightFunction)
    (argumentCertificate : EntailedAlignmentCertificate start next
      leftArgument rightArgument)
    (domain target : Ty)
    (leftArgumentAvoids : GeneratedAvoids
      functionCertificate.hidden leftArgument)
    (rightFunctionAvoids : GeneratedAvoids
      argumentCertificate.hidden rightFunction)
    (domainAvoidsFunction : TypeAvoids
      functionCertificate.hidden domain)
    (targetAvoidsFunction : TypeAvoids
      functionCertificate.hidden target)
    (domainAvoidsArgument : TypeAvoids
      argumentCertificate.hidden domain)
    (targetAvoidsArgument : TypeAvoids
      argumentCertificate.hidden target)
    (leftScoped : ∀ (frame : GeneratedFrame),
      frame.Avoids
          (functionCertificate.hidden ++ argumentCertificate.hidden) →
        InterfaceAliasDecomposition.AliasFreshness.ScopedBy
          (frame.plug (Generated.fromApp leftFunction leftArgument
            domain target)).unificationVars
          (functionCertificate.leftAliases ++
            argumentCertificate.leftAliases))
    (rightScoped : ∀ (frame : GeneratedFrame),
      frame.Avoids
          (functionCertificate.hidden ++ argumentCertificate.hidden) →
        InterfaceAliasDecomposition.AliasFreshness.ScopedBy
          (frame.plug (Generated.fromApp rightFunction rightArgument
            domain target)).unificationVars
          (functionCertificate.rightAliases ++
            argumentCertificate.rightAliases)) :
    EntailedAlignmentCertificate start next
      (Generated.fromApp leftFunction leftArgument domain target)
      (Generated.fromApp rightFunction rightArgument domain target) := by
  apply appCombined functionCertificate argumentCertificate domain target
    leftArgumentAvoids rightFunctionAvoids domainAvoidsFunction
    targetAvoidsFunction domainAvoidsArgument targetAvoidsArgument
  · intro frame frameAvoids
    exact InterfaceAliasDecomposition.AliasFreshness.admissible_of_scopedBy
      (leftScoped frame frameAvoids) (fun _candidate member => member)
  · intro frame frameAvoids
    exact InterfaceAliasDecomposition.AliasFreshness.admissible_of_scopedBy
      (rightScoped frame frameAvoids) (fun _candidate member => member)

def tupleItem
    {start next : Supply} {left right : Generated}
    (certificate : EntailedAlignmentCertificate start next left right)
    (before after : GeneratedItems)
    (beforeAvoids : GeneratedItemsAvoid certificate.hidden before)
    (afterAvoids : GeneratedItemsAvoid certificate.hidden after) :
    EntailedAlignmentCertificate start next
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append (GeneratedItems.singleton left) after)
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append (GeneratedItems.singleton right) after) :=
  { certificate with
    leftAdmissible := by
      intro outer outerAvoids
      exact certificate.leftAdmissible (.tupleItem before after outer)
        ⟨beforeAvoids, afterAvoids, outerAvoids⟩
    rightAdmissible := by
      intro outer outerAvoids
      exact certificate.rightAdmissible (.tupleItem before after outer)
        ⟨beforeAvoids, afterAvoids, outerAvoids⟩
    aligned := by
      intro outer outerAvoids
      exact certificate.aligned (.tupleItem before after outer)
        ⟨beforeAvoids, afterAvoids, outerAvoids⟩ }

def letBody
    {start next : Supply} {left right : Generated}
    (certificate : EntailedAlignmentCertificate start next left right)
    (effects : List Equation)
    (effectsAvoid : EquationsAvoid certificate.hidden effects) :
    EntailedAlignmentCertificate start next
      (Generated.fromLet effects left) (Generated.fromLet effects right) :=
  { certificate with
    leftAdmissible := by
      intro outer outerAvoids
      exact certificate.leftAdmissible (.letBody effects outer)
        ⟨effectsAvoid, outerAvoids⟩
    rightAdmissible := by
      intro outer outerAvoids
      exact certificate.rightAdmissible (.letBody effects outer)
        ⟨effectsAvoid, outerAvoids⟩
    aligned := by
      intro outer outerAvoids
      exact certificate.aligned (.letBody effects outer)
        ⟨effectsAvoid, outerAvoids⟩ }

/-- A certificate directly preserves and reflects acceptance in every
admissible frame.  Alias addition/removal uses the existing stepwise
freshness theorem; the middle step is the synchronized saturation transport. -/
theorem blockAccepts_iff
    {start next : Supply} {left right : Generated}
    (certificate : EntailedAlignmentCertificate start next left right)
    (frame : GeneratedFrame) (frameAvoids : frame.Avoids certificate.hidden) :
    BlockAccepts (frame.plug left) ↔ BlockAccepts (frame.plug right) := by
  let leftAugmented := FreshAliasSequence.addAll
    certificate.leftAliases (frame.plug left)
  let rightAugmented := FreshAliasSequence.addAll
    certificate.rightAliases (frame.plug right)
  have middle : BlockAccepts leftAugmented ↔ BlockAccepts rightAugmented :=
    BlockAccepts.iff_of_entailedAligned
      (certificate.aligned frame frameAvoids).hardEquivalent
      (certificate.aligned frame frameAvoids).pendingAligned
  exact (FreshAliasSequence.blockAccepts_addAll_iff
      certificate.leftAliases (frame.plug left)
      (certificate.leftAdmissible frame frameAvoids)).symm |>.trans
    (middle.trans
      (FreshAliasSequence.blockAccepts_addAll_iff
        certificate.rightAliases (frame.plug right)
        (certificate.rightAdmissible frame frameAvoids)))

/-- The certificate has exactly the contextual endpoint consumed by M2. -/
noncomputable def directContextual
    {start next : Supply} {left right : Generated}
    (certificate : EntailedAlignmentCertificate start next left right) :
    DirectGeneratedComparisonCertificate.DirectContextualGeneratedComparisonCertificate
      start next left right := by
  refine
    { hidden := certificate.hidden
      hiddenFresh := certificate.hiddenFresh
      normalize := ?_ }
  intro frame frameAvoids
  exact certificate.blockAccepts_iff frame frameAvoids

/-- Source-level construction target for the remaining `letE` induction. -/
def EntailedLetAlignmentHandler : Prop :=
  ∀ {signature : Signature} {context : Context} {value body : Expr}
      {start : Supply} {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      Elaborates signature context (.letE value body) start
          leftGenerated leftNext →
        Elaborates signature context (.letE value body) start
            rightGenerated rightNext →
          leftNext = rightNext ∧
            Nonempty (EntailedAlignmentCertificate start leftNext
              leftGenerated rightGenerated)

/-- Constructing semantic certificates for pairs of `letE` derivations is
enough to discharge the existing general source-composition handler. -/
theorem letComparisonHandler
    (handler : EntailedLetAlignmentHandler) : LetComparisonHandler := by
  intro signature context value body start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  obtain ⟨nextEquality, ⟨certificate⟩⟩ :=
    handler wellFormed leftElaboration rightElaboration
  subst rightNext
  exact certificate.directContextual.scopedGeneratedComparison

end EntailedAlignmentCertificate

/-! ## Support-strengthened certificates

Unlike `EntailedAlignmentCertificate`, the strengthened certificate stores
alias scope at the hole.  Frame admissibility and target invariance then
follow automatically from support monotonicity and frame avoidance. -/

structure SupportedEntailedAlignmentCertificate
    (start next : Supply) (left right : Generated) where
  hidden : List UnificationVar
  hiddenFresh : VariablesFreshIn start next hidden
  leftAliases : List FreshAliasSequence.Alias
  rightAliases : List FreshAliasSequence.Alias
  leftAliasFresh : ∀ alias, alias ∈ leftAliases →
    InterfaceAliasDecomposition.AliasFreshness.freshVariable alias ∈ hidden
  rightAliasFresh : ∀ alias, alias ∈ rightAliases →
    InterfaceAliasDecomposition.AliasFreshness.freshVariable alias ∈ hidden
  leftScoped : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
    left.unificationVars leftAliases
  rightScoped : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
    right.unificationVars rightAliases
  aligned : EntailedGeneratedAlignment
    (FreshAliasSequence.addAll leftAliases left)
    (FreshAliasSequence.addAll rightAliases right)

namespace SupportedEntailedAlignmentCertificate

open InterfaceAliasDecomposition.AliasFreshness
open FreshAliasPrincipalClosure

private theorem targetFixed_of_not_mem
    (alias : FreshAliasSequence.Alias) (body : Generated)
    (absent : freshVariable alias ∉ body.target.unificationVars) :
    TargetFixed alias body := by
  cases alias with
  | ty fresh existing =>
      unfold TargetFixed aliasSubstitution
      calc
        body.target.apply (Subst.singleTy fresh (.var existing)) =
            body.target.apply Subst.id := by
          apply Ty.apply_eq_of_agree body.target
          · intro index member
            have different : index ≠ fresh := by
              intro equality
              subst index
              exact absent ((Ty.mem_tyVars_iff_unificationVars fresh
                body.target).mp member)
            simp [Subst.singleTy, Subst.id, different]
          · intro _index _member
            rfl
        _ = body.target := Ty.apply_id body.target
  | cap fresh existing =>
      unfold TargetFixed aliasSubstitution
      calc
        body.target.apply (Subst.singleCap fresh (.var existing)) =
            body.target.apply Subst.id := by
          apply Ty.apply_eq_of_agree body.target
          · intro _index _member
            rfl
          · intro index member
            have different : index ≠ fresh := by
              intro equality
              subst index
              exact absent ((Ty.mem_capVars_iff_unificationVars fresh
                body.target).mp member)
            simp [Subst.singleCap, Subst.id, different]
        _ = body.target := Ty.apply_id body.target

/-- Hole-level alias scope implies the target-invariance premise required by
principal-closure lifting, at every intermediate alias step. -/
theorem sequenceTargetFixed_of_scopedBy
    {aliases : List FreshAliasSequence.Alias} {body : Generated}
    (scopeProof : ScopedBy body.unificationVars aliases) :
    SequenceTargetFixed aliases body := by
  induction aliases generalizing body with
  | nil => trivial
  | cons alias aliases induction =>
      have endpoints := scopeProof.2 alias (by simp)
      constructor
      · apply targetFixed_of_not_mem alias body
        intro targetMember
        exact endpoints.1 (by
          simp [Generated.unificationVars, targetMember])
      · have tailScope := scopeProof.tail_extended
        apply induction
        refine ⟨tailScope.1, ?_⟩
        intro later laterMember
        have laterEndpoints := tailScope.2 later laterMember
        constructor
        · intro addedMember
          exact laterEndpoints.1
            (alias_add_support_subset alias body
              (fun _ member => member) endpoints.2 _ addedMember)
        · have existingSplit : existingVariable later = freshVariable alias ∨
              existingVariable later ∈ body.unificationVars := by
            simpa only [List.mem_cons] using laterEndpoints.2
          rcases existingSplit with freshMember | originalMember
          · exact (alias_mem_unificationVars_add_iff alias body _).2
              (Or.inl freshMember)
          · exact (alias_mem_unificationVars_add_iff alias body _).2
              (Or.inr (Or.inr originalMember))

private theorem scopedBy_frame
    {aliases : List FreshAliasSequence.Alias} {body : Generated}
    {hidden : List UnificationVar} (scopeProof : ScopedBy body.unificationVars aliases)
    (freshHidden : ∀ alias, alias ∈ aliases → freshVariable alias ∈ hidden)
    (frame : GeneratedFrame) (frameAvoids : frame.Avoids hidden) :
    ScopedBy (frame.plug body).unificationVars aliases := by
  refine ⟨scopeProof.1, ?_⟩
  intro alias aliasMember
  have endpoints := scopeProof.2 alias aliasMember
  constructor
  · intro pluggedMember
    have frameAvoidsOne : frame.Avoids [freshVariable alias] :=
      frameAvoids.antitone (by
        intro candidate candidateMember
        have equality : candidate = freshVariable alias := by
          simpa using candidateMember
        exact equality ▸ freshHidden alias aliasMember)
    have bodyAvoidsOne : GeneratedAvoids [freshVariable alias] body := by
      intro candidate observed forbidden
      have equality : candidate = freshVariable alias := by simpa using forbidden
      subst candidate
      exact endpoints.1 observed
    have pluggedAvoidsOne := GeneratedFrame.plug_avoids
      frameAvoidsOne bodyAvoidsOne
    exact pluggedAvoidsOne (freshVariable alias) pluggedMember (by simp)
  · exact GeneratedFrame.hole_unificationVars_subset frame body _ endpoints.2

/-- The strengthened certificate supplies all frame-wise admissibility and
semantic-alignment fields of the original certificate. -/
def toCertificate
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right) :
    EntailedAlignmentCertificate start next left right :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftAdmissible := by
      intro frame frameAvoids
      exact admissible_of_scopedBy
        (scopedBy_frame certificate.leftScoped certificate.leftAliasFresh
          frame frameAvoids)
        (fun _ member => member)
    rightAdmissible := by
      intro frame frameAvoids
      exact admissible_of_scopedBy
        (scopedBy_frame certificate.rightScoped certificate.rightAliasFresh
          frame frameAvoids)
        (fun _ member => member)
    aligned := by
      intro frame _frameAvoids
      exact (EntailedGeneratedAlignment.addAll_frame_reposition
          certificate.leftAliases frame left).trans
        ((certificate.aligned.frame frame).trans
          (EntailedGeneratedAlignment.addAll_frame_reposition
            certificate.rightAliases frame right).symm) }

theorem leftTargetFixed
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right) :
    SequenceTargetFixed certificate.leftAliases left :=
  sequenceTargetFixed_of_scopedBy certificate.leftScoped

theorem rightTargetFixed
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right) :
    SequenceTargetFixed certificate.rightAliases right :=
  sequenceTargetFixed_of_scopedBy certificate.rightScoped

def refl (start next : Supply) (generated : Generated) :
    SupportedEntailedAlignmentCertificate start next generated generated :=
  { hidden := []
    hiddenFresh := VariablesFreshIn.nil start next
    leftAliases := []
    rightAliases := []
    leftAliasFresh := by simp
    rightAliasFresh := by simp
    leftScoped := by simp [ScopedBy]
    rightScoped := by simp [ScopedBy]
    aligned := EntailedGeneratedAlignment.refl generated }

def rebase
    {start next newStart newNext : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (hiddenFresh : VariablesFreshIn newStart newNext certificate.hidden) :
    SupportedEntailedAlignmentCertificate newStart newNext left right :=
  { certificate with hiddenFresh := hiddenFresh }

def symm
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right) :
    SupportedEntailedAlignmentCertificate start next right left :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.rightAliases
    rightAliases := certificate.leftAliases
    leftAliasFresh := certificate.rightAliasFresh
    rightAliasFresh := certificate.leftAliasFresh
    leftScoped := certificate.rightScoped
    rightScoped := certificate.leftScoped
    aligned := certificate.aligned.symm }

/-- Transitivity when the two augmented presentations of the middle block
use the same alias sequence.  The outward alias scopes remain attached only
to the actual left and right endpoints. -/
def trans
    {start next : Supply} {left middle right : Generated}
    (first : SupportedEntailedAlignmentCertificate start next left middle)
    (second : SupportedEntailedAlignmentCertificate start next middle right)
    (middleAliases : first.rightAliases = second.leftAliases) :
    SupportedEntailedAlignmentCertificate start next left right :=
  { hidden := first.hidden ++ second.hidden
    hiddenFresh := first.hiddenFresh.append second.hiddenFresh
    leftAliases := first.leftAliases
    rightAliases := second.rightAliases
    leftAliasFresh := by
      intro alias member
      exact List.mem_append_left _ (first.leftAliasFresh alias member)
    rightAliasFresh := by
      intro alias member
      exact List.mem_append_right _ (second.rightAliasFresh alias member)
    leftScoped := first.leftScoped
    rightScoped := second.rightScoped
    aligned := first.aligned.trans (by
      rw [middleAliases]
      exact second.aligned) }

/-- Move a supported certificate through any fixed source frame whose fixed
material avoids its hidden alias endpoints. -/
def underFrame
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (frame : GeneratedFrame) (frameAvoids : frame.Avoids certificate.hidden) :
    SupportedEntailedAlignmentCertificate start next
      (frame.plug left) (frame.plug right) :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := scopedBy_frame certificate.leftScoped
      certificate.leftAliasFresh frame frameAvoids
    rightScoped := scopedBy_frame certificate.rightScoped
      certificate.rightAliasFresh frame frameAvoids
    aligned := (EntailedGeneratedAlignment.addAll_frame_reposition
        certificate.leftAliases frame left).trans
      ((certificate.aligned.frame frame).trans
        (EntailedGeneratedAlignment.addAll_frame_reposition
          certificate.rightAliases frame right).symm) }

def lam
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (domain : Ty) (domainAvoids : TypeAvoids certificate.hidden domain) :
    SupportedEntailedAlignmentCertificate start next
      (Generated.fromLam domain left) (Generated.fromLam domain right) :=
  certificate.underFrame (.lam domain .hole) ⟨domainAvoids, trivial⟩

def appFunction
    {start next : Supply} {left right argument : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (domain target : Ty)
    (argumentAvoids : GeneratedAvoids certificate.hidden argument)
    (domainAvoids : TypeAvoids certificate.hidden domain)
    (targetAvoids : TypeAvoids certificate.hidden target) :
    SupportedEntailedAlignmentCertificate start next
      (Generated.fromApp left argument domain target)
      (Generated.fromApp right argument domain target) :=
  certificate.underFrame (.appFunction argument domain target .hole)
    ⟨argumentAvoids, domainAvoids, targetAvoids, trivial⟩

def appArgument
    {start next : Supply} {left right function : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (domain target : Ty)
    (functionAvoids : GeneratedAvoids certificate.hidden function)
    (domainAvoids : TypeAvoids certificate.hidden domain)
    (targetAvoids : TypeAvoids certificate.hidden target) :
    SupportedEntailedAlignmentCertificate start next
      (Generated.fromApp function left domain target)
      (Generated.fromApp function right domain target) :=
  certificate.underFrame (.appArgument function domain target .hole)
    ⟨functionAvoids, domainAvoids, targetAvoids, trivial⟩

/-- Compose independently supported function and argument certificates.
The four sibling-avoidance premises are the exact support facts needed on
the two output sides; disjoint hidden intervals make the concatenated fresh
alias endpoints distinct. -/
def app
    {start next : Supply}
    {leftFunction rightFunction leftArgument rightArgument : Generated}
    (functionCertificate : SupportedEntailedAlignmentCertificate start next
      leftFunction rightFunction)
    (argumentCertificate : SupportedEntailedAlignmentCertificate start next
      leftArgument rightArgument)
    (domain target : Ty)
    (leftArgumentAvoids : GeneratedAvoids
      functionCertificate.hidden leftArgument)
    (rightArgumentAvoids : GeneratedAvoids
      functionCertificate.hidden rightArgument)
    (leftFunctionAvoids : GeneratedAvoids
      argumentCertificate.hidden leftFunction)
    (rightFunctionAvoids : GeneratedAvoids
      argumentCertificate.hidden rightFunction)
    (domainAvoidsFunction : TypeAvoids
      functionCertificate.hidden domain)
    (targetAvoidsFunction : TypeAvoids
      functionCertificate.hidden target)
    (domainAvoidsArgument : TypeAvoids
      argumentCertificate.hidden domain)
    (targetAvoidsArgument : TypeAvoids
      argumentCertificate.hidden target)
    (hiddenDisjoint : ∀ candidate, candidate ∈ functionCertificate.hidden →
      candidate ∉ argumentCertificate.hidden) :
    SupportedEntailedAlignmentCertificate start next
      (Generated.fromApp leftFunction leftArgument domain target)
      (Generated.fromApp rightFunction rightArgument domain target) := by
  let leftFunctionScoped := scopedBy_frame functionCertificate.leftScoped
    functionCertificate.leftAliasFresh
    (.appFunction leftArgument domain target .hole)
    ⟨leftArgumentAvoids, domainAvoidsFunction, targetAvoidsFunction, trivial⟩
  let leftArgumentScoped := scopedBy_frame argumentCertificate.leftScoped
    argumentCertificate.leftAliasFresh
    (.appArgument leftFunction domain target .hole)
    ⟨leftFunctionAvoids, domainAvoidsArgument, targetAvoidsArgument, trivial⟩
  let rightFunctionScoped := scopedBy_frame functionCertificate.rightScoped
    functionCertificate.rightAliasFresh
    (.appFunction rightArgument domain target .hole)
    ⟨rightArgumentAvoids, domainAvoidsFunction, targetAvoidsFunction, trivial⟩
  let rightArgumentScoped := scopedBy_frame argumentCertificate.rightScoped
    argumentCertificate.rightAliasFresh
    (.appArgument rightFunction domain target .hole)
    ⟨rightFunctionAvoids, domainAvoidsArgument, targetAvoidsArgument, trivial⟩
  have leftFreshDisjoint : ∀ candidate,
      candidate ∈ functionCertificate.leftAliases.map freshVariable →
      candidate ∉ argumentCertificate.leftAliases.map freshVariable := by
    intro candidate functionMember argumentMember
    obtain ⟨functionAlias, functionAliasMember, functionEquality⟩ :=
      List.mem_map.mp functionMember
    obtain ⟨argumentAlias, argumentAliasMember, argumentEquality⟩ :=
      List.mem_map.mp argumentMember
    subst candidate
    have equality : freshVariable functionAlias = freshVariable argumentAlias := by
      simpa using argumentEquality.symm
    exact hiddenDisjoint _
      (functionCertificate.leftAliasFresh functionAlias functionAliasMember)
      (equality ▸ argumentCertificate.leftAliasFresh
        argumentAlias argumentAliasMember)
  have rightFreshDisjoint : ∀ candidate,
      candidate ∈ functionCertificate.rightAliases.map freshVariable →
      candidate ∉ argumentCertificate.rightAliases.map freshVariable := by
    intro candidate functionMember argumentMember
    obtain ⟨functionAlias, functionAliasMember, functionEquality⟩ :=
      List.mem_map.mp functionMember
    obtain ⟨argumentAlias, argumentAliasMember, argumentEquality⟩ :=
      List.mem_map.mp argumentMember
    subst candidate
    have equality : freshVariable functionAlias = freshVariable argumentAlias := by
      simpa using argumentEquality.symm
    exact hiddenDisjoint _
      (functionCertificate.rightAliasFresh functionAlias functionAliasMember)
      (equality ▸ argumentCertificate.rightAliasFresh
        argumentAlias argumentAliasMember)
  have leftScoped := ScopedBy.append leftFunctionScoped leftArgumentScoped
    leftFreshDisjoint
  have rightScoped := ScopedBy.append rightFunctionScoped rightArgumentScoped
    rightFreshDisjoint
  have combinedFresh : ∀ alias,
      alias ∈ functionCertificate.leftAliases ++
          argumentCertificate.leftAliases →
        freshVariable alias ∈
          functionCertificate.hidden ++ argumentCertificate.hidden := by
    intro alias member
    rcases List.mem_append.mp member with functionMember | argumentMember
    · exact List.mem_append_left _
        (functionCertificate.leftAliasFresh alias functionMember)
    · exact List.mem_append_right _
        (argumentCertificate.leftAliasFresh alias argumentMember)
  have combinedRightFresh : ∀ alias,
      alias ∈ functionCertificate.rightAliases ++
          argumentCertificate.rightAliases →
        freshVariable alias ∈
          functionCertificate.hidden ++ argumentCertificate.hidden := by
    intro alias member
    rcases List.mem_append.mp member with functionMember | argumentMember
    · exact List.mem_append_left _
        (functionCertificate.rightAliasFresh alias functionMember)
    · exact List.mem_append_right _
        (argumentCertificate.rightAliasFresh alias argumentMember)
  let oldCombined := EntailedAlignmentCertificate.appCombined
    functionCertificate.toCertificate argumentCertificate.toCertificate
    domain target leftArgumentAvoids rightFunctionAvoids
    domainAvoidsFunction targetAvoidsFunction domainAvoidsArgument
    targetAvoidsArgument
    (fun frame frameAvoids => admissible_of_scopedBy
      (scopedBy_frame leftScoped combinedFresh frame frameAvoids)
      (fun _ member => member))
    (fun frame frameAvoids => admissible_of_scopedBy
      (scopedBy_frame rightScoped combinedRightFresh frame frameAvoids)
      (fun _ member => member))
  have oldAligned := oldCombined.aligned .hole trivial
  exact
    { hidden := functionCertificate.hidden ++ argumentCertificate.hidden
      hiddenFresh := functionCertificate.hiddenFresh.append
        argumentCertificate.hiddenFresh
      leftAliases := functionCertificate.leftAliases ++
        argumentCertificate.leftAliases
      rightAliases := functionCertificate.rightAliases ++
        argumentCertificate.rightAliases
      leftAliasFresh := combinedFresh
      rightAliasFresh := combinedRightFresh
      leftScoped := leftScoped
      rightScoped := rightScoped
      aligned := by
        simpa [oldCombined, EntailedAlignmentCertificate.appCombined,
          toCertificate, GeneratedFrame.plug] using oldAligned }

def tupleItem
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (before after : GeneratedItems)
    (beforeAvoids : GeneratedItemsAvoid certificate.hidden before)
    (afterAvoids : GeneratedItemsAvoid certificate.hidden after) :
    SupportedEntailedAlignmentCertificate start next
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append (GeneratedItems.singleton left) after)
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append (GeneratedItems.singleton right) after) :=
  certificate.underFrame (.tupleItem before after .hole)
    ⟨beforeAvoids, afterAvoids, trivial⟩

def letBody
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (effects : List Equation)
    (effectsAvoid : EquationsAvoid certificate.hidden effects) :
    SupportedEntailedAlignmentCertificate start next
      (Generated.fromLet effects left) (Generated.fromLet effects right) :=
  certificate.underFrame (.letBody effects .hole) ⟨effectsAvoid, trivial⟩

/-- The exact source-specific bridge still required at a heterogeneous
`letE`.  It compares the original complete left block directly with the
post-renaming interface-normalized block.  Requiring its right alias list to
match the recursive body certificate avoids the invalid intermediate claim
that an isolated body renaming is contextually harmless. -/
def RenamingEntailedBodyBridge
    {context : Context} {start afterValue bodyFinish : Supply}
    {leftValue rightValue leftBody rightBody : Generated}
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (alignment : FreshClosureAlignment leftClosure rightClosure
      context afterValue)
    (bodyCertificate : SupportedEntailedAlignmentCertificate
      afterValue bodyFinish
      (ElaborationRenaming.renameGenerated alignment.alignment.rho leftBody)
      rightBody) : Prop :=
  ∃ bridge : SupportedEntailedAlignmentCertificate start bodyFinish
      (Generated.fromLet
        (context.interfaceEquations leftClosure.substitution) leftBody)
      (Generated.fromLet
        (context.interfaceEquations rightClosure.substitution)
        (ElaborationRenaming.renameGenerated alignment.alignment.rho leftBody)),
    bridge.rightAliases = bodyCertificate.leftAliases

/-- Conditional outer-`letE` assembly.  All ordinary support and alias
bookkeeping is discharged here; only `RenamingEntailedBodyBridge` remains a
source-structural obligation. -/
theorem wholeLet_of_renamingEntailedBodyBridge
    {context : Context} {start afterValue bodyFinish : Supply}
    {leftValue rightValue leftBody rightBody : Generated}
    (startToAfterValue : start.Le afterValue)
    (leftClosure : PrincipalBlockClosure leftValue)
    (rightClosure : PrincipalBlockClosure rightValue)
    (alignment : FreshClosureAlignment leftClosure rightClosure
      context afterValue)
    (bodyCertificate : SupportedEntailedAlignmentCertificate
      afterValue bodyFinish
      (ElaborationRenaming.renameGenerated alignment.alignment.rho leftBody)
      rightBody)
    (rightEffectsAvoidBodyHidden : EquationsAvoid bodyCertificate.hidden
      (context.interfaceEquations rightClosure.substitution))
    (bridgeProof : RenamingEntailedBodyBridge (start := start)
      leftClosure rightClosure alignment bodyCertificate) :
    Nonempty (SupportedEntailedAlignmentCertificate start bodyFinish
      (Generated.fromLet
        (context.interfaceEquations leftClosure.substitution) leftBody)
      (Generated.fromLet
        (context.interfaceEquations rightClosure.substitution) rightBody)) := by
  obtain ⟨bridge, middleAliases⟩ := bridgeProof
  let bodyUnderLet := bodyCertificate.letBody
    (context.interfaceEquations rightClosure.substitution)
    rightEffectsAvoidBodyHidden
  let bodyAtStart := bodyUnderLet.rebase
    (bodyCertificate.hiddenFresh.widen startToAfterValue
      (Supply.le_refl bodyFinish))
  exact ⟨bridge.trans bodyAtStart middleAliases⟩

/-- Source-induction signature for constructing the remaining bridge.  It
keeps both the original and transported derivations visible, so the proof
may proceed by the source constructors (including a recursive `letE`) while
using the closure interface equations as the common semantic reference. -/
def RenamingEntailedBodyBridgeProperty (expression : Expr) : Prop :=
  ∀ {signature : Signature} {context : Context}
      {start afterValue bodyFinish : Supply}
      {leftValue rightValue leftBody rightBody : Generated}
      (leftClosure : PrincipalBlockClosure leftValue)
      (rightClosure : PrincipalBlockClosure rightValue)
      (alignment : FreshClosureAlignment leftClosure rightClosure
        context afterValue)
      (_leftBodyElaboration : Elaborates signature
        ((context.applyFree leftClosure.substitution).generalize
            leftClosure.target ::
          context.applyFree leftClosure.substitution)
        expression afterValue leftBody bodyFinish)
      (_transportedBodyElaboration : Elaborates signature
        ((context.applyFree rightClosure.substitution).generalize
            rightClosure.target ::
          context.applyFree rightClosure.substitution)
        expression afterValue
        (ElaborationRenaming.renameGenerated alignment.alignment.rho leftBody)
        bodyFinish)
      (bodyCertificate : SupportedEntailedAlignmentCertificate
        afterValue bodyFinish
        (ElaborationRenaming.renameGenerated alignment.alignment.rho leftBody)
        rightBody),
    RenamingEntailedBodyBridge (start := start)
      leftClosure rightClosure alignment bodyCertificate

noncomputable def directContextual
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right) :
    DirectGeneratedComparisonCertificate.DirectContextualGeneratedComparisonCertificate
      start next left right :=
  certificate.toCertificate.directContextual

end SupportedEntailedAlignmentCertificate

/-! ## Support-strengthened generated-item certificates -/

/-- Item-list counterpart of `SupportedEntailedAlignmentCertificate`.
The semantic field is stable under arbitrary fixed item prefixes and
suffixes; this is the flat-list invariant needed by `ElaboratesItems.cons`. -/
structure SupportedItemsAlignmentCertificate
    (start next : Supply) (left right : GeneratedItems) where
  hidden : List UnificationVar
  hiddenFresh : VariablesFreshIn start next hidden
  leftAliases : List FreshAliasSequence.Alias
  rightAliases : List FreshAliasSequence.Alias
  leftAliasFresh : ∀ alias, alias ∈ leftAliases →
    InterfaceAliasDecomposition.AliasFreshness.freshVariable alias ∈ hidden
  rightAliasFresh : ∀ alias, alias ∈ rightAliases →
    InterfaceAliasDecomposition.AliasFreshness.freshVariable alias ∈ hidden
  leftScoped : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
    left.unificationVars leftAliases
  rightScoped : InterfaceAliasDecomposition.AliasFreshness.ScopedBy
    right.unificationVars rightAliases
  aligned : ∀ before after,
    EntailedGeneratedAlignment
      (FreshAliasSequence.addAll leftAliases
        (GeneratedItems.asTuple <| GeneratedItems.append before <|
          GeneratedItems.append left after))
      (FreshAliasSequence.addAll rightAliases
        (GeneratedItems.asTuple <| GeneratedItems.append before <|
          GeneratedItems.append right after))

namespace SupportedItemsAlignmentCertificate

open InterfaceAliasDecomposition.AliasFreshness

def refl (start next : Supply) (items : GeneratedItems) :
    SupportedItemsAlignmentCertificate start next items items :=
  { hidden := []
    hiddenFresh := VariablesFreshIn.nil start next
    leftAliases := []
    rightAliases := []
    leftAliasFresh := by simp
    rightAliasFresh := by simp
    leftScoped := by simp [ScopedBy]
    rightScoped := by simp [ScopedBy]
    aligned := by
      intro before after
      exact EntailedGeneratedAlignment.refl _ }

def rebase
    {start next newStart newNext : Supply} {left right : GeneratedItems}
    (certificate : SupportedItemsAlignmentCertificate start next left right)
    (hiddenFresh : VariablesFreshIn newStart newNext certificate.hidden) :
    SupportedItemsAlignmentCertificate newStart newNext left right :=
  { certificate with hiddenFresh := hiddenFresh }

/-- Forget the list boundary after all items have been accumulated. -/
def itemsTuple
    {start next : Supply} {left right : GeneratedItems}
    (certificate : SupportedItemsAlignmentCertificate start next left right) :
    SupportedEntailedAlignmentCertificate start next
      (GeneratedItems.asTuple left) (GeneratedItems.asTuple right) :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := certificate.leftScoped
    rightScoped := certificate.rightScoped
    aligned := by
      simpa using certificate.aligned GeneratedItems.nil GeneratedItems.nil }

private theorem headScopedInCons
    {aliases : List FreshAliasSequence.Alias} {head : Generated}
    {tail : GeneratedItems} {hidden : List UnificationVar}
    (scopeProof : ScopedBy head.unificationVars aliases)
    (freshHidden : ∀ alias, alias ∈ aliases → freshVariable alias ∈ hidden)
    (tailAvoids : GeneratedItemsAvoid hidden tail) :
    ScopedBy (GeneratedItems.cons head tail).unificationVars aliases := by
  refine ⟨scopeProof.1, ?_⟩
  intro alias aliasMember
  have endpoints := scopeProof.2 alias aliasMember
  constructor
  · intro member
    have appendedMember : freshVariable alias ∈
        (GeneratedItems.append (GeneratedItems.singleton head) tail).unificationVars := by
      simpa using member
    rcases (GeneratedItems.mem_unificationVars_append _ _ _).mp appendedMember with
      headMember | tailMember
    · exact endpoints.1 (by simpa using headMember)
    · exact tailAvoids _ tailMember (freshHidden alias aliasMember)
  · have singletonMember : existingVariable alias ∈
        (GeneratedItems.singleton head).unificationVars := by
      simpa using endpoints.2
    have appendedMember := (GeneratedItems.mem_unificationVars_append
      (existingVariable alias) (GeneratedItems.singleton head) tail).2
        (Or.inl singletonMember)
    simpa using appendedMember

private theorem tailScopedInCons
    {aliases : List FreshAliasSequence.Alias} {head : Generated}
    {tail : GeneratedItems} {hidden : List UnificationVar}
    (scopeProof : ScopedBy tail.unificationVars aliases)
    (freshHidden : ∀ alias, alias ∈ aliases → freshVariable alias ∈ hidden)
    (headAvoids : GeneratedAvoids hidden head) :
    ScopedBy (GeneratedItems.cons head tail).unificationVars aliases := by
  refine ⟨scopeProof.1, ?_⟩
  intro alias aliasMember
  have endpoints := scopeProof.2 alias aliasMember
  constructor
  · intro member
    have appendedMember : freshVariable alias ∈
        (GeneratedItems.append (GeneratedItems.singleton head) tail).unificationVars := by
      simpa using member
    rcases (GeneratedItems.mem_unificationVars_append _ _ _).mp appendedMember with
      headMember | tailMember
    · exact headAvoids _ (by simpa using headMember)
        (freshHidden alias aliasMember)
    · exact endpoints.1 tailMember
  · have appendedMember := (GeneratedItems.mem_unificationVars_append
      (existingVariable alias) (GeneratedItems.singleton head) tail).2
        (Or.inr endpoints.2)
    simpa using appendedMember

/-- Flat `GeneratedItems.cons` composition for independent head and tail
certificates. -/
def itemsCons
    {start next : Supply}
    {leftHead rightHead : Generated} {leftTail rightTail : GeneratedItems}
    (headCertificate : SupportedEntailedAlignmentCertificate start next
      leftHead rightHead)
    (tailCertificate : SupportedItemsAlignmentCertificate start next
      leftTail rightTail)
    (leftTailAvoids : GeneratedItemsAvoid headCertificate.hidden leftTail)
    (rightTailAvoids : GeneratedItemsAvoid headCertificate.hidden rightTail)
    (leftHeadAvoids : GeneratedAvoids tailCertificate.hidden leftHead)
    (rightHeadAvoids : GeneratedAvoids tailCertificate.hidden rightHead)
    (hiddenDisjoint : ∀ candidate, candidate ∈ headCertificate.hidden →
      candidate ∉ tailCertificate.hidden) :
    SupportedItemsAlignmentCertificate start next
      (GeneratedItems.cons leftHead leftTail)
      (GeneratedItems.cons rightHead rightTail) := by
  have leftHeadScoped := headScopedInCons headCertificate.leftScoped
    headCertificate.leftAliasFresh leftTailAvoids
  have leftTailScoped := tailScopedInCons tailCertificate.leftScoped
    tailCertificate.leftAliasFresh leftHeadAvoids
  have rightHeadScoped := headScopedInCons headCertificate.rightScoped
    headCertificate.rightAliasFresh rightTailAvoids
  have rightTailScoped := tailScopedInCons tailCertificate.rightScoped
    tailCertificate.rightAliasFresh rightHeadAvoids
  have leftFreshDisjoint : ∀ candidate,
      candidate ∈ headCertificate.leftAliases.map freshVariable →
      candidate ∉ tailCertificate.leftAliases.map freshVariable := by
    intro candidate headMember tailMember
    obtain ⟨headAlias, headAliasMember, headEquality⟩ := List.mem_map.mp headMember
    obtain ⟨tailAlias, tailAliasMember, tailEquality⟩ := List.mem_map.mp tailMember
    subst candidate
    have equality : freshVariable headAlias = freshVariable tailAlias := by
      simpa using tailEquality.symm
    exact hiddenDisjoint _
      (headCertificate.leftAliasFresh headAlias headAliasMember)
      (equality ▸ tailCertificate.leftAliasFresh tailAlias tailAliasMember)
  have rightFreshDisjoint : ∀ candidate,
      candidate ∈ headCertificate.rightAliases.map freshVariable →
      candidate ∉ tailCertificate.rightAliases.map freshVariable := by
    intro candidate headMember tailMember
    obtain ⟨headAlias, headAliasMember, headEquality⟩ := List.mem_map.mp headMember
    obtain ⟨tailAlias, tailAliasMember, tailEquality⟩ := List.mem_map.mp tailMember
    subst candidate
    have equality : freshVariable headAlias = freshVariable tailAlias := by
      simpa using tailEquality.symm
    exact hiddenDisjoint _
      (headCertificate.rightAliasFresh headAlias headAliasMember)
      (equality ▸ tailCertificate.rightAliasFresh tailAlias tailAliasMember)
  refine
    { hidden := headCertificate.hidden ++ tailCertificate.hidden
      hiddenFresh := headCertificate.hiddenFresh.append tailCertificate.hiddenFresh
      leftAliases := headCertificate.leftAliases ++ tailCertificate.leftAliases
      rightAliases := headCertificate.rightAliases ++ tailCertificate.rightAliases
      leftAliasFresh := ?_
      rightAliasFresh := ?_
      leftScoped := ScopedBy.append leftHeadScoped leftTailScoped leftFreshDisjoint
      rightScoped := ScopedBy.append rightHeadScoped rightTailScoped
        rightFreshDisjoint
      aligned := ?_ }
  · intro alias member
    rcases List.mem_append.mp member with headMember | tailMember
    · exact List.mem_append_left _
        (headCertificate.leftAliasFresh alias headMember)
    · exact List.mem_append_right _
        (tailCertificate.leftAliasFresh alias tailMember)
  · intro alias member
    rcases List.mem_append.mp member with headMember | tailMember
    · exact List.mem_append_left _
        (headCertificate.rightAliasFresh alias headMember)
    · exact List.mem_append_right _
        (tailCertificate.rightAliasFresh alias tailMember)
  · intro before after
    let leftHeadFrame := GeneratedFrame.tupleItem before
      (GeneratedItems.append leftTail after) .hole
    let rightHeadFrame := GeneratedFrame.tupleItem before
      (GeneratedItems.append leftTail after) .hole
    have headBase :=
      (EntailedGeneratedAlignment.addAll_frame_reposition
        headCertificate.leftAliases leftHeadFrame leftHead).trans
      ((headCertificate.aligned.frame leftHeadFrame).trans
        (EntailedGeneratedAlignment.addAll_frame_reposition
          headCertificate.rightAliases rightHeadFrame rightHead).symm)
    have tailBase := tailCertificate.aligned
      (GeneratedItems.append before (GeneratedItems.singleton rightHead)) after
    have headStrong := headBase.addAllBoth tailCertificate.leftAliases
    have tailStrong := tailBase.addAllBoth headCertificate.rightAliases
    have headStrong' := headStrong
    rw [← EntailedAlignmentCertificate.addAll_append,
      ← EntailedAlignmentCertificate.addAll_append] at headStrong'
    have tailStrong' := tailStrong
    rw [← EntailedAlignmentCertificate.addAll_append,
      ← EntailedAlignmentCertificate.addAll_append] at tailStrong'
    have headStrongNormalized : EntailedGeneratedAlignment
        (FreshAliasSequence.addAll
          (headCertificate.leftAliases ++ tailCertificate.leftAliases)
          (GeneratedItems.asTuple <| GeneratedItems.append before <|
            GeneratedItems.append (GeneratedItems.cons leftHead leftTail) after))
        (FreshAliasSequence.addAll
          (headCertificate.rightAliases ++ tailCertificate.leftAliases)
          (GeneratedItems.asTuple <| GeneratedItems.append before <|
            GeneratedItems.append (GeneratedItems.cons rightHead leftTail) after)) := by
      simpa [leftHeadFrame, rightHeadFrame, GeneratedFrame.plug,
        GeneratedItems.append_assoc] using headStrong'
    have tailStrongNormalized : EntailedGeneratedAlignment
        (FreshAliasSequence.addAll
          (tailCertificate.leftAliases ++ headCertificate.rightAliases)
          (GeneratedItems.asTuple <| GeneratedItems.append before <|
            GeneratedItems.append (GeneratedItems.cons rightHead leftTail) after))
        (FreshAliasSequence.addAll
          (tailCertificate.rightAliases ++ headCertificate.rightAliases)
          (GeneratedItems.asTuple <| GeneratedItems.append before <|
            GeneratedItems.append (GeneratedItems.cons rightHead rightTail) after)) := by
      simpa [GeneratedItems.append_assoc] using tailStrong'
    have middleSwap := EntailedGeneratedAlignment.addAll_swap
      headCertificate.rightAliases tailCertificate.leftAliases
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append (GeneratedItems.cons rightHead leftTail) after)
    have rightSwap := EntailedGeneratedAlignment.addAll_swap
      tailCertificate.rightAliases headCertificate.rightAliases
      (GeneratedItems.asTuple <| GeneratedItems.append before <|
        GeneratedItems.append (GeneratedItems.cons rightHead rightTail) after)
    exact headStrongNormalized.trans
      (middleSwap.trans (tailStrongNormalized.trans rightSwap))

end SupportedItemsAlignmentCertificate

/-! ## Positive regression at the source-safe alignment counterexample

The following two blocks are the concrete normal forms of the public
`pendingBlocks_not_renamingAwareDirectCertificate` fixture.  The left
interface contains `inherited = representative`; the right interface only
contains a reflexive equation.  Adding the missing alias on the right makes
the hard solution sets equal and makes the two pending checks equal under
every such solution.
-/

namespace EntailedAlignmentRegression

private def inherited : TyVar := ⟨0⟩
private def representative : TyVar := ⟨3⟩

private def commonHard : List Equation :=
  [.ty (.fn (.var ⟨4⟩) .int)
    (.fn (.var ⟨5⟩) (.var ⟨6⟩))]

def counterexampleLeft : Generated :=
  { target := .var ⟨6⟩
    hard := .ty (.var inherited) (.var representative) :: commonHard
    pending := [⟨.var representative, .var ⟨5⟩⟩] }

def counterexampleRight : Generated :=
  { target := .var ⟨6⟩
    hard := .ty (.var inherited) (.var inherited) :: commonHard
    pending := [⟨.var inherited, .var ⟨5⟩⟩] }

/-- The new relation succeeds on the exact hard/pending shapes that refute
the earlier whole-block bijective-renaming certificate. -/
theorem counterexample_entailedAlignment :
    EntailedGeneratedAlignment counterexampleLeft
      (FreshAliasSequence.addAll
        [.ty representative inherited] counterexampleRight) := by
  refine ⟨?_, EntailedTypeEq.refl _ _, ?_⟩
  · intro substitution
    simp [counterexampleLeft, counterexampleRight, commonHard,
      FreshAliasSequence.addAll, FreshAliasSequence.Alias.add,
      FreshAliasElimination.addTyAlias, Solves, Equation.Holds,
      eq_comm]
  · apply EntailedPendingEq.cons
    · intro substitution solved
      have aliasHolds :
          (Equation.ty (.var inherited) (.var representative)).Holds
            substitution := by
        exact solved _ (by simp [counterexampleLeft])
      simpa [CheckObligation.apply, Ty.apply, Equation.Holds] using aliasHolds.symm
    · exact .nil

end EntailedAlignmentRegression

end TypePM.Source
