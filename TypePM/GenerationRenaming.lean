import TypePM.SourcePermutation
import TypePM.GenerationFreshness

/-!
# Renaming fresh variables during generation

Generation uses consecutive natural numbers for fresh ordinary type variables.
This module proves that a relational generation derivation can be transported
to another consecutive interval whenever a bijective renaming maps the source
interval pointwise to the target interval.  The final theorem applies this
transport to the finite permutation that exchanges two adjacent sibling
allocation blocks.
-/

namespace TypePM

namespace Context

/-- Rename every ordinary type variable in a monomorphic context. -/
def rename (rho : TyRenaming) (context : Context) : Context :=
  context.map (Ty.rename rho)

theorem getElem?_rename
    {rho : TyRenaming} {context : Context} {position : Nat} {target : Ty}
    (lookup : context[position]? = some target) :
    (context.rename rho)[position]? = some (target.rename rho) := by
  simp [Context.rename, lookup]

end Context

/-- `MapsFreshInterval rho source target width` says that `rho` maps each
name in the half-open interval `[source, source + width)` to the name at the
same offset in `[target, target + width)`. -/
def MapsFreshInterval
    (rho : TyRenaming) (source target width : Nat) : Prop :=
  ∀ offset, offset < width →
    rho ⟨source + offset⟩ = ⟨target + offset⟩

namespace MapsFreshInterval

theorem zero (rho : TyRenaming) (source target : Nat) :
    MapsFreshInterval rho source target 0 := by
  intro offset impossible
  omega

theorem head
    {rho : TyRenaming} {source target width : Nat}
    (mapping : MapsFreshInterval rho source target (width + 1)) :
    rho ⟨source⟩ = ⟨target⟩ := by
  simpa using mapping 0 (by omega)

theorem initial
    {rho : TyRenaming} {source target whole prefixWidth : Nat}
    (mapping : MapsFreshInterval rho source target whole)
    (bounded : prefixWidth ≤ whole) :
    MapsFreshInterval rho source target prefixWidth := by
  intro offset inside
  exact mapping offset (Nat.lt_of_lt_of_le inside bounded)

theorem suffix
    {rho : TyRenaming} {source target whole prefixWidth suffixWidth : Nat}
    (mapping : MapsFreshInterval rho source target whole)
    (bounded : prefixWidth + suffixWidth ≤ whole) :
    MapsFreshInterval rho (source + prefixWidth)
      (target + prefixWidth) suffixWidth := by
  intro offset inside
  have mapped := mapping (prefixWidth + offset) (by omega)
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using mapped

end MapsFreshInterval

mutual

/-- Transport a generation derivation through a renaming that translates its
entire fresh allocation interval. -/
theorem Generates.rename
    {context : Context} {expression : Expr} {source next : Nat}
    {generated : Generated} (rho : TyRenaming) (target : Nat)
    (derivation : Generates context expression source generated next)
    (mapping : MapsFreshInterval rho source target expression.freshCount) :
    Generates (context.rename rho) expression target (generated.rename rho)
      (target + expression.freshCount) := by
  cases derivation with
  | var lookup =>
      simpa [Expr.freshCount, Generated.rename] using
        (Generates.var (Context.getElem?_rename lookup))
  | lit =>
      simpa [Expr.freshCount, Generated.rename, Ty.rename] using
        (Generates.lit (context := context.rename rho) (supply := target))
  | something =>
      have fresh : rho ⟨source⟩ = ⟨target⟩ := by
        simpa using mapping 0 (by simp [Expr.freshCount])
      simpa [Expr.freshCount, Generated.rename, Ty.rename, fresh] using
        (Generates.something (context := context.rename rho) (supply := target))
  | lam bodyDerivation =>
      rename_i body generatedBody
      have bodyNext := Generates.next_eq_start_add_freshCount bodyDerivation
      subst next
      have domain : rho ⟨source⟩ = ⟨target⟩ := by
        simpa using mapping 0 (by simp [Expr.freshCount]; omega)
      have transportedRaw :=
        Generates.rename rho (target + 1) bodyDerivation
          (MapsFreshInterval.suffix mapping (prefixWidth := 1) (by
            simp [Expr.freshCount]))
      simp only [Context.rename, List.map, Ty.rename, domain] at transportedRaw
      simpa [Expr.freshCount, Context.rename, Generated.rename, Ty.rename,
        domain, Nat.add_assoc] using Generates.lam transportedRaw
  | app functionDerivation argumentDerivation =>
      rename_i function argument generatedFunction afterFunction
        generatedArgument afterArgument
      have functionNext :=
        Generates.next_eq_start_add_freshCount functionDerivation
      have argumentNext :=
        Generates.next_eq_start_add_freshCount argumentDerivation
      subst_vars
      have argumentMapping :
          MapsFreshInterval rho (source + function.freshCount)
            (target + function.freshCount) argument.freshCount := by
        apply MapsFreshInterval.suffix mapping
        simp [Expr.freshCount]
      have functionTransport :=
        Generates.rename rho target functionDerivation
          (MapsFreshInterval.initial mapping (by
            simp [Expr.freshCount]
            omega))
      have argumentTransport :=
        Generates.rename rho (target + function.freshCount)
          argumentDerivation argumentMapping
      have domainMap := mapping
        (function.freshCount + argument.freshCount) (by
          simp [Expr.freshCount])
      have targetMap := mapping
        (function.freshCount + argument.freshCount + 1) (by
          simp [Expr.freshCount])
      have domainExact :
          rho ⟨source + function.freshCount + argument.freshCount⟩ =
            ⟨target + function.freshCount + argument.freshCount⟩ := by
        simpa [Nat.add_assoc] using domainMap
      have targetExact :
          rho ⟨source + function.freshCount + argument.freshCount + 1⟩ =
            ⟨target + function.freshCount + argument.freshCount + 1⟩ := by
        simpa [Nat.add_assoc] using targetMap
      have targetNormalized :
          rho ⟨source + (function.freshCount + (argument.freshCount + 1))⟩ =
            ⟨target + (function.freshCount + (argument.freshCount + 1))⟩ := by
        simpa only [Nat.add_assoc] using targetMap
      simpa [Expr.freshCount, Generated.rename, Equation.rename,
        CheckObligation.rename, Ty.rename, List.map_append, domainMap,
        domainExact, targetMap, targetExact, targetNormalized, Nat.add_assoc] using
        Generates.app functionTransport argumentTransport
  | tuple itemsDerivation =>
      have transported :=
        GeneratesItems.rename rho target itemsDerivation mapping
      simpa [Expr.freshCount, Generated.rename, GeneratedItems.rename,
        Ty.rename] using Generates.tuple transported

/-- List counterpart of `Generates.rename`. -/
theorem GeneratesItems.rename
    {context : Context} {expressions : List Expr} {source next : Nat}
    {generated : GeneratedItems} (rho : TyRenaming) (target : Nat)
    (derivation : GeneratesItems context expressions source generated next)
    (mapping : MapsFreshInterval rho source target
      (Expr.freshCountList expressions)) :
    GeneratesItems (context.rename rho) expressions target
      (generated.rename rho) (target + Expr.freshCountList expressions) := by
  cases derivation with
  | nil =>
      simpa [Expr.freshCountList, GeneratedItems.rename] using
        (GeneratesItems.nil (context := context.rename rho) (supply := target))
  | cons itemDerivation itemsDerivation =>
      rename_i item items generatedItem afterItem generatedItems
      have itemNext := Generates.next_eq_start_add_freshCount itemDerivation
      have itemsNext := GeneratesItems.next_eq_start_add_freshCount itemsDerivation
      subst_vars
      have itemsMapping :
          MapsFreshInterval rho (source + item.freshCount)
            (target + item.freshCount) (Expr.freshCountList items) := by
        apply MapsFreshInterval.suffix mapping
        simp [Expr.freshCountList]
      have itemTransport :=
        Generates.rename rho target itemDerivation
          (MapsFreshInterval.initial mapping (by
            simp [Expr.freshCountList]))
      have itemsTransport :=
        GeneratesItems.rename rho (target + item.freshCount)
          itemsDerivation itemsMapping
      simpa [Expr.freshCountList, Generated.rename, GeneratedItems.rename,
        Ty.renameList, List.map_append, Nat.add_assoc] using
        GeneratesItems.cons itemTransport itemsTransport

end

mutual

/-- A renaming that fixes every variable below `bound` fixes every type whose
next-variable index is at most `bound`. -/
theorem Ty.rename_eq_self_of_nextVar_le
    {rho : TyRenaming} {bound : Nat} (target : Ty)
    (fixed : ∀ index, index.index < bound → rho index = index)
    (bounded : target.nextVar ≤ bound) :
    target.rename rho = target := by
  cases target with
  | var index =>
      simp only [Ty.nextVar] at bounded
      simp [Ty.rename, fixed index (by omega)]
  | int => rfl
  | fn domain codomain =>
      simp only [Ty.nextVar, Nat.max_le] at bounded
      simp [Ty.rename,
        Ty.rename_eq_self_of_nextVar_le domain fixed bounded.1,
        Ty.rename_eq_self_of_nextVar_le codomain fixed bounded.2]
  | prod items =>
      exact congrArg Ty.prod
        (Ty.renameList_eq_self_of_nextVarList_le items fixed bounded)
  | matcher capability target =>
      simpa [Ty.rename, Ty.nextVar] using congrArg (Ty.matcher capability)
        (Ty.rename_eq_self_of_nextVar_le target fixed bounded)
  | slot capability target =>
      simpa [Ty.rename, Ty.nextVar] using congrArg (Ty.slot capability)
        (Ty.rename_eq_self_of_nextVar_le target fixed bounded)

/-- List counterpart of `Ty.rename_eq_self_of_nextVar_le`. -/
theorem Ty.renameList_eq_self_of_nextVarList_le
    {rho : TyRenaming} {bound : Nat} (targets : List Ty)
    (fixed : ∀ index, index.index < bound → rho index = index)
    (bounded : Ty.nextVarList targets ≤ bound) :
    Ty.renameList rho targets = targets := by
  cases targets with
  | nil => rfl
  | cons target targets =>
      simp only [Ty.nextVarList, Nat.max_le] at bounded
      simp only [Ty.renameList]
      rw [Ty.rename_eq_self_of_nextVar_le target fixed bounded.1,
        Ty.renameList_eq_self_of_nextVarList_le targets fixed bounded.2]

end


namespace Context

/-- A context lies below the root fresh supply, so exchanging fresh blocks at
or above that supply leaves the context unchanged. -/
theorem rename_swapAdjacentBlocks
    {context : Context} {start leftWidth rightWidth : Nat}
    (bounded : context.nextVar ≤ start) :
    context.rename (TyRenaming.swapAdjacentBlocks start leftWidth rightWidth) =
    context := by
  rw [Context.rename, ← Ty.renameList_eq_map]
  exact Ty.renameList_eq_self_of_nextVarList_le
    (rho := TyRenaming.swapAdjacentBlocks start leftWidth rightWidth)
    (bound := start) context
    (fun _ before => TyRenaming.swapAdjacentBlocks_before before)
    (by simpa [Context.nextVar] using bounded)

end Context

namespace TyRenaming

theorem mapsFreshInterval_swapAdjacentBlocks_left
    (start leftWidth rightWidth : Nat) :
    MapsFreshInterval (swapAdjacentBlocks start leftWidth rightWidth)
      start (start + rightWidth) leftWidth := by
  intro offset inside
  have notBefore : ¬start + offset < start := by omega
  have inLeft : start + offset < start + leftWidth := by omega
  simp [swapAdjacentBlocks, swapAdjacentIndex, notBefore, inLeft]
  omega

theorem mapsFreshInterval_swapAdjacentBlocks_right
    (start leftWidth rightWidth : Nat) :
    MapsFreshInterval (swapAdjacentBlocks start leftWidth rightWidth)
      (start + leftWidth) start rightWidth := by
  intro offset inside
  have notBefore : ¬start + leftWidth + offset < start := by omega
  have notLeft : ¬start + leftWidth + offset < start + leftWidth := by omega
  have inRight :
      start + leftWidth + offset < start + leftWidth + rightWidth := by omega
  simp [swapAdjacentBlocks, swapAdjacentIndex, notBefore, notLeft, inRight]
  omega

end TyRenaming

namespace GeneratedItems

/-- Swapping two already separated generated blocks gives sibling
alpha-equivalent collected output under the same fresh-name exchange. -/
theorem siblingAlphaEq_swap_pair
    (start : Nat) (left right : Generated)
    (leftWidth rightWidth : Nat) :
    SiblingAlphaEq (collect [left, right])
      (collect [
        right.rename
          (TyRenaming.swapAdjacentBlocks start leftWidth rightWidth),
        left.rename
          (TyRenaming.swapAdjacentBlocks start leftWidth rightWidth)]) := by
  let rho := TyRenaming.swapAdjacentBlocks start leftWidth rightWidth
  refine ⟨rho, TyRenaming.finiteSupport_swapAdjacentBlocks _ _ _, ?_, ?_, ?_⟩
  · change
      [left.target.rename rho, right.target.rename rho].Perm
        [right.target.rename rho, left.target.rename rho]
    exact List.Perm.swap _ _ []
  · change
      (GeneratedItems.rename rho (GeneratedItems.collect [left, right])).hard.Perm
        (GeneratedItems.collect [right.rename rho, left.rename rho]).hard
    simpa [GeneratedItems.collect, GeneratedItems.rename, Generated.rename,
      List.map_append] using
      (List.perm_append_comm :
        ((left.hard.map (Equation.rename rho)) ++
          (right.hard.map (Equation.rename rho))).Perm _)
  · change
      (GeneratedItems.rename rho (GeneratedItems.collect [left, right])).pending.Perm
        (GeneratedItems.collect [right.rename rho, left.rename rho]).pending
    simpa [GeneratedItems.collect, GeneratedItems.rename, Generated.rename,
      List.map_append] using
      (List.perm_append_comm :
        ((left.pending.map (CheckObligation.rename rho)) ++
          (right.pending.map (CheckObligation.rename rho))).Perm _)

end GeneratedItems

namespace GeneratesItems

/-- Administrative left-to-right generation of two siblings is invariant,
up to finite fresh-name renaming and worklist permutation, when their two
allocation blocks are exchanged.  This theorem concerns the generator only;
it does not assert invariance for arbitrary source AST permutations. -/
theorem swapAdjacentPair
    {context : Context} {left right : Expr}
    {supply afterLeft next : Nat}
    {generatedLeft generatedRight : Generated}
    (contextBound : context.nextVar ≤ supply)
    (leftDerivation :
      Generates context left supply generatedLeft afterLeft)
    (rightDerivation :
      Generates context right afterLeft generatedRight next) :
    ∃ swapped : GeneratedItems,
      GeneratesItems context [right, left] supply swapped next ∧
        GeneratedItems.SiblingAlphaEq
          (GeneratedItems.collect [generatedLeft, generatedRight]) swapped := by
  have leftNext := Generates.next_eq_start_add_freshCount leftDerivation
  have rightNext := Generates.next_eq_start_add_freshCount rightDerivation
  subst_vars
  let rho := TyRenaming.swapAdjacentBlocks supply
    left.freshCount right.freshCount
  have contextFixed : context.rename rho = context := by
    exact Context.rename_swapAdjacentBlocks contextBound
  have rightTransportRaw := Generates.rename rho supply rightDerivation
    (TyRenaming.mapsFreshInterval_swapAdjacentBlocks_right
      supply left.freshCount right.freshCount)
  have leftTransportRaw := Generates.rename rho
    (supply + right.freshCount) leftDerivation
    (TyRenaming.mapsFreshInterval_swapAdjacentBlocks_left
      supply left.freshCount right.freshCount)
  rw [contextFixed] at rightTransportRaw leftTransportRaw
  have swappedDerivation :
      GeneratesItems context [right, left] supply
        (GeneratedItems.collect
          [generatedRight.rename rho, generatedLeft.rename rho])
        (supply + left.freshCount + right.freshCount) := by
    have tail : GeneratesItems context [left]
        (supply + right.freshCount)
        (GeneratedItems.collect [generatedLeft.rename rho])
        (supply + right.freshCount + left.freshCount) := by
      simpa [GeneratedItems.collect, Nat.add_assoc] using
        GeneratesItems.cons leftTransportRaw
          (GeneratesItems.nil
            (context := context)
            (supply := supply + right.freshCount + left.freshCount))
    have whole := GeneratesItems.cons rightTransportRaw tail
    simpa [GeneratedItems.collect, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using whole
  refine ⟨GeneratedItems.collect
      [generatedRight.rename rho, generatedLeft.rename rho],
    swappedDerivation, ?_⟩
  exact GeneratedItems.siblingAlphaEq_swap_pair supply
    generatedLeft generatedRight left.freshCount right.freshCount

end GeneratesItems

end TypePM
