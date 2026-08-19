import TypePM.Source.InterfaceAliasDecomposition

/-!
# Reallocating interface aliases across a whole `let`

The pointwise interface comparison records a genuine alias on one side and
a reflexive equation on the other.  In one common coordinate system, aliases
originating on the right may instead be added to the left interface after
reversing their equation.  Aliases originating on the left may be added to
the right unchanged.  Both augmented interfaces then describe the
conjunction of those two interfaces.
-/

namespace TypePM.Source.InterfaceAliasDecomposition

open FreshAliasSequence

namespace EquationLists

/-- Reverse the endpoints of a mixed-sort alias. -/
def flipAlias : Alias → Alias
  | .ty fresh existing => .ty existing fresh
  | .cap fresh existing => .cap existing fresh

/-- Reverse every alias equation without changing list order. -/
def flipAliases (aliases : List Alias) : List Alias :=
  aliases.map flipAlias

@[simp] theorem flipAliases_nil : flipAliases [] = [] := rfl

@[simp] theorem flipAliases_cons (alias : Alias) (aliases : List Alias) :
    flipAliases (alias :: aliases) = flipAlias alias :: flipAliases aliases :=
  rfl

@[simp] theorem flipAliases_append (left right : List Alias) :
    flipAliases (left ++ right) = flipAliases left ++ flipAliases right := by
  simp [flipAliases]

@[simp] theorem aliasEquation_flipAlias (alias : Alias) :
    aliasEquation (flipAlias alias) = (aliasEquation alias).swapSides := by
  cases alias <;> rfl

/-- Adding the same alias prefix respects semantic hard-worklist
equivalence. -/
theorem addAliases_hardEquivalent
    (aliases : List Alias) {left right : List Equation}
    (equivalent : HardEquivalent left right) :
    HardEquivalent (addAliases aliases left) (addAliases aliases right) := by
  rw [addAliases_eq_reverse_map_append,
    addAliases_eq_reverse_map_append]
  exact (HardEquivalent.refl
    (aliases.reverse.map aliasEquation)).append equivalent

/-- Reversing every alias endpoint does not change the represented solution
set, because equality is symmetric. -/
theorem flipAliases_hardEquivalent
    (aliases : List Alias) (equations : List Equation) :
    HardEquivalent (addAliases (flipAliases aliases) equations)
      (addAliases aliases equations) := by
  induction aliases generalizing equations with
  | nil => exact HardEquivalent.refl equations
  | cons alias aliases induction =>
      change HardEquivalent
        (addAliases (flipAliases aliases)
          (aliasEquation (flipAlias alias) :: equations))
        (addAliases aliases (aliasEquation alias :: equations))
      exact
        (induction (aliasEquation (flipAlias alias) :: equations)).trans
          (addAliases_hardEquivalent aliases (by
            simpa only [aliasEquation_flipAlias] using
              (HardEquivalent.cons_swap
                (aliasEquation alias) equations).symm))

/-- The union of two alias presentations over one core is equivalent to
adding both alias sequences once. -/
private theorem combinedAliasPresentations_hardEquivalent
    (leftAliases rightAliases : List Alias) (core : List Equation) :
    HardEquivalent
      (addAliases rightAliases (addAliases leftAliases core))
      (addAliases leftAliases core ++ addAliases rightAliases core) := by
  intro substitution
  simp [addAliases_eq_reverse_map_append,
    and_assoc, and_left_comm, and_comm]

namespace PairwiseAliasShape

/-- Move every alias contributed by the right interface to the left,
reversing its equation.  The resulting worklist has exactly the solutions of
the conjunction of the original left and right interfaces. -/
theorem leftReallocated_hardEquivalent
    {left right : List Equation}
    (shape : PairwiseAliasShape left right) :
    HardEquivalent
      (addAliases
        (flipAliases shape.toEquationCommonCore.rightAliases) left)
      (left ++ right) := by
  let decomposition := shape.toEquationCommonCore
  change HardEquivalent
    (addAliases (flipAliases decomposition.rightAliases) left)
    (left ++ right)
  exact
    (flipAliases_hardEquivalent decomposition.rightAliases left).trans
      ((addAliases_hardEquivalent decomposition.rightAliases
          decomposition.leftEquivalent.symm).trans
        ((combinedAliasPresentations_hardEquivalent
            decomposition.leftAliases decomposition.rightAliases
            decomposition.core).trans
          (decomposition.leftEquivalent.append
            decomposition.rightEquivalent)))

/-- Move every alias contributed by the left interface to the right without
changing its equation.  This is the symmetric complete-interface endpoint. -/
theorem rightReallocated_hardEquivalent
    {left right : List Equation}
    (shape : PairwiseAliasShape left right) :
    HardEquivalent
      (addAliases shape.toEquationCommonCore.leftAliases right)
      (left ++ right) := by
  let decomposition := shape.toEquationCommonCore
  change HardEquivalent (addAliases decomposition.leftAliases right)
    (left ++ right)
  have reordered : HardEquivalent
      (addAliases decomposition.leftAliases
        (addAliases decomposition.rightAliases decomposition.core))
      (addAliases decomposition.leftAliases decomposition.core ++
        addAliases decomposition.rightAliases decomposition.core) := by
    intro substitution
    simp [addAliases_eq_reverse_map_append,
      and_left_comm, and_comm]
  exact
    (addAliases_hardEquivalent decomposition.leftAliases
      decomposition.rightEquivalent.symm).trans
        (reordered.trans
          (decomposition.leftEquivalent.append
            decomposition.rightEquivalent))

end PairwiseAliasShape

end EquationLists

namespace Automatic

open EquationLists

/-- Closure-specific left endpoint in the common coordinate system selected
by the automatic support renaming.  The left interface is deliberately the
renamed one: the pointwise shape contains no information about equations
which merely become equal after that renaming. -/
theorem renamedLeftReallocated_hardEquivalent
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := TypePM.Source.ClosureSupportConstruction.build
      transport context
    let shape := interfaceShape transport leftAbsorbing rightAbsorbing context
    HardEquivalent
      (addAliases
        (flipAliases shape.toEquationCommonCore.rightAliases)
        ((context.interfaceEquations left.substitution).map
          (ElaborationRenaming.renameEquation data.globalRenaming)))
      (((context.interfaceEquations left.substitution).map
          (ElaborationRenaming.renameEquation data.globalRenaming)) ++
        context.interfaceEquations right.substitution) := by
  let data := TypePM.Source.ClosureSupportConstruction.build transport context
  let shape := interfaceShape transport leftAbsorbing rightAbsorbing context
  exact shape.leftReallocated_hardEquivalent

/-- Closure-specific right endpoint in the same common coordinate system. -/
theorem renamedRightReallocated_hardEquivalent
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := TypePM.Source.ClosureSupportConstruction.build
      transport context
    let shape := interfaceShape transport leftAbsorbing rightAbsorbing context
    HardEquivalent
      (addAliases shape.toEquationCommonCore.leftAliases
        (context.interfaceEquations right.substitution))
      (((context.interfaceEquations left.substitution).map
          (ElaborationRenaming.renameEquation data.globalRenaming)) ++
        context.interfaceEquations right.substitution) := by
  let data := TypePM.Source.ClosureSupportConstruction.build transport context
  let shape := interfaceShape transport leftAbsorbing rightAbsorbing context
  exact shape.rightReallocated_hardEquivalent

end Automatic

/-! ## Alias graph of the finite representative transport -/

namespace SupportGraph

open EquationLists
open AliasFreshness

/-- Nontrivial ordinary support edges, oriented with the target name as the
fresh endpoint. -/
def movedTySources {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) : List TyVar :=
  support.ty.source.filter fun source =>
    decide (support.ty.forward source ≠ source)

def movedCapSources {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) : List CapVar :=
  support.cap.source.filter fun source =>
    decide (support.cap.forward source ≠ source)

def leftTyAliases {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) : List Alias :=
  (movedTySources support).map fun source =>
    .ty (support.ty.forward source) source

/-- The same ordinary edges oriented with the source name as the fresh
endpoint. -/
def rightTyAliases {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) : List Alias :=
  (movedTySources support).map fun source =>
    .ty source (support.ty.forward source)

def leftCapAliases {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) : List Alias :=
  (movedCapSources support).map fun source =>
    .cap (support.cap.forward source) source

def rightCapAliases {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) : List Alias :=
  (movedCapSources support).map fun source =>
    .cap source (support.cap.forward source)

def leftAliases {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) : List Alias :=
  leftTyAliases support ++ leftCapAliases support

def rightAliases {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) : List Alias :=
  rightTyAliases support ++ rightCapAliases support

theorem leftTyAlias_mem {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward)
    {source : TyVar} (member : source ∈ support.ty.source)
    (moved : support.ty.forward source ≠ source) :
    Alias.ty (support.ty.forward source) source ∈ leftTyAliases support := by
  exact List.mem_map.mpr ⟨source, by
    simp [movedTySources, member, moved], rfl⟩

theorem rightTyAlias_mem {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward)
    {source : TyVar} (member : source ∈ support.ty.source)
    (moved : support.ty.forward source ≠ source) :
    Alias.ty source (support.ty.forward source) ∈ rightTyAliases support := by
  exact List.mem_map.mpr ⟨source, by
    simp [movedTySources, member, moved], rfl⟩

theorem leftCapAlias_mem {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward)
    {source : CapVar} (member : source ∈ support.cap.source)
    (moved : support.cap.forward source ≠ source) :
    Alias.cap (support.cap.forward source) source ∈ leftCapAliases support := by
  exact List.mem_map.mpr ⟨source, by
    simp [movedCapSources, member, moved], rfl⟩

theorem rightCapAlias_mem {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward)
    {source : CapVar} (member : source ∈ support.cap.source)
    (moved : support.cap.forward source ≠ source) :
    Alias.cap source (support.cap.forward source) ∈ rightCapAliases support := by
  exact List.mem_map.mpr ⟨source, by
    simp [movedCapSources, member, moved], rfl⟩

/-- Every equation contributed by an alias sequence holds under a solution
of the augmented worklist. -/
theorem aliasEquation_holds_of_solves_addAliases
    {aliases : List Alias} {hard : List Equation} {substitution : Subst}
    (solved : Solves substitution (addAliases aliases hard))
    {alias : Alias} (member : alias ∈ aliases) :
    (aliasEquation alias).Holds substitution := by
  rw [addAliases_eq_reverse_map_append] at solved
  have prefixSolved := ((solves_append substitution
    (aliases.reverse.map aliasEquation) hard).mp solved).1
  apply prefixSolved (aliasEquation alias)
  exact List.mem_map.mpr ⟨alias, by simpa using member, rfl⟩

private theorem nodup_map_of_injectiveOn
    {α β : Type} (function : α → β) (items : List α)
    (itemsNodup : items.Nodup)
    (injectiveOn : ∀ {left right}, left ∈ items → right ∈ items →
      function left = function right → left = right) :
    (items.map function).Nodup := by
  induction items with
  | nil => exact .nil
  | cons head tail induction =>
      have split := List.nodup_cons.mp itemsNodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨other, otherMember, equality⟩ := List.mem_map.mp member
        have same := injectiveOn (by simp)
          (List.mem_cons_of_mem _ otherMember) equality.symm
        exact split.1 (same ▸ otherMember)
      · exact induction split.2 (by
          intro left right leftMember rightMember equality
          exact injectiveOn
            (List.mem_cons_of_mem _ leftMember)
            (List.mem_cons_of_mem _ rightMember) equality)

theorem movedTySources_nodup {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) :
    (movedTySources support).Nodup :=
  support.ty.source_nodup.filter _

theorem movedCapSources_nodup {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward) :
    (movedCapSources support).Nodup :=
  support.cap.source_nodup.filter _

theorem movedTySource_facts {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward)
    {source : TyVar} (member : source ∈ movedTySources support) :
    source ∈ support.ty.source ∧ support.ty.forward source ≠ source := by
  simpa [movedTySources] using member

theorem movedCapSource_facts {forward backward : Subst}
    (support : SubstitutionPartialBijection forward backward)
    {source : CapVar} (member : source ∈ movedCapSources support) :
    source ∈ support.cap.source ∧ support.cap.forward source ≠ source := by
  simpa [movedCapSources] using member

/-- A moved source representative cannot also be a target representative.
This uses only absorption and representative transport, not a context
membership assumption. -/
theorem movedTySource_not_target
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) {source : TyVar}
    (sourceMember : source ∈
      (ClosureSupportConstruction.build transport context).support.ty.source)
    (moved : (ClosureSupportConstruction.build transport context).support.ty.forward
      source ≠ source) :
    source ∉
      (ClosureSupportConstruction.build transport context).support.ty.target := by
  intro targetMember
  let data := ClosureSupportConstruction.build transport context
  have leftFixed := BuiltSupport.build_tySource_fixed transport
    leftAbsorbing context source sourceMember
  have rightFixed := BuiltSupport.build_tyTarget_fixed transport
    leftAbsorbing rightAbsorbing context source targetMember
  have factor := congrArg (fun substitution => substitution.ty source)
    transport.1
  change (left.substitution.ty source).apply forward =
    right.substitution.ty source at factor
  have forwardImage := data.support.ty_forward sourceMember
  have imageEquality : data.support.ty.forward source = source := by
    simpa only [leftFixed, rightFixed, Ty.apply, forwardImage, Ty.var.injEq]
      using factor
  exact moved imageEquality

theorem movedCapSource_not_target
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) {source : CapVar}
    (sourceMember : source ∈
      (ClosureSupportConstruction.build transport context).support.cap.source)
    (moved : (ClosureSupportConstruction.build transport context).support.cap.forward
      source ≠ source) :
    source ∉
      (ClosureSupportConstruction.build transport context).support.cap.target := by
  intro targetMember
  let data := ClosureSupportConstruction.build transport context
  have leftFixed := BuiltSupport.build_capSource_fixed transport
    leftAbsorbing context source sourceMember
  have rightFixed := BuiltSupport.build_capTarget_fixed transport
    leftAbsorbing rightAbsorbing context source targetMember
  have factor := congrArg (fun substitution => substitution.cap source)
    transport.1
  change (left.substitution.cap source).apply forward.cap =
    right.substitution.cap source at factor
  have forwardImage := data.support.cap_forward sourceMember
  have imageEquality : data.support.cap.forward source = source := by
    simpa only [leftFixed, rightFixed, Cap.apply, forwardImage, Cap.var.injEq]
      using factor
  exact moved imageEquality

/- The target of a moved support edge is outside the source support. -/
theorem movedTyTarget_not_source
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) {source : TyVar}
    (sourceMember : source ∈
      (ClosureSupportConstruction.build transport context).support.ty.source)
    (moved : (ClosureSupportConstruction.build transport context).support.ty.forward
      source ≠ source) :
    (ClosureSupportConstruction.build transport context).support.ty.forward source ∉
      (ClosureSupportConstruction.build transport context).support.ty.source := by
  intro imageSource
  let data := ClosureSupportConstruction.build transport context
  let image := data.support.ty.forward source
  have imageTarget : image ∈ data.support.ty.target :=
    data.support.ty.forward_mem sourceMember
  have leftFixed := BuiltSupport.build_tySource_fixed transport
    leftAbsorbing context image imageSource
  have rightFixed := BuiltSupport.build_tyTarget_fixed transport
    leftAbsorbing rightAbsorbing context image imageTarget
  have factor := congrArg (fun substitution => substitution.ty image) transport.1
  change (left.substitution.ty image).apply forward =
    right.substitution.ty image at factor
  have forwardImage := data.support.ty_forward imageSource
  have imageFixed : data.support.ty.forward image = image := by
    rw [leftFixed, rightFixed, Ty.apply, forwardImage] at factor
    exact Ty.var.inj factor
  have collision : data.support.ty.forward image =
      data.support.ty.forward source := by simpa [image] using imageFixed
  have same : image = source := by
    calc
      image = data.support.ty.backward (data.support.ty.forward image) :=
        (data.support.ty.backward_forward imageSource).symm
      _ = data.support.ty.backward (data.support.ty.forward source) :=
        congrArg data.support.ty.backward collision
      _ = source := data.support.ty.backward_forward sourceMember
  apply moved
  change image = source
  exact same

theorem movedCapTarget_not_source
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) {source : CapVar}
    (sourceMember : source ∈
      (ClosureSupportConstruction.build transport context).support.cap.source)
    (moved : (ClosureSupportConstruction.build transport context).support.cap.forward
      source ≠ source) :
    (ClosureSupportConstruction.build transport context).support.cap.forward source ∉
      (ClosureSupportConstruction.build transport context).support.cap.source := by
  intro imageSource
  let data := ClosureSupportConstruction.build transport context
  let image := data.support.cap.forward source
  have imageTarget : image ∈ data.support.cap.target :=
    data.support.cap.forward_mem sourceMember
  have leftFixed := BuiltSupport.build_capSource_fixed transport
    leftAbsorbing context image imageSource
  have rightFixed := BuiltSupport.build_capTarget_fixed transport
    leftAbsorbing rightAbsorbing context image imageTarget
  have factor := congrArg (fun substitution => substitution.cap image) transport.1
  change (left.substitution.cap image).apply forward.cap =
    right.substitution.cap image at factor
  have forwardImage := data.support.cap_forward imageSource
  have imageFixed : data.support.cap.forward image = image := by
    rw [leftFixed, rightFixed, Cap.apply, forwardImage] at factor
    exact Cap.var.inj factor
  have collision : data.support.cap.forward image =
      data.support.cap.forward source := by simpa [image] using imageFixed
  have same : image = source := by
    calc
      image = data.support.cap.backward (data.support.cap.forward image) :=
        (data.support.cap.backward_forward imageSource).symm
      _ = data.support.cap.backward (data.support.cap.forward source) :=
        congrArg data.support.cap.backward collision
      _ = source := data.support.cap.backward_forward sourceMember
  apply moved
  change image = source
  exact same

/-- Mixed-sort source support of the left representative. -/
def SourceVariables
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    List UnificationVar :=
  data.support.ty.source.map UnificationVar.ty ++
    data.support.cap.source.map UnificationVar.cap

theorem leftTyScoped
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (SourceVariables data) (leftTyAliases data.support) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (SourceVariables data) (leftTyAliases data.support)
  constructor
  · have images :
        ((movedTySources data.support).map
          (fun source => UnificationVar.ty
            (data.support.ty.forward source))).Nodup := by
      apply nodup_map_of_injectiveOn _ _
        (movedTySources_nodup data.support)
      intro first second firstMember secondMember equality
      injection equality with imageEquality
      have firstSource := (movedTySource_facts data.support firstMember).1
      have secondSource := (movedTySource_facts data.support secondMember).1
      have restored := congrArg data.support.ty.backward imageEquality
      simpa only [data.support.ty.backward_forward firstSource,
        data.support.ty.backward_forward secondSource] using restored
    rw [leftTyAliases, List.map_map]
    change ((movedTySources data.support).map
      (fun source => UnificationVar.ty
        (data.support.ty.forward source))).Nodup
    exact images
  · intro alias aliasMember
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp aliasMember
    have facts := movedTySource_facts data.support sourceMember
    constructor
    · change UnificationVar.ty (data.support.ty.forward source) ∉
        SourceVariables data
      intro combinedMember
      rcases List.mem_append.mp combinedMember with tyMember | capMember
      · obtain ⟨candidate, candidateMember, equality⟩ :=
          List.mem_map.mp tyMember
        have same := UnificationVar.ty.inj equality
        exact movedTyTarget_not_source transport leftAbsorbing
          rightAbsorbing context facts.1 facts.2 (same ▸ candidateMember)
      · obtain ⟨candidate, _, equality⟩ := List.mem_map.mp capMember
        cases equality
    · exact List.mem_append_left _
        (List.mem_map.mpr ⟨source, facts.1, rfl⟩)

theorem rightTyScoped
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (BuiltSupport.TargetVariables data)
      (rightTyAliases data.support) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (BuiltSupport.TargetVariables data)
    (rightTyAliases data.support)
  constructor
  · have sources : ((movedTySources data.support).map
        UnificationVar.ty).Nodup := by
      apply nodup_map_of_injectiveOn _ _
        (movedTySources_nodup data.support)
      intro first second _ _ equality
      exact UnificationVar.ty.inj equality
    rw [rightTyAliases, List.map_map]
    change ((movedTySources data.support).map UnificationVar.ty).Nodup
    exact sources
  · intro alias aliasMember
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp aliasMember
    have facts := movedTySource_facts data.support sourceMember
    constructor
    · change UnificationVar.ty source ∉ BuiltSupport.TargetVariables data
      simpa only [BuiltSupport.ty_mem_targetVariables] using
        movedTySource_not_target transport leftAbsorbing rightAbsorbing
          context facts.1 facts.2
    · exact (BuiltSupport.ty_mem_targetVariables data _).mpr
        (data.support.ty.forward_mem facts.1)

theorem leftCapScoped
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (SourceVariables data) (leftCapAliases data.support) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (SourceVariables data) (leftCapAliases data.support)
  constructor
  · have images :
        ((movedCapSources data.support).map
          (fun source => UnificationVar.cap
            (data.support.cap.forward source))).Nodup := by
      apply nodup_map_of_injectiveOn _ _
        (movedCapSources_nodup data.support)
      intro first second firstMember secondMember equality
      injection equality with imageEquality
      have firstSource := (movedCapSource_facts data.support firstMember).1
      have secondSource := (movedCapSource_facts data.support secondMember).1
      have restored := congrArg data.support.cap.backward imageEquality
      simpa only [data.support.cap.backward_forward firstSource,
        data.support.cap.backward_forward secondSource] using restored
    rw [leftCapAliases, List.map_map]
    change ((movedCapSources data.support).map
      (fun source => UnificationVar.cap
        (data.support.cap.forward source))).Nodup
    exact images
  · intro alias aliasMember
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp aliasMember
    have facts := movedCapSource_facts data.support sourceMember
    constructor
    · change UnificationVar.cap (data.support.cap.forward source) ∉
        SourceVariables data
      intro combinedMember
      rcases List.mem_append.mp combinedMember with tyMember | capMember
      · obtain ⟨candidate, _, equality⟩ := List.mem_map.mp tyMember
        cases equality
      · obtain ⟨candidate, candidateMember, equality⟩ :=
          List.mem_map.mp capMember
        have same := UnificationVar.cap.inj equality
        exact movedCapTarget_not_source transport leftAbsorbing
          rightAbsorbing context facts.1 facts.2 (same ▸ candidateMember)
    · exact List.mem_append_right _
        (List.mem_map.mpr ⟨source, facts.1, rfl⟩)

theorem rightCapScoped
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (BuiltSupport.TargetVariables data)
      (rightCapAliases data.support) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (BuiltSupport.TargetVariables data)
    (rightCapAliases data.support)
  constructor
  · have sources : ((movedCapSources data.support).map
        UnificationVar.cap).Nodup := by
      apply nodup_map_of_injectiveOn _ _
        (movedCapSources_nodup data.support)
      intro first second _ _ equality
      exact UnificationVar.cap.inj equality
    rw [rightCapAliases, List.map_map]
    change ((movedCapSources data.support).map UnificationVar.cap).Nodup
    exact sources
  · intro alias aliasMember
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp aliasMember
    have facts := movedCapSource_facts data.support sourceMember
    constructor
    · change UnificationVar.cap source ∉ BuiltSupport.TargetVariables data
      simpa only [BuiltSupport.cap_mem_targetVariables] using
        movedCapSource_not_target transport leftAbsorbing rightAbsorbing
          context facts.1 facts.2
    · exact (BuiltSupport.cap_mem_targetVariables data _).mpr
        (data.support.cap.forward_mem facts.1)

theorem leftScoped
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (SourceVariables data) (leftAliases data.support) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (SourceVariables data) (leftAliases data.support)
  apply ScopedBy.append
    (leftTyScoped transport leftAbsorbing rightAbsorbing context)
    (leftCapScoped transport leftAbsorbing rightAbsorbing context)
  intro candidate tyMember capMember
  simp [leftTyAliases, leftCapAliases, List.map_map,
    Function.comp_def, AliasFreshness.freshVariable] at tyMember capMember
  obtain ⟨tySource, _, tyEquality⟩ := tyMember
  obtain ⟨capSource, _, capEquality⟩ := capMember
  rw [← tyEquality] at capEquality
  cases capEquality

theorem rightScoped
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport : PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward)
    (leftAbsorbing : left.Absorbing)
    (rightAbsorbing : right.Absorbing)
    (context : Context) :
    let data := ClosureSupportConstruction.build transport context
    ScopedBy (BuiltSupport.TargetVariables data) (rightAliases data.support) := by
  let data := ClosureSupportConstruction.build transport context
  change ScopedBy (BuiltSupport.TargetVariables data) (rightAliases data.support)
  apply ScopedBy.append
    (rightTyScoped transport leftAbsorbing rightAbsorbing context)
    (rightCapScoped transport leftAbsorbing rightAbsorbing context)
  intro candidate tyMember capMember
  simp [rightTyAliases, rightCapAliases, List.map_map,
    Function.comp_def, AliasFreshness.freshVariable] at tyMember capMember
  obtain ⟨tySource, _, tyEquality⟩ := tyMember
  obtain ⟨capSource, _, capEquality⟩ := capMember
  rw [← tyEquality] at capEquality
  cases capEquality

end SupportGraph

end TypePM.Source.InterfaceAliasDecomposition
