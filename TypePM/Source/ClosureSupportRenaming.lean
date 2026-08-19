import TypePM.BlockClosureTransport
import TypePM.GeneralizationTransport
import TypePM.Source.FinitePartialRenaming

/-!
# Global renaming from closure-support bijections

This module connects a finite partial bijection covering the free support of
two closure representatives to exact transport of their closed contexts,
targets, and generalized schemes.
-/

namespace TypePM.Source

private theorem Ty.variableImage_of_roundtrip
    (forward backward : Subst) (needle : TyVar)
    (roundtrip : ((Ty.var needle).apply forward).apply backward =
      .var needle) :
    ∃ image, forward.ty needle = .var image ∧
      backward.ty image = .var needle := by
  cases imageEquality : forward.ty needle with
  | var image =>
      exact ⟨image, rfl, by
        simpa [Ty.apply, imageEquality] using roundtrip⟩
  | int => simp [Ty.apply, imageEquality] at roundtrip
  | fn => simp [Ty.apply, imageEquality] at roundtrip
  | prod => simp [Ty.apply, imageEquality] at roundtrip
  | data => simp [Ty.apply, imageEquality] at roundtrip
  | matcher => simp [Ty.apply, imageEquality] at roundtrip
  | slot => simp [Ty.apply, imageEquality] at roundtrip

private theorem Cap.variableImage_of_roundtrip
    (forward backward : CapSubst) (needle : CapVar)
    (roundtrip : ((Cap.var needle).apply forward).apply backward =
      .var needle) :
    ∃ image, forward needle = .var image ∧
      backward image = .var needle := by
  cases imageEquality : forward needle with
  | any => simp [Cap.apply, imageEquality] at roundtrip
  | var image =>
      exact ⟨image, rfl, by
        simpa [Cap.apply, imageEquality] using roundtrip⟩
  | prod => simp [Cap.apply, imageEquality] at roundtrip
  | con => simp [Cap.apply, imageEquality] at roundtrip

mutual

private theorem Ty.tyImage_of_roundtrip
    (forward backward : Subst) (needle : TyVar) (target : Ty)
    (member : needle ∈ target.tyVars)
    (roundtrip : (target.apply forward).apply backward = target) :
    ∃ image, forward.ty needle = .var image ∧
      backward.ty image = .var needle := by
  cases target with
  | var index =>
      simp [Ty.tyVars] at member
      subst index
      exact Ty.variableImage_of_roundtrip forward backward needle roundtrip
  | int => simp [Ty.tyVars] at member
  | fn domain codomain =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.fn.inj roundtrip
      simp only [Ty.tyVars, List.mem_append] at member
      rcases member with domainMember | codomainMember
      · exact Ty.tyImage_of_roundtrip forward backward needle domain
          domainMember parts.1
      · exact Ty.tyImage_of_roundtrip forward backward needle codomain
          codomainMember parts.2
  | prod items =>
      simp only [Ty.apply] at roundtrip
      exact Ty.tyListImage_of_roundtrip forward backward needle items
        (by simpa [Ty.tyVars] using member) (Ty.prod.inj roundtrip)
  | data former arguments =>
      simp only [Ty.apply] at roundtrip
      exact Ty.tyListImage_of_roundtrip forward backward needle arguments
        (by simpa [Ty.tyVars] using member) (Ty.data.inj roundtrip).2
  | matcher capability target =>
      simp only [Ty.apply] at roundtrip
      exact Ty.tyImage_of_roundtrip forward backward needle target
        (by simpa [Ty.tyVars] using member) (Ty.matcher.inj roundtrip).2
  | slot capability target =>
      simp only [Ty.apply] at roundtrip
      exact Ty.tyImage_of_roundtrip forward backward needle target
        (by simpa [Ty.tyVars] using member) (Ty.slot.inj roundtrip).2

private theorem Ty.tyListImage_of_roundtrip
    (forward backward : Subst) (needle : TyVar) (items : List Ty)
    (member : needle ∈ Ty.tyVarsList items)
    (roundtrip :
      Ty.applyList backward (Ty.applyList forward items) = items) :
    ∃ image, forward.ty needle = .var image ∧
      backward.ty image = .var needle := by
  cases items with
  | nil => simp [Ty.tyVarsList] at member
  | cons item items =>
      simp only [Ty.applyList] at roundtrip
      have parts := List.cons.inj roundtrip
      simp only [Ty.tyVarsList, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact Ty.tyImage_of_roundtrip forward backward needle item
          headMember parts.1
      · exact Ty.tyListImage_of_roundtrip forward backward needle items
          tailMember parts.2

end

private def Scheme.supportWitness (scheme : Scheme) : Ty :=
  scheme.body.openBound (fun _ => .int) (fun _ => .any)

private def Context.supportWitness (context : Context) : Ty :=
  .prod (context.map Scheme.supportWitness)

private def closureSupportWitness
    (context : Context) (target : Ty) : Ty :=
  .prod [context.supportWitness, target]

mutual

private theorem PolyTy.freeTy_mem_supportWitness
    (body : PolyTy) {index : TyVar}
    (member : index ∈ body.freeTyVars) :
    index ∈ (body.openBound (fun _ => .int) (fun _ => .any)).tyVars := by
  cases body with
  | free source => simpa [PolyTy.freeTyVars, PolyTy.openBound, Ty.tyVars] using member
  | bound => simp [PolyTy.freeTyVars] at member
  | int => simp [PolyTy.freeTyVars] at member
  | fn domain codomain =>
      simp only [PolyTy.freeTyVars, List.mem_append] at member
      simp only [PolyTy.openBound, Ty.tyVars, List.mem_append]
      exact member.elim
        (fun found => Or.inl (PolyTy.freeTy_mem_supportWitness domain found))
        (fun found => Or.inr (PolyTy.freeTy_mem_supportWitness codomain found))
  | prod items =>
      simpa [PolyTy.openBound, Ty.tyVars] using
        PolyTy.freeTyList_mem_supportWitness items member
  | data former arguments =>
      simpa [PolyTy.openBound, Ty.tyVars] using
        PolyTy.freeTyList_mem_supportWitness arguments member
  | matcher capability target =>
      simpa [PolyTy.openBound, Ty.tyVars] using
        PolyTy.freeTy_mem_supportWitness target member
  | slot capability target =>
      simpa [PolyTy.openBound, Ty.tyVars] using
        PolyTy.freeTy_mem_supportWitness target member

private theorem PolyTy.freeTyList_mem_supportWitness
    (items : List PolyTy) {index : TyVar}
    (member : index ∈ PolyTy.freeTyVarsList items) :
    index ∈ Ty.tyVarsList (PolyTy.openBoundList (fun _ => .int)
      (fun _ => .any) items) := by
  cases items with
  | nil => simp [PolyTy.freeTyVarsList] at member
  | cons item items =>
      simp only [PolyTy.freeTyVarsList, List.mem_append] at member
      simp only [PolyTy.openBoundList, Ty.tyVarsList, List.mem_append]
      exact member.elim
        (fun found => Or.inl (PolyTy.freeTy_mem_supportWitness item found))
        (fun found => Or.inr (PolyTy.freeTyList_mem_supportWitness items found))

end

mutual

private theorem PolyCap.freeCap_mem_supportWitness
    (body : PolyCap) {index : CapVar}
    (member : index ∈ body.freeCapVars) :
    index ∈ (body.openBound (fun _ => .any)).capVars := by
  cases body with
  | any => simp [PolyCap.freeCapVars] at member
  | free source => simpa [PolyCap.freeCapVars, PolyCap.openBound, Cap.capVars] using member
  | bound => simp [PolyCap.freeCapVars] at member
  | prod items =>
      simpa [PolyCap.openBound, Cap.capVars] using
        PolyCap.freeCapList_mem_supportWitness items member
  | con former arguments =>
      simpa [PolyCap.openBound, Cap.capVars] using
        PolyCap.freeCapList_mem_supportWitness arguments member

private theorem PolyCap.freeCapList_mem_supportWitness
    (items : List PolyCap) {index : CapVar}
    (member : index ∈ PolyCap.freeCapVarsList items) :
    index ∈ Cap.capVarsList
      (PolyCap.openBoundList (fun _ => .any) items) := by
  cases items with
  | nil => simp [PolyCap.freeCapVarsList] at member
  | cons item items =>
      simp only [PolyCap.freeCapVarsList, List.mem_append] at member
      simp only [PolyCap.openBoundList, Cap.capVarsList, List.mem_append]
      exact member.elim
        (fun found => Or.inl (PolyCap.freeCap_mem_supportWitness item found))
        (fun found => Or.inr (PolyCap.freeCapList_mem_supportWitness items found))

end

mutual

private theorem PolyTy.freeCap_mem_supportWitness
    (body : PolyTy) {index : CapVar}
    (member : index ∈ body.freeCapVars) :
    index ∈ (body.openBound (fun _ => .int) (fun _ => .any)).capVars := by
  cases body with
  | free => simp [PolyTy.freeCapVars] at member
  | bound => simp [PolyTy.freeCapVars] at member
  | int => simp [PolyTy.freeCapVars] at member
  | fn domain codomain =>
      simp only [PolyTy.freeCapVars, List.mem_append] at member
      simp only [PolyTy.openBound, Ty.capVars, List.mem_append]
      exact member.elim
        (fun found => Or.inl (PolyTy.freeCap_mem_supportWitness domain found))
        (fun found => Or.inr (PolyTy.freeCap_mem_supportWitness codomain found))
  | prod items =>
      simpa [PolyTy.openBound, Ty.capVars] using
        PolyTy.freeCapList_mem_supportWitness items member
  | data former arguments =>
      simpa [PolyTy.openBound, Ty.capVars] using
        PolyTy.freeCapList_mem_supportWitness arguments member
  | matcher capability target =>
      simp only [PolyTy.freeCapVars, List.mem_append] at member
      simp only [PolyTy.openBound, Ty.capVars, List.mem_append]
      exact member.elim
        (fun found => Or.inl (PolyCap.freeCap_mem_supportWitness capability found))
        (fun found => Or.inr (PolyTy.freeCap_mem_supportWitness target found))
  | slot capability target =>
      simp only [PolyTy.freeCapVars, List.mem_append] at member
      simp only [PolyTy.openBound, Ty.capVars, List.mem_append]
      exact member.elim
        (fun found => Or.inl (PolyCap.freeCap_mem_supportWitness capability found))
        (fun found => Or.inr (PolyTy.freeCap_mem_supportWitness target found))

private theorem PolyTy.freeCapList_mem_supportWitness
    (items : List PolyTy) {index : CapVar}
    (member : index ∈ PolyTy.freeCapVarsList items) :
    index ∈ Ty.capVarsList (PolyTy.openBoundList (fun _ => .int)
      (fun _ => .any) items) := by
  cases items with
  | nil => simp [PolyTy.freeCapVarsList] at member
  | cons item items =>
      simp only [PolyTy.freeCapVarsList, List.mem_append] at member
      simp only [PolyTy.openBoundList, Ty.capVarsList, List.mem_append]
      exact member.elim
        (fun found => Or.inl (PolyTy.freeCap_mem_supportWitness item found))
        (fun found => Or.inr (PolyTy.freeCapList_mem_supportWitness items found))

end

private theorem Scheme.supportWitness_applyFree
    (scheme : Scheme) (substitution : Subst) :
    (scheme.applyFree substitution).supportWitness =
      scheme.supportWitness.apply substitution := by
  exact PolyTy.openBound_applyFree substitution
    (fun _ => .int) (fun _ => .any) scheme.body

private theorem Context.supportWitness_applyFree
    (context : Context) (substitution : Subst) :
    (context.applyFree substitution).supportWitness =
      context.supportWitness.apply substitution := by
  induction context with
  | nil => rfl
  | cons scheme context induction =>
      have tailEquality := Ty.prod.inj induction
      change List.map Scheme.supportWitness
          (List.map (Scheme.applyFree substitution) context) =
        Ty.applyList substitution
          (List.map Scheme.supportWitness context) at tailEquality
      simp only [Context.supportWitness, Context.applyFree, List.map_cons,
        Ty.apply, Ty.applyList, Scheme.supportWitness_applyFree]
      rw [tailEquality]

private theorem Ty.mem_tyVarsList_of_mem
    {item : Ty} {items : List Ty} {index : TyVar}
    (itemMember : item ∈ items) (variableMember : index ∈ item.tyVars) :
    index ∈ Ty.tyVarsList items := by
  induction items with
  | nil => cases itemMember
  | cons head tail induction =>
      simp only [List.mem_cons] at itemMember
      simp only [Ty.tyVarsList, List.mem_append]
      rcases itemMember with equality | tailMember
      · subst head
        exact Or.inl variableMember
      · exact Or.inr (induction tailMember)

private theorem Ty.mem_capVarsList_of_mem
    {item : Ty} {items : List Ty} {index : CapVar}
    (itemMember : item ∈ items) (variableMember : index ∈ item.capVars) :
    index ∈ Ty.capVarsList items := by
  induction items with
  | nil => cases itemMember
  | cons head tail induction =>
      simp only [List.mem_cons] at itemMember
      simp only [Ty.capVarsList, List.mem_append]
      rcases itemMember with equality | tailMember
      · subst head
        exact Or.inl variableMember
      · exact Or.inr (induction tailMember)

private theorem Context.freeTy_mem_supportWitness
    (context : Context) {index : TyVar}
    (member : index ∈ context.freeTyVars) :
    index ∈ context.supportWitness.tyVars := by
  have flatMember := mem_dedupFirst.mp member
  obtain ⟨scheme, schemeMember, freeMember⟩ := List.mem_flatMap.mp flatMember
  simp only [Context.supportWitness, Ty.tyVars]
  apply Ty.mem_tyVarsList_of_mem
    (List.mem_map.mpr ⟨scheme, schemeMember, rfl⟩)
  exact PolyTy.freeTy_mem_supportWitness scheme.body
      (Scheme.mem_freeTyVars.mp freeMember)

private theorem Context.freeCap_mem_supportWitness
    (context : Context) {index : CapVar}
    (member : index ∈ context.freeCapVars) :
    index ∈ context.supportWitness.capVars := by
  have flatMember := mem_dedupFirst.mp member
  obtain ⟨scheme, schemeMember, freeMember⟩ := List.mem_flatMap.mp flatMember
  simp only [Context.supportWitness, Ty.capVars]
  apply Ty.mem_capVarsList_of_mem
    (List.mem_map.mpr ⟨scheme, schemeMember, rfl⟩)
  exact PolyTy.freeCap_mem_supportWitness scheme.body
      (Scheme.mem_freeCapVars.mp freeMember)

mutual

private theorem Cap.capImage_of_roundtrip
    (forward backward : CapSubst) (needle : CapVar) (capability : Cap)
    (member : needle ∈ capability.capVars)
    (roundtrip :
      (capability.apply forward).apply backward = capability) :
    ∃ image, forward needle = .var image ∧
      backward image = .var needle := by
  cases capability with
  | any => simp [Cap.capVars] at member
  | var index =>
      simp [Cap.capVars] at member
      subst index
      exact Cap.variableImage_of_roundtrip forward backward needle roundtrip
  | prod items =>
      simp only [Cap.apply] at roundtrip
      exact Cap.capListImage_of_roundtrip forward backward needle items
        (by simpa [Cap.capVars] using member) (Cap.prod.inj roundtrip)
  | con former arguments =>
      simp only [Cap.apply] at roundtrip
      exact Cap.capListImage_of_roundtrip forward backward needle arguments
        (by simpa [Cap.capVars] using member) (Cap.con.inj roundtrip).2

private theorem Cap.capListImage_of_roundtrip
    (forward backward : CapSubst) (needle : CapVar) (items : List Cap)
    (member : needle ∈ Cap.capVarsList items)
    (roundtrip :
      Cap.applyList backward (Cap.applyList forward items) = items) :
    ∃ image, forward needle = .var image ∧
      backward image = .var needle := by
  cases items with
  | nil => simp [Cap.capVarsList] at member
  | cons item items =>
      simp only [Cap.applyList] at roundtrip
      have parts := List.cons.inj roundtrip
      simp only [Cap.capVarsList, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact Cap.capImage_of_roundtrip forward backward needle item
          headMember parts.1
      · exact Cap.capListImage_of_roundtrip forward backward needle items
          tailMember parts.2

end

mutual

private theorem Ty.capImage_of_roundtrip
    (forward backward : Subst) (needle : CapVar) (target : Ty)
    (member : needle ∈ target.capVars)
    (roundtrip : (target.apply forward).apply backward = target) :
    ∃ image, forward.cap needle = .var image ∧
      backward.cap image = .var needle := by
  cases target with
  | var => simp [Ty.capVars] at member
  | int => simp [Ty.capVars] at member
  | fn domain codomain =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.fn.inj roundtrip
      simp only [Ty.capVars, List.mem_append] at member
      rcases member with domainMember | codomainMember
      · exact Ty.capImage_of_roundtrip forward backward needle domain
          domainMember parts.1
      · exact Ty.capImage_of_roundtrip forward backward needle codomain
          codomainMember parts.2
  | prod items =>
      simp only [Ty.apply] at roundtrip
      exact Ty.capListImage_of_roundtrip forward backward needle items
        (by simpa [Ty.capVars] using member) (Ty.prod.inj roundtrip)
  | data former arguments =>
      simp only [Ty.apply] at roundtrip
      exact Ty.capListImage_of_roundtrip forward backward needle arguments
        (by simpa [Ty.capVars] using member) (Ty.data.inj roundtrip).2
  | matcher capability target =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.matcher.inj roundtrip
      simp only [Ty.capVars, List.mem_append] at member
      rcases member with capabilityMember | targetMember
      · exact Cap.capImage_of_roundtrip forward.cap backward.cap needle
          capability capabilityMember parts.1
      · exact Ty.capImage_of_roundtrip forward backward needle target
          targetMember parts.2
  | slot capability target =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.slot.inj roundtrip
      simp only [Ty.capVars, List.mem_append] at member
      rcases member with capabilityMember | targetMember
      · exact Cap.capImage_of_roundtrip forward.cap backward.cap needle
          capability capabilityMember parts.1
      · exact Ty.capImage_of_roundtrip forward backward needle target
          targetMember parts.2

private theorem Ty.capListImage_of_roundtrip
    (forward backward : Subst) (needle : CapVar) (items : List Ty)
    (member : needle ∈ Ty.capVarsList items)
    (roundtrip :
      Ty.applyList backward (Ty.applyList forward items) = items) :
    ∃ image, forward.cap needle = .var image ∧
      backward.cap image = .var needle := by
  cases items with
  | nil => simp [Ty.capVarsList] at member
  | cons item items =>
      simp only [Ty.applyList] at roundtrip
      have parts := List.cons.inj roundtrip
      simp only [Ty.capVarsList, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact Ty.capImage_of_roundtrip forward backward needle item
          headMember parts.1
      · exact Ty.capListImage_of_roundtrip forward backward needle items
          tailMember parts.2

end

mutual

theorem Cap.apply_eq_of_agree {left right : CapSubst}
    (capability : Cap)
    (agree : ∀ index, index ∈ capability.capVars →
      left index = right index) :
    capability.apply left = capability.apply right := by
  cases capability with
  | any => rfl
  | var index => exact agree index (by simp [Cap.capVars])
  | prod items =>
      exact congrArg Cap.prod
        (Cap.applyList_eq_of_agree items agree)
  | con former arguments =>
      exact congrArg (Cap.con former)
        (Cap.applyList_eq_of_agree arguments agree)

theorem Cap.applyList_eq_of_agree {left right : CapSubst}
    (items : List Cap)
    (agree : ∀ index, index ∈ Cap.capVarsList items →
      left index = right index) :
    Cap.applyList left items = Cap.applyList right items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [Cap.applyList]
      congr 1
      · apply Cap.apply_eq_of_agree item
        intro index member
        exact agree index (by simp [Cap.capVarsList, member])
      · apply Cap.applyList_eq_of_agree items
        intro index member
        exact agree index (by simp [Cap.capVarsList, member])

end

mutual

theorem Ty.apply_eq_of_agree {left right : Subst}
    (target : Ty)
    (tyAgree : ∀ index, index ∈ target.tyVars →
      left.ty index = right.ty index)
    (capAgree : ∀ index, index ∈ target.capVars →
      left.cap index = right.cap index) :
    target.apply left = target.apply right := by
  cases target with
  | var index => exact tyAgree index (by simp [Ty.tyVars])
  | int => rfl
  | fn domain codomain =>
      simp only [Ty.apply]
      congr 1
      · apply Ty.apply_eq_of_agree domain
        · intro index member
          exact tyAgree index (by simp [Ty.tyVars, member])
        · intro index member
          exact capAgree index (by simp [Ty.capVars, member])
      · apply Ty.apply_eq_of_agree codomain
        · intro index member
          exact tyAgree index (by simp [Ty.tyVars, member])
        · intro index member
          exact capAgree index (by simp [Ty.capVars, member])
  | prod items =>
      exact congrArg Ty.prod
        (Ty.applyList_eq_of_agree items tyAgree capAgree)
  | data former arguments =>
      exact congrArg (Ty.data former)
        (Ty.applyList_eq_of_agree arguments tyAgree capAgree)
  | matcher capability target =>
      simp only [Ty.apply]
      congr 1
      · apply Cap.apply_eq_of_agree capability
        intro index member
        exact capAgree index (by simp [Ty.capVars, member])
      · apply Ty.apply_eq_of_agree target
        · intro index member
          exact tyAgree index (by simp [Ty.tyVars, member])
        · intro index member
          exact capAgree index (by simp [Ty.capVars, member])
  | slot capability target =>
      simp only [Ty.apply]
      congr 1
      · apply Cap.apply_eq_of_agree capability
        intro index member
        exact capAgree index (by simp [Ty.capVars, member])
      · apply Ty.apply_eq_of_agree target
        · intro index member
          exact tyAgree index (by simp [Ty.tyVars, member])
        · intro index member
          exact capAgree index (by simp [Ty.capVars, member])

theorem Ty.applyList_eq_of_agree {left right : Subst}
    (items : List Ty)
    (tyAgree : ∀ index, index ∈ Ty.tyVarsList items →
      left.ty index = right.ty index)
    (capAgree : ∀ index, index ∈ Ty.capVarsList items →
      left.cap index = right.cap index) :
    Ty.applyList left items = Ty.applyList right items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp only [Ty.applyList]
      congr 1
      · apply Ty.apply_eq_of_agree item
        · intro index member
          exact tyAgree index (by simp [Ty.tyVarsList, member])
        · intro index member
          exact capAgree index (by simp [Ty.capVarsList, member])
      · apply Ty.applyList_eq_of_agree items
        · intro index member
          exact tyAgree index (by simp [Ty.tyVarsList, member])
        · intro index member
          exact capAgree index (by simp [Ty.capVarsList, member])

end


/-- Finite-support data for a pair of closure representatives.  The four
coverage fields state that the partial bijections contain every free name
observable in the closed context and result type. -/
structure ClosureSupportBijection
    {generated : Generated}
    (left right : PrincipalBlockClosure generated)
    (forward backward : Subst) (context : Context) where
  transport :
    PrincipalBlockClosure.RepresentativeTransportUsing
      left right forward backward
  support : SubstitutionPartialBijection forward backward
  leftTy : ∀ {index},
    index ∈ (context.applyFree left.substitution).freeTyVars →
      index ∈ support.ty.source
  leftCap : ∀ {index},
    index ∈ (context.applyFree left.substitution).freeCapVars →
      index ∈ support.cap.source
  leftTargetTy : ∀ {index}, index ∈ left.target.tyVars →
    index ∈ support.ty.source
  leftTargetCap : ∀ {index}, index ∈ left.target.capVars →
    index ∈ support.cap.source

namespace ClosureSupportBijection

def globalRenaming {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    VariableRenaming := data.support.toVariableRenaming

theorem closedContext_exact {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    (context.applyFree left.substitution).applyFree
        data.globalRenaming.substitution =
      context.applyFree right.substitution := by
  calc
    (context.applyFree left.substitution).applyFree
        data.globalRenaming.substitution =
        (context.applyFree left.substitution).applyFree forward := by
      apply Context.applyFree_eq_of_substitutionsAgree
      constructor
      · intro index member
        exact data.support.substitution_ty_agrees (data.leftTy member)
      · intro index member
        exact data.support.substitution_cap_agrees (data.leftCap member)
    _ = context.applyFree right.substitution :=
      data.transport.context_forward context

theorem target_exact {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    left.target.apply data.globalRenaming.substitution = right.target := by
  calc
    left.target.apply data.globalRenaming.substitution =
        left.target.apply forward := by
      apply Ty.apply_eq_of_agree left.target
      · intro index member
        exact data.support.substitution_ty_agrees
          (data.leftTargetTy member)
      · intro index member
        exact data.support.substitution_cap_agrees
          (data.leftTargetCap member)
    _ = right.target := data.transport.target_forward

/-- Exact transport of the generalized let-bound scheme. -/
theorem generalized_exact {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst} {context : Context}
    (data : ClosureSupportBijection left right forward backward context) :
    ((context.applyFree left.substitution).generalize left.target).applyFree
        data.globalRenaming.substitution =
      (context.applyFree right.substitution).generalize right.target := by
  rw [Context.generalize_variableRenaming_exact]
  rw [data.closedContext_exact, data.target_exact]

end ClosureSupportBijection


namespace ClosureSupportConstruction

private def tyImage (substitution : Subst) (index : TyVar) : TyVar :=
  match substitution.ty index with
  | .var image => image
  | _ => index

private def capImage (substitution : Subst) (index : CapVar) : CapVar :=
  match substitution.cap index with
  | .var image => image
  | _ => index

private theorem nodup_map_of_leftInverse
    { α : Type } [DecidableEq α]
    (items : List α) (forward backward : α → α)
    (nodup : items.Nodup)
    (inverse : ∀ item, item ∈ items →
      backward (forward item) = item) :
    (items.map forward).Nodup := by
  induction items with
  | nil => simp
  | cons item items induction =>
      have fresh := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      apply List.nodup_cons.mpr
      constructor
      · intro membership
        obtain ⟨other, otherMember, equality⟩ := List.mem_map.mp membership
        have restored := congrArg backward equality
        have itemInverse := inverse item (by simp)
        have otherInverse := inverse other
          (List.mem_cons_of_mem _ otherMember)
        rw [itemInverse, otherInverse] at restored
        exact fresh (restored.symm ▸ otherMember)
      · exact induction tailNodup (fun source member =>
          inverse source (List.mem_cons_of_mem _ member))

private def partialOfLeftInverse
    { α : Type } [DecidableEq α]
    (source : List α) (forward backward : α → α)
    (sourceNodup : source.Nodup)
    (inverse : ∀ item, item ∈ source →
      backward (forward item) = item) :
    FinitePartialBijection α :=
  { source := source
    target := source.map forward
    forward := forward
    backward := backward
    source_nodup := sourceNodup
    target_nodup := nodup_map_of_leftInverse source forward backward
      sourceNodup inverse
    forward_mem := fun member => List.mem_map.mpr ⟨_, member, rfl⟩
    backward_mem := fun member => by
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      simpa [inverse source sourceMember] using sourceMember
    backward_forward := fun member => inverse _ member
    forward_backward := fun member => by
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      rw [inverse source sourceMember] }

private theorem observable_forward
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) :
    (closureSupportWitness (context.applyFree left.substitution) left.target).apply
        forward =
      closureSupportWitness (context.applyFree right.substitution) right.target := by
  have contextEquality := transport.context_forward context
  have witnessEquality := Context.supportWitness_applyFree
    (context.applyFree left.substitution) forward
  rw [contextEquality] at witnessEquality
  unfold closureSupportWitness
  simp only [Ty.apply, Ty.applyList]
  rw [← witnessEquality, transport.target_forward]

private theorem observable_backward
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) :
    (closureSupportWitness (context.applyFree right.substitution) right.target).apply
        backward =
      closureSupportWitness (context.applyFree left.substitution) left.target := by
  have contextEquality := transport.context_backward context
  have witnessEquality := Context.supportWitness_applyFree
    (context.applyFree right.substitution) backward
  rw [contextEquality] at witnessEquality
  unfold closureSupportWitness
  simp only [Ty.apply, Ty.applyList]
  rw [← witnessEquality, transport.target_backward]

private theorem ty_source_image
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) {index : TyVar}
    (member : index ∈ dedupFirst
      (closureSupportWitness
        (context.applyFree left.substitution) left.target).tyVars) :
    forward.ty index = .var (tyImage forward index) ∧
      tyImage backward (tyImage forward index) = index ∧
      backward.ty (tyImage forward index) = .var index := by
  let leftObservable := closureSupportWitness
    (context.applyFree left.substitution) left.target
  let rightObservable := closureSupportWitness
    (context.applyFree right.substitution) right.target
  have forwardEquality : leftObservable.apply forward = rightObservable :=
    observable_forward transport context
  have backwardEquality : rightObservable.apply backward = leftObservable :=
    observable_backward transport context
  have roundtrip :
      (leftObservable.apply forward).apply backward = leftObservable := by
    rw [forwardEquality, backwardEquality]
  obtain ⟨image, imageEquality, inverseEquality⟩ :=
    Ty.tyImage_of_roundtrip forward backward index leftObservable
      (mem_dedupFirst.mp member) roundtrip
  have imageDef : tyImage forward index = image := by
    simp [tyImage, imageEquality]
  have inverseDef : tyImage backward image = index := by
    simp [tyImage, inverseEquality]
  subst image
  exact ⟨imageEquality, inverseDef, inverseEquality⟩

private theorem cap_source_image
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) {index : CapVar}
    (member : index ∈ dedupFirst
      (closureSupportWitness
        (context.applyFree left.substitution) left.target).capVars) :
    forward.cap index = .var (capImage forward index) ∧
      capImage backward (capImage forward index) = index ∧
      backward.cap (capImage forward index) = .var index := by
  let leftObservable := closureSupportWitness
    (context.applyFree left.substitution) left.target
  let rightObservable := closureSupportWitness
    (context.applyFree right.substitution) right.target
  have forwardEquality : leftObservable.apply forward = rightObservable :=
    observable_forward transport context
  have backwardEquality : rightObservable.apply backward = leftObservable :=
    observable_backward transport context
  have roundtrip :
      (leftObservable.apply forward).apply backward = leftObservable := by
    rw [forwardEquality, backwardEquality]
  obtain ⟨image, imageEquality, inverseEquality⟩ :=
    Ty.capImage_of_roundtrip forward backward index leftObservable
      (mem_dedupFirst.mp member) roundtrip
  have imageDef : capImage forward index = image := by
    simp [capImage, imageEquality]
  have inverseDef : capImage backward image = index := by
    simp [capImage, inverseEquality]
  subst image
  exact ⟨imageEquality, inverseDef, inverseEquality⟩

/-- Construct all finite support data directly from mutual closure factors. -/
def supportBijection
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) :
    SubstitutionPartialBijection forward backward :=
  let observable := closureSupportWitness
    (context.applyFree left.substitution) left.target
  let tySource := dedupFirst observable.tyVars
  let capSource := dedupFirst observable.capVars
  let tyData := partialOfLeftInverse tySource
    (tyImage forward) (tyImage backward) (dedupFirst_nodup _)
    (fun index member => (ty_source_image transport context member).2.1)
  let capData := partialOfLeftInverse capSource
    (capImage forward) (capImage backward) (dedupFirst_nodup _)
    (fun index member => (cap_source_image transport context member).2.1)
  { ty := tyData
    cap := capData
    ty_forward := by
      dsimp [tyData, partialOfLeftInverse]
      intro index member
      exact (ty_source_image transport context member).1
    ty_backward := fun member => by
      dsimp [tyData, partialOfLeftInverse] at member ⊢
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      have facts := ty_source_image transport context sourceMember
      rw [facts.2.1]
      exact facts.2.2
    cap_forward := by
      dsimp [capData, partialOfLeftInverse]
      intro index member
      exact (cap_source_image transport context member).1
    cap_backward := fun member => by
      dsimp [capData, partialOfLeftInverse] at member ⊢
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      have facts := cap_source_image transport context sourceMember
      rw [facts.2.1]
      exact facts.2.2 }

private theorem contextTy_covered
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) {index : TyVar}
    (member : index ∈ (context.applyFree left.substitution).freeTyVars) :
    index ∈ (supportBijection transport context).ty.source := by
  change index ∈ dedupFirst
    (closureSupportWitness
      (context.applyFree left.substitution) left.target).tyVars
  apply mem_dedupFirst.mpr
  simp only [closureSupportWitness, Ty.tyVars, Ty.tyVarsList,
    List.mem_append]
  exact Or.inl (Context.freeTy_mem_supportWitness _ member)

private theorem contextCap_covered
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) {index : CapVar}
    (member : index ∈ (context.applyFree left.substitution).freeCapVars) :
    index ∈ (supportBijection transport context).cap.source := by
  change index ∈ dedupFirst
    (closureSupportWitness
      (context.applyFree left.substitution) left.target).capVars
  apply mem_dedupFirst.mpr
  simp only [closureSupportWitness, Ty.capVars, Ty.capVarsList,
    List.mem_append]
  exact Or.inl (Context.freeCap_mem_supportWitness _ member)

private theorem targetTy_covered
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) {index : TyVar}
    (member : index ∈ left.target.tyVars) :
    index ∈ (supportBijection transport context).ty.source := by
  change index ∈ dedupFirst
    (closureSupportWitness
      (context.applyFree left.substitution) left.target).tyVars
  apply mem_dedupFirst.mpr
  simp only [closureSupportWitness, Ty.tyVars, Ty.tyVarsList,
    List.mem_append]
  exact Or.inr (Or.inl member)

private theorem targetCap_covered
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) {index : CapVar}
    (member : index ∈ left.target.capVars) :
    index ∈ (supportBijection transport context).cap.source := by
  change index ∈ dedupFirst
    (closureSupportWitness
      (context.applyFree left.substitution) left.target).capVars
  apply mem_dedupFirst.mpr
  simp only [closureSupportWitness, Ty.capVars, Ty.capVarsList,
    List.mem_append]
  exact Or.inr (Or.inl member)

/-- Fully automatic finite-support renaming between two closure
representatives, including exact context, target, and generalization laws. -/
def build
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) :
    ClosureSupportBijection left right forward backward context :=
  { transport := transport
    support := supportBijection transport context
    leftTy := contextTy_covered transport context
    leftCap := contextCap_covered transport context
    leftTargetTy := targetTy_covered transport context
    leftTargetCap := targetCap_covered transport context }

end ClosureSupportConstruction

/-- Public automatic endpoint: mutual closure factors extend to a global
renaming that transports the closed context exactly. -/
theorem PrincipalBlockClosure.RepresentativeTransportUsing.closedContext_globalRenaming
    {generated : Generated}
    {left right : PrincipalBlockClosure generated}
    {forward backward : Subst}
    (transport :
      PrincipalBlockClosure.RepresentativeTransportUsing
        left right forward backward)
    (context : Context) :
    ∃ rho : VariableRenaming,
      (context.applyFree left.substitution).applyFree rho.substitution =
        context.applyFree right.substitution ∧
      left.target.apply rho.substitution = right.target ∧
      ((context.applyFree left.substitution).generalize left.target).applyFree
          rho.substitution =
        (context.applyFree right.substitution).generalize right.target := by
  let data := ClosureSupportConstruction.build transport context
  exact ⟨data.globalRenaming, data.closedContext_exact,
    data.target_exact, data.generalized_exact⟩

end TypePM.Source
