import TypePM.Principality

/-!
# Uniqueness of principal targets up to finite renaming

Mutual instancehood alone is stated using arbitrary substitutions.  On a
finite type, however, substitutions witnessing both directions cannot replace
an occurring variable by a proper type constructor: applying the reverse
substitution would then be unable to recover the variable.  This file makes
that observation precise for both ordinary type variables and capability
variables.

The resulting notion is deliberately support-local.  A type contains only
finitely many variables, so values of the two substitutions outside the
variables occurring in the two compared types are irrelevant.  On the finite
supports, the substitutions map variables to variables and are mutually
inverse.  This is exactly the finite-renaming content needed by the analogue
of Theorem 5.4, without imposing an unnecessary global permutation on all
natural-numbered variables.
-/

namespace TypePM

mutual

/-- A capability variable occurs in a capability. -/
def CapVarOccursCap (needle : CapVar) : Cap → Prop
  | .any => False
  | .var index => needle = index
  | .prod items => CapVarOccursCapList needle items

/-- Occurrence of a capability variable in a list of capabilities. -/
def CapVarOccursCapList (needle : CapVar) : List Cap → Prop
  | [] => False
  | item :: items =>
      CapVarOccursCap needle item ∨ CapVarOccursCapList needle items

end


mutual

/-- A capability variable occurs anywhere inside a type. -/
def CapVarOccursTy (needle : CapVar) : Ty → Prop
  | .var _ => False
  | .int => False
  | .fn domain codomain =>
      CapVarOccursTy needle domain ∨ CapVarOccursTy needle codomain
  | .prod items => CapVarOccursTyList needle items
  | .matcher capability target =>
      CapVarOccursCap needle capability ∨ CapVarOccursTy needle target
  | .slot capability target =>
      CapVarOccursCap needle capability ∨ CapVarOccursTy needle target

/-- Occurrence of a capability variable in a list of types. -/
def CapVarOccursTyList (needle : CapVar) : List Ty → Prop
  | [] => False
  | item :: items =>
      CapVarOccursTy needle item ∨ CapVarOccursTyList needle items

end

/- Applying a substitution carries an occurring ordinary variable to every
variable appearing as its image.  We only need the variable-image case. -/
mutual

private theorem tyVarOccurs_apply_of_eq_var
    (substitution : Subst) {source image : TyVar} {target : Ty}
    (occurs : TyVarOccurs source target)
    (image_eq : substitution.ty source = .var image) :
    TyVarOccurs image (target.apply substitution) := by
  cases occurs with
  | var =>
      simpa [Ty.apply, image_eq] using (TyVarOccurs.var (needle := image))
  | fnDomain domainOccurs =>
      exact TyVarOccurs.fnDomain
        (tyVarOccurs_apply_of_eq_var substitution domainOccurs image_eq)
  | fnCodomain codomainOccurs =>
      exact TyVarOccurs.fnCodomain
        (tyVarOccurs_apply_of_eq_var substitution codomainOccurs image_eq)
  | prod listOccurs =>
      exact TyVarOccurs.prod
        (tyVarOccursList_apply_of_eq_var substitution listOccurs image_eq)
  | matcher targetOccurs =>
      exact TyVarOccurs.matcher
        (tyVarOccurs_apply_of_eq_var substitution targetOccurs image_eq)
  | slot targetOccurs =>
      exact TyVarOccurs.slot
        (tyVarOccurs_apply_of_eq_var substitution targetOccurs image_eq)

private theorem tyVarOccursList_apply_of_eq_var
    (substitution : Subst) {source image : TyVar} {items : List Ty}
    (occurs : TyVarOccursList source items)
    (image_eq : substitution.ty source = .var image) :
    TyVarOccursList image (Ty.applyList substitution items) := by
  cases occurs with
  | head itemOccurs =>
      exact TyVarOccursList.head
        (tyVarOccurs_apply_of_eq_var substitution itemOccurs image_eq)
  | tail itemsOccurs =>
      exact TyVarOccursList.tail
        (tyVarOccursList_apply_of_eq_var substitution itemsOccurs image_eq)

end

mutual

private theorem capVarOccursCap_apply_of_eq_var
    (substitution : CapSubst) {source image : CapVar} {capability : Cap}
    (occurs : CapVarOccursCap source capability)
    (image_eq : substitution source = .var image) :
    CapVarOccursCap image (capability.apply substitution) := by
  cases capability with
  | any => exact False.elim occurs
  | var index =>
      have source_eq : source = index := occurs
      subst index
      simp [Cap.apply, image_eq, CapVarOccursCap]
  | prod items =>
      exact capVarOccursCapList_apply_of_eq_var substitution occurs image_eq

private theorem capVarOccursCapList_apply_of_eq_var
    (substitution : CapSubst) {source image : CapVar} {items : List Cap}
    (occurs : CapVarOccursCapList source items)
    (image_eq : substitution source = .var image) :
    CapVarOccursCapList image (Cap.applyList substitution items) := by
  cases items with
  | nil => exact False.elim occurs
  | cons item items =>
      rcases occurs with itemOccurs | itemsOccurs
      · exact Or.inl
          (capVarOccursCap_apply_of_eq_var substitution itemOccurs image_eq)
      · exact Or.inr
          (capVarOccursCapList_apply_of_eq_var substitution itemsOccurs image_eq)

end

mutual

private theorem capVarOccursTy_apply_of_eq_var
    (substitution : Subst) {source image : CapVar} {target : Ty}
    (occurs : CapVarOccursTy source target)
    (image_eq : substitution.cap source = .var image) :
    CapVarOccursTy image (target.apply substitution) := by
  cases target with
  | var index => exact False.elim occurs
  | int => exact False.elim occurs
  | fn domain codomain =>
      rcases occurs with domainOccurs | codomainOccurs
      · exact Or.inl
          (capVarOccursTy_apply_of_eq_var substitution domainOccurs image_eq)
      · exact Or.inr
          (capVarOccursTy_apply_of_eq_var substitution codomainOccurs image_eq)
  | prod items =>
      exact capVarOccursTyList_apply_of_eq_var substitution occurs image_eq
  | matcher capability target =>
      rcases occurs with capabilityOccurs | targetOccurs
      · exact Or.inl
          (capVarOccursCap_apply_of_eq_var substitution.cap capabilityOccurs
            image_eq)
      · exact Or.inr
          (capVarOccursTy_apply_of_eq_var substitution targetOccurs image_eq)
  | slot capability target =>
      rcases occurs with capabilityOccurs | targetOccurs
      · exact Or.inl
          (capVarOccursCap_apply_of_eq_var substitution.cap capabilityOccurs
            image_eq)
      · exact Or.inr
          (capVarOccursTy_apply_of_eq_var substitution targetOccurs image_eq)

private theorem capVarOccursTyList_apply_of_eq_var
    (substitution : Subst) {source image : CapVar} {items : List Ty}
    (occurs : CapVarOccursTyList source items)
    (image_eq : substitution.cap source = .var image) :
    CapVarOccursTyList image (Ty.applyList substitution items) := by
  cases items with
  | nil => exact False.elim occurs
  | cons item items =>
      rcases occurs with itemOccurs | itemsOccurs
      · exact Or.inl
          (capVarOccursTy_apply_of_eq_var substitution itemOccurs image_eq)
      · exact Or.inr
          (capVarOccursTyList_apply_of_eq_var substitution itemsOccurs image_eq)

end

/-- If applying a substitution produces a type variable, the original type
was itself a type variable. -/
private theorem Ty.eq_var_of_apply_eq_var
    {target : Ty} {substitution : Subst} {index : TyVar}
    (equation : target.apply substitution = .var index) :
    ∃ source, target = .var source ∧ substitution.ty source = .var index := by
  cases target with
  | var source =>
      exact ⟨source, rfl, equation⟩
  | int => cases equation
  | fn domain codomain => cases equation
  | prod items => cases equation
  | matcher capability target => cases equation
  | slot capability target => cases equation

/-- Capability counterpart of `Ty.eq_var_of_apply_eq_var`. -/
private theorem Cap.eq_var_of_apply_eq_var
    {capability : Cap} {substitution : CapSubst} {index : CapVar}
    (equation : capability.apply substitution = .var index) :
    ∃ source,
      capability = .var source ∧ substitution source = .var index := by
  cases capability with
  | any => cases equation
  | var source =>
      exact ⟨source, rfl, equation⟩
  | prod items => cases equation

mutual

/-- A round trip on a type forces the forward image of every occurring type
variable to be a variable, with the reverse image returning to the source. -/
private theorem tyVar_image_of_roundtrip
    (forward backward : Subst) (needle : TyVar) (target : Ty)
    (occurs : TyVarOccurs needle target)
    (roundtrip : (target.apply forward).apply backward = target) :
    ∃ image,
      forward.ty needle = .var image ∧
        backward.ty image = .var needle := by
  cases target with
  | var index =>
      cases occurs
      exact Ty.eq_var_of_apply_eq_var roundtrip
  | int => cases occurs
  | fn domain codomain =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.fn.inj roundtrip
      cases occurs with
      | fnDomain domainOccurs =>
          exact tyVar_image_of_roundtrip forward backward needle domain
            domainOccurs parts.1
      | fnCodomain codomainOccurs =>
          exact tyVar_image_of_roundtrip forward backward needle codomain
            codomainOccurs parts.2
  | prod items =>
      simp only [Ty.apply] at roundtrip
      have listRoundtrip := Ty.prod.inj roundtrip
      cases occurs with
      | prod listOccurs =>
          exact tyVarList_image_of_roundtrip forward backward needle items
            listOccurs listRoundtrip
  | matcher capability target =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.matcher.inj roundtrip
      cases occurs with
      | matcher targetOccurs =>
          exact tyVar_image_of_roundtrip forward backward needle target
            targetOccurs parts.2
  | slot capability target =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.slot.inj roundtrip
      cases occurs with
      | slot targetOccurs =>
          exact tyVar_image_of_roundtrip forward backward needle target
            targetOccurs parts.2

/-- List counterpart of `tyVar_image_of_roundtrip`. -/
private theorem tyVarList_image_of_roundtrip
    (forward backward : Subst) (needle : TyVar) (items : List Ty)
    (occurs : TyVarOccursList needle items)
    (roundtrip :
      Ty.applyList backward (Ty.applyList forward items) = items) :
    ∃ image,
      forward.ty needle = .var image ∧
        backward.ty image = .var needle := by
  cases items with
  | nil => cases occurs
  | cons item items =>
      simp only [Ty.applyList] at roundtrip
      have parts := List.cons.inj roundtrip
      cases occurs with
      | head itemOccurs =>
          exact tyVar_image_of_roundtrip forward backward needle item
            itemOccurs parts.1
      | tail itemsOccurs =>
          exact tyVarList_image_of_roundtrip forward backward needle items
            itemsOccurs parts.2

end


mutual

/-- Round-trip lemma for a capability variable occurring in a capability. -/
private theorem capVarCap_image_of_roundtrip
    (forward backward : CapSubst) (needle : CapVar) (capability : Cap)
    (occurs : CapVarOccursCap needle capability)
    (roundtrip :
      (capability.apply forward).apply backward = capability) :
    ∃ image,
      forward needle = .var image ∧ backward image = .var needle := by
  cases capability with
  | any => exact False.elim occurs
  | var index =>
      have needle_eq : needle = index := occurs
      subst index
      exact Cap.eq_var_of_apply_eq_var roundtrip
  | prod items =>
      simp only [Cap.apply] at roundtrip
      have listRoundtrip := Cap.prod.inj roundtrip
      exact capVarCapList_image_of_roundtrip forward backward needle items
        occurs listRoundtrip

/-- List counterpart of `capVarCap_image_of_roundtrip`. -/
private theorem capVarCapList_image_of_roundtrip
    (forward backward : CapSubst) (needle : CapVar) (items : List Cap)
    (occurs : CapVarOccursCapList needle items)
    (roundtrip :
      Cap.applyList backward (Cap.applyList forward items) = items) :
    ∃ image,
      forward needle = .var image ∧ backward image = .var needle := by
  cases items with
  | nil => exact False.elim occurs
  | cons item items =>
      simp only [Cap.applyList] at roundtrip
      have parts := List.cons.inj roundtrip
      rcases occurs with itemOccurs | itemsOccurs
      · exact capVarCap_image_of_roundtrip forward backward needle item
          itemOccurs parts.1
      · exact capVarCapList_image_of_roundtrip forward backward needle items
          itemsOccurs parts.2

end

mutual

/-- A round trip on a type forces the forward image of every occurring
capability variable to be a capability variable, with the reverse image
returning to the source. -/
private theorem capVarTy_image_of_roundtrip
    (forward backward : Subst) (needle : CapVar) (target : Ty)
    (occurs : CapVarOccursTy needle target)
    (roundtrip : (target.apply forward).apply backward = target) :
    ∃ image,
      forward.cap needle = .var image ∧
        backward.cap image = .var needle := by
  cases target with
  | var index => exact False.elim occurs
  | int => exact False.elim occurs
  | fn domain codomain =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.fn.inj roundtrip
      rcases occurs with domainOccurs | codomainOccurs
      · exact capVarTy_image_of_roundtrip forward backward needle domain
          domainOccurs parts.1
      · exact capVarTy_image_of_roundtrip forward backward needle codomain
          codomainOccurs parts.2
  | prod items =>
      simp only [Ty.apply] at roundtrip
      have listRoundtrip := Ty.prod.inj roundtrip
      exact capVarTyList_image_of_roundtrip forward backward needle items
        occurs listRoundtrip
  | matcher capability target =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.matcher.inj roundtrip
      rcases occurs with capabilityOccurs | targetOccurs
      · exact capVarCap_image_of_roundtrip forward.cap backward.cap needle
          capability capabilityOccurs parts.1
      · exact capVarTy_image_of_roundtrip forward backward needle target
          targetOccurs parts.2
  | slot capability target =>
      simp only [Ty.apply] at roundtrip
      have parts := Ty.slot.inj roundtrip
      rcases occurs with capabilityOccurs | targetOccurs
      · exact capVarCap_image_of_roundtrip forward.cap backward.cap needle
          capability capabilityOccurs parts.1
      · exact capVarTy_image_of_roundtrip forward backward needle target
          targetOccurs parts.2

/-- List counterpart of `capVarTy_image_of_roundtrip`. -/
private theorem capVarTyList_image_of_roundtrip
    (forward backward : Subst) (needle : CapVar) (items : List Ty)
    (occurs : CapVarOccursTyList needle items)
    (roundtrip :
      Ty.applyList backward (Ty.applyList forward items) = items) :
    ∃ image,
      forward.cap needle = .var image ∧
        backward.cap image = .var needle := by
  cases items with
  | nil => exact False.elim occurs
  | cons item items =>
      simp only [Ty.applyList] at roundtrip
      have parts := List.cons.inj roundtrip
      rcases occurs with itemOccurs | itemsOccurs
      · exact capVarTy_image_of_roundtrip forward backward needle item
          itemOccurs parts.1
      · exact capVarTyList_image_of_roundtrip forward backward needle items
          itemsOccurs parts.2

end

/-- Two types differ only by a finite renaming when there are substitutions
in both directions which produce the types and act as mutually inverse
variable maps on every variable occurring in either finite type.

No restriction is imposed outside those finite supports. -/
def FiniteRenamingEq (left right : Ty) : Prop :=
  ∃ forward backward : Subst,
    left.apply forward = right ∧
    right.apply backward = left ∧
    (∀ sourceVar, TyVarOccurs sourceVar left →
      ∃ image,
        TyVarOccurs image right ∧
        forward.ty sourceVar = .var image ∧
          backward.ty image = .var sourceVar) ∧
    (∀ sourceVar, TyVarOccurs sourceVar right →
      ∃ image,
        TyVarOccurs image left ∧
        backward.ty sourceVar = .var image ∧
          forward.ty image = .var sourceVar) ∧
    (∀ sourceVar, CapVarOccursTy sourceVar left →
      ∃ image,
        CapVarOccursTy image right ∧
        forward.cap sourceVar = .var image ∧
          backward.cap image = .var sourceVar) ∧
    (∀ sourceVar, CapVarOccursTy sourceVar right →
      ∃ image,
        CapVarOccursTy image left ∧
        backward.cap sourceVar = .var image ∧
          forward.cap image = .var sourceVar)

/-- Mutual instancehood of finite M1 types is exactly strong enough to yield
a two-sort finite renaming on their occurring variables. -/
theorem finiteRenamingEq_of_mutualInstances
    {left right : Ty}
    (instances : IsInstance left right ∧ IsInstance right left) :
    FiniteRenamingEq left right := by
  rcases instances.1 with ⟨forward, forward_eq⟩
  rcases instances.2 with ⟨backward, backward_eq⟩
  have leftRoundtrip :
      (left.apply forward).apply backward = left := by
    rw [forward_eq, backward_eq]
  have rightRoundtrip :
      (right.apply backward).apply forward = right := by
    rw [backward_eq, forward_eq]
  refine ⟨forward, backward, forward_eq, backward_eq, ?_, ?_, ?_, ?_⟩
  · intro sourceVar occurs
    obtain ⟨image, image_eq, inverse_eq⟩ :=
      tyVar_image_of_roundtrip forward backward sourceVar left occurs
        leftRoundtrip
    refine ⟨image, ?_, image_eq, inverse_eq⟩
    rw [← forward_eq]
    exact tyVarOccurs_apply_of_eq_var forward occurs image_eq
  · intro sourceVar occurs
    obtain ⟨image, image_eq, inverse_eq⟩ :=
      tyVar_image_of_roundtrip backward forward sourceVar right occurs
        rightRoundtrip
    refine ⟨image, ?_, image_eq, inverse_eq⟩
    rw [← backward_eq]
    exact tyVarOccurs_apply_of_eq_var backward occurs image_eq
  · intro sourceVar occurs
    obtain ⟨image, image_eq, inverse_eq⟩ :=
      capVarTy_image_of_roundtrip forward backward sourceVar left occurs
        leftRoundtrip
    refine ⟨image, ?_, image_eq, inverse_eq⟩
    rw [← forward_eq]
    exact capVarOccursTy_apply_of_eq_var forward occurs image_eq
  · intro sourceVar occurs
    obtain ⟨image, image_eq, inverse_eq⟩ :=
      capVarTy_image_of_roundtrip backward forward sourceVar right occurs
        rightRoundtrip
    refine ⟨image, ?_, image_eq, inverse_eq⟩
    rw [← backward_eq]
    exact capVarOccursTy_apply_of_eq_var backward occurs image_eq

namespace PrincipalTyping

/-- Analogue of Theorem 5.4 for M1: two principal targets for the same source
expression are identical up to a finite renaming of ordinary and capability
variables. -/
theorem finiteRenaming_unique
    {context : Context} {expression : Expr} {left right : Ty}
    (leftPrincipal : PrincipalTyping context expression left)
    (rightPrincipal : PrincipalTyping context expression right) :
    FiniteRenamingEq left right :=
  finiteRenamingEq_of_mutualInstances
    (mutualInstances leftPrincipal rightPrincipal)

end PrincipalTyping

end TypePM
