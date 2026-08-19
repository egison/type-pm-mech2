import TypePM.Types

/-!
# Simultaneous substitutions

Capability variables and ordinary type variables are distinct sorts.  A
substitution replaces both sorts simultaneously; images are not recursively
rewritten by the same substitution.
-/

namespace TypePM

abbrev CapSubst := CapVar → Cap
abbrev TySubst := TyVar → Ty

mutual

def Cap.apply (substitution : CapSubst) : Cap → Cap
  | .any => .any
  | .var index => substitution index
  | .prod items => .prod (Cap.applyList substitution items)

def Cap.applyList (substitution : CapSubst) : List Cap → List Cap
  | [] => []
  | item :: items => item.apply substitution :: Cap.applyList substitution items

end

structure Subst where
  cap : CapSubst
  ty : TySubst

mutual

def Ty.apply (substitution : Subst) : Ty → Ty
  | .var index => substitution.ty index
  | .int => .int
  | .prod items => .prod (Ty.applyList substitution items)
  | .matcher capability target =>
      .matcher (capability.apply substitution.cap) (target.apply substitution)
  | .slot capability target =>
      .slot (capability.apply substitution.cap) (target.apply substitution)

def Ty.applyList (substitution : Subst) : List Ty → List Ty
  | [] => []
  | item :: items => item.apply substitution :: Ty.applyList substitution items

end

namespace Subst

def id : Subst :=
  { cap := Cap.var
    ty := Ty.var }

/-- `compose later earlier` applies `earlier` first and `later` second. -/
def compose (later earlier : Subst) : Subst :=
  { cap := fun index => (earlier.cap index).apply later.cap
    ty := fun index => (earlier.ty index).apply later }

def singleTy (index : TyVar) (replacement : Ty) : Subst :=
  { cap := Cap.var
    ty := fun candidate =>
      if candidate = index then replacement else .var candidate }

end Subst

mutual

@[simp] theorem Cap.apply_id (capability : Cap) :
    capability.apply Subst.id.cap = capability := by
  cases capability with
  | any => rfl
  | var => rfl
  | prod items => simp [Cap.apply, Cap.applyList_id]

@[simp] theorem Cap.applyList_id (items : List Cap) :
    Cap.applyList Subst.id.cap items = items := by
  cases items with
  | nil => rfl
  | cons item items => simp [Cap.applyList, Cap.apply_id, Cap.applyList_id]

end

mutual

@[simp] theorem Ty.apply_id (target : Ty) :
    target.apply Subst.id = target := by
  cases target with
  | var => rfl
  | int => rfl
  | prod items => simp [Ty.apply, Ty.applyList_id]
  | matcher capability target => simp [Ty.apply, Ty.apply_id]
  | slot capability target => simp [Ty.apply, Ty.apply_id]

@[simp] theorem Ty.applyList_id (items : List Ty) :
    Ty.applyList Subst.id items = items := by
  cases items with
  | nil => rfl
  | cons item items => simp [Ty.applyList, Ty.apply_id, Ty.applyList_id]

end

mutual

@[simp] theorem Cap.apply_compose
    (later earlier : Subst) (capability : Cap) :
    (capability.apply earlier.cap).apply later.cap =
      capability.apply (Subst.compose later earlier).cap := by
  cases capability with
  | any => rfl
  | var => rfl
  | prod items => simp [Cap.apply, Cap.applyList_compose]

@[simp] theorem Cap.applyList_compose
    (later earlier : Subst) (items : List Cap) :
    Cap.applyList later.cap (Cap.applyList earlier.cap items) =
      Cap.applyList (Subst.compose later earlier).cap items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Cap.applyList, Cap.apply_compose, Cap.applyList_compose]

end

mutual

@[simp] theorem Ty.apply_compose
    (later earlier : Subst) (target : Ty) :
    (target.apply earlier).apply later =
      target.apply (Subst.compose later earlier) := by
  cases target with
  | var => rfl
  | int => rfl
  | prod items => simp [Ty.apply, Ty.applyList_compose]
  | matcher capability target =>
      simp [Ty.apply, Ty.apply_compose, Cap.apply_compose]
  | slot capability target =>
      simp [Ty.apply, Ty.apply_compose, Cap.apply_compose]

@[simp] theorem Ty.applyList_compose
    (later earlier : Subst) (items : List Ty) :
    Ty.applyList later (Ty.applyList earlier items) =
      Ty.applyList (Subst.compose later earlier) items := by
  cases items with
  | nil => rfl
  | cons item items =>
      simp [Ty.applyList, Ty.apply_compose, Ty.applyList_compose]

end

@[simp] theorem Subst.singleTy_hit (index : TyVar) (replacement : Ty) :
    (Ty.var index).apply (Subst.singleTy index replacement) = replacement := by
  simp [Ty.apply, Subst.singleTy]

/-- `specific` is an instance of `general` when one simultaneous substitution
turns the latter into the former. -/
def IsInstance (general specific : Ty) : Prop :=
  ∃ substitution, general.apply substitution = specific

end TypePM
