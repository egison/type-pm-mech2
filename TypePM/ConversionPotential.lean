import TypePM.Resolution

/-!
# Potential checking conversions

Hard-constraint saturation may turn a delayed check into an ordinary equality
only when no later substitution can expose a special matcher conversion.  The
Boolean predicates below conservatively recognize the source and expected
outer shapes that can still become such a conversion.
-/

namespace TypePM
namespace Ty

/-- A type whose outer constructor can become `matcher` after substitution. -/
def mayBecomeMatcher : Ty → Bool
  | .var _ => true
  | .matcher _ _ => true
  | _ => false

/-- Every item can become a matcher. -/
def mayBecomeMatcherItems : List Ty → Bool
  | [] => true
  | item :: items => item.mayBecomeMatcher && mayBecomeMatcherItems items

/-- A type whose outer constructor can become a nonempty product of matchers. -/
def mayBecomeMatcherProduct : Ty → Bool
  | .var _ => true
  | .prod [] => false
  | .prod (item :: items) =>
      item.mayBecomeMatcher && mayBecomeMatcherItems items
  | _ => false

/-- An expected type whose outer constructor can become `matcher`. -/
def mayBecomeExpectedMatcher : Ty → Bool
  | .var _ => true
  | .matcher _ _ => true
  | _ => false

/-- An expected type whose outer constructor can become `slot`. -/
def mayBecomeExpectedSlot : Ty → Bool
  | .var _ => true
  | .slot _ _ => true
  | _ => false

/-- Whether some future substitution could expose one of the special
checking conversions supported by M1. -/
def couldSpecial (source expected : Ty) : Bool :=
  (source.mayBecomeMatcher && expected.mayBecomeExpectedSlot) ||
  (source.mayBecomeMatcherProduct &&
    (expected.mayBecomeExpectedMatcher || expected.mayBecomeExpectedSlot))

theorem mayBecomeMatcher_of_apply
    (substitution : Subst) (target : Ty)
    (possible : (target.apply substitution).mayBecomeMatcher = true) :
    target.mayBecomeMatcher = true := by
  cases target <;> simp_all [Ty.apply, mayBecomeMatcher]

theorem mayBecomeMatcherItems_of_apply
    (substitution : Subst) (targets : List Ty)
    (possible :
      mayBecomeMatcherItems (Ty.applyList substitution targets) = true) :
    mayBecomeMatcherItems targets = true := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
      simp only [Ty.applyList, mayBecomeMatcherItems,
        Bool.and_eq_true] at possible ⊢
      exact ⟨mayBecomeMatcher_of_apply substitution target possible.1,
        induction possible.2⟩

theorem mayBecomeMatcherProduct_of_apply
    (substitution : Subst) (target : Ty)
    (possible : (target.apply substitution).mayBecomeMatcherProduct = true) :
    target.mayBecomeMatcherProduct = true := by
  cases target with
  | var => rfl
  | int => simp [Ty.apply, mayBecomeMatcherProduct] at possible
  | fn => simp [Ty.apply, mayBecomeMatcherProduct] at possible
  | matcher => simp [Ty.apply, mayBecomeMatcherProduct] at possible
  | slot => simp [Ty.apply, mayBecomeMatcherProduct] at possible
  | prod items =>
      cases items with
      | nil => simp [Ty.apply, Ty.applyList, mayBecomeMatcherProduct] at possible
      | cons item items =>
          simp only [Ty.apply, Ty.applyList, mayBecomeMatcherProduct,
            Bool.and_eq_true] at possible ⊢
          exact ⟨mayBecomeMatcher_of_apply substitution item possible.1,
            mayBecomeMatcherItems_of_apply substitution items possible.2⟩

theorem mayBecomeExpectedMatcher_of_apply
    (substitution : Subst) (target : Ty)
    (possible :
      (target.apply substitution).mayBecomeExpectedMatcher = true) :
    target.mayBecomeExpectedMatcher = true := by
  cases target <;> simp_all [Ty.apply, mayBecomeExpectedMatcher]

theorem mayBecomeExpectedSlot_of_apply
    (substitution : Subst) (target : Ty)
    (possible : (target.apply substitution).mayBecomeExpectedSlot = true) :
    target.mayBecomeExpectedSlot = true := by
  cases target <;> simp_all [Ty.apply, mayBecomeExpectedSlot]

/-- Potential for a special conversion can disappear after substitution, but
it cannot appear from an outer shape that was already impossible. -/
theorem couldSpecial_of_apply
    (substitution : Subst) (source expected : Ty)
    (possible :
      couldSpecial (source.apply substitution) (expected.apply substitution) =
        true) :
    couldSpecial source expected = true := by
  simp only [couldSpecial, Bool.or_eq_true, Bool.and_eq_true] at possible ⊢
  rcases possible with matcherToSlot | productConversion
  · exact Or.inl
      ⟨mayBecomeMatcher_of_apply substitution source matcherToSlot.1,
        mayBecomeExpectedSlot_of_apply substitution expected matcherToSlot.2⟩
  · exact Or.inr
      ⟨mayBecomeMatcherProduct_of_apply substitution source
          productConversion.1,
        productConversion.2.elim
          (fun matcher => Or.inl
            (mayBecomeExpectedMatcher_of_apply substitution expected matcher))
          (fun slot => Or.inr
            (mayBecomeExpectedSlot_of_apply substitution expected slot))⟩

private theorem matcherTypes_possible (duals : List Dual) :
    mayBecomeMatcherItems (duals.map Dual.matcherType) = true := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [mayBecomeMatcherItems, mayBecomeMatcher, Dual.matcherType, induction]

theorem matcherProduct_possible
    (duals : List Dual) (nonempty : duals ≠ []) :
    mayBecomeMatcherProduct (.prod (duals.map Dual.matcherType)) = true := by
  cases duals with
  | nil => exact (nonempty rfl).elim
  | cons dual duals =>
      simp [mayBecomeMatcherProduct, mayBecomeMatcher,
        matcherTypes_possible, Dual.matcherType]

end Ty

namespace Resolution

/-- A special resolution witnesses that its indexed types had special
conversion potential before residual equations were solved. -/
theorem special_implies_couldSpecial
    {source expected : Ty} (resolution : Resolution source expected)
    (special : resolution.Special) :
    source.couldSpecial expected = true := by
  cases resolution with
  | ordinary => simp [Resolution.Special] at special
  | matcherToSlot =>
      simp [Ty.couldSpecial, Ty.mayBecomeMatcher,
        Ty.mayBecomeExpectedSlot]
  | productMatcher _ duals typesEquality nonempty _ _ =>
      rw [← typesEquality]
      simp [Ty.couldSpecial, Ty.mayBecomeExpectedMatcher,
        Ty.matcherProduct_possible duals nonempty]
  | productMatcherToSlot _ duals typesEquality nonempty _ _ _ =>
      rw [← typesEquality]
      simp [Ty.couldSpecial, Ty.mayBecomeExpectedSlot,
        Ty.matcherProduct_possible duals nonempty]

end Resolution

/-- A delayed check is forced to be ordinary when no extension of the current
hard substitution can expose a special conversion. -/
def ForcedOrdinary (source expected : Ty) : Prop :=
  source.couldSpecial expected = false

theorem ForcedOrdinary.no_special_after
    {source expected : Ty} (forced : ForcedOrdinary source expected)
    (substitution : Subst)
    {resolution : Resolution (source.apply substitution)
      (expected.apply substitution)} :
    ¬ resolution.Special := by
  intro special
  have after := resolution.special_implies_couldSpecial special
  have before := Ty.couldSpecial_of_apply substitution source expected after
  change source.couldSpecial expected = false at forced
  rw [forced] at before
  contradiction

end TypePM
