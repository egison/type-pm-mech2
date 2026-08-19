import TypePM.Substitution
import TypePM.Typing

/-!
# M0 boundary regressions

These results fix only the synthesis/checking boundary.  They do not claim
source-level demand provenance or inference completeness.
-/

namespace TypePM
namespace Regression

def pair : Expr :=
  .tuple [.something, .something]

def pairPrincipal : Ty :=
  .prod [.matcher .any (.var ⟨0⟩), .matcher .any (.var ⟨1⟩)]

def pairConcrete : Ty :=
  .prod [.matcher .any .int, .matcher .any .int]

def pairMatcher : Ty :=
  .matcher (.prod [.any, .any]) (.prod [.int, .int])

def pairSlot : Ty :=
  .slot (.prod [.any, .any]) (.prod [.int, .int])

theorem pair_synthesizes_principal :
    Synth [] pair pairPrincipal := by
  exact .tuple (.cons .something (.cons .something .nil))

theorem pair_synthesizes_concrete :
    Synth [] pair pairConcrete := by
  exact .tuple (.cons .something (.cons .something .nil))

theorem pair_synthesis_head_is_product
    {target : Ty} (typing : Synth [] pair target) :
    ∃ targets, target = .prod targets :=
  typing.tuple_target

theorem pair_does_not_synthesize_matcher
    {capability : Cap} {target : Ty} :
    ¬ Synth [] pair (.matcher capability target) := by
  intro typing
  obtain ⟨targets, equality⟩ := typing.tuple_target
  cases equality

theorem pair_checks_as_matcher :
    RootChecks [] pair pairMatcher := by
  exact .via pair_synthesizes_concrete
    (.productMatcher (duals := [⟨.any, .int⟩, ⟨.any, .int⟩]) (by simp))

theorem pair_checks_as_slot :
    RootChecks [] pair pairSlot := by
  exact .via pair_synthesizes_concrete
    (.productMatcherToSlot
      (duals := [⟨.any, .int⟩, ⟨.any, .int⟩]) (by simp)
      .equal)

/-- The `Any` consumer is an explicit capability demand, rather than a
substitution guessed by synthesis. -/
theorem structured_matcher_checks_at_any_slot :
    CheckConversion .matcherToSlot
      (.matcher (.prod [.any]) .int) (.slot .any .int) := by
  exact .matcherToSlot .any

def pairSubst (left right : Ty) : Subst :=
  { cap := Cap.var
    ty := fun index =>
      if index.index = 0 then left
      else if index.index = 1 then right
      else .var index }

theorem pairSubst_applies (left right : Ty) :
    pairPrincipal.apply (pairSubst left right) =
      .prod [.matcher .any left, .matcher .any right] := by
  simp [pairPrincipal, pairSubst, Ty.apply, Ty.applyList, Cap.apply]

theorem pair_raw_targets
    {target : Ty} (typing : Synth [] pair target) :
    ∃ left right,
      target = .prod [.matcher .any left, .matcher .any right] := by
  cases typing with
  | tuple children =>
      cases children with
      | cons left tail =>
          cases left with
          | something =>
              cases tail with
              | cons right rest =>
                  cases right with
                  | something =>
                      cases rest with
                      | nil => exact ⟨_, _, rfl⟩

/-- Every raw synthesis of the pair is an instance of one product-headed
representative.  Matcher and slot checking results are intentionally outside
this theorem. -/
theorem pair_principal
    {target : Ty} (typing : Synth [] pair target) :
    IsInstance pairPrincipal target := by
  obtain ⟨left, right, rfl⟩ := pair_raw_targets typing
  exact ⟨pairSubst left right, pairSubst_applies left right⟩

end Regression
end TypePM
