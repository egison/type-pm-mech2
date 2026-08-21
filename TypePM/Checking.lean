import TypePM.Types

/-!
# Normalized checking conversions

A conversion changes how an already synthesized raw type may be used at an
explicitly supplied expected type.  There is no transitivity constructor;
the product-matcher-to-slot composite is represented directly.

M0 contains only the small conversion subset exercised by its regressions.
Conversions for products of slots and other language constructs are added with
the milestones that need them.
-/

namespace TypePM

inductive ConversionClass where
  | ordinary
  | matcherToSlot
  | productMatcherToSlot
deriving Repr, DecidableEq

/-- A producer capability can satisfy the same consumer capability, or a
consumer that explicitly accepts any capability. -/
inductive CapabilityDemand : Cap → Cap → Prop where
  | equal {capability} : CapabilityDemand capability capability
  | any {producer} : CapabilityDemand producer .any

inductive CheckConversion : ConversionClass → Ty → Ty → Prop where
  | ordinary {target} :
      CheckConversion .ordinary target target
  | matcherToSlot {producer consumer target} :
      CapabilityDemand producer consumer →
      CheckConversion .matcherToSlot
        (.matcher producer target) (.slot consumer target)
  | productMatcherToSlot {duals : List Dual} {consumer : Cap} :
      duals ≠ [] →
      CapabilityDemand (.prod (Dual.capabilities duals)) consumer →
      CheckConversion .productMatcherToSlot
        (.prod (duals.map Dual.matcherType))
        (.slot consumer (.prod (Dual.targets duals)))

namespace CheckConversion

/-- A checking conversion whose target is neither a matcher nor a matcher
slot is necessarily the ordinary identity conversion. -/
theorem source_eq_target_of_target_not_slot
    (conversion : CheckConversion conversionClass source target)
    (targetNotSlot : ∀ capability item,
      target ≠ .slot capability item) :
    source = target := by
  cases conversion with
  | ordinary => rfl
  | matcherToSlot => exact (targetNotSlot _ _ rfl).elim
  | productMatcherToSlot => exact (targetNotSlot _ _ rfl).elim

end CheckConversion

end TypePM
